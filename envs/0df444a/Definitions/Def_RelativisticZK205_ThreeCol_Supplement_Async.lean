-- Prove2me | Definitions.Def_RelativisticZK205_ThreeCol_Supplement_Async
-- name    : RelativisticZK205_ThreeCol_Supplement_Async
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:30:34.793986+00:00
-- url     : https://prove2.me/theorems/0cf052f2-c943-440c-80c0-aff445c4fba9
-- title:
--   Delayed channel interfaces and local stochastic verifier experiments
-- statement:
--   A stateful bipartite device has an initial state distribution and two local input/output interfaces. A channel instance initially has neither input. Its first caller immediately receives its marginal output, evaluated at a fixed dummy remote input. Its second caller receives the normalized conditional output given the first caller's already emitted output. For No-Signalling channels this implements the same channel independently of interface order. Zero-probability conditional histories have an explicit fallback.
--
--   A verifier consists of two local stochastic machines with private memory. An instruction can update local memory, access an unused verifier resource, invoke its prover interface once, or halt with a local output. Its continuation receives only its own reply. A finite schedule chooses one local instruction per tick. Each verifier resource has independent initialization, separate local histories and at most one access per side; resource indices may be accessed in different orders. The final distribution retains both local memories, terminal outputs and local usage records:
--   $$\operatorname{Experiment}(D,R,M_A,M_B,\mu,\sigma).$$
--   The initial joint verifier state $\mu$ is independent of the device and resource bank. Stochastic choices can be retained in memory, including every transcript, auxiliary input and private coin required by the verifier. All bounded local programs are represented by sufficiently large finite state spaces; a fixed alternating schedule with local idle steps accommodates variable local execution paths. This interface layer is reusable beyond Γ_LHV. It assumes no simulation identity and no No-Signalling property of the device being tested.
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.5, §2.4 local wirings; pp.8–9, Definitions 18–22

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Channel

namespace RelativisticZK205.ThreeCol.Supplement

/-- A stateful bipartite interface. State is internal to the device, never exposed
as an argument to either user's local program. -/
structure Device (A B X Y : Type) where
  State : Type
  initial : PMF State
  alice : State → A → PMF (X × State)
  bob : State → B → PMF (Y × State)

noncomputable def Device.joint {A B X Y : Type} (D : Device A B X Y)
    (a : A) (b : B) : PMF (X × Y) :=
  D.initial.bind fun s => (D.alice s a).bind fun xs =>
    (D.bob xs.2 b).map fun ys => (xs.1, ys.1)

noncomputable def Device.reverseJoint {A B X Y : Type} (D : Device A B X Y)
    (a : A) (b : B) : PMF (X × Y) :=
  D.initial.bind fun s => (D.bob s b).bind fun ys =>
    (D.alice ys.2 a).map fun xs => (xs.1, ys.1)

noncomputable def Device.alicePrefix {A B X Y : Type} (D : Device A B X Y) (a : A) : PMF X :=
  D.initial.bind fun s => (D.alice s a).map Prod.fst

noncomputable def Device.bobPrefix {A B X Y : Type} (D : Device A B X Y) (b : B) : PMF Y :=
  D.initial.bind fun s => (D.bob s b).map Prod.fst

/-- Normalized conditioning. The fallback is used only on a zero-probability history. -/
noncomputable def conditional {T R : Type} (p : PMF T) (event : Set T)
    (out : T → R) (fallback : R) : PMF R := by
  classical
  exact if h : ∃ t ∈ event, t ∈ p.support then (p.filter event h).map out
    else PMF.pure fallback

inductive Half (A B X Y : Type) where
  | empty
  | left : A → X → Half A B X Y
  | right : B → Y → Half A B X Y
  | full : A → B → X → Y → Half A B X Y

/-- First interface uses its marginal at a dummy remote input; the second uses
its conditional law given the already emitted output. This is an evaluation
semantics for a No-Signalling box, not a communication operation by its users. -/
noncomputable def leftStep {A B X Y : Type} [Inhabited B] [Inhabited X]
    (U : Channel A B X Y) (s : Half A B X Y) (a : A) : PMF (X × Half A B X Y) :=
  match s with
  | .empty => ((U a default).map Prod.fst).map fun x => (x, .left a x)
  | .right b y => (conditional (U a b) {o | o.2 = y} Prod.fst default).map
      fun x => (x, .full a b x y)
  | .left a₀ x => PMF.pure (x, .left a₀ x)
  | .full a₀ b x y => PMF.pure (x, .full a₀ b x y)

noncomputable def rightStep {A B X Y : Type} [Inhabited A] [Inhabited Y]
    (U : Channel A B X Y) (s : Half A B X Y) (b : B) : PMF (Y × Half A B X Y) :=
  match s with
  | .empty => ((U default b).map Prod.snd).map fun y => (y, .right b y)
  | .left a x => (conditional (U a b) {o | o.1 = x} Prod.snd default).map
      fun y => (y, .full a b x y)
  | .right b₀ y => PMF.pure (y, .right b₀ y)
  | .full a b₀ x y => PMF.pure (y, .full a b₀ x y)

/-- One fresh independent sample at each finite index. -/
noncomputable def independent {I T : Type} [Fintype I] [DecidableEq I] [Inhabited T]
    (p : I → PMF T) : PMF (I → T) :=
  Finset.univ.toList.foldl (fun law i => law.bind fun f =>
    (p i).map fun t => Function.update f i t) (PMF.pure fun _ => default)

instance {A B X Y : Type} : Inhabited (Half A B X Y) := ⟨.empty⟩

/-- Arbitrary local stochastic instructions; continuations see only local outputs. -/
inductive Instruction (A X I U S O : Type) where
  | internal : S → Instruction A X I U S O
  | resource : ℕ → I → (U → S) → Instruction A X I U S O
  | prover : A → (X → S) → Instruction A X I U S O
  | halt : O → Instruction A X I U S O

structure LocalMachine (A X I U S O : Type) where
  step : S → PMF (Instruction A X I U S O)

/-- Hidden bookkeeping ensures each interface is used at most once. Invalid
repeated accesses terminate that local program; they never expose remote data. -/
structure LocalState (S O : Type) where
  memory : S
  output : Option O := none
  stopped : Bool := false
  used : Finset ℕ := ∅
  usedProver : Bool := false

/-- A fixed finite bank of initialized verifier channels, independently of D.
The verifier's own shared coins are part of an arbitrary initial joint state.
Every tick acts on just one local machine. All finite interleavings are quantified
in the theorem. No interface waits for its partner to supply an input. -/
noncomputable def experiment {A B X Y I J U V SA SB OA OB : Type}
    [Inhabited I] [Inhabited J] [Inhabited U] [Inhabited V]
    (D : Device A B X Y) (m : ℕ) (R : Fin m → Channel I J U V)
    (MA : LocalMachine A X I U SA OA) (MB : LocalMachine B Y J V SB OB)
    (coins : PMF (SA × SB)) (schedule : List Bool) : PMF (LocalState SA OA × LocalState SB OB) := by
  classical
  let initial := coins.bind fun ab => D.initial.map fun s =>
    (({memory := ab.1} : LocalState SA OA), ({memory := ab.2} : LocalState SB OB),
      s, (fun _ : Fin m => (Half.empty : Half I J U V)))
  let tick := fun (law : PMF (LocalState SA OA × LocalState SB OB × D.State ×
      (Fin m → Half I J U V))) (side : Bool) => law.bind fun z =>
    let a := z.1
    let b := z.2.1
    let s := z.2.2.1
    let bank := z.2.2.2
    if side then
      if b.stopped then PMF.pure z else
      (MB.step b.memory).bind fun op => match op with
      | .internal t => PMF.pure (a, {b with memory := t}, s, bank)
      | .halt o => PMF.pure (a, {b with output := some o, stopped := true}, s, bank)
      | .prover q next =>
          if b.usedProver then PMF.pure (a, {b with stopped := true}, s, bank) else
          (D.bob s q).map fun ys =>
            (a, {b with memory := next ys.1, usedProver := true}, ys.2, bank)
      | .resource i q next =>
          if h : i < m then
            if i ∈ b.used then PMF.pure (a, {b with stopped := true}, s, bank) else
            (rightStep (R ⟨i,h⟩) (bank ⟨i,h⟩) q).map fun ys =>
              (a, {b with memory := next ys.1, used := insert i b.used}, s,
                Function.update bank ⟨i,h⟩ ys.2)
          else PMF.pure (a, {b with stopped := true}, s, bank)
    else
      if a.stopped then PMF.pure z else
      (MA.step a.memory).bind fun op => match op with
      | .internal t => PMF.pure ({a with memory := t}, b, s, bank)
      | .halt o => PMF.pure ({a with output := some o, stopped := true}, b, s, bank)
      | .prover q next =>
          if a.usedProver then PMF.pure ({a with stopped := true}, b, s, bank) else
          (D.alice s q).map fun xs =>
            ({a with memory := next xs.1, usedProver := true}, b, xs.2, bank)
      | .resource i q next =>
          if h : i < m then
            if i ∈ a.used then PMF.pure ({a with stopped := true}, b, s, bank) else
            (leftStep (R ⟨i,h⟩) (bank ⟨i,h⟩) q).map fun xs =>
              ({a with memory := next xs.1, used := insert i a.used}, b, s,
                Function.update bank ⟨i,h⟩ xs.2)
          else PMF.pure ({a with stopped := true}, b, s, bank)
  exact (schedule.foldl tick initial).map fun z => (z.1, z.2.1)

end RelativisticZK205.ThreeCol.Supplement


