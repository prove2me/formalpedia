-- Prove2me | Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_Protocols
-- name    : SuperactivatedCheating_StateConversion_Supplement_Protocols
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:19:08.429202+00:00
-- url     : https://prove2.me/theorems/525891a5-765d-4d73-9f9f-7e533946da19
-- title:
--   Concrete two-round verifier circuits and sequential channel protocols
-- statement:
--   A two-round verifier circuit has finite question, response and retained-reference registers; an initial density operator; a joint middle CPTP map; and a final orthogonal accepting projection. Validity states these physical conditions and nonempty registers, without any assumption about values or attainment. A strategy has arbitrary finite prior pure entanglement and arbitrary finite retained local memories. Each of its four local operations is CPTP. Local resources are product states. Success is the real part of the accepting trace, and each value is the supremum over the actual admissible strategies. A perfect assisted strategy means existence of a finite-dimensional strategy with success exactly one.
--
--   Parallel products and powers tensor the initial states, middle verifier channels and accepting projections, regrouping registers by prover. Each prover may apply arbitrary joint operations across all copies. Exact circuit identity under wire bijections requires equality of preparations, of channels on every operator, and of final projections.
--
--   In $G_{\rm seq}(N,M)$ the verifier chooses a uniform classical message $m$, sends it to Alice, sends Alice’s channel-input response through $N$ to Bob, and accepts exactly Bob’s correct message. In $H_{\rm seq}(N,M)$ the verifier draws a Haar-uniform unit vector in $\mathbb C^M$, sends its unknown state to Alice, keeps a copy, passes Alice’s response through $N$, and SWAP-tests Bob’s return against the copy. The acceptor is $(I+\mathrm{SWAP})/2$, giving probability $(1+\langle\psi|\sigma|\psi\rangle)/2$. The initial mixed density is the entrywise Haar expectation of the two-copy pure state, and the explicit Haar success expectation is also defined. Theorem 18 includes their equality as a construction obligation. Repetition uses independent draws and a product of SWAP projections. A referee-held purification of the averaged preparation changes no strategy probability; neither prover receives the sampled classical description.
--
--   These circuits are defined independently of capacities. Their physical validity and theorems about their success are not stored in the structures.
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), §2.1 p. 12, Definition 13 pp. 16–17, Definition 17 p. 19, Proposition 23 pp. 21–22.

import Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_Operations
import Definitions.Def_DesignTest_haarState

noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement
open scoped Matrix ComplexConjugate
open MeasureTheory

/-- Concrete finite two-round verifier circuit (§2.1 p.12). The initial state may be mixed:
a referee purification, never sent to the players, gives the identical circuit statistics.
The middle channel acts jointly on both responses and the retained reference. -/
structure Protocol where
  A₀ : Type
  B₀ : Type
  R₀ : Type
  A₁ : Type
  B₁ : Type
  A₂ : Type
  B₂ : Type
  R₂ : Type
  A₃ : Type
  B₃ : Type
  [fa0 : Fintype A₀] [fb0 : Fintype B₀] [fr0 : Fintype R₀]
  [fa1 : Fintype A₁] [fb1 : Fintype B₁] [fa2 : Fintype A₂]
  [fb2 : Fintype B₂] [fr2 : Fintype R₂] [fa3 : Fintype A₃] [fb3 : Fintype B₃]
  [da0 : DecidableEq A₀] [db0 : DecidableEq B₀] [dr0 : DecidableEq R₀]
  [da1 : DecidableEq A₁] [db1 : DecidableEq B₁] [da2 : DecidableEq A₂]
  [db2 : DecidableEq B₂] [dr2 : DecidableEq R₂] [da3 : DecidableEq A₃] [db3 : DecidableEq B₃]
  initial : Op (A₀ × B₀ × R₀)
  middle : Map (A₁ × B₁ × R₀) (A₂ × B₂ × R₂)
  acc : Op (A₃ × B₃ × R₂)
attribute [instance] Protocol.fa0 Protocol.fb0 Protocol.fr0 Protocol.fa1 Protocol.fb1
  Protocol.fa2 Protocol.fb2 Protocol.fr2 Protocol.fa3 Protocol.fb3
  Protocol.da0 Protocol.db0 Protocol.dr0 Protocol.da1 Protocol.db1
  Protocol.da2 Protocol.db2 Protocol.dr2 Protocol.da3 Protocol.db3

def Protocol.Valid (G : Protocol) : Prop :=
  Density G.initial ∧ QAlgorithms.IsChannel G.middle ∧ IsProjection G.acc ∧
  Nonempty G.A₀ ∧ Nonempty G.B₀ ∧ Nonempty G.R₀ ∧ Nonempty G.A₁ ∧ Nonempty G.B₁ ∧
  Nonempty G.A₂ ∧ Nonempty G.B₂ ∧ Nonempty G.R₂ ∧ Nonempty G.A₃ ∧ Nonempty G.B₃

/-- All finite private dimensions, including retained memories between turns. -/
structure Protocol.Strategy (G : Protocol) where
  shared : Shared
  mA : ℕ
  mB : ℕ
  E₁ : Map (G.A₀ × Fin shared.eA) (G.A₁ × Fin mA)
  F₁ : Map (G.B₀ × Fin shared.eB) (G.B₁ × Fin mB)
  E₂ : Map (G.A₂ × Fin mA) G.A₃
  F₂ : Map (G.B₂ × Fin mB) G.B₃
  hE₁ : QAlgorithms.IsChannel E₁
  hF₁ : QAlgorithms.IsChannel F₁
  hE₂ : QAlgorithms.IsChannel E₂
  hF₂ : QAlgorithms.IsChannel F₂

/-- Apply two local maps while preserving a referee register, with explicit regrouping. -/
def localStep {A B a b R : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (E : Map A a) (F : Map B b) : Map (A × B × R) (a × b × R) :=
  fun X o o' => tensorId (tensorMap E F)
    (relabel (fun x : (A × B) × R => (x.1.1,x.1.2,x.2)) X)
    ((o.1,o.2.1),o.2.2) ((o'.1,o'.2.1),o'.2.2)

def Protocol.Strategy.run {G : Protocol} (S : G.Strategy) (initial : Op (G.A₀ × G.B₀ × G.R₀)) :
    Op (G.A₃ × G.B₃ × G.R₂) :=
  let X := relabel (fun x : (G.A₀ × Fin S.shared.eA) × (G.B₀ × Fin S.shared.eB) × G.R₀ =>
    ((x.1.1,x.2.1.1,x.2.2),(x.1.2,x.2.1.2))) (tensor initial (pureState S.shared.ψ))
  let Y := localStep S.E₁ S.F₁ X
  let Z := tensorId G.middle (relabel
    (fun x : (G.A₁ × G.B₁ × G.R₀) × (Fin S.mA × Fin S.mB) =>
      ((x.1.1,x.2.1),(x.1.2.1,x.2.2),x.1.2.2)) Y)
  localStep S.E₂ S.F₂ (relabel
    (fun x : (G.A₂ × Fin S.mA) × (G.B₂ × Fin S.mB) × G.R₂ =>
      ((x.1.1,x.2.1.1,x.2.2),(x.1.2,x.2.1.2))) Z)

def Protocol.win (G : Protocol) (S : G.Strategy) : ℝ :=
  (G.acc * S.run G.initial).trace.re

def Protocol.localValue (G : Protocol) : ℝ :=
  sSup {p | ∃ S : G.Strategy, S.shared.product ∧ G.win S = p}
def Protocol.entangledValue (G : Protocol) : ℝ := sSup (Set.range G.win)
def Protocol.perfect (G : Protocol) : Prop := ∃ S : G.Strategy, G.win S = 1

/-- Parallel verifier copies, independent of any channel-capacity identity. -/
def Protocol.prod (G H : Protocol) : Protocol where
  A₀ := G.A₀ × H.A₀; B₀ := G.B₀ × H.B₀; R₀ := G.R₀ × H.R₀
  A₁ := G.A₁ × H.A₁; B₁ := G.B₁ × H.B₁
  A₂ := G.A₂ × H.A₂; B₂ := G.B₂ × H.B₂; R₂ := G.R₂ × H.R₂
  A₃ := G.A₃ × H.A₃; B₃ := G.B₃ × H.B₃
  initial := relabel (fun x => ((x.1.1,x.2.1.1,x.2.2.1),(x.1.2,x.2.1.2,x.2.2.2)))
    (tensor G.initial H.initial)
  middle X := relabel (fun x => ((x.1.1,x.2.1.1,x.2.2.1),(x.1.2,x.2.1.2,x.2.2.2)))
    (tensorMap G.middle H.middle (relabel
      (fun x => ((x.1.1,x.2.1),(x.1.2.1,x.2.2.1),(x.1.2.2,x.2.2.2))) X))
  acc := relabel (fun x => ((x.1.1,x.2.1.1,x.2.2.1),(x.1.2,x.2.1.2,x.2.2.2))) (tensor G.acc H.acc)

def Protocol.rep (G : Protocol) (n : ℕ) : Protocol where
  A₀ := Fin n → G.A₀; B₀ := Fin n → G.B₀; R₀ := Fin n → G.R₀
  A₁ := Fin n → G.A₁; B₁ := Fin n → G.B₁
  A₂ := Fin n → G.A₂; B₂ := Fin n → G.B₂; R₂ := Fin n → G.R₂
  A₃ := Fin n → G.A₃; B₃ := Fin n → G.B₃
  initial := relabel (fun x i => (x.1 i,x.2.1 i,x.2.2 i)) (piOp (fun _ => G.initial))
  middle X := relabel (fun x i => (x.1 i,x.2.1 i,x.2.2 i))
    (power G.middle n (relabel (fun x => (fun i => (x i).1,fun i => (x i).2.1,fun i => (x i).2.2)) X))
  acc := relabel (fun x i => (x.1 i,x.2.1 i,x.2.2 i)) (piOp (fun _ => G.acc))

/-- Definition 13, pp.16–17, with a general finite message alphabet. -/
def gseq {A B M : Type} [Fintype A] [Fintype B] [Fintype M]
    [DecidableEq A] [DecidableEq B] [DecidableEq M] (N : Map A B) : Protocol where
  A₀ := M; B₀ := Unit; R₀ := M
  A₁ := A; B₁ := Unit; A₂ := Unit; B₂ := B; R₂ := M; A₃ := Unit; B₃ := M
  initial x y := if x.1 = x.2.2 ∧ y.1 = y.2.2 ∧ x.1 = y.1 then
    1 / (Fintype.card M : ℂ) else 0
  middle X o o' := N (fun i j => X (i,(),o.2.2) (j,(),o'.2.2)) o.2.1 o'.2.1
  acc x y := if x = y ∧ x.2.1 = x.2.2 then 1 else 0

/-- Independent Haar preparation of input and retained copy, Definition 17, p.19. -/
def haarInitial (m : ℕ) : Op (Fin m × Unit × Fin m) :=
  fun x y => ∫ ψ : DesignTest.PureVec m,
    pureState (fun z : Fin m × Unit × Fin m => ψ.val z.1 * ψ.val z.2.2) x y ∂DesignTest.haarState m

def swapAccept (m : ℕ) : Op (Unit × Fin m × Fin m) :=
  fun x y => ((if x = y then 1 else 0) +
    (if x.2.1 = y.2.2 ∧ x.2.2 = y.2.1 then 1 else 0)) / 2

/-- Definition 17. Unknown quantum input: the local encoder is one fixed channel. -/
def hseq {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Map A B) (m : ℕ) : Protocol where
  A₀ := Fin m; B₀ := Unit; R₀ := Fin m
  A₁ := A; B₁ := Unit; A₂ := Unit; B₂ := B; R₂ := Fin m; A₃ := Unit; B₃ := Fin m
  initial := haarInitial m
  middle X o o' := N (fun i j => X (i,(),o.2.2) (j,(),o'.2.2)) o.2.1 o'.2.1
  acc := swapAccept m

/-- The Haar expectation of the actual acceptance probability, not a code predicate. -/
def hseqHaarWin {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {N : Map A B} {m : ℕ} (S : (hseq N m).Strategy) : ℝ :=
  ∫ ψ : DesignTest.PureVec m,
    (((hseq N m).acc * S.run (pureState
      (fun x : Fin m × Unit × Fin m => ψ.val x.1 * ψ.val x.2.2))).trace.re)
    ∂DesignTest.haarState m


/-- Relabelings of all circuit wires. -/
structure Protocol.PortEquiv (G H : Protocol) where
  a0 : G.A₀ ≃ H.A₀
  b0 : G.B₀ ≃ H.B₀
  r0 : G.R₀ ≃ H.R₀
  a1 : G.A₁ ≃ H.A₁
  b1 : G.B₁ ≃ H.B₁
  a2 : G.A₂ ≃ H.A₂
  b2 : G.B₂ ≃ H.B₂
  r2 : G.R₂ ≃ H.R₂
  a3 : G.A₃ ≃ H.A₃
  b3 : G.B₃ ≃ H.B₃

/-- Exact circuit identity: initial density, channel on every operator, final projector. -/
def Protocol.PortEquiv.Respects {G H : Protocol} (e : G.PortEquiv H) : Prop :=
  G.initial = relabel (fun x => (e.a0 x.1,e.b0 x.2.1,e.r0 x.2.2)) H.initial ∧
  (∀ X, G.middle X = relabel (fun x => (e.a2 x.1,e.b2 x.2.1,e.r2 x.2.2))
    (H.middle (relabel (fun x => (e.a1.symm x.1,e.b1.symm x.2.1,e.r0.symm x.2.2)) X))) ∧
  G.acc = relabel (fun x => (e.a3 x.1,e.b3 x.2.1,e.r2 x.2.2)) H.acc

def unitPair : Unit × Unit ≃ Unit where
  toFun _ := ()
  invFun _ := ((),())
  left_inv := by rintro ⟨⟨⟩,⟨⟩⟩; rfl
  right_inv := by rintro ⟨⟩; rfl

/-- The explicit canonical wire bijections in Proposition 23. -/
def gseqPairPorts {A B C D M T : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype M] [Fintype T] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq M] [DecidableEq T] (N : Map A B) (L : Map C D) :
    (Protocol.prod (gseq (M := M) N) (gseq (M := T) L)).PortEquiv
      (gseq (M := M × T) (tensorMap N L)) where
  a0 := Equiv.refl _; b0 := unitPair; r0 := Equiv.refl _
  a1 := Equiv.refl _; b1 := unitPair
  a2 := unitPair; b2 := Equiv.refl _; r2 := Equiv.refl _
  a3 := unitPair; b3 := Equiv.refl _

end SuperactivatedCheating.StateConversion.Supplement


