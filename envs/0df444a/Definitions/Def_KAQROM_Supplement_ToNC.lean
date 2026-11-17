-- Prove2me | Definitions.Def_KAQROM_Supplement_ToNC
-- name    : KAQROM_Supplement_ToNC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:52:50.664972+00:00
-- url     : https://prove2.me/theorems/04fe815c-3022-41b3-8894-fdf68fb54eb2
-- title:
--   Binary-output tests of non-commutation in the QROM, cheating provers and commuting final observables
-- statement:
--   A **binary-output test of non-commutation** with $r$ verifier rounds has a classical verifier with classical oracle access and a quantum prover that may query in superposition throughout. The parties start with no shared state and communicate classically. The preparation phase alternates prover and verifier stages $P_1,V_1,\dots,V_r,P_{r+1}$, producing the public transcript $M$ and the prover's state. The verifier then computes its output $(c,st)$ with $c\in\{0,1\}$ and sends $c$. The prover applies a binary measurement $P_c$ and returns $a\in\{0,1\}$, and the verifier accepts iff $V^H_{\mathrm{Ver}}(st,a)=1$. This deterministic predicate may accept both, one or neither answer. The honest acceptance probability is $\alpha_\Pi$, and a bound $Q$ on the **honest query complexity** bounds all of the verifier's and the honest prover's queries together.
--
--   A **cheating prover** replaces the prover's stages and final measurements. Fixing $H$ and $M$ determines its final observables $\tilde P^H_c=E^H_c(0)-E^H_c(1)$, where $E^H_c(a)$ is the effect operator of outcome $a$ on the prover's register. It has **commuting final observables** if, for every $H$ and $M$, each final measurement is projective and
--   $$
--   \tilde P^H_0\tilde P^H_1=\tilde P^H_1\tilde P^H_0 .
--   $$
--
--   These are the objects of Theorem 7.5.
--
--   **Formalization Note** The rounds are laid out as in Definition 6.10, and the verifier's stages are the published `KAQROM.PrefixParty`. The honest prover's final measurement is any binary-outcome quantum oracle algorithm. Commutation is required pointwise in $H$, as on p.76.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), §7.4, p.76

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_QAlg
import Definitions.Def_KAQROM_PrefixParty
import Definitions.Def_KAQROM_Supplement_CStage
import Definitions.Def_KAQROM_Supplement_DetAttacker

namespace KAQROM.Supplement

open Matrix
open KAQROM

/-- **A binary-output test of non-commutation (ToNC) in the QROM** (§7.4, p.76) with `r` verifier
rounds. A classical verifier with classical oracle access and a quantum prover that may query in
superposition throughout start in oracle-independent states with no shared state and communicate
classically. The **preparation phase** alternates prover stages `P₁, V₁, P₂, …, V_r, P_{r+1}`
(0-based: prover stage `i` sends message `M_{2i}`, verifier stage `i` sends `M_{2i+1}`; a fixed
empty message stands for a stage that sends none), producing the public transcript `M` and the
prover's retained state; the verifier then computes its output `(c, st)`, `c ∈ {0,1}`, with
classical queries, and sends `c`. The prover applies the binary measurement `P_c` (chosen by `M`
and `c`, possibly querying `H`) to its retained state and returns `a ∈ {0,1}`. The verifier accepts
iff `V^H_Ver(st, a) = 1`, a deterministic classical-query predicate (private verification coins are
part of `st`); it may accept both, one or neither answer.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), §7.4, p.76.

**Formalization Note.** "A constant number of rounds" is the number `r` of verifier stages of the
preparation phase, laid out as in Definition 6.10 (empty first or last stages let either party
speak first or last). The verifier's stages are a published `KAQROM.PrefixParty`; its output
computation is a classical-query stage on its register reading `M` and its query record. The
honest prover's final measurement is any `qF`-query quantum algorithm with a binary outcome (an
observable is the special case of a projective measurement). -/
structure ToNC (X : Type) [Fintype X] [DecidableEq X] (ℓ : ℕ) (Msg St : Type) [Fintype Msg]
    [DecidableEq Msg] [Fintype St] where
  /-- The verifier's register. -/
  RV : Type
  /-- The prover's register. -/
  RP : Type
  /-- Work register of the prover's algorithms. -/
  WP : Type
  /-- Kraus index type. -/
  ι : Type
  [fRV : Fintype RV] [dRV : DecidableEq RV]
  [fRP : Fintype RP] [dRP : DecidableEq RP]
  [fWP : Fintype WP] [dWP : DecidableEq WP]
  [fι : Fintype ι]
  /-- The number of verifier stages of the preparation phase. -/
  r : ℕ
  /-- Classical query steps per verifier stage. -/
  D : ℕ
  /-- The verifier's initial state. -/
  ρV0 : Matrix RV RV ℂ
  /-- The prover's initial state. -/
  ρP0 : Matrix RP RP ℂ
  ρV0_density : WildeQIT.IsDensityOperator ρV0
  ρP0_density : WildeQIT.IsDensityOperator ρP0
  /-- The verifier's preparation stages. -/
  verifier : PrefixParty X ℓ Msg RV ι D
  /-- Query bounds of the prover's preparation stages. -/
  b : Fin (r + 1) → ℕ
  /-- The prover's preparation stage `i`, chosen by the messages so far. -/
  prover : (i : Fin (r + 1)) → List Msg → QAlg X ℓ RP WP RP Msg ι (b i)
  /-- Classical query steps of the verifier's output computation. -/
  DO : ℕ
  /-- The verifier's output `(c, st)`, from `M` and its query record. -/
  vOut : CStage X ℓ ((Fin (2 * r + 1) → Msg) × Transcript X ℓ) (Bool × St) RV ι DO
  /-- Query bound of the prover's final measurement. -/
  qF : ℕ
  /-- The prover's final binary measurement `P_c`, chosen by `M` and `c`. -/
  final : (Fin (2 * r + 1) → Msg) → Bool → QAlg X ℓ RP WP Unit Bool ι qF
  /-- The verification predicate `V^H_Ver(st, a)`. -/
  ver : DetAttacker (St × Bool) X ℓ Bool

attribute [instance] ToNC.fRV ToNC.dRV ToNC.fRP ToNC.dRP ToNC.fWP ToNC.dWP ToNC.fι

/-- A **cheating prover** against a ToNC test: any computationally unbounded quantum prover with
the same communication pattern, i.e. its own register and initial state, preparation stages with
`b i` quantum queries, and final binary measurements chosen by `M` and `c` with `qF` queries. -/
structure CheatProver {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg St : Type} [Fintype Msg]
    [DecidableEq Msg] [Fintype St] (T : ToNC X ℓ Msg St) where
  /-- The prover's register. -/
  RP : Type
  /-- Work register. -/
  WP : Type
  /-- Kraus index type. -/
  ι : Type
  [fRP : Fintype RP] [dRP : DecidableEq RP]
  [fWP : Fintype WP] [dWP : DecidableEq WP]
  [fι : Fintype ι]
  /-- Initial state. -/
  ρ0 : Matrix RP RP ℂ
  ρ0_density : WildeQIT.IsDensityOperator ρ0
  /-- Query bounds of the preparation stages. -/
  b : Fin (T.r + 1) → ℕ
  /-- Preparation stage `i`. -/
  stages : (i : Fin (T.r + 1)) → List Msg → QAlg X ℓ RP WP RP Msg ι (b i)
  /-- Query bound of the final measurement. -/
  qF : ℕ
  /-- The final binary measurement for challenge `c`. -/
  final : (Fin (2 * T.r + 1) → Msg) → Bool → QAlg X ℓ RP WP Unit Bool ι qF

attribute [instance] CheatProver.fRP CheatProver.dRP CheatProver.fWP CheatProver.dWP
  CheatProver.fι

/-- The **effect operator** of outcome `o` of a quantum oracle algorithm with oracle `H`: the
operator `E` on the input register with `Tr(E ρ) = Pr[outcome o | input ρ]` for every `ρ`
(Heisenberg picture), computed entrywise from the run on matrix units. -/
noncomputable def qalgEffect {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ}
    {Rin W Rout O ι : Type} [Fintype Rin] [Fintype W] [Fintype Rout] [Fintype O] [Fintype ι]
    [DecidableEq Rin] [DecidableEq W] {q : ℕ} (A : QAlg X ℓ Rin W Rout O ι q) (H : Oracle X ℓ)
    (o : O) : Matrix Rin Rin ℂ :=
  fun j i => (A.run H (Matrix.single i j 1) o).trace

namespace ToNC

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg St : Type} [Fintype Msg]
  [DecidableEq Msg] [Fintype St]

/-- The verifier's prefix-party outcome vector: messages `m`, and its query outcomes `oq i` in its
stage `i` (position `2i + 1`). -/
def outcomes (T : ToNC X ℓ Msg St) (m : Fin (2 * T.r + 1) → Msg)
    (oq : Fin T.r → Fin T.D → Option X) : Fin (2 * T.r + 1) → (Fin T.D → Option X) × Msg :=
  fun i => (if h : i.val % 2 = 1 then oq ⟨i.val / 2, by omega⟩ else fun _ => none, m i)

/-- The verifier's run through the preparation phase on the branch `(m, oq)`: its unnormalized
state and its complete query–answer record. -/
noncomputable def prepRun (T : ToNC X ℓ Msg St) (H : Oracle X ℓ) (m : Fin (2 * T.r + 1) → Msg)
    (oq : Fin T.r → Fin T.D → Option X) : Matrix T.RV T.RV ℂ × Transcript X ℓ :=
  T.verifier.run H (fun i => i % 2 = 1) (2 * T.r + 1) (T.outcomes m oq) T.ρV0

/-- The verifier's output stage on the branch: unnormalized state and its query list. -/
noncomputable def vRun (T : ToNC X ℓ Msg St) (H : Oracle X ℓ) (m : Fin (2 * T.r + 1) → Msg)
    (oq : Fin T.r → Fin T.D → Option X) (oqO : Fin T.DO → Option X) (c : Bool) (st : St) :
    Matrix T.RV T.RV ℂ × Transcript X ℓ :=
  T.vOut.run H (m, (T.prepRun H m oq).2) oqO (c, st) (T.prepRun H m oq).1

/-- The honest prover's retained state after the preparation phase with messages `m`. -/
noncomputable def proverRun (T : ToNC X ℓ Msg St) (H : Oracle X ℓ)
    (m : Fin (2 * T.r + 1) → Msg) : Matrix T.RP T.RP ℂ :=
  (List.finRange (T.r + 1)).foldl
    (fun σ i => (T.prover i ((List.ofFn m).take (2 * i.val))).run H σ (m ⟨2 * i.val, by omega⟩))
    T.ρP0

/-- **The honest acceptance probability `α_Π`** (p.76), over `H ← ℋ` and the honest execution. -/
noncomputable def alpha (T : ToNC X ℓ Msg St) : ℝ :=
  (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ m : Fin (2 * T.r + 1) → Msg,
    ∑ oq : Fin T.r → Fin T.D → Option X, ∑ oqO : Fin T.DO → Option X, ∑ c : Bool, ∑ st : St,
      ∑ a : Bool, if T.ver.out H (st, a) = true then
        (T.vRun H m oq oqO c st).1.trace.re * ((T.final m c).run H (T.proverRun H m) a).trace.re
      else 0

/-- The verifier's stages make at most `a i` queries and its output computation at most `aO`, on
every oracle, every transcript and every branch of positive probability of the verifier. -/
def VQueriesLe (T : ToNC X ℓ Msg St) (a : Fin T.r → ℕ) (aO : ℕ) : Prop :=
  ∀ (H : Oracle X ℓ) (m : Fin (2 * T.r + 1) → Msg) (oq : Fin T.r → Fin T.D → Option X)
    (oqO : Fin T.DO → Option X) (c : Bool) (st : St),
    0 < (T.vRun H m oq oqO c st).1.trace.re →
      (∀ i : Fin T.r, (List.ofFn (oq i)).countP (fun o => o.isSome) ≤ a i) ∧
        (List.ofFn oqO).countP (fun o => o.isSome) ≤ aO

/-- `Q` bounds the honest query complexity of the test: the verifier's queries (preparation,
output and verification) plus the honest prover's queries (preparation and final measurement). -/
def HonestQueriesLe (T : ToNC X ℓ Msg St) (Q : ℕ) : Prop :=
  ∃ (a : Fin T.r → ℕ) (aO qV : ℕ), T.VQueriesLe a aO ∧ T.ver.QueriesLe qV ∧
    ∑ i, a i + aO + qV + ∑ i, T.b i + T.qF ≤ Q

/-- The cheating prover's retained state after the preparation phase. -/
noncomputable def cheatRun (T : ToNC X ℓ Msg St) (C : CheatProver T) (H : Oracle X ℓ)
    (m : Fin (2 * T.r + 1) → Msg) : Matrix C.RP C.RP ℂ :=
  (List.finRange (T.r + 1)).foldl
    (fun σ i => (C.stages i ((List.ofFn m).take (2 * i.val))).run H σ (m ⟨2 * i.val, by omega⟩))
    C.ρ0

/-- The acceptance probability of a cheating prover against the honest verifier. -/
noncomputable def acc (T : ToNC X ℓ Msg St) (C : CheatProver T) : ℝ :=
  (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ m : Fin (2 * T.r + 1) → Msg,
    ∑ oq : Fin T.r → Fin T.D → Option X, ∑ oqO : Fin T.DO → Option X, ∑ c : Bool, ∑ st : St,
      ∑ a : Bool, if T.ver.out H (st, a) = true then
        (T.vRun H m oq oqO c st).1.trace.re * ((C.final m c).run H (T.cheatRun C H m) a).trace.re
      else 0

end ToNC

namespace CheatProver

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg St : Type} [Fintype Msg]
  [DecidableEq Msg] [Fintype St] {T : ToNC X ℓ Msg St}

/-- The total number of oracle queries of a cheating prover. -/
def queries (C : CheatProver T) : ℕ := ∑ i, C.b i + C.qF

/-- The final observable `P̃^H_c = E^H_c(0) − E^H_c(1)` of challenge `c`, on transcript `m`. -/
noncomputable def obs (C : CheatProver T) (H : Oracle X ℓ) (m : Fin (2 * T.r + 1) → Msg)
    (c : Bool) : Matrix C.RP C.RP ℂ :=
  qalgEffect (C.final m c) H false - qalgEffect (C.final m c) H true

/-- **Commuting final observables** (p.76, pointwise in `H`): for every oracle `H` and every
transcript, each final measurement is projective (a binary observable) and
`P̃^H_0 P̃^H_1 = P̃^H_1 P̃^H_0`. -/
def HasCommutingObservables (C : CheatProver T) : Prop :=
  ∀ (H : Oracle X ℓ) (m : Fin (2 * T.r + 1) → Msg),
    (∀ c : Bool, qalgEffect (C.final m c) H false * qalgEffect (C.final m c) H false =
      qalgEffect (C.final m c) H false) ∧
    C.obs H m false * C.obs H m true = C.obs H m true * C.obs H m false

end CheatProver

end KAQROM.Supplement


