-- Prove2me | Definitions.Def_RandOrderKnapGAP_Integral_OnlineModel
-- name    : RandOrderKnapGAP_Integral_OnlineModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:26:57.659034+00:00
-- url     : https://prove2.me/theorems/3c3b3709-173a-4262-ac90-367c0c8eb020
-- title:
--   Randomized online algorithms in the random-order model for knapsack, GAP and GPAP, feasibility on every run, and $\mathbb E[\mathrm{ALG}]$
-- statement:
--   In the **random-order model** the instance is fixed in advance and its $n$ items arrive in a uniformly random order $\pi$; $\pi(r)$ is the item arriving in round $r$. A **randomized online algorithm** is fixed before the instance. It owns a probability space $(\Omega,P)$. In each round it decides, irrevocably, what to do with the current item, as a function of: the public parameter (for GAP and GPAP the number $m$ of machines/resources and the capacities $B_b$; for knapsack the capacity $B$), the number $n$ of items, the list of the items that have arrived so far in arrival order, each with its identity and its data (sizes and values; for GPAP the action set with values and consumptions), the current item last, and $\omega\in\Omega$. Each decision is measurable in $\omega$. The decision is accept/reject (knapsack), reject or a machine (GAP), or an action (GPAP).
--
--   For an order $\pi$ and $\omega$, $\mathrm{ALG}(\pi,\omega)$ is the total value of the decisions. The algorithm is **feasible** on an instance when for every $\pi$ and every $\omega$ no capacity is exceeded. Its expected value is
--   $$\mathbb E[\mathrm{ALG}]=\frac1{n!}\sum_{\pi\in S_n}\int_\Omega \mathrm{ALG}(\pi,\omega)\,dP(\omega).$$
--   A GAP algorithm is run on a knapsack instance as on the GAP instance with one machine (`toKnapsack`).
--
--   **Formalization Note.** `RandOnlineAlg Param X Dec` is a structure with fields `Ω`, its σ-algebra, a probability measure `P`, `decide : (p : Param) → (n : ℕ) → List (Fin n × X p) → Ω → Dec p` and measurability of every fibre of `decide`. Rounds are 0-based: the history of round $r$ is $(\pi 0, x_{\pi 0}),\dots,(\pi r, x_{\pi r})$. Earlier decisions are recomputable from the earlier histories and $\omega$, so they are not passed. For GPAP the decision is a natural number; an index outside the item's action set is executed as its rejection action.
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), pp. 1, 3 (PDF 3, 5), §1 and §2

import Mathlib
import Definitions.Def_RandOrderKnapGAP_Integral_Instances

open scoped BigOperators
open MeasureTheory

namespace RandOrderKnapGAP.Integral

/-!
# Randomized online algorithms in the random-order model

Agrawal, Khan, Pareek, *Improved Algorithms in the Random-Order Model: Knapsack, GAP, and
Beyond*, STOC 2027 submission, p. 1 (§1, the random-order model and `ρ`-competitiveness) and
p. 3 (§2, the arrival permutation `π`).

* The arrival order of `n` items is `π : Equiv.Perm (Fin n)`; `π r` is the item arriving in
  (0-based) round `r`. The expectation over the order is the average over all `n!` permutations.
* A randomized online algorithm is fixed before the instance. It carries its own probability
  space `(Ω, P)`. In round `r` its decision for the current item is a function of: the public
  parameter `p` (the capacities, and the number of machines / resources), the number of items
  `n`, the list of arrived items in arrival order (identity and data, current item last), and
  `ω ∈ Ω`. Each decision is measurable in `ω` (every fibre is a measurable set). Earlier
  decisions are recomputable from the same data, so they need not be passed.
* `ALG(π, ω)` is the total value of the run; `E[ALG] = (1/n!) ∑_π ∫ ALG(π, ω) dP(ω)`.
* Feasibility is required on every run: for every `π` and every `ω` no capacity is exceeded.
-/

/-- A randomized online algorithm for a family of problems indexed by the public parameter
`p : Param`, with per-item data `X p` and decisions `Dec p`. -/
structure RandOnlineAlg (Param : Type) (X : Param → Type) (Dec : Param → Type) : Type 1 where
  /-- The sample space of the internal randomness. -/
  Ω : Type
  /-- Its σ-algebra. -/
  mΩ : MeasurableSpace Ω
  /-- The law of the internal randomness. -/
  P : @Measure Ω mΩ
  /-- `P` is a probability measure. -/
  isProb : @IsProbabilityMeasure Ω mΩ P
  /-- The decision for the current (last) item of the history. -/
  decide : (p : Param) → (n : ℕ) → List (Fin n × X p) → Ω → Dec p
  /-- Each decision is a measurable function of the internal randomness. -/
  measurable_decide : ∀ p n (h : List (Fin n × X p)) (d : Dec p),
    MeasurableSet[mΩ] {ω | decide p n h ω = d}

namespace RandOnlineAlg

variable {Param : Type} {X : Param → Type} {Dec : Param → Type}

attribute [instance] RandOnlineAlg.mΩ RandOnlineAlg.isProb

/-- The revealed history in (0-based) round `r` under arrival order `π`: the arrived items
`π 0, …, π r` in order, with their identities and data. -/
def history {p : Param} {n : ℕ} (x : Fin n → X p) (π : Equiv.Perm (Fin n)) (r : Fin n) :
    List (Fin n × X p) :=
  List.ofFn (fun j : Fin (r.val + 1) =>
    (π ⟨j.val, lt_of_lt_of_le j.isLt r.isLt⟩, x (π ⟨j.val, lt_of_lt_of_le j.isLt r.isLt⟩)))

/-- The decision taken in round `r` for the item `π r`. -/
def decision (A : RandOnlineAlg Param X Dec) (p : Param) {n : ℕ} (x : Fin n → X p)
    (π : Equiv.Perm (Fin n)) (ω : A.Ω) (r : Fin n) : Dec p :=
  A.decide p n (history x π r) ω

/-- `E[ALG]` for the per-round gain `g` (value earned by a decision on an item):
`(1/n!) ∑_π ∫ ∑_r g(x_{π r}, d_r) dP`. -/
noncomputable def expectedValue (A : RandOnlineAlg Param X Dec) (p : Param) {n : ℕ}
    (x : Fin n → X p) (g : X p → Dec p → ℝ) : ℝ :=
  (∑ π : Equiv.Perm (Fin n), ∫ ω, (∑ r : Fin n, g (x (π r)) (A.decision p x π ω r)) ∂A.P)
    / (Nat.factorial n : ℝ)

end RandOnlineAlg

/-! ## Knapsack -/

/-- A randomized online algorithm for integral knapsack: the public parameter is the capacity
`B`, an item's data is `(s_i, v_i)`, the decision is accept (`true`) or reject (`false`). -/
abbrev KnapsackAlg := RandOnlineAlg ℝ (fun _ => ℝ × ℝ) (fun _ => Bool)

namespace KnapsackAlg

variable {n : ℕ}

/-- The item data `(s_i, v_i)`. -/
def data (I : KnapsackInstance n) : Fin n → ℝ × ℝ := fun i => (I.size i, I.value i)

/-- Feasible on every run: for every arrival order and every `ω`, the accepted sizes sum to at
most `B`. -/
def Feasible (A : KnapsackAlg) (I : KnapsackInstance n) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (ω : A.Ω),
    ∑ r : Fin n, (if A.decision I.cap (data I) π ω r then I.size (π r) else 0) ≤ I.cap

/-- `E[ALG]` for integral knapsack. -/
noncomputable def expectedValue (A : KnapsackAlg) (I : KnapsackInstance n) : ℝ :=
  RandOnlineAlg.expectedValue A I.cap (data I) (fun xi d => if d then xi.2 else 0)

end KnapsackAlg

/-! ## GAP -/

/-- A randomized online algorithm for integral GAP: the public parameter is `⟨m, B⟩` (number of
machines and capacities), an item's data is `b ↦ (s_{bi}, v_{bi})`, the decision is `none`
(reject) or `some b` (assign to machine `b`). -/
abbrev GAPAlg :=
  RandOnlineAlg (Σ m : ℕ, Fin m → ℝ) (fun p => Fin p.1 → ℝ × ℝ) (fun p => Option (Fin p.1))

namespace GAPAlg

variable {n m : ℕ}

/-- The public parameter `⟨m, B⟩`. -/
def param (I : GAPInstance n m) : Σ m : ℕ, Fin m → ℝ := ⟨m, I.cap⟩

/-- The item data `b ↦ (s_{bi}, v_{bi})`. -/
def data (I : GAPInstance n m) : Fin n → Fin m → ℝ × ℝ := fun i b => (I.size i b, I.value i b)

open Classical in
/-- Feasible on every run: for every order, every `ω` and every machine `b`, the sizes assigned
to `b` sum to at most `B_b`. -/
def Feasible (A : GAPAlg) (I : GAPInstance n m) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (ω : A.Ω) (b : Fin m),
    ∑ r : Fin n, (if A.decision (param I) (data I) π ω r = some b then I.size (π r) b else 0)
      ≤ I.cap b

/-- `E[ALG]` for integral GAP. -/
noncomputable def expectedValue (A : GAPAlg) (I : GAPInstance n m) : ℝ :=
  RandOnlineAlg.expectedValue A (param I) (data I)
    (fun xi d => match d with
      | none => 0
      | some b => (xi b).2)

/-- A GAP algorithm run on knapsack instances as GAP instances with one machine: it is given
`⟨1, fun _ => B⟩` and the item data `fun _ => (s_i, v_i)`, and accepts iff it assigns. -/
def toKnapsack (A : GAPAlg) : KnapsackAlg where
  Ω := A.Ω
  mΩ := A.mΩ
  P := A.P
  isProb := A.isProb
  decide B k h ω :=
    (A.decide ⟨1, fun _ => B⟩ k (h.map (fun e => (e.1, fun _ => e.2))) ω).isSome
  measurable_decide := by
    intro B k h d
    have : {ω | (A.decide ⟨1, fun _ => B⟩ k (h.map (fun e => (e.1, fun _ => e.2))) ω).isSome = d}
        = ⋃ o ∈ {o : Option (Fin 1) | o.isSome = d},
          {ω | A.decide ⟨1, fun _ => B⟩ k (h.map (fun e => (e.1, fun _ => e.2))) ω = o} := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) (fun o _ =>
      A.measurable_decide (⟨1, fun _ => B⟩ : Σ m : ℕ, Fin m → ℝ) k
        (h.map (fun e => (e.1, fun _ => e.2))) o)

end GAPAlg

/-! ## GPAP -/

/-- A randomized online algorithm for integral GPAP: the public parameter is `⟨m, B⟩`, an item's
data is its action set with values and consumptions, the decision is an action index (an index
outside `A_i` is executed as the rejection action). -/
abbrev GPAPAlg :=
  RandOnlineAlg (Σ m : ℕ, Fin m → ℝ) (fun p => GPAPItem p.1) (fun _ => ℕ)

namespace GPAPAlg

variable {n m : ℕ}

/-- The public parameter `⟨m, B⟩`. -/
def param (I : GPAPInstance n m) : Σ m : ℕ, Fin m → ℝ := ⟨m, I.cap⟩

/-- The action of `x` executed for the decision `d`. -/
def act {m : ℕ} (x : GPAPItem m) (d : ℕ) : Fin x.nA :=
  if h : d < x.nA then ⟨d, h⟩ else x.rej

/-- Feasible on every run: for every order, `ω` and resource `b`, the executed actions consume at
most `B_b` of resource `b`. -/
def Feasible (A : GPAPAlg) (I : GPAPInstance n m) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (ω : A.Ω) (b : Fin m),
    ∑ r : Fin n, (I.item (π r)).cons (act (I.item (π r)) (A.decision (param I) I.item π ω r)) b
      ≤ I.cap b

/-- `E[ALG]` for integral GPAP. -/
noncomputable def expectedValue (A : GPAPAlg) (I : GPAPInstance n m) : ℝ :=
  RandOnlineAlg.expectedValue A (param I) I.item (fun x d => x.val (act x d))

end GPAPAlg

end RandOrderKnapGAP.Integral


