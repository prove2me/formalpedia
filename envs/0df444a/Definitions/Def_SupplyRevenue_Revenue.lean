-- Prove2me | Definitions.Def_SupplyRevenue_Revenue
-- name    : SupplyRevenue_Revenue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:30.966196+00:00
-- url     : https://prove2.me/theorems/8e81cf56-b5d4-490b-9975-b0e536701c98
-- title:
--   Actual revenue: Rev, OblivItemRev, FixedItemRev, SeqItemRev
-- statement:
--   A price matrix $P$ gives one offer per buyer. Buyers arrive in order $\pi$, starting from full stock. Each demands from their assortment and the remaining stock, and pays; the purchase leaves the stock. $\mathrm{Rev}(P,D,\pi)$ is the expected payment over the independent types. The benchmarks are
--
--   $$\mathrm{OblivItemRev}(D)=\sup_{\mathcal P}\min_{\pi}E_{P\sim\mathcal P}\mathrm{Rev}(P,D,\pi),\qquad \mathrm{FixedItemRev}(D,\pi)=\sup_P\mathrm{Rev}(P,D,\pi),$$
--
--   over finite mixtures $\mathcal P$ of matrices, whose rows may be correlated, and $\mathrm{SeqItemRev}(D,\pi)$, the supremum over finite mixtures of adaptive policies of the expected revenue in order $\pi$. A policy maps the list of earlier purchases to the next offer.
--
--   The module also defines the probability that a buyer receives an item, the expectation over independently sampled rows, the offer at prices $\max\{p_j/2,L\}$ of Lemma 2.1, and whole-offer activation.
--
--   **Formalization Note** The minimum over orders is outside the expectation over matrices, so the guarantee is per order and not per matrix.
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §1.1, p.2; Lemma 2.1, p.5; §3, p.8

import Mathlib
import Definitions.Def_SupplyRevenue_Buyer

open scoped ENNReal

namespace SupplyRevenue

/-!
# Actual single-copy revenue: `Rev`, `OblivItemRev`, `FixedItemRev`, `SeqItemRev`

Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
§1.1, p.2: "For order π, SeqItemRev(D, π) adapts to sales, while FixedItemRev(D, π) commits a deterministic personalized
matrix. Writing Rev(P, D, π) for expected revenue when P is restricted to unsold items, define
OblivItemRev(D) = sup_𝒫 min_{π∈Π_n} E_{P∼𝒫} Rev(P, D, π). Finite mixtures 𝒫 may correlate rows but are independent of
types and order."

**Formalization Note** `π k` is the buyer at position `k`, and the arrival list is `List.ofFn π`. Stock starts full. An
arriving buyer demands from `A_i ∩ stock`; the purchase leaves the stock. The type profile has the product mass, which
is buyer independence. The infimum over `π` sits outside the mixture expectation: the guarantee is per order, not per
matrix. A sequential policy maps the list of earlier purchases to an offer, and the position is its length (reading R8);
randomization is a finite mixture of such policies. All suprema are in `ℝ≥0∞` (R9).
-/

/-- A price matrix: one personalized offer per buyer. -/
abbrev Matrix' (n m : ℕ) := Fin n → Offer m

/-- A type profile. -/
abbrev Profile {n m : ℕ} (D : Instance n m) := ∀ i, Fin (D i).numTypes

/-- The product expectation over independent types. -/
noncomputable def profileE {n m : ℕ} (D : Instance n m) (f : Profile D → ℝ) : ℝ :=
  ∑ θ : Profile D, (∏ i, (D i).mass (θ i)) * f θ

/-- The realized allocation when the buyers in `order` arrive with stock `S`. -/
noncomputable def runAlloc {n m : ℕ} (tie : Tie m) (D : Instance n m) (P : Matrix' n m)
    (θ : Profile D) : List (Fin n) → Finset (Fin m) → Fin n → Finset (Fin m)
  | [], _ => fun _ => ∅
  | i :: l, S =>
      let Q := demand tie ((D i).val (θ i)) (P i) S
      Function.update (runAlloc tie D P θ l (S \ Q)) i Q

/-- The realized allocation in order `π`, from full stock. -/
noncomputable def alloc {n m : ℕ} (tie : Tie m) (D : Instance n m) (P : Matrix' n m)
    (π : Equiv.Perm (Fin n)) (θ : Profile D) : Fin n → Finset (Fin m) :=
  runAlloc tie D P θ (List.ofFn π) Finset.univ

/-- `Rev(P, D, π)`: the expected actual revenue of matrix `P` in order `π` (p.2). -/
noncomputable def rev {n m : ℕ} (tie : Tie m) (D : Instance n m) (P : Matrix' n m)
    (π : Equiv.Perm (Fin n)) : ℝ :=
  profileE D fun θ => ∑ i, (P i).pay (alloc tie D P π θ i)

/-- The probability that buyer `i` actually receives item `j` under `P` in order `π`. -/
noncomputable def allocProb {n m : ℕ} (tie : Tie m) (D : Instance n m) (P : Matrix' n m)
    (π : Equiv.Perm (Fin n)) (i : Fin n) (j : Fin m) : ℝ :=
  profileE D fun θ => if j ∈ alloc tie D P π θ i then 1 else 0

/-- `OblivItemRev(D)` (p.2): the best worst-order expected revenue of a finite mixture of matrices. -/
noncomputable def oblivRev {n m : ℕ} (tie : Tie m) (D : Instance n m) : ℝ≥0∞ :=
  ⨆ mixture : Mix (Matrix' n m), ⨅ π : Equiv.Perm (Fin n),
    ENNReal.ofReal (mixture.E fun P => rev tie D P π)

/-- `FixedItemRev(D, π)` (p.2): the best deterministic matrix in the known order `π`. -/
noncomputable def fixedRev {n m : ℕ} (tie : Tie m) (D : Instance n m)
    (π : Equiv.Perm (Fin n)) : ℝ≥0∞ :=
  ⨆ P : Matrix' n m, ENNReal.ofReal (rev tie D P π)

/-- A deterministic adaptive policy: the list of earlier purchases determines the next offer (reading R8). -/
abbrev Policy (m : ℕ) := List (Finset (Fin m)) → Offer m

/-- The realized revenue of a policy for buyers in `order`, from history `h` and stock `S`. -/
noncomputable def policyRun {n m : ℕ} (tie : Tie m) (D : Instance n m) (pol : Policy m)
    (θ : Profile D) : List (Fin n) → List (Finset (Fin m)) → Finset (Fin m) → ℝ
  | [], _, _ => 0
  | i :: l, h, S =>
      let Q := demand tie ((D i).val (θ i)) (pol h) S
      (pol h).pay Q + policyRun tie D pol θ l (h ++ [Q]) (S \ Q)

/-- The expected revenue of a deterministic adaptive policy in order `π`. -/
noncomputable def policyRev {n m : ℕ} (tie : Tie m) (D : Instance n m) (pol : Policy m)
    (π : Equiv.Perm (Fin n)) : ℝ :=
  profileE D fun θ => policyRun tie D pol θ (List.ofFn π) [] Finset.univ

/-- `SeqItemRev(D, π)` (p.2, reading R8): the supremum over finite mixtures of adaptive policies, in order `π`. -/
noncomputable def seqRev {n m : ℕ} (tie : Tie m) (D : Instance n m)
    (π : Equiv.Perm (Fin n)) : ℝ≥0∞ :=
  ⨆ μ : Mix (Policy m), ENNReal.ofReal (μ.E fun pol => policyRev tie D pol π)

/-- `E_{P ∼ ∏_i σ_i} f(P)`: the expectation over independently sampled rows, one per finite mixture `σ i`. -/
noncomputable def indepE {n m : ℕ} (σ : Fin n → Mix (Offer m)) (f : Matrix' n m → ℝ) : ℝ :=
  ∑ a : (∀ i, Fin (σ i).N), (∏ i, (σ i).weight (a i)) * f fun i => (σ i).atom (a i)

/-- The offer of Lemma 2.1 (p.5): the same assortment, at prices `max{p_j / 2, L}`. -/
noncomputable def Offer.floorAt {m : ℕ} (o : Offer m) (L : ℝ) : Offer m where
  assort := o.assort
  price := fun j => max (o.price j / 2) L
  price_nonneg := fun j => le_max_of_le_left (div_nonneg (o.price_nonneg j) zero_le_two)

/-- The image of a finite mixture under a map of atoms. -/
def Mix.map {α β : Type} (μ : Mix α) (g : Fin μ.N → α → β) : Mix β where
  N := μ.N
  weight := μ.weight
  atom := fun a => g a (μ.atom a)
  weight_nonneg := μ.weight_nonneg
  weight_sum := μ.weight_sum

/-- Whole-offer activation by `t ∈ [0, 1]`: with probability `t` the offer drawn from `μ`, otherwise the empty offer.
`t` is clamped to `[0, 1]`, so the definition is total; all uses have `t` in that range. -/
noncomputable def Mix.activate {m : ℕ} (μ : Mix (Offer m)) (t : ℝ) : Mix (Offer m) where
  N := μ.N + 1
  weight := Fin.cons (1 - max 0 (min t 1)) fun a => max 0 (min t 1) * μ.weight a
  atom := Fin.cons (Offer.empty m) μ.atom
  weight_nonneg := by
    intro a
    refine Fin.cases ?_ (fun a => ?_) a
    · simp only [Fin.cons_zero]
      have : max 0 (min t 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
      linarith
    · simp only [Fin.cons_succ]
      exact mul_nonneg (le_max_left _ _) (μ.weight_nonneg a)
  weight_sum := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum, μ.weight_sum]
    ring

end SupplyRevenue


