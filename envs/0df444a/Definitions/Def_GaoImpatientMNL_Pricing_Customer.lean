-- Prove2me | Definitions.Def_GaoImpatientMNL_Pricing_Customer
-- name    : GaoImpatientMNL_Pricing_Customer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:22:42.442773+00:00
-- url     : https://prove2.me/theorems/5ef67579-11f2-403e-bcd5-1e630fc2f9d7
-- title:
--   Independent utilities, finite patience, and the purchase event
-- statement:
--   On an arbitrary measurable probability space, the customer has product utilities $U_i$ with Gumbel location $\mu_i$ and scale one, one outside utility $U_0$ with Gumbel location zero and scale one, and patience $Y\in\{1,\ldots,m\}$. All these random variables are mutually independent and measurable, with $P(Y\ge k)=\lambda_k\in(0,1]$. Independence is the standard Mathlib independence of the whole family, encoding the finite patience variable as its real-valued index. The outside utility is sampled once for the whole journey.
--
--   The event of purchasing product $i\in S_k$ consists of outcomes where patience permits stage $k$, every earlier offered product has utility at most $U_0$, and $i$ is a maximum-utility product of stage $k$ with utility strictly above $U_0$. Ties among stage products go to the smallest product index. This is an operational event, defined without using its desired probability. Empty stages still count toward patience. Product and stage labels are zero-based in Lean; the outside option has a distinct optional label.
-- source:
--   Gao et al., DOI 10.1287/opre.2021.2127, held source.pdf, §§2,4 and Appendix F; PDF pp.6,11–16,45–51 (printed pp.6,11–16,ec8–ec14).

import Mathlib
import Definitions.Def_GaoImpatientMNL_Pricing_Model
import Definitions.Def_GaoImpatientMNL_Pricing_GumbelLaw

open MeasureTheory ProbabilityTheory
noncomputable section

/- BEGIN IMPORTED LEAN FOR BLIND AUDIT
noncomputable section
namespace MultiStoreAssort.Pricing
variable {n : ℕ}
noncomputable def rev14 (a b : Fin n → ℝ) (S : Finset (Fin n)) (p : Fin n → ℝ) : ℝ :=
  (∑ k ∈ S, p k * Real.exp (a k - b k * p k)) / (1 + ∑ k ∈ S, Real.exp (a k - b k * p k))
end MultiStoreAssort.Pricing
end

open scoped BigOperators
noncomputable section
namespace GaoImpatientMNL.Pricing
def Parameters {n m : ℕ} (β : ℝ) (lam : Fin m → ℝ) : Prop :=
  0 < n ∧ 0 < m ∧ 0 < β ∧
    (∀ k, k.val = 0 → lam k = 1) ∧ (∀ k, 0 < lam k) ∧ Antitone lam
def Feasible {n m : ℕ} (S : Fin m → Finset (Fin n)) : Prop :=
  ∀ k h, k ≠ h → Disjoint (S k) (S h)
def attraction {n : ℕ} (α : Fin n → ℝ) (β : ℝ) (p : Fin n → ℝ)
    (s : Finset (Fin n)) : ℝ := ∑ i ∈ s, Real.exp (α i - β * p i)
def prefixWeight {n m : ℕ} (v : Fin n → ℝ) (S : Fin m → Finset (Fin n)) (k : Fin m) : ℝ :=
  ∑ h ∈ Finset.univ.filter (fun h => h < k), ∑ i ∈ S h, v i
def choiceFormula {n m : ℕ} (v : Fin n → ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (k : Fin m) (i : Fin n) : ℝ :=
  lam k * v i / ((1 + prefixWeight v S k) * (1 + prefixWeight v S k + ∑ j ∈ S k, v j))
def revenue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) : ℝ :=
  ∑ k, (lam k * ∑ i ∈ S k, p i * Real.exp (α i - β * p i)) /
    ((1 + prefixWeight (fun i => Real.exp (α i - β * p i)) S k) *
      (1 + prefixWeight (fun i => Real.exp (α i - β * p i)) S k + attraction α β p (S k)))
def firstSequence (n m : ℕ) : Fin m → Finset (Fin n) :=
  fun k => if k.val = 0 then Finset.univ else ∅
def firstRevenue {n : ℕ} (α : Fin n → ℝ) (β : ℝ) (p : Fin n → ℝ) : ℝ :=
  MultiStoreAssort.Pricing.rev14 α (fun _ => β) Finset.univ p
def jointRevenues {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ) : Set ℝ :=
  {r | ∃ S : Fin m → Finset (Fin n), Feasible S ∧ ∃ p : Fin n → ℝ, r = revenue α β lam S p}
def jointValue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ) : ℝ :=
  sSup (jointRevenues α β lam)
def firstValue {n : ℕ} (α : Fin n → ℝ) (β : ℝ) : ℝ :=
  sSup (Set.range (firstRevenue α β))
def IsPricingMax {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ)
    (S : Fin m → Finset (Fin n)) (p : Fin n → ℝ) : Prop :=
  ∀ p', revenue α β lam S p' ≤ revenue α β lam S p
def MaximaExist {n m : ℕ} (α : Fin n → ℝ) (β : ℝ) (lam : Fin m → ℝ) : Prop :=
  (jointRevenues α β lam).Nonempty ∧ BddAbove (jointRevenues α β lam) ∧
  (Set.range (firstRevenue α β)).Nonempty ∧ BddAbove (Set.range (firstRevenue α β)) ∧
  (∃ S p, Feasible S ∧ revenue α β lam S p = jointValue α β lam) ∧
  (∃ p, firstRevenue α β p = firstValue α β) ∧ 0 < jointValue α β lam
end GaoImpatientMNL.Pricing

noncomputable section
namespace ActuarialValuation
noncomputable def exGumbelMaxCdf (location scale x : ℝ) : ℝ := Real.exp (-Real.exp (-(x-location)/scale))
end ActuarialValuation
end

open MeasureTheory
noncomputable section
namespace GaoImpatientMNL.Pricing
def HasGumbelLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (location scale : ℝ) : Prop :=
  IsProbabilityMeasure P ∧ Measurable X ∧ 0 < scale ∧
    ∀ x, P {ω | X ω ≤ x} = ENNReal.ofReal (ActuarialValuation.exGumbelMaxCdf location scale x)
end GaoImpatientMNL.Pricing
END IMPORTED LEAN FOR BLIND AUDIT -/

namespace GaoImpatientMNL.Pricing

/-- §2's mutually independent family. Index none is patience, some none is
one fixed outside utility, and some (some i) is product i. Patience Y is zero-based. -/
def customerFamily {Ω : Type*} {n m : ℕ} (U : Option (Fin n) → Ω → ℝ)
    (Y : Ω → Fin m) : Option (Option (Fin n)) → Ω → ℝ
  | none => fun ω => (Y ω).val
  | some i => U i

/-- §2: source laws and mutual independence, with arbitrary strictly positive tails. -/
def CustomerLaw {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (P : Measure Ω)
    (μ : Fin n → ℝ) (lam : Fin m → ℝ)
    (U : Option (Fin n) → Ω → ℝ) (Y : Ω → Fin m) : Prop :=
  HasGumbelLaw P (U none) 0 1 ∧
  (∀ i, HasGumbelLaw P (U (some i)) (μ i) 1) ∧ Measurable Y ∧
  iIndepFun (customerFamily U Y) P ∧
  (∀ k, P {ω | k ≤ Y ω} = ENNReal.ofReal (lam k)) ∧
  (∀ k, 0 < lam k)

/-- Operational purchase event. All earlier products must fail to exceed the
single outside utility. At this stage the best product exceeding it is bought;
ties among products are broken in favor of the smallest index. -/
def purchaseEvent {Ω : Type*} {n m : ℕ} (U : Option (Fin n) → Ω → ℝ)
    (Y : Ω → Fin m) (S : Fin m → Finset (Fin n)) (k : Fin m) (i : Fin n) : Set Ω :=
  {ω | i ∈ S k ∧ k ≤ Y ω ∧
    (∀ h, h < k → ∀ j ∈ S h, U (some j) ω ≤ U none ω) ∧
    U none ω < U (some i) ω ∧
    (∀ j ∈ S k, U (some j) ω ≤ U (some i) ω) ∧
    (∀ j ∈ S k, U (some j) ω = U (some i) ω → i ≤ j)}

end GaoImpatientMNL.Pricing


