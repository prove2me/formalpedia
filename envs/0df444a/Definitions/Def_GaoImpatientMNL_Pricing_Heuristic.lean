-- Prove2me | Definitions.Def_GaoImpatientMNL_Pricing_Heuristic
-- name    : GaoImpatientMNL_Pricing_Heuristic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:24:08.273821+00:00
-- url     : https://prove2.me/theorems/73c938a2-0376-4899-b191-bfbfebdf9289
-- title:
--   First-stage heuristic prices and the Lambert performance function
-- statement:
--   Let $W$ be the published nonnegative Lambert function, defined by choosing a nonnegative root of $we^w=z$ when one exists, and returning zero otherwise. For $T=\sum_i e^{\alpha_i}$, the explicit heuristic charges every product $(1+W(T/e))/\beta$ and offers all products in the first stage. Its optimality and the root specification are theorem conclusions, not definition fields.
--
--   For $x>0$ put
--   $$H(x)=\frac{(1+x)W(x(1+x))}{2(1+x)\log(1+x)-x},$$
--   and set $H(0)=1$. The definition uses the displayed quotient for all nonzero real inputs, but the mission uses only $x\ge0$. The minimum value is represented by the real infimum of $H([0,\infty))$; lower boundedness and attainment are asserted in Theorem F.6. The value at zero is the intended continuous extension, not the total real quotient $0/0$.
-- source:
--   Gao et al., DOI 10.1287/opre.2021.2127, held source.pdf, §§2,4 and Appendix F; PDF pp.6,11–16,45–51 (printed pp.6,11–16,ec8–ec14).

import Mathlib
import Definitions.Def_GaoImpatientMNL_Pricing_Relaxation
import Definitions.Def_SinglePointPricing_Det_Setting

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

open scoped BigOperators
noncomputable section
namespace GaoImpatientMNL.Pricing
def totalAttraction {n : ℕ} (α : Fin n → ℝ) : ℝ := ∑ i, Real.exp (α i)
def stageAttraction {n m : ℕ} (α : Fin n → ℝ) (S : Fin m → Finset (Fin n))
    (k : Fin m) : ℝ := ∑ i ∈ S k, Real.exp (α i)
def QFeasible (l : ℕ) (q : ℕ → ℝ) : Prop :=
  q 0 = 1 ∧ ∀ k < l, 0 ≤ q (k + 1) ∧ q (k + 1) ≤ q k
def stageQ {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (ρ : Fin m → ℝ) (t : ℕ) : ℝ :=
  1 / (1 + ∑ k ∈ Finset.univ.filter (fun k => k.val < t),
    Real.exp (-β * ρ k) * stageAttraction α S k)
def recoveredPrice (β A a b : ℝ) : Option ℝ :=
  if 0 < β ∧ 0 < A ∧ 0 < b ∧ b < a then
    some ((Real.log A - Real.log (1 / b - 1 / a)) / β) else none
def relaxedStage (A a b : ℝ) : EReal :=
  if a = b then 0 else if A ≤ 0 ∨ b ≤ 0 ∨ a ≤ b then ⊥ else
    ((a - b) * (Real.log A - Real.log (1 / b - 1 / a)) : ℝ)
def infinitePatienceRevenue {n m : ℕ} (α : Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (q : ℕ → ℝ) : EReal :=
  ∑ k : Fin m, relaxedStage (stageAttraction α S k) (q k.val) (q (k.val + 1))
def patienceQRevenue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (q : ℕ → ℝ) : EReal :=
  if 0 < β then ∑ k : Fin m,
    (↑(lam k / β) : EReal) * relaxedStage (stageAttraction α S k) (q k.val) (q (k.val + 1))
  else ⊥
def relaxationReal (T : ℝ) (l : ℕ) (q : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range l, (q k - q (k + 1)) * Real.log (q k * q (k + 1))) +
    if q l = 1 then 0 else (1 - q l) * Real.log (T / (1 - q l))
def relaxation (T : ℝ) (l : ℕ) (q : ℕ → ℝ) : EReal :=
  if q l = 0 then ⊥ else (relaxationReal T l q : EReal)
def relaxationValue (T : ℝ) (l : ℕ) : EReal :=
  if l = 0 then 0 else sSup {r | ∃ q, QFeasible l q ∧ r = relaxation T l q}
def IsRelaxationMax (T : ℝ) (l : ℕ) (q : ℕ → ℝ) : Prop :=
  QFeasible l q ∧ ∀ r, QFeasible l r → relaxation T l r ≤ relaxation T l q
def G (T x : ℝ) : ℝ := (Real.sqrt (1 + 4 * T / Real.exp x) + 1) / 2
end GaoImpatientMNL.Pricing

noncomputable section
namespace SinglePointPricing.Det
def lambertW (x : ℝ) : ℝ :=
  open Classical in
  if h : ∃ w : ℝ, 0 ≤ w ∧ w * Real.exp w = x then Classical.choose h else 0
end SinglePointPricing.Det
end
END IMPORTED LEAN FOR BLIND AUDIT -/

namespace GaoImpatientMNL.Pricing

/-- Appendix F, ec13: actual first-stage heuristic price for every product. -/
def heuristicPrice {n : ℕ} (α : Fin n → ℝ) (β : ℝ) : Fin n → ℝ :=
  fun _ => (1 + SinglePointPricing.Det.lambertW (totalAttraction α / Real.exp 1)) / β

/-- F.6's quotient with its continuous extension at zero. Only x≥0 is used. -/
def H (x : ℝ) : ℝ :=
  if x = 0 then 1 else
    (1 + x) * SinglePointPricing.Det.lambertW (x * (1 + x)) /
      (2 * (1 + x) * Real.log (1 + x) - x)

/-- The entire continuum [0,∞), not a grid; attainment is asserted in F.6. -/
def minH : ℝ := sInf (H '' Set.Ici 0)

end GaoImpatientMNL.Pricing


