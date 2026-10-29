-- Prove2me | Definitions.Def_GaoImpatientMNL_Pricing_Relaxation
-- name    : GaoImpatientMNL_Pricing_Relaxation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:22:55.704733+00:00
-- url     : https://prove2.me/theorems/7e41195e-819e-4540-b830-c723924dee8d
-- title:
--   No-purchase coordinates and the extended-real smooth relaxation
-- statement:
--   For intrinsic utilities $\alpha$, let $T=\sum_i e^{\alpha_i}$ and $A_k=\sum_{i\in S_k}e^{\alpha_i}$. Stage prices $\rho$ give $q_t=1/(1+\sum_{k\le t}e^{-\beta\rho_k}A_k)$ and $q_0=1$. This is conditional no-purchase survival, not the unconditional probability of reaching a stage. On $\beta,A,b>0$ and $b<a$, price recovery is $[\log A-\log(1/b-1/a)]/\beta$; outside this meaningful domain the optional recovery returns none, leaving empty-stage prices arbitrary.
--
--   The closed feasible region is $1=q_0\ge q_1\ge\cdots\ge q_l\ge0$. A sequence encodes only its finite initial segment. A stage contribution is zero when its adjacent coordinates agree, minus infinity for a nonzero drop with no positive stage mass or no positive terminal coordinate, and otherwise $(a-b)[\log A-\log(1/b-1/a)]$. The sum is the infinite-patience objective (19) at $\beta=1$; a distinct objective includes weights $\lambda_k/\beta$ for (5).
--
--   For positive terminal coordinate define
--   $$R_T^{(l)}(q)=\sum_{k=1}^l(q_{k-1}-q_k)\log(q_{k-1}q_k)+(1-q_l)\log\frac{T}{1-q_l},$$
--   where the entropy term is explicitly zero at $q_l=1$. Set $R=-\infty$ at $q_l=0$. The optimal value is the extended-real supremum over the entire closed region, with $\widehat z_T^{(0)}=0$. A maximizer is feasible and dominates every feasible vector. Finally $G_T(x)=(\sqrt{1+4T/e^x}+1)/2$. These objects describe the source relaxation without assuming optimizer identities or approximation bounds. Outside the feasible region total-function values have no asserted source interpretation.
-- source:
--   Gao et al., DOI 10.1287/opre.2021.2127, held source.pdf, §§2,4 and Appendix F; PDF pp.6,11–16,45–51 (printed pp.6,11–16,ec8–ec14).

import Mathlib
import Definitions.Def_GaoImpatientMNL_Pricing_Model

open scoped BigOperators
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
END IMPORTED LEAN FOR BLIND AUDIT -/

namespace GaoImpatientMNL.Pricing

/-- (20): total intrinsic attraction of every product. -/
def totalAttraction {n : ℕ} (α : Fin n → ℝ) : ℝ := ∑ i, Real.exp (α i)

def stageAttraction {n m : ℕ} (α : Fin n → ℝ) (S : Fin m → Finset (Fin n))
    (k : Fin m) : ℝ := ∑ i ∈ S k, Real.exp (α i)

/-- Finite vectors q₀,…,qₗ encoded by a sequence whose later entries are ignored. -/
def QFeasible (l : ℕ) (q : ℕ → ℝ) : Prop :=
  q 0 = 1 ∧ ∀ k < l, 0 ≤ q (k + 1) ∧ q (k + 1) ≤ q k

/-- §4.1: conditional no-purchase probability through t stages, with q₀=1. -/
def stageQ {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (S : Fin m → Finset (Fin n)) (ρ : Fin m → ℝ) (t : ℕ) : ℝ :=
  1 / (1 + ∑ k ∈ Finset.univ.filter (fun k => k.val < t),
    Real.exp (-β * ρ k) * stageAttraction α S k)

/-- Price recovery only on its meaningful domain; none includes empty stages,
whose stage price is arbitrary, rather than log(0) giving a fake finite price. -/
def recoveredPrice (β A a b : ℝ) : Option ℝ :=
  if 0 < β ∧ 0 < A ∧ 0 < b ∧ b < a then
    some ((Real.log A - Real.log (1 / b - 1 / a)) / β) else none

/-- One term of (19), at β=1. Equal neighbors contribute zero; an active
stage with no intrinsic mass or a zero endpoint contributes minus infinity. -/
def relaxedStage (A a b : ℝ) : EReal :=
  if a = b then 0 else if A ≤ 0 ∨ b ≤ 0 ∨ a ≤ b then ⊥ else
    ((a - b) * (Real.log A - Real.log (1 / b - 1 / a)) : ℝ)

/-- Appendix F (19), distinct from the patience-weighted §4.1 objective. -/
def infinitePatienceRevenue {n m : ℕ} (α : Fin n → ℝ)
    (S : Fin m → Finset (Fin n)) (q : ℕ → ℝ) : EReal :=
  ∑ k : Fin m, relaxedStage (stageAttraction α S k) (q k.val) (q (k.val + 1))

/-- (5) on its feasible closed q domain. Off β>0 it returns bottom,
including when m=0. When beta>0 and m=0 it is the empty sum zero.
The unweighted infinitePatienceRevenue is the empty sum zero whenever m=0. -/
def patienceQRevenue {n m : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (lam : Fin m → ℝ) (S : Fin m → Finset (Fin n)) (q : ℕ → ℝ) : EReal :=
  if 0 < β then ∑ k : Fin m,
    (↑(lam k / β) : EReal) * relaxedStage (stageAttraction α S k) (q k.val) (q (k.val + 1))
  else ⊥

/-- The real formula in (20) on positive terminal q, with the entropy term
explicitly zero at qₗ=1. -/
def relaxationReal (T : ℝ) (l : ℕ) (q : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range l, (q k - q (k + 1)) * Real.log (q k * q (k + 1))) +
    if q l = 1 then 0 else (1 - q l) * Real.log (T / (1 - q l))

/-- (20), including all closed-boundary points in (22). -/
def relaxation (T : ℝ) (l : ℕ) (q : ℕ → ℝ) : EReal :=
  if q l = 0 then ⊥ else (relaxationReal T l q : EReal)

/-- (22), extended-real supremum; the l=0 convention is explicit.
Finite attainment and equality to the maximum are conclusions of F.2. -/
def relaxationValue (T : ℝ) (l : ℕ) : EReal :=
  if l = 0 then 0 else sSup {r | ∃ q, QFeasible l q ∧ r = relaxation T l q}

/-- Global maximizer over the whole closed monotone region. -/
def IsRelaxationMax (T : ℝ) (l : ℕ) (q : ℕ → ℝ) : Prop :=
  QFeasible l q ∧ ∀ r, QFeasible l r → relaxation T l r ≤ relaxation T l q

/-- Proposition F.5. -/
def G (T x : ℝ) : ℝ := (Real.sqrt (1 + 4 * T / Real.exp x) + 1) / 2

end GaoImpatientMNL.Pricing


