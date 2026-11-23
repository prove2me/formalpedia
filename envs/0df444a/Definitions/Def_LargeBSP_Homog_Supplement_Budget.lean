-- Prove2me | Definitions.Def_LargeBSP_Homog_Supplement_Budget
-- name    : LargeBSP_Homog_Supplement_Budget
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T16:52:56.248653+00:00
-- url     : https://prove2.me/theorems/c2377c2e-45a0-4766-af37-4cc2cf04e04d
-- title:
--   §5.3, p. 20, (22)–(24) — choice under a budget, profit, benchmark; menus of Theorems 5 and B1
-- statement:
--   Bundle-size pricing for a customer with a budget $b$ and identical marginal cost $c$.
--
--   1. **Choice (22).** The customer may take size $0$ for free or any offered size $n\le N$ with $p(n)\le b$, and buys a size $\zeta(X,p,b)$ maximizing $V_N(n)-p(n)$ among these. The smallest maximizer is chosen.
--   2. **Profit (23).** $\pi(p,b)=p(n)-nc$ when the chosen size is $n\ge1$, and $0$ when it is $0$. The expected profit is $\mathbb E[\pi(p,b)]$.
--   3. **Benchmark (24).** With $V_N(n,b)=\min(V_N(n),b)$, it is
--   $$\mathbb E\Bigl[\max_{n=0,\dots,N}\bigl(V_N(n,b)-nc\bigr)\Bigr].$$
--   4. **Optimum.** The supremum of $\mathbb E[\pi(p,b)]$ over menus with prices in $\mathbb R_+\cup\{\infty\}$.
--   5. **Menu of Theorem 5.** With $t=n/N$, size $n$ costs $N\bar V(t)-h(t)g(N)$ if $t\le t^\star$ and is not offered otherwise.
--   6. **Menu of Theorem B1.** Size $n\le K_b$ costs $n\eta-h(n)d(N)$, and larger sizes are not offered.
--
--   Neither menu depends on the budget, which the firm does not observe.
--
--   **Formalization Note** Entry $0$ of a menu is ignored and no purchase always costs $0$. The tie rule between sizes is the one of the model's unconstrained choice. The benchmark's maximum is over a nonempty finite set.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), SHA-256 1dfcad7675689de2118550b720b7488b45737ecd5ee5cd6085e5b5d0250d40cd, §5.3, (22)–(24), p. 20; Theorem 5 (menu), p. 21; Theorem B1 (menu), p. A14

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LargeBSP.Homog.Supplement

/-- (22): zero plus finite, affordable sizes, with the inherited no-purchase entry. -/
noncomputable def affordable (N : ℕ) (p : Menu) (b : ℝ) : Finset ℕ :=
  insert 0 ((offered N p).filter (fun n => price p n ≤ b))

/-- Smallest surplus maximizer among affordable sizes, the base size tie convention. -/
noncomputable def budgetChoice (x : ℕ → ℝ) (N : ℕ) (p : Menu) (b : ℝ) : ℕ :=
  sInf {n : ℕ | n ∈ affordable N p b ∧
    ∀ k ∈ affordable N p b, surplus x N p k ≤ surplus x N p n}

/-- (23), homogeneous marginal cost and zero payoff at no purchase. -/
noncomputable def budgetProfit (x : ℕ → ℝ) (c : ℝ) (N : ℕ) (p : Menu) (b : ℝ) : ℝ :=
  if budgetChoice x N p b = 0 then 0 else
    price p (budgetChoice x N p b) - (budgetChoice x N p b : ℝ) * c

noncomputable def budgetExpProfit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (c : ℝ) (N : ℕ) (p : Menu) (b : ℝ) : ℝ :=
  ∫ ω, budgetProfit (fun i => X i ω) c N p b ∂P

/-- Restricted valuation V_N(n,b) in Section 5.3. -/
noncomputable def restrictedValue (x : ℕ → ℝ) (N n : ℕ) (b : ℝ) : ℝ :=
  min (V x N n) b

/-- The expectation is OUTSIDE the finite maximum in (24), (25), and (B1).
The nonempty finite range includes n=0, so the real supremum is never a junk value. -/
noncomputable def budgetBenchmark {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (c : ℝ) (N : ℕ) (b : ℝ) : ℝ :=
  ∫ ω, ((Finset.range (N + 1)).image
    (fun n => restrictedValue (fun i => X i ω) N n b - (n : ℝ) * c)).sup' (by simp) id ∂P

/-- The optimal budget-constrained BSP value, with the original nonnegative menu domain. -/
noncomputable def budgetOptProfit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (c : ℝ) (N : ℕ) (b : ℝ) : ℝ :=
  ⨆ p : {p : Menu // IsBSPMenu p}, budgetExpProfit P X c N p.1 b

/-- The full integer-grid menu of Theorem 5. It contains no budget parameter. Entry 0 is ignored. -/
noncomputable def scalingBudgetMenu (ν : Measure ℝ) (c : ℝ)
    (g : ℕ → ℝ) (h : ℝ → ℝ) (N : ℕ) : Menu :=
  fun n => if (n : ℝ) / N ≤ tstar ν c then
    (((N : ℝ) * Vlim ν ((n : ℝ) / N) - h ((n : ℝ) / N) * g N) : WithTop ℝ)
    else ⊤

/-- The finite-size, budget-independent menu of Theorem B1. -/
noncomputable def endpointMenu (η : ℝ) (K : ℕ) (d : ℕ → ℝ) (h : ℕ → ℝ) (N : ℕ) : Menu :=
  fun n => if n ≤ min K N then (((n : ℝ) * η - h n * d N) : WithTop ℝ) else ⊤

end LargeBSP.Homog.Supplement


