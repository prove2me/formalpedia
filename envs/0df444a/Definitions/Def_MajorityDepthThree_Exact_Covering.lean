-- Prove2me | Definitions.Def_MajorityDepthThree_Exact_Covering
-- name    : MajorityDepthThree_Exact_Covering
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:58.616011+00:00
-- url     : https://prove2.me/theorems/7984466f-50b7-495c-89b7-3cdf9886da4d
-- title:
--   Finite weighted covering and packing programs
-- statement:
--   Let $\mathcal A$ be a finite family of finite subsets of a variable set. A weight is a real function on subsets; only its values on $\mathcal A$ enter either program. For real parameters $R,Q>0$, define
--
--   $$\operatorname{cost}_{\mathcal A,R}(f)=\sum_{U\in\mathcal A}f(U)R^{|U|},\qquad
--   \operatorname{cov}_{\mathcal A,Q}(f,S)=\sum_{U\in\mathcal A,\ U\subseteq S}f(U)Q^{|S|-|U|}.$$
--
--   A covering weight is feasible when it is nonnegative on $\mathcal A$ and has coverage at least one for every $S\in\mathcal A$. Its value $C_{\mathcal A}(R,Q)$ is the infimum of its costs. Covering optimality means feasibility and cost no greater than any feasible weight. The packing program has nonnegative weights $g$ and the constraints
--
--   $$\sum_{U\in\mathcal A,\ T\subseteq U}g(U)2^{-|U\setminus T|}\le1\quad(T\in\mathcal A).$$
--
--   Its value $D_{\mathcal A}(R)$ is the supremum of the same weighted objective; packing optimality reverses the objective comparison. The reduction uses $Q=(2R)^{-1}$. For Section 5 the fixed constants are $p=\sqrt{3/2}$, $r=p/2$, $q=1/p$, and $c_0=1$, $c_1=(2-q)^{-1}$, $c_2=c_1^2$, $c_3=r$.
--
--   These are the actual finite programs, independently of any desired bound. Attainment and duality are mathematical conclusions of the bridge item, never fields assumed of a formula. At positive parameters both objectives are finite; for an empty family both values are zero, and for $\{\varnothing\}$ both are one. Outside the stated positive parameter domains the real infimum/supremum uses Lean's total convention, which no theorem relies upon.
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), pp.11–12, (DLP-2), (P); p.16, constants before Theorem 5.15

import Definitions.Def_MajorityDepthThree_Exact_CNF

set_option autoImplicit false

namespace MajorityDepthThree.Exact

variable {α : Type} [DecidableEq α]

abbrev Family (α : Type) := Finset (Finset α)
abbrev Weight (α : Type) := Finset α → ℝ

noncomputable def cost (A : Family α) (r : ℝ) (f : Weight α) : ℝ :=
  ∑ U ∈ A, f U * r ^ U.card

noncomputable def contribution (A : Family α) (q : ℝ) (f : Weight α) (S : Finset α) : ℝ := by
  classical
  exact ∑ U ∈ A.filter (fun U => U ⊆ S), f U * q ^ (S.card - U.card)

def CoverFeasible (A : Family α) (q : ℝ) (f : Weight α) : Prop :=
  (∀ U ∈ A, 0 ≤ f U) ∧ ∀ S ∈ A, 1 ≤ contribution A q f S

noncomputable def coverValue (A : Family α) (r q : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ f : Weight α, CoverFeasible A q f ∧ cost A r f = v}

def CoverOptimal (A : Family α) (r q : ℝ) (f : Weight α) : Prop :=
  CoverFeasible A q f ∧ ∀ g, CoverFeasible A q g → cost A r f ≤ cost A r g

noncomputable def packingLoad (A : Family α) (f : Weight α) (T : Finset α) : ℝ := by
  classical
  exact ∑ U ∈ A.filter (fun U => T ⊆ U), f U * (2 : ℝ) ^ (-(U \ T).card : ℤ)

def PackingFeasible (A : Family α) (f : Weight α) : Prop :=
  (∀ U ∈ A, 0 ≤ f U) ∧ ∀ T ∈ A, packingLoad A f T ≤ 1

noncomputable def packingValue (A : Family α) (r : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ f : Weight α, PackingFeasible A f ∧ cost A r f = v}

def PackingOptimal (A : Family α) (r : ℝ) (f : Weight α) : Prop :=
  PackingFeasible A f ∧ ∀ g, PackingFeasible A g → cost A r g ≤ cost A r f

noncomputable def p : ℝ := Real.sqrt (3 / 2)
noncomputable def r : ℝ := p / 2
noncomputable def q : ℝ := 1 / p
noncomputable def c₀ : ℝ := 1
noncomputable def c₁ : ℝ := 1 / (2 - q)
noncomputable def c₂ : ℝ := c₁ ^ 2
noncomputable def c₃ : ℝ := r

end MajorityDepthThree.Exact


