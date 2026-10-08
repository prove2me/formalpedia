-- Prove2me | Definitions.Def_RobustPower_AdaptGap_Problems
-- name    : RobustPower_AdaptGap_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:40:52.22679+00:00
-- url     : https://prove2.me/theorems/fbca4568-af7c-4640-a22c-9233c7f12d23
-- title:
--   Two-stage robust and adaptive mixed-integer problems (1.5)–(1.6)
-- statement:
--   Let $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, $c\in\mathbb R^{n_1}$, and let each scenario $\omega\in\Omega$ provide a right-hand side $b(\omega)\in\mathbb R^m$ and a second-stage cost vector $d(\omega)\in\mathbb R^{n_2}$. For index sets $I_1\subseteq\{1,\dots,n_1\}$, $I_2\subseteq\{1,\dots,n_2\}$, first-stage decisions lie in $D_{I_1}$ and second-stage decisions lie in $D_{I_2}$, where $D_I$ is the set of nonnegative vectors whose coordinates in $I$ are integers (the paper's $\mathbb R^{n-p}_+\times\mathbb Z^p_+$ with $p=|I|$).
--
--   In $\Pi_{\mathrm{Rob}}(b,d)$ one pair $(x,y)$ satisfies $Ax+By\ge b(\omega)$ for every $\omega$ and has cost $c^Tx+\sup_\omega d(\omega)^Ty$. In $\Pi_{\mathrm{Adapt}}(b,d)$, one $x$ and a scenario-dependent policy $y(\omega)$ satisfy $Ax+By(\omega)\ge b(\omega)$ for every $\omega$ and have cost $c^Tx+\sup_\omega d(\omega)^Ty(\omega)$. Their optimal values are the infima of these costs over feasible decisions.
--
--   $$z_{\mathrm{Rob}}=\inf_{(x,y)\text{ robust feasible}}\left(c^Tx+\sup_\omega d(\omega)^Ty\right),\qquad z_{\mathrm{Adapt}}=\inf_{(x,y(\cdot))\text{ adaptive feasible}}\left(c^Tx+\sup_\omega d(\omega)^Ty(\omega)\right).$$
--
--   The paired uncertainty set is $I_{(b,d)}(\Omega)=\{(b(\omega),d(\omega)):\omega\in\Omega\}$. These are the objects compared by Theorem 5.1.
--
--   With $d(\omega)\equiv d$ constant the same objects are $\Pi_{\mathrm{Rob}}(b)$ and $\Pi_{\mathrm{Adapt}}(b)$ of (1.2)–(1.3).
--
--   **Formalization Note** The paper's $\max_\omega$ is a supremum in the extended reals $\overline{\mathbb R}$, so an unbounded worst-case cost is $+\infty$; the optimal values are infima in $\overline{\mathbb R}$, so infeasibility gives $+\infty$, and no optimal solution is assumed to exist. Over an empty scenario set the supremum is $-\infty$; the paper's scenario set is nonempty, and the theorems built on these objects either name a scenario or assume a symmetric or hypercube uncertainty set, which is nonempty. Feasibility is required for every scenario, as on the page. The integer coordinates form an arbitrary index set, equivalent to the paper's product form after relabelling; the page's $\mathbb Z^{n_2}_+$ in (1.4)–(1.6) is read as $\mathbb Z^{p_2}_+$, as in (1.1)–(1.3). Robust feasibility is the same predicate as in (1.2), since only the right-hand side is uncertain. The sign conditions $c\ge0$, $b(\omega)\ge0$, $d(\omega)\ge0$ of §1.1 are hypotheses of the theorems, not part of the definition.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, pp. 4–5, (1.5)–(1.6)

import Mathlib
import Definitions.Def_RobustPower_AdaptGap_SymmetricSets
import Definitions.Def_RobustPower_StochGap_Problems

open Matrix

namespace RobustPower.AdaptGap

/-- The paired right-hand-side and cost uncertainty set. -/
def scenarioSet {m n₂ : ℕ} {Ω : Type*} (b : Ω → Fin m → ℝ)
    (d : Ω → Fin n₂ → ℝ) : Set ((Fin m → ℝ) × (Fin n₂ → ℝ)) :=
  Set.range (fun ω => (b ω, d ω))

/-- Feasibility for the fully adaptive problem (1.6). -/
def AdaptFeasible {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) : Prop :=
  x ∈ RobustPower.StochGap.mixedIntDomain I₁ ∧
    ∀ ω, y ω ∈ RobustPower.StochGap.mixedIntDomain I₂ ∧ b ω ≤ A *ᵥ x + B *ᵥ y ω

/-- Worst-case cost in (1.5), as an extended real number. -/
noncomputable def robCost {n₁ n₂ : ℕ} {Ω : Type*}
    (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ) : EReal :=
  ((c ⬝ᵥ x : ℝ) : EReal) + ⨆ ω, ((d ω ⬝ᵥ y : ℝ) : EReal)

/-- Worst-case cost in (1.6), as an extended real number. -/
noncomputable def adaptCost {n₁ n₂ : ℕ} {Ω : Type*}
    (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) : EReal :=
  ((c ⬝ᵥ x : ℝ) : EReal) + ⨆ ω, ((d ω ⬝ᵥ y ω : ℝ) : EReal)

/-- Optimal robust value in (1.5), equal to `⊤` when infeasible. -/
noncomputable def zRob {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ)
    (_ : RobustPower.StochGap.RobFeasible A B b I₁ I₂ x y), robCost c d x y

/-- Optimal adaptive value in (1.6), equal to `⊤` when infeasible. -/
noncomputable def zAdapt {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂)) : EReal :=
  ⨅ (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ)
    (_ : AdaptFeasible A B b I₁ I₂ x y), adaptCost c d x y

end RobustPower.AdaptGap


