-- Prove2me | Definitions.Def_SmoothCCP_Asymptotic_Optimization
-- name    : SmoothCCP_Asymptotic_Optimization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:45:46.719142+00:00
-- url     : https://prove2.me/theorems/91c025e3-6bb3-49ce-8992-9d2a8248e0bd
-- title:
--   p. 10 — optimal solution set S, optimal value v*, and the feasible set of (2.4)
-- statement:
--   The optimization objects of the asymptotic analysis.
--
--   For $f : \mathbb R^n \to \mathbb R$ and $A \subseteq \mathbb R^n$, the **set of optimal solutions** of $\min_{x\in A} f(x)$ is
--   $$\operatorname{opt}(f,A) = \{x \in A \mid f(x) \le f(y) \text{ for all } y \in A\},$$
--   and the **optimal value** is $\operatorname{val}(f,A) = \inf_{x\in A} f(x)$.
--
--   The **feasible set of the approximation (2.4)** at sample values $\xi_1,\dots,\xi_N$ and smoothing parameter $\varepsilon$ is
--   $$\{x \in X \mid F^N_\varepsilon(0;x) \ge 1-\alpha\} = X^{N,0}_{\varepsilon,\alpha},$$
--   the case $t = 0$, $\delta = \alpha$ of (3.2) (p. 9). With these, $S = \operatorname{opt}(f, X_\alpha)$ and $v^* = \operatorname{val}(f,X_\alpha)$ are the solution set and value of the chance-constrained program (1.1), and $S^N_\varepsilon$, $v^N_\varepsilon$ those of (2.4) (p. 10).
--
--   **Formalization Note** The paper writes the constraint of (2.4) as $Q^{1-\alpha}_\varepsilon(C^N(x)) \le 0$, where the smoothed quantile $Q^{1-\alpha}_\varepsilon$ is defined only when $(1-\alpha)N \notin \mathbb Z$ (Lemma 2.1). The proof of Theorem 3.5 uses the equivalent form $F^N_\varepsilon(0;x) \ge 1-\alpha$, which is defined for every $N$; it is the form used here. The optimal value is the real infimum `sInf (f '' A)`, which Lean sets to $0$ when $A$ is empty or $f$ is unbounded below on $A$; every theorem of the mission reads it only where the infimum is attained, or asserts the nonemptiness itself.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, p. 10 (definitions of S, S^N_ε, v*, v^N_ε; proof of Theorem 3.5, first sentence), p. 9 (remark after (3.2)), (1.1), (2.4)

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting

namespace SmoothCCP.Asymptotic

/-- p. 10: the set of optimal solutions of min_{x ∈ A} f(x) (S for (1.1), S^N_ε for (2.4)). -/
def optSet {n : ℕ} (f : (Fin n → ℝ) → ℝ) (A : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | x ∈ A ∧ ∀ y ∈ A, f x ≤ f y}

/-- p. 10: the optimal value inf_{x ∈ A} f(x) (v* for (1.1), v^N_ε for (2.4)). Read only where
`A` is nonempty and the infimum is attained; on `∅` the real `sInf` returns the junk value `0`. -/
noncomputable def optVal {n : ℕ} (f : (Fin n → ℝ) → ℝ) (A : Set (Fin n → ℝ)) : ℝ :=
  sInf (f '' A)

/-- p. 10, first sentence of the proof of Theorem 3.5, and p. 9 ("if δ = α and t = 0, then
X^{N,0}_{ε,α} corresponds to the feasible region of (2.4)"): the feasible set
{x ∈ X | F^N_ε(0; x) ≥ 1 − α} of the approximation (2.4), on sample values `ξs`. -/
def saaFeasible {n N : ℕ} {Ξ : Type} (C : (Fin n → ℝ) → Ξ → ℝ) (X : Set (Fin n → ℝ))
    (ε : ℝ) (γ : ℝ → ℝ) (ξs : Fin N → Ξ) (α : ℝ) : Set (Fin n → ℝ) :=
  SmoothCCP.Feasibility.sampleFeasible C X ε γ ξs 0 α

end SmoothCCP.Asymptotic


