-- Prove2me | Definitions.Def_RobustSDP_Uniqueness_Hypotheses
-- name    : RobustSDP_Uniqueness_Hypotheses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:04:46.577315+00:00
-- url     : https://prove2.me/theorems/426f1d7b-8eb1-45f0-a4a5-5caa58de27d7
-- title:
--   Hypotheses H1–H3 of §4.1 and the quadratic growth condition for the SDP (15)
-- statement:
--   This file states the hypotheses of §4.1 of El Ghaoui, Oustry and Lebret (1998) and the quadratic growth condition of §4.3, for the SDP (15) with data $F_i$, $R_i$, $L$ and objective vector $c$ (see the definition file for $\mathcal{F}$, $F(x)$ and $R(x)$).
--
--   1. **Symmetry** (standing assumption of (1)): $F_0, \dots, F_m$ are symmetric.
--   2. **H1 (Slater).** Problem (15) is strictly feasible: $\mathcal{F}(x,\tau) \succ 0$ for some $(x,\tau)$.
--   3. **H2 (inf-compactness).** For every $M \in \mathbb{R}$ the sublevel set
--   $$\{(x,\tau) \in \mathbb{R}^m\times\mathbb{R} : \mathcal{F}(x,\tau) \succeq 0,\ c^T x \le M\}$$
--   is bounded; equivalently, every unbounded sequence of feasible points $(x_k,\tau_k)$ has objectives $c^T x_k \to +\infty$ along it.
--   4. **H3(a).** There is a subspace $N \subsetneq \mathbb{R}^n$ such that
--   $$\ker\Bigl(\lambda R_0 + \sum_{i=1}^m x_i R_i\Bigr) = N \quad\text{for every } (\lambda, x) \ne (0,0).$$
--   5. **H3(b).** For every $x$, the stacked matrix $\begin{bmatrix} L^T \\ R(x)\end{bmatrix} \in \mathbb{R}^{(p+q)\times n}$ has full column rank.
--   6. **Quadratic growth condition (QGC)** at a point $y^\star = (x^\star, \tau^\star)$: there are $\alpha > 0$ and $\varepsilon > 0$ such that every feasible $y = (x,\tau)$ with $\|y - y^\star\| < \varepsilon$ satisfies
--   $$c^T x \ \ge\ c^T x^\star + \alpha\, \|y - y^\star\|^2 ,$$
--   where $\|y - y^\star\|^2 = \sum_i (x_i - x_i^\star)^2 + (\tau - \tau^\star)^2$ is the squared Euclidean distance in $\mathbb{R}^{m+1}$.
--
--   These are the hypotheses of Theorem 4.2 and the property it concludes.
--
--   **Formalization Note** H2 is the paper's "inf-compact" read as bounded sublevel sets of the feasible set in $(x,\tau)$; the paper's literal wording ("any unbounded sequence of feasible points produces an unbounded sequence of objectives") is intended in this sense for a minimisation, as its claim that H1 and H2 ensure existence of optimal points shows. Full column rank in H3(b) is stated as injectivity of $\xi \mapsto (L^T\xi, R(x)\xi)$. The paper writes the QGC as $d^Ty \ge d^Ty_{\mathrm{opt}} + \alpha\|y-y_{\mathrm{opt}}\|^2 + o(\|y-y_{\mathrm{opt}}\|^2)$ for feasible $y$, which is equivalent to the local form used here (with a smaller $\alpha$); it is stated for (15) directly, since near $y^\star$ (with $\tau^\star > 0$) feasibility for (15) and for (16) coincide.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 33, Eq. (1) (symmetry); p. 38, §4.1, Hypotheses H1, H2, H3(a), H3(b); p. 39, §4.3, the quadratic growth condition

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model

open Matrix

namespace RobustSDP.Uniqueness

namespace SDPData

variable {m n p q : ℕ} (D : SDPData m n p q)

/-- Standing assumption of Eq. (1), p. 33: the matrices `F₀, …, F_m` are symmetric. -/
def Symmetric : Prop :=
  D.F0.IsSymm ∧ ∀ i, (D.Fs i).IsSymm

/-- Hypothesis H1 (p. 38), the Slater condition: (15) is strictly feasible,
`𝓕(x, τ) ≻ 0` for some `(x, τ)`. -/
def Slater : Prop :=
  ∃ (x : Fin m → ℝ) (τ : ℝ), (D.lmi x τ).PosDef

/-- Hypothesis H2 (p. 38), inf-compactness of (15) with objective `cᵀx`: every sublevel set
`{(x, τ) feasible | cᵀx ≤ M}` is bounded in `ℝ^m × ℝ`. -/
def InfCompact (c : Fin m → ℝ) : Prop :=
  ∀ M : ℝ, Bornology.IsBounded {y : (Fin m → ℝ) × ℝ | D.Feasible y ∧ c ⬝ᵥ y.1 ≤ M}

/-- Hypothesis H3(a) (p. 38): the nullspace of `λR₀ + ∑ xᵢRᵢ` is the same subspace `N` for every
`(λ, x) ≠ (0, 0)`, and `N` is not the whole space `ℝⁿ`. -/
def H3a : Prop :=
  ∃ N : Submodule ℝ (Fin n → ℝ), N ≠ ⊤ ∧
    ∀ (lam : ℝ) (x : Fin m → ℝ), (lam ≠ 0 ∨ x ≠ 0) →
      LinearMap.ker (Matrix.toLin' (D.pencil lam x)) = N

/-- Hypothesis H3(b) (p. 38): for every `x`, the stacked `(p+q) × n` matrix `[Lᵀ; R(x)]` has full
column rank, i.e. `ξ ↦ [Lᵀξ; R(x)ξ]` is injective. -/
def H3b : Prop :=
  ∀ x : Fin m → ℝ, Function.Injective (Matrix.fromRows D.Lᵀ (D.R x)).mulVec

/-- Squared Euclidean distance on `ℝ^m × ℝ = ℝ^{m+1}`: `‖y − y'‖² = ∑ᵢ (xᵢ − x'ᵢ)² + (τ − τ')²`. -/
def sqDist (y y' : (Fin m → ℝ) × ℝ) : ℝ :=
  ∑ i, (y.1 i - y'.1 i) ^ 2 + (y.2 - y'.2) ^ 2

/-- The quadratic growth condition (QGC, §4.3, p. 39) for (15) at a point `y⋆`: there are `α > 0`
and a Euclidean neighbourhood of radius `ε > 0` of `y⋆` in which every feasible `y` satisfies
`cᵀx ≥ cᵀx⋆ + α‖y − y⋆‖²`. -/
def QGC (c : Fin m → ℝ) (ystar : (Fin m → ℝ) × ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ y : (Fin m → ℝ) × ℝ, D.Feasible y →
    sqDist y ystar < ε ^ 2 → c ⬝ᵥ ystar.1 + α * sqDist y ystar ≤ c ⬝ᵥ y.1

end SDPData

end RobustSDP.Uniqueness


