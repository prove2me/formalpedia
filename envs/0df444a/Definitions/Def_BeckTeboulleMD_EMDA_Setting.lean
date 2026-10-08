-- Prove2me | Definitions.Def_BeckTeboulleMD_EMDA_Setting
-- name    : BeckTeboulleMD_EMDA_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T05:27:53.78365+00:00
-- url     : https://prove2.me/theorems/98bb985c-5722-44aa-9c17-8b01354d5ac1
-- title:
--   (3.10), (3.11), (5.27), EDA, pp. 170–174 — the distance B_ψ, SANP runs, the relative interior of Δ, the entropy ψ_e and EDA runs
-- statement:
--   This file fixes the objects of Beck and Teboulle's analysis of mirror descent. Throughout, $E$ is a real normed space (the paper's $\mathbb R^n$ with an arbitrary norm $\|\cdot\|$), $X \subseteq E$, and a "subgradient" $f'(x)$ is a continuous linear functional on $E$, so that $\langle u, f'(x)\rangle$ is the value of $f'(x)$ at $u$ and $\|f'(x)\|_*$ is its dual (operator) norm.
--
--   1. **The distance-like function** (3.10). For $\psi : E \to \mathbb R$ and $x, y \in E$,
--   $$B_\psi(x, y) = \psi(x) - \psi(y) - \langle x - y, \nabla\psi(y)\rangle,$$
--   where $\nabla\psi(y)$ is the derivative of $\psi$ at the second argument $y$.
--   2. **SANP runs** (3.11). Given $X$, $\psi$, a subgradient oracle $x \mapsto f'(x)$ and step sizes $(t_k)$, a sequence $(x^k)_{k \ge 1}$ is a run of the *subgradient algorithm with nonlinear projections* if for every $k \ge 1$: $t_k > 0$, $x^k \in X$, $\psi$ is differentiable at $x^k$, and
--   $$x^{k+1} \in \operatorname*{argmin}_{x \in X} \Big\{ \langle x, f'(x^k)\rangle + \frac{1}{t_k} B_\psi(x, x^k) \Big\}.$$
--   3. **The relative interior of the unit simplex.** With $\Delta = \{x \in \mathbb R^n : \sum_j x_j = 1,\ x \ge 0\}$, $\operatorname{int}\Delta = \{x \in \mathbb R^n : \sum_j x_j = 1,\ x_j > 0 \text{ for all } j\}$.
--   4. **The entropy** (5.27): $\psi_e(x) = \sum_{j=1}^n x_j \ln x_j$, with $0 \ln 0 = 0$.
--   5. **EDA runs** (p. 174). Given an oracle $x \mapsto f'(x) \in \mathbb R^n$ and a constant step $t$, a sequence $(x^s)_{s \ge 1}$ is a run of the *entropic descent algorithm* if for every $s \ge 1$ and every $j$,
--   $$x^{s+1}_j = \frac{x^s_j\, e^{-t f'_j(x^s)}}{\sum_{i=1}^n x^s_i\, e^{-t f'_i(x^s)}}.$$
--
--   These are the objects of the convergence analysis of Section 4 (Theorems 4.1 and 4.2) and of the entropic mirror descent algorithm of Section 5 (Theorem 5.1).
--
--   **Formalization Note** $B_\psi$ uses Lean's `fderiv`, which is $0$ where $\psi$ is not differentiable; every statement evaluates $B_\psi(\cdot, y)$ only where $\psi$ is differentiable at $y$, which a SANP run guarantees at every iterate. Iterates are indexed from $1$ as on the page; the value at index $0$ is unused. The SANP run is a predicate on sequences, not a choice of minimiser: it encodes the paper's assumption that the SANP sequence is well defined (p. 171) instead of the hypotheses "$X$ has nonempty interior" and "$x^1 \in \operatorname{int} X$", which fail for $X = \Delta$ in $\mathbb R^n$. The unit simplex $\Delta$ is Mathlib's `stdSimplex ℝ (Fin n)`. The entropy formula is total; the page's value $+\infty$ off $\Delta$ is never used, since every statement evaluates $\psi_e$ on $\Delta$ only. The EDA uses a constant step $t$, which is how Theorem 5.1 uses it (one step size for a fixed horizon $k$).
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003), pp. 170–174, (3.10), (3.11), (5.27), the EDA (p. 174); dual norm and well-definedness of SANP p. 171

import Mathlib

namespace BeckTeboulleMD.EMDA

/-- The distance-like function of (3.10), p. 170:
`B_ψ(x, y) = ψ(x) − ψ(y) − ⟨x − y, ∇ψ(y)⟩`, the pairing being the Fréchet derivative of `ψ` at the
**second** argument `y` applied to `x − y`. Lean's `fderiv` is `0` where `ψ` is not differentiable;
every statement using `bregman ψ x y` assumes differentiability of `ψ` at `y`. -/
noncomputable def bregman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E → ℝ) (x y : E) : ℝ :=
  ψ x - ψ y - fderiv ℝ ψ y (x - y)

/-- A run of the subgradient algorithm with nonlinear projections (SANP), (3.11), p. 170, indexed from
`1` as on the page (`x 1` is the starting point `x¹`; `x 0` is unused). For every `k ≥ 1`: the step
size `t k` is positive, the iterate `x k` lies in `X`, `ψ` is differentiable at `x k`, and `x (k + 1)`
minimises `u ↦ ⟨u, f′(x^k)⟩ + (1 / t_k) B_ψ(u, x^k)` over `X`, where `g (x k)` is the subgradient
`f′(x^k)` returned by the oracle, viewed as a continuous linear functional. The predicate encodes the
paper's assumption that the SANP sequence is well defined (p. 171). -/
def IsSANPRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ψ : E → ℝ) (g : E → E →L[ℝ] ℝ) (t : ℕ → ℝ) (x : ℕ → E) : Prop :=
  ∀ k, 1 ≤ k → 0 < t k ∧ x k ∈ X ∧ DifferentiableAt ℝ ψ (x k) ∧
    ∀ u ∈ X, g (x k) (x (k + 1)) + (1 / t k) * bregman ψ (x (k + 1)) (x k)
      ≤ g (x k) u + (1 / t k) * bregman ψ u (x k)

/-- The relative interior `int Δ = {x ∈ ℝⁿ : x_j > 0 ∀ j, ∑_j x_j = 1}` of the unit simplex
(Section 5, p. 173). The unit simplex `Δ` itself is Mathlib's `stdSimplex ℝ (Fin n)`. -/
def relIntSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ j, 0 < x j) ∧ ∑ j, x j = 1}

/-- The entropy function `ψ_e(x) = ∑_j x_j ln x_j` of (5.27), p. 173, with `0 ln 0 = 0` (Lean's
`Real.log 0 = 0`). The page sets `ψ_e = +∞` off `Δ`; this formula is total, and every statement
evaluates it only on `Δ`. -/
noncomputable def entropy {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ j, x j * Real.log (x j)

/-- A run of the entropic descent algorithm (EDA), p. 174, with constant step size `t`, indexed from
`1`: for every `s ≥ 1` and every coordinate `j`,
`x^{s+1}_j = x^s_j e^{−t g_j(x^s)} / ∑_i x^s_i e^{−t g_i(x^s)}`, where `g (x s)` is the subgradient
`f′(x^s)` returned by the oracle. -/
def IsEDARun {n : ℕ} (g : (Fin n → ℝ) → (Fin n → ℝ)) (t : ℝ) (x : ℕ → Fin n → ℝ) : Prop :=
  ∀ s, 1 ≤ s → ∀ j, x (s + 1) j =
    x s j * Real.exp (-(t * g (x s) j)) / ∑ i, x s i * Real.exp (-(t * g (x s) i))

end BeckTeboulleMD.EMDA


