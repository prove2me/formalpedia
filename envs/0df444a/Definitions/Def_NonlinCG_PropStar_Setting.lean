-- Prove2me | Definitions.Def_NonlinCG_PropStar_Setting
-- name    : NonlinCG_PropStar_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:38.447365+00:00
-- url     : https://prove2.me/theorems/d49cd80c-a4b1-40ef-83d2-fe1951332fe4
-- title:
--   The conjugate gradient iteration (1.2)–(1.3), Assumptions 2.1, Wolfe steps, the Zoutendijk and sufficient descent conditions, Property (*) and the sets 𝒦^λ_{k,Δ}
-- statement:
--   This file fixes the objects of §1, §2 and §4 of Gilbert and Nocedal's report.
--
--   Let $E$ be a finite-dimensional real inner product space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, and let $f : E \to \mathbb R$ be the function to be minimized, with gradient $g = \nabla f$ taken with respect to that inner product. Sequences are indexed from $1$ as in the paper.
--
--   1. **Level set.** For a starting point $x_1$, $\mathcal L := \{x : f(x) \le f(x_1)\}$.
--   2. **Assumptions 2.1.** $\mathcal L$ is bounded, and there is an open set $\mathcal N \supseteq \mathcal L$ on which $f$ is continuously differentiable and its gradient is Lipschitz continuous: for some $L > 0$, $\|g(x) - g(\tilde x)\| \le L\|x - \tilde x\|$ for all $x, \tilde x \in \mathcal N$.
--   3. **The conjugate gradient iteration (1.2)–(1.3).** Sequences $(x_k)$, $(d_k)$ in $E$ and scalars $(\beta_k)$, $(\alpha_k)$ form a run if, writing $g_k := g(x_k)$,
--   $$d_1 = -g_1,\qquad d_k = -g_k + \beta_k d_{k-1}\ (k \ge 2),\qquad x_{k+1} = x_k + \alpha_k d_k,\ \alpha_k > 0\ (k \ge 1).$$
--   The scalar $\beta_k$ is arbitrary; particular methods choose it by a formula.
--   4. **Polak–Ribière scalar (1.5).** $\beta_k^{PR} = \langle g_k, g_k - g_{k-1}\rangle / \|g_{k-1}\|^2$.
--   5. **Wolfe conditions (2.4)–(2.5).** A step $\alpha$ along $d$ from $x$ satisfies $f(x + \alpha d) \le f(x) + \sigma_1 \alpha \langle g(x), d\rangle$ and $\langle g(x + \alpha d), d\rangle \ge \sigma_2 \langle g(x), d\rangle$.
--   6. **Zoutendijk condition (2.7).** $\sum_{k \ge 1} \cos^2\theta_k \|g_k\|^2 < \infty$, where $\cos\theta_k = -\langle g_k, d_k\rangle/(\|g_k\|\|d_k\|)$; equivalently $\sum_{k\ge1} \langle g_k, d_k\rangle^2/\|d_k\|^2 < \infty$.
--   7. **Sufficient descent condition (4.1).** $\langle g_k, d_k\rangle \le -\sigma_3 \|g_k\|^2$ for all $k \ge 1$.
--   8. **Property (\*)** (4.10)–(4.12). Whenever $0 < \gamma \le \|g_k\| \le \bar\gamma$ for all $k \ge 1$, there are constants $b > 1$ and $\lambda > 0$ such that for all $k \ge 2$
--   $$|\beta_k| \le b \qquad\text{and}\qquad \|s_{k-1}\| \le \lambda \implies |\beta_k| \le \frac{1}{2b},$$
--   where $s_{k-1} := x_k - x_{k-1}$.
--   9. **Unit directions.** $u_k := d_k/\|d_k\|$.
--   10. **Large-step index sets.** For $\lambda > 0$, $k \ge 1$ and $\Delta \ge 1$,
--   $$\mathcal K^\lambda_{k,\Delta} := \{ i : k \le i \le k + \Delta - 1,\ i \ge 2,\ \|s_{i-1}\| > \lambda \}.$$
--   11. **liminf.** $\liminf_{k\to\infty} \|g_k\| = 0$: for every $\varepsilon > 0$ and every $K$ there is $k \ge K$ with $\|g_k\| < \varepsilon$.
--
--   Property (\*) says that $\beta_k$ is bounded and becomes small when the step is small; it is the property shared with the Polak–Ribière method on which the convergence theory of §4 rests.
--
--   **Formalization Note** $E$ is any finite-dimensional real inner product space, since the paper uses "the scalar product used to compute the gradient" (p. 2), not necessarily the Euclidean one; `gradient f` is the gradient for that product. Index $0$ of every sequence is unused. The "neighbourhood $\mathcal N$" is taken open. Property (\*) quantifies over every pair $\gamma, \bar\gamma$ for which (4.10) holds, and the constants $b, \lambda$ may depend on $\gamma, \bar\gamma$ (as the paper's constants for the PR method do); if (4.10) holds for no pair, Property (\*) holds vacuously, as in the paper's "Under this assumption we say …". "For all $k$" in (4.11)–(4.12) means $k \ge 2$, where $\beta_k$ and $s_{k-1}$ exist. The condition $i \ge 2$ in $\mathcal K^\lambda_{k,\Delta}$ is taken from the paper's $\mathcal K^\lambda$ ("$i \ge 2$"), since $s_0$ does not exist. Lean's division returns $0$ at a zero denominator, so $\beta^{PR}_k$ is $0$ when $g_{k-1} = 0$ and $u_k = 0$ when $d_k = 0$; the theorems use them only where the denominators are nonzero. The Zoutendijk summand is written without $\cos\theta_k$, which avoids the undefined quotient at $g_k = 0$ or $d_k = 0$.
-- source:
--   Gilbert & Nocedal, Global convergence properties of conjugate gradient methods for optimization, INRIA Rapport de Recherche 1268 (June 1990), HAL inria-00075291v1, pp. 2–4 (§1 (1.1)–(1.5), §2 (2.1), Assumptions 2.1, (2.2), (2.4)–(2.5), (2.7)), p. 11 ((4.1)), p. 12 (u_k, Lemma 4.1), p. 13 (Property (*), (4.10)–(4.12)), p. 14 (𝒦^λ, 𝒦^λ_{k,Δ})

import Mathlib
import Definitions.Def_NonlinCG_FRBound_Setting

namespace NonlinCG.PropStar

/-!
Gilbert & Nocedal, *Global convergence properties of conjugate gradient methods for
optimization*, INRIA Rapport de Recherche 1268 (June 1990), HAL inria-00075291v1, §1, §2 and §4,
pp. 2–4 and 11–14: the problem (1.1), the conjugate gradient iteration (1.2)–(1.3), the
Polak–Ribière scalar (1.5), Assumptions 2.1, the Wolfe conditions (2.4)–(2.5), the Zoutendijk
condition (2.7), the sufficient descent condition (4.1), Property (*) (4.10)–(4.12), the unit
directions `u_k := d_k/‖d_k‖` (Lemma 4.1) and the index sets `𝒦^λ_{k,Δ}` (p. 14).

Conventions: `E` is a finite-dimensional real inner product space (the "scalar product used to
compute the gradient", p. 2), and `gradient f` is the gradient for that product. Sequences are
indexed from `1` as in the paper; index `0` is never used.
-/

open Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The sufficient descent condition (4.1) with constant `σ₃`:
`⟨g_k, d_k⟩ ≤ −σ₃‖g_k‖²` for all `k ≥ 1`. -/
def SufficientDescent (f : E → ℝ) (σ₃ : ℝ) (x d : ℕ → E) : Prop :=
  ∀ k ≥ 1, inner ℝ (NonlinCG.FRBound.g f x k) (d k) ≤ -σ₃ * ‖NonlinCG.FRBound.g f x k‖ ^ 2

/-- Property (*) (p. 13, (4.10)–(4.12)): whenever `0 < γ ≤ ‖g_k‖ ≤ γ̄` for all `k ≥ 1` (4.10),
there are constants `b > 1` and `λ > 0` (allowed to depend on `γ, γ̄`) such that for all `k ≥ 2`
(where `β_k` and `s_{k−1} = x_k − x_{k−1}` exist), `|β_k| ≤ b` (4.11) and
`‖s_{k−1}‖ ≤ λ ⟹ |β_k| ≤ 1/(2b)` (4.12). If the run never satisfies (4.10) the property holds
vacuously, as in the paper ("Under this assumption we say …"). -/
def PropertyStar (f : E → ℝ) (β : ℕ → ℝ) (x : ℕ → E) : Prop :=
  ∀ γ γbar : ℝ, 0 < γ → (∀ k ≥ 1, γ ≤ ‖NonlinCG.FRBound.g f x k‖ ∧ ‖NonlinCG.FRBound.g f x k‖ ≤ γbar) →
    ∃ b > 1, ∃ lam > 0, ∀ k ≥ 2,
      |β k| ≤ b ∧ (‖x k - x (k - 1)‖ ≤ lam → |β k| ≤ 1 / (2 * b))

/-- The unit direction `u_k := d_k/‖d_k‖` (Lemma 4.1, p. 12). Meaningful only when `d_k ≠ 0`
(Lean returns `0` at `d_k = 0`). -/
noncomputable def u (d : ℕ → E) (k : ℕ) : E := ‖d k‖⁻¹ • d k

/-- `𝒦^λ_{k,Δ} := {i ∈ ℕ* : k ≤ i ≤ k + Δ − 1, ‖s_{i−1}‖ > λ}` (p. 14), the indices of a block of
`Δ` consecutive iterates whose preceding step `s_{i−1} = x_i − x_{i−1}` exceeds `λ`. As in
`𝒦^λ := {i ∈ ℕ* : i ≥ 2, ‖s_{i−1}‖ > λ}` only indices `i ≥ 2` are counted, since `s₀` does not
exist in the paper. Used with `Δ ≥ 1`. -/
noncomputable def Kset (lam : ℝ) (x : ℕ → E) (k Δ : ℕ) : Finset ℕ :=
  (Finset.Icc k (k + Δ - 1)).filter (fun i => 2 ≤ i ∧ lam < ‖x i - x (i - 1)‖)

end NonlinCG.PropStar


