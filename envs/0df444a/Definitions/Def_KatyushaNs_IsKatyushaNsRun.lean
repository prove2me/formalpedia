-- Prove2me | Definitions.Def_KatyushaNs_IsKatyushaNsRun
-- name    : KatyushaNs_IsKatyushaNsRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:47:36.017259+00:00
-- url     : https://prove2.me/theorems/0185e926-e8e4-4102-896e-ff646459df7a
-- title:
--   A run of Katyusha$^{\mathrm{ns}}$ (Algorithm 2, Option I)
-- statement:
--   Let $f = \frac1n\sum_i f_i$, let $\psi$ have effective domain $D$, let $L > 0$, $x_0 \in \mathbb{R}^d$, and set $m = 2n$, $\tau_2 = 1/2$. For an index sequence $\omega = (\omega_0, \omega_1, \dots)$ with values in $\{1,\dots,n\}$, the iterates $x_k, y_k, z_k$ and snapshots $\widetilde x^s$ form a **run of Katyusha$^{\mathrm{ns}}$ along $\omega$** if
--
--   1. $y_0 = z_0 = \widetilde x^0 = x_0$;
--   2. for every epoch $s \ge 0$ and every $j \in \{0, \dots, m-1\}$, with $k = sm + j$:
--   $$x_{k+1} = \tau_{1,s} z_k + \tau_2 \widetilde x^s + (1 - \tau_{1,s} - \tau_2) y_k,$$
--   $$\widetilde\nabla_{k+1} = \nabla f(\widetilde x^s) + \nabla f_{\omega_k}(x_{k+1}) - \nabla f_{\omega_k}(\widetilde x^s),$$
--   $$z_{k+1} \in \operatorname*{arg\,min}_z \Big\{ \frac{1}{2\alpha_s}\|z - z_k\|^2 + \langle \widetilde\nabla_{k+1}, z\rangle + \psi(z) \Big\},$$
--   $$y_{k+1} \in \operatorname*{arg\,min}_y \Big\{ \frac{3L}{2}\|y - x_{k+1}\|^2 + \langle \widetilde\nabla_{k+1}, y\rangle + \psi(y) \Big\};$$
--   3. for every epoch $s \ge 0$, $\widetilde x^{s+1} = \frac1m \sum_{j=1}^m y_{sm+j}$.
--
--   Here $\tau_{1,s} = 2/(s+4)$ and $\alpha_s = 1/(3\tau_{1,s}L)$. The predicate asserts this for **every** index sequence $\omega$; the iterates are functions of $\omega$.
--
--   **Formalization Note** This is Option I of Algorithm 2, the variant the paper analyzes. The random index of iteration $k$ is $\omega_k$, with $\{1,\dots,n\}$ shifted to `Fin n`. The arg mins are the predicate `IsQuadProxMin`, so lower semicontinuity of $\psi$ is not assumed and the existence of the minimizers is part of the hypothesis. The value $x_0$ of the iterate sequence $x$ is unconstrained. Since the minimizers are unique for $L > 0$ and convex $\psi$, the iterates of iteration $k$ depend only on $\omega_0, \dots, \omega_{k-1}$.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Algorithm 2 (Option I), p. 15

import Mathlib
import Definitions.Def_KatyushaNs_svrgEst
import Definitions.Def_KatyushaNs_IsQuadProxMin
import Definitions.Def_KatyushaNs_tau1
import Definitions.Def_KatyushaNs_alphaS

namespace KatyushaNs

/-- **A run of Katyusha^ns (Algorithm 2, Option I) along every index sequence.**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Algorithm 2, p. 15 (PDF p. 16):
1: m ← 2n; 2: τ₂ ← 1/2; 3: y₀ = z₀ = x̃⁰ ← x₀;
4: for s ← 0 to S − 1 do 5: τ_{1,s} ← 2/(s+4), α_s ← 1/(3τ_{1,s}L); 6: μ^s ← ∇f(x̃^s);
7: for j ← 0 to m − 1 do 8: k ← (sm) + j;
9: x_{k+1} ← τ_{1,s}z_k + τ₂x̃^s + (1 − τ_{1,s} − τ₂)y_k;
10: ∇̃_{k+1} ← μ^s + ∇fi(x_{k+1}) − ∇fi(x̃^s) where i is randomly chosen from {1, 2, …, n};
11: z_{k+1} = arg min_z { 1/(2α_s) ‖z − z_k‖² + ⟨∇̃_{k+1}, z⟩ + ψ(z) };
12: Option I: y_{k+1} ← arg min_y { 3L/2 ‖y − x_{k+1}‖² + ⟨∇̃_{k+1}, y⟩ + ψ(y) };
15: x̃^{s+1} ← (1/m) Σ_{j=1}^m y_{sm+j}.

`IsKatyushaNsRun fi L D ψ x0 x y z xt` says: for **every** index sequence `ω : ℕ → Fin n`
(iteration `k` uses the index `ω k`), the iterates `x ω k`, `y ω k`, `z ω k` and the snapshots
`xt ω s` satisfy line 3 (`y₀ = z₀ = x̃⁰ = x₀`), lines 9, 11 and 12 for every epoch `s` and every
`j < m = 2n` with `k = s·(2n) + j`, and line 15 for every epoch `s`.

**Formalization Note.** Option I is the variant the paper analyzes ("we analyze only I").
The extended-valued `ψ` is encoded by its effective domain `D` and its finite values `ψ` on `D`;
the arg mins are the predicate `IsQuadProxMin` (line 11 with `κ = 1/α_s`, line 12 with
`κ = 3L`), so no lower semicontinuity of `ψ` is assumed and the existence of the arg mins is part
of the hypothesis that a run exists. The paper's random index `i ∈ {1, …, n}` drawn in iteration
`k` is `ω k : Fin n`. The epoch length is `m = 2n` and `τ₂ = 1/2`. `x ω 0` is not constrained
(the algorithm has no iterate `x₀` other than its input). Since the arg mins are unique for
`L > 0` and convex `ψ`, the values at iteration `k` depend only on `ω 0, …, ω (k − 1)`. -/
def IsKatyushaNsRun {d n : ℕ} (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x0 : EuclideanSpace ℝ (Fin d))
    (x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ ω : ℕ → Fin n,
    (y ω 0 = x0 ∧ z ω 0 = x0 ∧ xt ω 0 = x0) ∧
    (∀ s j : ℕ, j < 2 * n →
      x ω (s * (2 * n) + j + 1) =
          tau1 s • z ω (s * (2 * n) + j) + (1 / 2 : ℝ) • xt ω s +
            (1 - tau1 s - 1 / 2) • y ω (s * (2 * n) + j) ∧
        IsQuadProxMin D ψ (alphaS L s)⁻¹ (z ω (s * (2 * n) + j))
          (svrgEst fi (xt ω s) (x ω (s * (2 * n) + j + 1)) (ω (s * (2 * n) + j)))
          (z ω (s * (2 * n) + j + 1)) ∧
        IsQuadProxMin D ψ (3 * L) (x ω (s * (2 * n) + j + 1))
          (svrgEst fi (xt ω s) (x ω (s * (2 * n) + j + 1)) (ω (s * (2 * n) + j)))
          (y ω (s * (2 * n) + j + 1))) ∧
    (∀ s : ℕ, xt ω (s + 1) =
      (1 / (2 * n : ℝ)) • ∑ j ∈ Finset.range (2 * n), y ω (s * (2 * n) + j + 1))

end KatyushaNs


