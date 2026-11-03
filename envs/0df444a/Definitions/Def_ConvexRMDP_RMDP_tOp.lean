-- Prove2me | Definitions.Def_ConvexRMDP_RMDP_tOp
-- name    : ConvexRMDP_RMDP_tOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:28.152242+00:00
-- url     : https://prove2.me/theorems/2025c5a3-c53e-4222-aaa6-1c4d1c3b1073
-- title:
--   The operator $\tilde t$ of (4.5), the weights $\omega_b(s,a)$ and the scaled $\log_b$, $\exp_b$
-- statement:
--   For $b > 0$ the **scaled logarithm and exponential** are
--   $$
--   \log_b(z) = \frac{\log z}{b}, \qquad \exp_b(z') = \exp(b \cdot z'), \qquad z > 0,\ z' \in \mathbb R,
--   $$
--   applied componentwise to vectors. Here $b$ is not the base of the logarithm; it is the denominator in $z \mapsto \log(z)/b$.
--
--   For an sa-rectangular robust MDP $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ let $\omega_b(s,a) = \frac{1}{|\mathcal A|}\exp_b(r_{sa})$. The operator $\tilde t : (\mathbb R^*_+)^{\mathcal S} \to (\mathbb R^*_+)^{\mathcal S}$ is
--   $$
--   \tilde t(x)_s = \sum_{a \in \mathcal A} \omega_b(s,a) \min_{p \in \mathcal U_{sa}} \prod_{s' \in \mathcal S} x_{s'}^{\gamma p_{s'}}, \qquad s \in \mathcal S.
--   $$
--
--   Under the change of variables $x = \exp_b(v)$ the operator $\tilde t$ is conjugate to the regularized robust Bellman operator, $\tilde T = \log_b \circ \tilde t \circ \exp_b$, and the constraints $1 \le x \le \tilde t(x)$ define the feasible set of the convex program (4.7).
--
--   **Formalization Note** `logB b z` is $\log(z)/b$, not Mathlib's `Real.logb` (which is $\log z / \log b$). The operator `tOp` is a total function on `S → ℝ`; its values are the paper's only on vectors with positive entries, because the real power with a nonpositive base is not the paper's power. Every statement uses it only on positive vectors or on vectors with entries at least $1$. The minimum over $\mathcal U_{sa}$ is an infimum.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), §4.2, pp.12–13: logb and expb (p.12), (4.5) and ωb(s,a) (p.13)

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP

namespace ConvexRMDP

/-- The scaled exponential `exp_b(z) = exp(b · z)` (Grand-Clément & Petrik, arXiv:2209.10187v2,
§4.2, p.12). -/
noncomputable def expB (b z : ℝ) : ℝ := Real.exp (b * z)

/-- The scaled logarithm `log_b(z) = log(z)/b` (Grand-Clément & Petrik, arXiv:2209.10187v2, §4.2,
p.12). "Note that `b` is not the base of the logarithm": this is **not** Mathlib's `Real.logb`. It
is the paper's value for `z > 0`. -/
noncomputable def logB (b z : ℝ) : ℝ := Real.log z / b

namespace RMDP

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The weight `ω_b(s,a) = (1/|A|) exp_b(r_{sa})` (Grand-Clément & Petrik, arXiv:2209.10187v2,
p.13, after (4.5)). -/
noncomputable def omega (M : RMDP S A) (b : ℝ) (s : S) (a : A) : ℝ :=
  expB b (M.r s a) / (Fintype.card A : ℝ)

/-- **The operator `t̃`** of (4.5) (Grand-Clément & Petrik, arXiv:2209.10187v2, p.13):
`t̃(x)_s = ∑_a (1/|A|) exp_b(r_{sa}) min_{p ∈ 𝒰_{sa}} ∏_{s'} x_{s'}^{γ p_{s'}}`.

**Formalization Note.** The paper defines `t̃` on `(ℝ*₊)^S`; here it is a total function on `S → ℝ`
whose values are the paper's only for `x` with positive entries (`Real.rpow` with a nonpositive base
is not the paper's power). Every statement uses it only on positive vectors or on `x ≥ 1`. The
minimum over `𝒰_{sa}` is `sInf` (the set is nonempty and, for positive `x`, bounded below by `0`). -/
noncomputable def tOp (M : RMDP S A) (b : ℝ) (x : S → ℝ) : S → ℝ := fun s =>
  ∑ a, M.omega b s a * sInf ((fun p : S → ℝ => ∏ s', x s' ^ (M.γ * p s')) '' M.U s a)

end RMDP

end ConvexRMDP


