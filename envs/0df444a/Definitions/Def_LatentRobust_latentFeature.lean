-- Prove2me | Definitions.Def_LatentRobust_latentFeature
-- name    : LatentRobust_latentFeature
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:34.047028+00:00
-- url     : https://prove2.me/theorems/7e3f2819-2421-486c-9f8a-6f072c1b641f
-- title:
--   The latent generator $x=\varphi(Wz)$ and its standing assumptions
-- statement:
--   Features are generated from a low-dimensional latent vector $z\in\mathbb R^k$ by
--   $$
--   x=G(z)=\varphi(Wz),
--   $$
--   where $W\in\mathbb R^{d\times k}$ is a weight matrix and $\varphi:\mathbb R\to\mathbb R$ acts entrywise. The module also fixes the standard Gaussian law $\mathsf N(0,I_k)$ on $\mathbb R^k$ (independent standard normal coordinates).
--
--   The paper's standing assumptions on the generator, for a constant $c$, are:
--
--   1. the latent dimension is $k\ge 1$;
--   2. $W$ has full column rank, $\operatorname{rank}W=k$;
--   3. $\varphi$ is differentiable with $\varphi'(t)\ge c$ for every $t$ (with $c>0$, stated separately in each theorem).
--
--   Under these assumptions $\varphi$ is a strictly increasing bijection of $\mathbb R$ and $Wz$ determines $z$, so the feature determines the latent vector.
--
--   **Formalization Note** "Tall" ($k<d$) is not part of the assumption predicate; no statement of the mission needs it.
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, §2.2, p.6 ("G(z) = φ(Wz) with W ∈ R^{d×k} a tall full-rank weight matrix, and φ acting entry-wise ... with a derivative dφ/dt ≥ c")

import Mathlib

namespace LatentRobust

open MeasureTheory ProbabilityTheory

/-- The standard Gaussian law `N(0, I_k)` on `ℝ^k`: `k` independent standard normal
coordinates. -/
noncomputable def stdNormal (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun _ : Fin k => gaussianReal 0 1)

/-- The latent-manifold feature map `x = G(z) = φ(Wz)` (Javanmard, Mehrabi,
arXiv:2110.11950v2, §2.2, p.6), with `φ : ℝ → ℝ` acting entrywise. -/
def latentFeature {d k : ℕ} (W : Matrix (Fin d) (Fin k) ℝ) (φ : ℝ → ℝ) (z : Fin k → ℝ) :
    Fin d → ℝ :=
  fun i => φ ((W.mulVec z) i)

/-- The standing assumptions on the generator `G(z) = φ(Wz)` (Javanmard, Mehrabi,
arXiv:2110.11950v2, §2.2, p.6: "`W ∈ R^{d×k}` a tall full-rank weight matrix, and `φ` acting
entry-wise on vector inputs with a derivative `dφ/dt ≥ c`"), for a given constant `c`:

1. the latent dimension is at least one, `k ≥ 1`;
2. `W` has full column rank, `rank W = k`;
3. `φ` is differentiable with `φ'(t) ≥ c` for every `t`.

**Formalization Note** The positivity `c > 0` is a separate hypothesis of every theorem.
"Tall" (`k < d`) is not part of this predicate: no statement of the mission needs it, and the
theorems are stated for every `d`, which specializes to tall `W`. -/
def IsStandardGenerator {d k : ℕ} (W : Matrix (Fin d) (Fin k) ℝ) (φ : ℝ → ℝ) (c : ℝ) : Prop :=
  1 ≤ k ∧ W.rank = k ∧ Differentiable ℝ φ ∧ ∀ t, c ≤ deriv φ t

end LatentRobust


