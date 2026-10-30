-- Prove2me | Definitions.Def_GoldenRatioVI_IsEGRAALRun
-- name    : GoldenRatioVI_IsEGRAALRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:23:21.856933+00:00
-- url     : https://prove2.me/theorems/530f2598-a513-4371-8930-dccc786b6cab
-- title:
--   A run of Algorithm 1 (Explicit Golden Ratio Algorithm, EGRAAL)
-- statement:
--   Let $g:\mathcal E\to(-\infty,+\infty]$ have domain $D$, let $F:\mathcal E\to\mathcal E$, and let $\varphi,\lambda_0,\bar\lambda\in\mathbb R$. Sequences $(z^k)_{k\ge0}$, $(\bar z^k)_{k\ge0}$ in $\mathcal E$ and $(\lambda_k)_{k\ge0}$, $(\theta_k)_{k\ge0}$ in $\mathbb R$ form a **run of Algorithm 1** if $\bar z^0=z^1$, $\lambda_0$ is the given initial stepsize, $\theta_0=1$, and for every $k\ge1$:
--
--   1. $\lambda_k$ is given by the stepsize rule (15) from $\lambda_{k-1}$, $\theta_{k-1}$, $z^k$, $z^{k-1}$;
--   2. $\bar z^k=\dfrac{(\varphi-1)z^k+\bar z^{k-1}}{\varphi}$ (16);
--   3. $z^{k+1}=\operatorname{prox}_{\lambda_k g}\big(\bar z^k-\lambda_kF(z^k)\big)$ (17);
--   4. $\theta_k=\dfrac{\lambda_k}{\lambda_{k-1}}\,\varphi$.
--
--   The starting points $z^0,z^1\in\mathcal E$ are arbitrary. Each iteration evaluates $F$ once and the proximal operator once.
--
--   **Formalization Note** Indices are the paper's; every $k-1$ occurs under $k\ge1$. The parameter conditions $\varphi\in(1,\phi]$, $\lambda_0>0$, $\bar\lambda>0$ are hypotheses of the theorems, not part of the run.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (2018), §2.1, p. 5, Algorithm 1 (eqs. (15)–(17) and step 3)

import Mathlib
import Definitions.Def_GoldenRatioVI_IsProx
import Definitions.Def_GoldenRatioVI_egraalStep

namespace GoldenRatioVI

/-- **A run of Algorithm 1 (Explicit Golden Ratio Algorithm, EGRAAL).**
Malitsky, *Golden Ratio Algorithms for Variational Inequalities*, preprint (2018), §2.1, p. 5,
Algorithm 1: "Input: Choose z0, z1 ∈ E, λ0 > 0, φ ∈ (1, ϕ], λ̄ > 0. Set z̄0 = z1, θ0 = 1,
ρ = 1/φ + 1/φ². For k ≥ 1 do 1. Find the stepsize: λk = min{ρλk−1, φθk−1/(4λk−1)
‖zk − zk−1‖²/‖F(zk) − F(zk−1)‖², λ̄} (15) 2. Compute the next iterates: z̄k = ((φ − 1)zk + z̄k−1)/φ
(16), zk+1 = prox_{λk g}(z̄k − λkF(zk)) (17) 3. Update: θk = λk/λk−1 φ."

`IsEGRAALRun D g F phi lam0 lbar z zbar lam theta` says: `zbar 0 = z 1`, `lam 0 = lam0`,
`theta 0 = 1`, and for every `k ≥ 1`:
1. `lam k = egraalStep F phi (lam (k−1)) (theta (k−1)) lbar (z k) (z (k−1))` (rule (15));
2. `zbar k = phi⁻¹ • ((phi − 1) • z k + zbar (k−1))` (16);
3. `z (k+1)` is `prox_{lam k · g}(zbar k − lam k • F (z k))` (17);
4. `theta k = lam k / lam (k−1) * phi` (step 3).

**Formalization Note.** Indices are the paper's. The starting points `z 0, z 1 ∈ E` are free (the
input `z⁰, z¹`). Every `k − 1` is guarded by `1 ≤ k`. The prox step is the minimizer predicate
`IsProx` applied to `λ_k g` with domain `D`. The parameter conditions (`1 < phi ≤ ϕ`, `lam0 > 0`,
`lbar > 0`) are hypotheses of the theorems, not part of the run. -/
def IsEGRAALRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Set E) (g : E → ℝ) (F : E → E) (phi lam0 lbar : ℝ)
    (z zbar : ℕ → E) (lam theta : ℕ → ℝ) : Prop :=
  zbar 0 = z 1 ∧ lam 0 = lam0 ∧ theta 0 = 1 ∧
    ∀ k : ℕ, 1 ≤ k →
      lam k = egraalStep F phi (lam (k - 1)) (theta (k - 1)) lbar (z k) (z (k - 1)) ∧
      zbar k = phi⁻¹ • ((phi - 1) • z k + zbar (k - 1)) ∧
      IsProx D (fun x => lam k * g x) (zbar k - lam k • F (z k)) (z (k + 1)) ∧
      theta k = lam k / lam (k - 1) * phi

end GoldenRatioVI


