-- Prove2me | Definitions.Def_SteuerChoo_Discrete_Tchebycheff
-- name    : SteuerChoo_Discrete_Tchebycheff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:44:01.621646+00:00
-- url     : https://prove2.me/theorems/725fd760-d94f-4c81-86f5-25ceacc94a36
-- title:
--   Steuer–Choo §§2–3: weighted and augmented weighted Tchebycheff values and the sets Φ(α)
-- statement:
--   Fix $k \ge 1$, weights $\lambda \in \mathbb R^k$, a reference vector $z^* \in \mathbb R^k$ and a scalar $\rho$. For a criterion vector $z \in \mathbb R^k$ define the *weighted Tchebycheff value* and the *augmented weighted Tchebycheff value*
--   $$T_\lambda(z) = \max_{1\le i\le k} \lambda_i (z^*_i - z_i), \qquad A_{\lambda,\rho}(z) = \max_{1\le i\le k} \lambda_i (z^*_i - z_i) + \rho\, e^{\mathsf T}(z^* - z),$$
--   where $e$ is the vector of ones. $T_\lambda(z)$ is the minimal $\alpha$ in the weighted Tchebycheff program
--   $$\min\{\alpha\} \quad \text{s.t.} \quad \alpha \ge \lambda_i(z^*_i - z_i),\ 1 \le i \le k,$$
--   at the criterion vector $z$, and $A_{\lambda,\rho}(z)$ is the minimal objective value $\alpha + \rho\, e^{\mathsf T}(z^*-z)$ of the augmented weighted Tchebycheff program at $z$. So "$z$ minimizes the (augmented) weighted Tchebycheff program over $Z$" means that $z \in Z$ minimizes $T_\lambda$ (resp. $A_{\lambda,\rho}$) over $Z$.
--
--   For $\alpha \in \mathbb R$ define
--   $$\Phi(\alpha) = \{z \in \mathbb R^k \mid z_i \ge z^*_i - \alpha/\lambda_i \text{ for every } i \text{ with } \lambda_i > 0\}.$$
--   These are the level sets of the weighted Tchebycheff program: $z \in \Phi(\alpha)$ exactly when $\lambda_i(z^*_i - z_i) \le \alpha$ for every $i$ with $\lambda_i > 0$.
--
--   **Formalization Note** The program variable $\alpha$ is eliminated by taking its minimal value at each $z$, and the decision variables $x$ with $f_i(x) = z_i$ are eliminated because the programs are stated over $Z = f(S)$. The paper's metric uses $|z^*_i - z_i|$; the programs use $z^*_i - z_i$, and the two agree on $Z$ when $z^*$ is ideal (then $z \le z^*$). These definitions follow the programs. The division $\alpha/\lambda_i$ in $\Phi$ only occurs for $\lambda_i > 0$.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983) 326–344, https://doi.org/10.1007/BF02591870, pp. 327–328, §2 (weighted and augmented weighted Tchebycheff metrics); p. 330, §3 (weighted Tchebycheff program and Φ(α)); p. 332, program (3.5)

import Mathlib

/-!
# Steuer–Choo (1983), §§2–3: weighted and augmented weighted Tchebycheff values, the sets `Φ(α)`

R. E. Steuer and E.-U. Choo, Math. Programming 26 (1983), §2, pp. 327–328, and §3, p. 330.

The weighted Tchebycheff program `min {α} s.t. α ≥ λᵢ(z*ᵢ − zᵢ), 1 ≤ i ≤ k, fᵢ(x) = zᵢ, x ∈ S`
has, for a fixed criterion vector `z`, minimal `α` equal to `maxᵢ λᵢ(z*ᵢ − zᵢ)`; `tcheb` is that value
and `augTcheb` adds the augmentation term `ρ eᵀ(z* − z)`. The program variable `α` is thereby
eliminated.
-/

namespace SteuerChoo.Discrete

/-- The weighted Tchebycheff value `maxᵢ λᵢ (z*ᵢ − zᵢ)`, the minimal `α` of the weighted Tchebycheff
program at the criterion vector `z` (§3, p. 330). -/
noncomputable def tcheb {k : ℕ} [NeZero k] (lam zstar z : Fin k → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => lam i * (zstar i - z i))

/-- The augmented weighted Tchebycheff value `maxᵢ λᵢ (z*ᵢ − zᵢ) + ρ eᵀ(z* − z)` (§2, p. 328; the
objective of the augmented weighted Tchebycheff program (3.5), p. 332, at `z` with minimal `α`). -/
noncomputable def augTcheb {k : ℕ} [NeZero k] (lam : Fin k → ℝ) (rho : ℝ) (zstar z : Fin k → ℝ) :
    ℝ :=
  tcheb lam zstar z + rho * ∑ i, (zstar i - z i)

/-- `Φ(α) = {z ∈ ℝᵏ | zᵢ ∈ [z*ᵢ − (α/λᵢ), +∞) when λᵢ > 0}` (§3, p. 330). -/
def Phi {k : ℕ} (lam zstar : Fin k → ℝ) (α : ℝ) : Set (Fin k → ℝ) :=
  {z | ∀ i, 0 < lam i → zstar i - α / lam i ≤ z i}

end SteuerChoo.Discrete


