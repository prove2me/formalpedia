-- Prove2me | Definitions.Def_SteuerChoo_Discrete_Weights
-- name    : SteuerChoo_Discrete_Weights
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:44:35.340601+00:00
-- url     : https://prove2.me/theorems/1d4ff3bd-64e7-4322-8bc7-484ea81aa068
-- title:
--   Steuer–Choo §3: the weights λᵖ of (b), α_pq of (c)–(d), ρ_p of (3.6) and ρ of (3.8)
-- statement:
--   Let $Z \subset \mathbb R^k$ be finite with nondominated set $N$, let $z^*$ be a reference vector, and write $e$ for the vector of ones.
--
--   1. **Weights (b).** For $z^p \in \mathbb R^k$,
--   $$\lambda^p_i = \begin{cases} \dfrac{1}{z^*_i - z^p_i}\Big[\displaystyle\sum_{j=1}^k \frac{1}{z^*_j - z^p_j}\Big]^{-1} & \text{if } z^p_j \ne z^*_j \text{ for all } j,\\ 1 & \text{if } z^p_i = z^*_i,\\ 0 & \text{if } z^p_i \ne z^*_i \text{ but } z^p_j = z^*_j \text{ for some } j.\end{cases}$$
--   2. **Values (c)–(d).** $\alpha_{pq} = \max_i \lambda^p_i (z^*_i - z^q_i)$, the minimal value of $\min\{\alpha\}$ s.t. $\alpha \ge \lambda^p_i(z^*_i - z^q_i)$, $1\le i\le k$; in particular $\alpha_{pp} = \max_i \lambda^p_i(z^*_i - z^p_i)$.
--   3. **$\rho_p$ of (3.6).**
--   $$\rho_p = \tfrac12 \min_{z^q \in Z} \Big\{ \frac{\alpha_{pq} - \alpha_{pp}}{e^{\mathsf T}(z^q - z^p)} \;\Big|\; e^{\mathsf T}(z^q - z^p) > 0 \Big\},$$
--   and $\rho_p = 1$ if no $z^q \in Z$ satisfies $e^{\mathsf T}(z^q - z^p) > 0$.
--   4. **$\rho$ of (3.8).**
--   $$\rho = \tfrac12 \min_{z^i \in N} \Big[ \min_{z^j \in Z} \Big\{ \frac{\alpha_{ij} - \alpha_{ii}}{e^{\mathsf T}(z^j - z^i)} \;\Big|\; e^{\mathsf T}(z^j - z^i) > 0 \Big\} \Big],$$
--   where $\alpha_{ij}$ is (d) with the weights $\lambda^i$ of $z^i$; the double minimum is the minimum over all pairs $(z^i, z^j) \in N \times Z$ with $e^{\mathsf T}(z^j - z^i) > 0$, and $\rho = 1$ if there is no such pair.
--
--   The weights $\lambda^p$ make $z^p$ the vertex of the Tchebycheff level set through it, and $\rho_p$ (for one vector) and $\rho$ (for all of $N$ at once) are augmentation coefficients small enough that the augmentation term never overturns the order given by the Tchebycheff term.
--
--   **Formalization Note** The condition $e^{\mathsf T}(z^q - z^p) > 0$ excludes $q = p$, so the paper's range $q \in I_Z - \{p\}$ is automatic. The paper leaves the minima of (3.6) and (3.8) undefined when their index sets are empty (for example $Z = \{z^p\}$); this formalization assigns the value $1$ then. Any positive value would serve; the value $0$ produced by Lean's defaults would not. In (b) the division by $z^*_i - z^p_i$ occurs only in the first case, where all these differences are nonzero. Note that (b) gives $\lambda^p_j = 1$ for every $j$ with $z^p_j = z^*_j$, so $\lambda^p$ is a probability vector only when at most one such $j$ exists; for $z^p \in N$ and an ideal $z^*$ this is a consequence of the $\varepsilon$-rule, not a hypothesis.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983) 326–344, https://doi.org/10.1007/BF02591870, pp. 330–331, assumptions (b), (c), (d); p. 332, eq. (3.6) and eq. (3.8)

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated
import Definitions.Def_SteuerChoo_Discrete_Tchebycheff

/-!
# Steuer–Choo (1983), §3: the weights `λᵖ` of (b), the values `α_pq` of (c)–(d), `ρ_p` of (3.6) and
`ρ` of (3.8)

R. E. Steuer and E.-U. Choo, Math. Programming 26 (1983), §3, pp. 330–332.

**Empty minima.** The minima in (3.6) and (3.8) range over sets that can be empty (e.g. when no
`z^q ∈ Z` has a larger coordinate sum than `z^p`). The paper does not assign a value in that case;
here the value is then `1` (any positive value would do; `0` would not).
-/

namespace SteuerChoo.Discrete

/-- The weights `λᵖ` of (b), §3, p. 330:
`λᵖᵢ = [1/(z*ᵢ − zᵖᵢ)] [Σⱼ 1/(z*ⱼ − zᵖⱼ)]⁻¹` if `zᵖᵢ ≠ z*ᵢ` for all `i`;
`λᵖᵢ = 1` if `zᵖᵢ = z*ᵢ`; `λᵖᵢ = 0` if `zᵖᵢ ≠ z*ᵢ` but `zᵖⱼ = z*ⱼ` for some `j`. -/
noncomputable def lamP {k : ℕ} (zstar zp : Fin k → ℝ) : Fin k → ℝ := by
  classical
  exact fun i =>
    if ∀ j, zp j ≠ zstar j then
      (1 / (zstar i - zp i)) * (∑ j, 1 / (zstar j - zp j))⁻¹
    else if zp i = zstar i then 1 else 0

/-- `α_pq` of (d), §3, p. 331: the minimal value of `min {α} s.t. α ≥ λᵖᵢ(z*ᵢ − z^qᵢ), 1 ≤ i ≤ k`,
i.e. `maxᵢ λᵖᵢ(z*ᵢ − z^qᵢ)`. With `zq = zp` this is `α_pp` of (c), p. 330. -/
noncomputable def alphaPQ {k : ℕ} [NeZero k] (zstar zp zq : Fin k → ℝ) : ℝ :=
  tcheb (lamP zstar zp) zstar zq

/-- `ρ_p` of (3.6), §3, p. 332:
`ρ_p = ½ min_{q ∈ I_Z − {p}} {(α_pq − α_pp) / eᵀ(z^q − zᵖ) | eᵀ(z^q − zᵖ) > 0}`,
and `1` when no `z^q ∈ Z` satisfies `eᵀ(z^q − zᵖ) > 0`. -/
noncomputable def rhoP {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar zp : Fin k → ℝ) : ℝ := by
  classical
  exact
    let T := Z.filter (fun zq => 0 < ∑ i, (zq i - zp i))
    if h : T.Nonempty then
      (1 / 2) * T.inf' h
        (fun zq => (alphaPQ zstar zp zq - alphaPQ zstar zp zp) / ∑ i, (zq i - zp i))
    else 1

/-- `ρ` of (3.8), §3, p. 332:
`ρ = ½ min_{i ∈ I_N} [min_{j ∈ I_Z − {i}} {(α_ij − α_ii) / eᵀ(zʲ − zⁱ) | eᵀ(zʲ − zⁱ) > 0}]`,
the minimum taken over all pairs `(zⁱ, zʲ) ∈ N × Z` with `eᵀ(zʲ − zⁱ) > 0`, where `α_ij` is (d)
with the weights `λⁱ` of `zⁱ`; and `1` when there is no such pair. -/
noncomputable def rho38 {k : ℕ} [NeZero k] (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ) : ℝ := by
  classical
  exact
    let T := (nondominated Z ×ˢ Z).filter (fun pr => 0 < ∑ i, (pr.2 i - pr.1 i))
    if h : T.Nonempty then
      (1 / 2) * T.inf' h
        (fun pr => (alphaPQ zstar pr.1 pr.2 - alphaPQ zstar pr.1 pr.1) / ∑ i, (pr.2 i - pr.1 i))
    else 1

end SteuerChoo.Discrete


