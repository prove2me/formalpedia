-- Prove2me | Definitions.Def_ChitourPrescribedTime_FixedTime_VaryingDegree
-- name    : ChitourPrescribedTime_FixedTime_VaryingDegree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:06:53.195836+00:00
-- url     : https://prove2.me/theorems/88dee562-b4e2-4603-b410-3f33d6908cfb
-- title:
--   The state-dependent degree $\kappa(x)$ (49), the radii $r(m,\pm\kappa_0)$ and the settling bound (52)
-- statement:
--   Let $V_0$ denote $V_\kappa$ at $\kappa=0$. For $m\in(0,1)$ and $\kappa_0\in(0,\tfrac1{2n})$, Definition 27 sets
--   $$\kappa(x)=\begin{cases}\kappa_0 & \text{if } V_0(x)>1+m,\\ \kappa_0\Big(1+\dfrac{V_0(x)-(1+m)}{m}\Big) & \text{if } 1-m\le V_0(x)\le 1+m,\\ -\kappa_0 & \text{if } V_0(x)<1-m,\end{cases}$$
--   a continuous function with values in $[-\kappa_0,\kappa_0]$.
--
--   With $B^\kappa_{<a}=\{x\mid V_\kappa(x)<a\}$, Theorem 28 introduces $r(m,\kappa_0)$, the largest $r>0$ such that $B^{\kappa_0}_{<r}\subseteq B^0_{<1+m}$, and $r(m,-\kappa_0)$, the smallest $r>0$ such that $B^{-\kappa_0}_{<r}\supseteq B^0_{<1-m}$. Here they are the supremum, respectively the infimum, of the set of admissible $r>0$. For a constant $C>0$, the right-hand side of (52) is
--   $$T^\ast(m,\kappa_0)=\frac1C\left(\frac{r(m,\kappa_0)^{-\alpha(\kappa_0)}}{\alpha(\kappa_0)}-2\ln(2m)+\frac{r(m,-\kappa_0)^{-\alpha(-\kappa_0)}}{-\alpha(-\kappa_0)}\right).$$
--
--   These objects define the fixed-time controller $\omega^H_{\kappa(x)}(x)$ of Theorem 28 and the bound on its settling time.
--
--   **Formalization Note** `kappaOf ℓ m κ0` is $\kappa(\cdot)$, `rPlus` and `rMinus` are $r(m,\kappa_0)$ and $r(m,-\kappa_0)$, and `settlingBound ℓ C m κ0` is $T^\ast(m,\kappa_0)$. "Largest"/"smallest" are taken as `sSup`/`sInf` of the admissible radii, since the extremum may fail to be attained for the strict-inequality sets. The theorems using them also assert $r(m,\pm\kappa_0)>0$, as the page does.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1036, Definition 27, eq. (49); p. 1037, Theorem 28, eq. (52)

import Mathlib
import Definitions.Def_ChitourPrescribedTime_FixedTime_Lyapunov

namespace ChitourPrescribedTime.FixedTime

/-- The state-dependent homogeneity degree `κ(x)` of Definition 27, (49), built from
`V_0 = V_κ` at `κ = 0`:
`κ(x) = κ₀` if `V_0(x) > 1 + m`, `κ(x) = κ₀ (1 + (V_0(x) - (1 + m))/m)` if
`1 - m ≤ V_0(x) ≤ 1 + m`, and `κ(x) = -κ₀` if `V_0(x) < 1 - m`. -/
noncomputable def kappaOf {n : ℕ} (ℓ : Fin n → ℝ) (m κ0 : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ℝ :=
  if 1 + m < lyapV ℓ 0 x then κ0
  else if lyapV ℓ 0 x < 1 - m then -κ0
  else κ0 * (1 + (lyapV ℓ 0 x - (1 + m)) / m)

/-- `r(m, κ₀)` of Theorem 28: the largest `r > 0` such that
`B^{κ₀}_{<r} = {x | V_{κ₀}(x) < r}` is contained in `B^0_{<1+m} = {x | V_0(x) < 1 + m}`,
taken as the supremum of the admissible `r`. -/
noncomputable def rPlus {n : ℕ} (ℓ : Fin n → ℝ) (m κ0 : ℝ) : ℝ :=
  sSup {r : ℝ | 0 < r ∧
    {x : EuclideanSpace ℝ (Fin n) | lyapV ℓ κ0 x < r} ⊆
      {x : EuclideanSpace ℝ (Fin n) | lyapV ℓ 0 x < 1 + m}}

/-- `r(m, -κ₀)` of Theorem 28: the smallest `r > 0` such that
`B^{-κ₀}_{<r} = {x | V_{-κ₀}(x) < r}` contains `B^0_{<1-m} = {x | V_0(x) < 1 - m}`,
taken as the infimum of the admissible `r`. -/
noncomputable def rMinus {n : ℕ} (ℓ : Fin n → ℝ) (m κ0 : ℝ) : ℝ :=
  sInf {r : ℝ | 0 < r ∧
    {x : EuclideanSpace ℝ (Fin n) | lyapV ℓ 0 x < 1 - m} ⊆
      {x : EuclideanSpace ℝ (Fin n) | lyapV ℓ (-κ0) x < r}}

/-- The right-hand side of the settling-time bound (52):
`(1/C) ( r(m,κ₀)^{-α(κ₀)}/α(κ₀) - 2 ln(2m) + r(m,-κ₀)^{-α(-κ₀)}/(-α(-κ₀)) )`. -/
noncomputable def settlingBound {n : ℕ} (ℓ : Fin n → ℝ) (C m κ0 : ℝ) : ℝ :=
  (1 / C) * (rPlus ℓ m κ0 ^ (-alpha κ0) / alpha κ0 - 2 * Real.log (2 * m)
    + rMinus ℓ m κ0 ^ (-alpha (-κ0)) / (-alpha (-κ0)))

end ChitourPrescribedTime.FixedTime


