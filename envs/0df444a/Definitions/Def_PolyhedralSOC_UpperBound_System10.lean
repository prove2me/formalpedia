-- Prove2me | Definitions.Def_PolyhedralSOC_UpperBound_System10
-- name    : PolyhedralSOC_UpperBound_System10
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:46:34.410008+00:00
-- url     : https://prove2.me/theorems/506b981c-b648-4fb9-b152-77e34a94cb44
-- title:
--   The system (10): system (8) along the tower of variables
-- statement:
--   Let $k=2^\theta$ and let $\nu_1,\dots,\nu_\theta$ be natural numbers. With the tower notation $y_i^\ell$ (generation $\ell$, index $i$; parents $y_{2i-1}^{\ell-1},y_{2i}^{\ell-1}$), system (10) consists, for every $\ell=1,\dots,\theta$ and $i=1,\dots,2^{\theta-\ell}$, of the blocks
--
--   $(a_{\ell,i})$: $\xi_{\ell,i}^0\ge|y_{2i-1}^{\ell-1}|$, $\eta_{\ell,i}^0\ge|y_{2i}^{\ell-1}|$;
--
--   $(b_{\ell,i})$: for $j=1,\dots,\nu_\ell$,
--   $$\xi_{\ell,i}^j=\cos\Big(\frac{\pi}{2^{j+1}}\Big)\xi_{\ell,i}^{j-1}+\sin\Big(\frac{\pi}{2^{j+1}}\Big)\eta_{\ell,i}^{j-1},\qquad \eta_{\ell,i}^j\ge\Big|-\sin\Big(\frac{\pi}{2^{j+1}}\Big)\xi_{\ell,i}^{j-1}+\cos\Big(\frac{\pi}{2^{j+1}}\Big)\eta_{\ell,i}^{j-1}\Big|;$$
--
--   $(c_{\ell,i})$: $\xi_{\ell,i}^{\nu_\ell}\le y_i^\ell$, $\eta_{\ell,i}^{\nu_\ell}\le\tan\big(\frac{\pi}{2^{\nu_\ell+1}}\big)\xi_{\ell,i}^{\nu_\ell}$.
--
--   That is, block $(\ell,i)$ is system (8) with parameter $\nu_\ell$ applied to $(x_1,x_2,x_3)=(y_{2i-1}^{\ell-1},y_{2i}^{\ell-1},y_i^\ell)$, with its own variables $\xi_{\ell,i}^j,\eta_{\ell,i}^j$.
--
--   **Formalization Note** Tower variables are `Y ℓ i` $=y_{i+1}^\ell$ (0-based `i`), and `ξ ℓ i j`, `η ℓ i j` are $\xi_{\ell,i+1}^j$, $\eta_{\ell,i+1}^j$. The definition reuses the definition of system (8).
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), proof of Theorem 1.1, p. 200, system (10)

import Mathlib
import Definitions.Def_PolyhedralSOC_UpperBound_System8

namespace PolyhedralSOC.UpperBound

/-- The system of linear inequalities (10) of Ben-Tal & Nemirovski, *On Polyhedral
Approximations of the Second-Order Cone*, Math. Oper. Res. 26(2):193–205 (2001), proof of
Theorem 1.1, p. 200 (PDF p. 8), for `k = 2^θ` and parameters `ν_1, …, ν_θ` (`νs ℓ`):
for every `ℓ = 1, …, θ` and `i = 1, …, 2^{θ−ℓ}`, the blocks `(a_{ℓ,i})`, `(b_{ℓ,i})`,
`(c_{ℓ,i})`, i.e. the system (8) with parameter `ν_ℓ`, with
`(x₁, x₂, x₃) = (y_{2i−1}^{ℓ−1}, y_{2i}^{ℓ−1}, y_i^ℓ)` and own variables
`ξ_{ℓ,i}^j = ξ ℓ i j`, `η_{ℓ,i}^j = η ℓ i j`. Tower variables are `Y ℓ i = y_{i+1}^ℓ`
(0-based `i`), so the parents of `Y ℓ i` are `Y (ℓ-1) (2i)` and `Y (ℓ-1) (2i+1)`. -/
def System10 (θ : ℕ) (νs : ℕ → ℕ) (Y : ℕ → ℕ → ℝ) (ξ η : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ θ → ∀ i : ℕ, i < 2 ^ (θ - ℓ) →
    System8 (νs ℓ) (Y (ℓ - 1) (2 * i)) (Y (ℓ - 1) (2 * i + 1)) (Y ℓ i) (ξ ℓ i) (η ℓ i)

end PolyhedralSOC.UpperBound


