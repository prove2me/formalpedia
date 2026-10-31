-- Prove2me | Definitions.Def_CoCoNet_Hfair
-- name    : CoCoNet_Hfair
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:47.102161+00:00
-- url     : https://prove2.me/theorems/cebe375f-03bd-4b2b-bcf6-b1326953e0b1
-- title:
--   $H(a)$: banks healthy at asset values $a$ in the fair case
-- statement:
--   In the fair case (credit amounts $c_i=m_il_i$) the map $\Phi$ is a bijection (Proposition 4), so for every asset vector $a$ there is exactly one equilibrium price vector $\Phi^{-1}(a)$. The set of banks healthy at $a$ in the fair case is
--   $$H(a)=\{i : \Phi^{-1}(a)_i>l_i\}.$$
--
--   **Formalization Note** $\Phi^{-1}$ is `Function.invFun` of the fair map `Phi m W l (m * l)`. It is the genuine inverse only when that map is bijective; every statement using `Hfair` assumes an admissible network and $l\ge0$, under which it is (Proposition 4).
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, §3.3, p.19

import Mathlib
import Definitions.Def_CoCoNet_healthy
import Definitions.Def_CoCoNet_Phi

namespace CoCoNet

/-- **`H(a)`: the banks healthy at asset values `a` in the fair case.**
Balter, Schweizer & Vera, arXiv:2011.06474v1, §3.3, p.19: "In the fair case, Φ is a bijection.
Thus we can define H(a) = {i : Φ⁻¹(a)ᵢ > ℓᵢ}, the set of banks which are healthy in a in the fair
case."

**Formalization Note.** The fair credit is `c = m ∘ l` (pointwise `m * l`, i.e. `lᵢ = cᵢ/mᵢ`).
`Φ⁻¹` is `Function.invFun` of the fair map; it is the genuine inverse because the fair map is
bijective (Proposition 4), which needs an admissible network and `0 ≤ l`; every statement using
`Hfair` carries those hypotheses. -/
noncomputable def Hfair {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (l : Fin n → ℝ)
    (a : Fin n → ℝ) : Finset (Fin n) :=
  healthy l (Function.invFun (Phi m W l (m * l)) a)

end CoCoNet


