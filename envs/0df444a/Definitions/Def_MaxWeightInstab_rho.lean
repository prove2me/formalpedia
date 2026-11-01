-- Prove2me | Definitions.Def_MaxWeightInstab_rho
-- name    : MaxWeightInstab_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:37.274977+00:00
-- url     : https://prove2.me/theorems/87c3b8f0-5a1b-4f2a-b4e9-fd699ba06e58
-- title:
--   Traffic intensity $\boldsymbol\rho$ of display (2)
-- statement:
--   The traffic intensity of the network of Figure 1 is
--
--   $$
--   \rho_{\mathcal A_0}=\rho_{\mathcal B_0}=a,\qquad \rho_{\mathcal A_j}=\rho_{\mathcal B_j}=\frac aJ,\quad j=1,\dots,J .
--   $$
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (2), p.3

import Mathlib
import Definitions.Def_MaxWeightInstab_Queue

namespace MaxWeightInstab

/-- The traffic intensity of the network of Figure 1, display (2) (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.3):
`ρ_{𝒜₀} = ρ_{ℬ₀} = a` and `ρ_{𝒜_j} = ρ_{ℬ_j} = a/J` for `j = 1, …, J`. -/
noncomputable def rho (a : ℝ) (J : ℕ) : Queue J → ℝ
  | Sum.inl i => Fin.cases (motive := fun _ => ℝ) a (fun _ => a / J) i
  | Sum.inr i => Fin.cases (motive := fun _ => ℝ) a (fun _ => a / J) i

end MaxWeightInstab


