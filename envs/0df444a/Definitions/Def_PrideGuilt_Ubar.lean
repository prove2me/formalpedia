-- Prove2me | Definitions.Def_PrideGuilt_Ubar
-- name    : PrideGuilt_Ubar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:39.87038+00:00
-- url     : https://prove2.me/theorems/793be084-ca16-4979-9d41-2db4ea3d8837
-- title:
--   Average consumer utility $\bar U(f)$ at equilibrium
-- statement:
--   The consumers' average utility at the equilibrium induced by the reward $f$ is
--
--   $$
--   \bar U(f)=\begin{cases} U_R(f,1) & \text{if } \tau^*(f)=1,\\ U_N(0) & \text{if } \tau^*(f)=0,\\ U_R(f,\tau_m(f))=U_N(\tau_m(f)) & \text{if } \tau^*(f)=\tau_m(f).\end{cases}
--   $$
--
--   It enters the demand through the consumers' consideration of the product's end-of-life recyclability.
--
--   **Formalization Note** $\bar U$ is defined by the branch of $\tau^*$ that applies, with the same tests in the same order. This agrees with the page's case split by value because on the interior branch $\tau_m(f)\in(0,1)$, so the three cases never compete.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), display above eq. (3), p.11

import Mathlib
import Definitions.Def_PrideGuilt_tauM
import Definitions.Def_PrideGuilt_UR
import Definitions.Def_PrideGuilt_UN

namespace PrideGuilt

/-- **The consumers' average utility `Ū(f)` at equilibrium.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, display above (3), p.11 (PDF 12):
`Ū(f) = U_R|_{τ=1}` if `τ*(f) = 1`; `U_N|_{τ=0}` if `τ*(f) = 0`;
`U_R|_{τ=τ_m(f)} = U_N|_{τ=τ_m(f)}` if `τ*(f) = τ_m(f)`.

**Formalization Note.** Defined by the branch of `tauStar` that applies, with the same tests in
the same order: `U_N(0)` on the `τ* = 0` branches, `U_R(f, 1)` on the `τ* = 1` branches and
`U_R(f, τ_m(f))` on the interior branch. This agrees with the page's case split by value, because
on the interior branch `τ_m(f) ∈ (0, 1)` (Lemma 1), so the three cases of the page never compete. -/
noncomputable def Ubar (P : Params) (γP γG f : ℝ) : ℝ :=
  if f ≤ cr P - max γP γG then UN P γG 0
  else if cr P - min γP γG ≤ f then UR P γP f 1
  else if γG < γP then UR P γP f (tauM P γP γG f)
  else if tauM P γP γG f ≤ P.τ0 then UR P γP f 1 else UN P γG 0

end PrideGuilt


