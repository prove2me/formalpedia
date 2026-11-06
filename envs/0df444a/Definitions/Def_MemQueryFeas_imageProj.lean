-- Prove2me | Definitions.Def_MemQueryFeas_imageProj
-- name    : MemQueryFeas_imageProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:21.30993+00:00
-- url     : https://prove2.me/theorems/562a41b4-393e-43ba-be24-1af1e15a8c55
-- title:
--   Image $T(E)$ of a subspace under a linear map
-- statement:
--   For a linear map $T$ and a subspace $E$, $T(E)=\{Tx:x\in E\}$; the subspace $T(E)$ is represented by its orthogonal projection $P_{T(E)}$. This is how the maps $H_{v'}$, $T$ and $T_{E^{(i-1)},\eta}$ act on subspaces in Algorithm 2 and Game 1.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Algorithm 2, p.8 (PDF p.9); Game 1, p.12

import Mathlib
import Definitions.Def_MemQueryFeas_projOnto

namespace MemQueryFeas

/-- **Image of a subspace under a linear map.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Algorithm 2, p.8 (PDF p.9): "`H_{v'}(E_p)`";
Game 1, p.12: "`T(E)`" and "`T_{E^(i−1),η}(E^(i))`".

For a linear map `T` and a subspace `E` given by its projection `p = P_E`, `imageProj T p` is the
orthogonal projection onto `T(E) = {T x : x ∈ E}`. -/
noncomputable def imageProj {d : ℕ} (T p : Op d) : Op d :=
  projOnto ((LinearMap.range (p : Vec d →ₗ[ℝ] Vec d)).map (T : Vec d →ₗ[ℝ] Vec d))

end MemQueryFeas


