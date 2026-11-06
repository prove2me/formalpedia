-- Prove2me | Definitions.Def_AnytimeAdaVR_smReport
-- name    : AnytimeAdaVR_smReport
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:12.101201+00:00
-- url     : https://prove2.me/theorems/91f47208-ff04-47ec-b25a-2d8408ace424
-- title:
--   Report $R_{S,N}$, $R_{M,N}$ of an S or M path
-- statement:
--   The report of an S or M path after $N$ local queries is the label of the query retained by its reservoir:
--   $$
--   R_{N}=\ell_{R(N)} .
--   $$
--   Reports are defined after any number of queries, including interruptions inside a block or between the two queries of an M pair.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §5.1, p.8; Algorithm 2, p.8

import Mathlib
import Definitions.Def_AnytimeAdaVR_smLabel
import Definitions.Def_AnytimeAdaVR_reservoirIndex

namespace AnytimeAdaVR

/-- **The report `R_{S,N}` / `R_{M,N}` of an S or M path after `N` local queries.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), §5.1,
p.8: "This reservoir is uniform over all query labels after any deterministic number of queries,
including interruptions inside a block or pair", and Algorithm 2, p.8.

`smReport k g xinit ξ U N` is the label of the query retained by the reservoir with coins `U` after
`N` local queries of the path with sample stream `ξ`.

**Formalization Note.** The coins `U` are separate from the samples `ξ` (in every statement they are
independent and uniform on `[0,1]`), so the reservoir never affects optimization. -/
noncomputable def smReport {d : ℕ} {Ξ : Type*} (k : SMKind)
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
    (xinit : EuclideanSpace ℝ (Fin d)) (ξ : ℕ → Ξ) (U : ℕ → unitInterval) (N : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  smLabel k g xinit ξ (reservoirIndex U N)

end AnytimeAdaVR


