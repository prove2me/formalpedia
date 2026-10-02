-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_KTildeR
-- name    : DiscreteConvex_ConjugacyDualityD_KTildeR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:03:47.070883+00:00
-- url     : https://prove2.me/theorems/dac8a9cc-70cc-4d51-b068-ba0043f557bb
-- title:
--   KTildeR
-- statement:
--   The dual-of-dual Lagrangian $\tilde K_r(x,y)=\sup_v[G_r(y,v)+\langle x,v\rangle]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Eq. (8.69).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Eq. (8.69)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRBig

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The dual-of-dual Lagrangian `K̃r(x,y) = sup_v [Gr(y,v) + ⟨x,v⟩]`, Eq. (8.69). -/
noncomputable def KTildeR (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x y : V → ℤ) : EReal :=
  sSup {t : EReal | ∃ v : V → ℤ, t = GRBig c r B y v + ((∑ i, (x i : ℝ) * (v i : ℝ) : ℝ) : EReal)}

end DiscreteConvex.ConjugacyDualityD


