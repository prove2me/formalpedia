-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_GRBig
-- name    : DiscreteConvex_ConjugacyDualityD_GRBig
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:02:00.550497+00:00
-- url     : https://prove2.me/theorems/ca62ce37-516b-4c84-8186-4dfadec664af
-- title:
--   GRBig
-- statement:
--   The dual perturbation $G_r(y,v)=\inf_x[K_r(x,y)-\langle x,v\rangle]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Eq. (8.67).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.241, Eq. (8.67)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KR

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The dual perturbation `Gr(y,v) = inf_x [Kr(x,y) - ⟨x,v⟩]`, Eq. (8.67). -/
noncomputable def GRBig (c r : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (y v : V → ℤ) : EReal :=
  sInf {t : EReal | ∃ x : V → ℤ,
    t = KR c r B x y - ((∑ i, (x i : ℝ) * (v i : ℝ) : ℝ) : EReal)}

end DiscreteConvex.ConjugacyDualityD


