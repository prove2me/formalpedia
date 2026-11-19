-- Prove2me | Definitions.Def_RPLib_S4_CDPack30d
-- name    : RPLib_S4_CDPack30d
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T10:53:02.229576+00:00
-- url     : https://prove2.me/theorems/a135106e-bfa3-4512-ba31-884ff8bf2f0f
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 30d of 71
-- statement:
--   Part 30d of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_InstL2`: S4-JacLaw, file O10e (part L, law_l_m, law_m_l): the point relations of `Law`/`Assoc` on `T0[1/u3][1/u2]`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack30b
import Definitions.Def_RPLib_S4_CDPack30x

/-!
# Curve-duality library package, part 30d of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_InstL2`: S4-JacLaw, file O10e (part L, law_l_m, law_m_l): the point relations of `Law`/`Assoc` on `T0[1/u3][1/u2]`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstL2 =====
section

/-!
# S4-JacLaw, file O10e (part L, law_l_m, law_m_l): the point relations of `Law`/`Assoc` on `T0[1/u3][1/u2]`

`law_r_m law_m_r law_l_m law_m_l law_assoc`: `r_mOut`, `m_rOut`, `l_mOut`, `m_lOut`, `assoc_mOut` at `T := T0 K F`,
`iL`, `iR`, for abstract points `y` (instantiating them at `x ∘ nestK` directly is slow).
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section Inst

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace LawData

variable (L : LawData K F)

section Law

/-! The point relations of `Law`/`Assoc` for abstract points `y` of the nested localizations (instantiating them
at `x ∘ nestK` directly is slow; through these lemmas it is a plain application). -/

variable (y y₁ y₂ y₃ y₄ : Localization.Away L.mU →ₐ[K] K) (yr : Localization.Away L.rU →ₐ[K] K)
  (yl : Localization.Away L.lU →ₐ[K] K)

set_option maxHeartbeats 400000 in
theorem law_l_m (hb : (L.lB yl).comp (iR K F) = (L.mB y).comp (iR K F))
    (hc : (L.lB yl).comp (iL K F) = y.comp L.mOutL) : yl.comp L.lOutL = (L.mB y).comp (iL K F) :=
  l_mOut (T := T0 K F) (T' := T0 K F) (D3 := L.Dm3) (D3' := L.Dl3) (D2 := L.Dm2) (D2' := L.Dl2) (c0 := L.c0)
    (c1 := L.c1) (φa := iL K F) (φb := iR K F) (ψb := iR K F) (ψc := iL K F) L.hl3 L.hl2 y yl hb hc

set_option maxHeartbeats 400000 in
theorem law_m_l (ha : (L.mB y).comp (iL K F) = yl.comp L.lOutL)
    (hb : (L.mB y).comp (iR K F) = (L.lB yl).comp (iR K F)) : y.comp L.mOutL = (L.lB yl).comp (iL K F) :=
  m_lOut (T := T0 K F) (T' := T0 K F) (D3 := L.Dl3) (D3' := L.Dm3) (D2 := L.Dl2) (D2' := L.Dm2) (c0 := L.c0)
    (c1 := L.c1) (ψb := iR K F) (ψc := iL K F) (φa := iL K F) (φb := iR K F) L.hl3.symm L.hl2.symm yl y ha hb

end Law

end LawData

end Inst

end RamanujanPetersson.JacLaw

end


