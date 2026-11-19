-- Prove2me | Definitions.Def_RPLib_S4_CDPack30f
-- name    : RPLib_S4_CDPack30f
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T10:54:57.852516+00:00
-- url     : https://prove2.me/theorems/f8dcb1b9-5897-4d78-8646-7651fca34cf7
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 30f of 71
-- statement:
--   Part 30f of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_InstL3`: S4-JacLaw, file O10e (part L, law_assoc): the point relations of `Law`/`Assoc` on `T0[1/u3][1/u2]`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack30b
import Definitions.Def_RPLib_S4_CDPack30x

/-!
# Curve-duality library package, part 30f of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_InstL3`: S4-JacLaw, file O10e (part L, law_assoc): the point relations of `Law`/`Assoc` on `T0[1/u3][1/u2]`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstL3 =====
section

/-!
# S4-JacLaw, file O10e (part L, law_assoc): the point relations of `Law`/`Assoc` on `T0[1/u3][1/u2]`

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
theorem law_assoc (ha : (L.mB y₄).comp (iL K F) = (L.mB y₁).comp (iL K F))
    (hb : (L.mB y₂).comp (iL K F) = (L.mB y₁).comp (iR K F))
    (hc : (L.mB y₃).comp (iR K F) = (L.mB y₂).comp (iR K F))
    (hab : (L.mB y₃).comp (iL K F) = y₁.comp L.mOutL)
    (hbc : (L.mB y₄).comp (iR K F) = y₂.comp L.mOutL) : y₃.comp L.mOutL = y₄.comp L.mOutL :=
  assoc_mOut (T1 := T0 K F) (T2 := T0 K F) (T3 := T0 K F) (T4 := T0 K F) (D3 := L.Dm3) (D2 := L.Dm2)
    (c0 := L.c0) (c1 := L.c1) (φa := iL K F) (φb := iR K F) (φb' := iL K F) (φc := iR K F) (ψab := iL K F)
    (ψc := iR K F) (χa := iL K F) (χbc := iR K F) y₁ y₂ y₃ y₄ ha hb hc hab hbc

end Law

end LawData

end Inst

end RamanujanPetersson.JacLaw

end


