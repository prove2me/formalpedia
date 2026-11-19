-- Prove2me | Definitions.Def_RPLib_S4_CDPack30x
-- name    : RPLib_S4_CDPack30x
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T10:30:42.482092+00:00
-- url     : https://prove2.me/theorems/4e080b8b-8d2d-4df7-8b4f-17be2a32e8b8
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 30x of 71
-- statement:
--   Part 30x of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_InstBaseB`: S4-JacLaw, file O10e (part Base): points below points of `D(numA _)` [pack-only part InstBaseB: `rB_R`, `lB_L`, `lB_R`, `r_nest`, `l_nest`]
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack30

/-!
# Curve-duality library package, part 30x of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_InstBaseB`: S4-JacLaw, file O10e (part Base): points below points of `D(numA _)` [pack-only part InstBaseB: `rB_R`, `lB_L`, `lB_R`, `r_nest`, `l_nest`]
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstBaseB =====
section

/-!
# S4-JacLaw, file O10e (part Base): points below points of `D(numA _)` [pack-only part InstBaseB: `rB_R`, `lB_L`, `lB_R`, `r_nest`, `l_nest`]

`mB_L mB_R rB_L rB_R lB_L lB_R` (`nestK_base` at `T0`, `iL`, `iR`: the base of `x ∘ nestK` is `pL x`, `pR x`)
and `m_nest r_nest l_nest` (`x ∘ μm = (x ∘ nestK) ∘ mOutL`, etc.).
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

section Base

variable (x : Localization.Away L.ωm →ₐ[K] K) (xr : Localization.Away L.ωr →ₐ[K] K)
  (xl : Localization.Away L.ωl →ₐ[K] K)

theorem rB_R : (L.rB (xr.comp (nestK (K := K) L.rU))).comp (iR K F) = pR xr := nestK_base L.rU xr (iR K F)

theorem lB_L : (L.lB (xl.comp (nestK (K := K) L.lU))).comp (iL K F) = pL xl := nestK_base L.lU xl (iL K F)

theorem lB_R : (L.lB (xl.comp (nestK (K := K) L.lU))).comp (iR K F) = pR xl := nestK_base L.lU xl (iR K F)

theorem r_nest : xr.comp L.ρr = (xr.comp (nestK (K := K) L.rU)).comp L.rOutL :=
  (AlgHom.comp_assoc _ _ _).symm

theorem l_nest : xl.comp L.lal = (xl.comp (nestK (K := K) L.lU)).comp L.lOutL :=
  (AlgHom.comp_assoc _ _ _).symm

end Base

end LawData

end Inst

end RamanujanPetersson.JacLaw

end


