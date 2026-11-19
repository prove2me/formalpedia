-- Prove2me | Definitions.Def_RPLib_S4_CDPack30z
-- name    : RPLib_S4_CDPack30z
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T11:03:14.391947+00:00
-- url     : https://prove2.me/theorems/13a7d3be-46a7-4f7c-a8de-b468102ef590
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 30z of 71
-- statement:
--   Part 30z of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_InstA2`: S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)` [pack-only part InstA2: `b_Lmu`, `b_Rmu`]
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack30f

/-!
# Curve-duality library package, part 30z of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_InstA2`: S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)` [pack-only part InstA2: `b_Lmu`, `b_Rmu`]
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstA2 =====
section

/-!
# S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)` [pack-only part InstA2: `b_Lmu`, `b_Rmu`]

`b_LL b_LR b_RR b_Lmu b_Rmu` (base identities through the nest) and `rel_assoc`.
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

section Rel

variable (x : Localization.Away L.ωm →ₐ[K] K) (xr : Localization.Away L.ωr →ₐ[K] K)
  (xl : Localization.Away L.ωl →ₐ[K] K)

variable {x xr xl} in
theorem b_Lmu {x' : Localization.Away L.ωm →ₐ[K] K} (h : pL x = x'.comp L.μm) :
    (L.mB (x.comp (nestK (K := K) L.mU))).comp (iL K F) = (x'.comp (nestK (K := K) L.mU)).comp L.mOutL :=
  (L.mB_L x).trans (h.trans (L.m_nest x'))

variable {x xr xl} in
theorem b_Rmu {x' : Localization.Away L.ωm →ₐ[K] K} (h : pR x = x'.comp L.μm) :
    (L.mB (x.comp (nestK (K := K) L.mU))).comp (iR K F) = (x'.comp (nestK (K := K) L.mU)).comp L.mOutL :=
  (L.mB_R x).trans (h.trans (L.m_nest x'))

end Rel

end LawData

end Inst

end RamanujanPetersson.JacLaw

end


