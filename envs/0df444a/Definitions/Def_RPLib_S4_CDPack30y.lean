-- Prove2me | Definitions.Def_RPLib_S4_CDPack30y
-- name    : RPLib_S4_CDPack30y
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T11:01:41.350729+00:00
-- url     : https://prove2.me/theorems/f8d756c1-68ad-486e-b2d6-e2deb6c70aba
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 30y of 71
-- statement:
--   Part 30y of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_InstR2`: S4-JacLaw, file O10e (part R): the `PreChunk` relations `rel_r_m rel_m_r rel_l_m rel_m_l` [pack-only part InstR2: `rel_l_m`, `rel_m_l`]
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack30c
import Definitions.Def_RPLib_S4_CDPack30d

/-!
# Curve-duality library package, part 30y of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_InstR2`: S4-JacLaw, file O10e (part R): the `PreChunk` relations `rel_r_m rel_m_r rel_l_m rel_m_l` [pack-only part InstR2: `rel_l_m`, `rel_m_l`]
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstR2 =====
section

/-!
# S4-JacLaw, file O10e (part R): the `PreChunk` relations `rel_r_m rel_m_r rel_l_m rel_m_l` [pack-only part InstR2: `rel_l_m`, `rel_m_l`]

For points of `D(ωm)`, `D(ωr)`, `D(ωl)` (through `law_*` at `x ∘ nestK`).
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

theorem rel_l_m (hR : pR xl = pR x) (hL : pL xl = x.comp L.μm) : xl.comp L.lal = pL x :=
  (L.l_nest xl).trans <| (L.law_l_m (x.comp (nestK (K := K) L.mU)) (xl.comp (nestK (K := K) L.lU))
    ((L.lB_R xl).trans (hR.trans (L.mB_R x).symm)) ((L.lB_L xl).trans (hL.trans (L.m_nest x)))).trans (L.mB_L x)

theorem rel_m_l (hR : pR x = pR xl) (hL : pL x = xl.comp L.lal) : x.comp L.μm = pL xl :=
  (L.m_nest x).trans <| (L.law_m_l (x.comp (nestK (K := K) L.mU)) (xl.comp (nestK (K := K) L.lU))
    ((L.mB_L x).trans (hL.trans (L.l_nest xl))) ((L.mB_R x).trans (hR.trans (L.lB_R xl).symm))).trans (L.lB_L xl)

end Rel

end LawData

end Inst

end RamanujanPetersson.JacLaw

end


