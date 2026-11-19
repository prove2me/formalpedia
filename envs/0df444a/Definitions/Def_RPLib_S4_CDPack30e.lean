-- Prove2me | Definitions.Def_RPLib_S4_CDPack30e
-- name    : RPLib_S4_CDPack30e
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T11:01:31.099913+00:00
-- url     : https://prove2.me/theorems/3e7920f6-2f15-40a1-a5b6-cb02e1139613
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 30e of 71
-- statement:
--   Part 30e of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_InstR1`: S4-JacLaw, file O10e (part R): the `PreChunk` relations `rel_r_m rel_m_r rel_l_m rel_m_l` [pack-only part InstR1: `rel_r_m`, `rel_m_r`]
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack30c
import Definitions.Def_RPLib_S4_CDPack30d

/-!
# Curve-duality library package, part 30e of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_InstR1`: S4-JacLaw, file O10e (part R): the `PreChunk` relations `rel_r_m rel_m_r rel_l_m rel_m_l` [pack-only part InstR1: `rel_r_m`, `rel_m_r`]
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstR1 =====
section

/-!
# S4-JacLaw, file O10e (part R): the `PreChunk` relations `rel_r_m rel_m_r rel_l_m rel_m_l` [pack-only part InstR1: `rel_r_m`, `rel_m_r`]

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

theorem rel_r_m (hL : pL xr = pL x) (hR : pR xr = x.comp L.μm) : xr.comp L.ρr = pR x :=
  (L.r_nest xr).trans <| (L.law_r_m (x.comp (nestK (K := K) L.mU)) (xr.comp (nestK (K := K) L.rU))
    ((L.rB_L xr).trans (hL.trans (L.mB_L x).symm)) ((L.rB_R xr).trans (hR.trans (L.m_nest x)))).trans (L.mB_R x)

theorem rel_m_r (hL : pL x = pL xr) (hR : pR x = xr.comp L.ρr) : x.comp L.μm = pR xr :=
  (L.m_nest x).trans <| (L.law_m_r (x.comp (nestK (K := K) L.mU)) (xr.comp (nestK (K := K) L.rU))
    ((L.mB_L x).trans (hL.trans (L.rB_L xr).symm)) ((L.mB_R x).trans (hR.trans (L.r_nest xr)))).trans (L.rB_R xr)

end Rel

end LawData

end Inst

end RamanujanPetersson.JacLaw

end


