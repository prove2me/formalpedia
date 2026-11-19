-- Prove2me | Definitions.Def_RPLib_S4_CDPack30w
-- name    : RPLib_S4_CDPack30w
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T11:27:47.341791+00:00
-- url     : https://prove2.me/theorems/a7c11d29-37bf-4254-969c-9db9797acc17
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 30w of 71
-- statement:
--   Part 30w of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_InstA3`: S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)` [pack-only part InstA3: `rel_assoc`]
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack30g
import Definitions.Def_RPLib_S4_CDPack30z

/-!
# Curve-duality library package, part 30w of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_InstA3`: S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)` [pack-only part InstA3: `rel_assoc`]
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstA3 =====
section

/-!
# S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)` [pack-only part InstA3: `rel_assoc`]

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

set_option maxHeartbeats 400000 in
theorem rel_assoc (x₁ x₂ x₃ x₄ : Localization.Away L.ωm →ₐ[K] K) (e₁ : pR x₁ = pL x₂)
    (e₂ : pL x₃ = x₁.comp L.μm) (e₃ : pR x₃ = pR x₂) (e₄ : pL x₄ = pL x₁) (e₅ : pR x₄ = x₂.comp L.μm) :
    x₃.comp L.μm = x₄.comp L.μm :=
  (L.m_nest x₃).trans <| (L.law_assoc (x₁.comp (nestK (K := K) L.mU)) (x₂.comp (nestK (K := K) L.mU))
    (x₃.comp (nestK (K := K) L.mU)) (x₄.comp (nestK (K := K) L.mU)) (L.b_LL e₄) (L.b_LR e₁.symm)
    (L.b_RR e₃) (L.b_Lmu e₂) (L.b_Rmu e₅)).trans (L.m_nest x₄).symm

end Rel

end LawData

end Inst

end RamanujanPetersson.JacLaw

end


