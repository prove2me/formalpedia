-- Prove2me | Definitions.Def_RPLib_F2_074
-- name    : RPLib_F2_074
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T13:49:41.572263+00:00
-- url     : https://prove2.me/theorems/f7c40a52-d38e-4896-8f7e-99b6ad248ff1
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 074 (part 2 of file 029 of 70)
-- statement:
--   File 074 (part 2 of file 029 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_InstBase`: S4-JacLaw, file O10e (part Base): points below points of `D(numA _)`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_028
import Definitions.Def_RPLib_F2_073

/-!
# Ramanujan-Petersson curve library (flat edition), file 074 (part 2 of file 029 of 70)

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_InstBase`: S4-JacLaw, file O10e (part Base): points below points of `D(numA _)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstBase =====
section

/-!
# S4-JacLaw, file O10e (part Base): points below points of `D(numA _)`

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

/-- `x ∘ μ` through the nest. -/
theorem m_nest : x.comp L.μm = (x.comp (nestK (K := K) L.mU)).comp L.mOutL :=
  (AlgHom.comp_assoc _ _ _).symm
theorem r_nest : xr.comp L.ρr = (xr.comp (nestK (K := K) L.rU)).comp L.rOutL :=
  (AlgHom.comp_assoc _ _ _).symm

end Base

end LawData

end Inst

end RamanujanPetersson.JacLaw


end


