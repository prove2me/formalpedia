-- Prove2me | Definitions.Def_RPLib_F2_078
-- name    : RPLib_F2_078
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T14:43:16.404635+00:00
-- url     : https://prove2.me/theorems/a9201176-26e1-4073-bb9d-7cea26c94d98
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 078 (part 2 of file 033 of 70)
-- statement:
--   File 078 (part 2 of file 033 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_InstA`: S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_029
import Definitions.Def_RPLib_F2_077

/-!
# Ramanujan-Petersson curve library (flat edition), file 078 (part 2 of file 033 of 70)

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_InstA`: S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstA =====
section

/-!
# S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)`

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
theorem b_LR {x' : Localization.Away L.ωm →ₐ[K] K} (h : pL x = pR x') :
    (L.mB (x.comp (nestK (K := K) L.mU))).comp (iL K F) = (L.mB (x'.comp (nestK (K := K) L.mU))).comp (iR K F) :=
  (L.mB_L x).trans (h.trans (L.mB_R x').symm)

variable {x xr xl} in
theorem b_RR {x' : Localization.Away L.ωm →ₐ[K] K} (h : pR x = pR x') :
    (L.mB (x.comp (nestK (K := K) L.mU))).comp (iR K F) = (L.mB (x'.comp (nestK (K := K) L.mU))).comp (iR K F) :=
  (L.mB_R x).trans (h.trans (L.mB_R x').symm)

end Rel

end LawData

end Inst

end RamanujanPetersson.JacLaw


end


