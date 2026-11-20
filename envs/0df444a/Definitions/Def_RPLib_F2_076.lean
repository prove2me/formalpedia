-- Prove2me | Definitions.Def_RPLib_F2_076
-- name    : RPLib_F2_076
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T13:51:28.645688+00:00
-- url     : https://prove2.me/theorems/0aa27dc3-e514-4bcf-a443-c100afe88a10
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 076 (part 2 of file 030 of 70)
-- statement:
--   File 076 (part 2 of file 030 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_InstL2`: S4-JacLaw, file O10e (part L, law_l_m, law_m_l): the point relations of `Law`/`Assoc` on `T0[1/u3][1/u2]`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_028
import Definitions.Def_RPLib_F2_075

/-!
# Ramanujan-Petersson curve library (flat edition), file 076 (part 2 of file 030 of 70)

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_InstL2`: S4-JacLaw, file O10e (part L, law_l_m, law_m_l): the point relations of `Law`/`Assoc` on `T0[1/u3][1/u2]`
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

end Law

end LawData

end Inst

end RamanujanPetersson.JacLaw


end


