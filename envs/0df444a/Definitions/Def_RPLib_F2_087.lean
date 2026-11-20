-- Prove2me | Definitions.Def_RPLib_F2_087
-- name    : RPLib_F2_087
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T13:28:48.575545+00:00
-- url     : https://prove2.me/theorems/f256c3b6-eb54-45d5-93b7-c519518fac7f
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 087 (part 3 of file 028 of 70)
-- statement:
--   File 087 (part 3 of file 028 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_Inst`: S4-JacLaw, file O10e (part A): the law of a `LawData` on `S_g ⊗ S_g`, pulled back to `D(numA _)`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_026
import Definitions.Def_RPLib_F2_072

/-!
# Ramanujan-Petersson curve library (flat edition), file 087 (part 3 of file 028 of 70)

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_Inst`: S4-JacLaw, file O10e (part A): the law of a `LawData` on `S_g ⊗ S_g`, pulled back to `D(numA _)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_Inst =====
section

/-!
# S4-JacLaw, file O10e (part A): the law of a `LawData` on `S_g ⊗ S_g`, pulled back to `D(numA _)`

* `nestK v : T[1/w][1/v] → T[1/(w·num v)]` (`numA v`), `nestK_base`; `nestC f`, `tgtW f` read `v` off the type of `f`.
* `TT K S := S ⊗[K] S` with `iLg`, `iRg`: every `S`-instance through `CommRing S` (the path of `PreChunk K S`;
  a tensor product elaborated directly at `S_g` takes Subalgebra instances and its defeq checks time out).
* `LawData`: `mOutL rOutL lOutL`, `mU rU lU`, `ωm μm ωr ρr ωl lal`, bases `mB rB lB`.
  Base lemmas are in `Def_RP_JacLaw_InstBase`, the point relations in `Def_RP_JacLaw_InstL`.
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section Nest

variable {K : Type u} [Field K] [IsAlgClosed K] {T : Type u} [CommRing T] [Algebra K T] [Algebra.FiniteType K T]
  {w : T} (v : Localization.Away w)

end Nest

section NestC

variable {K : Type u} [Field K] [IsAlgClosed K] {T : Type u} [CommRing T] [Algebra K T] [Algebra.FiniteType K T]
  {w : T} {A : Type u} [CommRing A] [Algebra K A]

end NestC

section TT

variable (K : Type u) [Field K] (S : Type u) [CommRing S] [Algebra K S]

end TT

section Inst

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace LawData

variable (L : LawData K F)

/-- The law `m(a,b)` of `L` on `T0[1/u3][1/u2]`. -/
noncomputable abbrev mOutL := mOut (T := T0 K F) L.Dm3 L.Dm2 L.c0 L.c1 (iL K F) (iR K F)
/-- `r(a,c)` on `T0[1/v2][1/v3]`. -/
noncomputable abbrev rOutL := rOut (T := T0 K F) L.Dr3 L.Dr2 L.c0 L.c1 (iL K F) (iR K F)
/-- `l(c,b) = ν3(b + ν2(c + c1) + c0)`. -/
noncomputable abbrev lOutL := rOut (T := T0 K F) L.Dl3 L.Dl2 L.c0 L.c1 (iR K F) (iL K F)

noncomputable abbrev mU := tgtW L.mOutL
noncomputable abbrev rU := tgtW L.rOutL
noncomputable abbrev lU := tgtW L.lOutL

noncomputable abbrev ωm : T0 K F := numA L.mU
noncomputable abbrev μm := nestC L.mOutL
noncomputable abbrev ωr : T0 K F := numA L.rU
noncomputable abbrev ρr := nestC L.rOutL
noncomputable abbrev ωl : T0 K F := numA L.lU
noncomputable abbrev lal := nestC L.lOutL

/-- The point of `T0` below a point of `T0[1/u3][1/u2]` (`m`), resp. of the `r`, `l` targets. -/
noncomputable abbrev mB (y : Localization.Away L.mU →ₐ[K] K) :=
  mBase (T := T0 K F) L.Dm3 L.Dm2 L.c0 L.c1 (iL K F) (iR K F) y
noncomputable abbrev rB (y : Localization.Away L.rU →ₐ[K] K) :=
  rBase (T := T0 K F) L.Dr3 L.Dr2 L.c0 L.c1 (iL K F) (iR K F) y
noncomputable abbrev lB (y : Localization.Away L.lU →ₐ[K] K) :=
  rBase (T := T0 K F) L.Dl3 L.Dl2 L.c0 L.c1 (iR K F) (iL K F) y

end LawData

end Inst

end RamanujanPetersson.JacLaw


end


