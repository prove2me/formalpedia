-- Prove2me | Definitions.Def_RPLib_S4_CDPack41u
-- name    : RPLib_S4_CDPack41u
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T13:44:32.000027+00:00
-- url     : https://prove2.me/theorems/cc4f4cf2-8d29-4b5b-b060-abf6e01136d9
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 41u of 71
-- statement:
--   Part 41u of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_AJPieceA2`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0` [pack-only part AJPieceA2: `lawMapP`, `lawMapP_comp`, `comp_lawMapP`]
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack41

/-!
# Curve-duality library package, part 41u of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_AJPieceA2`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0` [pack-only part AJPieceA2: `lawMapP`, `lawMapP_comp`, `comp_lawMapP`]
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_AJPieceA2 =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0` [pack-only part AJPieceA2: `lawMapP`, `lawMapP_comp`, `comp_lawMapP`]

In `F' = SynF K F c0` (coordinate `x' = 1/(x - c0)`), the `ν`-piece `pieceMap D c : Sym^g(B') → B'[1/f]` of
`AJLoc` is localized at `N(x')` (`ConvR`), converted to `F`-coordinates by `convSym` (`convS`), and localized at
the image of `u0` (`LocR`). This gives **`lawMapP : LawRing K F → LocR`**, i.e. `Spec LocR → X0`, on the open
`Spec LocR ⊆ Spec B'` (`pieceIn`), with the class formula **`psiJ_lawMapP`**: `ψ(piece(Q)) = κ - [Θ] - [Q]`.
`exists_pieceIn`: a point `Q` of `B'` lies on the piece when `f`, `N(x')` and `u0` do not vanish there.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section AwayPt

variable {K : Type u} [Field K] [IsAlgClosed K]

end AwayPt

section AJPiece

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

/-- **The piece `Spec LocR → X0`** as `LawRing K F → LocR`. -/
noncomputable def lawMapP : LawRing K F →ₐ[K] LocR c0 D c :=
  IsLocalization.Away.liftAlgHom (f := (awayι (K := K) (convU c0 D c)).comp (convS c0 D c)) (lawPre K F).u0
    (isUnit_convU c0 D c)

theorem lawMapP_comp : (lawMapP c0 D c).comp (awayι (K := K) (lawPre K F).u0) =
    (awayι (K := K) (convU c0 D c)).comp (convS c0 D c) :=
  AlgHom.ext fun t => by
    rw [AlgHom.comp_apply, awayι_apply, lawMapP, IsLocalization.Away.liftAlgHom_apply,
      IsLocalization.Away.lift_eq]
    rfl

theorem comp_lawMapP (x : LocR c0 D c →ₐ[K] K) :
    (x.comp (lawMapP c0 D c)).comp (awayι (K := K) (lawPre K F).u0) =
      (x.comp (awayι (K := K) (convU c0 D c))).comp (convS c0 D c) := by
  rw [AlgHom.comp_assoc, lawMapP_comp, ← AlgHom.comp_assoc]

end AJPiece

end RamanujanPetersson.JacComplete

end


