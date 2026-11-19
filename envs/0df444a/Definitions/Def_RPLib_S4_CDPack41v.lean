-- Prove2me | Definitions.Def_RPLib_S4_CDPack41v
-- name    : RPLib_S4_CDPack41v
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T14:01:46.987189+00:00
-- url     : https://prove2.me/theorems/0674b46c-a50e-4dab-9868-3d14c6663fd6
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 41v of 71
-- statement:
--   Part 41v of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_AJPieceB2`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0` [pack-only part AJPieceB2: `clsK_convS`, `psiJ_lawMapP`]
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack41u
import Definitions.Def_RPLib_S4_CDPack41t

/-!
# Curve-duality library package, part 41v of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_AJPieceB2`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0` [pack-only part AJPieceB2: `clsK_convS`, `psiJ_lawMapP`]
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_AJPieceB2 =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0` [pack-only part AJPieceB2: `clsK_convS`, `psiJ_lawMapP`]

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

/-- **Class of the converted piece**: `[conv ν(Q + c)] = κ - [Q]`. -/
theorem clsK_convS (y : ConvR c0 D c →ₐ[K] K) :
    clsK K F (Zdiv (ptSet (y.comp (convS c0 D c)))) = kapP c0 D c -
      clsK K F (Finsupp.single ((synPlace c0).symm
        (Sum.inl (ptP ((y.comp (awayι (K := K) (pieceN c0 D c))).comp (pieceι D c))))) 1) := by
  have h1 : divMap (synEquiv K F c0) (Zdiv (ptSet (y.comp (convS c0 D c)))) =
      Zdiv (ptSet (y.comp (convφ c0 D c))) :=
    divMap_Zdiv_convSym c0 (convφ c0 D c) (isUnit_convφ c0 D c) (genusFK_eq (synEquiv K F c0)).symm y
  have h2 := clsK_pieceMap D c (y.comp (awayι (K := K) (pieceN c0 D c)))
  rw [kapP, ← clsK_single_syn, ← map_sub, AddEquiv.eq_symm_apply, picMap_clsK, h1, convφ,
    ← AlgHom.comp_assoc, h2]
  abel

/-- **The class function on the piece**: `ψ(piece(Q)) = κ - [Θ] - [Q]`. -/
theorem psiJ_lawMapP (x : LocR c0 D c →ₐ[K] K) :
    psiJ K F (kpt (x.comp (lawMapP c0 D c))) = kapP c0 D c -
      clsK K F (ThetaD (lawData K F).Dm3 (lawData K F).Dm2 (lawData K F).c0 (lawData K F).c1) -
      clsK K F (Finsupp.single ((synPlace c0).symm (Sum.inl (ptP (x.comp (pieceIn c0 D c))))) 1) := by
  have e : x.comp (pieceIn c0 D c) =
      ((x.comp (awayι (K := K) (convU c0 D c))).comp (awayι (K := K) (pieceN c0 D c))).comp (pieceι D c) := rfl
  rw [e, psiJ, psiS_kpt, psiA, comp_lawMapP, psiL, clsK_convS]
  abel

end AJPiece

end RamanujanPetersson.JacComplete

end


