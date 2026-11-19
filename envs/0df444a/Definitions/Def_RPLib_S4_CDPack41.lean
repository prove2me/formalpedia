-- Prove2me | Definitions.Def_RPLib_S4_CDPack41
-- name    : RPLib_S4_CDPack41
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T13:38:44.66442+00:00
-- url     : https://prove2.me/theorems/890adaa0-d14a-4469-ac31-c0d26a0b397c
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 41 of 71
-- statement:
--   Part 41 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_AJPieceA1`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0` [pack-only part AJPieceA1: `exists_away_pt`, `pieceN`, `ConvR`, `convφ`, `isUnit_convφ`, `convS`, `comp_convS`, `convU`, `LocR`, `pieceIn`, `isUnit_convU`]
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack36c
import Definitions.Def_RPLib_S4_CDPack40

/-!
# Curve-duality library package, part 41 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_AJPieceA1`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0` [pack-only part AJPieceA1: `exists_away_pt`, `pieceN`, `ConvR`, `convφ`, `isUnit_convφ`, `convS`, `comp_convS`, `convU`, `LocR`, `pieceIn`, `isUnit_convU`]
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_AJPieceA1 =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0` [pack-only part AJPieceA1: `exists_away_pt`, `pieceN`, `ConvR`, `convφ`, `isUnit_convφ`, `convS`, `comp_convS`, `convU`, `LocR`, `pieceIn`, `isUnit_convU`]

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

/-- A `K`-point not killing `ω` extends to `A[1/ω]`. -/
theorem exists_away_pt {A : Type u} [CommRing A] [Algebra K A] (Q : A →ₐ[K] K) (ω : A) (h : Q ω ≠ 0) :
    ∃ x : Localization.Away ω →ₐ[K] K, x.comp (awayι (K := K) ω) = Q :=
  ⟨liftPt (B := K) Q ω fun y => by rw [show y (Q ω) = Q ω from y.commutes (Q ω)]; exact h,
    liftPt_comp (B := K) Q ω _⟩

end AwayPt

section AJPiece

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

/-- `N(x')` on the piece. -/
noncomputable def pieceN : PieceR D c := pieceMap D c (normS K (xS K F c0))

/-- `B'[1/f][1/N(x')]`. -/
abbrev ConvR : Type u := Localization.Away (pieceN c0 D c)

/-- The piece over `ConvR`. -/
noncomputable def convφ : SymRing K (Rfin K (SynF K F c0)) (genusFK K (SynF K F c0)) →ₐ[K] ConvR c0 D c :=
  (awayι (K := K) (pieceN c0 D c)).comp (pieceMap D c)

theorem isUnit_convφ : IsUnit (convφ c0 D c (normS K (xS K F c0))) :=
  IsLocalization.Away.algebraMap_isUnit (pieceN c0 D c)

/-- **The piece in `F`-coordinates**: `Sym^g(Rfin F) → ConvR`. -/
noncomputable def convS : SymRing K (Rfin K F) (genusFK K F) →ₐ[K] ConvR c0 D c :=
  convSym c0 (convφ c0 D c) (isUnit_convφ c0 D c) (genusFK_eq (synEquiv K F c0)).symm

theorem comp_convS (y : ConvR c0 D c →ₐ[K] K) :
    y.comp (convS c0 D c) =
      symPt (convPt c0 (convφ c0 D c) (isUnit_convφ c0 D c) (genusFK_eq (synEquiv K F c0)).symm y) :=
  comp_convSym c0 _ _ _ y

/-- `u0` on the piece. -/
noncomputable def convU : ConvR c0 D c := convS c0 D c (lawPre K F).u0

/-- **The coordinate ring of the piece**. -/
abbrev LocR : Type u := Localization.Away (convU c0 D c)

/-- `B' → LocR` (`Spec LocR` is an open of `Spec B'`). -/
noncomputable def pieceIn : Rfin K (SynF K F c0) →ₐ[K] LocR c0 D c :=
  (awayι (K := K) (convU c0 D c)).comp ((awayι (K := K) (pieceN c0 D c)).comp (pieceι D c))

theorem isUnit_convU : IsUnit (((awayι (K := K) (convU c0 D c)).comp (convS c0 D c)) (lawPre K F).u0) :=
  IsLocalization.Away.algebraMap_isUnit (convU c0 D c)

end AJPiece

end RamanujanPetersson.JacComplete

end


