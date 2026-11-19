-- Prove2me | Definitions.Def_RPLib_S4_CDPack41b
-- name    : RPLib_S4_CDPack41b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T14:23:18.607962+00:00
-- url     : https://prove2.me/theorems/cdcd8a2f-2c06-40bf-8bf6-8ea07b0f2c37
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 41b of 71
-- statement:
--   Part 41b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_AJVal2A`: The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)` [pack-only part AJVal2A: all but `isOpenImmersion_pieceIn`]
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack41w

/-!
# Curve-duality library package, part 41b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_AJVal2A`: The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)` [pack-only part AJVal2A: all but `isOpenImmersion_pieceIn`]
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_AJVal2A =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)` [pack-only part AJVal2A: all but `isOpenImmersion_pieceIn`]

* `plC c0 Q` (the place of `F` at a `K`-point `Q` of `B'`), `plP c0 D c x`, `psiJ_plP`.
* **`kptO_ajPiece`**, **`ajPiece_kpt`**: the piece takes the value `ajPt P0 (plP c0 D c x)` (class `[Q] - [P0]`).
* `isOpenImmersion_pieceIn`: `Spec LocR → Spec B'` is an open immersion; `pieceIn_over`.
* **`ajChart P0 c0 : Spec B' ⟶ J`** glued (`JacChunk.glueY`) from the pieces; `ajChart_over`,
  **`ajChart_kpt`**: value `ajPt P0 (plC c0 Q)` at every closed point `kpt Q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- the instance diamonds on the nested localizations need nested synthPending (diagnostics, session 20)
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section PlP

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K)

/-- The place of `F` at a `K`-point of the chart ring `B' = Rfin (SynF K F c0)`. -/
noncomputable def plC (Q : Rfin K (SynF K F c0) →ₐ[K] K) : Place K F :=
  (synPlace c0).symm (Sum.inl (ptP Q))

variable {r : ℕ} (D : NuData K (SynF K F c0) (1 + r)) (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

/-- The place of `F` at a `K`-point of the piece. -/
noncomputable def plP (x : LocR c0 D c →ₐ[K] K) : Place K F :=
  plC c0 (x.comp (pieceIn c0 D c))

theorem psiJ_plP (x : LocR c0 D c →ₐ[K] K) :
    psiJ K F (kpt (x.comp (lawMapP c0 D c))) =
      kapP c0 D c - thetaK K F - clsK K F (Finsupp.single (plP c0 D c x) 1) :=
  psiJ_lawMapP c0 D c x

end PlP

section PieceVal

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

/-- **Value of the piece at a `K`-point**: `[Q] - [P0]`, `Q = plP c0 D c x`. -/
theorem kptO_ajPiece (x : LocR c0 D c →ₐ[K] K) :
    kptO (R := LocR c0 D c) x ≫ ajPiece P0 c0 D c = ajK K F P0 (plP c0 D c x) :=
  kptO_ajMap (R := LocR c0 D c) K F P0 (lawMapP c0 D c) (kapP c0 D c) x _ (psiJ_plP c0 D c x)

/-- **Value of the piece at a closed point** `kpt x`. -/
theorem ajPiece_kpt (x : LocR c0 D c →ₐ[K] K) :
    (ajPiece P0 c0 D c).left (kpt (A := LocR c0 D c) x) = ajPt K F P0 (plP c0 D c x) :=
  ajMap_kpt (R := LocR c0 D c) K F P0 (lawMapP c0 D c) (kapP c0 D c) x _ (psiJ_plP c0 D c x)

theorem pieceIn_over :
    Spec.map (CommRingCat.ofHom (pieceIn c0 D c : Rfin K (SynF K F c0) →+* LocR c0 D c)) ≫
      sR K (Rfin K (SynF K F c0)) = sR K (LocR c0 D c) :=
  SpecMap_sR _

end PieceVal

end RamanujanPetersson.JacComplete

end


