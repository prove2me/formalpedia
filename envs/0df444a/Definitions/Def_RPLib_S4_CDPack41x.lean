-- Prove2me | Definitions.Def_RPLib_S4_CDPack41x
-- name    : RPLib_S4_CDPack41x
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T15:01:24.756021+00:00
-- url     : https://prove2.me/theorems/ca446e2c-094e-4f3c-9925-07c76c61a60f
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 41x of 71
-- statement:
--   Part 41x of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_AJVal2B`: The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)` [pack-only part AJVal2B: `isOpenImmersion_pieceIn`]
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack41w

/-!
# Curve-duality library package, part 41x of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_AJVal2B`: The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)` [pack-only part AJVal2B: `isOpenImmersion_pieceIn`]
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_AJVal2B =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)` [pack-only part AJVal2B: `isOpenImmersion_pieceIn`]

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

section PieceVal

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

-- S13 11-18: the kernel check of this instance (instance diamonds on LocR) costs ~230k heartbeats; the server
-- elaborates with Elab.async=false, so they count toward the command (laptop -DElab.async=false: 286609 in all)
set_option maxHeartbeats 1000000 in
/-- `Spec LocR → Spec B'` is an open immersion (three successive localizations away from one element). -/
instance isOpenImmersion_pieceIn :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (R := Rfin K (SynF K F c0)) (S := LocR c0 D c)
      (pieceIn c0 D c : Rfin K (SynF K F c0) →+* LocR c0 D c))) := by
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (awayι (K := K) (convU c0 D c) : ConvR c0 D c →+* LocR c0 D c))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of (ConvR c0 D c)) (convU c0 D c)
  have h2 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (awayι (K := K) (pieceN c0 D c) : PieceR D c →+* ConvR c0 D c))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of (PieceR D c)) (pieceN c0 D c)
  have h3 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (pieceι D c : Rfin K (SynF K F c0) →+* PieceR D c))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of (Rfin K (SynF K F c0))) (pieceF D c)
  have e : Spec.map (CommRingCat.ofHom (R := Rfin K (SynF K F c0)) (S := LocR c0 D c)
      (pieceIn c0 D c : Rfin K (SynF K F c0) →+* LocR c0 D c)) =
      Spec.map (CommRingCat.ofHom (awayι (K := K) (convU c0 D c) : ConvR c0 D c →+* LocR c0 D c)) ≫
        Spec.map (CommRingCat.ofHom (awayι (K := K) (pieceN c0 D c) : PieceR D c →+* ConvR c0 D c)) ≫
          Spec.map (CommRingCat.ofHom (pieceι D c : Rfin K (SynF K F c0) →+* PieceR D c)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  rw [e]
  infer_instance

end PieceVal

end RamanujanPetersson.JacComplete

end


