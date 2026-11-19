-- Prove2me | Definitions.Def_RPLib_S4_CDPack41d
-- name    : RPLib_S4_CDPack41d
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T15:10:45.164343+00:00
-- url     : https://prove2.me/theorems/ed477050-18c4-4ff4-b6a1-993651961050
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 41d of 71
-- statement:
--   Part 41d of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
--   * `Def_RP_JacComplete_AJGlue2`: The Jacobian (unit S4-JacComplete), part `AJGlue2`: the Abel-Jacobi map on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack41b
import Definitions.Def_RPLib_S4_CDPack41x
import Definitions.Def_RPLib_S4_CDPack41c

/-!
# Curve-duality library package, part 41d of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
* `Def_RP_JacComplete_AJGlue2`: The Jacobian (unit S4-JacComplete), part `AJGlue2`: the Abel-Jacobi map on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_AJGlue =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces

`B' = Rfin (SynF K F c0)`.
* `locallyOfFiniteType_sR`; the piece index `PIdx K F c0` and the open immersions `pj c0 i : Spec LocR → Spec B'`.
* `pj_kpt` (closed points), `pj_cov` (the pieces cover the closed points), `pj_over`.
The glued map `ajChart` is in part `AJGlue2`.
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

section Glue

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K]

/-- `Spec R → Spec K` is locally of finite type for a finite type `K`-algebra `R`. -/
instance locallyOfFiniteType_sR (R : Type u) [CommRing R] [Algebra K R] [Algebra.FiniteType K R] :
    LocallyOfFiniteType (sR K R) := by
  show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K R)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

variable [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- The index type of the AJ pieces on the chart `c0`. -/
abbrev PIdx (c0 : K) : Type u :=
  Σ r : ℕ, Σ _ : NuData K (SynF K F c0) (1 + r), Fin r → (Rfin K (SynF K F c0) →ₐ[K] K)

variable (P0 : Place K F) (c0 : K)

/-- The open immersion of the piece `i` into `Spec B'`. -/
noncomputable abbrev pj (i : PIdx K F c0) :
    Spec (.of (LocR c0 i.2.1 i.2.2)) ⟶ Spec (.of (Rfin K (SynF K F c0))) :=
  Spec.map (CommRingCat.ofHom (R := Rfin K (SynF K F c0)) (S := LocR c0 i.2.1 i.2.2)
    (pieceIn c0 i.2.1 i.2.2 : Rfin K (SynF K F c0) →+* LocR c0 i.2.1 i.2.2))

theorem pj_kpt (i : PIdx K F c0) (x : LocR c0 i.2.1 i.2.2 →ₐ[K] K) :
    pj c0 i (kpt (A := LocR c0 i.2.1 i.2.2) x) =
      kpt (A := Rfin K (SynF K F c0)) (x.comp (pieceIn c0 i.2.1 i.2.2)) :=
  SpecMap_kpt (A := Rfin K (SynF K F c0)) (B := LocR c0 i.2.1 i.2.2) (pieceIn c0 i.2.1 i.2.2) x

/-- The pieces cover the closed points of `Spec B'`. -/
theorem pj_cov (t : Spec (.of (Rfin K (SynF K F c0)))) (ht : IsClosed ({t} : Set (Spec (.of (Rfin K (SynF K F c0)))))) :
    ∃ i : PIdx K F c0, ∃ p : Spec (.of (LocR c0 i.2.1 i.2.2)), pj c0 i p = t := by
  obtain ⟨Q0, rfl⟩ := exists_kpt (K := K) (A := Rfin K (SynF K F c0)) t ht
  obtain ⟨r, D, c, x, rfl⟩ := exists_piece_through (F := F) c0 Q0
  exact ⟨⟨r, D, c⟩, kpt (A := LocR c0 D c) x, pj_kpt c0 ⟨r, D, c⟩ x⟩

theorem pj_over (i : PIdx K F c0) :
    (ajPiece P0 c0 i.2.1 i.2.2).left ≫ (Jac K F).hom = pj c0 i ≫ sR K (Rfin K (SynF K F c0)) :=
  (ajPiece_over P0 c0 i.2.1 i.2.2).trans (pieceIn_over c0 i.2.1 i.2.2).symm

end Glue

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacComplete_AJGlue2 =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGlue2`: the Abel-Jacobi map on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`

* `pj_comp`: the pieces agree at closed points over the same point of `Spec B'`.
* **`ajChart P0 c0 : Spec B' ⟶ J`** glued (`JacChunk.glueY`) from the pieces; `ajChart_over`
  (its value `ajChart_kpt` moved to AJCo, session 22, to keep this file under the 150 user-s cap).
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

section Glue

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K]

variable [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K)

set_option maxHeartbeats 800000 in
/-- The pieces agree at closed points over the same point of `Spec B'`. -/
theorem pj_comp (i i' : PIdx K F c0) (p : Spec (.of (LocR c0 i.2.1 i.2.2)))
    (p' : Spec (.of (LocR c0 i'.2.1 i'.2.2)))
    (hp : IsClosed ({p} : Set (Spec (.of (LocR c0 i.2.1 i.2.2)))))
    (hp' : IsClosed ({p'} : Set (Spec (.of (LocR c0 i'.2.1 i'.2.2)))))
    (e : pj c0 i p = pj c0 i' p') :
    (ajPiece P0 c0 i.2.1 i.2.2).left p = (ajPiece P0 c0 i'.2.1 i'.2.2).left p' := by
  obtain ⟨x, rfl⟩ := exists_kpt (K := K) (A := LocR c0 i.2.1 i.2.2) p hp
  obtain ⟨x', rfl⟩ := exists_kpt (K := K) (A := LocR c0 i'.2.1 i'.2.2) p' hp'
  have h1 := pj_kpt c0 i x
  have h2 := pj_kpt c0 i' x'
  have h : x.comp (pieceIn c0 i.2.1 i.2.2) = x'.comp (pieceIn c0 i'.2.1 i'.2.2) :=
    kpt_injective (K := K) (A := Rfin K (SynF K F c0)) (h1.symm.trans (e.trans h2))
  rw [ajPiece_kpt, ajPiece_kpt]
  unfold plP
  rw [h]

/-- **The Abel-Jacobi map on the chart** `Spec B'` (`B' = Rfin (SynF K F c0)`), glued from the pieces. -/
noncomputable def ajChart : Spec (.of (Rfin K (SynF K F c0))) ⟶ (Jac K F).left :=
  JacChunk.glueY (sR K (Rfin K (SynF K F c0))) (Jac K F).hom
    (fun i : PIdx K F c0 => Spec (.of (LocR c0 i.2.1 i.2.2))) (pj c0)
    (fun i => (ajPiece P0 c0 i.2.1 i.2.2).left) (pj_cov c0) (pj_over P0 c0) (pj_comp P0 c0)

theorem ajChart_over : ajChart P0 c0 ≫ (Jac K F).hom = sR K (Rfin K (SynF K F c0)) :=
  JacChunk.glueY_over _ _ _ _ _ _ _ _

end Glue

end RamanujanPetersson.JacComplete

end


