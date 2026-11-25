-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CMUniformizationSpread
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_CMUniformizationSpread
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:13.614795+00:00
-- url     : https://prove2.me/theorems/5dc7f800-6bc4-4196-af8a-881f7187d56d
-- title:
--   CMUniformization Spread
-- statement:
--   Definitions and structural lemmas for CMUniformization Spread, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CMUniformizationSpread.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.CMUniformizationSpread
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def omegaC (H : Host E) : ℂ := (1 + H.rt0) / 2
def pureSub {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    (pos : Bool) : Submodule (𝓞 E) D.La where
  carrier := {x | ∀ j, (ty j (H.rt : E) = H.rt0 ↔ pos = false) → P x j = 0}
  add_mem' := by
    intro x y hx hy j hj
    simp [hx j hj, hy j hj]
  zero_mem' := by
    intro j _
    simp
  smul_mem' := by
    intro a x hx j hj
    rw [hP.1, hx j hj, mul_zero]
def IsCMUnif (H : Host E) {k : Type} [Field k] (κ : k →+* ℂ) (A : Over (Sp k)) [GrpObj A]
    (e : ℂ → (Over.mk (spMap κ) ⟶ A)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧
    (∀ z, e z = 1 ↔ ∃ m n : ℤ, z = m + n * omegaC H) ∧ IsHolTo Set.univ (fun z => (e z).left)
section Alg
variable {k R : Type} [CommRing k] [CommRing R] {X : Scheme.{0}}
abbrev curveOver (A : Over (Sp k)) (a : k →+* R) (y : Sp R ⟶ X) : Over X :=
  Over.mk (pullback.snd A.hom (spMap a) ≫ y)
def img {A : Over (Sp k)} {a : k →+* R} {y : Sp R ⟶ X} {G : Over X} (φ : curveOver A a y ⟶ G)
    {Z : Scheme.{0}} (t : Z ⟶ Sp R) (p : Over.mk (t ≫ spMap a) ⟶ A) : Over.mk (t ≫ y) ⟶ G :=
  (Over.homMk (pullback.lift p.left t (Over.w p)) (pullback.lift_snd_assoc _ _ _ _) : Over.mk (t ≫ y) ⟶ curveOver A a y) ≫ φ
def IsAlgFamily (D : Datum H) (C : Out.PolAV (Sp k)) (t : SAB H X) (a : k →+* R) (y : Sp R ⟶ X) (ρ : R)
    (pos : Bool) (M : Submodule (𝓞 E) D.La) (φ : M → (curveOver C.A a y ⟶ t.G)) : Prop :=
  (∀ (x : M) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (p q : Over.mk (s ≫ spMap a) ⟶ C.A),
      img (φ x) s (p * q) = img (φ x) s p * img (φ x) s q) ∧
  (∀ x x' : M, φ (x + x') = φ x * φ x') ∧
  (∀ (c : 𝓞 E) (x : M), φ (c • x) = φ x ≫ t.act.act c) ∧
  (∀ (x : M) (v : epsR k ⟶ C.A), IsTangent v →
    ∀ vR : Over.mk (spMap (algebraMap R (DualNumber R)) ≫ spMap a) ⟶ C.A,
      vR.left = spMap (Chart.dualMapR a) ≫ v.left →
      (img (φ x) _ vR ≫ t.act.act H.rt).left =
        spMap (epsScaleR (if pos then ρ else -ρ)) ≫ (img (φ x) _ vR).left) ∧
  ∀ x : M, ∃ N : ℕ, 0 < N ∧
    LBIso (lbPow (t.PP.L.pull (φ x).left) N)
      (lbPow (C.L.pull (pullback.fst C.A.hom (spMap a))) (N * (D.EF (H.w0 • (x : D.La)) (x : D.La)).natAbs))
end Alg
def CMSpread : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n)
    (P : (U.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ty P), σ (baseKA l).ρ = H.rt0 →
    ∀ (k : Type) [Field k] [NumberField k] [Algebra k ℂ] (C : Out.PolAV (Sp k)), C.g = 1 →
    ∀ e : ℂ → (Over.mk (spMap (algebraMap k ℂ)) ⟶ C.A), IsCMUnif H (algebraMap k ℂ) C.A e →
    ∃ (R : Subalgebra k ℂ) (σR : KA l →+* R) (y : Sp R ⟶ Xo.X)
      (φ : ∀ pos : Bool, pureSub hP pos → (curveOver C.A (algebraMap k R) y ⟶ Xo.univ.t.G)),
      R.FG ∧ (∀ b, (σR b : ℂ) = σ b) ∧ y ≫ Xo.s = spMap σR ∧
      spMap R.val.toRingHom ≫ y = U.u i P ∧
      ∀ pos : Bool,
        IsAlgFamily (U.Di i) C Xo.univ.t (algebraMap k R) y (σR (baseKA l).ρ) pos (pureSub hP pos) (φ pos) ∧
        (∀ w : C.A ⟶ C.A, (∀ z, e (omegaC H * z) = e z ≫ w) →
          ∀ (x : pureSub hP pos) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (p : Over.mk (s ≫ spMap (algebraMap k R)) ⟶ C.A),
            img (φ pos x) s (p ≫ w) =
              img (φ pos x) s p ≫ Xo.univ.t.act.act (if pos then H.w0 else H.bar H.w0)) ∧
        ∀ (x : pureSub hP pos) (z : ℂ) (p : Sp ℂ ⟶ pullback C.A.hom (spMap (algebraMap k R))),
          p ≫ pullback.fst _ _ = (e z).left → p ≫ pullback.snd _ _ = spMap R.val.toRingHom →
          p ≫ (φ pos x).left = (U.ex i P (z • P (x : (U.Di i).La))).left
example {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    (x : pureSub hP true) : P (H.rt • (x : D.La)) = H.rt0 • P x := by
  funext j
  rw [hP.1, Pi.smul_apply, smul_eq_mul]
  by_cases h : ty j (H.rt : E) = H.rt0
  · rw [h]
  · rw [x.2 j (by simp [h]), mul_zero, mul_zero]
example {k R : Type} [CommRing k] [CommRing R] (a : k →+* R) (A : Over (Sp k)) (v : epsR k ⟶ A) :
    ∃ vR : Over.mk (spMap (algebraMap R (DualNumber R)) ≫ spMap a) ⟶ A,
      vR.left = spMap (Chart.dualMapR a) ≫ v.left := by
  refine ⟨Over.homMk (spMap (Chart.dualMapR a) ≫ v.left) ?_, rfl⟩
  have hv : v.left ≫ A.hom = spMap (algebraMap k (DualNumber k)) := Over.w v
  change (spMap (Chart.dualMapR a) ≫ v.left) ≫ A.hom = spMap (algebraMap R (DualNumber R)) ≫ spMap a
  rw [Category.assoc, hv, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext b <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
end GlobalTheory.IndefiniteRowSideFullHecke.CMUniformizationSpread


