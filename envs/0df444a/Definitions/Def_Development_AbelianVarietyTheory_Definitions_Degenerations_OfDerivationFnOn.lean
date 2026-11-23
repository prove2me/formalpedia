-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
-- name    : Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:54.693999+00:00
-- url     : https://prove2.me/theorems/af645e59-fa57-4e2c-be2d-c671d75d8a71
-- title:
--   Of Derivation Fn On
-- statement:
--   Definitions and structural lemmas for Of Derivation Fn On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/OfDerivationFnOn.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.SS
variable (R : Type) [CommRing R] {K : Type} [Field K] [Algebra R K]
structure Model (A : Over (Sp K)) where
  Y : Over (Sp R)
  e : (Over.pullback (spMap (algebraMap R K))).obj Y ≅ A
  smooth : Smooth Y.hom
  sep : IsSeparated Y.hom
  qc : QuasiCompact Y.hom
variable {R} {A A' : Over (Sp K)}
def Model.j (M : Model R A) : A.left ⟶ M.Y.left := M.e.inv.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))
def Model.twist (M : Model R A) (f : A ≅ A') : Model R A' := ⟨M.Y, M.e ≪≫ f, M.smooth, M.sep, M.qc⟩
def Model.prod (M : Model R A) (N : Model R A') : Model R (A ⊗ A') where
  Y := M.Y ⊗ N.Y
  e := (Functor.Monoidal.μIso (Over.pullback (spMap (algebraMap R K))) M.Y N.Y).symm ≪≫ tensorIso M.e N.e
  smooth := by have := M.smooth; have := N.smooth; show Smooth (pullback.fst _ _ ≫ M.Y.hom); infer_instance
  sep := by have := M.sep; have := N.sep; show IsSeparated (pullback.fst _ _ ≫ M.Y.hom); infer_instance
  qc := by have := M.qc; have := N.qc; show QuasiCompact (pullback.fst _ _ ≫ M.Y.hom); infer_instance
def Model.sp [IsLocalRing R] (M : Model R A) : Set M.Y.left := {y | M.Y.hom y = IsLocalRing.closedPoint R}
def Model.Irr [IsLocalRing R] (M : Model R A) : Prop := IsIrreducible M.sp
def Extends (M : Model R A) (N : Model R A') (f : A ⟶ A') (U : M.Y.left.Opens) (g : U.toScheme ⟶ N.Y.left) : Prop :=
  g ≫ N.Y.hom = U.ι ≫ M.Y.hom ∧ (M.j ∣_ U) ≫ g = (M.j ⁻¹ᵁ U).ι ≫ f.left ≫ N.j
def DefAt (M : Model R A) (N : Model R A') (f : A ⟶ A') (y : M.Y.left) : Prop :=
  ∃ (U : M.Y.left.Opens) (g : U.toScheme ⟶ N.Y.left), y ∈ U ∧ Extends M N f U g
def IsoAt (M : Model R A) (N : Model R A') (f : A ⟶ A') (y : M.Y.left) : Prop :=
  ∃ (U : M.Y.left.Opens) (g : U.toScheme ⟶ N.Y.left), y ∈ U ∧ Extends M N f U g ∧ IsOpenImmersion g
def GenIso [IsLocalRing R] (M : Model R A) (N : Model R A') (f : A ⟶ A') : Prop := ∃ y ∈ M.sp, IsoAt M N f y
def Model.Le (M N : Model R A) : Prop := ∃ g : M.Y ⟶ N.Y, IsOpenImmersion g.left ∧ M.j ≫ g.left = N.j
def Compat (M N : Model R A) : Prop :=
  ∃ (W : Model R A) (g : W.Y ⟶ M.Y) (h : W.Y ⟶ N.Y), IsOpenImmersion g.left ∧ IsOpenImmersion h.left ∧
    W.j ≫ g.left = M.j ∧ W.j ≫ h.left = N.j ∧ IsClosedImmersion (lift g h).left
def WeakNeron [IsLocalRing R] {I : Type} (M : I → Model R A) : Prop :=
  ∀ (R' K' : Type) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Field K'] [Algebra R' K']
    [IsFractionRing R' K'], (IsLocalRing.maximalIdeal R).map (algebraMap R R') = IsLocalRing.maximalIdeal R' →
    ∀ a : Sp K' ⟶ A.left, a ≫ A.hom ≫ spMap (algebraMap R K) = spMap ((algebraMap R' K').comp (algebraMap R R')) →
      ∃ (i : I) (b : Sp R' ⟶ (M i).Y.left), b ≫ (M i).Y.hom = spMap (algebraMap R R') ∧ spMap (algebraMap R' K') ≫ b = a ≫ (M i).j
def cstK (A : Over (Sp K)) (U : A.left.Opens) : K →+* Γ(A.left, U) :=
  (A.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
structure VF (A : Over (Sp K)) where
  D : ∀ U : A.left.Opens, Γ(A.left, U) →+ Γ(A.left, U)
  leibniz : ∀ U a b, D U (a * b) = a * D U b + b * D U a
  const : ∀ U c, D U (cstK A U c) = 0
  res : ∀ (U V : A.left.Opens) (h : V ≤ U) a,
    D V ((A.left.presheaf.map (homOfLE h).op).hom a) = (A.left.presheaf.map (homOfLE h).op).hom (D U a)
def jac {I : Type} [Fintype I] [DecidableEq I] (D : I → VF A) (U : A.left.Opens) (t : I → Γ(A.left, U)) : Γ(A.left, U) :=
  (Matrix.of fun i j => (D i).D U (t j)).det
def IsFrame {I : Type} [Fintype I] [DecidableEq I] (D : I → VF A) : Prop :=
  SmoothOfRelativeDimension (Fintype.card I) A.hom ∧ ∀ x : A.left, ∃ (U : A.left.Opens) (t : I → Γ(A.left, U)), x ∈ U ∧ IsUnit (jac D U t)
def HasOrd [IsLocalRing R] {I : Type} [Fintype I] [DecidableEq I] (M : Model R A) (D : I → VF A) (π : R) (n : ℤ) : Prop :=
  (∀ (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)), ∃ s : Γ(M.Y.left, U),
    jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) = cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s) ∧
  ∃ (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)) (s : Γ(M.Y.left, U)), ((U : Set M.Y.left) ∩ M.sp).Nonempty ∧ IsUnit s ∧
    jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) = cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s
section
variable [GrpObj A] [IsCommMonObj A]
def transl (a : 𝟙_ (Over (Sp K)) ⟶ A) : A ≅ A where
  hom := (toUnit A ≫ a) * 𝟙 A
  inv := (toUnit A ≫ a)⁻¹ * 𝟙 A
  hom_inv_id := by simp [MonObj.comp_mul, GrpObj.comp_inv, toUnit_unique (_ ≫ toUnit A) (toUnit A), ← Category.assoc]
  inv_hom_id := by simp [MonObj.comp_mul, GrpObj.comp_inv, toUnit_unique (_ ≫ toUnit A) (toUnit A), ← Category.assoc]
def shear (A : Over (Sp K)) [GrpObj A] : Bool → (A ⊗ A ⟶ A ⊗ A)
  | true => lift (fst A A) (fst A A * snd A A)
  | false => lift (fst A A) ((fst A A)⁻¹ * snd A A)
def BirLaw [IsLocalRing R] (M : Model R A) : Prop :=
  M.Irr ∧ (∀ b, GenIso (M.prod M) (M.prod M) (shear A b)) ∧ GenIso M M (ι[A])
def Strict [IsLocalRing R] (M : Model R A) : Prop :=
  BirLaw M ∧ ∀ b, ∀ x ∈ M.sp,
    (∃ z, (fst M.Y M.Y).left z = x ∧ IsoAt (M.prod M) (M.prod M) (shear A b) z) ∧
    ∃ z, (snd M.Y M.Y).left z = x ∧ IsoAt (M.prod M) (M.prod M) (shear A b) z
end
def SH (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K] : Prop :=
  IsDiscreteValuationRing R ∧ HenselianLocalRing R ∧ IsAlgClosed (IsLocalRing.ResidueField R) ∧ IsFractionRing R K
def SmConn {S : Scheme.{0}} (G : Over S) [GrpObj G] : Prop :=
  IsCommMonObj G ∧ Smooth G.hom ∧ IsSeparated G.hom ∧ QuasiCompact G.hom ∧ GeometricallyConnected G.hom
def FrobLike {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (F : End G) (q : ℕ) : Prop :=
  IsMonHom (show G ⟶ G from F) ∧ ∀ (U : G.left.Opens) (f : Γ(G.left, U)), Set.range (η[G]).left ⊆ U → ∃ m : ℕ, 1 ≤ m ∧ ∃ (U' : G.left.Opens)
    (h : U' ≤ U) (h' : U' ≤ (show G ⟶ G from F ^ m).left ⁻¹ᵁ U), Set.range (η[G]).left ⊆ U' ∧
    ((show G ⟶ G from F ^ m).left.appLE U U' h').hom f = (G.left.presheaf.map (homOfLE h).op).hom f ^ (q ^ m)
def Wt {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (i : splitTorus S X ⟶ G) (V : G.left.Opens)
    (u : Γ(G.left, V)) (χ : X) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
    (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom u = t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u
def GoodOpen {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (i : splitTorus S X ⟶ G) (V : G.left.Opens) : Prop :=
  IsAffineOpen V ∧ (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V ∧
    ∃ u : Multiplicative X →* Γ(G.left, V)ˣ, ∀ χ, Wt i V (u (Multiplicative.ofAdd χ)).val χ
def IsQuot {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B] (i : T ⟶ G) (q : G ⟶ B) : Prop :=
  IsMonHom i ∧ IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsPullback i (toUnit _) q (η[B]) ∧ SmConn B
def polyPt {S : Scheme.{0}} {G Z : Over S} [GrpObj G] (F : End G) (P : Polynomial ℤ) (x : Z ⟶ G) : Z ⟶ G :=
  ((List.range (P.natDegree + 1)).map fun n => (x ≫ (show G ⟶ G from F ^ n)) ^ P.coeff n).prod
def Defect {R B R' : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R') (π : R) (c : ℕ) : Prop :=
  letI := a.toRingHom.toAlgebra
  ∀ w ∈ Submodule.torsion R' (TensorProduct B R' (KaehlerDifferential R B)), algebraMap R R' π ^ c • w = 0
def Unr {R : Type} [CommRing R] (π : R) (R' : Type) [CommRing R'] [Algebra R R'] : Prop :=
  ∃ _ : IsDomain R', IsDiscreteValuationRing R' ∧ Irreducible (algebraMap R R' π)
def Model.ofScheme (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K] (Y : Over (Sp R))
    [h₁ : Smooth Y.hom] [h₂ : IsSeparated Y.hom] [h₃ : QuasiCompact Y.hom] :
    Model R ((Over.pullback (spMap (algebraMap R K))).obj Y) := ⟨Y, Iso.refl _, h₁, h₂, h₃⟩
def Model.ofAlgebra (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K] (B : Type) [CommRing B] [Algebra R B]
    [Algebra.Smooth R B] :
    Model R ((Over.pullback (spMap (algebraMap R K))).obj (Over.mk (spMap (algebraMap R B)))) where
  Y := Over.mk (spMap (algebraMap R B))
  e := Iso.refl _
  smooth := by
    show Smooth (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  sep := by show IsSeparated (Spec.map _); infer_instance
  qc := by show QuasiCompact (Spec.map _); infer_instance
example (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K] (n : ℕ) :
    Model R ((Over.pullback (spMap (algebraMap R K))).obj
      (Over.mk (spMap (algebraMap R (MvPolynomial (Fin n) R))))) :=
  haveI : Algebra.Smooth R (MvPolynomial (Fin n) R) := ⟨inferInstance, inferInstance⟩
  Model.ofAlgebra R K (MvPolynomial (Fin n) R)
theorem Model.Le.trans {M N P : Model R A} (h : M.Le N) (h' : N.Le P) : M.Le P := by
  obtain ⟨g, hg, hgj⟩ := h
  obtain ⟨g', hg', hgj'⟩ := h'
  refine ⟨g ≫ g', ?_, ?_⟩
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left, ← Category.assoc, hgj, hgj']
def VF.zero (A : Over (Sp K)) : VF A where
  D _ := 0
  leibniz _ _ _ := by simp
  const _ _ := rfl
  res _ _ _ _ := by simp
section LocDer
variable {k B : Type} [CommRing k] [CommRing B] [Algebra k B] (d : Derivation k B B) (S : Submonoid B)
def derDual : B →+* DualNumber (Localization S) where
  toFun b := (algebraMap B (Localization S) b, algebraMap B (Localization S) (d b))
  map_one' := TrivSqZeroExt.ext (map_one _) (by
    show algebraMap B (Localization S) (d 1) = 0
    rw [Derivation.map_one_eq_zero, map_zero])
  map_mul' a b := TrivSqZeroExt.ext (map_mul _ a b) (by
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    show algebraMap B (Localization S) (d (a * b)) = algebraMap B (Localization S) a * algebraMap B (Localization S) (d b) +
      algebraMap B (Localization S) (d a) * algebraMap B (Localization S) b
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]; ring)
  map_zero' := TrivSqZeroExt.ext (map_zero _) (by
    show algebraMap B (Localization S) (d 0) = 0
    rw [map_zero, map_zero])
  map_add' a b := TrivSqZeroExt.ext (map_add _ a b) (by
    show algebraMap B (Localization S) (d (a + b)) = algebraMap B (Localization S) (d a) + algebraMap B (Localization S) (d b)
    rw [map_add, map_add])
theorem derDual_isUnit (s : S) : IsUnit (derDual d S s) := by
  refine TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ?_
  exact IsLocalization.map_units (Localization S) s
def locDual : Localization S →+* DualNumber (Localization S) := IsLocalization.lift (derDual_isUnit d S)
theorem locDual_fst (x : Localization S) : (locDual d S x).fst = x := by
  let φ : Localization S →+* Localization S :=
    (TrivSqZeroExt.fstHom (Localization S) (Localization S) (Localization S)).toRingHom.comp (locDual d S)
  have hφ : φ = RingHom.id _ := by
    refine IsLocalization.ringHom_ext S (RingHom.ext fun b => ?_)
    simp only [φ, RingHom.comp_apply, locDual, IsLocalization.lift_eq, RingHom.id_apply]
    rfl
  exact RingHom.congr_fun hφ x
def locDer : Localization S →+ Localization S where
  toFun x := (locDual d S x).snd
  map_zero' := by simp
  map_add' a b := by simp
theorem locDer_mul (x y : Localization S) : locDer d S (x * y) = x * locDer d S y + y * locDer d S x := by
  show (locDual d S (x * y)).snd = x * (locDual d S y).snd + y * (locDual d S x).snd
  rw [map_mul, DualNumber.snd_mul, locDual_fst, locDual_fst]
  ring
theorem locDer_algebraMap (b : B) : locDer d S (algebraMap B _ b) = algebraMap B _ (d b) := by
  show (locDual d S (algebraMap B _ b)).snd = _
  unfold locDual
  rw [IsLocalization.lift_eq]
  rfl
theorem locDer_mk (a : B) (s : S) :
    locDer d S (Localization.mk a s) = Localization.mk (s.1 * d a - a * d s.1) (s * s) := by
  have hu : IsUnit (algebraMap B (Localization S) s) := IsLocalization.map_units (Localization S) s
  rw [Localization.mk_eq_mk']
  have key := locDer_mul d S (IsLocalization.mk' (Localization S) a s) (algebraMap B _ s)
  rw [IsLocalization.mk'_spec, locDer_algebraMap, locDer_algebraMap] at key
  have spec : algebraMap B (Localization S) s * IsLocalization.mk' (Localization S) a s = algebraMap B _ a :=
    IsLocalization.mk'_spec' _ _ _
  have spec2 : algebraMap B (Localization S) s * algebraMap B (Localization S) s *
      IsLocalization.mk' (Localization S) (s.1 * d a - a * d s.1) (s * s) = algebraMap B _ (s.1 * d a - a * d s.1) := by
    rw [← map_mul, ← Submonoid.coe_mul, IsLocalization.mk'_spec']
  refine (hu.mul hu).mul_left_cancel ?_
  rw [spec2, map_sub, map_mul, map_mul]
  linear_combination (-algebraMap B (Localization S) s) * key - algebraMap B (Localization S) (d s.1) * spec
end LocDer
section SpecVF
variable {B : Type} [CommRing B] [Algebra K B]
abbrev denoms (B : Type) [CommRing B] (x : PrimeSpectrum B) : Submonoid B := x.asIdeal.primeCompl
def secDer (d : Derivation K B B) (U : (Sp B).Opens) : Γ(Sp B, U) →+ Γ(Sp B, U) where
  toFun s := ⟨fun x => locDer d (denoms B x.1) (s.1 x), fun x => by
    obtain ⟨V, m, i, r, t, w⟩ := s.2 x
    refine ⟨V, m, i, t * d r - r * d t, t * t, fun y => ?_⟩
    obtain ⟨ht, hw⟩ := w y
    refine ⟨(denoms B y.1).mul_mem ht ht, ?_⟩
    exact (congrArg (locDer d (denoms B y.1)) hw).trans (locDer_mk d (denoms B y.1) r ⟨t, ht⟩)⟩
  map_zero' := Subtype.ext (funext fun x => map_zero (locDer d (denoms B x.1)))
  map_add' a b := Subtype.ext (funext fun x => map_add (locDer d (denoms B x.1)) (a.1 x) (b.1 x))
def fnOn (B : Type) [CommRing B] (U : (Sp B).Opens) : B →+* Γ(Sp B, U) :=
  ((Sp B).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
theorem secDer_fnOn (d : Derivation K B B) (U : (Sp B).Opens) (b : B) : secDer d U (fnOn B U b) = fnOn B U (d b) := by
  apply Subtype.ext
  funext x
  show locDer d (denoms B x.1) ((fnOn B U b).1 x) = (fnOn B U (d b)).1 x
  have h : ∀ c : B, (fnOn B U c).1 x = algebraMap B (Localization (denoms B x.1)) c := fun c => rfl
  rw [h, h, locDer_algebraMap]
theorem cstK_spec (U : (Sp B).Opens) (c : K) :
    cstK (Over.mk (spMap (algebraMap K B))) U c = fnOn B U (algebraMap K B c) := by
  have e := congrArg (fun g => (g ≫ (Sp B).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K B)))
  exact e.symm
def VF.ofDerivation (d : Derivation K B B) : VF (Over.mk (spMap (algebraMap K B))) where
  D U := secDer d U
  leibniz U a b := Subtype.ext (funext fun x => locDer_mul d (denoms B x.1) (a.1 x) (b.1 x))
  const U c := by
    have := secDer_fnOn d U (algebraMap K B c)
    rw [Derivation.map_algebraMap, map_zero] at this
    exact (congrArg (secDer d U) (cstK_spec U c)).trans this
  res U V h a := rfl
end SpecVF
end GlobalTheory.SS
end


