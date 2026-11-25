-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:25.653814+00:00
-- url     : https://prove2.me/theorems/d2ef5d8e-c8cd-4924-8734-8c4d1e6752fd
-- title:
--   Axes Vanishing Structure Sheaf Deg One
-- statement:
--   Definitions and structural lemmas for Axes Vanishing Structure Sheaf Deg One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/AxesVanishingStructureSheafDegOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_oneCocycle_vanishing_comma_of_basis
import Theorems.Thm_GlobalTheory_CatCoh_Desc_glue_comma_of_basis
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_cup
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_one
import Theorems.Thm_GlobalTheory_CechDR_exists_pair_below_two
import Theorems.Thm_GlobalTheory_CechDR_hasLoc_OAff
import Theorems.Thm_GlobalTheory_CechDR_pair_cover_affine
import Theorems.Thm_GlobalTheory_T_comma_descent_injective
import Theorems.Thm_GlobalTheory_T_comma_descent_restriction_equiv
import Theorems.Thm_GlobalTheory_T_twoCocycle_coboundary_of_basisFunctor
import Theorems.Thm_GlobalTheory_sep_of_factoring_cover

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
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AbCoh
def FP (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ) : Prop :=
  Module.Finite R M ∧ Module.Projective R M ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n
section Formal
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
def CohomZeroIsConstants : Prop := ∀ g : C0 F, d0 F g = 0 → ∃! r : R, ∀ T, g T = algebraMap R (F.obj T) r
def WedgeO : Prop :=
  ∃ e : ⋀[R]^2 (CatCoh.H1 F) ≃ₗ[R] CatCoh.H2 F, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup F a b
structure Frame (n : ℕ) where

  w : Fin n → Glob1 F

  δ : Fin n → ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T
  nat : ∀ (i : Fin n) ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ i T' (p1 F φ ω) = mp F φ (δ i T ω)
  sum : ∀ (T : C) (ω : Ω[F.obj T⁄R]), ω = ∑ i, δ i T ω • (w i).1 T
def HasFrame : Prop := ∃ n, Nonempty (Frame F n)
variable {n : ℕ}
def wsum (u v : Fin n → Glob1 F) : W0 F 2 := fun T ↦ ∑ k, wedge R (F.obj T) ((u k).1 T) ((v k).1 T)
def ClRel (w : Glob1 F) (u v : Fin n → Glob1 F) : Prop := ∀ T, dOne R (F.obj T) (w.1 T) = wsum F u v T
def DRel (x : CatCoh.H1 F) (y : Fin n → CatCoh.H1 F) (w : Fin n → Glob1 F) : Prop :=
  ∃ (f : Z1 F) (g : Fin n → Z1 F) (ω : A0 F), CatCoh.H1.mk F f = x ∧ (∀ k, CatCoh.H1.mk F (g k) = y k) ∧
    ∀ ⦃T T' : C⦄ (φ : T ⟶ T'),
      D R (F.obj T') (f.1 T T' φ) = ∑ k, (g k).1 T T' φ • (w k).1 T' + (ω T' - p1 F φ (ω T))
def ObRel (x : CatCoh.H1 F) (u v : Fin n → Glob1 F) : Prop :=
  ∃ (f : Z1 F) (ω : A0 F), CatCoh.H1.mk F f = x ∧
    (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω T' = p1 F φ (ω T) + D R (F.obj T') (f.1 T T' φ)) ∧
    ∀ T, dOne R (F.obj T) (ω T) = wsum F u v T
def clAll (h : Closed1 F = ⊤) : Glob1 F →ₗ[R] Hyp1 F :=
  ofForm F ∘ₗ (LinearEquiv.ofTop _ h).symm.toLinearMap
end Formal
section Pull
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
abbrev HO2 (s : X ⟶ Sp R) : Type := CatCoh.H2 (OAff s)
theorem pairRes_pull2_bijective (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : Function.Bijective (pairRes φ s').pull2 := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') (pairFst φ) H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s') (pairFst φ) H hcov hdir
  exact ⟨GlobalTheory.T.comma_descent_injective _ _ hs hg hv, GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2⟩
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)
def pullHO2 : HO2 s →ₛₗ[σ] HO2 s' :=
  (LinearEquiv.ofBijective (pairRes φ s').pull2 (pairRes_pull2_bijective φ s')).symm.toLinearMap.comp
    (pairPull h).pull2
def Red1 (f : C1 (OAff s)) (x : HO1 s') : Prop :=
  ∃ c : Z1 (OPair φ s'), (∀ p q (a : p ⟶ q), c.1 p q a = (pairPull h).α q (f _ _ ((pairPull h).G.map a))) ∧
    CatCoh.H1.mk _ c = (pairRes φ s').pull1 x
def Red2 (w : C2 (OAff s)) (z : HO2 s') : Prop :=
  ∃ c : Z2 (OPair φ s'), (∀ p q r (a : p ⟶ q) (b : q ⟶ r),
      c.1 p q r a b = (pairPull h).α r (w _ _ _ ((pairPull h).G.map a) ((pairPull h).G.map b))) ∧
    CatCoh.H2.mk _ c = (pairRes φ s').pull2 z
def TMul (t : R) (u : HO1 s') (y : HO1 s) : Prop :=
  ∃ (f : C1 (OAff s)) (c : Z1 (OAff s)), c.1 = t • f ∧ CatCoh.H1.mk _ c = y ∧ Red1 h f u
def Bock {R₀ : Type} [CommRing R₀] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {σ₀ : R →+* R₀} {φ₀ : X₀ ⟶ X}
    (h₀ : φ₀ ≫ s = s₀ ≫ spMap σ₀) (t : R) (x : HO1 s') (z : HO2 s₀) : Prop :=
  ∃ (f : C1 (OAff s)) (w : C2 (OAff s)), d1 (OAff s) f = t • w ∧ Red1 h f x ∧ Red2 h₀ w z
end Pull
def SmallExt {R R' R₀ : Type} [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) : Prop :=
  Function.Surjective σ ∧ RingHom.ker σ = Ideal.span {t} ∧ Function.Surjective σ₀ ∧ ∀ a, σ₀ a = 0 ↔ a * t = 0
section BaseChange
variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
def StructureSheafH1BaseChange : Prop := ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X)
  (h : IsPullback φ s' s (spMap (algebraMap R R'))),
    ∃ e : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s', ∀ c, e (1 ⊗ₜ c) = pullHO1 h.w c
def StructureSheafH2BaseChange : Prop := ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X)
  (h : IsPullback φ s' s (spMap (algebraMap R R'))),
    ∃ e : R' ⊗[R] HO2 s ≃ₗ[R'] HO2 s', ∀ c, e (1 ⊗ₜ c) = pullHO2 h.w c
def UConst : Prop := ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X),
  IsPullback φ s' s (spMap (algebraMap R R')) → CohomZeroIsConstants (OAff s')
abbrev dB (K : CochainComplex (ModuleCat.{0} R) ℕ) (R' : Type) [CommRing R'] [Algebra R R'] (i j : ℕ) :
    R' ⊗[R] K.X i →ₗ[R'] R' ⊗[R] K.X j := (K.d i j).hom.baseChange R'
abbrev ext {R' R'' : Type} [CommRing R'] [Algebra R R'] [CommRing R''] [Algebra R R''] (α : R' →ₐ[R] R'')
    (M : Type) [AddCommGroup M] [Module R M] : R' ⊗[R] M →ₗ[R] R'' ⊗[R] M := α.toLinearMap.rTensor M
structure Model (K : CochainComplex (ModuleCat.{0} R) ℕ) where

  θ0 : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (_ : IsPullback φ s' s (spMap (algebraMap R R'))),
    LinearMap.ker (dB K R' 0 1) ≃ₗ[R'] LinearMap.ker (d0 (OAff s'))

  one : K.X 0
  θ0_one : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap (algebraMap R R'))),
    ∃ e : (1 : R') ⊗ₜ[R] one ∈ LinearMap.ker (dB K R' 0 1), ∀ T, (θ0 h ⟨_, e⟩).1 T = 1

  θ1 : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (_ : IsPullback φ s' s (spMap (algebraMap R R'))), LinearMap.ker (dB K R' 1 2) →ₗ[R'] HO1 s'

  θ2 : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (_ : IsPullback φ s' s (spMap (algebraMap R R'))), LinearMap.ker (dB K R' 2 3) →ₗ[R'] HO2 s'
  exact : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap (algebraMap R R'))),
    Function.Surjective (θ1 h) ∧ (∀ z, θ1 h z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' 0 1)) ∧
    Function.Surjective (θ2 h) ∧ ∀ z, θ2 h z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' 1 2)
  nat : ∀ {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap (algebraMap R R')))
    {R'' : Type} [CommRing R''] [Algebra R R''] {X'' : Scheme.{0}} {s'' : X'' ⟶ Sp R''} {φ' : X'' ⟶ X}
    (h' : IsPullback φ' s'' s (spMap (algebraMap R R''))) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X')
    (w : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' →
    (∀ z z', z'.1 = ext α _ z.1 → θ1 h' z' = pullHO1 w (θ1 h z)) ∧
    ∀ z z', z'.1 = ext α _ z.1 → θ2 h' z' = pullHO2 w (θ2 h z)
def LiftsAt (K : CochainComplex (ModuleCat.{0} R) ℕ) {R' R'' : Type} [CommRing R'] [Algebra R R'] [CommRing R'']
    [Algebra R R''] (α : R' →ₐ[R] R'') (i : ℕ) : Prop :=
  ∀ z : R'' ⊗[R] K.X i, dB K R'' i (i + 1) z = 0 → ∃ (y : R' ⊗[R] K.X i) (b : R'' ⊗[R] K.X (i - 1)),
    dB K R' i (i + 1) y = 0 ∧ z = ext α _ y + dB K R'' (i - 1) i b
end BaseChange
section Over
variable {R : Type} [CommRing R] {Y A : Over (Sp R)}
theorem ovw (f : Y ⟶ A) : f.left ≫ A.hom = Y.hom ≫ spMap (RingHom.id R) := by
  rw [spMap_id, Over.w f]; exact (Category.comp_id _).symm
def pO1 (f : Y ⟶ A) : HO1 A.hom →ₗ[R] HO1 Y.hom := pullHO1 (ovw f)
def structureSheafH2Pullback (f : Y ⟶ A) : HO2 A.hom →ₗ[R] HO2 Y.hom := pullHO2 (ovw f)
def pF (f : Y ⟶ A) : GlobForm A.hom →ₗ[R] GlobForm Y.hom := pullForm (ovw f)
def deRhamH1Pullback (f : Y ⟶ A) : HH1 A.hom →ₗ[R] HH1 Y.hom := pullHH1 (ovw f)
def deRhamH2Pullback (f : Y ⟶ A) : HH2 A.hom →ₗ[R] HH2 Y.hom := pullHH2 (ovw f)
variable (A) [GrpObj A]
def StructureSheafH1Primitive : Prop := ∀ x : HO1 A.hom, pO1 μ[A] x = pO1 (fst A A) x + pO1 (snd A A) x
def PrimF : Prop := ∀ x : GlobForm A.hom, pF μ[A] x = pF (fst A A) x + pF (snd A A) x
def DeRhamH1Primitive : Prop := ∀ x : HH1 A.hom, deRhamH1Pullback μ[A] x = deRhamH1Pullback (fst A A) x + deRhamH1Pullback (snd A A) x
def NoPrimitiveStructureSheafH2 : Prop := ∀ z : HO2 A.hom, structureSheafH2Pullback μ[A] z = structureSheafH2Pullback (fst A A) z + structureSheafH2Pullback (snd A A) z → z = 0
def AxesVanishingStructureSheafDegOne : Prop := ∀ y : HO1 (A ⊗ A).hom, pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 →
  pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0
end Over
def OStr : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    FP R (HO1 A.hom) g ∧ WedgeO (OAff A.hom) ∧ StructureSheafH1BaseChange A.hom ∧ StructureSheafH2BaseChange A.hom
example (R : Type) [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (h : ∀ T, Subsingleton Ω[F.obj T⁄R]) : HasFrame F :=
  ⟨0, ⟨⟨Fin.elim0, Fin.elim0, fun i ↦ i.elim0, fun T _ ↦ (h T).elim _ _⟩⟩⟩
end GlobalTheory.AbCoh


