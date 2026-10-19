-- Prove2me | Definitions.Def_MazurTransfer_MixedOriginalAffineSectionNaturalityAndLaurentCechCoordinateData20261019
-- name    : MazurTransfer_MixedOriginalAffineSectionNaturalityAndLaurentCechCoordinateData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T07:31:37.772883+00:00
-- url     : https://prove2.me/theorems/4748f9ce-0b3e-415c-93e3-74e7b2a5d3ec
-- title:
--   Original affine sections and Laurent Cech coordinates
-- statement:
--   The original affine-open section equivalences, naturality, Laurent overlap coordinates and coefficient-quotient comparison. Both the original bare constructors and exact copied consumer contexts have their complete types and whole values checked. Named downstream consumer: actual structure-sheaf Cech cohomology and genus two.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact original affine-open section isomorphisms and algebra
equivalences with restriction naturality, Laurent quadratic overlap
coordinates, the two coefficient boundary images and their Cech quotient.
Named downstream consumer: actual mixed structure-sheaf Cech H1 and the
dyadic genus-two curve models used for Picard chart sections.
Original per-file headers and attribution are retained below.
-/
import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_MazurTransfer_Order13MixedOriginalRecoveredReciprocalAndSingleSectionPolynomialBasesData20261019
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: genuine affine coordinate sections of an open immersion
compatible with the base-field morphism. Named downstream consumer: the actual
order-thirteen chart/overlap section comparison with the official FLT cover.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace MazurTransfer.MixedOriginalDyadicAffineOpenCoordinateSections20261019
universe u
variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]
variable {X : Scheme.{u}} (c : X ⟶ Spec (.of K))
variable (f : Spec (.of A) ⟶ X) [IsOpenImmersion f]

theorem sectionsIso_inv :
    (IsOpenImmersion.ΓIsoTop f).inv = f.appLE f.opensRange ⊤ (by simp) := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, eqToIso.inv, eqToHom_op, Iso.symm_inv, Scheme.Hom.appIso_hom']
  rw [Scheme.Hom.map_appLE]

def sectionsRingIso : Γ(X, f.opensRange) ≅ CommRingCat.of A :=
  (IsOpenImmersion.ΓIsoTop f).symm ≪≫ Scheme.ΓSpecIso (.of A)

theorem sectionsRingIso_hom :
    (sectionsRingIso A f).hom = f.appLE f.opensRange ⊤ (by simp) ≫
      (Scheme.ΓSpecIso (.of A)).hom := by
  simp only [sectionsRingIso, Iso.trans_hom, Iso.symm_hom, sectionsIso_inv]

theorem sectionsRingIso_commutes
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    (Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ f.opensRange (by simp) ≫
      (sectionsRingIso A f).hom = CommRingCat.ofHom (algebraMap K A) := by
  have H : c.appLE ⊤ f.opensRange (by simp) ≫ f.appLE f.opensRange ⊤ (by simp) =
      (f ≫ c).appLE ⊤ ⊤ (by simp) :=
    Scheme.Hom.appLE_comp_appLE f c ⊤ f.opensRange ⊤ (by simp) (by simp)
  have H' : (f ≫ c).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop := by
    rw [hf]
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  calc
    _ = (Scheme.ΓSpecIso (.of K)).inv ≫ (f ≫ c).appLE ⊤ ⊤ (by simp) ≫
        (Scheme.ΓSpecIso (.of A)).hom := by
      rw [sectionsRingIso_hom]
      simpa only [Category.assoc] using congrArg
        (fun t => (Scheme.ΓSpecIso (.of K)).inv ≫ t ≫ (Scheme.ΓSpecIso (.of A)).hom) H
    _ = (Scheme.ΓSpecIso (.of K)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop ≫
        (Scheme.ΓSpecIso (.of A)).hom := congrArg
          (fun t => (Scheme.ΓSpecIso (.of K)).inv ≫ t ≫ (Scheme.ΓSpecIso (.of A)).hom) H'
    _ = _ := by rw [Scheme.ΓSpecIso_naturality]; simp

def sectionsAlgEquiv
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c f.opensRange
    Γ(X, f.opensRange) ≃ₐ[K] A := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c f.opensRange
  exact AlgEquiv.ofRingEquiv
    (f := (sectionsRingIso A f).commRingCatIsoToRingEquiv) (fun k =>
      congrArg (fun t => t.hom k) (sectionsRingIso_commutes K A c f hf))

variable {B : Type u} [CommRing B]

theorem sectionsRingIso_restriction (φ : A →+* B)
    (g : Spec (.of B) ⟶ X) [IsOpenImmersion g]
    (hg : Spec.map (CommRingCat.ofHom φ) ≫ f = g)
    (hU : g.opensRange ≤ f.opensRange) :
    X.presheaf.map (Opposite.op (homOfLE hU)) ≫ (sectionsRingIso B g).hom =
      (sectionsRingIso A f).hom ≫ CommRingCat.ofHom φ := by
  have eg : (⊤ : (Spec (.of B)).Opens) ≤ g ⁻¹ᵁ f.opensRange := by
    simpa only [Scheme.Hom.preimage_opensRange] using g.preimage_mono hU
  have Hres : X.presheaf.map (homOfLE hU).op ≫ g.appLE g.opensRange ⊤ (by simp) =
      g.appLE f.opensRange ⊤ eg := Scheme.Hom.map_appLE g (by simp) (homOfLE hU).op
  have Hcomp : f.appLE f.opensRange ⊤ (by simp) ≫
      (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (by simp) =
      g.appLE f.opensRange ⊤ eg := by
    have H := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) f
      f.opensRange ⊤ ⊤ (by simp) (by simp)
    simpa only [hg] using H
  have Htop : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom φ)).appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  calc
    _ = g.appLE f.opensRange ⊤ eg ≫ (Scheme.ΓSpecIso (.of B)).hom := by
      rw [sectionsRingIso_hom]
      exact congrArg (fun t => t ≫ (Scheme.ΓSpecIso (.of B)).hom) Hres
    _ = f.appLE f.opensRange ⊤ (by simp) ≫
        (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ (by simp) ≫
        (Scheme.ΓSpecIso (.of B)).hom := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ (Scheme.ΓSpecIso (.of B)).hom) Hcomp.symm
    _ = f.appLE f.opensRange ⊤ (by simp) ≫
        (Spec.map (CommRingCat.ofHom φ)).appTop ≫
        (Scheme.ΓSpecIso (.of B)).hom := congrArg
          (fun t => f.appLE f.opensRange ⊤ (by simp) ≫ t ≫
            (Scheme.ΓSpecIso (.of B)).hom) Htop
    _ = _ := by rw [Scheme.ΓSpecIso_naturality, sectionsRingIso_hom]; simp only [Category.assoc]

def sectionsAlgEquivAt (U : X.Opens) (hU : f.opensRange = U)
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Γ(X, U) ≃ₐ[K] A := by
  subst U
  exact sectionsAlgEquiv K A c f hf

theorem sectionsAlgEquivAt_restriction [Algebra K B] (φ : A →ₐ[K] B)
    (g : Spec (.of B) ⟶ X) [IsOpenImmersion g]
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (hg : g ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (hgf : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f = g)
    (U V : X.Opens) (hU : f.opensRange = U) (hV : g.opensRange = V) (hVU : V ≤ U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    ∀ z : Γ(X, U),
      sectionsAlgEquivAt K B c g V hV hg
        (Scheme.TwoAffineOpenCover.restrictAlgHom c hVU z) =
      φ (sectionsAlgEquivAt K A c f U hU hf z) := by
  subst U
  subst V
  intro z
  exact congrArg (fun t => t.hom z) (sectionsRingIso_restriction A f φ.toRingHom g hgf hVU)

end MazurTransfer.MixedOriginalDyadicAffineOpenCoordinateSections20261019
#print axioms MazurTransfer.MixedOriginalDyadicAffineOpenCoordinateSections20261019.sectionsAlgEquiv

#print axioms MazurTransfer.MixedOriginalDyadicAffineOpenCoordinateSections20261019.sectionsRingIso_restriction

#print axioms MazurTransfer.MixedOriginalDyadicAffineOpenCoordinateSections20261019.sectionsAlgEquivAt_restriction

end

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: compute the quotient of Laurent coefficient pairs by the
two chart images with transitions x = z^-1 and y = w z^-3.
Named downstream consumer: the actual order-thirteen two-chart Cech quotient.
This algebraic coefficient calculation alone is not a genus theorem.
-/

noncomputable section
namespace MazurTransfer.MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019

variable (K : Type*) [Field K]
abbrev LaurentCoefficients := ℤ →₀ K
abbrev ChartCoefficients := ℕ →₀ K
abbrev OverlapCoefficients := LaurentCoefficients K × LaurentCoefficients K

def ordinary : (ChartCoefficients K × ChartCoefficients K) →ₗ[K] OverlapCoefficients K :=
  (Finsupp.lmapDomain K K (fun n : ℕ => (n : ℤ))).prodMap
    (Finsupp.lmapDomain K K (fun n : ℕ => (n : ℤ)))

def reciprocal : (ChartCoefficients K × ChartCoefficients K) →ₗ[K] OverlapCoefficients K :=
  (Finsupp.lmapDomain K K (fun n : ℕ => -(n : ℤ))).prodMap
    (Finsupp.lmapDomain K K (fun n : ℕ => -(n : ℤ) - 3))

def boundaries : Submodule K (OverlapCoefficients K) := (ordinary K).range ⊔ (reciprocal K).range

def survivingCoefficients : OverlapCoefficients K →ₗ[K] K × K where
  toFun v := (v.2 (-1), v.2 (-2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem range_lmapDomain_eq_supported (e : ℕ → ℤ) :
    (Finsupp.lmapDomain K K e).range = Finsupp.supported K K (Set.range e) := by
  rw [Finsupp.range_lmapDomain, Finsupp.supported_eq_span_single]
  congr 1
  ext z
  simp

theorem ordinary_range : (ordinary K).range =
    (Finsupp.supported K K {n : ℤ | 0 ≤ n}).prod
      (Finsupp.supported K K {n : ℤ | 0 ≤ n}) := by
  rw [ordinary, LinearMap.range_prodMap, range_lmapDomain_eq_supported]
  congr 2 <;> ext z <;> simp

theorem reciprocal_range : (reciprocal K).range =
    (Finsupp.supported K K {n : ℤ | n ≤ 0}).prod
      (Finsupp.supported K K {n : ℤ | n ≤ -3}) := by
  rw [reciprocal, LinearMap.range_prodMap, range_lmapDomain_eq_supported,
    range_lmapDomain_eq_supported]
  have h₀ : Set.range (fun n : ℕ => -(n : ℤ)) = {n : ℤ | n ≤ 0} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩; simp
    · intro hz
      change z ≤ 0 at hz
      refine ⟨(-z).toNat, ?_⟩
      change -((-z).toNat : ℤ) = z
      rw [Int.toNat_of_nonneg (by omega)]
      omega
  have h₃ : Set.range (fun n : ℕ => -(n : ℤ) - 3) = {n : ℤ | n ≤ -3} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩; simp
    · intro hz
      change z ≤ -3 at hz
      refine ⟨(-z-3).toNat, ?_⟩
      change -((-z-3).toNat : ℤ) - 3 = z
      rw [Int.toNat_of_nonneg (by omega)]
      omega
  rw [h₀, h₃]

theorem boundaries_eq_kernel : boundaries K = (survivingCoefficients K).ker := by
  rw [boundaries, ordinary_range, reciprocal_range]
  apply le_antisymm
  · apply sup_le
    · intro v hv
      rw [LinearMap.mem_ker]
      have hy := hv.2
      have h₁ := (Finsupp.mem_supported' K v.2).mp hy (-1) (by simp)
      have h₂ := (Finsupp.mem_supported' K v.2).mp hy (-2) (by simp)
      exact Prod.ext h₁ h₂
    · intro v hv
      rw [LinearMap.mem_ker]
      have hy := hv.2
      have h₁ := (Finsupp.mem_supported' K v.2).mp hy (-1) (by simp)
      have h₂ := (Finsupp.mem_supported' K v.2).mp hy (-2) (by simp)
      exact Prod.ext h₁ h₂
  · intro v hv
    have hzero : v.2 (-1) = 0 ∧ v.2 (-2) = 0 := by
      change (v.2 (-1), v.2 (-2)) = (0, 0) at hv
      exact Prod.mk.inj hv
    let positive (a : ℤ →₀ K) := a.filter (fun n => 0 ≤ n)
    let negative (a : ℤ →₀ K) := a.filter (fun n => n < 0)
    refine Submodule.mem_sup.mpr ⟨(positive v.1, positive v.2), ?_,
      (negative v.1, negative v.2), ?_, ?_⟩
    · constructor <;> apply (Finsupp.mem_supported' K _).mpr <;>
        intro n hn <;> change ¬ 0 ≤ n at hn <;> simp [positive, hn]
    · constructor
      · apply (Finsupp.mem_supported' K _).mpr
        intro n hn
        simp only [Set.mem_ofPred_eq, not_le] at hn
        simp [negative, show ¬ n < 0 by omega]
      · apply (Finsupp.mem_supported' K _).mpr
        intro n hn
        simp only [Set.mem_ofPred_eq, not_le] at hn
        by_cases hp : 0 ≤ n
        · simp [negative, show ¬ n < 0 by omega]
        · have hn' : n = -1 ∨ n = -2 := by omega
          rcases hn' with rfl | rfl <;> simp [negative, hzero.1, hzero.2]
    · apply Prod.ext <;> ext n <;> by_cases hn : 0 ≤ n <;>
        simp [positive, negative, hn, show n < 0 ↔ ¬ 0 ≤ n by omega]

theorem survivingCoefficients_surjective : Function.Surjective (survivingCoefficients K) := by
  rintro ⟨a, b⟩
  let v : ℤ →₀ K := Finsupp.single (-1) a + Finsupp.single (-2) b
  refine ⟨(0, v), ?_⟩
  change (v (-1), v (-2)) = (a, b)
  simp [v]

def quotientEquiv : (OverlapCoefficients K ⧸ boundaries K) ≃ₗ[K] K × K :=
  (Submodule.quotEquivOfEq _ _ (boundaries_eq_kernel K)).trans
    ((survivingCoefficients K).quotKerEquivOfSurjective (survivingCoefficients_surjective K))

theorem quotient_finrank : Module.finrank K (OverlapCoefficients K ⧸ boundaries K) = 2 := by
  rw [(quotientEquiv K).finrank_eq]
  simp

end MazurTransfer.MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019

#print axioms MazurTransfer.MixedOriginalDyadicLaurentTwoChartCoefficientQuotient20261019.quotient_finrank

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: affine chart section equivalences at an equal open, with
transport confined to the ring isomorphism and explicit restriction naturality.
Named downstream consumer: mixed order-13 ordinary and overlap sections.
Reuses the owned MixedOriginalDyadicAffineOpenCoordinateSections20261019 ring-level naturality proof.
-/

noncomputable section
universe u
namespace MazurTransfer.MixedOriginalDyadicAffineOpenCoordinateSectionsAt20261019
open CategoryTheory AlgebraicGeometry Opposite
open MazurTransfer.MixedOriginalDyadicAffineOpenCoordinateSections20261019
variable {X : Scheme.{u}} (A : Type u) [CommRing A]
  (f : Spec (.of A) ⟶ X) [IsOpenImmersion f]

def sectionsRingIsoAt (U : X.Opens) (hU : f.opensRange = U) :
    Γ(X,U) ≅ CommRingCat.of A :=
  Classical.choose (show ∃ e : Γ(X,U) ≅ CommRingCat.of A,
    e = hU ▸ sectionsRingIso A f from ⟨hU ▸ sectionsRingIso A f, rfl⟩)

theorem sectionsRingIsoAt_eq (U : X.Opens) (hU : f.opensRange = U) :
    sectionsRingIsoAt A f U hU = hU ▸ sectionsRingIso A f :=
  Classical.choose_spec (show ∃ e : Γ(X,U) ≅ CommRingCat.of A,
    e = hU ▸ sectionsRingIso A f from ⟨hU ▸ sectionsRingIso A f, rfl⟩)

variable {B : Type u} [CommRing B]

theorem sectionsRingIsoAt_restriction (φ : A →+* B)
    (g : Spec (.of B) ⟶ X) [IsOpenImmersion g]
    (hg : Spec.map (CommRingCat.ofHom φ) ≫ f = g)
    (U V : X.Opens) (hU : f.opensRange = U) (hV : g.opensRange = V) (hVU : V ≤ U) :
    X.presheaf.map (homOfLE hVU).op ≫ (sectionsRingIsoAt B g V hV).hom =
      (sectionsRingIsoAt A f U hU).hom ≫ CommRingCat.ofHom φ := by
  subst U
  subst V
  rw [sectionsRingIsoAt_eq, sectionsRingIsoAt_eq]
  exact sectionsRingIso_restriction A f φ g hg hVU

variable (K : Type u) [CommRing K] [Algebra K A]
  (c : X ⟶ Spec (.of K))

def sectionsAlgEquivAt (U : X.Opens) (hU : f.opensRange = U)
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Γ(X,U) ≃ₐ[K] A := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  refine { (sectionsRingIsoAt A f U hU).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro r
  subst U
  rw [sectionsRingIsoAt_eq]
  change (sectionsRingIso A f).hom.hom
    ((Scheme.TwoAffineOpenCover.algebraOfHom c f.opensRange).algebraMap r) = _
  exact congrArg (fun t : CommRingCat.of K ⟶ CommRingCat.of A => t.hom r)
    (sectionsRingIso_commutes K A c f hf)

theorem sectionsAlgEquivAt_apply (U : X.Opens) (hU : f.opensRange = U)
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (z : Γ(X,U)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    sectionsAlgEquivAt A f K c U hU hf z = (sectionsRingIsoAt A f U hU).hom.hom z := rfl

theorem sectionsAlgEquivAt_restriction [Algebra K B] (φ : A →ₐ[K] B)
    (g : Spec (.of B) ⟶ X) [IsOpenImmersion g]
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (hg : g ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (hgf : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f = g)
    (U V : X.Opens) (hU : f.opensRange = U) (hV : g.opensRange = V) (hVU : V ≤ U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    ∀ z : Γ(X,U),
      sectionsAlgEquivAt B g K c V hV hg
        (Scheme.TwoAffineOpenCover.restrictAlgHom c hVU z) =
      φ (sectionsAlgEquivAt A f K c U hU hf z) := by
  intro z
  change (sectionsRingIsoAt B g V hV).hom.hom
    ((X.presheaf.map (homOfLE hVU).op).hom z) =
      φ ((sectionsRingIsoAt A f U hU).hom.hom z)
  exact congrArg (fun t => t.hom z)
    (sectionsRingIsoAt_restriction A f φ.toRingHom g hgf U V hU hV hVU)

end MazurTransfer.MixedOriginalDyadicAffineOpenCoordinateSectionsAt20261019
#print axioms MazurTransfer.MixedOriginalDyadicAffineOpenCoordinateSectionsAt20261019.sectionsAlgEquivAt_restriction

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: localizing a mixed monic quadratic chart at its coordinate
is its actual Laurent coefficient algebra, over every commutative ring.
Named downstream consumer: the mixed order-13 two-chart Cech quotient.
Adapted from the checked owned HyperellipticLaurentOverlap construction.
-/

noncomputable section
namespace MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019
open Polynomial

variable (K : Type*) [CommRing K] (h f : Polynomial K)

instance : IsScalarTower K (Polynomial K) (LaurentPolynomial K) :=
  IsScalarTower.of_algebraMap_eq fun k => by
    rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.algebraMap_eq,
      Polynomial.toLaurent_C]
    exact (LaurentPolynomial.C_eq_algebraMap k).symm

def equation : Polynomial (Polynomial K) := X ^ 2 + C h * X - C f
abbrev Chart := AdjoinRoot (equation K h f)
def x : Chart K h f := AdjoinRoot.of (equation K h f) X
def y : Chart K h f := AdjoinRoot.root (equation K h f)
abbrev Overlap := Localization.Away (x K h f)
abbrev laurentEquation : Polynomial (LaurentPolynomial K) := X ^ 2 + C h.toLaurent * X - C f.toLaurent
abbrev LaurentChart := AdjoinRoot (laurentEquation K h f)

def toLaurentBase : Chart K h f →ₐ[K] LaurentChart K h f :=
  AdjoinRoot.liftAlgHom (equation K h f)
    ((AdjoinRoot.ofAlgHom K (laurentEquation K h f)).comp Polynomial.toLaurentAlg)
    (AdjoinRoot.root (laurentEquation K h f)) (by
      have heq := AdjoinRoot.eval₂_root (laurentEquation K h f)
      change Polynomial.eval₂ _ _ (X ^ 2 + C h.toLaurent * X - C f.toLaurent) = 0 at heq
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at heq
      change Polynomial.eval₂ _ _ (X ^ 2 + C h * X - C f) = 0
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      exact heq)

@[simp] theorem toLaurentBase_x :
    toLaurentBase K h f (x K h f) =
      AdjoinRoot.of (laurentEquation K h f) (LaurentPolynomial.T 1) := by
  simp [toLaurentBase, x]

@[simp] theorem toLaurentBase_y :
    toLaurentBase K h f (y K h f) = AdjoinRoot.root (laurentEquation K h f) := by
  simp [toLaurentBase, y]

def toLaurent : Overlap K h f →ₐ[K] LaurentChart K h f :=
  IsLocalization.Away.liftAlgHom (x K h f) (by
    rw [toLaurentBase_x]
    exact (LaurentPolynomial.isUnit_T (1 : ℤ)).map (AdjoinRoot.of (laurentEquation K h f)))

@[simp] theorem toLaurent_algebraMap (a : Chart K h f) :
    toLaurent K h f (algebraMap (Chart K h f) (Overlap K h f) a) = toLaurentBase K h f a := by
  simp [toLaurent, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

theorem coefficient_X_unit : IsUnit
    (((Algebra.algHom K (Chart K h f) (Overlap K h f)).comp
      (AdjoinRoot.ofAlgHom K (equation K h f))) X) := by
  change IsUnit (algebraMap (Chart K h f) (Overlap K h f) (x K h f))
  exact IsLocalization.Away.algebraMap_isUnit (x K h f)

def fromLaurentCoefficients : LaurentPolynomial K →ₐ[K] Overlap K h f :=
  IsLocalization.Away.liftAlgHom (X : Polynomial K)
    (f := (Algebra.algHom K (Chart K h f) (Overlap K h f)).comp
      (AdjoinRoot.ofAlgHom K (equation K h f))) (coefficient_X_unit K h f)

@[simp] theorem fromLaurentCoefficients_toLaurent (p : Polynomial K) :
    fromLaurentCoefficients K h f p.toLaurent =
      algebraMap (Chart K h f) (Overlap K h f) (AdjoinRoot.of (equation K h f) p) := by
  change fromLaurentCoefficients K h f
    (algebraMap (Polynomial K) (LaurentPolynomial K) p) = _
  exact IsLocalization.Away.lift_eq (X : Polynomial K) (coefficient_X_unit K h f) p

def fromLaurent : LaurentChart K h f →ₐ[K] Overlap K h f :=
  AdjoinRoot.liftAlgHom (laurentEquation K h f) (fromLaurentCoefficients K h f)
    (algebraMap (Chart K h f) (Overlap K h f) (y K h f)) (by
      have heq := AdjoinRoot.eval₂_root (equation K h f)
      change Polynomial.eval₂ _ _ (X ^ 2 + C h * X - C f) = 0 at heq
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at heq
      have hm := congrArg (algebraMap (Chart K h f) (Overlap K h f)) heq
      change Polynomial.eval₂ _ _ (X ^ 2 + C h.toLaurent * X - C f.toLaurent) = 0
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      change (algebraMap (Chart K h f) (Overlap K h f) (y K h f)) ^ 2 +
        fromLaurentCoefficients K h f h.toLaurent *
          algebraMap (Chart K h f) (Overlap K h f) (y K h f) -
        fromLaurentCoefficients K h f f.toLaurent = 0
      rw [fromLaurentCoefficients_toLaurent, fromLaurentCoefficients_toLaurent]
      simpa only [map_sub, map_add, map_mul, map_pow, map_zero, y] using hm)

@[simp] theorem fromLaurent_root :
    fromLaurent K h f (AdjoinRoot.root (laurentEquation K h f)) =
      algebraMap (Chart K h f) (Overlap K h f) (y K h f) := by
  simp [fromLaurent]

theorem fromLaurent_comp_toLaurent :
    (fromLaurent K h f).comp (toLaurent K h f) = AlgHom.id K (Overlap K h f) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (x K h f))
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change fromLaurent K h f (toLaurent K h f
      (algebraMap (Chart K h f) (Overlap K h f) (x K h f))) =
      algebraMap (Chart K h f) (Overlap K h f) (x K h f)
    rw [toLaurent_algebraMap, toLaurentBase_x]
    rw [← Polynomial.toLaurent_X]
    change AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.of _ _) = _
    rw [AdjoinRoot.liftAlgHom_of, fromLaurentCoefficients_toLaurent]
    rfl
  · change fromLaurent K h f (toLaurent K h f
      (algebraMap (Chart K h f) (Overlap K h f) (y K h f))) =
      algebraMap (Chart K h f) (Overlap K h f) (y K h f)
    simp

theorem toLaurent_comp_fromLaurent :
    (toLaurent K h f).comp (fromLaurent K h f) = AlgHom.id K (LaurentChart K h f) := by
  apply AdjoinRoot.algHom_ext'
  · apply IsLocalization.algHom_ext (Submonoid.powers (X : Polynomial K))
    apply Polynomial.algHom_ext
    change toLaurent K h f (fromLaurent K h f (AdjoinRoot.of (laurentEquation K h f)
      (Polynomial.toLaurent X))) = AdjoinRoot.of (laurentEquation K h f) (Polynomial.toLaurent X)
    change toLaurent K h f (AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.of _ _)) = _
    rw [AdjoinRoot.liftAlgHom_of, fromLaurentCoefficients_toLaurent,
      toLaurent_algebraMap]
    simpa only [x, Polynomial.toLaurent_X] using toLaurentBase_x K h f
  · simp

def overlapAlgEquiv : Overlap K h f ≃ₐ[K] LaurentChart K h f :=
  AlgEquiv.ofAlgHom (toLaurent K h f) (fromLaurent K h f)
    (toLaurent_comp_fromLaurent K h f) (fromLaurent_comp_toLaurent K h f)

end MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019
#print axioms MazurTransfer.MixedOriginalDyadicMixedQuadraticLaurentOverlap20261019.overlapAlgEquiv

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: coordinate linear equivalences compatible with the two
restriction maps identify the actual structure-sheaf Cech cokernel.
Named downstream consumer: the mixed order-13 structure-sheaf H1 calculation.
-/

noncomputable section
namespace MazurTransfer.MixedOriginalDyadicTwoChartCechCoordinateComparison20261019
universe u v w
variable {R : Type u} [CommRing R] (𝒰 : TwoChartCech.Cover.{u,v} R)
variable {N0 N1 N01 : Type w} [AddCommGroup N0] [AddCommGroup N1] [AddCommGroup N01]
  [Module R N0] [Module R N1] [Module R N01]
variable (e0 : 𝒰.A0 ≃ₗ[R] N0) (e1 : 𝒰.A1 ≃ₗ[R] N1) (e01 : 𝒰.A01 ≃ₗ[R] N01)
  (f0 : N0 →ₗ[R] N01) (f1 : N1 →ₗ[R] N01)
  (h0 : ∀ z, e01 (𝒰.ρ0 z) = f0 (e0 z))
  (h1 : ∀ z, e01 (𝒰.ρ1 z) = f1 (e1 z))

include h0 h1

theorem diff_natural (z : 𝒰.A0 × 𝒰.A1) :
    e01 (𝒰.structureSheaf.cechDiff z) =
      ((-f0).coprod f1) ((e0.prodCongr e1) z) := by
  rw [TwoChartCech.Sections.cechDiff_apply]
  change e01 ((1 : 𝒰.A01) * 𝒰.ρ1 z.2 - 𝒰.ρ0 z.1) = _
  rw [one_mul, map_sub, h1, h0]
  change f1 (e1 z.2) - f0 (e0 z.1) = -f0 (e0 z.1) + f1 (e1 z.2)
  exact sub_eq_neg_add _ _

theorem range_natural :
    Submodule.map e01.toLinearMap 𝒰.structureSheaf.cechDiff.range =
      ((-f0).coprod f1).range := by
  ext y
  constructor
  · rintro ⟨_,⟨z,rfl⟩,rfl⟩
    exact ⟨(e0.prodCongr e1) z, (diff_natural 𝒰 e0 e1 e01 f0 f1 h0 h1 z).symm⟩
  · rintro ⟨z,rfl⟩
    let w := (e0.prodCongr e1).symm z
    refine ⟨𝒰.structureSheaf.cechDiff w, ⟨w,rfl⟩, ?_⟩
    change e01 (𝒰.structureSheaf.cechDiff w) = _
    rw [diff_natural 𝒰 e0 e1 e01 f0 f1 h0 h1, LinearEquiv.apply_symm_apply]

def quotientEquiv (B : Submodule R N01) (hB : ((-f0).coprod f1).range = B) :
    𝒰.structureSheaf.H1 ≃ₗ[R] (N01 ⧸ B) :=
  Submodule.Quotient.equiv _ _ e01 ((range_natural 𝒰 e0 e1 e01 f0 f1 h0 h1).trans hB)

end MazurTransfer.MixedOriginalDyadicTwoChartCechCoordinateComparison20261019
#print axioms MazurTransfer.MixedOriginalDyadicTwoChartCechCoordinateComparison20261019.quotientEquiv

end


