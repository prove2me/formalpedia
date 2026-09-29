-- Prove2me | solution 1 for AutomorphicForm.exists_isArithBoundedGenuineCuspRealizable_eq_comap_galRestrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2538a839-71c9-5382-b51e-31bd3f661957

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_DedekindDomain_FiniteAdeleRing_BaseChange
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Theorems.Thm_AutomorphicForm_isArithBoundedGenuineCuspRealizable_of_isArithBoundedGenuineCuspRealizable_of_pos_of_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_isArithBoundedGenuineCuspRealizable_eq_comap_galRestrict

noncomputable section

open NumberField IsDedekindDomain NumberField.AdelicLevel NumberField.AdelicVolume
open AutomorphicForm AutomorphicForm.WindowedSiegel

namespace GaloisConjugationTransport

section Coordinates

variable {K₁ K₂ : Type*} [NormedField K₁] [NormedField K₂]

private theorem coe_glMap (f : K₁ →+* K₂) (g : GL (Fin 2) K₁) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) K₂) : Matrix (Fin 2) (Fin 2) K₂) =
      f.mapMatrix (g : Matrix (Fin 2) (Fin 2) K₁) :=
  rfl

private theorem rowNormSq_mapMatrix (f : K₁ →+* K₂) (hf : ∀ x, ‖f x‖ = ‖x‖) (M : Matrix (Fin 2) (Fin 2) K₁) :
    rowNormSq (f.mapMatrix M) = rowNormSq M := by
  simp only [rowNormSq, RingHom.mapMatrix_apply, Matrix.map_apply, hf]

private theorem topNormSq_mapMatrix (f : K₁ →+* K₂) (hf : ∀ x, ‖f x‖ = ‖x‖) (M : Matrix (Fin 2) (Fin 2) K₁) :
    topNormSq (f.mapMatrix M) = topNormSq M := by
  simp only [topNormSq, RingHom.mapMatrix_apply, Matrix.map_apply, hf]

private theorem localHeight_glMap (f : K₁ →+* K₂) (hf : ∀ x, ‖f x‖ = ‖x‖) (g : GL (Fin 2) K₁) :
    localHeight (Matrix.GeneralLinearGroup.map f g) = localHeight g := by
  rw [localHeight, localHeight, coe_glMap, ← RingHom.map_det, hf, rowNormSq_mapMatrix f hf]

private theorem xWindowSq_glMap (f : K₁ →+* K₂) (hf : ∀ x, ‖f x‖ = ‖x‖) (g : GL (Fin 2) K₁) :
    xWindowSq (Matrix.GeneralLinearGroup.map f g) = xWindowSq g := by
  rw [xWindowSq, xWindowSq, coe_glMap, topNormSq_mapMatrix f hf, rowNormSq_mapMatrix f hf, localHeight_glMap f hf]

end Coordinates

section Generic

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private scoped instance liesOver_comap (w : InfinitePlace L) : w.1.LiesOver (w.comap (algebraMap K L)).1 where
  comp_eq := rfl

open scoped NumberField.LiesOver in
private def iota (w : InfinitePlace L) : (w.comap (algebraMap K L)).Completion →+* w.Completion :=
  algebraMap (w.comap (algebraMap K L)).Completion w.Completion

private theorem isometry_iota (w : InfinitePlace L) : Isometry (iota (K := K) w) :=
  (NumberField.InfinitePlace.Completion.isometryEquivCompletion w).symm.isometry.comp
    ((NumberField.InfinitePlace.LiesOver.isometry_algebraMap w (w.comap (algebraMap K L))).isometry_mapRingHom.comp
      (NumberField.InfinitePlace.Completion.isometry_toCompletion _))

private theorem norm_iota (w : InfinitePlace L) (x : (w.comap (algebraMap K L)).Completion) :
    ‖iota w x‖ = ‖x‖ :=
  (isometry_iota (K := K) w).norm_map_of_map_zero (map_zero _) x

private def infiniteMap : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  RingHom.pi fun w : InfinitePlace L =>
    (iota w).comp (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) (w.comap (algebraMap K L)))

private theorem continuous_infiniteMap : Continuous (infiniteMap (K := K) (L := L)) :=
  continuous_pi fun w : InfinitePlace L =>
    ((isometry_iota (K := K) w).continuous).comp (continuous_apply (w.comap (algebraMap K L)))

private def infGL2 : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) (InfiniteAdeleRing L) :=
  Matrix.GeneralLinearGroup.map (infiniteMap (K := K) (L := L))

private theorem archComponent_infGL2 (w : InfinitePlace L) (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    archComponent L w (infGL2 g) =
      Matrix.GeneralLinearGroup.map (iota w) (archComponent K (w.comap (algebraMap K L)) g) :=
  rfl

private theorem norm_det_archComponent_infGL2 (w : InfinitePlace L) (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    ‖((archComponent L w (infGL2 g) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖ =
      ‖((archComponent K (w.comap (algebraMap K L)) g : GL (Fin 2) (w.comap (algebraMap K L)).Completion) :
          Matrix (Fin 2) (Fin 2) (w.comap (algebraMap K L)).Completion).det‖ := by
  rw [archComponent_infGL2, ← norm_iota (K := K) w, RingHom.map_det]
  rfl

private theorem localHeight_archComponent_infGL2 (w : InfinitePlace L) (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    localHeight (archComponent L w (infGL2 g)) = localHeight (archComponent K (w.comap (algebraMap K L)) g) := by
  rw [archComponent_infGL2]
  exact localHeight_glMap (iota w) (norm_iota (K := K) w) _

private theorem xWindowSq_archComponent_infGL2 (w : InfinitePlace L) (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    xWindowSq (archComponent L w (infGL2 g)) = xWindowSq (archComponent K (w.comap (algebraMap K L)) g) := by
  rw [archComponent_infGL2]
  exact xWindowSq_glMap (iota w) (norm_iota (K := K) w) _

end Generic

variable {E : Type} [Field E] [NumberField E]

private def Tw (_σ : E ≃ₐ[ℚ] E) : Type := E

variable (σ : E ≃ₐ[ℚ] E)

private scoped instance instFieldTw : Field (Tw σ) := inferInstanceAs (Field E)
private scoped instance instNumberFieldTw : NumberField (Tw σ) := inferInstanceAs (NumberField E)
private scoped instance instAlgebraTw : Algebra E (Tw σ) :=
  RingHom.toAlgebra (show E →+* Tw σ from σ.toRingEquiv.toRingHom)

private def conjPlace (w : InfinitePlace E) : InfinitePlace E :=
  (show InfinitePlace (Tw σ) from w).comap (algebraMap E (Tw σ))

private def sigmaInfinite : InfiniteAdeleRing E →+* InfiniteAdeleRing E :=
  (infiniteMap (K := E) (L := Tw σ) : InfiniteAdeleRing E →+* InfiniteAdeleRing (Tw σ))

private theorem continuous_sigmaInfinite : Continuous (sigmaInfinite σ) :=
  continuous_infiniteMap (K := E) (L := Tw σ)

private def sigmaFinAdele :
    ContinuousSemialgHom σ.toRingEquiv.toRingHom (FiniteAdeleRing (𝓞 E) E) (FiniteAdeleRing (𝓞 E) E) :=
  IsDedekindDomain.FiniteAdeleRing.mapSemialgHom (𝓞 E) E (Tw σ) (𝓞 (Tw σ))

private def sigmaFin : FiniteAdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E :=
  (sigmaFinAdele σ).toRingHom

private def sigmaAdele : AdeleRing (𝓞 E) E →+* AdeleRing (𝓞 E) E :=
  RingHom.prodMap (sigmaInfinite σ) (sigmaFin σ)

private theorem continuous_sigmaAdele : Continuous (sigmaAdele σ) :=
  (continuous_sigmaInfinite σ).prodMap (sigmaFinAdele σ).continuous_toFun

private def sigmaGL2 : AdelicGL2 (𝓞 E) E →* AdelicGL2 (𝓞 E) E :=
  Matrix.GeneralLinearGroup.map (sigmaAdele σ)

private def sigmaFinGL2 : GL (Fin 2) (FiniteAdeleRing (𝓞 E) E) →* GL (Fin 2) (FiniteAdeleRing (𝓞 E) E) :=
  Matrix.GeneralLinearGroup.map (sigmaFin σ)

private theorem sigmaFin_mem_integral {x : FiniteAdeleRing (𝓞 E) E} (hx : x ∈ integralFiniteAdeles (𝓞 E) E) :
    sigmaFin σ x ∈ integralFiniteAdeles (𝓞 E) E := by
  intro w
  show IsDedekindDomain.FiniteAdeleRing.mapSemialgHom (𝓞 E) E (Tw σ) (𝓞 (Tw σ)) x
      (show HeightOneSpectrum (𝓞 (Tw σ)) from w) ∈
    (show HeightOneSpectrum (𝓞 (Tw σ)) from w).adicCompletionIntegers (Tw σ)
  rw [IsDedekindDomain.FiniteAdeleRing.mapSemialgHom_apply]
  exact IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_image_adicCompletionIntegers E (Tw σ)
    ⟨show HeightOneSpectrum (𝓞 (Tw σ)) from w, rfl⟩ ⟨_, hx _, rfl⟩

private theorem sigmaFinGL2_mem_finiteIntegralGL2 {g : GL (Fin 2) (FiniteAdeleRing (𝓞 E) E)}
    (hg : g ∈ finiteIntegralGL2 (𝓞 E) E) : sigmaFinGL2 σ g ∈ finiteIntegralGL2 (𝓞 E) E := by
  rw [mem_finiteIntegralGL2_iff] at hg ⊢
  obtain ⟨h₁, h₂⟩ := hg
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · exact sigmaFin_mem_integral σ (h₁ i j)
  · rw [← map_inv]
    exact sigmaFin_mem_integral σ (h₂ i j)

private theorem glFin_sigmaGL2 (g : AdelicGL2 (𝓞 E) E) :
    glFin (𝓞 E) E (sigmaGL2 σ g) = sigmaFinGL2 σ (glFin (𝓞 E) E g) :=
  Units.ext (Matrix.ext fun _ _ => rfl)

private theorem glFin_sigmaGL2_mem (g : AdelicGL2 (𝓞 E) E) (hg : glFin (𝓞 E) E g ∈ finiteIntegralGL2 (𝓞 E) E) :
    glFin (𝓞 E) E (sigmaGL2 σ g) ∈ finiteIntegralGL2 (𝓞 E) E := by
  rw [glFin_sigmaGL2]
  exact sigmaFinGL2_mem_finiteIntegralGL2 σ hg

private theorem localHeight_sigmaGL2 (w : InfinitePlace E) (g : AdelicGL2 (𝓞 E) E) :
    localHeight (archComponent E w (glArch (𝓞 E) E (sigmaGL2 σ g))) =
      localHeight (archComponent E (conjPlace σ w) (glArch (𝓞 E) E g)) :=
  localHeight_archComponent_infGL2 (K := E) (L := Tw σ) (show InfinitePlace (Tw σ) from w) (glArch (𝓞 E) E g)

private theorem xWindowSq_sigmaGL2 (w : InfinitePlace E) (g : AdelicGL2 (𝓞 E) E) :
    xWindowSq (archComponent E w (glArch (𝓞 E) E (sigmaGL2 σ g))) =
      xWindowSq (archComponent E (conjPlace σ w) (glArch (𝓞 E) E g)) :=
  xWindowSq_archComponent_infGL2 (K := E) (L := Tw σ) (show InfinitePlace (Tw σ) from w) (glArch (𝓞 E) E g)

private theorem archDetNorm_sigmaGL2 (w : InfinitePlace E) (g : AdelicGL2 (𝓞 E) E) :
    archDetNorm w (sigmaGL2 σ g) = archDetNorm (conjPlace σ w) g :=
  norm_det_archComponent_infGL2 (K := E) (L := Tw σ) (show InfinitePlace (Tw σ) from w) (glArch (𝓞 E) E g)

private theorem sigmaGL2_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} {g : AdelicGL2 (𝓞 E) E}
    (hg : g ∈ centreCutSiegelSet E c u d₁ d₂) : sigmaGL2 σ g ∈ centreCutSiegelSet E c u d₁ d₂ := by
  rw [mem_centreCutSiegelSet_iff] at hg ⊢
  obtain ⟨h₀, h₁, h₂, h₃⟩ := hg
  refine ⟨glFin_sigmaGL2_mem σ g h₀, fun w => ?_, fun w => ?_, fun w => ?_⟩
  · rw [localHeight_sigmaGL2]
    exact h₁ _
  · rw [xWindowSq_sigmaGL2]
    exact h₂ _
  · rw [archDetNorm_sigmaGL2]
    exact h₃ _

private theorem image_centreCutSiegelSet_subset (c u d₁ d₂ : ℝ) :
    sigmaGL2 σ '' centreCutSiegelSet E c u d₁ d₂ ⊆ centreCutSiegelSet E c u d₁ d₂ := by
  rintro _ ⟨g, hg, rfl⟩
  exact sigmaGL2_mem_centreCutSiegelSet σ hg

open scoped Classical in

private theorem sigmaGL2_mem_window {c u d₁ d₂ : ℝ} (T : Finset (AdelicGL2 (𝓞 E) E)) {g : AdelicGL2 (𝓞 E) E}
    (hg : g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet E c u d₁ d₂) :
    sigmaGL2 σ g ∈ ⋃ x ∈ T.image (sigmaGL2 σ), (· * x) '' centreCutSiegelSet E c u d₁ d₂ := by
  obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_iUnion₂.mp hg
  exact Set.mem_iUnion₂.mpr
    ⟨sigmaGL2 σ x, Finset.mem_image_of_mem _ hx, sigmaGL2 σ s, sigmaGL2_mem_centreCutSiegelSet σ hs,
      (map_mul (sigmaGL2 σ) s x).symm⟩

private def intEquiv : 𝓞 E ≃+* 𝓞 E := (galRestrict ℤ ℚ E (𝓞 E) σ).toRingEquiv

private def placeEquiv : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E) :=
  HeightOneSpectrum.equivOfRingEquiv (intEquiv σ)

private theorem placeEquiv_symm_of_comap {v w : HeightOneSpectrum (𝓞 E)}
    (h : w.asIdeal = v.asIdeal.comap (galRestrict ℤ ℚ E (𝓞 E) σ)) : (placeEquiv σ).symm v = w := by
  ext x
  rw [h]
  exact Iff.rfl

private def conjTable (Φ : HeckeEigensystem E ℂ) : HeckeEigensystem E ℂ where
  level := Φ.level.comap (intEquiv σ : 𝓞 E →+* 𝓞 E)
  level_ne_bot := fun h => Φ.level_ne_bot (Ideal.eq_bot_of_comap_eq_bot' (intEquiv σ).surjective h)
  a := fun w => Φ.a (placeEquiv σ w)
  b := fun w => Φ.b (placeEquiv σ w)

private theorem conjTable_eq_of_comap (Φ : HeckeEigensystem E ℂ) :
    ∀ v w : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
      w.asIdeal = v.asIdeal.comap (galRestrict ℤ ℚ E (𝓞 E) σ) →
        (conjTable σ Φ).a w = Φ.a v ∧ (conjTable σ Φ).b w = Φ.b v := by
  intro v w h
  rw [← placeEquiv_symm_of_comap σ h]
  exact ⟨congrArg Φ.a ((placeEquiv σ).apply_symm_apply v), congrArg Φ.b ((placeEquiv σ).apply_symm_apply v)⟩

private theorem absNorm_comap_ringEquiv (e : 𝓞 E ≃+* 𝓞 E) (I : Ideal (𝓞 E)) :
    Ideal.absNorm (I.comap (e : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv (I.comap (e : 𝓞 E →+* 𝓞 E)) I e
      (Ideal.map_comap_of_surjective (e : 𝓞 E →+* 𝓞 E) e.surjective I).symm).toEquiv

private theorem cNorm_placeEquiv (w : HeightOneSpectrum (𝓞 E)) :
    HeckeEigensystem.cNorm (placeEquiv σ w) = HeckeEigensystem.cNorm w := by
  show ((Ideal.absNorm (w.asIdeal.comap ((intEquiv σ).symm : 𝓞 E →+* 𝓞 E)) : ℕ) : ℂ) =
    ((Ideal.absNorm w.asIdeal : ℕ) : ℂ)
  rw [absNorm_comap_ringEquiv]

private theorem conjTable_toRawCentral (Φ : HeckeEigensystem E ℂ) :
    conjTable σ Φ.toRawCentral = (conjTable σ Φ).toRawCentral := by
  simp only [conjTable, HeckeEigensystem.toRawCentral, cNorm_placeEquiv]

section Inverse

private theorem local_fin_agree (v z : HeightOneSpectrum (𝓞 E))
    (h₁ : (show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E) = v)
    (h₂ : (show HeightOneSpectrum (𝓞 (Tw σ.symm)) from v).under (𝓞 E) = z) (a : WithVal (v.valuation E)) :
    IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E (Tw σ.symm)
        (⟨show HeightOneSpectrum (𝓞 (Tw σ.symm)) from v, h₂⟩ :
          IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 (Tw σ.symm)) z)
        (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E (Tw σ)
          (⟨show HeightOneSpectrum (𝓞 (Tw σ)) from z, h₁⟩ : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 (Tw σ)) v)
          a) =
      (a : v.adicCompletion E) := by
  erw [IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe]
  erw [IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe]
  apply congrArg (fun t : WithVal (v.valuation E) => (t : v.adicCompletion E))
  exact congrArg (WithVal.equiv (v.valuation E)).symm (σ.symm_apply_apply a.ofVal)

private theorem local_fin_inv (x : FiniteAdeleRing (𝓞 E) E) (v w z : HeightOneSpectrum (𝓞 E))
    (h₁ : (show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E) = v)
    (h₂ : (show HeightOneSpectrum (𝓞 (Tw σ.symm)) from w).under (𝓞 E) = z) (hv : v = w) :
    IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E (Tw σ.symm)
        (⟨show HeightOneSpectrum (𝓞 (Tw σ.symm)) from w, h₂⟩ :
          IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 (Tw σ.symm)) z)
        (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E (Tw σ)
          (⟨show HeightOneSpectrum (𝓞 (Tw σ)) from z, h₁⟩ : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 (Tw σ)) v)
          (x v)) =
      x w := by
  subst hv
  have hc : Continuous (⇑(IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E (Tw σ.symm)
        (⟨show HeightOneSpectrum (𝓞 (Tw σ.symm)) from v, h₂⟩ :
          IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 (Tw σ.symm)) z)) ∘
      ⇑(IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E (Tw σ)
          (⟨show HeightOneSpectrum (𝓞 (Tw σ)) from z, h₁⟩ : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 (Tw σ)) v))) :=
    (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous E (Tw σ.symm) _).comp
      (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous E (Tw σ) _)
  obtain ⟨y, hy⟩ :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective (K := E) (v := v) (x v)
  rw [← hy]
  refine UniformSpace.Completion.induction_on
    (p := fun t => (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E (Tw σ.symm)
        (⟨show HeightOneSpectrum (𝓞 (Tw σ.symm)) from v, h₂⟩ :
          IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 (Tw σ.symm)) z))
      ((IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E (Tw σ)
          (⟨show HeightOneSpectrum (𝓞 (Tw σ)) from z, h₁⟩ : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 (Tw σ)) v))
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion t)) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion t) y ?_ ?_
  · exact isClosed_eq (hc.comp (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion E v))
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion E v)
  · intro a
    exact local_fin_agree σ v z h₁ h₂ a

private theorem under_under_symm (w : HeightOneSpectrum (𝓞 E)) :
    (show HeightOneSpectrum (𝓞 (Tw σ)) from
        (show HeightOneSpectrum (𝓞 (Tw σ.symm)) from w).under (𝓞 E)).under (𝓞 E) = w := by
  ext a
  show (algebraMap (𝓞 E) (𝓞 (Tw σ.symm)) (algebraMap (𝓞 E) (𝓞 (Tw σ)) a) : 𝓞 E) ∈ w.asIdeal ↔ a ∈ w.asIdeal
  exact Iff.of_eq (congrArg (fun b : 𝓞 E => b ∈ w.asIdeal)
    (Subtype.ext (σ.symm_apply_apply (a : E)) :
      (algebraMap (𝓞 E) (𝓞 (Tw σ.symm)) (algebraMap (𝓞 E) (𝓞 (Tw σ)) a) : 𝓞 E) = a))

private theorem sigmaFin_symm_sigmaFin (x : FiniteAdeleRing (𝓞 E) E) : sigmaFin σ.symm (sigmaFin σ x) = x := by
  ext w
  exact local_fin_inv σ x _ w _ rfl rfl (under_under_symm σ w)

section IotaAt

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

@[reducible] private def liesOverOf (z : InfinitePlace L) (v : InfinitePlace K) (h : z.comap (algebraMap K L) = v) :
    z.1.LiesOver v.1 := by
  subst h
  exact liesOver_comap z

open scoped NumberField.LiesOver in
private def iotaAt (z : InfinitePlace L) (v : InfinitePlace K) (h : z.comap (algebraMap K L) = v) :
    v.Completion →+* z.Completion :=
  letI := liesOverOf z v h
  algebraMap v.Completion z.Completion

open scoped NumberField.LiesOver in
private theorem iotaAt_coe (z : InfinitePlace L) (v : InfinitePlace K) (h : z.comap (algebraMap K L) = v)
    (a : WithAbs v.1) :
    iotaAt z v h a = ((algebraMap (WithAbs v.1) (WithAbs z.1) a : WithAbs z.1) : z.Completion) := by
  letI := liesOverOf z v h
  exact NumberField.InfinitePlace.Completion.algebraMap_coe z a

open scoped NumberField.LiesOver in
private theorem continuous_iotaAt (z : InfinitePlace L) (v : InfinitePlace K) (h : z.comap (algebraMap K L) = v) :
    Continuous (iotaAt z v h) := by
  letI := liesOverOf z v h
  exact NumberField.LiesOver.continuous_completionMap

end IotaAt

private theorem local_inf_agree (v z : InfinitePlace E)
    (h₁ : (show InfinitePlace (Tw σ) from z).comap (algebraMap E (Tw σ)) = v)
    (h₂ : (show InfinitePlace (Tw σ.symm) from v).comap (algebraMap E (Tw σ.symm)) = z) (a : WithAbs v.1) :
    iotaAt (K := E) (L := Tw σ.symm) (show InfinitePlace (Tw σ.symm) from v) z h₂
        (iotaAt (K := E) (L := Tw σ) (show InfinitePlace (Tw σ) from z) v h₁ a) =
      (a : v.Completion) := by
  erw [iotaAt_coe]
  erw [iotaAt_coe]
  apply congrArg (fun t : WithAbs v.1 => (t : v.Completion))
  exact congrArg (WithAbs.equiv v.1).symm (σ.symm_apply_apply a.ofAbs)

private theorem local_inf_inv (x : InfiniteAdeleRing E) (v w z : InfinitePlace E)
    (h₁ : (show InfinitePlace (Tw σ) from z).comap (algebraMap E (Tw σ)) = v)
    (h₂ : (show InfinitePlace (Tw σ.symm) from w).comap (algebraMap E (Tw σ.symm)) = z) (hv : v = w) :
    iotaAt (K := E) (L := Tw σ.symm) (show InfinitePlace (Tw σ.symm) from w) z h₂
        (iotaAt (K := E) (L := Tw σ) (show InfinitePlace (Tw σ) from z) v h₁ (x v)) =
      x w := by
  subst hv
  exact NumberField.InfinitePlace.Completion.induction_on _
    (p := fun y => iotaAt (K := E) (L := Tw σ.symm) (show InfinitePlace (Tw σ.symm) from v) z h₂
      (iotaAt (K := E) (L := Tw σ) (show InfinitePlace (Tw σ) from z) v h₁ y) = y) (x v)
    (isClosed_eq ((continuous_iotaAt _ _ h₂).comp (continuous_iotaAt _ _ h₁)) continuous_id)
    (fun a => local_inf_agree σ v z h₁ h₂ a)

private theorem comap_comap_symm (w : InfinitePlace E) :
    (show InfinitePlace (Tw σ) from (show InfinitePlace (Tw σ.symm) from w).comap (algebraMap E (Tw σ.symm))).comap
        (algebraMap E (Tw σ)) = w := by
  ext a
  exact congrArg w (σ.symm_apply_apply a)

private theorem sigmaInfinite_symm_sigmaInfinite (x : InfiniteAdeleRing E) :
    sigmaInfinite σ.symm (sigmaInfinite σ x) = x := by
  funext w
  exact local_inf_inv σ x _ w _ rfl rfl (comap_comap_symm σ w)

private theorem sigmaAdele_symm_sigmaAdele (x : AdeleRing (𝓞 E) E) : sigmaAdele σ.symm (sigmaAdele σ x) = x :=
  Prod.ext (sigmaInfinite_symm_sigmaInfinite σ x.1) (sigmaFin_symm_sigmaFin σ x.2)

private theorem sigmaAdele_bijective : Function.Bijective (sigmaAdele σ) :=
  ⟨Function.LeftInverse.injective (sigmaAdele_symm_sigmaAdele σ),
    Function.RightInverse.surjective (g := sigmaAdele σ.symm) (sigmaAdele_symm_sigmaAdele σ.symm)⟩

private def sigmaAdeleHomeomorph : AdeleRing (𝓞 E) E ≃ₜ AdeleRing (𝓞 E) E where
  toFun := sigmaAdele σ
  invFun := sigmaAdele σ.symm
  left_inv := sigmaAdele_symm_sigmaAdele σ
  right_inv := sigmaAdele_symm_sigmaAdele σ.symm
  continuous_toFun := continuous_sigmaAdele σ
  continuous_invFun := continuous_sigmaAdele σ.symm

private theorem sigmaGL2_surjective : Function.Surjective (sigmaGL2 σ) := fun g =>
  ⟨sigmaGL2 σ.symm g, Units.ext (Matrix.ext fun i j => sigmaAdele_symm_sigmaAdele σ.symm (g i j))⟩

end Inverse

section FurnitureGL

private theorem sigmaGL2_symm_sigmaGL2 (g : AdelicGL2 (𝓞 E) E) : sigmaGL2 σ.symm (sigmaGL2 σ g) = g :=
  Units.ext (Matrix.ext fun i j => sigmaAdele_symm_sigmaAdele σ (g i j))

private theorem sigmaGL2_sigmaGL2_symm (g : AdelicGL2 (𝓞 E) E) : sigmaGL2 σ (sigmaGL2 σ.symm g) = g :=
  Units.ext (Matrix.ext fun i j => sigmaAdele_symm_sigmaAdele σ.symm (g i j))

private def sigmaGL2Equiv : AdelicGL2 (𝓞 E) E ≃* AdelicGL2 (𝓞 E) E where
  toFun := sigmaGL2 σ
  invFun := sigmaGL2 σ.symm
  left_inv := sigmaGL2_symm_sigmaGL2 σ
  right_inv := sigmaGL2_sigmaGL2_symm σ
  map_mul' := map_mul (sigmaGL2 σ)

private theorem sigmaGL2Equiv_apply (g : AdelicGL2 (𝓞 E) E) : sigmaGL2Equiv σ g = sigmaGL2 σ g := rfl

private theorem continuous_val_sigmaGL2 :
    Continuous fun g : AdelicGL2 (𝓞 E) E =>
      ((sigmaGL2 σ g : AdelicGL2 (𝓞 E) E) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 E) E)) :=
  Units.continuous_val.matrix_map (continuous_sigmaAdele σ)

private theorem continuous_sigmaGL2 : Continuous (sigmaGL2 σ) :=
  Units.continuous_iff.mpr ⟨continuous_val_sigmaGL2 σ, by
    simp only [← map_inv]
    exact (continuous_val_sigmaGL2 σ).comp continuous_inv⟩

private theorem algebraMap_tw (x : 𝓞 E) :
    (show 𝓞 E from algebraMap (𝓞 E) (𝓞 (Tw σ)) x) = intEquiv σ x :=
  Subtype.ext (algebraMap_galRestrict_apply ℤ σ x).symm

private theorem under_placeEquiv (w : HeightOneSpectrum (𝓞 E)) :
    (show HeightOneSpectrum (𝓞 (Tw σ)) from placeEquiv σ w).under (𝓞 E) = w := by
  ext x
  show (show 𝓞 E from algebraMap (𝓞 E) (𝓞 (Tw σ)) x) ∈ (placeEquiv σ w).asIdeal ↔ x ∈ w.asIdeal
  rw [algebraMap_tw]
  show (intEquiv σ).symm (intEquiv σ x) ∈ w.asIdeal ↔ x ∈ w.asIdeal
  rw [RingEquiv.symm_apply_apply]

private theorem placeEquiv_under (z : HeightOneSpectrum (𝓞 E)) :
    placeEquiv σ ((show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E)) = z := by
  ext x
  show (intEquiv σ).symm x ∈ ((show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E)).asIdeal ↔
    x ∈ z.asIdeal
  show (show 𝓞 E from algebraMap (𝓞 E) (𝓞 (Tw σ)) ((intEquiv σ).symm x)) ∈ z.asIdeal ↔ x ∈ z.asIdeal
  rw [algebraMap_tw, RingEquiv.apply_symm_apply]

private theorem asIdeal_placeEquiv (w : HeightOneSpectrum (𝓞 E)) :
    (placeEquiv σ w).asIdeal = w.asIdeal.map (intEquiv σ : 𝓞 E →+* 𝓞 E) :=
  Ideal.comap_symm (intEquiv σ)

private theorem sigmaGL2_centralScalar (z : (AdeleRing (𝓞 E) E)ˣ) :
    sigmaGL2 σ (centralScalar (𝓞 E) E z)
      = centralScalar (𝓞 E) E (Units.map (sigmaAdele σ).toMonoidHom z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [centralScalar, sigmaGL2]

private theorem sigmaGL2_unipotentGL2 (x : AdeleRing (𝓞 E) E) :
    sigmaGL2 σ (unipotentGL2 x) = unipotentGL2 (sigmaAdele σ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaGL2]

private theorem glArch_sigmaGL2 (g : AdelicGL2 (𝓞 E) E) :
    glArch (𝓞 E) E (sigmaGL2 σ g)
      = Matrix.GeneralLinearGroup.map (sigmaInfinite σ) (glArch (𝓞 E) E g) :=
  Units.ext (Matrix.ext fun _ _ => rfl)

private theorem sigmaGL2_mem_finiteAdelicGL2Subgroup {g : AdelicGL2 (𝓞 E) E}
    (hg : g ∈ finiteAdelicGL2Subgroup E) : sigmaGL2 σ g ∈ finiteAdelicGL2Subgroup E := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at hg ⊢
  rw [glArch_sigmaGL2, hg, map_one]

private def conjCentralChar (χ : (⊤ : Subgroup (AdeleRing (𝓞 E) E)ˣ) →* ℂˣ) :
    (⊤ : Subgroup (AdeleRing (𝓞 E) E)ˣ) →* ℂˣ :=
  χ.comp (((Units.map (sigmaAdele σ).toMonoidHom).domRestrict
    (⊤ : Subgroup (AdeleRing (𝓞 E) E)ˣ)).codRestrict ⊤ fun _ => Subgroup.mem_top _)

private theorem conjCentralChar_apply (χ : (⊤ : Subgroup (AdeleRing (𝓞 E) E)ˣ) →* ℂˣ)
    (z : (⊤ : Subgroup (AdeleRing (𝓞 E) E)ˣ)) :
    conjCentralChar σ χ z
      = χ ⟨Units.map (sigmaAdele σ).toMonoidHom (z : (AdeleRing (𝓞 E) E)ˣ), Subgroup.mem_top _⟩ := rfl

end FurnitureGL

section CosetTransport

variable {G : Type*} [Group G]

private theorem doubleCoset_mul_right (U : Subgroup G) (g : G) {u : G} (hu : u ∈ U) :
    HeckePair.doubleCoset U (g * u) = HeckePair.doubleCoset U g := by
  ext x
  simp only [HeckePair.mem_doubleCoset_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, u * b, U.mul_mem hu hb, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, u⁻¹ * b, U.mul_mem (U.inv_mem hu) hb, by group⟩

private theorem map_mem_doubleCoset_map_iff (α : G ≃* G) (U : Subgroup G) (g x : G) :
    α x ∈ HeckePair.doubleCoset (U.map α.toMonoidHom) (α g) ↔ x ∈ HeckePair.doubleCoset U g := by
  simp only [HeckePair.mem_doubleCoset_iff]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    refine ⟨a', ha', b', hb', α.injective ?_⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using h
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨α a, Subgroup.mem_map_of_mem _ ha, α b, Subgroup.mem_map_of_mem _ hb, by simp only [map_mul]⟩

private theorem isHeckeCosetSystem_map (α : G ≃* G) {U : Subgroup G} {g : G} {ι : Type*} {reps : ι → G}
    (h : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) :
    HeckeIntegralSeam.IsHeckeCosetSystem (U.map α.toMonoidHom) (α g) (fun i => α (reps i)) where
  mem_doubleCoset i := (map_mem_doubleCoset_map_iff α U g (reps i)).mpr (h.mem_doubleCoset i)
  covers x hx := by
    obtain ⟨i, hi⟩ := h.covers (α.symm x)
      ((map_mem_doubleCoset_map_iff α U g (α.symm x)).mp (by simpa using hx))
    refine ⟨i, ?_⟩
    show (QuotientGroup.mk x : G ⧸ U.map α.toMonoidHom) = QuotientGroup.mk (α (reps i))
    rw [QuotientGroup.eq] at hi ⊢
    have hmem := Subgroup.mem_map_of_mem α.toMonoidHom hi
    simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hmem
  mk_injective i j hij := by
    apply h.mk_injective
    have hij' : (QuotientGroup.mk (α (reps i)) : G ⧸ U.map α.toMonoidHom)
        = QuotientGroup.mk (α (reps j)) := hij
    show (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
    rw [QuotientGroup.eq] at hij' ⊢
    obtain ⟨y, hy, hy'⟩ := Subgroup.mem_map.mp hij'
    have hyy : y = (reps i)⁻¹ * reps j := α.injective (by rw [map_mul, map_inv]; exact hy')
    rwa [hyy] at hy

end CosetTransport

section FurnitureMeasure

open MeasureTheory in
private theorem memLp_restrict_empty {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℂ) :
    MemLp f 2 (μ.restrict (∅ : Set X)) := by
  rw [Measure.restrict_empty]
  exact ⟨aestronglyMeasurable_zero_measure f, by rw [eLpNorm_measure_zero]; exact ENNReal.zero_lt_top⟩

end FurnitureMeasure

section IdealBound

private theorem irreducible_mk_asIdeal (v : HeightOneSpectrum (𝓞 E)) :
    Irreducible (Associates.mk v.asIdeal) :=
  Associates.irreducible_mk.mpr v.irreducible

private theorem count_eq_of_pow_dvd_iff {p q N M : Ideal (𝓞 E)} (hN : N ≠ ⊥) (hM : M ≠ ⊥)
    (hp : Irreducible (Associates.mk p)) (hq : Irreducible (Associates.mk q))
    (h : ∀ k : ℕ, p ^ k ∣ N ↔ q ^ k ∣ M) :
    (Associates.mk p).count (Associates.mk N).factors
      = (Associates.mk q).count (Associates.mk M).factors := by
  have hN' : Associates.mk N ≠ 0 := Associates.mk_ne_zero.mpr (show N ≠ 0 from hN)
  have hM' : Associates.mk M ≠ 0 := Associates.mk_ne_zero.mpr (show M ≠ 0 from hM)
  have key : ∀ k : ℕ, k ≤ (Associates.mk p).count (Associates.mk N).factors ↔
      k ≤ (Associates.mk q).count (Associates.mk M).factors := by
    intro k
    rw [← Associates.prime_pow_dvd_iff_le hN' hp, ← Associates.prime_pow_dvd_iff_le hM' hq,
      ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
      Associates.mk_le_mk_iff_dvd]
    exact h k
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

private theorem pow_map_dvd_map_iff (N : Ideal (𝓞 E)) (w : HeightOneSpectrum (𝓞 E)) (k : ℕ) :
    (placeEquiv σ w).asIdeal ^ k ∣ N.map (intEquiv σ : 𝓞 E →+* 𝓞 E) ↔ w.asIdeal ^ k ∣ N := by
  rw [asIdeal_placeEquiv, ← Ideal.map_pow, Ideal.dvd_iff_le, Ideal.dvd_iff_le,
    Ideal.map_le_iff_le_comap,
    Ideal.comap_map_of_bijective (intEquiv σ : 𝓞 E →+* 𝓞 E) (intEquiv σ).bijective]

private theorem idealBound_map_placeEquiv (N : Ideal (𝓞 E)) (w : HeightOneSpectrum (𝓞 E)) :
    idealBound (𝓞 E) (N.map (intEquiv σ : 𝓞 E →+* 𝓞 E)) (placeEquiv σ w) = idealBound (𝓞 E) N w := by
  by_cases hN : N = ⊥
  · subst hN
    rw [Ideal.map_bot, idealBound_bot, idealBound_bot]
  have hM : N.map (intEquiv σ : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    rwa [Ne, Ideal.map_eq_bot_iff_of_injective (f := (intEquiv σ : 𝓞 E →+* 𝓞 E)) (intEquiv σ).injective]
  rw [idealBound_of_ne_bot hM, idealBound_of_ne_bot hN,
    count_eq_of_pow_dvd_iff hM hN (irreducible_mk_asIdeal _) (irreducible_mk_asIdeal w)
      (pow_map_dvd_map_iff σ N w)]

end IdealBound

section GlobalPoints

private theorem sigmaFin_algebraMap (x : E) :
    sigmaFin σ (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (σ x) :=
  (sigmaFinAdele σ).toSemialgHom.commutes x

private theorem sigmaFin_algebraMap' (x : E) :
    sigmaFin σ (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (σ x) :=
  @ContinuousSemialgHom.commutes _ _ _ _ _ _ _ _ _ _ _ _ _ (sigmaFinAdele σ) x

private theorem sigmaFin_algebraMap'' (x : E) :
    sigmaFin σ (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (σ x) := by
  show IsDedekindDomain.FiniteAdeleRing.mapSemialgHom (𝓞 E) E (Tw σ) (𝓞 (Tw σ))
        (algebraMap E (FiniteAdeleRing (𝓞 E) E) x)
      = algebraMap (Tw σ) (FiniteAdeleRing (𝓞 (Tw σ)) (Tw σ)) (algebraMap E (Tw σ) x)
  exact (IsDedekindDomain.FiniteAdeleRing.mapSemialgHom (𝓞 E) E (Tw σ) (𝓞 (Tw σ))).toSemialgHom.commutes x

private theorem sigmaInfinite_algebraMap (x : E) :
    sigmaInfinite σ (algebraMap E (InfiniteAdeleRing E) x) = algebraMap E (InfiniteAdeleRing E) (σ x) := by
  funext w
  show iotaAt (K := E) (L := Tw σ) (show InfinitePlace (Tw σ) from w) (conjPlace σ w) rfl
      (((WithAbs.equiv _).symm x : WithAbs (conjPlace σ w).1) : (conjPlace σ w).Completion)
    = (((WithAbs.equiv _).symm (σ x) : WithAbs w.1) : w.Completion)
  exact (iotaAt_coe (K := E) (L := Tw σ) _ _ rfl _).trans rfl

private theorem sigmaAdele_algebraMap (x : E) :
    sigmaAdele σ (algebraMap E (AdeleRing (𝓞 E) E) x) = algebraMap E (AdeleRing (𝓞 E) E) (σ x) :=
  Prod.ext (sigmaInfinite_algebraMap σ x) (sigmaFin_algebraMap σ x)

private theorem sigmaGL2_globalPoints (γ : GL (Fin 2) E) :
    sigmaGL2 σ (globalPoints (𝓞 E) E γ)
      = globalPoints (𝓞 E) E (Matrix.GeneralLinearGroup.map (σ : E →+* E) γ) :=
  Units.ext (Matrix.ext fun i j => sigmaAdele_algebraMap σ (γ i j))

private theorem sigmaAdele_mem_principalSubgroup {p : AdeleRing (𝓞 E) E}
    (hp : p ∈ AdeleRing.principalSubgroup (𝓞 E) E) :
    sigmaAdele σ p ∈ AdeleRing.principalSubgroup (𝓞 E) E := by
  obtain ⟨k, rfl⟩ := hp
  exact ⟨σ k, (sigmaAdele_algebraMap σ k).symm⟩

end GlobalPoints

section Ramification

private theorem algebraMap_tw_surjective : Function.Surjective (algebraMap (𝓞 E) (𝓞 (Tw σ))) := fun y =>
  ⟨(intEquiv σ).symm y, (algebraMap_tw σ _).trans ((intEquiv σ).apply_symm_apply y)⟩

private theorem ramificationIdx_tw_eq_one (w : HeightOneSpectrum (𝓞 (Tw σ))) :
    (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1 := by
  have hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 (Tw σ))) (w.under (𝓞 E)).asIdeal = w.asIdeal :=
    Ideal.map_comap_of_surjective _ (algebraMap_tw_surjective σ) _
  refine Ideal.ramificationIdx_spec ?_ ?_
  · rw [hmap, pow_one]
  · rw [hmap]
    intro h
    exact lt_irrefl _ (lt_of_lt_of_le (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl) h)

private theorem valued_sigmaFin (x : FiniteAdeleRing (𝓞 E) E) (z : HeightOneSpectrum (𝓞 E)) :
    Valued.v (sigmaFin σ x z)
      = Valued.v (x ((show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E))) := by
  have h := IsDedekindDomain.HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom E (Tw σ)
    (⟨show HeightOneSpectrum (𝓞 (Tw σ)) from z, rfl⟩ :
      IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 (Tw σ))
        ((show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E)))
    (x ((show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E)))
  rw [ramificationIdx_tw_eq_one, pow_one] at h
  show Valued.v (IsDedekindDomain.FiniteAdeleRing.mapSemialgHom (𝓞 E) E (Tw σ) (𝓞 (Tw σ)) x
      (show HeightOneSpectrum (𝓞 (Tw σ)) from z)) = _
  rw [IsDedekindDomain.FiniteAdeleRing.mapSemialgHom_apply]
  exact h

end Ramification

section Level

private theorem sigmaFin_mem_idealBall {N : Ideal (𝓞 E)} {x : FiniteAdeleRing (𝓞 E) E}
    (hx : x ∈ idealBall (𝓞 E) E N) :
    sigmaFin σ x ∈ idealBall (𝓞 E) E (N.map (intEquiv σ : 𝓞 E →+* 𝓞 E)) := by
  intro z
  rw [valued_sigmaFin]
  have h := hx ((show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E))
  rwa [← idealBound_map_placeEquiv σ N, placeEquiv_under] at h

private theorem isLevelZeroMatrix_map {N : Ideal (𝓞 E)} {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 E) E)}
    (hm : IsLevelZeroMatrix (𝓞 E) E N m) :
    IsLevelZeroMatrix (𝓞 E) E (N.map (intEquiv σ : 𝓞 E →+* 𝓞 E)) (m.map (sigmaFin σ)) where
  integral i j := sigmaFin_mem_integral σ (hm.integral i j)
  lowerLeft := sigmaFin_mem_idealBall σ hm.lowerLeft

private theorem isLevelOneMatrix_map {N : Ideal (𝓞 E)} {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 E) E)}
    (hm : IsLevelOneMatrix (𝓞 E) E N m) :
    IsLevelOneMatrix (𝓞 E) E (N.map (intEquiv σ : 𝓞 E →+* 𝓞 E)) (m.map (sigmaFin σ)) where
  toIsLevelZeroMatrix := isLevelZeroMatrix_map σ hm.toIsLevelZeroMatrix
  lowerRight := by
    have h := sigmaFin_mem_idealBall σ hm.lowerRight
    rwa [map_sub, map_one] at h

private theorem sigmaFinGL2_mem_finiteLevelOne {N : Ideal (𝓞 E)} {g : GL (Fin 2) (FiniteAdeleRing (𝓞 E) E)}
    (hg : g ∈ finiteLevelOne (𝓞 E) E N) :
    sigmaFinGL2 σ g ∈ finiteLevelOne (𝓞 E) E (N.map (intEquiv σ : 𝓞 E →+* 𝓞 E)) := by
  rw [mem_finiteLevelOne_iff] at hg ⊢
  refine ⟨isLevelOneMatrix_map σ hg.1, ?_⟩
  rw [← map_inv]
  exact isLevelOneMatrix_map σ hg.2

private theorem sigmaGL2_mem_levelOne {N : Ideal (𝓞 E)} {g : AdelicGL2 (𝓞 E) E} (hg : g ∈ levelOne (𝓞 E) E N) :
    sigmaGL2 σ g ∈ levelOne (𝓞 E) E (N.map (intEquiv σ : 𝓞 E →+* 𝓞 E)) := by
  have hg' : glFin (𝓞 E) E g ∈ finiteLevelOne (𝓞 E) E N := hg
  show glFin (𝓞 E) E (sigmaGL2 σ g) ∈ finiteLevelOne (𝓞 E) E (N.map (intEquiv σ : 𝓞 E →+* 𝓞 E))
  rw [glFin_sigmaGL2]
  exact sigmaFinGL2_mem_finiteLevelOne σ hg'

private theorem sigmaGL2_mem_rowLevel {N : Ideal (𝓞 E)} {g : AdelicGL2 (𝓞 E) E}
    (hg : g ∈ levelOne (𝓞 E) E N ⊓ finiteAdelicGL2Subgroup E) :
    sigmaGL2 σ g ∈ levelOne (𝓞 E) E (N.map (intEquiv σ : 𝓞 E →+* 𝓞 E)) ⊓ finiteAdelicGL2Subgroup E := by
  rw [Subgroup.mem_inf] at hg ⊢
  exact ⟨sigmaGL2_mem_levelOne σ hg.1, sigmaGL2_mem_finiteAdelicGL2Subgroup σ hg.2⟩

private theorem map_comap_intEquiv (I : Ideal (𝓞 E)) :
    (I.comap (intEquiv σ : 𝓞 E →+* 𝓞 E)).map (intEquiv σ : 𝓞 E →+* 𝓞 E) = I :=
  Ideal.map_comap_of_surjective _ (intEquiv σ).surjective I

private theorem sigmaGL2_mem_rowLevel_conjTable (Φ : HeckeEigensystem E ℂ) {g : AdelicGL2 (𝓞 E) E}
    (hg : g ∈ levelOne (𝓞 E) E (conjTable σ Φ).level ⊓ finiteAdelicGL2Subgroup E) :
    sigmaGL2 σ g ∈ levelOne (𝓞 E) E Φ.level ⊓ finiteAdelicGL2Subgroup E := by
  have h := sigmaGL2_mem_rowLevel σ hg
  rwa [show (conjTable σ Φ).level = Φ.level.comap (intEquiv σ : 𝓞 E →+* 𝓞 E) from rfl,
    map_comap_intEquiv] at h

end Level

section NuRoad

open MeasureTheory

private scoped instance instMeasurableSpaceAdele : MeasurableSpace (AdeleRing (𝓞 E) E) :=
  AdelicHaar.adeleBorel (𝓞 E) E

private scoped instance instBorelSpaceAdele : BorelSpace (AdeleRing (𝓞 E) E) :=
  AdelicHaar.borelSpace_adeleBorel (𝓞 E) E

private scoped instance instIsAddHaarMeasure_adelicAddHaar :
    (AdelicHaar.adelicAddHaar (𝓞 E) E).IsAddHaarMeasure :=
  AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 E) E

private scoped instance instRegular_adelicAddHaar : (AdelicHaar.adelicAddHaar (𝓞 E) E).Regular :=
  inferInstanceAs (Measure.addHaarMeasure (Classical.arbitrary _)).Regular

private theorem regular_adelicAddHaar' : (AdelicHaar.adelicAddHaar (𝓞 E) E).Regular := by
  unfold AdelicHaar.adelicAddHaar Measure.addHaar
  infer_instance

private def sigmaAddEquiv : AdeleRing (𝓞 E) E ≃+ AdeleRing (𝓞 E) E :=
  { (sigmaAdeleHomeomorph σ).toEquiv with map_add' := map_add (sigmaAdele σ) }

private def sigmaMeasurableEquiv : AdeleRing (𝓞 E) E ≃ᵐ AdeleRing (𝓞 E) E :=
  (sigmaAdeleHomeomorph σ).toMeasurableEquiv

private theorem coe_sigmaMeasurableEquiv : ⇑(sigmaMeasurableEquiv σ) = ⇑(sigmaAdele σ) := rfl

private theorem isAddHaarMeasure_map_sigmaAdele :
    (Measure.map (sigmaAdele σ) (AdelicHaar.adelicAddHaar (𝓞 E) E)).IsAddHaarMeasure :=
  (sigmaAddEquiv σ).isAddHaarMeasure_map _ (continuous_sigmaAdele σ) (continuous_sigmaAdele σ.symm)

private theorem regular_map_sigmaAdele :
    (Measure.map (sigmaAdele σ) (AdelicHaar.adelicAddHaar (𝓞 E) E)).Regular :=
  Measure.Regular.map (μ := AdelicHaar.adelicAddHaar (𝓞 E) E) (sigmaAdeleHomeomorph σ)

private theorem exists_map_sigmaAdele_eq_smul :
    ∃ c : NNReal, 0 < c ∧
      Measure.map (sigmaAdele σ) (AdelicHaar.adelicAddHaar (𝓞 E) E)
        = c • AdelicHaar.adelicAddHaar (𝓞 E) E := by
  haveI := isAddHaarMeasure_map_sigmaAdele σ
  haveI := regular_map_sigmaAdele σ
  exact ⟨_, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (Measure.map (sigmaAdele σ) (AdelicHaar.adelicAddHaar (𝓞 E) E)) (AdelicHaar.adelicAddHaar (𝓞 E) E),
    Measure.isAddLeftInvariant_eq_smul_of_regular _ _⟩

private noncomputable def sigmaFactor : NNReal := (exists_map_sigmaAdele_eq_smul σ).choose

private theorem sigmaFactor_pos : 0 < sigmaFactor σ := (exists_map_sigmaAdele_eq_smul σ).choose_spec.1

private theorem map_sigmaAdele_eq_smul :
    Measure.map (sigmaAdele σ) (AdelicHaar.adelicAddHaar (𝓞 E) E)
      = sigmaFactor σ • AdelicHaar.adelicAddHaar (𝓞 E) E :=
  (exists_map_sigmaAdele_eq_smul σ).choose_spec.2

private theorem quasiMeasurePreserving_sigmaAdele :
    Measure.QuasiMeasurePreserving (sigmaAdele σ) (AdelicHaar.adelicAddHaar (𝓞 E) E)
      (AdelicHaar.adelicAddHaar (𝓞 E) E) :=
  ⟨(continuous_sigmaAdele σ).measurable, by
    rw [map_sigmaAdele_eq_smul, ENNReal.smul_def]
    exact Measure.smul_absolutelyContinuous⟩

private def principalMap (p : AdeleRing.principalSubgroup (𝓞 E) E) : AdeleRing.principalSubgroup (𝓞 E) E :=
  ⟨sigmaAdele σ p, sigmaAdele_mem_principalSubgroup σ p.2⟩

private theorem principalMap_symm_principalMap (p : AdeleRing.principalSubgroup (𝓞 E) E) :
    principalMap σ.symm (principalMap σ p) = p :=
  Subtype.ext (sigmaAdele_symm_sigmaAdele σ p)

private theorem principalMap_bijective : Function.Bijective (principalMap σ) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨principalMap σ.symm, principalMap_symm_principalMap σ, principalMap_symm_principalMap σ.symm⟩

private scoped instance instCountablePrincipal : Countable (AdeleRing.principalSubgroup (𝓞 E) E) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  refine Function.Surjective.countable (f := fun k : E =>
    (⟨algebraMap E (AdeleRing (𝓞 E) E) k, k, rfl⟩ : AdeleRing.principalSubgroup (𝓞 E) E)) ?_
  rintro ⟨_, k, rfl⟩
  exact ⟨k, rfl⟩

private theorem isAddFundamentalDomain_preimage_box :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E)
      (sigmaAdele σ.symm ⁻¹' AdelicBox.adelicBox E) (AdelicHaar.adelicAddHaar (𝓞 E) E) :=
  (AdelicBox.isAddFundamentalDomain_adelicBox E _).preimage_of_equiv
    (quasiMeasurePreserving_sigmaAdele σ.symm) (principalMap_bijective σ) (fun p x => by
      show sigmaAdele σ.symm ((sigmaAdele σ p : AdeleRing (𝓞 E) E) + x)
        = (p : AdeleRing (𝓞 E) E) + sigmaAdele σ.symm x
      rw [map_add, sigmaAdele_symm_sigmaAdele])

private theorem preimage_sigmaAdele_preimage_symm (s : Set (AdeleRing (𝓞 E) E)) :
    sigmaAdele σ ⁻¹' (sigmaAdele σ.symm ⁻¹' s) = s := by
  ext x
  simp only [Set.mem_preimage, sigmaAdele_symm_sigmaAdele]

private theorem setIntegral_box_comp_sigmaAdele (H : AdeleRing (𝓞 E) E → ℂ)
    (hH : ∀ (p : AdeleRing.principalSubgroup (𝓞 E) E) (x : AdeleRing (𝓞 E) E), H (p +ᵥ x) = H x) :
    ∫ x in AdelicBox.adelicBox E, H (sigmaAdele σ x) ∂AdelicHaar.adelicAddHaar (𝓞 E) E
      = sigmaFactor σ • ∫ x in AdelicBox.adelicBox E, H x ∂AdelicHaar.adelicAddHaar (𝓞 E) E := by
  have h₁ := setIntegral_map_equiv (μ := AdelicHaar.adelicAddHaar (𝓞 E) E) (sigmaMeasurableEquiv σ) H
    (sigmaAdele σ.symm ⁻¹' AdelicBox.adelicBox E)
  rw [coe_sigmaMeasurableEquiv, preimage_sigmaAdele_preimage_symm, map_sigmaAdele_eq_smul,
    Measure.restrict_smul, integral_smul_nnreal_measure] at h₁
  rw [← h₁]
  congr 1
  exact (isAddFundamentalDomain_preimage_box σ).setIntegral_eq
    (AdelicBox.isAddFundamentalDomain_adelicBox E _) hH

private theorem integrableOn_box_comp_sigmaAdele_iff (H : AdeleRing (𝓞 E) E → ℂ)
    (hH : ∀ (p : AdeleRing.principalSubgroup (𝓞 E) E) (x : AdeleRing (𝓞 E) E), H (p +ᵥ x) = H x) :
    IntegrableOn (fun x => H (sigmaAdele σ x)) (AdelicBox.adelicBox E) (AdelicHaar.adelicAddHaar (𝓞 E) E)
      ↔ IntegrableOn H (AdelicBox.adelicBox E) (AdelicHaar.adelicAddHaar (𝓞 E) E) := by
  have h₁ : IntegrableOn H (sigmaAdele σ.symm ⁻¹' AdelicBox.adelicBox E)
      (Measure.map (sigmaAdele σ) (AdelicHaar.adelicAddHaar (𝓞 E) E))
      ↔ IntegrableOn (fun x => H (sigmaAdele σ x)) (AdelicBox.adelicBox E)
          (AdelicHaar.adelicAddHaar (𝓞 E) E) := by
    unfold IntegrableOn
    rw [← coe_sigmaMeasurableEquiv, (sigmaMeasurableEquiv σ).measurableEmbedding.restrict_map,
      integrable_map_equiv (sigmaMeasurableEquiv σ), coe_sigmaMeasurableEquiv,
      preimage_sigmaAdele_preimage_symm]
    exact Iff.rfl
  rw [← h₁, map_sigmaAdele_eq_smul, ENNReal.smul_def, IntegrableOn, Measure.restrict_smul,
    integrable_smul_measure (by exact_mod_cast (sigmaFactor_pos σ).ne') ENNReal.coe_ne_top]
  exact (isAddFundamentalDomain_preimage_box σ).integrableOn_iff
    (AdelicBox.isAddFundamentalDomain_adelicBox E _) hH

private theorem integral_cond_comp_sigmaAdele (H : AdeleRing (𝓞 E) E → ℂ)
    (hH : ∀ (p : AdeleRing.principalSubgroup (𝓞 E) E) (x : AdeleRing (𝓞 E) E), H (p +ᵥ x) = H x) :
    ∫ x, H (sigmaAdele σ x) ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 E) E) (AdelicBox.adelicBox E))
      = sigmaFactor σ •
        ∫ x, H x ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 E) E) (AdelicBox.adelicBox E)) := by
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure, integral_smul_measure, setIntegral_box_comp_sigmaAdele σ H hH, smul_comm]

private theorem integrable_cond_comp_sigmaAdele_iff (H : AdeleRing (𝓞 E) E → ℂ)
    (hH : ∀ (p : AdeleRing.principalSubgroup (𝓞 E) E) (x : AdeleRing (𝓞 E) E), H (p +ᵥ x) = H x) :
    Integrable (fun x => H (sigmaAdele σ x))
        (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 E) E) (AdelicBox.adelicBox E))
      ↔ Integrable H (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 E) E) (AdelicBox.adelicBox E)) := by
  unfold ProbabilityTheory.cond
  rcases eq_or_ne (AdelicHaar.adelicAddHaar (𝓞 E) E (AdelicBox.adelicBox E)) 0 with h0 | h0
  · rw [Measure.restrict_eq_zero.mpr h0, smul_zero]
    exact ⟨fun _ => integrable_zero_measure, fun _ => integrable_zero_measure⟩
  rcases eq_or_ne (AdelicHaar.adelicAddHaar (𝓞 E) E (AdelicBox.adelicBox E)) ⊤ with htop | htop
  · rw [htop, ENNReal.inv_top, zero_smul]
    exact ⟨fun _ => integrable_zero_measure, fun _ => integrable_zero_measure⟩
  rw [integrable_smul_measure (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr h0),
    integrable_smul_measure (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr h0)]
  exact integrableOn_box_comp_sigmaAdele_iff σ H hH

end NuRoad

section Token

variable {φ : AdelicGL2 (𝓞 E) E → ℂ}

private theorem continuous_comp_sigmaGL2 (hφ : Continuous φ) : Continuous (fun g => φ (sigmaGL2 σ g)) :=
  hφ.comp (continuous_sigmaGL2 σ)

open scoped Classical in
private theorem isBoundedOnSiegelWindows_comp_sigmaGL2 (hφ : IsBoundedOnSiegelWindows E φ) :
    IsBoundedOnSiegelWindows E (fun g => φ (sigmaGL2 σ g)) := by
  intro c u d₁ d₂ T hc hd₁
  obtain ⟨C, hC⟩ := hφ c u d₁ d₂ (T.image (sigmaGL2 σ)) hc hd₁
  exact ⟨C, fun g hg => hC _ (sigmaGL2_mem_window σ T hg)⟩

private theorem isLsXiFunction_comp_sigmaGL2 (χ : (⊤ : Subgroup (AdeleRing (𝓞 E) E)ˣ) →* ℂˣ)
    (hφ : IsLsXiFunction (𝓞 E) E ⊤ χ φ) :
    IsLsXiFunction (𝓞 E) E ⊤ (conjCentralChar σ χ) (fun g => φ (sigmaGL2 σ g)) where
  left_invariant γ g := by
    show φ (sigmaGL2 σ (globalPoints (𝓞 E) E γ * g)) = φ (sigmaGL2 σ g)
    rw [map_mul, sigmaGL2_globalPoints]
    exact hφ.left_invariant _ _
  central_transform z g := by
    show φ (sigmaGL2 σ (centralScalar (𝓞 E) E (z : (AdeleRing (𝓞 E) E)ˣ) * g))
      = ((conjCentralChar σ χ z : ℂˣ) : ℂ) * φ (sigmaGL2 σ g)
    rw [map_mul, sigmaGL2_centralScalar, conjCentralChar_apply]
    exact hφ.central_transform ⟨Units.map (sigmaAdele σ).toMonoidHom (z : (AdeleRing (𝓞 E) E)ˣ),
      Subgroup.mem_top _⟩ _

private def sigmaKf (k : finiteAdelicGL2Subgroup E) : finiteAdelicGL2Subgroup E :=
  ⟨sigmaGL2 σ k, sigmaGL2_mem_finiteAdelicGL2Subgroup σ k.2⟩

private theorem continuous_sigmaKf : Continuous (sigmaKf σ) :=
  ((continuous_sigmaGL2 σ).comp continuous_subtype_val).subtype_mk _

open FLT.SmoothVectors in
private theorem isKfSmooth_comp_sigmaGL2 (hφ : IsKfSmooth E φ) : IsKfSmooth E (fun g => φ (sigmaGL2 σ g)) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hφ ⊢
  have hset : ((MulAction.stabilizer (finiteAdelicGL2Subgroup E)
        (RightTranslationFn.mk (fun g => φ (sigmaGL2 σ g)) : RightTranslationFn (AdelicGL2 (𝓞 E) E) ℂ) :
          Subgroup (finiteAdelicGL2Subgroup E)) : Set (finiteAdelicGL2Subgroup E))
      = sigmaKf σ ⁻¹' ((MulAction.stabilizer (finiteAdelicGL2Subgroup E)
          (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 E) E) ℂ) :
            Subgroup (finiteAdelicGL2Subgroup E)) : Set (finiteAdelicGL2Subgroup E)) := by
    ext k
    simp only [SetLike.mem_coe, Set.mem_preimage, MulAction.mem_stabilizer_iff]
    constructor
    · intro hk
      refine RightTranslationFn.ext fun y => ?_
      obtain ⟨x, rfl⟩ := sigmaGL2_surjective σ y
      have h₁ : φ (sigmaGL2 σ (x * (k : AdelicGL2 (𝓞 E) E))) = φ (sigmaGL2 σ x) :=
        congrArg (fun f : RightTranslationFn (AdelicGL2 (𝓞 E) E) ℂ => RightTranslationFn.toFun f x) hk
      show φ (sigmaGL2 σ x * sigmaGL2 σ (k : AdelicGL2 (𝓞 E) E)) = φ (sigmaGL2 σ x)
      rw [← map_mul]
      exact h₁
    · intro hk
      refine RightTranslationFn.ext fun x => ?_
      have h₂ : φ (sigmaGL2 σ x * sigmaGL2 σ (k : AdelicGL2 (𝓞 E) E)) = φ (sigmaGL2 σ x) :=
        congrArg (fun f : RightTranslationFn (AdelicGL2 (𝓞 E) E) ℂ =>
          RightTranslationFn.toFun f (sigmaGL2 σ x)) hk
      show φ (sigmaGL2 σ (x * (k : AdelicGL2 (𝓞 E) E))) = φ (sigmaGL2 σ x)
      rw [map_mul]
      exact h₂
  rw [hset]
  exact hφ.preimage (continuous_sigmaKf σ)

private theorem exists_comp_sigmaGL2_ne_zero (hφ : ∃ g, φ g ≠ 0) : ∃ g, φ (sigmaGL2 σ g) ≠ 0 := by
  obtain ⟨g, hg⟩ := hφ
  refine ⟨(sigmaGL2Equiv σ).symm g, ?_⟩
  show φ (sigmaGL2Equiv σ ((sigmaGL2Equiv σ).symm g)) ≠ 0
  rwa [MulEquiv.apply_symm_apply]

private theorem unipotentGL2_algebraMap (k : E) :
    unipotentGL2 (algebraMap E (AdeleRing (𝓞 E) E) k) = globalPoints (𝓞 E) E (unipotentGL2 k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPoints, unipotentGL2]

private theorem unipotent_integrand_vadd (hφ : ∀ (γ : GL (Fin 2) E) (g : AdelicGL2 (𝓞 E) E),
      φ (globalPoints (𝓞 E) E γ * g) = φ g) (h : AdelicGL2 (𝓞 E) E)
    (p : AdeleRing.principalSubgroup (𝓞 E) E) (x : AdeleRing (𝓞 E) E) :
    φ (unipotentGL2 (p +ᵥ x) * h) = φ (unipotentGL2 x * h) := by
  obtain ⟨p, k, rfl⟩ := p
  show φ (unipotentGL2 (algebraMap E (AdeleRing (𝓞 E) E) k + x) * h) = φ (unipotentGL2 x * h)
  rw [unipotentGL2_add, unipotentGL2_algebraMap, mul_assoc]
  exact hφ _ _

open MeasureTheory in

private theorem isCuspidalFn_comp_sigmaGL2
    (hφ : ∀ (γ : GL (Fin 2) E) (g : AdelicGL2 (𝓞 E) E), φ (globalPoints (𝓞 E) E γ * g) = φ g)
    (hcusp : IsCuspidalFn (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 E) E) (AdelicBox.adelicBox E))
      unipotentGL2 φ) :
    IsCuspidalFn (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 E) E) (AdelicBox.adelicBox E))
      unipotentGL2 (fun g => φ (sigmaGL2 σ g)) := by
  intro g
  have h := integral_cond_comp_sigmaAdele σ (fun y => φ (unipotentGL2 y * sigmaGL2 σ g))
    (unipotent_integrand_vadd hφ (sigmaGL2 σ g))
  have hc : constantTerm (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 E) E) (AdelicBox.adelicBox E))
      unipotentGL2 (fun g => φ (sigmaGL2 σ g)) g
        = ∫ q, φ (unipotentGL2 (sigmaAdele σ q) * sigmaGL2 σ g)
            ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 E) E) (AdelicBox.adelicBox E)) := by
    simp only [constantTerm, constantTermIntegrand, map_mul, sigmaGL2_unipotentGL2]
  rw [hc, h]
  have h0 := hcusp (sigmaGL2 σ g)
  simp only [constantTerm, constantTermIntegrand] at h0
  rw [h0, smul_zero]

end Token

section CharacterInvariance

open NumberField.StandardAddChar NumberField.AdelicTrace

private theorem traceInfHom_sigmaInfinite (x : InfiniteAdeleRing E) :
    traceInfHom E (sigmaInfinite σ x) = traceInfHom E x := by
  have h : (fun y : InfiniteAdeleRing E => traceInfHom E (sigmaInfinite σ y)) = fun y => traceInfHom E y := by
    refine Continuous.ext_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap E)
      ((continuous_traceInfHom E).comp (continuous_sigmaInfinite σ)) (continuous_traceInfHom E) ?_
    rintro _ ⟨k, rfl⟩
    show traceInfHom E (sigmaInfinite σ (algebraMap E (InfiniteAdeleRing E) k))
      = traceInfHom E (algebraMap E (InfiniteAdeleRing E) k)
    rw [sigmaInfinite_algebraMap, traceInfHom_algebraMap, traceInfHom_algebraMap, Algebra.trace_eq_of_algEquiv σ k]
  exact congrFun h x

private abbrev smE : (Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E) → FiniteAdeleRing (𝓞 E) E :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite

private theorem smE_mem_integral (w : Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E) :
    smE w ∈ integralFiniteAdeles (𝓞 E) E := by
  intro v
  exact (w v).2

private theorem smE_add (w₁ w₂ : Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E) :
    smE (w₁ + w₂) = smE w₁ + smE w₂ :=
  RestrictedProduct.ext _ _ fun _ => rfl

private def sigmaInt (w : Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E)
    (z : HeightOneSpectrum (𝓞 E)) : z.adicCompletionIntegers E :=
  ⟨sigmaFin σ (smE w) z, sigmaFin_mem_integral σ (smE_mem_integral w) z⟩

private theorem smE_sigmaInt (w : Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E) :
    smE (sigmaInt σ w) = sigmaFin σ (smE w) :=
  RestrictedProduct.ext _ _ fun _ => rfl

private def sigmaIntHom : (Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E)
    →+ (Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E) :=
  AddMonoidHom.mk' (sigmaInt σ) fun w₁ w₂ => funext fun z => Subtype.ext (by
    show sigmaFin σ (smE (w₁ + w₂)) z = sigmaFin σ (smE w₁) z + sigmaFin σ (smE w₂) z
    rw [smE_add, map_add]
    rfl)

private theorem continuous_sigmaInt : Continuous (sigmaInt σ) :=
  continuous_pi fun z =>
    (((RestrictedProduct.continuous_eval z).comp
      ((sigmaFinAdele σ).continuous_toFun.comp RestrictedProduct.isEmbedding_structureMap.continuous))).subtype_mk _

private theorem smE_diag (a : 𝓞 E) :
    smE (diag E a) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E a) := by
  refine RestrictedProduct.ext _ _ fun v => ?_
  show ((algebraMap (𝓞 E) (v.adicCompletionIntegers E) a : v.adicCompletionIntegers E) : v.adicCompletion E)
    = algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E a) v
  rw [coe_algebraMap_adicCompletionIntegers, IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]
  exact IsScalarTower.algebraMap_apply (𝓞 E) E (v.adicCompletion E) a

private theorem sigmaInt_diag (a : 𝓞 E) : sigmaInt σ (diag E a) = diag E (galRestrict ℤ ℚ E (𝓞 E) σ a) := by
  have h : smE (sigmaInt σ (diag E a)) = smE (diag E (galRestrict ℤ ℚ E (𝓞 E) σ a)) := by
    rw [smE_sigmaInt, smE_diag, smE_diag, sigmaFin_algebraMap, algebraMap_galRestrict_apply]
  exact (RestrictedProduct.isEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))).injective h

private theorem traceInt_comp_sigmaInt : (traceInt E).comp (sigmaIntHom σ) = traceInt E := by
  refine eq_traceInt E ((continuous_traceInt E).comp (continuous_sigmaInt σ)) fun a => ?_
  show traceInt E (sigmaInt σ (diag E a)) = traceInt E (diag E a)
  rw [sigmaInt_diag, traceInt_diag, traceInt_diag, Algebra.trace_eq_of_algEquiv (galRestrict ℤ ℚ E (𝓞 E) σ) a]

private theorem traceInt_sigmaInt (w : Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E) :
    traceInt E (sigmaInt σ w) = traceInt E w :=
  congrArg (fun T => T w) (traceInt_comp_sigmaInt σ)

private theorem traceFinHom_sigmaFin (y : FiniteAdeleRing (𝓞 E) E) :
    traceFinHom E (sigmaFin σ y) = traceFinHom E y := by
  open NumberField.AdelicBox in
  obtain ⟨k, hk⟩ := exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 E) E y
  obtain ⟨w, hw⟩ : ∃ w : Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E,
      smE w = algebraMap E (FiniteAdeleRing (𝓞 E) E) k + y :=
    RestrictedProduct.exists_structureMap_eq_of_forall _ _ fun v => hk v
  have hy : y = smE w - algebraMap E (FiniteAdeleRing (𝓞 E) E) k := by rw [hw, add_sub_cancel_left]
  rw [hy]
  simp only [map_sub]
  rw [sigmaFin_algebraMap, ← smE_sigmaInt, traceFinHom_structureMap, traceFinHom_structureMap,
    traceFinHom_algebraMap, traceFinHom_algebraMap, traceInt_sigmaInt, Algebra.trace_eq_of_algEquiv σ k]

private theorem stdAddChar_sigmaAdele (u : AdeleRing (𝓞 E) E) :
    stdAddChar E (sigmaAdele σ u) = stdAddChar E u := by
  show psiQ ((adelicTraceData E).adelicTrace (sigmaAdele σ u)) = psiQ ((adelicTraceData E).adelicTrace u)
  congr 1
  exact Prod.ext (traceInfHom_sigmaInfinite σ u.1) (traceFinHom_sigmaFin σ u.2)

end CharacterInvariance

section ComponentFurniture

private theorem sigmaFin_apply_congr {x y : FiniteAdeleRing (𝓞 E) E} (z : HeightOneSpectrum (𝓞 E))
    (h : x ((show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E))
      = y ((show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E))) :
    sigmaFin σ x z = sigmaFin σ y z := by
  have h1 : IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E (Tw σ)
      (⟨show HeightOneSpectrum (𝓞 (Tw σ)) from z, rfl⟩ :
        IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 (Tw σ))
          ((show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E)))
      (x ((show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E)))
      = IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E (Tw σ)
      (⟨show HeightOneSpectrum (𝓞 (Tw σ)) from z, rfl⟩ :
        IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 (Tw σ))
          ((show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E)))
      (y ((show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E))) := by
    rw [h]
  show IsDedekindDomain.FiniteAdeleRing.mapSemialgHom (𝓞 E) E (Tw σ) (𝓞 (Tw σ)) x
      (show HeightOneSpectrum (𝓞 (Tw σ)) from z)
    = IsDedekindDomain.FiniteAdeleRing.mapSemialgHom (𝓞 E) E (Tw σ) (𝓞 (Tw σ)) y
      (show HeightOneSpectrum (𝓞 (Tw σ)) from z)
  rw [IsDedekindDomain.FiniteAdeleRing.mapSemialgHom_apply, IsDedekindDomain.FiniteAdeleRing.mapSemialgHom_apply]
  exact h1

private theorem sigmaFin_apply_eq_one {x : FiniteAdeleRing (𝓞 E) E} (z : HeightOneSpectrum (𝓞 E))
    (h : x ((show HeightOneSpectrum (𝓞 (Tw σ)) from z).under (𝓞 E)) = 1) : sigmaFin σ x z = 1 := by
  rw [sigmaFin_apply_congr σ (y := 1) z (by rw [h]; rfl), map_one]
  rfl

private theorem intEquiv_symm_eq : intEquiv σ.symm = (intEquiv σ).symm := by
  refine RingEquiv.ext fun a => (intEquiv σ).injective ?_
  rw [RingEquiv.apply_symm_apply]
  apply NumberField.RingOfIntegers.ext
  show algebraMap (𝓞 E) E (galRestrict ℤ ℚ E (𝓞 E) σ (galRestrict ℤ ℚ E (𝓞 E) σ.symm a)) = algebraMap (𝓞 E) E a
  rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply, AlgEquiv.apply_symm_apply]

end ComponentFurniture

section GeneratorTransport

private abbrev genIdele (v : HeightOneSpectrum (𝓞 E)) : FiniteAdeleRing (𝓞 E) E :=
  ((localUnit (𝓞 E) E v (uniformizerUnit E v) : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)

private theorem valued_sigmaFin_genIdele (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v (sigmaFin σ (genIdele v) (placeEquiv σ v)) = WithZero.exp (-1 : ℤ) := by
  rw [valued_sigmaFin, under_placeEquiv]
  show Valued.v (((localUnit (𝓞 E) E v (uniformizerUnit E v) : (FiniteAdeleRing (𝓞 E) E)ˣ) :
    FiniteAdeleRing (𝓞 E) E) v) = WithZero.exp (-1 : ℤ)
  rw [localUnit_apply_self]
  exact valued_uniformizerUnit E v

private theorem sigmaFin_genIdele_ne_zero (v : HeightOneSpectrum (𝓞 E)) :
    sigmaFin σ (genIdele v) (placeEquiv σ v) ≠ 0 :=
  (Valuation.ne_zero_iff Valued.v).mp (by rw [valued_sigmaFin_genIdele]; exact WithZero.exp_ne_zero)

private noncomputable def twUnit (v : HeightOneSpectrum (𝓞 E)) : ((placeEquiv σ v).adicCompletion E)ˣ :=
  Units.mk0 _ (sigmaFin_genIdele_ne_zero σ v)

private theorem valued_twUnit (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v (twUnit σ v : (placeEquiv σ v).adicCompletion E) = WithZero.exp (-1 : ℤ) :=
  valued_sigmaFin_genIdele σ v

private theorem map_localUnit_uniformizer (v : HeightOneSpectrum (𝓞 E)) :
    Units.map (sigmaFin σ).toMonoidHom (localUnit (𝓞 E) E v (uniformizerUnit E v))
      = localUnit (𝓞 E) E (placeEquiv σ v) (twUnit σ v) := by
  refine Units.ext (RestrictedProduct.ext _ _ fun w => ?_)
  show sigmaFin σ (genIdele v) w
    = ((localUnit (𝓞 E) E (placeEquiv σ v) (twUnit σ v) : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) w
  by_cases hw : w = placeEquiv σ v
  · subst hw
    rw [localUnit_apply_self]
    rfl
  · rw [localUnit_apply_of_ne (𝓞 E) E _ _ hw]
    refine sigmaFin_apply_eq_one σ w ?_
    have hne : (show HeightOneSpectrum (𝓞 (Tw σ)) from w).under (𝓞 E) ≠ v := fun h =>
      hw (by rw [← placeEquiv_under σ w, h])
    exact localUnit_apply_of_ne (𝓞 E) E v (uniformizerUnit E v) hne

private theorem sigmaGL2_diagOne (a : (AdeleRing (𝓞 E) E)ˣ) :
    sigmaGL2 σ (diagOne a) = diagOne (Units.map (sigmaAdele σ).toMonoidHom a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaGL2, diagOne_coe_apply]

private theorem map_sigmaAdele_map_finIncl (u : (FiniteAdeleRing (𝓞 E) E)ˣ) :
    Units.map (sigmaAdele σ).toMonoidHom (Units.map (finIncl (𝓞 E) E) u)
      = Units.map (finIncl (𝓞 E) E) (Units.map (sigmaFin σ).toMonoidHom u) :=
  Units.ext (Prod.ext (map_one (sigmaInfinite σ)) rfl)

private theorem sigmaGL2_heckeGen (v : HeightOneSpectrum (𝓞 E)) :
    sigmaGL2 σ (heckeGen (𝓞 E) E v) = heckeGenAt (𝓞 E) E (placeEquiv σ v) (twUnit σ v) := by
  show sigmaGL2 σ (diagOne (Units.map (finIncl (𝓞 E) E) (localUnit (𝓞 E) E v (uniformizerUnit E v))))
    = diagOne (Units.map (finIncl (𝓞 E) E) (localUnit (𝓞 E) E (placeEquiv σ v) (twUnit σ v)))
  rw [sigmaGL2_diagOne, map_sigmaAdele_map_finIncl, map_localUnit_uniformizer]

private theorem heckeGenAt_mem_finiteAdelicGL2Subgroup (v : HeightOneSpectrum (𝓞 E)) (t : (v.adicCompletion E)ˣ) :
    heckeGenAt (𝓞 E) E v t ∈ finiteAdelicGL2Subgroup E := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem heckeGen_inv_mul_sigmaGL2_heckeGen_mem (v : HeightOneSpectrum (𝓞 E)) (N : Ideal (𝓞 E)) :
    (heckeGen (𝓞 E) E (placeEquiv σ v))⁻¹ * sigmaGL2 σ (heckeGen (𝓞 E) E v)
      ∈ levelOne (𝓞 E) E N ⊓ finiteAdelicGL2Subgroup E := by
  rw [sigmaGL2_heckeGen, Subgroup.mem_inf]
  exact ⟨heckeGen_inv_mul_heckeGenAt_mem_levelOne (twUnit σ v) (valued_twUnit σ v) N,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (heckeGenAt_mem_finiteAdelicGL2Subgroup _ _))
      (heckeGenAt_mem_finiteAdelicGL2Subgroup _ _)⟩

private theorem doubleCoset_sigmaGL2_heckeGen (v : HeightOneSpectrum (𝓞 E)) (N : Ideal (𝓞 E)) :
    HeckePair.doubleCoset (levelOne (𝓞 E) E N ⊓ finiteAdelicGL2Subgroup E) (sigmaGL2 σ (heckeGen (𝓞 E) E v))
      = HeckePair.doubleCoset (levelOne (𝓞 E) E N ⊓ finiteAdelicGL2Subgroup E)
          (heckeGen (𝓞 E) E (placeEquiv σ v)) := by
  conv_lhs => rw [← mul_inv_cancel_left (heckeGen (𝓞 E) E (placeEquiv σ v)) (sigmaGL2 σ (heckeGen (𝓞 E) E v))]
  exact doubleCoset_mul_right _ _ (heckeGen_inv_mul_sigmaGL2_heckeGen_mem σ v N)

private theorem det_diagOne (a : (AdeleRing (𝓞 E) E)ˣ) : Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  ext
  simp [Matrix.det_fin_two, diagOne_coe_apply]

private theorem det_heckeGenAt (v : HeightOneSpectrum (𝓞 E)) (t : (v.adicCompletion E)ˣ) :
    Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 E) E v t) = Units.map (finIncl (𝓞 E) E) (localUnit (𝓞 E) E v t) :=
  det_diagOne _

end GeneratorTransport

section LevelFurniture

private theorem map_intEquiv_symm_eq_comap (N : Ideal (𝓞 E)) :
    N.map ((intEquiv σ).symm : 𝓞 E →+* 𝓞 E) = N.comap (intEquiv σ : 𝓞 E →+* 𝓞 E) :=
  (Ideal.comap_symm (intEquiv σ).symm).symm

private theorem sigmaGL2_mem_rowLevel_iff (N : Ideal (𝓞 E)) (g : AdelicGL2 (𝓞 E) E) :
    sigmaGL2 σ g ∈ levelOne (𝓞 E) E N ⊓ finiteAdelicGL2Subgroup E
      ↔ g ∈ levelOne (𝓞 E) E (N.comap (intEquiv σ : 𝓞 E →+* 𝓞 E)) ⊓ finiteAdelicGL2Subgroup E := by
  constructor
  · intro hg
    have h := sigmaGL2_mem_rowLevel σ.symm hg
    rwa [sigmaGL2_symm_sigmaGL2, intEquiv_symm_eq, map_intEquiv_symm_eq_comap] at h
  · intro hg
    have h := sigmaGL2_mem_rowLevel σ hg
    rwa [map_comap_intEquiv] at h

private theorem map_rowLevel_conjTable (Φ : HeckeEigensystem E ℂ) :
    (levelOne (𝓞 E) E (conjTable σ Φ).level ⊓ finiteAdelicGL2Subgroup E).map (sigmaGL2Equiv σ).toMonoidHom
      = levelOne (𝓞 E) E Φ.level ⊓ finiteAdelicGL2Subgroup E := by
  ext x
  rw [Subgroup.mem_map_equiv]
  show sigmaGL2 σ.symm x ∈ _ ↔ _
  conv_rhs => rw [← sigmaGL2_sigmaGL2_symm σ x]
  exact (sigmaGL2_mem_rowLevel_iff σ Φ.level (sigmaGL2 σ.symm x)).symm

end LevelFurniture

section CosetFurniture

variable {G : Type*} [Group G]

private theorem isHeckeCosetSystem_of_doubleCoset_eq {U : Subgroup G} {g g' : G} {ι : Type*} {reps : ι → G}
    (hgg : HeckePair.doubleCoset U g = HeckePair.doubleCoset U g')
    (h : HeckeIntegralSeam.IsHeckeCosetSystem U g' reps) : HeckeIntegralSeam.IsHeckeCosetSystem U g reps where
  mem_doubleCoset i := by rw [hgg]; exact h.mem_doubleCoset i
  covers x hx := h.covers x (by rw [← hgg]; exact hx)
  mk_injective := h.mk_injective

private theorem isHeckeCosetSystem_reindex {U : Subgroup G} {g : G} {ι κ : Type*} {reps : ι → G} (e : κ ≃ ι)
    (h : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) :
    HeckeIntegralSeam.IsHeckeCosetSystem U g (fun k => reps (e k)) where
  mem_doubleCoset k := h.mem_doubleCoset (e k)
  covers x hx := by
    obtain ⟨i, hi⟩ := h.covers x hx
    refine ⟨e.symm i, ?_⟩
    show (QuotientGroup.mk x : G ⧸ U) = QuotientGroup.mk (reps (e (e.symm i)))
    rw [e.apply_symm_apply]
    exact hi
  mk_injective k₁ k₂ hk := e.injective (h.mk_injective hk)

private theorem isHeckeCosetSystem_of_map (α : G ≃* G) {U : Subgroup G} {g : G} {ι : Type*} {reps : ι → G}
    (h : HeckeIntegralSeam.IsHeckeCosetSystem (U.map α.toMonoidHom) (α g) (fun i => α (reps i))) :
    HeckeIntegralSeam.IsHeckeCosetSystem U g reps where
  mem_doubleCoset i := (map_mem_doubleCoset_map_iff α U g (reps i)).mp (h.mem_doubleCoset i)
  covers x hx := by
    obtain ⟨i, hi⟩ := h.covers (α x) ((map_mem_doubleCoset_map_iff α U g x).mpr hx)
    refine ⟨i, ?_⟩
    have hi₁ : (QuotientGroup.mk (α x) : G ⧸ U.map α.toMonoidHom) = QuotientGroup.mk (α (reps i)) := hi
    rw [QuotientGroup.eq] at hi₁ ⊢
    have hi₂ : α.symm ((α x)⁻¹ * α (reps i)) ∈ U := (Subgroup.mem_map_equiv (f := α)).mp hi₁
    rwa [← map_inv, ← map_mul, MulEquiv.symm_apply_apply] at hi₂
  mk_injective i₁ i₂ hi := by
    apply h.mk_injective
    have hi₁ : (QuotientGroup.mk (reps i₁) : G ⧸ U) = QuotientGroup.mk (reps i₂) := hi
    show (QuotientGroup.mk (α (reps i₁)) : G ⧸ U.map α.toMonoidHom) = QuotientGroup.mk (α (reps i₂))
    rw [QuotientGroup.eq] at hi₁ ⊢
    rw [← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem _ hi₁

end CosetFurniture

section CentralUnits

private noncomputable def levelSupport (N : Ideal (𝓞 E)) (hN : N ≠ ⊥) : Finset (HeightOneSpectrum (𝓞 E)) :=
  (finite_setOf_idealBound_ne_one (R := 𝓞 E) hN).toFinset

private theorem idealBound_eq_one_of_not_mem_levelSupport {N : Ideal (𝓞 E)} (hN : N ≠ ⊥)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∉ levelSupport N hN) : idealBound (𝓞 E) N v = 1 := by
  by_contra h
  exact hv ((finite_setOf_idealBound_ne_one hN).mem_toFinset.mpr h)

private theorem localUnit_mem_integral (v : HeightOneSpectrum (𝓞 E)) {s : (v.adicCompletion E)ˣ}
    (hs : Valued.v (s : v.adicCompletion E) = 1) :
    ((localUnit (𝓞 E) E v s : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)
      ∈ integralFiniteAdeles (𝓞 E) E := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [localUnit_apply_self, HeightOneSpectrum.mem_adicCompletionIntegers, hs]
  · rw [localUnit_apply_of_ne (𝓞 E) E _ _ hw]
    exact one_mem _

private theorem localUnit_sub_one_mem_idealBall {N : Ideal (𝓞 E)} (hN : N ≠ ⊥) {v : HeightOneSpectrum (𝓞 E)}
    (hv : v ∉ levelSupport N hN) {s : (v.adicCompletion E)ˣ} (hs : Valued.v (s : v.adicCompletion E) = 1) :
    ((localUnit (𝓞 E) E v s : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) - 1 ∈ idealBall (𝓞 E) E N := by
  intro w
  rw [coe_sub_apply, coe_one_apply]
  by_cases hw : w = v
  · subst hw
    rw [localUnit_apply_self, idealBound_eq_one_of_not_mem_levelSupport hN hv]
    exact (Valuation.map_sub _ _ _).trans (le_of_eq (by rw [hs, map_one, max_self]))
  · rw [localUnit_apply_of_ne (𝓞 E) E _ _ hw, sub_self, map_zero]
    exact zero_le'

private theorem glFin_centralScalar_localUnit (v : HeightOneSpectrum (𝓞 E)) (s : (v.adicCompletion E)ˣ) :
    (glFin (𝓞 E) E (centralScalar (𝓞 E) E (Units.map (finIncl (𝓞 E) E) (localUnit (𝓞 E) E v s))) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 E) E))
      = Matrix.diagonal fun _ =>
          ((localUnit (𝓞 E) E v s : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem isLevelOneMatrix_centralScalar_localUnit {N : Ideal (𝓞 E)} (hN : N ≠ ⊥) {v : HeightOneSpectrum (𝓞 E)}
    (hv : v ∉ levelSupport N hN) {s : (v.adicCompletion E)ˣ} (hs : Valued.v (s : v.adicCompletion E) = 1) :
    IsLevelOneMatrix (𝓞 E) E N
      (glFin (𝓞 E) E (centralScalar (𝓞 E) E (Units.map (finIncl (𝓞 E) E) (localUnit (𝓞 E) E v s))) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 E) E)) := by
  rw [glFin_centralScalar_localUnit]
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      exact localUnit_mem_integral v hs
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact zero_mem_integralFiniteAdeles
  · rw [Matrix.diagonal_apply_ne _ (by decide)]
    exact zero_mem_idealBall N
  · rw [Matrix.diagonal_apply_eq]
    exact localUnit_sub_one_mem_idealBall hN hv hs

private theorem centralScalar_localUnit_mem_rowLevel {N : Ideal (𝓞 E)} (hN : N ≠ ⊥) {v : HeightOneSpectrum (𝓞 E)}
    (hv : v ∉ levelSupport N hN) {s : (v.adicCompletion E)ˣ} (hs : Valued.v (s : v.adicCompletion E) = 1) :
    centralScalar (𝓞 E) E (Units.map (finIncl (𝓞 E) E) (localUnit (𝓞 E) E v s))
      ∈ levelOne (𝓞 E) E N ⊓ finiteAdelicGL2Subgroup E := by
  rw [Subgroup.mem_inf]
  constructor
  · have hsi : Valued.v ((s⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hs, inv_one]
    refine ⟨isLevelOneMatrix_centralScalar_localUnit hN hv hs, ?_⟩
    rw [← map_inv, ← map_inv, ← map_inv, ← map_inv]
    exact isLevelOneMatrix_centralScalar_localUnit hN hv hsi
  · rw [mem_finiteAdelicGL2Subgroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

private theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 E) E)ˣ) (h : AdelicGL2 (𝓞 E) E) :
    centralScalar (𝓞 E) E z * h = h * centralScalar (𝓞 E) E z := by
  ext i j
  simp [centralScalar, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

end CentralUnits

section RealizationTransport

open NumberField.StandardAddChar

private abbrev rowPins (D : Set (AdelicGL2 (𝓞 E) E)) : CarrierPins E :=
  productionPinsOf E D (fun N => levelOne (𝓞 E) E N ⊓ finiteAdelicGL2Subgroup E) (fun v => heckeGen (𝓞 E) E v)
    (AdelicBox.adelicBox E)

private theorem det_heckeGen (v : HeightOneSpectrum (𝓞 E)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 E) E v)
      = Units.map (finIncl (𝓞 E) E) (localUnit (𝓞 E) E v (uniformizerUnit E v)) :=
  det_diagOne _

private theorem absNorm_placeEquiv (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (placeEquiv σ w).asIdeal = Ideal.absNorm w.asIdeal :=
  absNorm_comap_ringEquiv (intEquiv σ).symm w.asIdeal

private theorem valued_correction (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (((uniformizerUnit E (placeEquiv σ w))⁻¹ * twUnit σ w : ((placeEquiv σ w).adicCompletion E)ˣ) :
      (placeEquiv σ w).adicCompletion E) = 1 := by
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, valued_uniformizerUnit, valued_twUnit,
    inv_mul_cancel₀ WithZero.exp_ne_zero]

open scoped Classical in

private noncomputable def conjRealization {D : Set (AdelicGL2 (𝓞 E) E)} {Ψ : HeckeEigensystem E ℂ}
    (R : SmoothCuspRealizationAt E (rowPins D) Ψ) : SmoothCuspRealizationAt E (rowPins ∅) (conjTable σ Ψ) where
  toFun := fun g => R.toFun (sigmaGL2 σ g)
  exists_ne_zero := exists_comp_sigmaGL2_ne_zero σ R.exists_ne_zero
  centralChar := conjCentralChar σ R.centralChar
  smoothCusp := by
    obtain ⟨⟨hlsxi, -⟩, hcusp⟩ := R.smoothCusp.1
    refine ⟨⟨?_, isCuspidalFn_comp_sigmaGL2 σ hlsxi.left_invariant hcusp⟩, isKfSmooth_comp_sigmaGL2 σ R.smoothCusp.2⟩
    letI := (rowPins (E := E) ∅).mS
    letI : MeasureTheory.MeasureSpace (AdelicGL2 (𝓞 E) E) := ⟨(rowPins (E := E) ∅).μ⟩
    exact ⟨isLsXiFunction_comp_sigmaGL2 σ R.centralChar hlsxi, memLp_restrict_empty _ _⟩
  level_invariant := fun g u hu => by
    show R.toFun (sigmaGL2 σ (g * u)) = R.toFun (sigmaGL2 σ g)
    rw [map_mul]
    exact R.level_invariant _ _ (sigmaGL2_mem_rowLevel_conjTable σ Ψ hu)
  exceptionalSet :=
    (R.exceptionalSet ∪ levelSupport Ψ.level Ψ.level_ne_bot).map (placeEquiv σ).symm.toEmbedding
  hecke_eigen := fun w hw => by
    have hw' : placeEquiv σ w ∉ R.exceptionalSet ∪ levelSupport Ψ.level Ψ.level_ne_bot :=
      fun h => hw (Finset.mem_map_equiv.mpr h)
    obtain ⟨reps, hsys, hsum⟩ := R.hecke_eigen (placeEquiv σ w) fun h => hw' (Finset.mem_union_left _ h)
    have e : Fin (Ideal.absNorm w.asIdeal + 1) ≃ Fin (Ideal.absNorm (placeEquiv σ w).asIdeal + 1) :=
      finCongr (by rw [absNorm_placeEquiv])
    refine ⟨fun i => sigmaGL2 σ.symm (reps (e i)), ?_, ?_⟩
    · have hsys' : HeckeIntegralSeam.IsHeckeCosetSystem
          (levelOne (𝓞 E) E Ψ.level ⊓ finiteAdelicGL2Subgroup E) (sigmaGL2 σ (heckeGen (𝓞 E) E w))
          (fun i => reps (e i)) :=
        isHeckeCosetSystem_of_doubleCoset_eq (doubleCoset_sigmaGL2_heckeGen σ w Ψ.level)
          (isHeckeCosetSystem_reindex e hsys)
      have hreps : (fun i => sigmaGL2Equiv σ (sigmaGL2 σ.symm (reps (e i)))) = fun i => reps (e i) :=
        funext fun i => sigmaGL2_sigmaGL2_symm σ _
      have hsys'' : HeckeIntegralSeam.IsHeckeCosetSystem
          ((levelOne (𝓞 E) E (conjTable σ Ψ).level ⊓ finiteAdelicGL2Subgroup E).map (sigmaGL2Equiv σ).toMonoidHom)
          (sigmaGL2Equiv σ (heckeGen (𝓞 E) E w)) (fun i => sigmaGL2Equiv σ (sigmaGL2 σ.symm (reps (e i)))) := by
        rw [map_rowLevel_conjTable, hreps]
        exact hsys'
      exact isHeckeCosetSystem_of_map (sigmaGL2Equiv σ) hsys''
    · intro g
      show ∑ i, R.toFun (sigmaGL2 σ (g * sigmaGL2 σ.symm (reps (e i))))
        = Ψ.a (placeEquiv σ w) * R.toFun (sigmaGL2 σ g)
      simp only [map_mul, sigmaGL2_sigmaGL2_symm]
      exact (Fintype.sum_equiv e _ (fun j => R.toFun (sigmaGL2 σ g * reps j)) fun _ => rfl).trans
        (hsum (sigmaGL2 σ g))
  central_eigen := fun w hw g => by
    have hw' : placeEquiv σ w ∉ R.exceptionalSet ∪ levelSupport Ψ.level Ψ.level_ne_bot :=
      fun h => hw (Finset.mem_map_equiv.mpr h)
    have hce : ∀ x : AdelicGL2 (𝓞 E) E,
        R.toFun (centralScalar (𝓞 E) E (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 E) E (placeEquiv σ w))) * x)
          = Ψ.b (placeEquiv σ w) * R.toFun x :=
      R.central_eigen (placeEquiv σ w) fun h => hw' (Finset.mem_union_left _ h)
    have hmem : centralScalar (𝓞 E) E (Units.map (finIncl (𝓞 E) E) (localUnit (𝓞 E) E (placeEquiv σ w)
          ((uniformizerUnit E (placeEquiv σ w))⁻¹ * twUnit σ w)))
        ∈ levelOne (𝓞 E) E Ψ.level ⊓ finiteAdelicGL2Subgroup E :=
      centralScalar_localUnit_mem_rowLevel Ψ.level_ne_bot (fun h => hw' (Finset.mem_union_right _ h))
        (valued_correction σ w)
    have htw : twUnit σ w
        = uniformizerUnit E (placeEquiv σ w) * ((uniformizerUnit E (placeEquiv σ w))⁻¹ * twUnit σ w) :=
      (mul_inv_cancel_left _ _).symm
    show R.toFun (sigmaGL2 σ (centralScalar (𝓞 E) E (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 E) E w)) * g))
      = Ψ.b (placeEquiv σ w) * R.toFun (sigmaGL2 σ g)
    rw [map_mul, sigmaGL2_centralScalar, det_heckeGen, map_sigmaAdele_map_finIncl, map_localUnit_uniformizer, htw,
      map_mul, map_mul, map_mul, mul_assoc, ← det_heckeGen, hce, centralScalar_mul_comm,
      R.level_invariant _ _ hmem]

end RealizationTransport

section TokenTransport

open NumberField.StandardAddChar MeasureTheory

private theorem whittaker_integrand_comp (φ : AdelicGL2 (𝓞 E) E → ℂ) (α : E) (g : AdelicGL2 (𝓞 E) E)
    (x : AdeleRing (𝓞 E) E) :
    φ (sigmaGL2 σ (unipotentGL2 x * g)) * stdAddChar E (-(algebraMap E (AdeleRing (𝓞 E) E) α * x))
      = φ (unipotentGL2 (sigmaAdele σ x) * sigmaGL2 σ g)
          * stdAddChar E (-(algebraMap E (AdeleRing (𝓞 E) E) (σ α) * sigmaAdele σ x)) := by
  rw [map_mul, sigmaGL2_unipotentGL2, ← stdAddChar_sigmaAdele σ (-(algebraMap E (AdeleRing (𝓞 E) E) α * x)),
    map_neg, map_mul, sigmaAdele_algebraMap]

private theorem whittaker_integrand_vadd {φ : AdelicGL2 (𝓞 E) E → ℂ}
    (hφ : ∀ (γ : GL (Fin 2) E) (g : AdelicGL2 (𝓞 E) E), φ (globalPoints (𝓞 E) E γ * g) = φ g)
    (α : E) (h : AdelicGL2 (𝓞 E) E) (p : AdeleRing.principalSubgroup (𝓞 E) E) (x : AdeleRing (𝓞 E) E) :
    φ (unipotentGL2 (p +ᵥ x) * h) * stdAddChar E (-(algebraMap E (AdeleRing (𝓞 E) E) α * (p +ᵥ x)))
      = φ (unipotentGL2 x * h) * stdAddChar E (-(algebraMap E (AdeleRing (𝓞 E) E) α * x)) := by
  rw [unipotent_integrand_vadd hφ h p x]
  congr 1
  obtain ⟨_, k, rfl⟩ := p
  show stdAddChar E (-(algebraMap E (AdeleRing (𝓞 E) E) α * (algebraMap E (AdeleRing (𝓞 E) E) k + x)))
    = stdAddChar E (-(algebraMap E (AdeleRing (𝓞 E) E) α * x))
  have h1 : stdAddChar E (algebraMap E (AdeleRing (𝓞 E) E) (-(α * k))) = 1 :=
    (adelicTraceData E).psiK_algebraMap _
  rw [mul_add, neg_add, ← map_mul, ← map_neg, AddChar.map_add_eq_mul, h1, one_mul]

private theorem isBoundedGenuineFn_comp {D : Set (AdelicGL2 (𝓞 E) E)} {φ : AdelicGL2 (𝓞 E) E → ℂ}
    (hinv : ∀ (γ : GL (Fin 2) E) (g : AdelicGL2 (𝓞 E) E), φ (globalPoints (𝓞 E) E γ * g) = φ g)
    (h : IsBoundedGenuineFn E (rowPins D) (stdAddChar E) φ) :
    IsBoundedGenuineFn E (rowPins ∅) (stdAddChar E) (fun g => φ (sigmaGL2 σ g)) := by
  obtain ⟨hcont, hsiegel, hint, hsum⟩ := h
  refine ⟨continuous_comp_sigmaGL2 σ hcont, isBoundedOnSiegelWindows_comp_sigmaGL2 σ hsiegel, fun α g => ?_,
    fun g => ?_⟩
  · show Integrable
        (fun x => φ (sigmaGL2 σ (unipotentGL2 x * g)) * stdAddChar E (-(algebraMap E (AdeleRing (𝓞 E) E) α * x)))
        (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 E) E) (AdelicBox.adelicBox E))
    simp_rw [whittaker_integrand_comp σ φ α g]
    exact (integrable_cond_comp_sigmaAdele_iff σ
      (fun y => φ (unipotentGL2 y * sigmaGL2 σ g) * stdAddChar E (-(algebraMap E (AdeleRing (𝓞 E) E) (σ α) * y)))
      (whittaker_integrand_vadd hinv (σ α) (sigmaGL2 σ g))).mpr (hint (σ α) (sigmaGL2 σ g))
  · have hW : ∀ α : E, whittakerCoefficient E (rowPins ∅) (stdAddChar E) (fun g => φ (sigmaGL2 σ g)) α g
        = sigmaFactor σ • whittakerCoefficient E (rowPins D) (stdAddChar E) φ (σ α) (sigmaGL2 σ g) := by
      intro α
      show (∫ x, φ (sigmaGL2 σ (unipotentGL2 x * g)) * stdAddChar E (-(algebraMap E (AdeleRing (𝓞 E) E) α * x))
          ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 E) E) (AdelicBox.adelicBox E)))
        = sigmaFactor σ • whittakerCoefficient E (rowPins D) (stdAddChar E) φ (σ α) (sigmaGL2 σ g)
      simp_rw [whittaker_integrand_comp σ φ α g]
      exact integral_cond_comp_sigmaAdele σ
        (fun y => φ (unipotentGL2 y * sigmaGL2 σ g) * stdAddChar E (-(algebraMap E (AdeleRing (𝓞 E) E) (σ α) * y)))
        (whittaker_integrand_vadd hinv (σ α) (sigmaGL2 σ g))
    show Summable fun α : E => whittakerCoefficient E (rowPins ∅) (stdAddChar E) (fun g => φ (sigmaGL2 σ g)) α g
    simp_rw [hW, NNReal.smul_def, Complex.real_smul]
    exact Summable.mul_left _ (σ.toEquiv.summable_iff.mpr (hsum (sigmaGL2 σ g)))

end TokenTransport

end GaloisConjugationTransport
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArithBoundedGenuineCuspRealizable_eq_comap_galRestrict.GaloisConjugationTransport"

open NumberField.AdelicBox in
theorem solution
    (K : Type) [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (Φ : HeckeEigensystem K ℂ)
    (hΦ : IsArithBoundedGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (StandardAddChar.stdAddChar K) Φ) :
    ∃ Φ' : HeckeEigensystem K ℂ,
      IsArithBoundedGenuineCuspRealizable K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (StandardAddChar.stdAddChar K) Φ' ∧
      ∀ v w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        w.asIdeal = v.asIdeal.comap (galRestrict ℤ ℚ K (𝓞 K) σ) →
          Φ'.a w = Φ.a v ∧ Φ'.b w = Φ.b v := by
  have _ := hd
  obtain ⟨R, hR⟩ := hΦ
  have hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), R.toFun (globalPoints (𝓞 K) K γ * g) = R.toFun g := by
    obtain ⟨⟨h, -⟩, -⟩ := R.smoothCusp.1
    exact h.left_invariant
  refine ⟨GaloisConjugationTransport.conjTable σ Φ, ?_, GaloisConjugationTransport.conjTable_eq_of_comap σ Φ⟩
  refine AutomorphicForm.isArithBoundedGenuineCuspRealizable_of_isArithBoundedGenuineCuspRealizable_of_pos_of_pos
    K ∅ _ _ _ _ ?_ c u d₁ d₂ T hc hd₁
  show IsBoundedGenuineCuspRealizable K _ _ (GaloisConjugationTransport.conjTable σ Φ).toRawCentral
  rw [← GaloisConjugationTransport.conjTable_toRawCentral]
  exact ⟨GaloisConjugationTransport.conjRealization σ R, GaloisConjugationTransport.isBoundedGenuineFn_comp σ hinv hR⟩

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArithBoundedGenuineCuspRealizable_eq_comap_galRestrict.GaloisConjugationTransport"

end S_AutomorphicForm_exists_isArithBoundedGenuineCuspRealizable_eq_comap_galRestrict
end P2MW
export P2MW.S_AutomorphicForm_exists_isArithBoundedGenuineCuspRealizable_eq_comap_galRestrict (solution)
