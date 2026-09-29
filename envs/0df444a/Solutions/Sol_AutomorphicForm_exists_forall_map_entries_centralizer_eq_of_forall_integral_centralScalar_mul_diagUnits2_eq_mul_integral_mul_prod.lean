-- Prove2me | solution 1 for AutomorphicForm.exists_forall_map_entries_centralizer_eq_of_forall_integral_centralScalar_mul_diagUnits2_eq_mul_integral_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ad44b91a-f805-5bd0-9be4-5570dfaba715

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Theorems.Thm_AutomorphicForm_glArch_centralScalar_mul_diagUnits2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_map_entries_centralizer_eq_of_forall_integral_centralScalar_mul_diagUnits2_eq_mul_integral_mul_prod

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace ArchTorusPin

open NumberField

variable (K : Type) [Field K] [NumberField K]

def box (n : ℕ) : Set (InfiniteAdeleRing K) :=
  {x | ∀ w : InfinitePlace K, ((n : ℝ) + 1)⁻¹ ≤ ‖x w‖ ∧ ‖x w‖ ≤ (n : ℝ) + 1}

theorem mem_box {n : ℕ} {x : InfiniteAdeleRing K} :
    x ∈ box K n ↔ ∀ w : InfinitePlace K, ((n : ℝ) + 1)⁻¹ ≤ ‖x w‖ ∧ ‖x w‖ ≤ (n : ℝ) + 1 := Iff.rfl

theorem isCompact_box (n : ℕ) : IsCompact (box K n) := by
  have hset : box K n = Set.univ.pi fun w : InfinitePlace K =>
      {y : w.Completion | ((n : ℝ) + 1)⁻¹ ≤ ‖y‖ ∧ ‖y‖ ≤ (n : ℝ) + 1} := by
    ext x
    exact ⟨fun h w _ => h w, fun h w => h w (Set.mem_univ w)⟩
  rw [hset]
  refine isCompact_univ_pi fun w => ?_
  haveI := AutomorphicForm.WindowedSiegel.properSpace_completion (F := K) w
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : w.Completion) ((n : ℝ) + 1)) ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  · intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hy.2

theorem isClosed_box (n : ℕ) : IsClosed (box K n) := (isCompact_box K n).isClosed

theorem box_mono {m n : ℕ} (h : m ≤ n) : box K m ⊆ box K n := by
  intro x hx w
  obtain ⟨h1, h2⟩ := hx w
  have hmn : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    linarith
  refine ⟨le_trans ?_ h1, h2.trans hmn⟩
  exact inv_anti₀ (by positivity) hmn

theorem apply_ne_zero (c : (InfiniteAdeleRing K)ˣ) (w : InfinitePlace K) : (c : InfiniteAdeleRing K) w ≠ 0 := by
  have hu : IsUnit ((c : InfiniteAdeleRing K) w) :=
    (Pi.isUnit_iff.1 (show IsUnit (c : InfiniteAdeleRing K) from Units.isUnit c)) w
  exact hu.ne_zero

theorem exists_mem_box (a b : (InfiniteAdeleRing K)ˣ) :
    ∃ n : ℕ, (a : InfiniteAdeleRing K) ∈ box K n ∧ (b : InfiniteAdeleRing K) ∈ box K n := by
  set f : InfinitePlace K → ℝ := fun w => ‖(a : InfiniteAdeleRing K) w‖ + ‖(a : InfiniteAdeleRing K) w‖⁻¹ +
      ‖(b : InfiniteAdeleRing K) w‖ + ‖(b : InfiniteAdeleRing K) w‖⁻¹ with hf
  obtain ⟨n, hn⟩ := exists_nat_ge (∑ w : InfinitePlace K, f w)
  have hterm : ∀ w : InfinitePlace K, f w ≤ (n : ℝ) + 1 := by
    intro w
    refine le_trans ?_ (hn.trans (by linarith))
    exact Finset.single_le_sum (f := f) (fun w _ => by rw [hf]; positivity) (Finset.mem_univ w)
  refine ⟨n, fun w => ?_, fun w => ?_⟩
  · have ha := norm_pos_iff.2 (apply_ne_zero K a w)
    have h := hterm w
    simp only [hf] at h
    have hbi : 0 ≤ ‖(b : InfiniteAdeleRing K) w‖⁻¹ := by positivity
    have hb := norm_nonneg ((b : InfiniteAdeleRing K) w)
    have hai := inv_nonneg.2 ha.le
    constructor
    · rw [inv_le_comm₀ (by positivity) ha]; linarith
    · linarith
  · have hb := norm_pos_iff.2 (apply_ne_zero K b w)
    have h := hterm w
    simp only [hf] at h
    have hai : 0 ≤ ‖(a : InfiniteAdeleRing K) w‖⁻¹ := by positivity
    have ha := norm_nonneg ((a : InfiniteAdeleRing K) w)
    have hbi := inv_nonneg.2 hb.le
    constructor
    · rw [inv_le_comm₀ (by positivity) hb]; linarith
    · linarith

theorem mem_box_of_mul_eq_one {n : ℕ} {x y : InfiniteAdeleRing K} (hx : x ∈ box K n)
    (hxy : x * y = 1) : y ∈ box K n := by
  intro w
  obtain ⟨h1, h2⟩ := hx w
  have hw : x w * y w = 1 := by
    have := congrFun hxy w
    exact this
  have hn : ‖x w‖ * ‖y w‖ = 1 := by rw [← norm_mul, hw, norm_one]
  have hxpos : 0 < ‖x w‖ := lt_of_lt_of_le (by positivity) h1
  have hy : ‖y w‖ = ‖x w‖⁻¹ := eq_inv_of_mul_eq_one_right hn
  rw [hy]
  constructor
  · exact inv_anti₀ hxpos h2
  · have := inv_anti₀ (by positivity) h1
    rwa [inv_inv] at this

variable {K}

theorem isCompact_preimage_box (γ : GL (Fin 2) (InfiniteAdeleRing K))
    (hγ : ∀ g : GL (Fin 2) (InfiniteAdeleRing K), g ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) →
      ((g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0 ∧
      ((g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0)
    (n : ℕ) :
    IsCompact ((fun x : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
        ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
          ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
          InfiniteAdeleRing K × InfiniteAdeleRing K)) ⁻¹' (box K n ×ˢ box K n)) := by

  set ent : GL (Fin 2) (InfiniteAdeleRing K) → InfiniteAdeleRing K × InfiniteAdeleRing K := fun g =>
    (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0), ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1))
    with hent
  have hent_cont : Continuous ent :=
    (Units.continuous_val.matrix_elem 0 0).prodMk (Units.continuous_val.matrix_elem 1 1)
  rw [Subtype.isCompact_iff]
  have hA : Subtype.val '' ((fun x : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
        ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
          ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
          InfiniteAdeleRing K × InfiniteAdeleRing K)) ⁻¹' (box K n ×ˢ box K n)) =
      {g : GL (Fin 2) (InfiniteAdeleRing K) | γ * g = g * γ} ∩ ent ⁻¹' (box K n ×ˢ box K n) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(Subgroup.mem_centralizer_iff.1 x.2) γ (Set.mem_singleton γ), hx⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨g, Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact h1⟩, h2, rfl⟩
  rw [hA]

  set D : Set (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    {M | M 0 0 ∈ box K n ∧ M 1 1 ∈ box K n ∧ M 0 1 = 0 ∧ M 1 0 = 0} with hD
  have hDc : IsCompact D := by
    have hP : IsCompact (Set.univ.pi fun i : Fin 2 => Set.univ.pi fun j : Fin 2 =>
        (if i = j then box K n else {0} : Set (InfiniteAdeleRing K))) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j => by
        split_ifs
        · exact isCompact_box K n
        · exact isCompact_singleton
    refine IsCompact.of_isClosed_subset hP ?_ ?_
    · rw [hD]
      refine (((isClosed_box K n).preimage (continuous_id.matrix_elem 0 0)).inter
        (((isClosed_box K n).preimage (continuous_id.matrix_elem 1 1)).inter
          ((isClosed_singleton.preimage (continuous_id.matrix_elem 0 1)).inter
            (isClosed_singleton.preimage (continuous_id.matrix_elem 1 0)))))
    · intro M hM
      rw [hD] at hM
      obtain ⟨h00, h11, h01, h10⟩ := hM
      intro i _ j _
      fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10]
  have hDop : IsCompact (MulOpposite.unop ⁻¹' D : Set (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))ᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hDc
  have hP : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) ⁻¹'
      (D ×ˢ (MulOpposite.unop ⁻¹' D))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hDc.prod hDop)
  refine IsCompact.of_isClosed_subset hP ?_ ?_
  · exact (isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)).inter
      (((isClosed_box K n).prod (isClosed_box K n)).preimage hent_cont)
  · rintro g ⟨hc, hb⟩
    have hb' : ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0) ∈ box K n ∧
        ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) ∈ box K n := by
      simpa [hent, Set.mem_prod] using hb
    have hmem : ∀ g' : GL (Fin 2) (InfiniteAdeleRing K), γ * g' = g' * γ →
        g' ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) :=
      fun g' h => Subgroup.mem_centralizer_iff.2 fun h' hh => by rw [Set.mem_singleton_iff.1 hh]; exact h
    have hoff := hγ g (hmem g hc)
    have hc' : γ * g⁻¹ = g⁻¹ * γ := (Commute.inv_right hc : Commute γ g⁻¹)
    have hoff' := hγ g⁻¹ (hmem g⁻¹ hc')
    have hgi : ((g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) *
        ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e00 := congrFun (congrFun hgi 0) 0
    have e11 := congrFun (congrFun hgi 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, hoff.1, hoff.2, zero_mul, add_zero,
      zero_add] at e00 e11
    show Units.embedProduct _ g ∈ D ×ˢ (MulOpposite.unop ⁻¹' D)
    rw [Units.embedProduct_apply, Set.mem_prod, Set.mem_preimage, MulOpposite.unop_op, hD]
    exact ⟨⟨hb'.1, hb'.2, hoff.1, hoff.2⟩,
      ⟨mem_box_of_mul_eq_one K hb'.1 e00, mem_box_of_mul_eq_one K hb'.2 e11, hoff'.1, hoff'.2⟩⟩

end ArchTorusPin

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (cτK : ℝ) (hcτK : 0 < cτK)
    (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure)
    (hτGc : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA u z))
    (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v))
    (hτF1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        (u : K) ≠ 1 →
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA u z) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF u z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v))
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)] :
    ∃ τ₀ : Measure (InfiniteAdeleRing K × InfiniteAdeleRing K), ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      (u : K) ≠ 1 →
        Measure.map
          (fun x : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
              ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
              InfiniteAdeleRing K × InfiniteAdeleRing K))
          (τA u z) = τ₀ := by
  classical

  have hu₀ : ((-1 : Kˣ) : K) ≠ 1 := by
    rw [Units.val_neg, Units.val_one]
    norm_num
  refine ⟨Measure.map (fun x : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (1 : (AdeleRing (𝓞 K) K)ˣ) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (-1 : Kˣ)) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
              ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
              InfiniteAdeleRing K × InfiniteAdeleRing K)) (τA (-1) 1), fun u z hu => ?_⟩

  let Wt : (InfiniteAdeleRing K × InfiniteAdeleRing K → ℂ) → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ := fun F g =>
    if (∀ v : HeightOneSpectrum (𝓞 K), AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
        AutomorphicForm.localIntegralSet K v)
    then F ((((AdelicLevel.glArch (𝓞 K) K g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
            ((AdelicLevel.glArch (𝓞 K) K g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1))
    else 0

  let Λ : (InfiniteAdeleRing K × InfiniteAdeleRing K → ℂ) → ℂ := fun F =>
    ((cT⁻¹ * cτK : ℝ) : ℂ) * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, Wt F (diagUnits2 p.1 p.2) ∂(νZK.prod νZK)

  have hI : ∀ (u' : Kˣ) (z' : (AdeleRing (𝓞 K) K)ˣ), ((u' : Kˣ) : K) ≠ 1 → ∀ F : InfiniteAdeleRing K × InfiniteAdeleRing K → ℂ, Measurable F →
      ∫ x,
          F (((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
              ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) ∂(τA u' z') = Λ F := by
    intro u' z' hu' F hF

    haveI : BorelSpace (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
    have hme : Measurable (fun x : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
        ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
          ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) : InfiniteAdeleRing K × InfiniteAdeleRing K)) :=
      (((Units.continuous_val.matrix_elem 0 0).comp continuous_subtype_val).measurable).prodMk
        (((Units.continuous_val.matrix_elem 1 1).comp continuous_subtype_val).measurable)
    have hmeas : AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1))]
        (fun t : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
          (fun g : GL (Fin 2) (InfiniteAdeleRing K) => F (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0), ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1))) t)
        (τA u' z') :=
      (hF.comp hme).aestronglyMeasurable
    have hfac := hT u' z' ∅ (Wt F)
      (fun g : GL (Fin 2) (InfiniteAdeleRing K) => F (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0), ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1)))
      (fun _ _ => 0) hu' hmeas (fun v hv => absurd hv (Finset.notMem_empty v))
      (fun t ht => by
        simp only [Finset.prod_empty, mul_one]
        exact if_pos fun v => ht v (Finset.notMem_empty v))
      (fun t ht => by
        obtain ⟨v, -, hv⟩ := ht
        exact if_neg fun h => hv (h v))
    have hcpl := hτGc u' z' hu' (Wt F)
    rw [hcpl, Finset.prod_empty, mul_one] at hfac

    have hcT0 : ((cT : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcT.ne'
    show _ = ((cT⁻¹ * cτK : ℝ) : ℂ) * _
    rw [Complex.ofReal_mul, Complex.ofReal_inv, mul_assoc, hfac, ← mul_assoc, inv_mul_cancel₀ hcT0, one_mul]

  have hme : ∀ (u' : Kˣ) (z' : (AdeleRing (𝓞 K) K)ˣ), @Measurable _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1))) _
      (fun x : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
              ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
              InfiniteAdeleRing K × InfiniteAdeleRing K)) := by
    intro u' z'
    haveI : BorelSpace (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
    exact (((Units.continuous_val.matrix_elem 0 0).comp continuous_subtype_val).measurable).prodMk
      (((Units.continuous_val.matrix_elem 1 1).comp continuous_subtype_val).measurable)
  have hreal : ∀ (u' : Kˣ) (z' : (AdeleRing (𝓞 K) K)ˣ), ((u' : Kˣ) : K) ≠ 1 → ∀ S : Set (InfiniteAdeleRing K × InfiniteAdeleRing K), MeasurableSet S →
      ((Measure.map (fun x : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
              ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
              InfiniteAdeleRing K × InfiniteAdeleRing K)) (τA u' z')) S).toReal = (Λ (S.indicator fun _ => (1 : ℂ))).re := by
    intro u' z' hu' S hS
    rw [Measure.map_apply (hme u' z') hS]
    have h := hI u' z' hu' (S.indicator fun _ => (1 : ℂ)) (measurable_const.indicator hS)
    have h1 : ∫ x, (((fun x : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
              ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
              InfiniteAdeleRing K × InfiniteAdeleRing K))) ⁻¹' S).indicator (fun _ => (1 : ℂ)) x ∂(τA u' z') =
        Λ (S.indicator fun _ => (1 : ℂ)) := h
    rw [integral_indicator_const (1 : ℂ) ((hme u' z') hS)] at h1
    have h2 := congrArg Complex.re h1
    rw [Complex.real_smul, mul_one, Complex.ofReal_re] at h2
    exact h2

  have hoff : ∀ (u' : Kˣ) (z' : (AdeleRing (𝓞 K) K)ˣ), ((u' : Kˣ) : K) ≠ 1 →
      ∀ g : GL (Fin 2) (InfiniteAdeleRing K), g ∈ Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) →
        ((g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0 ∧
        ((g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0 := by
    intro u' z' hu' g hg

    have hcl : AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) z') *
          diagUnits2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u'))
            (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) 1) :=
      AutomorphicForm.glArch_centralScalar_mul_diagUnits2 K z' (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1
    rw [map_one] at hcl
    set zA : (InfiniteAdeleRing K)ˣ := Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) z' with hzA
    set uA : (InfiniteAdeleRing K)ˣ := Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') with huA

    have huw : ∀ w : InfinitePlace K, ((uA : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w = algebraMap K w.Completion ((u' : Kˣ) : K) := by
      intro w
      first
        | rfl
        | simp [huA, Units.coe_map, MonoidHom.coe_coe]
    have hunit : IsUnit (((uA : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) - 1) := by
      rw [show IsUnit (((uA : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) - 1) ↔ ∀ w : InfinitePlace K, IsUnit ((((uA : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) - 1) w)
        from Pi.isUnit_iff]
      intro w
      refine isUnit_iff_ne_zero.2 ?_
      show ((uA : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w - 1 ≠ 0
      rw [huw]
      intro h
      exact hu' ((algebraMap K w.Completion).injective ((sub_eq_zero.1 h).trans (map_one _).symm))
    rw [Subgroup.mem_centralizer_iff] at hg
    have hcomm := hg _ (Set.mem_singleton _)
    rw [hcl] at hcomm
    have hM := congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing K) => ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) hcomm
    simp only [Units.val_mul] at hM
    have e01 := congrFun (congrFun hM 0) 1
    have e10 := congrFun (congrFun hM 1) 0
    simp [Matrix.GeneralLinearGroup.scalar, diagUnits2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] at e01 e10

    have hz : IsUnit ((zA : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) := Units.isUnit _
    constructor
    · have : (((zA : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * (((uA : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) - 1)) *
          ((g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0 := by
        linear_combination e01
      exact ((hz.mul hunit).mul_right_eq_zero).1 this
    · have : (((zA : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * (((uA : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) - 1)) *
          ((g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0 := by
        linear_combination (-1 : InfiniteAdeleRing K) * e10
      exact ((hz.mul hunit).mul_right_eq_zero).1 this

  have hboxmeas : ∀ n : ℕ, MeasurableSet (ArchTorusPin.box K n ×ˢ ArchTorusPin.box K n : Set (InfiniteAdeleRing K × InfiniteAdeleRing K)) := fun n =>
    (ArchTorusPin.isClosed_box K n).measurableSet.prod (ArchTorusPin.isClosed_box K n).measurableSet
  have hfin : ∀ (u' : Kˣ) (z' : (AdeleRing (𝓞 K) K)ˣ), ((u' : Kˣ) : K) ≠ 1 → ∀ (n : ℕ) (S : Set (InfiniteAdeleRing K × InfiniteAdeleRing K)),
      MeasurableSet S → (Measure.map (fun x : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
              ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
              InfiniteAdeleRing K × InfiniteAdeleRing K)) (τA u' z')) (S ∩ (ArchTorusPin.box K n ×ˢ ArchTorusPin.box K n)) ≠ ⊤ := by
    intro u' z' hu' n S hS
    haveI := hτA u' z' hu'
    rw [Measure.map_apply (hme u' z') (hS.inter (hboxmeas n))]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (Set.preimage_mono Set.inter_subset_right)) ?_)
    exact (ArchTorusPin.isCompact_preimage_box _ (hoff u' z' hu') n).measure_lt_top
  have hexh : ∀ (u' : Kˣ) (z' : (AdeleRing (𝓞 K) K)ˣ), ((u' : Kˣ) : K) ≠ 1 → ∀ x : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))),
      (fun x : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
              ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
              InfiniteAdeleRing K × InfiniteAdeleRing K)) x ∈ ⋃ n : ℕ, (ArchTorusPin.box K n ×ˢ ArchTorusPin.box K n : Set (InfiniteAdeleRing K × InfiniteAdeleRing K)) := by
    intro u' z' hu' x
    have hoffx := hoff u' z' hu' x.1 x.2
    have hdet : IsUnit (((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).det) := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.isUnit _
    rw [Matrix.det_fin_two, hoffx.1, zero_mul, sub_zero] at hdet
    obtain ⟨n, ha, hb⟩ := ArchTorusPin.exists_mem_box K (isUnit_of_mul_isUnit_left hdet).unit
      (isUnit_of_mul_isUnit_right hdet).unit
    rw [IsUnit.unit_spec] at ha hb
    exact Set.mem_iUnion.2 ⟨n, Set.mk_mem_prod ha hb⟩

  have hsup : ∀ (u' : Kˣ) (z' : (AdeleRing (𝓞 K) K)ˣ), ((u' : Kˣ) : K) ≠ 1 → ∀ S : Set (InfiniteAdeleRing K × InfiniteAdeleRing K), MeasurableSet S →
      (Measure.map (fun x : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
              ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
              InfiniteAdeleRing K × InfiniteAdeleRing K)) (τA u' z')) S =
        ⨆ n : ℕ, (Measure.map (fun x : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
              ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
              InfiniteAdeleRing K × InfiniteAdeleRing K)) (τA u' z')) (S ∩ (ArchTorusPin.box K n ×ˢ ArchTorusPin.box K n)) := by
    intro u' z' hu' S hS
    set μ := Measure.map (fun x : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
              ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
              InfiniteAdeleRing K × InfiniteAdeleRing K)) (τA u' z') with hμ
    have hU : MeasurableSet (⋃ n : ℕ, (ArchTorusPin.box K n ×ˢ ArchTorusPin.box K n : Set (InfiniteAdeleRing K × InfiniteAdeleRing K))) :=
      MeasurableSet.iUnion hboxmeas
    have hnull : μ (⋃ n : ℕ, (ArchTorusPin.box K n ×ˢ ArchTorusPin.box K n : Set (InfiniteAdeleRing K × InfiniteAdeleRing K)))ᶜ = 0 := by
      rw [hμ, Measure.map_apply (hme u' z') hU.compl]
      have hempty : (fun x : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z' * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u') 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
              ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
              InfiniteAdeleRing K × InfiniteAdeleRing K)) ⁻¹' (⋃ n : ℕ, (ArchTorusPin.box K n ×ˢ ArchTorusPin.box K n : Set (InfiniteAdeleRing K × InfiniteAdeleRing K)))ᶜ = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
        exact hexh u' z' hu' x
      rw [hempty, measure_empty]
    have h1 : μ S = μ (S ∩ ⋃ n : ℕ, (ArchTorusPin.box K n ×ˢ ArchTorusPin.box K n : Set (InfiniteAdeleRing K × InfiniteAdeleRing K))) := by
      have hadd := measure_inter_add_diff (μ := μ) S hU
      have h0 : μ (S \ ⋃ n : ℕ, (ArchTorusPin.box K n ×ˢ ArchTorusPin.box K n : Set (InfiniteAdeleRing K × InfiniteAdeleRing K))) = 0 :=
        measure_mono_null (fun x hx => hx.2) hnull
      rw [← hadd, h0, add_zero]
    rw [h1, Set.inter_iUnion]
    refine (monotone_nat_of_le_succ fun n => ?_).measure_iUnion
    exact Set.inter_subset_inter_right _
      (Set.prod_mono (ArchTorusPin.box_mono K (Nat.le_succ n)) (ArchTorusPin.box_mono K (Nat.le_succ n)))
  apply Measure.ext
  intro S hS
  rw [hsup u z hu S hS, hsup (-1) 1 hu₀ S hS]
  refine iSup_congr fun n => ?_
  refine (ENNReal.toReal_eq_toReal_iff' (hfin u z hu n S hS) (hfin (-1) 1 hu₀ n S hS)).1 ?_
  rw [hreal u z hu _ (hS.inter (hboxmeas n)), hreal (-1) 1 hu₀ _ (hS.inter (hboxmeas n))]

end S_AutomorphicForm_exists_forall_map_entries_centralizer_eq_of_forall_integral_centralScalar_mul_diagUnits2_eq_mul_integral_mul_prod
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_map_entries_centralizer_eq_of_forall_integral_centralScalar_mul_diagUnits2_eq_mul_integral_mul_prod (solution)
