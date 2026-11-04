-- Prove2me | Definitions.Def_FreeGroupFactorProof16
-- name    : FreeGroupFactorProof16
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T02:39:59.239044+00:00
-- url     : https://prove2.me/theorems/93d16737-04c5-41ab-94b7-51baea862061
-- title:
--   Free group factors: supporting development, part 16
-- statement:
--   Part 16 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof15

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock MeasureTheory CyclicSpectral
variable {ι : Type u_1} [DecidableEq ι]

theorem diagonalGenerator_noAtoms (u v : ℝ) (hu : u≠0) (hv : v≠0) (i : ι) :
    NullSingletonClass (measure (diagonalGenerator u v i) (diagonalGenerator_selfAdjoint u v i) (vacuum u v)) := by
  let : InnerProductSpace ℝ (H ι) := InnerProductSpace.rclikeToReal ℂ (H ι)
  apply noAtoms
  intro r η hη
  have he : diagonalGenerator u v i η=(r:ℂ) • η := by
    exact hη.trans (by
      apply Subtype.ext
      funext w
      change r • η w=(r:ℂ)*(η w)
      exact Complex.real_smul)
  have hh := diagonalGenerator_eigen_root_zero u v hu hv i (r:ℂ) η he
  change (inner ℂ (vacuum u v) η).re=0
  rw [hh,Complex.zero_re]

variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

def ambientUniform : UniformAlgebra →⋆ₐ[ℂ] Operator ℕ := by
  letI := probability _ (diagonalGenerator_selfAdjoint u v (0:ℕ)) (vacuum u v) (vacuum_norm_one u v hunit)
  letI := diagonalGenerator_noAtoms u v hu hv (0:ℕ)
  exact uniformHom (diagonalGenerator u v (0:ℕ)) (diagonalGenerator_selfAdjoint u v 0) (vacuum u v)

theorem ambientUniform_mem (a : UniformAlgebra) : ambientUniform u v hu hv hunit a∈diagonalBase u v (0:ℕ) := by
  let := probability _ (diagonalGenerator_selfAdjoint u v (0:ℕ)) (vacuum u v) (vacuum_norm_one u v hunit)
  let := diagonalGenerator_noAtoms u v hu hv (0:ℕ)
  exact uniformHom_mem _ _ _ _ (Set.isClosed_centralizer _) (diagonalGenerator_mem u v 0) a

def ambientUniformBase : UniformAlgebra →⋆ₐ[ℂ] diagonalBase u v (0:ℕ) :=
  (ambientUniform u v hu hv hunit).codRestrict _ (ambientUniform_mem u v hu hv hunit)

theorem ambientUniform_state (a : UniformAlgebra) :
    vacuumTrace u v (ambientUniform u v hu hv hunit a)=uniformState a := by
  let := probability _ (diagonalGenerator_selfAdjoint u v (0:ℕ)) (vacuum u v) (vacuum_norm_one u v hunit)
  let := diagonalGenerator_noAtoms u v hu hv (0:ℕ)
  exact uniformHom_state _ _ _ a
end

section
open FreeFock WeightedCornerIndex GaussianRecognition CyclicSpectral

def diagonalAnnihilators (u v : ℝ) : Submodule ℂ (Operator ℕ) where
  carrier := {X | ∀ a : diagonalBase u v (0:ℕ),star X ((a:Operator ℕ) (vacuum u v))=0}
  zero_mem' := by intro a;simp [star_zero (R := Operator ℕ)]
  add_mem' := by intro X Y hX hY a;rw [star_add (R := Operator ℕ),add_apply,hX a,hY a,add_zero]
  smul_mem' := by intro c X hX a;rw [star_smul,smul_apply,hX a,smul_zero]

theorem diagonalAnnihilators_sandwich (u v : ℝ) (p q : diagonalBase u v (0:ℕ)) (X : Operator ℕ)
    (hX : X∈diagonalAnnihilators u v) : (p:Operator ℕ)*X*(q:Operator ℕ)∈diagonalAnnihilators u v := by
  intro a
  rw [star_mul,star_mul,mul_apply_eq_comp,mul_apply_eq_comp]
  have hh := hX (star p*a)
  change star X (star (p:Operator ℕ) ((a:Operator ℕ) (vacuum u v)))=0 at hh
  rw [hh,map_zero]

theorem ambientExtra_annihilator (u v : ℝ) (i : WeightedCornerIndex.Index) : ambientExtra u v i∈diagonalAnnihilators u v := by
  intro a
  unfold ambientExtra
  cases residualSlot i with
  | none => simp [star_zero (R := Operator ℕ)]
  | some b => exact diagonal_base_annihilate u v 0 b a

theorem ambientRaw_annihilator (u v : ℝ) (i : WeightedCornerIndex.Index) (n : ℕ) : ambientRaw u v i n∈diagonalAnnihilators u v := by
  intro a
  exact fresh_C_annihilates_old_vacuum u v {0} (reservoirCode (i,n)+1) (by simp)
    ⟨a,diagonalBase_le_singleton u v 0 a.property⟩

variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

def ambientCreation (i : WeightedCornerIndex.Index × ℕ) : Operator ℕ := (ambientAbsorption u v hu hv).output i.1 i.2

theorem ambientCreation_annihilator (i : WeightedCornerIndex.Index × ℕ) : ambientCreation u v hu hv i∈diagonalAnnihilators u v :=
  (ambientAbsorption u v hu hv).output_mem (diagonalAnnihilators u v) (diagonalAnnihilators_sandwich u v)
    (ambientExtra_annihilator u v) (ambientRaw_annihilator u v) i.1 i.2

theorem ambientCreation_covariance (i j : WeightedCornerIndex.Index × ℕ) (a : UniformAlgebra) :
    star (ambientCreation u v hu hv i)*ambientUniform u v hu hv hunit a*ambientCreation u v hu hv j=
      if i=j then uniformState a • (1:Operator ℕ) else 0 := by
  have hh := (ambientAbsorption u v hu hv).output_cov i.1 j.1 i.2 j.2 (ambientUniformBase u v hu hv hunit a)
  have hs : (ambientAbsorption u v hu hv).τ (ambientUniformBase u v hu hv hunit a)=uniformState a :=
    ambientUniform_state u v hu hv hunit a
  rw [hs] at hh
  change star (ambientCreation u v hu hv i)*ambientUniform u v hu hv hunit a*ambientCreation u v hu hv j=
    (if i.1=j.1 ∧ i.2=j.2 then uniformState a • (1:Operator ℕ) else 0) at hh
  simpa only [← Prod.ext_iff] using hh

def ambientSystem : GaussianRecognition.System UniformAlgebra (H ℕ)
    (WeightedCornerIndex.Index × ℕ) uniformCovariance where
  coeff := ambientUniform u v hu hv hunit
  root := vacuum u v
  create := ambientCreation u v hu hv
  contract i j a := by
    rw [ambientCreation_covariance]
    by_cases h : i=j
    · simp only [uniformCovariance,h,ite_true,map_smul,map_one]
    · simp only [uniformCovariance,ite_eq_right h,map_zero]
  annihilate i a := ambientCreation_annihilator u v hu hv i (ambientUniformBase u v hu hv hunit a)
end

section
open FreeFock CyclicSpectral GaussianRecognition Filter Topology
open scoped ENNReal
variable {ι : Type u_2} [DecidableEq ι]

theorem path_closed_total (K : Submodule ℂ (H ι)) (hK : IsClosed (K:Set (H ι)))
    (hδ : ∀ w : Path ι,lp.single 2 w (1:ℂ)∈K) : K=⊤ := by
  apply top_unique
  intro ξ _
  apply hK.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) ξ)
  filter_upwards [] with s
  apply K.sum_mem
  intro w _
  have he : lp.single (E := fun _ : Path ι => ℂ) 2 w (ξ w)=(ξ w) • lp.single 2 w 1 := by
    ext v
    simp [lp.single_apply,Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hδ w)

theorem ambient_commutant_total (u v : ℝ) (hu : u≠0) (hv : v≠0) :
    (Submodule.span ℂ (Set.range (fun B : StarSubalgebra.centralizer ℂ
      (ambientAlgebra (ι := ι) u v:Set (Operator ι)) => (B:Operator ι) (vacuum u v)))).topologicalClosure=⊤ := by
  apply path_closed_total _ (Submodule.isClosed_topologicalClosure _)
  intro w
  obtain ⟨B,hB,heB,_⟩ := good_right_basis u v hu hv w
  have hh : B∈StarSubalgebra.centralizer ℂ (ambientAlgebra (ι := ι) u v:Set (Operator ι)) :=
    centralizer_bicommutant _ ⟨_,hB⟩
  apply Submodule.le_topologicalClosure _
  rw [← heB]
  exact Submodule.subset_span ⟨⟨B,hh⟩,rfl⟩

variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

theorem diagonalGenerator_mem_uniform : diagonalGenerator u v (0:ℕ)∈
    Bicommutant.algebra (Set.range (ambientUniform u v hu hv hunit)) := by
  let : Nontrivial (H ℕ) := nontrivial_of_ne (vacuum u v:H ℕ) 0 (by
    intro h
    have hh := vacuum_norm_one (ι := ℕ) u v hunit
    rw [h,norm_zero] at hh
    exact zero_ne_one hh)
  let := probability _ (diagonalGenerator_selfAdjoint u v (0:ℕ)) (vacuum u v) (vacuum_norm_one u v hunit)
  let := diagonalGenerator_noAtoms u v hu hv (0:ℕ)
  have h := operator_mem_haar_bicommutant (diagonalGenerator u v (0:ℕ)) (diagonalGenerator_selfAdjoint u v 0)
    (vacuum u v) (ambientAlgebra u v) (Set.isClosed_centralizer _)
    (diagonalBase_le_ambient u v 0 (diagonalGenerator_mem u v 0)) (ambient_commutant_total u v hu hv)
  apply Bicommutant.mono _ (Set.range (ambientUniform u v hu hv hunit)) ?_ h
  rintro T rfl
  exact ⟨uniformPhase,(uniformHom_phase (diagonalGenerator u v (0:ℕ)) (diagonalGenerator_selfAdjoint u v 0) (vacuum u v)).symm⟩

theorem diagonalBase_le_uniform : diagonalBase u v (0:ℕ)≤
    Bicommutant.algebra (Set.range (ambientUniform u v hu hv hunit)) := by
  rw [diagonalBase_eq_generated]
  apply Bicommutant.generated_le
  rintro T rfl
  exact diagonalGenerator_mem_uniform u v hu hv hunit
end

section
open FreeFock WeightedCornerIndex GaussianRecognition
variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

theorem ambientExtra_pair_mem (i : WeightedCornerIndex.Index) :
    ambientExtra u v i+star (ambientExtra u v (CircularRotation.flip i))∈ambientAlgebra u v := by
  simp only [ambientExtra,residualSlot_flip]
  cases residualSlot i with
  | none => simp only [Option.map_none,Option.elim_none,star_zero (Operator ℕ),add_zero];exact zero_mem _
  | some b =>
    simp only [Option.map_some,Option.elim_some,Bool.not_not]
    rw [rect_paired_eq]
    have hm (r : Bool) : (vertex r : Operator ℕ)∈ambientAlgebra u v := by
      cases r
      · exact sub_mem (one_mem _) (P_mem_ambient u v)
      · exact P_mem_ambient u v
    exact mul_mem (mul_mem (hm _) (S_mem_ambient u v 0)) (hm _)

theorem ambientOutput_pair_mem (i : WeightedCornerIndex.Index) (n : ℕ) :
    (ambientAbsorption u v hu hv).output i n+
      star ((ambientAbsorption u v hu hv).output (CircularRotation.flip i) n)∈ambientAlgebra u v := by
  apply ((ambientAbsorption u v hu hv).output_generation (ambientAlgebra u v)
    (fun i => diagonalBase_le_ambient u v 0 (ambientLeft u v i).property)
    (fun i => diagonalBase_le_ambient u v 0 (ambientRight u v i).property)).mp ?_ i n
  exact ⟨ambientExtra_pair_mem u v,fun i n => S_mem_ambient u v (reservoirCode (i,n)+1)⟩

theorem ambientSystem_le_ambient : (ambientSystem u v hu hv hunit).generated scalarFlip≤ambientAlgebra u v := by
  apply Bicommutant.generated_le
  rintro T (⟨a,rfl⟩|⟨i,rfl⟩)
  · exact diagonalBase_le_ambient u v 0 (ambientUniformBase u v hu hv hunit a).property
  · exact ambientOutput_pair_mem u v hu hv i.1 i.2

theorem diagonalBase_le_system : diagonalBase u v (0:ℕ)≤(ambientSystem u v hu hv hunit).generated scalarFlip :=
  (diagonalBase_le_uniform u v hu hv hunit).trans
    (Bicommutant.mono _ _ (fun _ h => Or.inl h))

theorem ambient_generator_decomposition :
    S u v (0:ℕ)=diagonalSelf u v 0+
      (ambientExtra u v (residualIndex true)+star (ambientExtra u v (residualIndex false)))+
      (ambientExtra u v (residualIndex false)+star (ambientExtra u v (residualIndex true))) := by
  change S u v 0=diagonalSelf u v 0+
    (ambientRect u v 0 true false+star (ambientRect u v 0 false true))+
    (ambientRect u v 0 false true+star (ambientRect u v 0 true false))
  rw [diagonalSelf,diagonalLeg,diagonalLeg,rect_paired_eq,rect_paired_eq,rect_paired_eq,rect_paired_eq]
  change S u v 0=P*S u v 0*P+(1-P)*S u v 0*(1-P)+P*S u v 0*(1-P)+(1-P)*S u v 0*P
  simp only [sub_mul,mul_sub,one_mul,mul_one]
  abel

theorem ambient_le_ambientSystem : ambientAlgebra u v≤(ambientSystem u v hu hv hunit).generated scalarFlip := by
  let G := (ambientSystem u v hu hv hunit).generated scalarFlip
  have hbase := diagonalBase_le_system u v hu hv hunit
  have hout (i : WeightedCornerIndex.Index) (n : ℕ) :
      (ambientAbsorption u v hu hv).output i n+
        star ((ambientAbsorption u v hu hv).output (CircularRotation.flip i) n)∈G :=
    Bicommutant.subset _ (Or.inr (Set.mem_range_self (i,n)))
  have hgen := ((ambientAbsorption u v hu hv).output_generation G
    (fun i => hbase (ambientLeft u v i).property)
    (fun i => hbase (ambientRight u v i).property)).mpr hout
  apply Bicommutant.generated_le
  rintro T (rfl|⟨n,rfl⟩)
  · exact hbase (P_mem_diagonalBase u v 0)
  · cases n with
    | zero =>
      rw [ambient_generator_decomposition u v]
      exact add_mem (add_mem (hbase (diagonalSelf_mem u v 0)) (hgen.1 (residualIndex true)))
        (hgen.1 (residualIndex false))
    | succ n =>
      obtain ⟨⟨i,k⟩,he⟩ := reservoirCode.surjective n
      subst n
      exact hgen.2 i k

theorem ambient_generated_eq : (ambientSystem u v hu hv hunit).generated scalarFlip=ambientAlgebra u v :=
  le_antisymm (ambientSystem_le_ambient u v hu hv hunit) (ambient_le_ambientSystem u v hu hv hunit)

theorem ambientSystem_total :
    (Submodule.span ℂ (Set.range (ambientSystem u v hu hv hunit).family)).topologicalClosure=⊤ := by
  apply path_closed_total _ (Submodule.isClosed_topologicalClosure _)
  intro w
  obtain ⟨B,hB,hh⟩ := good_basis u v hu hv w
  rw [← hh]
  exact (ambientSystem u v hu hv hunit).normalHull_bicommutant scalarFlip B
    (ambient_le_ambientSystem u v hu hv hunit hB.1)
end

open FreeFock GaussianRecognition CyclicSpectral
variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

theorem scalar_ambient_state (a : UniformAlgebra) :
    inner ℂ scalarSystem.root (scalarSystem.coeff a scalarSystem.root)=
      inner ℂ (ambientSystem u v hu hv hunit).root
        ((ambientSystem u v hu hv hunit).coeff a (ambientSystem u v hu hv hunit).root) := by
  exact (scalarUniform_state (none:ScalarIndex) a).trans (ambientUniform_state u v hu hv hunit a).symm

def ambientGaussianIso : (ambientSystem u v hu hv hunit).generated scalarFlip ≃⋆ₐ[ℂ]
    scalarSystem.generated scalarFlip :=
  (ambientSystem u v hu hv hunit).generatedIso scalarSystem
    (scalar_ambient_state u v hu hv hunit)
    (ambientSystem_total u v hu hv hunit) scalarSystem_total scalarFlip

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36
universe u_37 u_38 u_39 u_40 u_41 u_42 u_43 u_44 u_45 u_46 u_47 u_48
universe u_49

open Filter Topology

namespace FreeFock
open Filter Topology
open scoped ENNReal
variable {α : Type u_6} [DecidableEq α]

end FreeFock
open MeasureTheory Set CompactlySupported
open scoped ENNReal
namespace CyclicSpectral
variable {H : Type u_7} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
end CyclicSpectral

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal

namespace CyclicSpectral

section
open MeasureTheory
variable {H : Type u_19} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
section
open MeasureTheory Filter
variable {H : Type u_20} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
open MeasureTheory Filter
variable {H : Type u_21} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end CyclicSpectral
namespace FreeFock

section
open MeasureTheory
variable {α : Type u_22} [DecidableEq α]

end
open MeasureTheory
variable {α : Type u_23} [DecidableEq α]

instance semicircular_spectral_probability (i : α) :
    IsProbabilityMeasure (CyclicSpectral.measure (semicircular i) (semicircular_selfAdjoint i) vacuum) := by
  apply CyclicSpectral.probability
  simp [vacuum,lp.norm_single]

instance semicircular_spectral_diffuse (i : α) :
    NullSingletonClass (CyclicSpectral.measure (semicircular i) (semicircular_selfAdjoint i) vacuum) :=
  semicircular_spectral_noAtoms i

 theorem spectralHaar_mem (i : α) :
    (CyclicSpectral.haarUnitary (semicircular i) (semicircular_selfAdjoint i) vacuum : Operator α)
      ∈ gaussianAlgebra α := by
  apply CyclicSpectral.complexHom_mem
  · rw [gaussianAlgebra,StarSubalgebra.coe_centralizer]
    exact Set.isClosed_centralizer _
  · exact StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
      (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self i))

def spectralHaar (i : α) : unitary (gaussianAlgebra α) := by
  let U := CyclicSpectral.haarUnitary (semicircular i) (semicircular_selfAdjoint i) vacuum
  refine ⟨⟨U,spectralHaar_mem i⟩,Unitary.mem_iff.mpr ⟨?_,?_⟩⟩
  · apply Subtype.ext
    exact (Unitary.mem_iff.mp U.property).1
  · apply Subtype.ext
    exact (Unitary.mem_iff.mp U.property).2

 theorem spectralHaar_moment (i : α) (n : ℕ) :
    vacuumTrace ((((spectralHaar i : gaussianAlgebra α) : Operator α)^n))=if n=0 then 1 else 0 :=
  CyclicSpectral.haarUnitary_moment (semicircular i) (semicircular_selfAdjoint i) vacuum n

end FreeFock
open Filter Topology
open scoped ENNReal
 theorem lp_strong_limit_of_bounded_basis {α : Type u_24} [DecidableEq α]
    (T : ℕ → lp (fun _ : α => ℂ) 2 →L[ℂ] lp (fun _ : α => ℂ) 2)
    (A : lp (fun _ : α => ℂ) 2 →L[ℂ] lp (fun _ : α => ℂ) 2)
    (C : ℝ) (hbound : ∀ n, ‖T n‖ ≤ C)
    (hbasis : ∀ a, Tendsto (fun n => T n (lp.single 2 a 1)) atTop (𝓝 (A (lp.single 2 a 1))))
    (ξ : lp (fun _ : α => ℂ) 2) : Tendsto (fun n => T n ξ) atTop (𝓝 (A ξ)) := by
  have heq : Equicontinuous (fun n => (T n : lp (fun _ : α => ℂ) 2 → lp (fun _ : α => ℂ) 2)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => C*r)
      (by simpa using (tendsto_const_nhds.mul (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0))))
    intro x y n
    rw [dist_eq_norm,← map_sub]
    exact (T n).le_opNorm (x-y) |>.trans
      (by simpa only [dist_eq_norm] using mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg (x-y)))
  have hc := heq.isClosed_setOfPred_tendsto (l := atTop) A.continuous
  apply hc.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) ξ)
  filter_upwards [] with s
  have hs (a : α) : Tendsto (fun n => T n (lp.single 2 a (ξ a))) atTop (𝓝 (A (lp.single 2 a (ξ a)))) := by
    have h : lp.single (E := fun _ : α => ℂ) 2 a (ξ a)=(ξ a) • lp.single 2 a 1 := by
      ext b
      simp [lp.single_apply,Pi.single_apply]
    simpa only [h,map_smul] using (hbasis a).const_smul (ξ a)
  simpa only [map_sum] using tendsto_finsetSum s (fun a _ => hs a)
namespace FreeFock

section
open Filter Topology Set MeasureTheory
variable {α : Type u_25} [DecidableEq α]

end
section
open Set
variable {α : Type u_26} [DecidableEq α]

end

section
open Filter Topology
open scoped ENNReal
variable {α : Type u_28} [DecidableEq α]

end
section
open scoped ComplexConjugate
variable {α : Type u_29} [DecidableEq α]

end
section
variable {α : Type u_30} [DecidableEq α]

end
variable {α : Type u_31} [DecidableEq α]

end FreeFock
section

variable {A : Type u_32} [NormedRing A] [NormedAlgebra ℂ A]

end
namespace FreeFock

section
variable {α : Type u_33} [DecidableEq α]

end
variable {α : Type u_34} [DecidableEq α]

end FreeFock

section
variable {α : Type u_35}

end
section
variable {α : Type u_36} {G : Type u_37} [Group G]

end
namespace FreeFock
variable {α : Type u_38} [DecidableEq α]

end FreeFock

namespace CyclicUnitary
open scoped ENNReal
variable {G : Type u_42} {E : Type u_43} [Group G] [DecidableEq G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (ρ : G →* (E →L[ℂ] E)) (hstar : ∀ g,star (ρ g)=ρ g⁻¹) (ξ : E)

end CyclicUnitary
namespace FreeFock
variable {α : Type u_44} [DecidableEq α]

end FreeFock

section

variable {A : Type u_45} {B : Type u_46} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
  [StarRing A] [StarRing B] [StarModule ℂ A] [StarModule ℂ B]

end
open scoped ENNReal
variable {G : Type u_47} [Group G] [DecidableEq G]

namespace FreeFock
variable {α : Type u_48} [DecidableEq α]

end FreeFock

end FreeGroupFactorMain

end

end OAI
end


