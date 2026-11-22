-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
-- name    : LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:50:29.749884+00:00
-- url     : https://prove2.me/theorems/2ff10664-5eb3-44ef-b192-c6bd2626ddfc
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_P2M_ProbabilityTheory_Kernel_chain_rule__5854b667e2d9
public import Theorems.Thm_P2M_ProbabilityTheory_condDistrib_apply__7130db3f8416
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_snd
public import Theorems.Thm_ProbabilityTheory_Kernel_chain_rule
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_congr
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft_unit
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
public import Theorems.Thm_ProbabilityTheory_Kernel_finiteKernelSupport_of_const
public import Theorems.Thm_ProbabilityTheory_Kernel_mutualInfo_def
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteRight_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_snd_reverse
public import Theorems.Thm_ProbabilityTheory_Measure_ext_iff_measureReal_singleton_finiteSupport
public import Theorems.Thm_ProbabilityTheory_condDistrib_const_unit
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
public import Theorems.Thm_ProbabilityTheory_integral_congr_finiteSupport
public import Theorems.Thm_ProbabilityTheory_measureEntropy_map_of_injective
public import Theorems.Thm_ProbabilityTheory_measureMutualInfo_eq_zero_iff
public import Theorems.Thm_prod_eq
attribute [local simp] MeasureTheory.Measure.pi_eval_preimage
attribute [local simp] MeasureTheory.Measure.pi_pi_set
attribute [local simp] P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
attribute [local simp] ProbabilityTheory.Kernel.entropy_compProd_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_const
attribute [local simp] ProbabilityTheory.Kernel.entropy_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_prod
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkLeft
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkRight
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_kernel
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_measure
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteMiddle_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteRight_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_snd_reverse
attribute [local simp] ProbabilityTheory.identDistrib_id
attribute [local simp] ProbabilityTheory.indepFun_zero_measure
attribute [local simp] prod_eq


set_option autoImplicit true
@[expose] public section
@[expose] public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
namespace ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
section entropy
noncomputable
def entropy (X : Ω → S) (μ : Measure Ω := by volume_tac) := Hm[μ.map X]
@[inherit_doc entropy] notation3:max "H[" X "; " μ "]" => entropy X μ
@[inherit_doc entropy] notation3:max "H[" X "]" => entropy X volume
@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y "; " μ "]" =>
  entropy X (μ[|Y ← y])
@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y "]" => entropy X (ℙ[|Y ← y])
lemma entropy_def (X : Ω → S) (μ : Measure Ω) : entropy X μ = Hm[μ.map X] := rfl
lemma entropy_eq_kernel_entropy (X : Ω → S) (μ : Measure Ω) :
    H[X; μ] = Hk[Kernel.const Unit (μ.map X), Measure.dirac ()] := by simp [entropy]
@[simp]
lemma entropy_zero_measure (X : Ω → S) : H[X; (0 : Measure Ω)] = 0 := by simp [entropy]
lemma entropy_congr {X X' : Ω → S} (h : X =ᵐ[μ] X') : H[X; μ] = H[X'; μ] := by
  rw [entropy_def, Measure.map_congr h, entropy_def]
lemma _root_.ProbabilityTheory.IdentDistrib.entropy_congr
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} {X' :
  Ω' → S}
    (h : IdentDistrib X X' μ μ') : H[X; μ] = H[X'; μ'] := by
  simp [entropy_def, h.map_eq]
lemma entropy_comp_of_injective [MeasurableSpace T] [Countable S] [MeasurableSingletonClass S]
    [MeasurableSingletonClass T]
    (μ : Measure Ω) (hX : Measurable X) (f : S → T) (hf : Function.Injective f) :
    H[f ∘ X; μ] = H[X; μ] := by
  have hf_m : Measurable f := .of_discrete
  rw [entropy_def, ← Measure.map_map hf_m hX, measureEntropy_map_of_injective _ _ hf_m hf,
    entropy_def]
@[simp] lemma entropy_const [MeasurableSingletonClass S] [IsZeroOrProbabilityMeasure μ] (c : S) :
    H[fun _ ↦ c; μ] = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ <;>
  simp [entropy, Measure.map_const]
open Set
open Function
variable [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
@[simp] lemma entropy_prod_comp (hX : Measurable X) (μ : Measure Ω) (f : S → T) :
    H[⟨X, f ∘ X⟩; μ] = H[X ; μ] :=
  entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) fun _ _ ab ↦ (Prod.ext_iff.1 ab).1
variable [Countable T]
lemma entropy_comm (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨X, Y⟩; μ] = H[⟨Y, X⟩ ; μ] := by
  change H[Prod.swap ∘ ⟨Y, X⟩; μ] = H[⟨Y, X⟩; μ]
  exact entropy_comp_of_injective μ (hY.prodMk hX) Prod.swap Prod.swap_injective
end entropy
section condEntropy
variable [MeasurableSpace T]
variable {X : Ω → S} {Y : Ω → T}
noncomputable
def _root_.ProbabilityTheory.condEntropy
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  (μ.map Y)[fun y ↦ H[X | Y ← y; μ]]
lemma _root_.ProbabilityTheory.condEntropy_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    condEntropy X Y μ = (μ.map Y)[fun y ↦ H[X | Y ← y; μ]] := rfl
@[inherit_doc condEntropy] notation3:max "H[" X " | " Y "; " μ "]" => condEntropy X Y μ
@[inherit_doc condEntropy] notation3:max "H[" X " | " Y "]" => condEntropy X Y volume
section
variable [MeasurableSingletonClass T]
lemma _root_.ProbabilityTheory.condEntropy_eq_kernel_entropy
    [Nonempty S] [Countable S] [MeasurableSingletonClass S]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] [FiniteRange Y] :
    H[X | Y; μ] = Hk[condDistrib X Y μ, μ.map Y] := by
  rw [condEntropy_def, Kernel.entropy]
  apply integral_congr_finiteSupport
  intro t ht
  rw [Measure.map_apply hY (.singleton _)] at ht
  simp only [entropy_def]
  congr
  ext s hs
  rw [condDistrib_apply' hX hY _ _ ht hs, Measure.map_apply hX hs,
      cond_apply (hY (.singleton _))]
variable [Countable T] [Nonempty T] [Nonempty S] [MeasurableSingletonClass S] [Countable S]
  [Countable U] [MeasurableSingletonClass U]
end
@[simp]
lemma _root_.ProbabilityTheory.condEntropy_zero_measure
    (X : Ω → S) (Y : Ω → T) : H[X | Y; (0 : Measure Ω)] = 0 :=
  by simp [condEntropy]
variable [MeasurableSingletonClass T]
variable [MeasurableSingletonClass S]
variable [Countable S]
end condEntropy
section pair
variable [MeasurableSpace T]
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]
lemma _root_.ProbabilityTheory.chain_rule' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    H[⟨X, Y⟩; μ] = H[X; μ] + H[Y | X; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [entropy_eq_kernel_entropy, Kernel.chain_rule]
  · simp_rw [← Kernel.map_const _ (hX.prodMk hY), Kernel.fst_map_prod _ hY,
    Kernel.map_const _ hX,
      Kernel.map_const _ (hX.prodMk hY)]
    congr 1
    · rw [Kernel.entropy, integral_dirac]
      rfl
    · simp_rw [condEntropy_eq_kernel_entropy hY hX]
      have : Measure.dirac () ⊗ₘ Kernel.const Unit (μ.map X) = μ.map (fun ω ↦ ((),
        X ω)) := by
        ext s _
        rw [Measure.dirac_unit_compProd_const, Measure.map_map measurable_prodMk_left hX]
        congr
      rw [this, Kernel.entropy_congr (condDistrib_const_unit hX hY μ)]
      have : μ.map (fun ω ↦ ((), X ω)) = (μ.map X).map (Prod.mk ()) := by
        ext s _
        rw [Measure.map_map measurable_prodMk_left hX]
        rfl
      rw [this, Kernel.entropy_prodMkLeft_unit]
  · apply Kernel.FiniteKernelSupport.aefiniteKernelSupport
    exact Kernel.finiteKernelSupport_of_const _
lemma _root_.ProbabilityTheory.chain_rule (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    H[⟨X, Y⟩; μ] = H[Y; μ] + H[X | Y; μ] := by
  rw [entropy_comm hX hY, chain_rule' μ hY hX]
variable [Countable U] [MeasurableSingletonClass U]
end pair
section mutualInfo
variable [MeasurableSpace T]
noncomputable
def _root_.ProbabilityTheory.mutualInfo
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  H[X; μ] + H[Y; μ] - H[⟨X, Y⟩; μ]
@[inherit_doc mutualInfo] notation3:max "I[" X " : " Y "; " μ "]" => mutualInfo X Y μ
@[inherit_doc mutualInfo] notation3:max "I[" X " : " Y "]" => mutualInfo X Y volume
lemma _root_.ProbabilityTheory.mutualInfo_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
  I[X : Y; μ] = H[X; μ] + H[Y; μ] - H[⟨X, Y⟩; μ] := rfl
noncomputable
def _root_.ProbabilityTheory.condMutualInfo
    (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω := by volume_tac) :
    ℝ := (μ.map Z)[fun z ↦ H[X | Z ← z; μ] + H[Y | Z ← z; μ] - H[⟨X,
      Y⟩ | Z ← z; μ]]
@[inherit_doc condMutualInfo]
notation3:max "I[" X " : " Y "|" Z ";" μ "]" => condMutualInfo X Y Z μ
@[inherit_doc condMutualInfo]
notation3:max "I[" X " : " Y "|" Z "]" => condMutualInfo X Y Z volume
@[simp] lemma _root_.ProbabilityTheory.condMutualInfo_zero_measure : I[X : Y | Z; 0] = 0 := by
  simp [condMutualInfo]
section
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]
lemma _root_.ProbabilityTheory.mutualInfo_eq_zero
    (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    I[X : Y; μ] = 0 ↔ IndepFun X Y μ := by
  simp_rw [mutualInfo_def, entropy_def]
  have h_fst : μ.map X = (μ.map (⟨X, Y⟩)).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    congr
  have h_snd : μ.map Y = (μ.map (⟨X, Y⟩)).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    congr
  rw [h_fst, h_snd]
  convert measureMutualInfo_eq_zero_iff (μ := μ.map (⟨X, Y⟩)) using 2
  · exact measureMutualInfo_def _
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
    Measure.ext_iff_measureReal_singleton_finiteSupport]
  congr! with p
  convert measureReal_prod_prod (μ := μ.map X) (ν := μ.map Y) {p.1} {p.2}
  · simp
  · exact Measure.map_map measurable_fst (hX.prodMk hY)
  · exact Measure.map_map measurable_snd (hX.prodMk hY)
protected alias ⟨_, IndepFun.mutualInfo_eq_zero⟩ := mutualInfo_eq_zero
lemma _root_.ProbabilityTheory.entropy_pair_eq_add
    (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    H[⟨X, Y⟩; μ] = H[X; μ] + H[Y; μ] ↔ IndepFun X Y μ := by
  rw [eq_comm, ← sub_eq_zero, ← mutualInfo_eq_zero hX hY]; rfl
protected alias ⟨_, IndepFun.entropy_pair_eq_add⟩ := entropy_pair_eq_add
variable [Countable S] [Countable T]
variable [Countable U] [MeasurableSingletonClass U] [Nonempty S] [Nonempty T]
end
section
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]
variable [Countable S] [Countable T]
variable [MeasurableSingletonClass U]
end
section IsProbabilityMeasure
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]
variable [Countable U] [MeasurableSingletonClass U]
variable (μ)
variable [Countable S] [Countable T]
variable [IsZeroOrProbabilityMeasure μ]
end IsProbabilityMeasure
end mutualInfo
end ProbabilityTheory
section dataProcessing
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
namespace ProbabilityTheory
universe uΩ uS uT uU uV uW
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {U : Type uU} {V : Type uV} {W : Type uW}
  [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSpace V] [MeasurableSpace W]
  [Countable S] [Countable T] [Countable V] [Countable W]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [MeasurableSingletonClass V] [MeasurableSingletonClass W]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
  {μ : Measure Ω}
end ProbabilityTheory
end dataProcessing
section MeasureSpace_example
open ProbabilityTheory
variable {Ω S T : Type*} [MeasureSpace Ω] [IsZeroOrProbabilityMeasure (ℙ : Measure Ω)]
  [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T}
example (hX : Measurable X) (hY : Measurable Y) :
  H[⟨X, Y⟩] = H[Y] + H[X | Y] := chain_rule _ hX hY
end MeasureSpace_example


