-- Prove2me | Definitions.Def_Q220Uk002
-- name    : Q220Uk002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:37:36.076895+00:00
-- url     : https://prove2.me/theorems/c3bbb03b-d77f-45dc-bae6-7b4f062ec4d1
-- title:
--   Definitions bundle Q220Uk002 of the split of OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 746 declarations of OpenAI's Lean: 361 definitions, 31 inductive types or structures, 19 instances and 335 theorems. The definitions and types are `OAI.UniformKServer.BalancedStar.fraction`, `OAI.UniformKServer.BinaryTape.token`, `OAI.UniformKServer.BinaryTape.word`, `OAI.UniformKServer.BitSampling.bitsEquiv`, `OAI.UniformKServer.BitSampling.cumulative`, `OAI.UniformKServer.BitSampling.mean`, `OAI.UniformKServer.BitSampling.row`, `OAI.UniformKServer.BitSampling.rowCost`, `OAI.UniformKServer.BitSampling.runCost`, `OAI.UniformKServer.BoundaryPartition.join`, `OAI.UniformKServer.BoundaryPartition.split`, `OAI.UniformKServer.ComputedInstance.allDistances`, `OAI.UniformKServer.ComputedInstance.cap`, `OAI.UniformKServer.ComputedInstance.diameter`, `OAI.UniformKServer.ComputedInstance.positiveDistances`, `OAI.UniformKServer.ComputedInstance.prefixTrace`, `OAI.UniformKServer.ComputedInstance.restart`, `OAI.UniformKServer.ComputedInstance.separation`, `OAI.UniformKServer.ConstructorProgram.read`, `OAI.UniformKServer.EffectiveLP.BoundedFlow`, `OAI.UniformKServer.EffectiveLP.Config`, `OAI.UniformKServer.EffectiveLP.Edge`, `OAI.UniformKServer.EffectiveLP.Form.RowV`, `OAI.UniformKServer.EffectiveLP.Form.constant`, `OAI.UniformKServer.EffectiveLP.Form.eqRows`, `OAI.UniformKServer.EffectiveLP.Form.objective`, `OAI.UniformKServer.EffectiveLP.Form.recover`, `OAI.UniformKServer.EffectiveLP.Form.sum`, `OAI.UniformKServer.EffectiveLP.Form.var`, `OAI.UniformKServer.EffectiveLP.Form.vector`, `OAI.UniformKServer.EffectiveLP.Label`, `OAI.UniformKServer.EffectiveLP.Row`, `OAI.UniformKServer.EffectiveLP.Short`, `OAI.UniformKServer.EffectiveLP.Variable`, `OAI.UniformKServer.EffectiveLP.Word`, `OAI.UniformKServer.EffectiveLP.chosen`, `OAI.UniformKServer.EffectiveLP.costRow`, `OAI.UniformKServer.EffectiveLP.enumerate`, `OAI.UniformKServer.EffectiveLP.extend`, `OAI.UniformKServer.EffectiveLP.flowRow` and 352 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `UniformKServer_ActualAnchorDriftSum`, `UniformKServer_ActualCoordinate`, `UniformKServer_ActualPublicFlow`, `UniformKServer_BalancedStar`, `UniformKServer_BinaryTape`, `UniformKServer_BitPaths`, `UniformKServer_BitSampling`, `UniformKServer_BoundaryPartition`, `UniformKServer_BoundedFilter`, `UniformKServer_ComputedInstance`, `UniformKServer_ConstructorProgram`, `UniformKServer_DyadicRows`, `UniformKServer_EntropyCredit`, `UniformKServer_EpochAlpha`, `UniformKServer_EpochCut`, `UniformKServer_EpochExpectation`, `UniformKServer_EpochFinite`, `UniformKServer_EpochParameters`, `UniformKServer_EpochPartition`, `UniformKServer_EpochShadow`, `UniformKServer_Epochs`, `UniformKServer_ExactOptimum`, `UniformKServer_ExecutableDyadic`, `UniformKServer_Fallback`, `UniformKServer_FineCaps`, `UniformKServer_FineVariation`, `UniformKServer_FiniteFlow`, `UniformKServer_FiniteFlowCompact`, `UniformKServer_FiniteFlowMinimax`, `UniformKServer_FiniteFlowSpace`, `UniformKServer_FiniteLawFinance`, `UniformKServer_FiniteSeparation`, `UniformKServer_FiniteTable`, `UniformKServer_FlatOperational`, `UniformKServer_FlatTM2`, `UniformKServer_FlatTermination`, `UniformKServer_FourierMotzkin`, `UniformKServer_HeldRelative`, `UniformKServer_IntegerParks`, `UniformKServer_KeyCountVariation`, `UniformKServer_KeySizeTracker`, `UniformKServer_LaminarTransport`, `UniformKServer_LazyFinance`, `UniformKServer_LevelParkCapacity`, `UniformKServer_LinearProgram`, `UniformKServer_LiteralInput`, `UniformKServer_LiteralPartial`, `UniformKServer_LiteralPartrec`, `UniformKServer_LiteralVector`, `UniformKServer_MetricRealization`, `UniformKServer_OfflineDynamic`, `UniformKServer_OfflineLaw`, `UniformKServer_OffsetBridge`, `UniformKServer_OffsetInstance`, `UniformKServer_OffsetLP`, `UniformKServer_OffsetParameters`, `UniformKServer_OffsetTable`, `UniformKServer_ParameterGaps`, `UniformKServer_ParkCapacity`, `UniformKServer_ParkCoefficients`, `UniformKServer_ParkedTransport`, `UniformKServer_PartitionAnchors`, `UniformKServer_PartitionLaw`, `UniformKServer_PartitionTransport`, `UniformKServer_PathExpansion`, `UniformKServer_PositiveSupport`, `UniformKServer_PrefixMovement`, `UniformKServer_PrefixTree`, `UniformKServer_PrimitiveRules`, `UniformKServer_PublicFlow`, `UniformKServer_PublicRounding`, `UniformKServer_RankData`, `UniformKServer_RankFunctions`, `UniformKServer_RankTracking`, `UniformKServer_RankedTree`, `UniformKServer_RawAccepted`, `UniformKServer_RawArithmetic`, `UniformKServer_RawBinary`, `UniformKServer_RawBits`, `UniformKServer_RawBlockCharge`, `UniformKServer_RawCertificate`, `UniformKServer_RawControllerCost`, `UniformKServer_RawExpansion`, `UniformKServer_RawFallback`, `UniformKServer_RawFilter`, `UniformKServer_RawFinite`, `UniformKServer_RawMarks`, `UniformKServer_RawMetric`, `UniformKServer_RawPartition`, `UniformKServer_RawPath`, `UniformKServer_RawProgram`, `UniformKServer_RawRepresentation`, `UniformKServer_RawRowSelect`, `UniformKServer_RawRows`, `UniformKServer_RawTable`, `UniformKServer_RawTape`, `UniformKServer_RawTyped`, `UniformKServer_RawWords`, `UniformKServer_RealFlow`, `UniformKServer_RealFlowBounds`, `UniformKServer_RealFlowConvex`, `UniformKServer_RealFlowMixture`, `UniformKServer_RoundedMetricStep`, `UniformKServer_RoundedState`, `UniformKServer_RoundingChain`, `UniformKServer_RuntimeCertificate`, `UniformKServer_StackCoins`, `UniformKServer_StackCompiler`, `UniformKServer_StackPrimitive`, `UniformKServer_StackRun`, `UniformKServer_StackSimulation`, `UniformKServer_StackTape`, `UniformKServer_StarConstants`, `UniformKServer_StarEnergy`, `UniformKServer_SwitchFinite`, `UniformKServer_SwitchTracker`, `UniformKServer_TapeController`, `UniformKServer_TreeAllocationMovement`, `UniformKServer_TreeAncestry`, `UniformKServer_TreeDistribution`, `UniformKServer_TreeLeaves`, `UniformKServer_TreeParking`, `UniformKServer_TreeRankData`, `UniformKServer_TreeRounding`, `UniformKServer_TreeTransport`, `UniformKServer_TypedStack`, `UniformKServer_UniformParameters`, `UniformKServer_UniformSlope`, `UniformKServer_UniformWrapper`, `UniformKServer_WrapperMachine`, `UniformKServer_WrapperPrefix`, `UniformKServer_WrapperTransfer`.
--
--   **Imports.** It imports the published bundle `Def_UniformKServer`.
--
--   **Imported by** (directly, in this split): the bundles `Q220Uk005` and `Q220Uk006`.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_UniformKServer

section
-- module Solutions.Q220_UK.UniformKServer_Epochs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer

/-- The exact source horizon H. -/
def horizon (k M : ℕ) : ℕ := ∑ i ∈ Finset.range (M+1), k^i

end UniformKServer



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PositiveSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Removing zero atoms of a finite nonnegative law does not change any
weighted observable or conditional law on its support. This justifies the
positive-law presentation, without an assertion on impossible histories. -/
noncomputable section
namespace UniformKServer.PositiveSupport
open Finset
open scoped Classical
variable {Ω : Type*} [Fintype Ω]

abbrev Support (w : Ω → ℝ) := {ω : Ω // 0 < w ω}

theorem sum_support (w f : Ω → ℝ) (hz : ∀ ω, ¬ 0 < w ω → f ω = 0) :
    (∑ ω : Support w, f ω) = ∑ ω, f ω := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun ω => 0 < w ω) f
  have he : (∑ ω : {ω : Ω // ¬0 < w ω}, f ω) = 0 := by
    exact sum_eq_zero fun ω _ => hz ω ω.property
  rw [he,add_zero] at h
  exact h

theorem weighted_sum (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (f : Ω → ℝ) :
    (∑ ω : Support w, w ω*f ω) = ∑ ω, w ω*f ω := by
  apply sum_support w (fun ω => w ω*f ω)
  intro ω hω
  have hz : w ω=0 := le_antisymm (le_of_not_gt hω) (hw ω)
  simp only [hz,zero_mul]

theorem total (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (ht : ∑ ω, w ω=1) :
    (∑ ω : Support w, w ω)=1 := by
  have h := weighted_sum w hw (fun _ => 1)
  simpa only [mul_one,ht] using h

end UniformKServer.PositiveSupport

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LaminarTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

                                                                              
                                                                           
                                            
noncomputable section
namespace UniformKServer.LaminarTransport
open Finset
open scoped Classical
variable {I V E : Type*} [Fintype I] [Fintype E] [DecidableEq V]

def bit (C : Finset V) (x : V) : ℝ := if x∈C then 1 else 0
def cross (C : Finset V) (x y : V) : ℝ := |bit C x-bit C y|
def mass (C : Finset V) (a : I→V) : ℝ := ∑ i,bit C (a i)
def crossings (C : Finset V) (a b : I→V) (π : Equiv.Perm I) : ℝ :=
  ∑ i,cross C (a i) (b (π i))
def objective (C : E→Finset V) (a b : I→V) (π : Equiv.Perm I) : ℝ :=
  ∑ e,crossings (C e) a b π

def Laminar (C : E→Finset V) : Prop :=
  ∀ e f, C e⊆C f ∨ C f⊆C e ∨ Disjoint (C e) (C f)

theorem cross_swap_le {C B : Finset V} {x y u v : V}
    (hl : C⊆B ∨ B⊆C ∨ Disjoint C B)
    (hx : x∈C) (hy : y∉C) (hu : u∉C) (hv : v∈C) :
    cross B x v+cross B u y ≤ cross B x y+cross B u v := by
  rcases hl with h|h|h
  · have hxb := h hx
    have hvb := h hv
    by_cases hyb : y∈B <;> by_cases hub : u∈B <;>
      simp [cross,bit,hxb,hvb,hyb,hub]
  · have hyb : y∉B := fun h' => hy (h h')
    have hub : u∉B := fun h' => hu (h h')
    by_cases hxb : x∈B <;> by_cases hvb : v∈B <;>
      simp [cross,bit,hxb,hvb,hyb,hub]
  · have hxb : x∉B := fun h' => disjoint_left.mp h hx h'
    have hvb : v∉B := fun h' => disjoint_left.mp h hv h'
    by_cases hyb : y∈B <;> by_cases hub : u∈B <;>
      simp [cross,bit,hxb,hvb,hyb,hub]

theorem sum_swap (f : I→I→ℝ) (i j : I) (hij : i≠j) :
    (∑ u,f u (Equiv.swap i j u)) = (∑ u,f u u)+
      (f i j-f i i)+(f j i-f j j) := by
  classical
  have hp : ∀ u, f u (Equiv.swap i j u)=f u u+
      (if u=i then f i j-f i i else 0)+(if u=j then f j i-f j j else 0) := by
    intro u
    by_cases hi : u=i
    · subst u
      simp [hij]
    by_cases hj : u=j
    · subst u
      simp [Ne.symm hij]
    simp [Equiv.swap_apply_of_ne_of_ne hi hj,hi,hj]
  simp_rw [hp]
  simp only [sum_add_distrib]
  simp

theorem crossings_swap (C : Finset V) (a b : I→V) (π : Equiv.Perm I)
    (i j : I) (hij : i≠j) :
    crossings C a b ((Equiv.swap i j).trans π)=crossings C a b π+
      (cross C (a i) (b (π j))-cross C (a i) (b (π i)))+
      (cross C (a j) (b (π i))-cross C (a j) (b (π j))) := by
  exact sum_swap (fun u v=>cross C (a u) (b (π v))) i j hij

theorem cut_identity (C : Finset V) (a b : I→V) (π : Equiv.Perm I)
    (hno : ∀ i j,a i∈C → b (π i)∉C → a j∉C → b (π j)∈C → False) :
    crossings C a b π=|mass C a-mass C b| := by
  have hm : (∑ i,bit C (b (π i)))=∑ i,bit C (b i) := Equiv.sum_comp π (fun i=>bit C (b i))
  have hs : (∑ i,(bit C (a i)-bit C (b (π i))))=mass C a-mass C b := by
    rw [sum_sub_distrib,hm]
    rfl
  by_cases ho : ∃ i,a i∈C ∧ b (π i)∉C
  · obtain ⟨i,hi,hbi⟩ := ho
    have hp : ∀ j,0≤bit C (a j)-bit C (b (π j)) := by
      intro j
      by_cases hj : a j∈C <;> by_cases hbj : b (π j)∈C
      · simp [bit,hj,hbj]
      · simp [bit,hj,hbj]
      · exact (hno i j hi hbi hj hbj).elim
      · simp [bit,hj,hbj]
    change (∑ j,|bit C (a j)-bit C (b (π j))|)=_
    simp_rw [abs_of_nonneg (hp _)]
    rw [hs,abs_of_nonneg (by rw [←hs]; exact sum_nonneg (fun j _=>hp j))]
  · have hp : ∀ j,bit C (a j)-bit C (b (π j))≤0 := by
      intro j
      by_cases hj : a j∈C <;> by_cases hbj : b (π j)∈C
      · simp [bit,hj,hbj]
      · exact (ho ⟨j,hj,hbj⟩).elim
      · simp [bit,hj,hbj]
      · simp [bit,hj,hbj]
    change (∑ j,|bit C (a j)-bit C (b (π j))|)=_
    simp_rw [abs_of_nonpos (hp _)]
    rw [sum_neg_distrib,hs,abs_of_nonpos (by rw [←hs]; exact sum_nonpos (fun j _=>hp j))]

end UniformKServer.LaminarTransport

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BalancedStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.BalancedStar
open scoped symmDiff
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]

noncomputable def fraction (b : ι → ℝ) (i : ι) : ℝ := b i - ⌊b i⌋

omit [Fintype ι] [DecidableEq ι] in
theorem fraction_bounds (b : ι → ℝ) (i : ι) : fraction b i ∈ Set.Icc (0 : ℝ) 1 := by
  dsimp [fraction]
  constructor
  · exact sub_nonneg.mpr (Int.floor_le _)
  · exact (Int.fract_lt_one (b i)).le

end UniformKServer.BalancedStar

/-! One conditional update of the complete finite tree rounding process.
The arbitrary supported old law includes every correlation produced by earlier
ancestor roundings; no conditional independence is imposed. -/

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace UniformKServer.TreeRounding
open UniformKServer.BalancedStar
noncomputable section

structure Shape (n : ℕ) where
  parent : Fin (n+1) → Fin (n+1)
  earlier : ∀ v, v ≠ 0 → (parent v).val < v.val

abbrev Vertex (n : ℕ) := Fin (n+1)

def Children {n : ℕ} (S : Shape n) (v : Vertex n) :=
  {u : Vertex n // u ≠ 0 ∧ S.parent u = v}

instance instFintypeChildren {n : ℕ} (S : Shape n) (v : Vertex n) : Fintype (Children S v) :=
  by
  classical
  unfold Children
  infer_instance

def park {n : ℕ} (S : Shape n) (q : Vertex n → ℝ) (v : Vertex n) : ℝ :=
  q v - ∑ i : Children S v, q i.val

def intPark {n : ℕ} (S : Shape n) (x : Vertex n → ℤ) (v : Vertex n) : ℤ :=
  x v - ∑ i : Children S v, x i.val

structure Allocation {n : ℕ} (S : Shape n) (k : ℕ) where
  amount : Vertex n → ℝ
  nonneg : ∀ v, 0 ≤ amount v
  park_nonneg : ∀ v, 0 ≤ park S amount v
  root : amount 0 = k

structure Law where
  State : Type
  finite : Fintype State
  mass : State → ℝ
  nonneg : ∀ s, 0 ≤ mass s
  total : letI := finite; ∑ s, mass s = 1

attribute [instance] Law.finite

def mean (L : Law) (f : L.State → ℝ) : ℝ := ∑ s, L.mass s * f s

structure Extension (L : Law) (n : ℕ) where
  law : Law
  original : law.State → L.State
  preserves : ∀ f : L.State → ℝ, mean law (f ∘ original) = mean L f
  value : law.State → Vertex n → ℤ

def movement {n : ℕ} (S : Shape n) (w : Vertex n → ℝ)
    (L : Law) (X : L.State → Vertex n → ℤ) (E : Extension L n) : ℝ :=
  ∑ v : Vertex n, if v = 0 then 0 else
    w (S.parent v) * mean E.law (fun s => |(E.value s v : ℝ) - (X (E.original s) v : ℝ)|)

def variation {n k : ℕ} {S : Shape n} (w : Vertex n → ℝ)
    (a b : Allocation S k) : ℝ :=
  ∑ v : Vertex n, if v = 0 then 0 else
    w (S.parent v) * |b.amount v - a.amount v|


abbrev Local {n : ℕ} (S : Shape n) (v : Vertex n) := Children S v ⊕ Unit

def localReal {n : ℕ} (S : Shape n) (q : Vertex n → ℝ) (v : Vertex n) : Local S v → ℝ
  | .inl i => q i.val
  | .inr _ => park S q v

def localInt {n : ℕ} (S : Shape n) (x : Vertex n → ℤ) (v : Vertex n) : Local S v → ℤ
  | .inl i => x i.val
  | .inr _ => intPark S x v

theorem sum_localReal {n : ℕ} (S : Shape n) (q : Vertex n → ℝ) (v : Vertex n) :
    ∑ i, localReal S q v i = q v := by
  rw [Fintype.sum_sum_type]
  simp [localReal, park]

theorem sum_localInt {n : ℕ} (S : Shape n) (x : Vertex n → ℤ) (v : Vertex n) :
    ∑ i, localInt S x v i = x v := by
  rw [Fintype.sum_sum_type]
  simp [localInt, intPark]

theorem cast_intPark {n : ℕ} (S : Shape n) (x : Vertex n → ℤ) (v : Vertex n) :
    (intPark S x v : ℝ) = (x v : ℝ) - ∑ i : Children S v, (x i.val : ℝ) := by
  simp [intPark]

theorem mean_sub (L : Law) (f g : L.State → ℝ) :
    mean L (fun s => f s-g s) = mean L f-mean L g := by
  simp [mean,mul_sub,Finset.sum_sub_distrib]

theorem mean_sum {ι : Type} [Fintype ι] (L : Law) (f : ι → L.State → ℝ) :
    mean L (fun s => ∑ i, f i s) = ∑ i, mean L (f i) := by
  simp only [mean,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mean_congr (L : Law) {f g : L.State → ℝ} (h : ∀ s, f s = g s) :
    mean L f = mean L g := by
  simp only [mean,h]

theorem mean_const (L : Law) (c : ℝ) : mean L (fun _ => c) = c := by
  rw [mean,← Finset.sum_mul,L.total,one_mul]

theorem mean_mono (L : Law) {f g : L.State → ℝ} (h : ∀ s, f s ≤ g s) :
    mean L f ≤ mean L g :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (L.nonneg s)

theorem mean_nonneg (L : Law) {f : L.State → ℝ} (h : ∀ s, 0 ≤ f s) :
    0 ≤ mean L f :=
  Finset.sum_nonneg fun s _ => mul_nonneg (L.nonneg s) (h s)


def assigned {n : ℕ} (S : Shape n) (s : ℕ) (u : Vertex n) : Prop :=
  u = 0 ∨ (S.parent u).val < s

def localMovement {n : ℕ} (S : Shape n) (L : Law)
    (X : L.State → Vertex n → ℤ) (E : Extension L n) (v : Vertex n) : ℝ :=
  mean E.law (fun s => ∑ i : Local S v,
    |(localInt S (E.value s) v i : ℝ) - (localInt S (X (E.original s)) v i : ℝ)|)

def nodeMovement {n : ℕ} (L : Law) (X : L.State → Vertex n → ℤ)
    (E : Extension L n) (v : Vertex n) : ℝ :=
  mean E.law (fun s => |(E.value s v : ℝ) - (X (E.original s) v : ℝ)|)

def localVariation {n k : ℕ} {S : Shape n} (a b : Allocation S k) (v : Vertex n) : ℝ :=
  ∑ i : Local S v, |localReal S a.amount v i - localReal S b.amount v i|

def assignChildren {n : ℕ} (S : Shape n) (v : Vertex n)
    (old : Vertex n → ℤ) (y : Local S v → ℤ) (u : Vertex n) : ℤ := by
  classical
  exact if h : u ≠ 0 ∧ S.parent u = v then y (.inl ⟨u,h⟩) else old u

theorem assigned_current {n : ℕ} (S : Shape n) (v : Vertex n) : assigned S v.val v := by
  by_cases hv : v=0
  · exact Or.inl hv
  · exact Or.inr (S.earlier v hv)

theorem assign_unchanged {n : ℕ} (S : Shape n) (v : Vertex n)
    (old : Vertex n → ℤ) (y : Local S v → ℤ) (u : Vertex n)
    (hu : u = 0 ∨ S.parent u ≠ v) : assignChildren S v old y u = old u := by
  classical
  rcases hu with rfl | hu
  · simp [assignChildren]
  · simp [assignChildren,hu]

theorem assign_earlier {n : ℕ} (S : Shape n) (v : Vertex n)
    (old : Vertex n → ℤ) (y : Local S v → ℤ) (u : Vertex n) (hu : u.val ≤ v.val) :
    assignChildren S v old y u = old u := by
  apply assign_unchanged
  by_cases hz : u=0
  · exact Or.inl hz
  · right
    intro he
    have := S.earlier u hz
    rw [he] at this
    omega

theorem assign_old_local {n : ℕ} (S : Shape n) (v : Vertex n)
    (old : Vertex n → ℤ) (y : Local S v → ℤ) (j : Vertex n) (hj : j.val < v.val) :
    ∀ i, localInt S (assignChildren S v old y) j i = localInt S old j i := by
  have hne : j ≠ v := by intro he; subst j; exact lt_irrefl _ hj
  have hc (i : Children S j) : assignChildren S v old y i.val = old i.val :=
    assign_unchanged S v old y i.val (Or.inr (by rw [i.property.2]; exact hne))
  intro i
  cases i with
  | inl i => exact hc i
  | inr u => simp only [localInt,intPark,assign_earlier S v old y j hj.le,hc]

theorem old_local_mean {n k : ℕ} (S : Shape n) (a : Allocation S k)
    (L : Law) (X : L.State → Vertex n → ℤ)
    (hm : ∀ v, mean L (fun s => (X s v : ℝ)) = a.amount v)
    (E : Extension L n) (v : Vertex n) :
    ∀ i, mean E.law (fun s => (localInt S (X (E.original s)) v i : ℝ)) =
      localReal S a.amount v i := by
  intro i
  rw [show (fun s => (localInt S (X (E.original s)) v i : ℝ)) =
    (fun s => (localInt S (X s) v i : ℝ)) ∘ E.original from rfl,E.preserves]
  cases i with
  | inl i => exact hm i.val
  | inr u =>
    simp only [localInt,cast_intPark,mean_sub,mean_sum,hm,localReal,park]


theorem sum_children {n : ℕ} (S : Shape n) (v : Vertex n) (f : Vertex n → ℝ) :
    ∑ i : Children S v, f i.val = ∑ u, if u ≠ 0 ∧ S.parent u = v then f u else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by intro u; simp) f).symm

theorem weighted_children {n : ℕ} (S : Shape n) (w f : Vertex n → ℝ) :
    (∑ v, w v * ∑ i : Children S v, f i.val) =
      ∑ u, if u=0 then 0 else w (S.parent u)*f u := by
  classical
  have he (v : Vertex n) : w v * (∑ i : Children S v, f i.val) =
      ∑ u, if u ≠ 0 ∧ S.parent u = v then w v*f u else 0 := by
    rw [sum_children S v f,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u=0
  · simp [hu]
  · simp [hu,eq_comm]

theorem localVariation_le {n k : ℕ} (S : Shape n) (a b : Allocation S k)
    (v : Vertex n) :
    localVariation a b v ≤ 2*(∑ i : Children S v, |b.amount i.val-a.amount i.val|) +
      |b.amount v-a.amount v| := by
  have hp : |park S a.amount v - park S b.amount v| ≤
      |a.amount v-b.amount v| + ∑ i : Children S v, |a.amount i.val-b.amount i.val| := by
    calc
      _ = |(a.amount v-b.amount v) -
        ∑ i : Children S v, (a.amount i.val-b.amount i.val)| := by
          congr 1
          simp only [park,Finset.sum_sub_distrib]
          ring
      _ ≤ |a.amount v-b.amount v| + |∑ i : Children S v,
          (a.amount i.val-b.amount i.val)| := abs_sub _ _
      _ ≤ _ := by
        have ht := Finset.abs_sum_le_sum_abs
          (fun i : Children S v => a.amount i.val-b.amount i.val) Finset.univ
        linarith
  dsimp only [localVariation]
  rw [Fintype.sum_sum_type]
  simp only [localReal,Fintype.sum_unique]
  simp_rw [abs_sub_comm (b.amount _) (a.amount _)]
  linarith

theorem childMovement_le {n : ℕ} (S : Shape n) (L : Law)
    (X : L.State → Vertex n → ℤ) (E : Extension L n) (v : Vertex n) :
    (∑ i : Children S v, nodeMovement L X E i.val) ≤ localMovement S L X E v := by
  dsimp only [nodeMovement,localMovement]
  rw [← mean_sum]
  apply mean_mono
  intro s
  rw [Fintype.sum_sum_type]
  simp only [localInt,Fintype.sum_unique]
  exact le_add_of_nonneg_right (abs_nonneg _)

end
end UniformKServer.TreeRounding

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeParking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! Park conservation, subtree-cut capacities, and weighted park variation. -/
noncomputable section
namespace UniformKServer.TreeParking
open Finset TreeRounding
open scoped Classical
variable {n k : ℕ} {S : Shape n}

theorem weighted_identity (q g : Vertex n → ℝ) :
    (∑ v, g v*park S q v)=∑ v, (g v*q v-if v=0 then 0 else g (S.parent v)*q v) := by
  simp only [park,mul_sub,sum_sub_distrib]
  rw [weighted_children]

theorem total (a : Allocation S k) : (∑ v, park S a.amount v)=k := by
  have h := weighted_identity (S:=S) a.amount (fun _ => 1)
  simp only [one_mul] at h
  rw [h]
  have he (v : Vertex n) : a.amount v-(if v=0 then 0 else a.amount v)=if v=0 then a.amount 0 else 0 := by
    split_ifs with hv
    · simp [hv]
    · simp
  simp only [he,sum_ite_eq',mem_univ,ite_true, if_true,a.root]

def boundary (A : Finset (Vertex n)) : Finset (Vertex n) := A.filter (fun v => v=0 ∨ S.parent v ∉ A)

theorem cut (a : Allocation S k) (A : Finset (Vertex n))
    (hc : ∀ v, v ≠ 0 → S.parent v ∈ A → v ∈ A) :
    (∑ v ∈ A, park S a.amount v)=∑ v ∈ boundary (S:=S) A, a.amount v := by
  have h := weighted_identity (S:=S) a.amount (fun v => if v ∈ A then 1 else 0)
  simp only [ite_mul,one_mul,zero_mul] at h
  have he (v : Vertex n) :
      (if v ∈ A then a.amount v else 0)-(if v=0 then 0 else if S.parent v ∈ A then a.amount v else 0)=
      if v ∈ boundary (S:=S) A then a.amount v else 0 := by
    by_cases h0 : v=0
    · simp [h0,boundary]
    · by_cases hv : v ∈ A
      · by_cases hp : S.parent v ∈ A <;> simp [h0,hv,hp,boundary]
      · have hp : S.parent v ∉ A := fun hp => hv (hc v h0 hp)
        simp [h0,hv,hp,boundary]
  simp_rw [he] at h
  simpa only [←sum_filter,filter_mem_eq_inter,univ_inter] using h

theorem pointwise_variation (a b : Allocation S k) (v : Vertex n) :
    |park S b.amount v-park S a.amount v| ≤
      |b.amount v-a.amount v|+∑ i : Children S v, |b.amount i.val-a.amount i.val| := by
  have he : park S b.amount v-park S a.amount v=
      (b.amount v-a.amount v)-∑ i : Children S v, (b.amount i.val-a.amount i.val) := by
    simp only [park,sum_sub_distrib] <;> ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add_right (abs_sum_le_sum_abs _ _) _)

end UniformKServer.TreeParking

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeAncestry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Literal ancestry in a finite ordered rooted tree, including all internal
parks and the root. -/
noncomputable section
namespace UniformKServer.TreeAncestry
open Finset TreeRounding TreeParking
open scoped Classical
variable {n k : ℕ} {S : Shape n}

def edge (S : Shape n) (u v : Vertex n) : Prop := v ≠ 0 ∧ S.parent v=u
def descends (S : Shape n) : Vertex n → Vertex n → Prop := Relation.ReflTransGen (edge S)
def subtree (S : Shape n) (u : Vertex n) : Finset (Vertex n) := univ.filter (descends S u)

def depth (S : Shape n) (v : Vertex n) : ℕ := if hv : v=0 then 0 else depth S (S.parent v)+1
termination_by v.val
decreasing_by exact S.earlier v hv

theorem desc_refl (v : Vertex n) : descends S v v := .refl

theorem desc_tail {u v w : Vertex n} (h : descends S u v) (hw : w ≠ 0) (hp : S.parent w=v) :
    descends S u w := h.tail ⟨hw,hp⟩

theorem desc_val {u v : Vertex n} (h : descends S u v) : u.val ≤ v.val := by
  induction h with
  | refl => rfl
  | @tail v w h e ih =>
    have hh := S.earlier w e.1
    rw [e.2] at hh
    omega

theorem subtree_closed (u v : Vertex n) (hv : v ≠ 0) (hp : S.parent v ∈ subtree S u) :
    v ∈ subtree S u := by
  simp only [subtree,mem_filter,mem_univ,true_and] at *
  exact desc_tail hp hv rfl

theorem subtree_boundary (u : Vertex n) : boundary (S:=S) (subtree S u)={u} := by
  ext v
  simp only [boundary,mem_filter,subtree,mem_univ,true_and,mem_singleton]
  constructor
  · rintro ⟨h,hv | hp⟩
    · subst v
      have hh := desc_val h
      apply Fin.ext
      exact (Nat.le_zero.mp hh).symm
    · rcases h.cases_tail with hv | ⟨w,hw,e⟩
      · exact hv
      · exact (hp (e.2.symm ▸ hw)).elim
  · intro hv
    subst v
    refine ⟨desc_refl u,?_⟩
    by_cases hu : u=0
    · exact Or.inl hu
    · right
      intro h
      have hh := desc_val h
      have he := S.earlier u hu
      omega

theorem subtree_total (a : Allocation S k) (u : Vertex n) :
    (∑ v ∈ subtree S u, park S a.amount v)=a.amount u := by
  rw [cut a (subtree S u) (subtree_closed u),subtree_boundary,sum_singleton]

end UniformKServer.TreeAncestry

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Unique child on a leaf path and conservation of literal hidden counts. -/
noncomputable section
namespace UniformKServer.TreeLeaves
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {n : ℕ} {S : Shape n}

def leaf (v : Vertex n) : Prop := ∀ _u : Children S v, False

theorem root_descends (v : Vertex n) : descends S 0 v := by
  induction v using WellFounded.induction (measure Fin.val).wf with
  | h v ih =>
    by_cases hv : v=0
    · subst v; exact desc_refl 0
    · exact desc_tail (ih (S.parent v) (S.earlier v hv)) hv rfl

def indicator (v w : Vertex n) : ℕ := if descends S v w then 1 else 0

def count {k : ℕ} (p : Fin k → Vertex n) (v : Vertex n) : ℕ := ∑ a, indicator (S:=S) v (p a)

theorem count_le {k : ℕ} (p : Fin k → Vertex n) (v : Vertex n) : count (S:=S) p v ≤ k := by
  calc
    _ ≤ ∑ _ : Fin k, 1 := sum_le_sum fun a _ => by unfold indicator; split_ifs <;> omega
    _ = _ := by simp

end UniformKServer.TreeLeaves

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The laminar cuts of the literal finite tree; exact matching transport and
an occupied-endpoint separating edge below a deepest common ancestor. -/
noncomputable section
namespace UniformKServer.TreeAncestry
open Finset TreeRounding
open scoped Classical
variable {n : ℕ} {S : Shape n}

def pathCost (w : Vertex n→ℝ) (u v : Vertex n) : ℝ :=
  ∑ c : Vertex n,if c=0 then 0 else
    w (S.parent c)*LaminarTransport.cross (subtree S c) u v

end UniformKServer.TreeAncestry

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_IntegerParks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! A rounded, consistent hierarchy contains exactly k integer parks. Their
literal labeled enumeration has the prescribed subtree counts. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset TreeAncestry BalancedStar
open scoped Classical
variable {n k : ℕ} {S : Shape n}

structure Realization (x : Vertex n→ℤ) where
  tuple : Fin k→Vertex n
  sum : ∀ f : Vertex n→ℝ,(∑ i,f (tuple i))=∑ v,(intPark S x v:ℝ)*f v
  positive : ∀ i,0 < intPark S x (tuple i)

end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParkedTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! The literal one-step matching realization of joint tree rounding. The
coincident-label charge is restricted to labels occupied at both times. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X : Type*} [PseudoMetricSpace X]

def Realization.permute {x : Vertex n→ℤ} (R : Realization (k:=k) (S:=S) x)
    (π : Equiv.Perm (Fin k)) : Realization (k:=k) (S:=S) x where
  tuple i := R.tuple (π i)
  sum f := (Equiv.sum_comp π (fun i=>f (R.tuple i))).trans (R.sum f)
  positive i := R.positive (π i)

def commonDistance (a b : Allocation S k) (f g : Vertex n→X) (v : Vertex n) : ℝ :=
  if 0<park S a.amount v ∧ 0<park S b.amount v then dist (f v) (g v) else 0

theorem commonDistance_nonneg (a b : Allocation S k) (f g : Vertex n→X) (v : Vertex n) :
    0 ≤ commonDistance a b f g v := by unfold commonDistance; split <;> positivity

theorem mean_intPark {a : Allocation S k} (L : Law) (x : L.State→Vertex n→ℤ)
    (hm : ∀ v,mean L (fun s=>(x s v:ℝ))=a.amount v) (v : Vertex n) :
    mean L (fun s=>(intPark S (x s) v:ℝ))=park S a.amount v := by
  simp only [cast_intPark]
  rw [mean_sub,mean_sum,hm]
  unfold park
  congr 1
  exact sum_congr rfl (fun c _=>hm c.val)

end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RoundedMetricStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! A causal one-step extension with a literal labeled metric configuration.
No independence between old parent and child counts is imposed. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X : Type*} [PseudoMetricSpace X]

theorem mean_add (L : Law) (f g : L.State→ℝ) :
    mean L (fun s=>f s+g s)=mean L f+mean L g := by
  simp only [mean,mul_add,sum_add_distrib]

theorem mean_mul (L : Law) (c : ℝ) (f : L.State→ℝ) :
    mean L (fun s=>c*f s)=c*mean L f := by
  simp only [mean,mul_sum]
  exact sum_congr rfl (fun s _=>by ring)

end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RoundedState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! A fixed finite state space for the causal rounding kernels. It records
only bounded integer subtree counts, not an assumed distribution. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n}

def bounded (x : Vertex n→Fin (k+1)) : Vertex n→ℤ := fun v=>(x v).val

abbrev State (S : Shape n) (k : ℕ) := {p : (Vertex n→Fin (k+1)) × (Fin k→Vertex n) //
  (∀ f : Vertex n→ℝ,(∑ i,f (p.2 i))=∑ v,(intPark S (bounded p.1) v:ℝ)*f v) ∧
    ∀ i,0 < intPark S (bounded p.1) (p.2 i)}

def State.value (s : State S k) : Vertex n→ℤ := bounded s.val.1

def State.realization (s : State S k) : Realization (k:=k) (S:=S) s.value :=
  ⟨s.val.2,s.property.1,s.property.2⟩

end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Initial and next rounded configurations live in one fixed finite alphabet;
conditional extension states are eliminated by exact finite push-forward. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset
open scoped Classical
variable {n k : ℕ} {S : Shape n}

variable {X : Type} [PseudoMetricSpace X]

def stateDistance (f g : Vertex n→X) (s t : State S k) : ℝ :=
  ∑ i,dist (f (s.realization.tuple i)) (g (t.realization.tuple i))

end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RoundingChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Chosen joint repairs form one adapted Markov chain on a fixed finite state
space. The choices use the old distribution and current geometric data only. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [PseudoMetricSpace X]

structure ChainInput (S : Shape n) (k : ℕ) (X Ω : Type) [PseudoMetricSpace X] where
  allocation : ℕ→Ω→Allocation S k
  anchors : ℕ→Ω→Vertex n→X
  filtration : ℕ→Setoid Ω
  refines : ∀ t ω v,(filtration (t+1)).r ω v → (filtration t).r ω v
  allocation_causal : ∀ t ω v,(filtration t).r ω v → allocation t ω=allocation t v
  anchors_causal : ∀ t ω v,(filtration t).r ω v → anchors t ω=anchors t v
  weight : Vertex n→ℝ
  weight_nonneg : ∀ v,0≤weight v
  weight_separated : ∀ v,v≠0 → 22*weight v≤weight (S.parent v)
  factor : ℝ
  factor_nonneg : 0≤factor
  geometry : ∀ t ω u v,0<park S (allocation t ω).amount u →
    0<park S (allocation (t+1) ω).amount v → u≠v →
    dist (anchors t ω u) (anchors (t+1) ω v)≤factor*TreeAncestry.pathCost (S:=S) weight u v

end UniformKServer.TreeRounding

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RankedTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! A finite ranked rooted tree is enumerated in increasing rank and converted
to the ordered finite shapes used by the allocator and rounding proofs. -/
noncomputable section
namespace UniformKServer.RankedTree
open TreeRounding TreeAncestry
open scoped Classical

structure Data (V : Type*) where
  root : V
  parent : V → V
  level : V → ℕ
  level_root : level root=0
  level_zero : ∀ v, level v=0 → v=root
  step : ∀ v, v ≠ root → level (parent v)+1=level v

variable {V : Type*} [Fintype V]

def size (_T : Data V) : ℕ := Fintype.card V-1

theorem size_card (T : Data V) : Fintype.card V=size T+1 := by
  have : Nonempty V := ⟨T.root⟩
  have hp := Fintype.card_pos_iff.mpr this
  unfold size
  omega

def orderKey (T : Data V) (v : V) : Lex (ℕ × ℕ) := toLex (T.level v,(Fintype.equivFin V v).val)

theorem orderKey_injective (T : Data V) : Function.Injective (orderKey T) := by
  intro u v he
  have hh : (Fintype.equivFin V u).val=(Fintype.equivFin V v).val := congrArg (fun p => (ofLex p).2) he
  exact (Fintype.equivFin V).injective (Fin.ext hh)

abbrev order (T : Data V) : LinearOrder V := LinearOrder.lift' (orderKey T) (orderKey_injective T)

def chart (T : Data V) : Vertex (size T) ≃ V :=
  letI := order T
  (Fintype.orderIsoFinOfCardEq V (size_card T)).toEquiv

theorem key_less (T : Data V) (u v : V) (h : T.level u < T.level v) : orderKey T u < orderKey T v :=
  Prod.Lex.left _ _ h

theorem vertex_less (T : Data V) (u v : V) (h : T.level u < T.level v) :
    (chart T).symm u < (chart T).symm v := by
  let := order T
  exact (Fintype.orderIsoFinOfCardEq V (size_card T)).symm.strictMono (key_less T u v h)

theorem chart_zero (T : Data V) : chart T 0=T.root := by
  by_contra h
  have hp : 0 < T.level (chart T 0) := by
    by_contra hp
    exact h (T.level_zero _ (by omega))
  have hh := vertex_less T T.root (chart T 0) (by rw [T.level_root]; exact hp)
  simp only [Equiv.symm_apply_apply] at hh
  exact (Nat.not_lt_zero _ hh).elim

theorem root_vertex (T : Data V) : (chart T).symm T.root=0 := by rw [←chart_zero T]; exact (chart T).symm_apply_apply 0

end UniformKServer.RankedTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PrefixTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! The full fixed finite wordPrefix universe. Its vertices include every formal
wordPrefix, without deleting presently empty branches. -/
noncomputable section
namespace UniformKServer.PrefixTree
open TreeRounding TreeAncestry TreeLeaves
open scoped Classical

abbrev Word (A : Type*) (J : ℕ) := Σ d : Fin (J+1), Fin d.val → A
variable {A : Type*} [Fintype A] {J : ℕ}

def root : Word A J := ⟨0,Fin.elim0⟩
def parent (v : Word A J) : Word A J :=
  if h : v.1.val=0 then root else
    ⟨⟨v.1.val-1,by have := v.1.isLt; omega⟩,fun i => v.2 ⟨i.val,by have hi := i.isLt; change i.val < v.1.val-1 at hi; omega⟩⟩

def wordPrefix (p : Fin J → A) (d : ℕ) (hd : d ≤ J) : Word A J :=
  ⟨⟨d,by omega⟩,fun i => p ⟨i.val,by omega⟩⟩

end UniformKServer.PrefixTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PrefixMovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Height-free deterministic conversion of coordinate-key disagreements into
weighted subtree-count variation on the literal full prefix universe. -/
noncomputable section
namespace UniformKServer.PrefixMovement
open Finset TreeRounding TreeAncestry TreeLeaves PrefixTree
open scoped Classical
variable {A : Type*} [Fintype A] {J : ℕ}

def diff {T : Type*} (a b : T) : ℝ := if a=b then 0 else 1

theorem diff_nonneg {T : Type*} (a b : T) : 0 ≤ diff a b := by
  unfold diff; split_ifs <;> norm_num

theorem tail_bound (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i) (hdec : ∀ i, 2*r (i+1) ≤ r i)
    (m N : ℕ) : (∑ i ∈ range N, r (m+i)) ≤ 2*r m := by
  induction N generalizing m with
  | zero => simp only [sum_range_zero]; exact mul_nonneg (by norm_num) (hr m)
  | succ N ih =>
    rw [sum_range_succ']
    have hh := ih (m+1)
    have he : (∑ x ∈ range N, r (m+(x+1)))=∑ x ∈ range N, r (m+1+x) := by
      apply sum_congr rfl
      intro x _
      congr 1; omega
    rw [he]
    simp only [Nat.add_zero]
    linarith [hdec m]

def edgeWeight (r : ℕ → ℝ) (d : ℕ) : ℝ := if d=0 then 0 else r (d-1)

end UniformKServer.PrefixMovement

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RankTracking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

                                                                    
                                                                          
                                                                              
                                                                     
namespace UniformKServer.RankTracking

variable {Ω : Type*} [Fintype Ω]

def potential (p r : ℝ) : ℝ := p * (1 - p) + (p - r) ^ 2

theorem potential_range {p r : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : potential p r ∈ Set.Icc (0 : ℝ) 1 := by
  rcases hp with ⟨hp, hp'⟩
  rcases hr with ⟨hr, hr'⟩
  constructor
  · exact add_nonneg (mul_nonneg hp (sub_nonneg.mpr hp')) (sq_nonneg _)
  · unfold potential
    have h₁ := mul_nonneg (sub_nonneg.mpr hp') (mul_nonneg hr (sub_nonneg.mpr hr'))
    have h₂ := mul_nonneg hp (mul_nonneg hr (sub_nonneg.mpr hr'))
    have h₃ := mul_nonneg (sub_nonneg.mpr hp') (sub_nonneg.mpr hr')
    have h₄ := mul_nonneg hp hr
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hp')]

theorem reset_identity (p p' pminus r r' : ℝ) (hr : r' = r ∨ r' = p') :
    potential p' r' + (r' - r)^2 = potential p r +
      (1 - 2*r) * (pminus - p) + (1 - 2*r) * (p' - pminus) := by
  rcases hr with h | h <;> subst r' <;> unfold potential <;> ring

theorem drift_slope {r d : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    (1 - 2*r) * d ≤ |d| := by
  have h : |1 - 2*r| ≤ 1 := abs_le.mpr ⟨by linarith [hr.2], by linarith [hr.1]⟩
  calc
    (1 - 2*r)*d ≤ |(1 - 2*r)*d| := le_abs_self _
    _ = |1 - 2*r| * |d| := abs_mul _ _
    _ ≤ 1 * |d| := mul_le_mul_of_nonneg_right h (abs_nonneg _)
    _ = |d| := one_mul _

theorem square_root_failure_ordered {a b ξ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hξ : 0 < ξ) (hξ' : ξ < 1/2) (hfail : (1+ξ)*a < b) :
    ξ * |a-b| ≤ 5*(Real.sqrt a - Real.sqrt b)^2 := by
  have ha' := Real.sqrt_nonneg a
  have hb' := Real.sqrt_nonneg b
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hab : a < b := by nlinarith
  have hdiff : 0 ≤ Real.sqrt b - Real.sqrt a := by
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt hab.le)
  have hsum : 0 < Real.sqrt b + Real.sqrt a := by
    have : 0 < Real.sqrt b := Real.sqrt_pos.mpr (by linarith)
    linarith
  have hprod : (Real.sqrt b+Real.sqrt a)*(Real.sqrt b-Real.sqrt a) = b-a := by
    nlinarith
  have hnorm : (Real.sqrt b+Real.sqrt a)^2 ≤ 2*(a+b) := by
    nlinarith [sq_nonneg (Real.sqrt b - Real.sqrt a)]
  have hnorm' := mul_le_mul_of_nonneg_left hnorm hξ.le
  have hsmall := mul_le_mul_of_nonneg_right hξ'.le (sub_nonneg.mpr hab.le)
  have hsq : ξ*(Real.sqrt b+Real.sqrt a)^2 ≤ 5*(b-a) := by
    nlinarith
  have hratio : ξ*(Real.sqrt b+Real.sqrt a) ≤ 5*(Real.sqrt b-Real.sqrt a) := by
    apply (mul_le_mul_iff_right₀ hsum).mp
    nlinarith [hprod]
  have hfin := mul_le_mul_of_nonneg_right hratio hdiff
  rw [abs_of_neg (sub_neg.mpr hab)]
  nlinarith [hprod]

theorem square_root_failure {a b ξ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hξ : 0 < ξ) (hξ' : ξ < 1/2)
    (hfail : ¬ (a ≤ (1+ξ)*b ∧ b ≤ (1+ξ)*a)) :
    ξ * |a-b| ≤ 5*(Real.sqrt a - Real.sqrt b)^2 := by
  by_cases hab : a ≤ (1+ξ)*b
  · have h : (1+ξ)*a < b := lt_of_not_ge (fun h => hfail ⟨hab, h⟩)
    exact square_root_failure_ordered ha hb hξ hξ' h
  · have h := square_root_failure_ordered hb ha hξ hξ' (lt_of_not_ge hab)
    simpa only [abs_sub_comm b a, sub_sq_comm (Real.sqrt b) (Real.sqrt a)] using h

end UniformKServer.RankTracking

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RankFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

                                                                      
                                                          
noncomputable section
namespace UniformKServer.RankFunctions

theorem sqrt_diff_aux {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hroot : 1 ≤ Real.sqrt x+Real.sqrt y) :
    |Real.sqrt x-Real.sqrt y| ≤ |x-y| := by
  have hid : |Real.sqrt x-Real.sqrt y| *(Real.sqrt x+Real.sqrt y) = |x-y| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)), ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]
  have := abs_nonneg (Real.sqrt x-Real.sqrt y)
  nlinarith

end UniformKServer.RankFunctions

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RankData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

/-! Exact size rank and held core flags from companion §03. -/
noncomputable section
namespace UniformKServer.RankData
open RankFunctions

variable {Ω : Type*} [Fintype Ω]

variable {A : Type*} [Fintype A]
def coreMass (c : A → Bool) (p : A → ℝ) : ℝ := ∑ a, if c a then p a else 0

end UniformKServer.RankData

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EntropyCredit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Exact tangent credit for the source's multiplicative held-size tracker. -/
noncomputable section
namespace UniformKServer.EntropyCredit

def tangent (u s : ℝ) : ℝ := u-(1+Real.log u)*s

def remainder (u M x : ℝ) : ℝ := x*(Real.log x-Real.log u)-x+u-(x-u)^2/(2*M)

theorem remainder_deriv (u M x : ℝ) (hx : 0 < x) (hu : 0 < u) (hM : 0 < M) :
    HasDerivAt (remainder u M) (Real.log (x/u)-(x-u)/M) x := by
  have h := (((hasDerivAt_id x).mul ((Real.hasDerivAt_log hx.ne').sub_const (Real.log u))).sub
    (hasDerivAt_id x)).add_const u
  have hg := h.sub ((((hasDerivAt_id x).sub_const u).pow 2).div_const (2*M))
  apply hg.congr_deriv
  rw [Real.log_div hx.ne' hu.ne']
  simp only [id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,one_mul]
  field_simp
  ring

theorem credit (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    (s-u)^2/(2*max s u) ≤ tangent u s-tangent s s := by
  by_cases hsu : s ≤ u
  · have hd (x : ℝ) (hx : x ∈ Set.Icc s u) := remainder_deriv u u x (lt_of_lt_of_le hs hx.1) hu hu
    have hc : ContinuousOn (remainder u u) (Set.Icc s u) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
    have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s u) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) (fun x hx => by
        have hx' := interior_subset hx
        have hp : 0 < x/u := div_pos (lt_of_lt_of_le hs hx'.1) hu
        have hl := Real.log_le_sub_one_of_pos hp
        have he : x/u-1=(x-u)/u := by field_simp
        rw [he] at hl
        linarith)
    have he := hm (show s ∈ Set.Icc s u from ⟨le_rfl,hsu⟩)
      (show u ∈ Set.Icc s u from ⟨hsu,le_rfl⟩) hsu
    simp only [remainder,sub_self,mul_zero,zero_div,zero_sub,sub_zero,zero_pow,
      ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] at he
    rw [max_eq_right hsu]
    unfold tangent
    nlinarith
  · have hus := le_of_not_ge hsu
    have hd (x : ℝ) (hx : x ∈ Set.Icc u s) := remainder_deriv u s x (lt_of_lt_of_le hu hx.1) hu hs
    have hc : ContinuousOn (remainder u s) (Set.Icc u s) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
    have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc u s) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) (fun x hx => by
        have hx' := interior_subset hx
        have hxp : 0 < x := lt_of_lt_of_le hu hx'.1
        have hl := Real.one_sub_inv_le_log_of_pos (div_pos hxp hu)
        have hk : (x-u)/s ≤ (x-u)/x := div_le_div_of_nonneg_left (sub_nonneg.mpr hx'.1) hxp hx'.2
        have he : 1-(x/u)⁻¹=(x-u)/x := by field_simp
        rw [he] at hl
        linarith)
    have he := hm (show u ∈ Set.Icc u s from ⟨le_rfl,hus⟩)
      (show s ∈ Set.Icc u s from ⟨hus,le_rfl⟩) hus
    simp only [remainder,sub_self,mul_zero,zero_div,zero_sub,sub_zero,zero_pow,
      ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] at he
    rw [max_eq_left hus]
    unfold tangent
    nlinarith


theorem relative_credit (s u : ℝ) (hs : 0 < s) (hu : 0 < u)
    (hfail : ¬ (s ≤ (6/5)*u ∧ u ≤ (6/5)*s)) :
    s+u ≤ 144*(tangent u s-tangent s s) := by
  let M := max s u
  have hM : 0 < M := lt_of_lt_of_le hs (le_max_left _ _)
  have hc := (div_le_iff₀ (show 0 < 2*M by positivity)).mp (credit s u hs hu)
  have hgap : M/6 ≤ |s-u| := by
    by_cases hsu : s ≤ u
    · have hfail' : (6/5)*s < u := by
        by_contra hh
        apply hfail
        constructor <;> nlinarith
      rw [abs_of_nonpos (sub_nonpos.mpr hsu)]
      dsimp [M]
      rw [max_eq_right hsu]
      linarith
    · have hus : u ≤ s := le_of_not_ge hsu
      have hfail' : (6/5)*u < s := by
        by_contra hh
        apply hfail
        constructor <;> nlinarith
      rw [abs_of_nonneg (sub_nonneg.mpr hus)]
      dsimp [M]
      rw [max_eq_left hus]
      linarith
  have hg := mul_self_le_mul_self (show 0 ≤ M/6 by positivity) hgap
  rw [←sq,←sq,sq_abs] at hg
  have hh : M*M ≤ (72*(tangent u s-tangent s s))*M := by nlinarith
  have hb := (mul_le_mul_iff_left₀ hM).mp hh
  have hsu : s+u ≤ 2*M := by dsimp [M] <;> linarith [le_max_left s u,le_max_right s u]
  linarith

end UniformKServer.EntropyCredit

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_KeySizeTracker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! The unreset affine entropy tracker for each fixed heavy-key slot. Filtering
is charged at the old measurable coefficient on every step. -/
noncomputable section
namespace UniformKServer.KeySizeTracker
open Finset RankTracking EntropyCredit
open scoped Classical
variable {Ω : Type*} [Fintype Ω]

variable {K : ℝ}

def ell (K : ℝ) : ℝ := 1+Real.log K

theorem slope_bound (K u : ℝ) (_hK : 1 ≤ K) (hu : u ∈ Set.Icc 1 K) :
    |-(1+Real.log u)| ≤ ell K := by
  have hup : 0 < u := by linarith [hu.1]
  have hl := Real.log_nonneg hu.1
  have hm := Real.log_le_log hup hu.2
  rw [abs_neg,abs_of_nonneg (by linarith : 0 ≤ 1+Real.log u)]
  unfold ell
  linarith

end UniformKServer.KeySizeTracker

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParkCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Shared subtree capacity for parks at many depths. The geometry enters only
through nested regions, same-depth disjointness, and actual validity witnesses. -/
noncomputable section
namespace UniformKServer.ParkCapacity
open Finset TreeRounding TreeParking TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n}

variable {X : Type*} [Fintype X] [MetricSpace X]

structure Geometry (S : Shape n) (X : Type*) [MetricSpace X] where
  region : Vertex n → Finset X
  nested : ∀ u v, descends S u v → region v ⊆ region u
  disjoint : ∀ u v, depth S u=depth S v → u ≠ v → Disjoint (region u) (region v)
  radius : ℕ → ℝ
  nonneg : ∀ j, 0 ≤ radius j
  antitone : Antitone radius
  diameter : ∀ v, ∀ x ∈ region v, ∀ z ∈ region v, dist x z ≤ 40*radius (depth S v)

def ball (y : X) (r : ℝ) : Finset X := univ.filter (fun z => dist y z ≤ r)
def mass (μ : X → ℝ) (A : Finset X) : ℝ := ∑ z ∈ A, μ z

omit [Fintype X] in
theorem disjoint_mass (μ : X → ℝ) (hμ : ∀ z, 0 ≤ μ z)
    (G : Geometry S X) (U : Finset (Vertex n)) (j : ℕ) (B : Finset X)
    (hj : ∀ u ∈ U, depth S u=j) (hsub : ∀ u ∈ U, G.region u ⊆ B) :
    (∑ u ∈ U, mass μ (G.region u)) ≤ mass μ B := by
  have hd : (U : Set (Vertex n)).PairwiseDisjoint G.region := by
    intro u hu v hv hne
    exact G.disjoint u v ((hj u hu).trans (hj v hv).symm) hne
  have he : (∑ u ∈ U, mass μ (G.region u))=mass μ (U.biUnion G.region) := by
    unfold mass
    exact (sum_biUnion hd).symm
  rw [he]
  apply sum_le_sum_of_subset_of_nonneg
  · intro z hz
    obtain ⟨u,hu,hz⟩ := mem_biUnion.mp hz
    exact hsub u hu hz
  · intro z _ _
    exact hμ z

end UniformKServer.ParkCapacity

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Parameters on the actual positive held-size domain of one vector epoch.
These are the geometric hypotheses of the logarithmic proportion minimizer. -/
noncomputable section
namespace UniformKServer.EpochParameters
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def active (a : ι → ℝ) : Finset ι := by
  classical
  exact univ.filter fun i => 0 < a i

theorem mem_active {a : ι → ℝ} {i : ι} : i ∈ active a ↔ 0 < a i := by
  classical
  simp [active]

end UniformKServer.EpochParameters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochAlpha
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Source logarithmic configurations are built on the actual active-size
 domain, including the automatic one-point domain. -/
noncomputable section
namespace UniformKServer.EpochAlpha
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem eta_bound {ct h ell : ℝ} (hc : 0 < ct) (hl : 0 < ell)
    (hct : ct*50000 ≤ 1) (hh : h ≤ 50000*ell) : ct*h/ell ≤ 1 := by
  apply (div_le_iff₀ hl).mpr
  have hm := mul_le_mul_of_nonneg_left hh hc.le
  have hm' := mul_le_mul_of_nonneg_right hct hl.le
  nlinarith

end UniformKServer.EpochAlpha

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeldRelative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Held scalar references with forced epoch resets. The potential is not
 restarted: its nonnegative value is discarded on a wholesale step, while
 the full new installation is charged to that step. -/
noncomputable section
namespace UniformKServer.HeldRelative
open Finset

def expenditure (δ K : ℝ) (x : ℕ → ℝ) (reset : ℕ → Bool) (t : ℕ) : ℝ :=
  if reset t then (1+δ)*(x t+x (t+1)) else K*|x (t+1)-x t|

end UniformKServer.HeldRelative

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FineCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

/-! Companion §03, fine cap algebra.  The tolerance hypotheses below are the
actual absolute choices in Lemma caps; there is no assumed cap feasibility. -/
namespace UniformKServer.FineCaps
noncomputable section
open Finset

/-- A held convex interpolation costs no more variation than the two
persistent endpoint trackers. -/
theorem interpolation_variation {a b A B c : ℝ} (hc : c ∈ Set.Icc (0:ℝ) 1) :
    |((1-c)*A+c*B)-((1-c)*a+c*b)| ≤ |A-a|+|B-b| := by
  have h0 : 0 ≤ 1-c := by linarith [hc.2]
  calc
    _ = |(1-c)*(A-a)+c*(B-b)| := by congr 1; ring
    _ ≤ |(1-c)*(A-a)|+|c*(B-b)| := abs_add_le _ _
    _ = (1-c)*|A-a|+c*|B-b| := by rw [abs_mul,abs_mul,abs_of_nonneg h0,abs_of_nonneg hc.1]
    _ ≤ _ := add_le_add
      (mul_le_of_le_one_left (abs_nonneg _) (by linarith [hc.1]))
      (mul_le_of_le_one_left (abs_nonneg _) hc.2)

end
end UniformKServer.FineCaps

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FineVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Fine endpoint movement is charged once, without the logarithmic weight
of the proportion potentials. Trackers continue through every epoch. -/
noncomputable section
namespace UniformKServer.FineVariation
open Finset RankFunctions RankData RankTracking
open scoped Classical
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

theorem masked_noncore (a b : Bool) {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) :
    |(if b then 0 else y)-(if a then 0 else x)| ≤ |y-x|+(if b=a then 0 else 1) := by
  cases a <;> cases b
  · simp
  · simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,zero_sub,abs_neg,Bool.true_eq_false]
    rw [abs_of_nonneg hx.1]
    linarith [abs_nonneg (y-x),hx.2,hy.2]
  · simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,sub_zero]
    rw [abs_of_nonneg hy.1]
    linarith [abs_nonneg (y-x),hx.2,hy.2]
  · simp only [ite_true, if_true,sub_self,abs_zero,add_zero]
    exact abs_nonneg _

end UniformKServer.FineVariation

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParameterGaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Companion §03, coarse epoch parameter gaps.  These explicit constants prove
 the manuscript's uniform logarithmic comparison without a compactness/minimum
 oracle.  Hypotheses are the exact held-size and non-dominance inequalities. -/
namespace UniformKServer.ParameterGaps
noncomputable section

/-- The same comparison for the marked child.  The constant 1/2 is a
    conservative consequence of the source's side/reference comparisons. -/
theorem dominant_log {u r : ℝ} (hu : 0 ≤ u) (hu₁ : u ≤ 1/4)
    (hr : 1+u/2 ≤ r) : u/3 ≤ Real.log r := by
  have hp : 0 < 1+u/2 := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hm := Real.log_le_log hp hr
  have he : 1-(1+u/2)⁻¹ = (u/2)/(1+u/2) := by field_simp <;> ring
  rw [he] at hl
  have hb : u/3 ≤ (u/2)/(1+u/2) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  linarith

/-- With δ_s=10⁻³, the marked side-reference gives the concrete ratio used
    in `dominant_log`.  No additive lower bound on u is needed. -/
theorem dominant_ratio {A a side U r : ℝ} (hA : 0 < A) (ha : 0 < a)
    (hside : 0 ≤ side) (haA : a ≤ (101:ℝ)/100*A)
    (hU : U ≤ (1001:ℝ)/1000*side)
    (hr : 1+(9:ℝ)/11*(side/a) ≤ r) :
    1+(U/A)/2 ≤ r := by
  have hb : (U/A)/2 ≤ (9:ℝ)/11*(side/a) := by
    apply (div_le_iff₀ (show (0:ℝ)<2 by norm_num)).mpr
    apply (div_le_iff₀ hA).mpr
    apply (mul_le_mul_iff_left₀ ha).mp
    have hc : ((9:ℝ)/11*(side/a)*2*A)*a = (18:ℝ)/11*side*A := by
      field_simp
      ring
    rw [hc]
    nlinarith [mul_le_mul_of_nonneg_right hU ha.le,
      mul_le_mul_of_nonneg_left haA hside]
  linarith

end
end UniformKServer.ParameterGaps

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! One absolute choice in the source's ordered smallness requirements.
All parameters remain independent of the star, k, law and horizon. -/
namespace UniformKServer.StarConstants
noncomputable section

def delta : ℝ := 1/1000000000000
def rho : ℝ := 1/10000000000000000
def lam : ℝ := 1/1000000000000
def eps : ℝ := 1/100000000000
def ct : ℝ := 1/1000000000000
def cw : ℝ := 1/100000000000000
def multiplier : ℝ := 10000000000000000

theorem delta_bounds : 0 < delta ∧ delta < 1/2 := by norm_num [delta]
theorem rho_bounds : 0 < rho ∧ rho < 1/2 := by norm_num [rho]
theorem lam_bounds : 0 < lam ∧ lam ≤ 1/4 := by norm_num [lam]
theorem fine_eps : 4*lam ≤ eps := by norm_num [lam,eps]
theorem ct_pos : 0 < ct := by norm_num [ct]
theorem ct_height : ct*50000 ≤ 1 := by norm_num [ct]
theorem multiplier_bound : 1000 < multiplier*ct := by norm_num [multiplier,ct]
theorem cw_pos : 0 < cw := by norm_num [cw]
theorem cw_height : cw*50000 ≤ 1 := by norm_num [cw]

end
end UniformKServer.StarConstants

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SwitchTracker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Literal hysteresis of the two allocation-rule outputs and its drop
 potential. This is not total-variation tracking of S: only changes of the
 old-rule potential after filtering enter the all-step ledger. -/
namespace UniformKServer.SwitchTracker

inductive Rule where
  | one | two
  deriving DecidableEq

noncomputable def update (old : Rule) (S D : ℝ) : Rule :=
  match old with
  | .one => if S < D/2 then .two else .one
  | .two => if 2*D < S then .one else .two

def valid (rule : Rule) (S D : ℝ) : Prop :=
  match rule with
  | .one => D/2 ≤ S
  | .two => S ≤ 2*D

def potential (rule : Rule) (S D : ℝ) : ℝ :=
  match rule with
  | .one => D
  | .two => S

noncomputable def charge (old : Rule) (S D : ℝ) : ℝ :=
  match old with
  | .one => if S < D/2 then D else 0
  | .two => if 2*D < S then S else 0

theorem update_valid (old : Rule) {S D : ℝ} (hS : 0 ≤ S) (hD : 0 ≤ D) :
    valid (update old S D) S D := by
  cases old <;> unfold update <;> split_ifs <;> simp only [valid] <;> linarith

theorem potential_nonneg (rule : Rule) {S D : ℝ} (hS : 0 ≤ S) (hD : 0 ≤ D) :
    0 ≤ potential rule S D := by cases rule <;> assumption

theorem charge_nonneg (rule : Rule) {S D : ℝ} (hS : 0 ≤ S) (hD : 0 ≤ D) :
    0 ≤ charge rule S D := by cases rule <;> unfold charge <;> split_ifs <;> linarith

/-- The actual Rule I→II charge is D, and II→I charge is S. -/
theorem switch_drop (old : Rule) (S D : ℝ) :
    potential (update old S D) S D ≤ potential old S D-charge old S D/2 := by
  cases old <;> unfold update charge <;> split_ifs <;> simp only [potential] <;> linarith

theorem input_slope (old : Rule) (S D S' D' : ℝ) :
    potential old S' D'-potential old S D ≤ |S'-S|+|D'-D| := by
  cases old <;> simp only [potential]
  · linarith [le_abs_self (D'-D),abs_nonneg (S'-S)]
  · linarith [le_abs_self (S'-S),abs_nonneg (D'-D)]

/-- New S here is compared to the OLD flag sum at NEW posteriors.  Thus its
 error is the number of flag changes, not absolute posterior variation. -/
theorem nonwholesale_step (old : Rule) (Sbar Dold Snew Dnew K : ℝ)
    (hK : |Snew-Sbar| ≤ K) :
    potential (update old Snew Dnew) Snew Dnew-potential old Sbar Dold ≤
      K+|Dnew-Dold|-charge old Snew Dnew/2 := by
  have h₁ := switch_drop old Snew Dnew
  have h₂ := input_slope old Sbar Dold Snew Dnew
  linarith

/-- At wholesale resets no switch credit is claimed. -/
theorem wholesale_step (old new : Rule) {Sbar Dold Snew Dnew C : ℝ}
    (hS : 0 ≤ Sbar) (hD : 0 ≤ Dold) (hSC : Snew ≤ C) (hDC : Dnew ≤ C) :
    potential new Snew Dnew-potential old Sbar Dold ≤ C := by
  have hp := potential_nonneg old hS hD
  cases old <;> cases new <;> simp only [potential] at * <;> linarith

end UniformKServer.SwitchTracker

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SwitchFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Literal causal hysteresis under finite observation laws.  The old-rule
potential is filtered on every step, before the wholesale/reset decision. -/
noncomputable section
namespace UniformKServer.SwitchFinite
open Finset UniformKServer.SwitchTracker
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def indicator (rule : Rule) : ℝ := if rule=.two then 1 else 0

theorem affine (r : Rule) (S D : ℝ) :
    SwitchTracker.potential r S D=indicator r*S+(1-indicator r)*D := by
  have hn : Rule.one ≠ Rule.two := by intro h; cases h
  cases r <;> simp [SwitchTracker.potential,indicator,hn]

end UniformKServer.SwitchFinite

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeRankData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Fixed-tree finite count laws. Internal counts are exactly sums of child
counts; leaves keep their own counts. All operations depend on the observed
finite filtration only. -/
noncomputable section
namespace UniformKServer.TreeRankData
open Finset TreeRounding RankTracking RankData RankFunctions
open scoped Classical
variable {Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

structure Data (Ω : Type*) [Fintype Ω] {n : ℕ} (S : Shape n) (k : ℕ) where
  weight : Ω → ℝ
  positive : ∀ ω, 0 < weight ω
  total : ∑ ω, weight ω=1
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω v, (filtration (t+1)).r ω v → (filtration t).r ω v
  count : ℕ → Ω → Vertex n → ℕ
  bound : ∀ t ω v, count t ω v ≤ k
  conserves : ∀ t ω v, Nonempty (Children S v) → (∑ i : Children S v, count t ω i.val)=count t ω v

end UniformKServer.TreeRankData

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionAnchors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Literal last-key representatives and validity from actual posterior domination. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def lastWord {B : Type} (base : B) (w : PrefixTree.Word B J) : B :=
  if h : 0<w.1.val then w.2 ⟨w.1.val-1,by omega⟩ else base

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParkCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Height-free parked coefficient finance. A logarithmic tail telescope gives
 the manuscript's dyadic-group estimate directly, using the same shared subtree
 capacity; no independence or average-state premise is used. -/
noncomputable section
namespace UniformKServer.ParkCoefficients
open Finset
open scoped Classical

def tail (b : ℕ→ℝ) (N j : ℕ) : ℝ := ∑ i∈Ico j N, b i

theorem tail_nonneg (b : ℕ→ℝ) (hb : ∀ i, 0≤b i) (N j : ℕ) : 0≤tail b N j :=
  sum_nonneg fun i _ => hb i

theorem tail_step (b : ℕ→ℝ) (N j : ℕ) (hj : j<N) : tail b N j=b j+tail b N (j+1) := by
  simp only [tail,sum_Ico_eq_sub _ (Nat.le_of_lt hj),sum_Ico_eq_sub _ (by omega : j+1≤N),sum_range_succ]
  ring

theorem tail_end (b : ℕ→ℝ) (N : ℕ) : tail b N N=0 := by simp [tail]

theorem log_increment (c u v : ℝ) (hc : 0 < c) (hu : 0≤u) (hv : 0≤v) :
    u/(c+u+v)≤Real.log (c+u+v)-Real.log (c+v) := by
  have h1 : 0 < c+v := by linarith
  have h2 : 0 < c+u+v := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos h2 h1)
  rw [Real.log_div h2.ne' h1.ne'] at h
  have he : 1-((c+u+v)/(c+v))⁻¹=u/(c+u+v) := by field_simp <;> ring
  rwa [he] at h

theorem reciprocal_telescope (c : ℝ) (hc : 0 < c) (b : ℕ→ℝ) (hb : ∀ i, 0≤b i) (N : ℕ) :
    (∑ j∈range N, b j/(c+tail b N j))≤Real.log (c+tail b N 0)-Real.log c := by
  have h (j : ℕ) (hj : j∈range N) : b j/(c+tail b N j)≤
      Real.log (c+tail b N j)-Real.log (c+tail b N (j+1)) := by
    rw [tail_step b N j (mem_range.mp hj),←add_assoc]
    exact log_increment c (b j) (tail b N (j+1)) hc (hb j) (tail_nonneg b hb N _)
  have hs := sum_le_sum h
  rw [sum_range_sub',tail_end,add_zero] at hs
  exact hs

theorem capacity_telescope (c K : ℝ) (hc : 0 < c) (hK : 1≤K)
    (b A : ℕ→ℝ) (hb : ∀ i, 0≤b i) (N : ℕ)
    (hA : ∀ j, 1≤A j) (hcap : ∀ j<N, tail b N j ≤ c*(A j-1))
    (htotal : tail b N 0 ≤ c*(K-1)) :
    (∑ j∈range N, b j/A j) ≤ c*Real.log K := by
  have hp (j : ℕ) (hj : j<N) : b j/A j ≤ c*(b j/(c+tail b N j)) := by
    have ht := tail_nonneg b hb N j
    have hd : 0 < c+tail b N j := by linarith
    have ha : 0<A j := by linarith [hA j]
    have hca : c+tail b N j ≤ c*A j := by linarith [hcap j hj]
    apply (div_le_iff₀ ha).mpr
    have he : c*(b j/(c+tail b N j))*A j=(c*b j*A j)/(c+tail b N j) := by ring
    rw [he]
    exact (le_div_iff₀ hd).mpr (by nlinarith [mul_le_mul_of_nonneg_left hca (hb j)])
  have hs := sum_le_sum fun j hj => hp j (mem_range.mp hj)
  rw [←mul_sum] at hs
  have ht := mul_le_mul_of_nonneg_left (reciprocal_telescope c hc b hb N) hc.le
  have hlog : Real.log (c+tail b N 0)-Real.log c≤Real.log K := by
    rw [←Real.log_div (by linarith [tail_nonneg b hb N 0]) hc.ne']
    apply (Real.log_le_log_iff
      (div_pos (by linarith [tail_nonneg b hb N 0]) hc)
      (lt_of_lt_of_le zero_lt_one hK)).mpr
    apply (div_le_iff₀ hc).mpr
    nlinarith
  exact (hs.trans ht).trans (mul_le_mul_of_nonneg_left hlog hc.le)

end UniformKServer.ParkCoefficients

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelParkCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! A cumulative level sum retains the shared tree subtree capacity. Zero
parks require no fictitious nonempty region. -/
noncomputable section
namespace UniformKServer.ParkCapacity
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X : Type*} [Fintype X] [MetricSpace X]

theorem positive_sum (a : Allocation S k) (V : Finset (Vertex n)) :
    (∑ v∈V.filter (fun u=>0<park S a.amount u),park S a.amount v)=∑ v∈V,park S a.amount v := by
  rw [sum_filter]
  apply sum_congr rfl
  intro v _
  split_ifs with h
  · rfl
  · exact (le_antisymm (le_of_not_gt h) (a.park_nonneg v)).symm

end UniformKServer.ParkCapacity

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_Fallback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer
namespace Fallback

structure State (n k : ℕ) where
  position : Configuration n k
  marked : Finset (Fin k)

def pick {k : ℕ} (hk : 0 < k) (A : Finset (Fin k)) : Fin k :=
  if h : A.Nonempty then A.min' h else ⟨0,hk⟩

def coverers {n k : ℕ} (c : Configuration n k) (r : Fin n) : Finset (Fin k) :=
  Finset.univ.filter (fun j => c j = r)

def choose {n k : ℕ} (hk : 0 < k) (s : State n k) (r : Fin n) : Fin k :=
  if (coverers s.position r).Nonempty then pick hk (coverers s.position r)
  else pick hk (Finset.univ \ s.marked)

def step {n k : ℕ} (hk : 0 < k) (s : State n k) (r : Fin n) : State n k :=
  let j := choose hk s r
  ⟨serve s.position r j, insert j s.marked⟩

/-- A raw nonendpoint portion has at most k distinct requested points.
Marks are a subset of the points already seen in that same raw block. -/
def Valid {n k : ℕ} (s : State n k) (S : Finset (Fin n)) : Prop :=
  Function.Injective s.position ∧ s.marked.image s.position ⊆ S ∧ S.card ≤ k


@[simp] theorem mem_coverers {n k : ℕ} (c : Configuration n k) (r : Fin n)
    (j : Fin k) : j ∈ coverers c r ↔ c j = r := by simp [coverers]

end Fallback


namespace Fallback

structure RawState (n k : ℕ) where
  marking : State n k
  seen : Finset (Fin n)
  completed : ℕ

def isEndpoint {n k : ℕ} (s : RawState n k) (r : Fin n) : Prop :=
  k < (insert r s.seen).card
instance instDecidableIsEndpoint {n k : ℕ} (s : RawState n k) (r : Fin n) : Decidable (isEndpoint s r) :=
  inferInstanceAs (Decidable (k < (insert r s.seen).card))

def rawChoice {n k : ℕ} (hk : 0 < k) (s : RawState n k) (r : Fin n) : Fin k :=
  if isEndpoint s r then pick hk (coverers s.marking.position r)
  else choose hk s.marking r

def rawStep {n k : ℕ} (hk : 0 < k) (s : RawState n k) (r : Fin n) : RawState n k :=
  if isEndpoint s r then
    ⟨⟨serve s.marking.position r (rawChoice hk s r), ∅⟩, ∅, s.completed + 1⟩
  else ⟨step hk s.marking r, insert r s.seen, s.completed⟩

def rawTrace {n k : ℕ} (hk : 0 < k) : RawState n k → List (Fin n) → History n k
  | _, [] => []
  | s, r :: w => (r,rawChoice hk s r) :: rawTrace hk (rawStep hk s r) w

def rawRun {n k : ℕ} (hk : 0 < k) : RawState n k → List (Fin n) → RawState n k
  | s, [] => s
  | s, r :: w => rawRun hk (rawStep hk s r) w

def portions {n k : ℕ} (s : RawState n k) : ℕ :=
  s.completed + if s.seen.Nonempty then 1 else 0


/-- Marked points pay the unfinished part of the current block; completed
blocks pay their endpoint as well. This potential prevents a charge per raw
request, even when an epoch is arbitrarily long. -/
def ledger {n k : ℕ} (D : ℝ) (s : RawState n k) : ℝ :=
  s.completed * (k+1) * D + s.marking.marked.card * D

end Fallback
end UniformKServer


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! The sole law-dependent energy is the actual hidden child-count movement.
Posterior drift is derived by conditional contraction, never assumed. -/
noncomputable section
namespace UniformKServer.StarEnergy
open Finset RankTracking
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def allowance (ι : Type*) [Fintype ι] (k : ℕ) : ℝ := (Fintype.card ι+1:ℝ)*(k+1)

theorem allowance_bounds (ι : Type*) [Fintype ι] (k : ℕ) :
    0 ≤ allowance ι k ∧ (k:ℝ) ≤ allowance ι k ∧ (Fintype.card ι:ℝ) ≤ allowance ι k ∧
    (Fintype.card ι:ℝ)*k ≤ allowance ι k := by
  have hk := Nat.cast_nonneg (α:=ℝ) k
  have hi := Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)
  unfold allowance
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

end UniformKServer.StarEnergy

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeAllocationMovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                             
section

/-! Global allocation movement with an absolute, degree/depth independent
coefficient. The finite additive term is displayed as a function of the fixed
tree, its radii and k, not of a law or a horizon. -/
noncomputable section
namespace UniformKServer.TreeAllocationMovement
open Finset TreeRounding TreeRankData RankTracking
open scoped Classical
variable {Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

def allowance (S : Shape n) (k : ℕ) (w : Vertex n → ℝ) : ℝ :=
  ∑ v, w v*StarEnergy.allowance (Children S v) k

end UniformKServer.TreeAllocationMovement

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualAnchorDriftSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                           
section

/-! The individual retained-anchor hidden drift summed over exactly the
chosen mover and all stationary members. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def driftLog (k : ℕ) : ℝ := (6/5)*132*(2+7/Real.log 2)*Real.log (k+1)

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! The multiscale independent partition tape; its law is input-law independent. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance ixPL (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairPL : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Literal coordinate-key motion split into actual edits and the one mover. -/
namespace UniformKServer.PartitionTree
open Finset
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance ixAC (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)

local instance pairAC_reed5be_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
theorem diff_triangle {B : Type*} (a b c : B) :
    PrefixMovement.diff a c≤PrefixMovement.diff a b+PrefixMovement.diff b c := by
  unfold PrefixMovement.diff
  split_ifs <;> norm_num
  aesop

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_KeyCountVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! Key-count L1 drift from the coupled literal member keys. -/
noncomputable section
namespace UniformKServer.KeyCountVariation
open Finset
open scoped Classical
variable {L : Type*} [Fintype L] {k : ℕ}

def indicator (p l : L) : ℝ := if p=l then 1 else 0

def count (p : Fin k→L) (l : L) : ℝ := ∑ a,indicator (p a) l

theorem single (p q : L) : (∑ l,|indicator p l-indicator q l|)≤2*PrefixMovement.diff p q := by
  by_cases he : p=q
  · subst q
    simp [PrefixMovement.diff]
  · have h (l : L) : |indicator p l-indicator q l|≤ indicator p l+indicator q l := by
      unfold indicator
      split_ifs <;> norm_num
    have hs := sum_le_sum (fun l (_ : l∈univ)=>h l)
    norm_num [indicator,PrefixMovement.diff,he,sum_add_distrib] at hs ⊢
    exact hs

theorem total (p q : Fin k→L) : (∑ l,|count p l-count q l|)≤2*∑ a,PrefixMovement.diff (p a) (q a) := by
  calc
    _≤∑ l,∑ a,|indicator (p a) l-indicator (q a) l| := by
      apply sum_le_sum
      intro l _
      unfold count
      rw [←sum_sub_distrib]
      exact abs_sum_le_sum_abs _ _
    _=∑ a,∑ l,|indicator (p a) l-indicator (q a) l| := sum_comm
    _≤∑ a,2*PrefixMovement.diff (p a) (q a) := sum_le_sum (fun a _=>single (p a) (q a))
    _=_ := (mul_sum ..).symm

end UniformKServer.KeyCountVariation

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! Metric realization between occupied vertices in consecutive literal maps.
Intermediate nonexistent prefixes are never used as validity witnesses. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance ixPT (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BoundedFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer
/-- Final labeled positions after the specified legal one-label service. -/
def finish {n k : ℕ} : Configuration n k → History n k → Configuration n k
  | s, [] => s
  | s, (r,j) :: h => finish (serve s r j) h

end UniformKServer



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LazyFinance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A literal labeled strongly-lazy simulation. Fixed-label mismatch suffices
for the movement telescope; no forbidden move or future request is used. -/
namespace UniformKServer.LazyFinance
open Finset
open scoped Classical
variable {X : Type*} [PseudoMetricSpace X] {k : ℕ}

def mismatch (a b : Fin k→X) : ℝ := ∑ i,dist (a i) (b i)

theorem mismatch_nonneg (a b : Fin k→X) : 0 ≤ mismatch a b := sum_nonneg fun _ _=>dist_nonneg

theorem mismatch_triangle (a b c : Fin k→X) : mismatch a c ≤ mismatch a b+mismatch b c := by
  unfold mismatch
  rw [←sum_add_distrib]
  exact sum_le_sum fun i _=>dist_triangle _ _ _

def choice (hk : 0 < k) (a v : Fin k→X) (r : X) : Fin k :=
  if h : ∃ i,a i=r then h.choose else if h : ∃ i,v i=r then h.choose else ⟨0,hk⟩

theorem at_request (a v : Fin k→X) (r : X) (i : Fin k) (hi : v i=r) :
    dist (a i) r+mismatch (Function.update a i r) v=mismatch a v := by
  symm
  calc
    _ = ∑ j : Fin k,((if j=i then dist (a i) r else 0)+dist (Function.update a i r j) (v j)) := by
      apply sum_congr rfl
      intro j _
      by_cases hj : j=i
      · subst j; simp [hi]
      · simp [hj]
    _ = _ := by simp only [sum_add_distrib,sum_ite_eq',mem_univ,ite_true, if_true,mismatch]

theorem initial_bound (a b : Fin k→X) (Δ : ℝ) (hdiam : ∀ x y : X,dist x y ≤ Δ) :
    mismatch a b ≤ k*Δ := by
  calc
    _  ≤  ∑ _ : Fin k,Δ := sum_le_sum fun i _=>hdiam _ _
    _ = _ := by simp

end UniformKServer.LazyFinance

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RealFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Real-valued causal conditional rows, mirroring the exact finite-flow proof.
Uniform-computation Section 02,
Proposition finite-table. This verifies the finite flow -> finite policy step,
including every zero-marginal row. It is support, not an existence input. -/
namespace UniformKServer.RealFlow
variable {R C J : Type*} [Fintype C] [Fintype J] [DecidableEq C] [DecidableEq J]

structure Data (R C J : Type*) where
  mass : List R → C → ℝ
  flow : List R → R → C → J → ℝ

structure Valid (F : Data R C J) (T : C → R → J → C)
    (allowed : C → R → J → Prop) (initial : C) (H : ℕ) : Prop where
  mass_nonneg : ∀ w, w.length ≤ H → ∀ c, 0 ≤ F.mass w c
  mass_total : ∀ w, w.length ≤ H → ∑ c, F.mass w c = 1
  initial : ∀ c, F.mass [] c = if c = initial then 1 else 0
  flow_nonneg : ∀ w, w.length < H → ∀ r c j, 0 ≤ F.flow w r c j
  support : ∀ w, w.length < H → ∀ r c j, ¬allowed c r j → F.flow w r c j = 0
  outflow : ∀ w, w.length < H → ∀ r c, ∑ j, F.flow w r c j = F.mass w c
  inflow : ∀ w, w.length < H → ∀ r c',
    ∑ c, ∑ j, (if T c r j = c' then F.flow w r c j else 0) = F.mass (w++[r]) c'

def flowCost (F : Data R C J) (d : C → R → J → ℝ) : List R → List R → ℝ
  | _, [] => 0
  | w, r :: rs => (∑ c, ∑ j, F.flow w r c j*d c r j) + flowCost F d (w++[r]) rs

-- PROOFS

variable (F : Data R C J) (T : C → R → J → C)
  (allowed : C → R → J → Prop) (initial : C) (H : ℕ)
  (fallback : C → R → J)
  (hF : Valid F T allowed initial H)

include hF

omit [DecidableEq J] in
theorem zero_flow (w : List R) (hw : w.length < H) (r : R) (c : C)
    (hp : F.mass w c = 0) (j : J) : F.flow w r c j = 0 := by
  have hn := hF.flow_nonneg w hw r c j
  have hs := Finset.single_le_sum (fun j _ => hF.flow_nonneg w hw r c j) (Finset.mem_univ j)
  rw [hF.outflow w hw r c, hp] at hs
  exact le_antisymm hs hn

end UniformKServer.RealFlow

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PublicRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Causal rounded distributions are realized without exposing the hidden
trajectory. Only an observed request prefix selects the conditional rows. -/
namespace UniformKServer.TreeRounding
open Finset
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [Fintype X] [MetricSpace X]

structure PublicInput (D : ChainInput S k X Ω) where
  default : Ω
  request : ℕ→Ω→X
  trace : ℕ→Ω→List X
  trace_zero : ∀ ω,trace 0 ω=[]
  trace_snoc : ∀ t ω,trace (t+1) ω=trace t ω++[request t ω]
  trace_length : ∀ t ω,(trace t ω).length=t
  reflects : ∀ t ω v,trace t ω=trace t v → (D.filtration t).r ω v

namespace PublicInput
variable {D : ChainInput S k X Ω} (O : PublicInput D)

def pick (w : List X) : Ω :=
  if h : ∃ ω,O.trace w.length ω=w then h.choose else O.default

end PublicInput
end UniformKServer.TreeRounding

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RealFlowMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Independent finite random seeds are eliminated by linear flow mixtures,
not by revealing them to the request law. -/
namespace UniformKServer.RealFlow
open Finset
open scoped Classical
variable {R C J Z : Type*} [Fintype C] [Fintype J] [Fintype Z]

theorem flowCost_append (F : Data R C J) (d : C→R→J→ℝ) (w u v : List R) :
    flowCost F d w (u++v)=flowCost F d w u+flowCost F d (w++u) v := by
  induction u generalizing w with
  | nil => simp [flowCost]
  | cons r rs ih =>
    rw [List.cons_append,flowCost,flowCost,ih]
    simp only [List.append_assoc,List.singleton_append,add_assoc]

end UniformKServer.RealFlow

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PublicFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A rounded private process gives a literal nonnegative configuration/action
flow with legal zero-marginal rows and the same expected movement. -/
namespace UniformKServer.TreeRounding.PublicInput
open Finset
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [Fintype X] [MetricSpace X]
local instance configEq : DecidableEq (Fin k→X) := fun a b=>Classical.propDecidable (a=b)
variable {D : ChainInput S k X Ω} (O : PublicInput D)

def allowed (c : Fin k→X) (r : X) (j : Fin k) : Prop := (∃ i,c i=r) → c j=r

end UniformKServer.TreeRounding.PublicInput

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualPublicFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Law-dependent but genuinely online configuration/action flows for the
actual pilot, partition, allocation, anchor, and rounding construction. -/

namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance configEq : DecidableEq (Fin k→X) := fun a b=>Classical.propDecidable (a=b)

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PrimitiveRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Composition rules for the explicit primitive-recursive constructor.
`fun_prop` only builds terms from the listed proved closure lemmas. -/
attribute [fun_prop] Primrec
attribute [fun_prop] Primrec.id Primrec.const Primrec.comp Primrec.pair Primrec.fst Primrec.snd

namespace UniformKServer.PrimitiveRules
open Primrec
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

@[fun_prop] theorem add (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x+g x) := nat_add.comp hf hg
@[fun_prop] theorem mul (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x*g x) := nat_mul.comp hf hg
@[fun_prop] theorem sub (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x-g x) := nat_sub.comp hf hg
@[fun_prop] theorem pow (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x^g x) := (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp hf hg
@[fun_prop] theorem div (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x/g x) := nat_div.comp hf hg
@[fun_prop] theorem eqs [DecidableEq β] (f g : α→β) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>decide (f x=g x)) := (Primrec.eq.comp hf hg).decide
@[fun_prop] theorem les (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>decide (f x≤g x)) := (nat_le.comp hf hg).decide
@[fun_prop] theorem lts (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>decide (f x<g x)) := (nat_lt.comp hf hg).decide
@[fun_prop] theorem encoded (f : α→β) (hf : Primrec f) :
    Primrec (fun x=>Encodable.encode (f x)) := Primrec.encode.comp hf
@[fun_prop] theorem decoded (f : α→ℕ) (hf : Primrec f) :
    Primrec (fun x=>@Encodable.decode β _ (f x)) := Primrec.decode.comp hf
@[fun_prop] theorem length (f : α→List β) (hf : Primrec f) :
    Primrec (fun x=>(f x).length) := list_length.comp hf
@[fun_prop] theorem range (f : α→ℕ) (hf : Primrec f) :
    Primrec (fun x=>List.range (f x)) := list_range.comp hf
@[fun_prop] theorem getD (f : α→List β) (g : α→ℕ) (d : β) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>(f x).getD (g x) d) := (list_getD d).comp hf hg
@[fun_prop] theorem set (f : α→List β) (g : α→ℕ) (v : α→β)
    (hf : Primrec f) (hg : Primrec g) (hv : Primrec v) :
    Primrec (fun x=>(f x).set (g x) (v x)) := list_set.comp hf (pair hg hv)
@[fun_prop] theorem append (f g : α→List β) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x++g x) := list_append.comp hf hg
@[fun_prop] theorem cons (f : α→β) (g : α→List β) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x::g x) := list_cons.comp hf hg
@[fun_prop] theorem map (f : α→List β) (g : α→β→γ) (hf : Primrec f)
    (hg : Primrec (fun p : α×β=>g p.1 p.2)) :
    Primrec (fun x=>(f x).map (g x)) := list_map hf hg.to₂
@[fun_prop] theorem flatMap (f : α→List β) (g : α→β→List γ) (hf : Primrec f)
    (hg : Primrec (fun p : α×β=>g p.1 p.2)) :
    Primrec (fun x=>(f x).flatMap (g x)) := list_flatMap hf hg.to₂
@[fun_prop] theorem foldl (f : α→List β) (g : α→γ) (h : α→γ×β→γ)
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec (fun p : α×(γ×β)=>h p.1 p.2)) :
    Primrec (fun x=>(f x).foldl (fun v b=>h x (v,b)) (g x)) := list_foldl hf hg hh.to₂
@[fun_prop] theorem bool_and (f g : α→Bool) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x && g x) := (Primrec.dom_finite (f:=fun p : Bool×Bool=>p.1&&p.2)).comp (pair hf hg)
@[fun_prop] theorem bool_or (f g : α→Bool) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>f x || g x) := (Primrec.dom_finite (f:=fun p : Bool×Bool=>p.1||p.2)).comp (pair hf hg)
@[fun_prop] theorem bool_not (f : α→Bool) (hf : Primrec f) :
    Primrec (fun x=> !(f x)) := (Primrec.dom_finite (f:=Bool.not)).comp hf
@[fun_prop] theorem bool_all (f : α→List β) (g : α→β→Bool) (hf : Primrec f)
    (hg : Primrec (fun p : α×β=>g p.1 p.2)) :
    Primrec (fun x=>(f x).all (g x)) := by
  have h := list_foldr hf (const true)
    ((bool_and _ _ (hg.comp (pair fst (fst.comp snd))) (snd.comp snd)).to₂)
  refine h.of_eq ?_
  intro x
  induction f x <;> simp [List.all_cons, *]

end UniformKServer.PrimitiveRules

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! A primitive-recursive nonnegative rational presentation for the uniform
finite certificate search. Denominators are stored minus one, so every bit
string denotes a valid nonnegative rational; there is no division oracle. -/
namespace UniformKServer.RawArithmetic
abbrev Q := ℕ × ℕ

def value (a : Q) : ℚ := (a.1:ℚ)/(a.2+1)
def natural (n : ℕ) : Q := (n,0)
def add (a b : Q) : Q := (a.1*(b.2+1)+b.1*(a.2+1),(a.2+1)*(b.2+1)-1)
def mul (a b : Q) : Q := (a.1*b.1,(a.2+1)*(b.2+1)-1)
def divide (a : Q) (b : ℕ) : Q := (a.1,(a.2+1)*(b+1)-1)
def le (a b : Q) : Prop := a.1*(b.2+1) ≤ b.1*(a.2+1)
instance instDecidableLe (a b : Q) : Decidable (le a b) := inferInstanceAs (Decidable (_≤_))

theorem denominator (a b : ℕ) : (a+1)*(b+1)-1+1=(a+1)*(b+1) := by
  have h : 1≤(a+1)*(b+1) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  omega

@[simp] theorem value_natural (n : ℕ) : value (natural n) = n := by simp [value,natural]
@[simp] theorem value_add (a b : Q) : value (add a b)=value a+value b := by
  have ha : (a.2:ℚ)+1≠0 := by positivity
  have hb : (b.2:ℚ)+1≠0 := by positivity
  simp only [value,add,← Nat.cast_one (R:=ℚ),← Nat.cast_add,denominator,Nat.cast_mul]
  push_cast
  field_simp

@[simp] theorem value_mul (a b : Q) : value (mul a b)=value a*value b := by
  simp only [value,mul,← Nat.cast_one (R:=ℚ),← Nat.cast_add,denominator,Nat.cast_mul]
  ring

@[simp] theorem value_divide (a : Q) (b : ℕ) : value (divide a b)=value a/(b+1) := by
  simp only [value,divide,← Nat.cast_one (R:=ℚ),← Nat.cast_add,denominator,Nat.cast_mul]
  ring

theorem le_iff (a b : Q) : le a b ↔ value a≤value b := by
  unfold le value
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_cast

open Primrec

theorem primitive_natural : Primrec natural := pair .id (const 0)
theorem primitive_add : Primrec₂ add := by
  unfold add
  exact pair (nat_add.comp (nat_mul.comp (fst.comp fst) (succ.comp (snd.comp snd)))
    (nat_mul.comp (fst.comp snd) (succ.comp (snd.comp fst))))
    (nat_sub.comp (nat_mul.comp (succ.comp (snd.comp fst)) (succ.comp (snd.comp snd))) (const 1))
theorem primitive_mul : Primrec₂ mul := by
  unfold mul
  exact pair (nat_mul.comp (fst.comp fst) (fst.comp snd))
    (nat_sub.comp (nat_mul.comp (succ.comp (snd.comp fst)) (succ.comp (snd.comp snd))) (const 1))
theorem primitive_divide : Primrec₂ divide := by
  unfold divide
  exact pair (fst.comp fst)
    (nat_sub.comp (nat_mul.comp (succ.comp (snd.comp fst)) (succ.comp snd)) (const 1))
theorem primitive_le : PrimrecRel le := by
  unfold le
  exact nat_le.comp (nat_mul.comp (fst.comp fst) (succ.comp (snd.comp snd)))
    (nat_mul.comp (fst.comp snd) (succ.comp (snd.comp fst)))

end UniformKServer.RawArithmetic

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

namespace UniformKServer.RawWords

def words (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | l+1 => (List.range n).flatMap fun r => (words n l).map (r::·)

theorem mem_words (n l : ℕ) (w : List ℕ) :
    w∈words n l ↔ w.length=l ∧ ∀r∈w,r<n := by
  induction l generalizing w with
  | zero => cases w <;> simp [words]
  | succ l ih =>
    cases w with
    | nil => simp [words]
    | cons r w =>
      simp only [words,List.mem_flatMap,List.mem_map,List.cons.injEq,List.length_cons,
        Nat.succ.injEq,List.mem_range]
      constructor
      · rintro ⟨a,ha,v,hv,he,hwe⟩
        subst a;subst v
        obtain ⟨hl,hv⟩:= (ih w).mp hv
        exact ⟨hl,by simpa using And.intro ha hv⟩
      · rintro ⟨hl,hv⟩
        refine ⟨r,hv r (by simp),w,(ih w).mpr ⟨hl,?_⟩,rfl,rfl⟩
        intro q hq
        exact hv q (by simp [hq])

def upto (n H : ℕ) : List (List ℕ) := (List.range (H+1)).flatMap (words n)

theorem mem_upto (n H : ℕ) (w : List ℕ) :
    w∈upto n H ↔ w.length≤H ∧ ∀r∈w,r<n := by
  simp only [upto,List.mem_flatMap,List.mem_range,mem_words]
  constructor
  · rintro ⟨l,hl,he,hw⟩
    exact ⟨by omega,hw⟩
  · rintro ⟨hl,hw⟩
    exact ⟨w.length,by omega,rfl,hw⟩

open Primrec

theorem primitive_words : Primrec₂ words := by
  have h : Primrec₂ (fun n (p : ℕ × List (List ℕ)) =>
      (List.range n).flatMap fun r => p.2.map (r::·)) := by
    apply list_flatMap (list_range.comp fst)
    apply list_map ((snd.comp snd).comp fst)
    exact list_cons.comp (snd.comp fst) snd
  exact (nat_rec (const [[]]) h).of_eq (by intro n l;induction l <;> simp [words, *])

theorem primitive_upto : Primrec₂ upto := by
  unfold upto
  exact list_flatMap (list_range.comp (succ.comp snd)) (primitive_words.comp (fst.comp fst) snd)

theorem primitive_sum : Primrec (List.sum : List ℕ→ℕ) := by
  exact (list_foldr .id (const 0) (nat_add.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq
    (by intro l; change l.foldr (·+·) 0=l.sum; induction l <;> simp [*])

theorem primitive_Qsum : Primrec (fun l : List RawArithmetic.Q=>l.foldr RawArithmetic.add (RawArithmetic.natural 0)) :=
  list_foldr .id (const _) (RawArithmetic.primitive_add.comp (fst.comp snd) (snd.comp snd)).to₂

end UniformKServer.RawWords

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

namespace UniformKServer.RawTable
open RawArithmetic RawWords

def history (w g : List ℕ) : List (ℕ×ℕ) :=
  (List.range w.length).map fun i=>(w.getD i 0,g.getD i 0)
def key (p c : List ℕ) (r j : ℕ) : ℕ := Encodable.encode (p,c,r,j)
def entry (T : List ℕ) (p c : List ℕ) (r j : ℕ) : ℕ := T.getD (key p c r j) 0
def dist (n : ℕ) (d : List Q) (x y : ℕ) : Q := d.getD (x*n+y) (natural 0)
abbrev PathState := (List ℕ × List ℕ) × (ℕ × Q)
def pathStep (n : ℕ) (d : List Q) (T : List ℕ) (z : PathState) (rj : ℕ×ℕ) : PathState :=
  ((z.1.1++[rj.1], z.1.2.set rj.2 rj.1),
    (z.2.1*entry T z.1.1 z.1.2 rj.1 rj.2,
      add z.2.2 (dist n d (z.1.2.getD rj.2 0) rj.1)))
def path (n : ℕ) (d : List Q) (T : List ℕ) (p c w g : List ℕ) : PathState :=
  (history w g).foldl (pathStep n d T) ((p,c),(1,natural 0))
def term (n : ℕ) (d : List Q) (T : List ℕ) (p c w g : List ℕ) : Q :=
  let z:=path n d T p c w g
  mul (natural z.2.1) z.2.2

def total (n k : ℕ) (d : List Q) (T : List ℕ) (p c w : List ℕ) : Q :=
  ((words k w.length).map fun g=>term n d T p c w g).foldr add (natural 0)
def expected (n k b : ℕ) (d : List Q) (T : List ℕ) (p c w : List ℕ) : Q :=
  divide (total n k d T p c w) (2^(b*w.length)-1)
def cost (n : ℕ) (d : List Q) (c w g : List ℕ) : Q := (path n d [] [] c w g).2.2

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_natural (f : α→ℕ) (hf : Primrec f) :
    Primrec (fun x=>natural (f x)) := RawArithmetic.primitive_natural.comp hf
@[fun_prop] theorem primitive_add (f g : α→Q) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>add (f x) (g x)) := RawArithmetic.primitive_add.comp hf hg
@[fun_prop] theorem primitive_mul (f g : α→Q) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>mul (f x) (g x)) := RawArithmetic.primitive_mul.comp hf hg
@[fun_prop] theorem primitive_divide (f : α→Q) (g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>divide (f x) (g x)) := RawArithmetic.primitive_divide.comp hf hg
@[fun_prop] theorem primitive_words (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>words (f x) (g x)) := RawWords.primitive_words.comp hf hg
@[fun_prop] theorem primitive_upto (f g : α→ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>upto (f x) (g x)) := RawWords.primitive_upto.comp hf hg
@[fun_prop] theorem primitive_sum (f : α→List ℕ) (hf : Primrec f) :
    Primrec (fun x=>(f x).sum) := RawWords.primitive_sum.comp hf

@[fun_prop] theorem primitive_history (f g : α→List ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>history (f x) (g x)) := by unfold history;fun_prop
@[fun_prop] theorem primitive_key (p c : α→List ℕ) (r j : α→ℕ)
    (hp : Primrec p) (hc : Primrec c) (hr : Primrec r) (hj : Primrec j) :
    Primrec (fun x=>key (p x) (c x) (r x) (j x)) := by unfold key;fun_prop
@[fun_prop] theorem primitive_entry (T p c : α→List ℕ) (r j : α→ℕ)
    (hT : Primrec T) (hp : Primrec p) (hc : Primrec c) (hr : Primrec r) (hj : Primrec j) :
    Primrec (fun x=>entry (T x) (p x) (c x) (r x) (j x)) := by unfold entry;fun_prop
@[fun_prop] theorem primitive_dist (n : α→ℕ) (d : α→List Q) (x y : α→ℕ)
    (hn : Primrec n) (hd : Primrec d) (hx : Primrec x) (hy : Primrec y) :
    Primrec (fun v=>dist (n v) (d v) (x v) (y v)) := by unfold dist;fun_prop
@[fun_prop] theorem primitive_pathStep (n : α→ℕ) (d : α→List Q) (T : α→List ℕ)
    (z : α→PathState) (rj : α→ℕ×ℕ) (hn : Primrec n) (hd : Primrec d)
    (hT : Primrec T) (hz : Primrec z) (hrj : Primrec rj) :
    Primrec (fun x=>pathStep (n x) (d x) (T x) (z x) (rj x)) := by unfold pathStep;fun_prop
@[fun_prop] theorem primitive_path (n : α→ℕ) (d : α→List Q) (T p c w g : α→List ℕ)
    (hn : Primrec n) (hd : Primrec d) (hT : Primrec T) (hp : Primrec p)
    (hc : Primrec c) (hw : Primrec w) (hg : Primrec g) :
    Primrec (fun x=>path (n x) (d x) (T x) (p x) (c x) (w x) (g x)) := by
  unfold path
  apply Primrec.list_foldl (h:=fun x v=>pathStep (n x) (d x) (T x) v.1 v.2)
  · fun_prop
  · fun_prop
  · change Primrec (fun a : α × (PathState × (ℕ×ℕ)) =>
      pathStep (n a.1) (d a.1) (T a.1) a.2.1 a.2.2)
    fun_prop
@[fun_prop] theorem primitive_term (n : α→ℕ) (d : α→List Q) (T p c w g : α→List ℕ)
    (hn : Primrec n) (hd : Primrec d) (hT : Primrec T) (hp : Primrec p)
    (hc : Primrec c) (hw : Primrec w) (hg : Primrec g) :
    Primrec (fun x=>term (n x) (d x) (T x) (p x) (c x) (w x) (g x)) := by
  unfold term
  fun_prop
@[fun_prop] theorem primitive_total (n k : α→ℕ) (d : α→List Q) (T p c w : α→List ℕ)
    (hn : Primrec n) (hk : Primrec k) (hd : Primrec d) (hT : Primrec T) (hp : Primrec p)
    (hc : Primrec c) (hw : Primrec w) :
    Primrec (fun x=>total (n x) (k x) (d x) (T x) (p x) (c x) (w x)) := by
  unfold total
  apply RawWords.primitive_Qsum.comp
  fun_prop
@[fun_prop] theorem primitive_expected (n k b : α→ℕ) (d : α→List Q) (T p c w : α→List ℕ)
    (hn : Primrec n) (hk : Primrec k) (hb : Primrec b) (hd : Primrec d) (hT : Primrec T)
    (hp : Primrec p) (hc : Primrec c) (hw : Primrec w) :
    Primrec (fun x=>expected (n x) (k x) (b x) (d x) (T x) (p x) (c x) (w x)) := by
  unfold expected
  fun_prop
@[fun_prop] theorem primitive_cost (n : α→ℕ) (d : α→List Q) (c w g : α→List ℕ)
    (hn : Primrec n) (hd : Primrec d) (hc : Primrec c) (hw : Primrec w) (hg : Primrec g) :
    Primrec (fun x=>cost (n x) (d x) (c x) (w x) (g x)) := by unfold cost;fun_prop
end Primitive
end UniformKServer.RawTable

end


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Finite arithmetic certificates of the *unknown-offset* construction.
The verifier checks every finite word and every hindsight label history; no
competitive conclusion is an input. All its checks are primitive recursive. -/
namespace UniformKServer.RawCertificate
open RawArithmetic RawWords RawTable

abbrev Input := ℕ × ℕ × List Q
abbrev Certificate := (ℕ × ℕ × ℕ × ℕ) × (Q × Q) × List ℕ

def ell (v : Certificate) := v.1.1
def bits (v : Certificate) := v.1.2.1
def cap (v : Certificate) := v.1.2.2.1
def restart (v : Certificate) := v.1.2.2.2
def diam (v : Certificate) := v.2.1.1
def sep (v : Certificate) := v.2.1.2
def table (v : Certificate) := v.2.2

def horizon (k M : ℕ) := ((List.range (M+1)).map fun i=>k^i).sum

def rowOK (k b : ℕ) (T p c : List ℕ) (r : ℕ) : Bool :=
  decide (((List.range k).map fun j=>entry T p c r j).sum=2^b) &&
  (List.range k).all fun j=>
    (!(c.any fun x=>decide (x=r))) || decide (c.getD j 0=r) || decide (entry T p c r j=0)

def rowsOK (n k H b : ℕ) (T : List ℕ) : Bool :=
  (upto n H).all fun p=>(words n k).all fun c=>(List.range n).all fun r=>rowOK k b T p c r

def tableOK (n k H b A R : ℕ) (d : List Q) (D δ : Q) (T : List ℕ) : Bool :=
  (upto n H).all fun w=>(words k w.length).all fun g=> decide
    (le (expected n k b d T [] (List.range k) w)
      (add (mul (natural A) (cost n d (List.range k) w g)) (add (mul (natural R) δ) D)))

def numbersOK (k : ℕ) (v : Certificate) : Bool :=
  decide (0<ell v) && decide (2^(ell v-1)<k+1) && decide (k+1≤2^(ell v)) &&
  decide (0 < restart v) && decide (0<(sep v).1) &&
  decide (le (mul (natural k) (diam v)) (mul (natural (restart v)) (sep v))) &&
  decide (le (mul (natural (restart v*(k+1))) (diam v)) (mul (natural (cap v+1)) (sep v)))

def boundsOK (n : ℕ) (d : List Q) (D δ : Q) : Bool :=
  (List.range n).all (fun x=>(List.range n).all fun y=>
    decide (le (dist n d x y) D) && (decide (x=y) || decide (le δ (dist n d x y))))

def verify (mult : ℕ) (i : Input) (v : Certificate) : Bool :=
  let n:=i.1; let k:=i.2.1; let d:=i.2.2
  let H:=horizon k (cap v)
  numbersOK k v && boundsOK n d (diam v) (sep v) &&
  rowsOK n k H (bits v) (table v) &&
  tableOK n k H (bits v) (mult*(ell v)^2) (restart v) d (diam v) (sep v) (table v)

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_le (f g : α→Q) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x=>decide (le (f x) (g x))) := (RawArithmetic.primitive_le.comp hf hg).decide
@[fun_prop] theorem primitive_any (f : α→List ℕ) (g : α→ℕ→Bool) (hf : Primrec f)
    (hg : Primrec (fun p : α×ℕ=>g p.1 p.2)) :
    Primrec (fun x=>(f x).any (g x)) := by
  have h : Primrec (fun x=> !((f x).all fun y=> !(g x y))) := by fun_prop
  exact h.of_eq (by intro x;simp [List.any_eq_not_all_not])
@[fun_prop] theorem primitive_horizon (k M : α→ℕ) (hk : Primrec k) (hM : Primrec M) :
    Primrec (fun x=>horizon (k x) (M x)) := by unfold horizon;fun_prop
@[fun_prop] theorem primitive_rowOK (k b : α→ℕ) (T p c : α→List ℕ) (r : α→ℕ)
    (hk : Primrec k) (hb : Primrec b) (hT : Primrec T) (hp : Primrec p) (hc : Primrec c) (hr : Primrec r) :
    Primrec (fun x=>rowOK (k x) (b x) (T x) (p x) (c x) (r x)) := by unfold rowOK;fun_prop
@[fun_prop] theorem primitive_rowsOK (n k H b : α→ℕ) (T : α→List ℕ)
    (hn : Primrec n) (hk : Primrec k) (hH : Primrec H) (hb : Primrec b) (hT : Primrec T) :
    Primrec (fun x=>rowsOK (n x) (k x) (H x) (b x) (T x)) := by unfold rowsOK;fun_prop
@[fun_prop] theorem primitive_tableOK (n k H b A R : α→ℕ) (d : α→List Q) (D δ : α→Q) (T : α→List ℕ)
    (hn : Primrec n) (hk : Primrec k) (hH : Primrec H) (hb : Primrec b) (hA : Primrec A)
    (hR : Primrec R) (hd : Primrec d) (hD : Primrec D) (hδ : Primrec δ) (hT : Primrec T) :
    Primrec (fun x=>tableOK (n x) (k x) (H x) (b x) (A x) (R x) (d x) (D x) (δ x) (T x)) := by
  unfold tableOK;fun_prop

@[fun_prop] theorem primitive_numbersOK (k : α→ℕ) (v : α→Certificate)
    (hk : Primrec k) (hv : Primrec v) : Primrec (fun x=>numbersOK (k x) (v x)) := by
  unfold numbersOK ell cap restart diam sep
  fun_prop
@[fun_prop] theorem primitive_boundsOK (n : α→ℕ) (d : α→List Q) (D δ : α→Q)
    (hn : Primrec n) (hd : Primrec d) (hD : Primrec D) (hδ : Primrec δ) :
    Primrec (fun x=>boundsOK (n x) (d x) (D x) (δ x)) := by unfold boundsOK;fun_prop

theorem primitive_verify (mult : ℕ) : Primrec₂ (verify mult) := by
  unfold verify ell bits cap restart diam sep table
  change Primrec (fun p : Input×Certificate=> _)
  fun_prop
end Primitive
end UniformKServer.RawCertificate

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                              
section

namespace UniformKServer.RawPath
open RawArithmetic RawTable RawWords

def weight (T : List ℕ) : List ℕ → List ℕ → List (ℕ×ℕ) → ℕ
  | _,_,[]=>1
  | p,c,(r,j)::h=>entry T p c r j*weight T (p++[r]) (c.set j r) h

def movement (n : ℕ) (d : List Q) : List ℕ → List (ℕ×ℕ) → ℚ
  | _,[]=>0
  | c,(r,j)::h=>value (dist n d (c.getD j 0) r)+movement n d (c.set j r) h

end UniformKServer.RawPath

end


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawTyped
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

namespace UniformKServer.RawTyped
open RawArithmetic RawWords RawTable RawPath

def requests {n : ℕ} (w : List (Fin n)) : List ℕ := w.map Fin.val
def config {n k : ℕ} (c : Configuration n k) : List ℕ := List.ofFn fun j=> (c j).val
def events {n k : ℕ} (h : History n k) : List (ℕ×ℕ) := h.map fun x=>(x.1.val,x.2.val)

theorem config_mem {n k : ℕ} (c : Configuration n k) : config c∈words n k := by
  apply (mem_words n k _).mpr
  refine ⟨by simp [config],?_⟩
  intro r hr
  rcases List.mem_ofFn.mp hr with ⟨j,rfl⟩
  exact (c j).isLt

theorem requests_mem {n : ℕ} (w : List (Fin n)) (H : ℕ) (hw : w.length≤H) :
    requests w∈upto n H := by
  apply (mem_upto n H _).mpr
  refine ⟨by simpa [requests] using hw,?_⟩
  intro r hr
  rcases List.mem_map.mp hr with ⟨x,hx,rfl⟩
  exact x.isLt

end UniformKServer.RawTyped

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawMetric
open RawArithmetic RawWords RawTable RawTyped RawCertificate

def present (a : ℚ) : Q := (a.num.natAbs,a.den-1)

theorem horizon_eq (k M : ℕ) : RawCertificate.horizon k M=UniformKServer.horizon k M := by
  unfold RawCertificate.horizon UniformKServer.horizon
  have h : ∀m,(List.map (fun i=>k^i) (List.range m)).sum=∑i∈Finset.range m,k^i := by
    intro m
    induction m with
    | zero=>simp
    | succ m ih=>simp [List.range_succ,Finset.sum_range_succ,ih]
  exact h _

end UniformKServer.RawMetric

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawBinary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawBinary
open Primrec RawCertificate
attribute [fun_prop] Primrec.list_tail

def value (w : List Bool) : ℕ := w.foldr (fun b v=>(if b then 1 else 0)+2*v) 0

@[simp] theorem value_nil : value []=0 := rfl
@[simp] theorem value_cons (b : Bool) (w : List Bool) : value (b::w)=Nat.bit b (value w) := by
  cases b <;> simp [value,Nat.bit_val,Nat.add_comm]

@[fun_prop] theorem primitive_value {α : Type*} [Primcodable α] (w : α→List Bool) (hw : Primrec w) :
    Primrec (fun x=>value (w x)) := by
  unfold value
  have h : Primrec (fun p : α×(Bool×ℕ)=>(if p.2.1 then 1 else 0)+2*p.2.2) :=
    by
      simp only [←Bool.cond_eq_ite]
      exact Primrec.nat_add.comp
        (Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const 1) (Primrec.const 0))
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_foldr hw (Primrec.const 0) h.to₂

def readNat (w : List Bool) : ℕ×List Bool :=
  let a:=(w.takeWhile id).length
  let v:=w.drop (a+1)
  (value (v.take a),v.drop a)

def readQ (w : List Bool) : RawArithmetic.Q×List Bool :=
  let a:=readNat w.tail
  let b:=readNat a.2
  ((a.1,b.1-1),b.2)

def readMany (n : ℕ) (w : List Bool) : List RawArithmetic.Q×List Bool :=
  (List.range n).foldl (fun p _=>let a:=readQ p.2;(p.1++[a.1],a.2)) ([],w)

def input (w : List Bool) : Input :=
  let n:=readNat w
  let k:=readNat n.2
  (n.1,k.1,(readMany (n.1*n.1) k.2).1)

section Primitive
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_readNat (w : α→List Bool) (hw : Primrec w) :
    Primrec (fun x=>readNat (w x)) := by
  have ht : Primrec (fun x=>(w x).takeWhile id) := (Primrec.list_takeWhile Primrec.id).comp hw
  have ha : Primrec (fun x=>(w x).takeWhile id |>.length) := Primrec.list_length.comp ht
  have hd : Primrec (fun x=>(w x).drop (((w x).takeWhile id).length+1)) :=
    Primrec.list_drop.comp (Primrec.succ.comp ha) hw
  exact Primrec.pair (primitive_value _ (Primrec.list_take.comp ha hd))
    (Primrec.list_drop.comp ha hd)
@[fun_prop] theorem primitive_readQ (w : α→List Bool) (hw : Primrec w) :
    Primrec (fun x=>readQ (w x)) := by unfold readQ;fun_prop
@[fun_prop] theorem primitive_readMany (n : α→ℕ) (w : α→List Bool) (hn : Primrec n) (hw : Primrec w) :
    Primrec (fun x=>readMany (n x) (w x)) := by
  unfold readMany
  have h : Primrec (fun p : α×((List RawArithmetic.Q×List Bool)×ℕ)=>
      let a:=readQ p.2.1.2;(p.2.1.1++[a.1],a.2)) := by fun_prop
  exact Primrec.list_foldl (Primrec.list_range.comp hn) (Primrec.pair (Primrec.const []) hw) h.to₂
@[fun_prop] theorem primitive_input (w : α→List Bool) (hw : Primrec w) :
    Primrec (fun x=>input (w x)) := by unfold input;fun_prop
end Primitive

def distances {n : ℕ} (d : RationalMetric n) : List ℚ :=
  (List.ofFn fun x : Fin n=>(List.ofFn fun y : Fin n=>d.distance x y)).flatten

@[simp] theorem distances_length {n : ℕ} (d : RationalMetric n) : (distances d).length=n*n := by
  simp [distances,List.length_flatten,List.sum_ofFn,Finset.sum_const,smul_eq_mul]

end UniformKServer.RawBinary

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                              
section

namespace UniformKServer.RawBits
open Primrec

 theorem size_graph (a b : ℕ) : a.size=b ↔ a<2^b ∧ (b=0 ∨ 2^(b-1)≤a) := by
  constructor
  · rintro rfl
    refine ⟨Nat.lt_size_self a,?_⟩
    by_cases h : a.size=0
    · exact Or.inl h
    · exact Or.inr (Nat.lt_size.mp (by omega))
  · rintro ⟨h,he|he⟩
    · have:=Nat.size_le.mpr h;omega
    · have:=Nat.size_le.mpr h
      have:=Nat.lt_size.mpr he
      omega

 theorem primitive_size : Primrec Nat.size := by
  apply Primrec.of_graph ⟨id,Primrec.id,fun a=>Nat.size_le.mpr Nat.lt_two_pow_self⟩
  refine ⟨inferInstance,?_⟩
  have h : Primrec (fun p : ℕ×ℕ=>decide (p.1<2^p.2) &&
      (decide (p.2=0) || decide (2^(p.2-1)≤p.1))) := by fun_prop
  exact h.of_eq (by
    intro p
    change _=decide (p.1.size=p.2)
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,size_graph])

 theorem primitive_testBit : Primrec₂ Nat.testBit := by
  have h : Primrec (fun p : ℕ×ℕ=>decide (p.1/2^p.2%2=1)) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp (by fun_prop) (Primrec.const 2)) (Primrec.const 1)).decide
  exact h.of_eq (by intro p;exact Nat.testBit_eq_decide_div_mod_eq.symm)

 theorem bits_eq (a : ℕ) : a.bits=(List.range a.size).map (Nat.testBit a) := by
  apply List.ext_getElem
  · simp [Nat.size_eq_bits_len]
  · intro i h₁ h₂
    simp only [List.getElem_map,List.getElem_range,Nat.testBit_eq_inth]
    exact (List.getI_eq_getElem _ h₁).symm

 theorem primitive_bits : Primrec Nat.bits := by
  have h : Primrec (fun a=>(List.range a.size).map (Nat.testBit a)) :=
    Primrec.list_map (Primrec.list_range.comp primitive_size) primitive_testBit
  exact h.of_eq (fun a=>(bits_eq a).symm)

open Turing.PartrecToTM2

def letter (b : Bool) : Γ' := bif b then .bit1 else .bit0

theorem trPos_bits (a : PosNum) : trPosNum a=((a:ℕ).bits.map letter) := by
  induction a with
  | one=>rfl
  | bit0 a ih=>
    rw [PosNum.cast_bit0,←two_mul,Nat.bit0_bits _ (ne_of_gt (PosNum.to_nat_pos a))]
    simp only [trPosNum,List.map_cons,←ih]
    rfl
  | bit1 a ih=>
    rw [PosNum.cast_bit1,←two_mul,Nat.bit1_bits]
    simp only [trPosNum,List.map_cons,←ih]
    rfl

theorem trNum_bits (a : Num) : trNum a=((a:ℕ).bits.map letter) := by
  cases a with
  | zero=>rfl
  | pos a=>exact trPos_bits a

theorem trNat_bits (a : ℕ) : trNat a=a.bits.map letter := by
  unfold trNat
  rw [trNum_bits,Num.to_of_nat]

end UniformKServer.RawBits

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BitSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.BitSampling

def bitsEquiv (b : ℕ) : (Fin b → Bool) ≃ Fin (2^b) :=
  (Equiv.piCongrRight (fun _ : Fin b => finTwoEquiv.symm)).trans
    (finPiFinEquiv.trans (finCongr (by simp)))

def row {k b : ℕ} (N : Fin k → ℕ) (hN : ∑ j, N j = 2^b)
    (coins : Fin b → Bool) : Fin k :=
  (finSigmaFinEquiv.symm ((finCongr hN).symm (bitsEquiv b coins))).1

def cumulative {k : ℕ} (N : Fin k → ℕ) (j : Fin k) : ℕ :=
  ∑ i : Fin j.val, N (Fin.castLE j.isLt.le i)

end UniformKServer.BitSampling



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BitPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.BitSampling

noncomputable def mean {A : Type*} [Fintype A] (v : A → ℝ) : ℝ :=
  (∑ a, v a) / Fintype.card A

def runCost {S R : Type*} {k b : ℕ} (N : S → R → Fin k → ℕ)
    (hN : ∀ s r, ∑ j, N s r j = 2^b) (next : S → R → Fin k → S)
    (charge : S → R → Fin k → ℝ) :
    (s : S) → (w : List R) → (Fin w.length → Fin b → Bool) → ℝ
  | _, [], _ => 0
  | s, r::w, coins =>
    let j := row (N s r) (hN s r) (coins 0)
    charge s r j + runCost N hN next charge (next s r j) w (Fin.tail coins)

noncomputable def rowCost {S R : Type*} {k b : ℕ} (N : S → R → Fin k → ℕ)
    (next : S → R → Fin k → S) (charge : S → R → Fin k → ℝ) : S → List R → ℝ
  | _, [] => 0
  | s, r::w => ∑ j, (N s r j : ℝ) / (2^b : ℕ) *
    (charge s r j + rowCost (b:=b) N next charge (next s r j) w)

end UniformKServer.BitSampling



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochShadow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.EpochShadow

def bookStep {n k : ℕ} (seen : Finset (Fin n)) (r : Fin n) : Finset (Fin n) :=
  if k < (insert r seen).card then ∅ else insert r seen

/-- Number of portions, including an inherited nonempty raw block. -/
def blockCount {n k : ℕ} : Finset (Fin n) → List (Fin n) → ℕ
  | seen, [] => if seen.Nonempty then 1 else 0
  | seen, r :: w => (if k < (insert r seen).card then 1 else 0) +
      blockCount (k:=k) (bookStep (k:=k) seen r) w


end UniformKServer.EpochShadow

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.EpochExpectation
open EpochShadow

def extend {m b : ℕ} (coins : Fin m → Fin b → Bool) (t : ℕ) : Fin b → Bool :=
  if h : t < m then coins ⟨t,h⟩ else fun _ => false

end UniformKServer.EpochExpectation



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.EpochControl
open EpochShadow

abbrev BList (A : Type*) (B : ℕ) := {l : List A // l.length ≤ B}
instance instFiniteBList {A : Type*} [Finite A] (B : ℕ) : Finite (BList A B) :=
  (List.finite_length_le A B).to_subtype

end UniformKServer.EpochControl

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawMarks
attribute [-instance] _root_.OAI.UniformKServer.EpochControl.instFiniteBList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                               
section

namespace UniformKServer.RawMarks
open RawTyped

def bits {a : ℕ} (A : Finset (Fin a)) : List Bool := List.ofFn fun j=>decide (j∈A)
def empty (a : ℕ) : List Bool := List.replicate a false
def insert (A : List Bool) (j : ℕ) : List Bool := A.set j true
def card (A : List Bool) : ℕ := (A.map (fun b=>if b then 1 else 0)).sum
def complement (A : List Bool) : List Bool := A.map Bool.not
def covers (c : List ℕ) (r : ℕ) : List Bool := c.map (fun x=>decide (x=r))
def pick (A : List Bool) : ℕ := let j:=A.findIdx id; if j<A.length then j else 0

@[simp] theorem empty_bits (a : ℕ) : empty a=bits (∅ : Finset (Fin a)) := by
  simp [empty,bits,List.ofFn_const]
@[simp] theorem insert_bits {a : ℕ} (A : Finset (Fin a)) (j : Fin a) :
    insert (bits A) j.val=bits (Insert.insert j A) := by
  apply List.ext_getElem
  · simp [insert,bits]
  · intro i hi hj
    simp only [insert,List.length_set,List.length_ofFn,bits] at hi hj ⊢
    rw [List.getElem_set]
    simp only [List.getElem_ofFn,Finset.mem_insert]
    by_cases h : j.val=i
    · have he : (⟨i,hj⟩ : Fin a)=j := Fin.ext h.symm
      simp [h,he]
    · have he : (⟨i,hj⟩ : Fin a)≠j := by intro he;exact h (congrArg Fin.val he).symm
      simp [h,he]
@[simp] theorem card_bits {a : ℕ} (A : Finset (Fin a)) : card (bits A)=A.card := by
  simp [card,bits,List.map_ofFn,List.sum_ofFn]
@[simp] theorem complement_bits {a : ℕ} (A : Finset (Fin a)) :
    complement (bits A)=bits (Finset.univ\A) := by
  simp [complement,bits,List.map_ofFn,Function.comp_def]
@[simp] theorem covers_bits {n k : ℕ} (c : Configuration n k) (r : Fin n) :
    covers (config c) r.val=bits (Fallback.coverers c r) := by
  simp [covers,config,bits,Fallback.coverers,List.map_ofFn,Fin.ext_iff,Function.comp_def]

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_empty (f : α→ℕ) (hf : Primrec f) :
    Primrec (fun x=>empty (f x)) := by
  have h : Primrec (fun x=>(List.range (f x)).map (fun _=>false)) := by fun_prop
  exact h.of_eq (by intro x;simp [empty])
@[fun_prop] theorem primitive_insert (f : α→List Bool) (j : α→ℕ) (hf : Primrec f) (hj : Primrec j) :
    Primrec (fun x=>insert (f x) (j x)) := by unfold insert;fun_prop
@[fun_prop] theorem primitive_card (f : α→List Bool) (hf : Primrec f) :
    Primrec (fun x=>card (f x)) := by
  unfold card
  apply RawTable.primitive_sum
  apply PrimitiveRules.map _ _ hf
  exact (Primrec.dom_finite (f:=fun b : Bool=>if b then 1 else 0)).comp Primrec.snd
@[fun_prop] theorem primitive_complement (f : α→List Bool) (hf : Primrec f) :
    Primrec (fun x=>complement (f x)) := by unfold complement;fun_prop
@[fun_prop] theorem primitive_covers (f : α→List ℕ) (r : α→ℕ) (hf : Primrec f) (hr : Primrec r) :
    Primrec (fun x=>covers (f x) (r x)) := by unfold covers;fun_prop
@[fun_prop] theorem primitive_pick (f : α→List Bool) (hf : Primrec f) :
    Primrec (fun x=>pick (f x)) := by
  have hg : Primrec (fun x=>(f x).findIdx id) := Primrec.list_findIdx hf Primrec.snd
  unfold pick
  exact Primrec.ite (Primrec.nat_lt.comp hg (Primrec.list_length.comp hf)) hg (Primrec.const 0)
end Primitive
end UniformKServer.RawMarks

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawFallback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.RawFallback
open RawTyped RawMarks

def endpoint (k : ℕ) (seen : List Bool) (r : ℕ) : Bool :=
  decide (k < card (RawMarks.insert seen r))
def choose (c : List ℕ) (marked : List Bool) (r : ℕ) : ℕ :=
  bif decide (0 < card (covers c r)) then pick (covers c r) else pick (complement marked)
def label (k : ℕ) (c : List ℕ) (marked seen : List Bool) (r : ℕ) : ℕ :=
  bif endpoint k seen r then pick (covers c r) else choose c marked r
def nextMarked (k : ℕ) (marked seen : List Bool) (r j : ℕ) : List Bool :=
  bif endpoint k seen r then empty k else RawMarks.insert marked j
def nextSeen (n k : ℕ) (seen : List Bool) (r : ℕ) : List Bool :=
  bif endpoint k seen r then empty n else RawMarks.insert seen r

@[simp] theorem endpoint_bits {n k : ℕ} (s : Finset (Fin n)) (r : Fin n) :
    endpoint k (bits s) r.val=decide (k<(Insert.insert r s).card) := by
  simp only [endpoint,insert_bits,card_bits]

@[simp] theorem nextSeen_bits {n k : ℕ} (s : Finset (Fin n)) (r : Fin n) :
    nextSeen n k (bits s) r.val=bits (EpochShadow.bookStep (k:=k) s r) := by
  simp only [nextSeen,endpoint_bits,Bool.cond_decide,empty_bits,insert_bits,EpochShadow.bookStep]
  split_ifs <;> simp_all

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_endpoint (k : α→ℕ) (s : α→List Bool) (r : α→ℕ)
    (hk : Primrec k) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>endpoint (k x) (s x) (r x)) := by unfold endpoint;fun_prop
@[fun_prop] theorem primitive_choose (c : α→List ℕ) (m : α→List Bool) (r : α→ℕ)
    (hc : Primrec c) (hm : Primrec m) (hr : Primrec r) :
    Primrec (fun x=>choose (c x) (m x) (r x)) := by
  unfold choose
  exact Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop)
@[fun_prop] theorem primitive_label (k : α→ℕ) (c : α→List ℕ) (m s : α→List Bool) (r : α→ℕ)
    (hk : Primrec k) (hc : Primrec c) (hm : Primrec m) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>label (k x) (c x) (m x) (s x) (r x)) := by
  unfold label
  exact Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop)
@[fun_prop] theorem primitive_nextMarked (k : α→ℕ) (m s : α→List Bool) (r j : α→ℕ)
    (hk : Primrec k) (hm : Primrec m) (hs : Primrec s) (hr : Primrec r) (hj : Primrec j) :
    Primrec (fun x=>nextMarked (k x) (m x) (s x) (r x) (j x)) := by
  unfold nextMarked
  exact Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop)
@[fun_prop] theorem primitive_nextSeen (n k : α→ℕ) (s : α→List Bool) (r : α→ℕ)
    (hn : Primrec n) (hk : Primrec k) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>nextSeen (n x) (k x) (s x) (r x)) := by
  unfold nextSeen
  exact Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop)
end Primitive
end UniformKServer.RawFallback

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PathExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

namespace UniformKServer.PathExpansion
variable {S R : Type*} {k b : ℕ}

def traces (k : ℕ) : List R → List (List (R×Fin k))
  | []=>[[]]
  | r::w=>(List.ofFn fun j : Fin k => (traces k w).map ((r,j)::·)).flatten

def weight (N : S→R→Fin k→ℕ) (next : S→R→Fin k→S) : S→List (R×Fin k)→ℕ
  | _,[]=>1
  | s,(r,j)::h=>N s r j*weight N next (next s r j) h

def movement (next : S→R→Fin k→S) (charge : S→R→Fin k→ℝ) : S→List (R×Fin k)→ℝ
  | _,[]=>0
  | s,(r,j)::h=>charge s r j+movement next charge (next s r j) h

end UniformKServer.PathExpansion

end


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

namespace UniformKServer.RawExpansion
open RawArithmetic RawWords RawTable RawPath RawTyped

theorem range_eq_ofFn (k : ℕ) : List.range k=List.ofFn (fun j : Fin k=>j.val) := by
  apply List.ext_getElem <;> simp

end UniformKServer.RawExpansion

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawFilter
open RawTyped
abbrev E := List ℕ×ℕ
abbrev F := List E×List ℕ×ℕ

def cover (e : E) (r : ℕ) : Bool := e.1.any (fun x=>decide (x=r))
def allCover (s : F) (r : ℕ) : Bool := s.1.all (fun e=>cover e r)
def expand (k M r : ℕ) (e : E) : List E :=
  bif cover e r then [e] else
    bif decide (e.2<M) then (List.range k).map (fun j=>(e.1.set j r,e.2+1)) else []
def births (k M r : ℕ) (e : E) : ℕ :=
  bif cover e r then 0 else bif decide (e.2<M) then k else 0
def step (k M : ℕ) (s : F) (r : ℕ) : F :=
  bif allCover s r then s else
    (s.1.flatMap (expand k M r),s.2.1++[r],s.2.2+(s.1.map (births k M r)).sum)
end UniformKServer.RawFilter

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawRowSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                   
section

namespace UniformKServer.RawRowSelect
open RawTyped RawTable

def partialMass (T p c : List ℕ) (r j : ℕ) : ℕ :=
  ((List.range j).map (fun i=>entry T p c r i)).sum

def choose (k : ℕ) (T p c : List ℕ) (r coin : ℕ) : ℕ :=
  RawMarks.pick ((List.range k).map (fun j=>decide (coin<partialMass T p c r (j+1))))

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_partialMass (T p c : α→List ℕ) (r j : α→ℕ)
    (hT : Primrec T) (hp : Primrec p) (hc : Primrec c) (hr : Primrec r) (hj : Primrec j) :
    Primrec (fun x=>partialMass (T x) (p x) (c x) (r x) (j x)) := by unfold partialMass;fun_prop
@[fun_prop] theorem primitive_choose (k : α→ℕ) (T p c : α→List ℕ) (r a : α→ℕ)
    (hk : Primrec k) (hT : Primrec T) (hp : Primrec p) (hc : Primrec c) (hr : Primrec r) (ha : Primrec a) :
    Primrec (fun x=>choose (k x) (T x) (p x) (c x) (r x) (a x)) := by unfold choose;fun_prop
end Primitive
end UniformKServer.RawRowSelect

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                              
section

namespace UniformKServer.RawRows
open RawArithmetic RawWords RawTable RawTyped RawExpansion RawCertificate

theorem selected_row {n k H b : ℕ} {T : List ℕ} (h : rowsOK n k H b T=true)
    (p c : List ℕ) (r : ℕ) (hp : p∈upto n H) (hc : c∈words n k) (hr : r<n) :
    rowOK k b T p c r=true := by
  exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h p hp) c hc) r (List.mem_range.mpr hr)

end UniformKServer.RawRows

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                              
section

namespace UniformKServer.RawTape
open RawTyped

def tape {H b : ℕ} (coins : Fin H→Fin b→Bool) : List ℕ :=
  List.ofFn (fun i=>(BitSampling.bitsEquiv b (coins i)).val)

end UniformKServer.RawTape

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TapeController
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                     
section

namespace UniformKServer.TapeController
open EpochShadow EpochExpectation

abbrev Tape (k M b : ℕ) := Fin (horizon k M) → Fin b → Bool

end UniformKServer.TapeController

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.RawProgram
open Primrec RawCertificate
attribute [fun_prop] RawBits.primitive_bits

def request (a : ℕ) : ℕ := (RawBinary.readNat a.bits).1-1

def fresh (k M b a : ℕ) : List ℕ :=
  (List.range (RawCertificate.horizon k M)).map (fun i=>RawBinary.value ((a.bits.drop (b*i)).take b))

section Primitive
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_natCode (a : α→ℕ) (ha : Primrec a) :
    Primrec (fun x=>natCode (a x)) := by
  unfold natCode
  have hb:=RawBits.primitive_bits.comp ha
  have hr : Primrec (fun x=>List.replicate (a x).bits.length true) := by
    have h := Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp hb))
      (Primrec.const true : Primrec (fun _ : α×ℕ=>true)).to₂
    exact h.of_eq (by intro x;simp)
  exact Primrec.list_append.comp
    (Primrec.list_append.comp hr
      (Primrec.const [false])) hb
@[fun_prop] theorem primitive_request (a : α→ℕ) (ha : Primrec a) :
    Primrec (fun x=>request (a x)) := by unfold request;fun_prop
@[fun_prop] theorem primitive_fresh (k M b a : α→ℕ) (hk : Primrec k) (hM : Primrec M)
    (hb : Primrec b) (ha : Primrec a) : Primrec (fun x=>fresh (k x) (M x) (b x) (a x)) := by
  unfold fresh
  have hm : Primrec (fun p : α×ℕ=>RawBinary.value (((a p.1).bits.drop (b p.1*p.2)).take (b p.1))) :=
    RawBinary.primitive_value _ (Primrec.list_take.comp (by fun_prop)
      (Primrec.list_drop.comp (by fun_prop) (by fun_prop)))
  exact Primrec.list_map (by fun_prop) hm.to₂
@[fun_prop] theorem primitive_get {n : ℕ} (v : α→List.Vector ℕ n) (i : Fin n) (hv : Primrec v) :
    Primrec (fun x=>(v x).get i) := Primrec.vector_get.comp hv (Primrec.const i)
end Primitive

end UniformKServer.RawProgram

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BinaryTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.BinaryTape
open RawBinary

 def word {H b : ℕ} (v : Fin H→Fin b→Bool) : List Bool :=
  (List.ofFn fun i=>List.ofFn (v i)).flatten
 def token {H b : ℕ} (v : Fin H→Fin b→Bool) : ℕ := value (word v++[true])
 @[simp] theorem word_length {H b : ℕ} (v : Fin H→Fin b→Bool) : (word v).length=H*b := by
  simp [word,List.length_flatten,List.sum_ofFn,Finset.sum_const,smul_eq_mul]

end UniformKServer.BinaryTape

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawBlockCharge
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.RawBlockCharge

theorem cost_append {n k : ℕ} (d : RationalMetric n) (g h : History n k)
    (s : Configuration n k) :
    costAlong d s (g++h) = costAlong d s g + costAlong d (finish s g) h := by
  induction g generalizing s with
  | nil => simp [costAlong, finish]
  | cons a g ih => cases a; simp [costAlong, finish, ih, add_assoc]

end UniformKServer.RawBlockCharge


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.RawPartition
open EpochShadow

def pack {n : ℕ} (k : ℕ) : List (Fin n) → List (Fin n) → List (List (Fin n))
  | acc, [] => if acc = [] then [] else [acc]
  | acc, r::w => if k < (acc++[r]).toFinset.card then
      (acc++[r]) :: pack k [] w else pack k (acc++[r]) w

def GoodBlock {n : ℕ} (k : ℕ) (b : List (Fin n)) : Prop :=
  ∃ p r, b = p++[r] ∧ p.toFinset.card ≤ k

end UniformKServer.RawPartition


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.EpochPartition
open RawPartition EpochShadow

def chunks {α : Type} (R : ℕ) (hR : 0 < R) : List α → List (List α)
  | [] => []
  | b::bs => (b::bs).take R :: chunks R hR ((b::bs).drop R)
termination_by bs => bs.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  omega

def epochs {n : ℕ} (k R : ℕ) (hR : 0 < R) (w : List (Fin n)) : List (List (Fin n)) :=
  (chunks R hR (pack k [] w)).map List.flatten

end UniformKServer.EpochPartition




end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BoundaryPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                        
section

namespace UniformKServer.BoundaryPartition
open EpochShadow RawPartition EpochPartition

def join {A : Type} (R : ℕ) : ℕ → List A → List (List A) → List (List A)
  | _,acc,[] => if acc=[] then [] else [acc]
  | c,acc,b::bs => if c+1=R then (acc++b)::join R 0 [] bs else join R (c+1) (acc++b) bs

def split {n : ℕ} (k R : ℕ) : Finset (Fin n) → ℕ → List (Fin n) → List (Fin n) → List (List (Fin n))
  | _,_,acc,[] => if acc=[] then [] else [acc]
  | seen,c,acc,r::w =>
    if k<(insert r seen).card then
      if c+1=R then (acc++[r])::split k R ∅ 0 [] w
      else split k R ∅ (c+1) (acc++[r]) w
    else split k R (insert r seen) c (acc++[r]) w

end UniformKServer.BoundaryPartition

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_DyadicRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer
/-- Downward rounding at every label other than the reserved allowed label.
The reserved label receives the remainder, exactly as in Section 02. -/
noncomputable def roundedRow {k : ℕ} (q : Fin k → ℝ) (j₀ : Fin k) (B : ℕ)
    (j : Fin k) : ℝ :=
  if j = j₀ then
    1 - ∑ i ∈ Finset.univ.erase j₀, (⌊(B : ℝ) * q i⌋₊ : ℝ) / B
  else (⌊(B : ℝ) * q j⌋₊ : ℝ) / B


theorem floor_fraction_bounds {k : ℕ} (q : Fin k → ℝ)
    (hq : ∀ j, 0 ≤ q j) (B : ℕ) (hB : 0 < B) (j : Fin k) :
    0 ≤ (⌊(B : ℝ) * q j⌋₊ : ℝ) / B ∧
    (⌊(B : ℝ) * q j⌋₊ : ℝ) / B ≤ q j ∧
    q j - (⌊(B : ℝ) * q j⌋₊ : ℝ) / B ≤ 1 / B := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hf := Nat.floor_le (mul_nonneg (le_of_lt hb) (hq j))
  have hg := Nat.lt_floor_add_one ((B : ℝ) * q j)
  refine ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hb), ?_, ?_⟩
  · exact (div_le_iff₀ hb).2 (by simpa [mul_comm] using hf)
  · apply (le_div_iff₀ hb).2
    have hb0 : (B : ℝ) ≠ 0 := ne_of_gt hb
    field_simp
    simp only [mul_comm (q j) (B : ℝ)]
    linarith

theorem round_row_sum {k : ℕ} (q : Fin k → ℝ)
    (j₀ : Fin k) (B : ℕ) : ∑ j, roundedRow q j₀ B j = 1 := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀)]
  simp only [roundedRow, ↓reduceIte]
  have he : ∑ x ∈ Finset.univ.erase j₀,
      (if x = j₀ then 1 - ∑ i ∈ Finset.univ.erase j₀,
        (⌊(B : ℝ) * q i⌋₊ : ℝ) / B
       else (⌊(B : ℝ) * q x⌋₊ : ℝ) / B) =
      ∑ x ∈ Finset.univ.erase j₀, (⌊(B : ℝ) * q x⌋₊ : ℝ) / B := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.ne_of_mem_erase hi]
  rw [he]
  ring

theorem round_row_nonneg {k : ℕ} (q : Fin k → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hs : ∑ j, q j = 1)
    (j₀ : Fin k) (B : ℕ) (hB : 0 < B) (j : Fin k) :
    0 ≤ roundedRow q j₀ B j := by
  classical
  unfold roundedRow
  split_ifs
  · have hd : ∑ i ∈ Finset.univ.erase j₀,
        (⌊(B : ℝ) * q i⌋₊ : ℝ) / B ≤ ∑ i ∈ Finset.univ.erase j₀, q i :=
      Finset.sum_le_sum (fun i _ => (floor_fraction_bounds q hq B hB i).2.1)
    have ht := Finset.sum_erase_add Finset.univ q (Finset.mem_univ j₀)
    rw [hs] at ht
    have := hq j₀
    linarith
  · exact (floor_fraction_bounds q hq B hB j).1


end UniformKServer




end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ExecutableDyadic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.ExecutableDyadic

def numerators {k : ℕ} (q : Fin k → ℚ) (j₀ : Fin k) (B : ℕ) (j : Fin k) : ℕ :=
  if j = j₀ then B - ∑ i ∈ Finset.univ.erase j₀, ⌊(B : ℚ) * q i⌋₊
  else ⌊(B : ℚ) * q j⌋₊

def rationalCost {S R : Type*} {k : ℕ} (q : S → R → Fin k → ℚ)
    (next : S → R → Fin k → S) (charge : S → R → Fin k → ℚ) : S → List R → ℚ
  | _, [] => 0
  | s, r::w => ∑ j, q s r j * (charge s r j + rationalCost q next charge (next s r j) w)

theorem natFloor_cast (x : ℚ) : ⌊(x : ℝ)⌋₊ = ⌊x⌋₊ := by
  rw [← Int.floor_toNat, ← Int.floor_toNat, Rat.floor_cast]

theorem numerators_repr {k : ℕ} (q : Fin k → ℚ) (hq : ∀ j, 0 ≤ q j)
    (hs : ∑ j, q j = 1) (j₀ : Fin k) (B : ℕ) (hB : 0 < B) (j : Fin k) :
    (numerators q j₀ B j : ℝ) / B = roundedRow (fun i => (q i : ℝ)) j₀ B j := by
  classical
  have hf (i : Fin k) : ⌊(B : ℝ) * (q i : ℝ)⌋₊ = ⌊(B : ℚ) * q i⌋₊ := by
    simpa using natFloor_cast ((B : ℚ) * q i)
  have hqr (i : Fin k) : (0 : ℝ) ≤ q i := by exact_mod_cast hq i
  have hsr : ∑ i, (q i : ℝ) = 1 := by exact_mod_cast hs
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hS : ∑ i ∈ Finset.univ.erase j₀, ⌊(B : ℚ) * q i⌋₊ ≤ B := by
    have hn := round_row_nonneg (fun i => (q i : ℝ)) hqr hsr j₀ B hB j₀
    simp only [roundedRow, ↓reduceIte, hf, ← Finset.sum_div] at hn
    have hr : (∑ i ∈ Finset.univ.erase j₀, (⌊(B : ℚ) * q i⌋₊ : ℝ)) ≤ B :=
      (div_le_one hb).mp (by linarith)
    exact_mod_cast hr
  by_cases hj : j = j₀
  · subst j
    simp only [numerators, roundedRow, ↓reduceIte, Nat.cast_sub hS, Nat.cast_sum, hf]
    rw [sub_div, div_self (ne_of_gt hb), Finset.sum_div]
  · simp [numerators, roundedRow, hj, hf]

theorem numerators_sum {k : ℕ} (q : Fin k → ℚ) (hq : ∀ j, 0 ≤ q j)
    (hs : ∑ j, q j = 1) (j₀ : Fin k) (B : ℕ) (hB : 0 < B) :
    ∑ j, numerators q j₀ B j = B := by
  have ht := round_row_sum (fun i => (q i : ℝ)) j₀ B
  simp only [← numerators_repr q hq hs j₀ B hB, ← Finset.sum_div] at ht
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
  have heq := (div_eq_one_iff_eq hb).mp ht
  exact_mod_cast heq

end UniformKServer.ExecutableDyadic



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FourierMotzkin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.FourierMotzkin

structure Row (n : ℕ) where
  constant : ℚ
  coefficient : Fin n → ℚ
  deriving DecidableEq

namespace Row

def eval {n : ℕ} {K : Type*} [Field K] (r : Row n) (x : Fin n → K) : K :=
  (r.constant : K) + ∑ i, (r.coefficient i : K) * x i

def tail {n : ℕ} (r : Row (n+1)) : Row n :=
  ⟨r.constant, fun i => r.coefficient i.succ⟩

def scale {n : ℕ} (c : ℚ) (r : Row n) : Row n :=
  ⟨c*r.constant, fun i => c*r.coefficient i⟩

def sub {n : ℕ} (r s : Row n) : Row n :=
  ⟨r.constant-s.constant, fun i => r.coefficient i-s.coefficient i⟩

def bound {n : ℕ} (r : Row (n+1)) : Row n :=
  r.tail.scale (-1 / r.coefficient 0)

section Algebra
variable {n : ℕ} {K : Type*} [Field K] [CharZero K]

@[simp] theorem eval_scale (c : ℚ) (r : Row n) (x : Fin n → K) :
    (r.scale c).eval x = (c : K) * r.eval x := by
  simp only [eval, scale, Rat.cast_mul, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem eval_sub (r s : Row n) (x : Fin n → K) :
    (r.sub s).eval x = r.eval x - s.eval x := by
  simp only [eval, sub, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
  ring

omit [CharZero K] in
@[simp] theorem eval_cons (r : Row (n+1)) (z : K) (x : Fin n → K) :
    r.eval (Fin.cons z x) = (r.coefficient 0 : K) * z + r.tail.eval x := by
  simp only [eval, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, tail]
  ring

@[simp] theorem eval_bound (r : Row (n+1)) (x : Fin n → K) :
    r.bound.eval x = - r.tail.eval x / (r.coefficient 0 : K) := by
  simp only [bound, eval_scale, Rat.cast_div, Rat.cast_neg, Rat.cast_one]
  ring

end Algebra

@[simp] theorem eval_rat_cast {n : ℕ} (r : Row n) (x : Fin n → ℚ) :
    r.eval (fun i => (x i : ℝ)) = ((r.eval x : ℚ) : ℝ) := by
  simp [eval]

variable {n : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

 theorem negative_iff (r : Row (n+1)) (z : K) (x : Fin n → K)
    (h : r.coefficient 0 < 0) :
    r.eval (Fin.cons z x) ≤ 0 ↔ r.bound.eval x ≤ z := by
  have h' : (r.coefficient 0 : K) < 0 := by exact_mod_cast h
  rw [eval_cons, eval_bound, div_le_iff_of_neg h']
  constructor <;> intro H <;> nlinarith

 theorem positive_iff (r : Row (n+1)) (z : K) (x : Fin n → K)
    (h : 0 < r.coefficient 0) :
    r.eval (Fin.cons z x) ≤ 0 ↔ z ≤ r.bound.eval x := by
  have h' : (0 : K) < r.coefficient 0 := by exact_mod_cast h
  rw [eval_cons, eval_bound, le_div_iff₀ h']
  constructor <;> intro H <;> nlinarith

omit [IsStrictOrderedRing K] in
 theorem zero_iff (r : Row (n+1)) (z : K) (x : Fin n → K)
    (h : r.coefficient 0 = 0) :
    r.eval (Fin.cons z x) ≤ 0 ↔ r.tail.eval x ≤ 0 := by
  simp [h]

end Row

def lower {n : ℕ} (R : List (Row (n+1))) : List (Row n) :=
  (R.filter fun r => r.coefficient 0 < 0).map Row.bound

def upper {n : ℕ} (R : List (Row (n+1))) : List (Row n) :=
  (R.filter fun r => 0 < r.coefficient 0).map Row.bound

def independent {n : ℕ} (R : List (Row (n+1))) : List (Row n) :=
  (R.filter fun r => r.coefficient 0 = 0).map Row.tail

def project {n : ℕ} (R : List (Row (n+1))) : List (Row n) :=
  independent R ++ (lower R).flatMap fun l => (upper R).map fun u => l.sub u

def Satisfies {n : ℕ} {K : Type*} [Field K] [LE K]
    (R : List (Row n)) (x : Fin n → K) : Prop := ∀ r ∈ R, r.eval x ≤ 0

section Projection
variable {n : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

 theorem satisfies_cons_iff (R : List (Row (n+1))) (z : K) (x : Fin n → K) :
    Satisfies R (Fin.cons z x) ↔
      Satisfies (independent R) x ∧
      (∀ l ∈ lower R, l.eval x ≤ z) ∧ (∀ u ∈ upper R, z ≤ u.eval x) := by
  constructor
  · intro H
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hs, hz⟩ := List.mem_filter.mp hs
      exact (s.zero_iff z x (by simpa using hz)).mp (H s hs)
    · intro r hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hs, hn⟩ := List.mem_filter.mp hs
      exact (s.negative_iff z x (by simpa using hn)).mp (H s hs)
    · intro r hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hs, hp⟩ := List.mem_filter.mp hs
      exact (s.positive_iff z x (by simpa using hp)).mp (H s hs)
  · rintro ⟨hz, hl, hu⟩ r hr
    rcases lt_trichotomy (r.coefficient 0) 0 with hn | he | hp
    · apply (r.negative_iff z x hn).mpr
      apply hl r.bound
      simp only [lower, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨r, ⟨hr, hn⟩, rfl⟩
    · apply (r.zero_iff z x he).mpr
      apply hz r.tail
      simp only [independent, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨r, ⟨hr, he⟩, rfl⟩
    · apply (r.positive_iff z x hp).mpr
      apply hu r.bound
      simp only [upper, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨r, ⟨hr, hp⟩, rfl⟩

 theorem satisfies_project_iff (R : List (Row (n+1))) (x : Fin n → K) :
    Satisfies (project R) x ↔ Satisfies (independent R) x ∧
      ∀ l ∈ lower R, ∀ u ∈ upper R, l.eval x ≤ u.eval x := by
  constructor
  · intro H
    refine ⟨fun r hr => H r (List.mem_append_left _ hr), ?_⟩
    intro l hl u hu
    have hs : l.sub u ∈ project R := by
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      exact ⟨l, hl, List.mem_map.mpr ⟨u, hu, rfl⟩⟩
    simpa only [Row.eval_sub, sub_nonpos] using H (l.sub u) hs
  · rintro ⟨hz, hp⟩ r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hz r hr
    · obtain ⟨l, hl, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
      simpa only [Row.eval_sub, sub_nonpos] using hp l hl u hu

 theorem project_of_satisfies (R : List (Row (n+1))) (x : Fin (n+1) → K)
    (H : Satisfies R x) : Satisfies (project R) (Fin.tail x) := by
  have hx : x = Fin.cons (x 0) (Fin.tail x) := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [hx, satisfies_cons_iff] at H
  rw [satisfies_project_iff]
  exact ⟨by simpa using H.1, fun l hl u hu => le_trans (H.2.1 l hl) (H.2.2 u hu)⟩

end Projection

def high {K : Type*} [LinearOrder K] (a : K) (l : List K) : K := l.foldr max a

def low {K : Type*} [LinearOrder K] (a : K) (l : List K) : K := l.foldr min a

 theorem high_le_iff {K : Type*} [LinearOrder K] (a z : K) (l : List K) :
    high a l ≤ z ↔ a ≤ z ∧ ∀ b ∈ l, b ≤ z := by
  induction l with
  | nil => simp [high]
  | cons b l ih =>
    simp only [high, List.foldr_cons, max_le_iff] at ⊢
    change (b ≤ z ∧ high a l ≤ z) ↔ _
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

 theorem le_low_iff {K : Type*} [LinearOrder K] (a z : K) (l : List K) :
    z ≤ low a l ↔ z ≤ a ∧ ∀ b ∈ l, z ≤ b := by
  induction l with
  | nil => simp [low]
  | cons b l ih =>
    simp only [low, List.foldr_cons, le_min_iff] at ⊢
    change (z ≤ b ∧ z ≤ low a l) ↔ _
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

def intervalPivot {K : Type*} [Zero K] [LinearOrder K] (l u : List K) : K :=
  match l with
  | a :: as => high a as
  | [] => match u with
    | b :: bs => low b bs
    | [] => 0

/-- Reversing one elimination. With no lower bound choose the least upper
    bound; with no bounds choose zero, exactly as in the source. -/
def pivot {n : ℕ} {K : Type*} [Field K] [LinearOrder K]
    (R : List (Row (n+1))) (x : Fin n → K) : K :=
  intervalPivot ((lower R).map (fun r => r.eval x))
    ((upper R).map (fun r => r.eval x))

 theorem pivot_bounds {K : Type*} [Zero K] [LinearOrder K] {l u : List K}
    (H : ∀ a ∈ l, ∀ b ∈ u, a ≤ b) :
    (∀ a ∈ l, a ≤ intervalPivot l u) ∧ ∀ b ∈ u, intervalPivot l u ≤ b := by
  cases l with
  | nil =>
    simp only [List.not_mem_nil, false_implies, implies_true, true_and]
    cases u with
    | nil => simp
    | cons b bs =>
      have h := (le_low_iff b (low b bs) bs).mp (le_refl _)
      simpa only [intervalPivot, List.mem_cons, forall_eq_or_imp] using h
  | cons a as =>
    refine ⟨?_, ?_⟩
    · have h := (high_le_iff a (high a as) as).mp (le_refl _)
      simpa only [intervalPivot, List.mem_cons, forall_eq_or_imp] using h
    · intro b hb
      apply (high_le_iff a b as).mpr
      exact ⟨H a (by simp) b hb, fun x hx => H x (by simp [hx]) b hb⟩

 theorem satisfies_pivot {n : ℕ} {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (R : List (Row (n+1))) (x : Fin n → K) (H : Satisfies (project R) x) :
    Satisfies R (Fin.cons (pivot R x) x) := by
  obtain ⟨hz, hp⟩ := (satisfies_project_iff R x).mp H
  have hp' : ∀ a ∈ (lower R).map (fun r => r.eval x),
      ∀ b ∈ (upper R).map (fun r => r.eval x), a ≤ b := by
    intro a ha b hb
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
    exact hp l hl u hu
  have h := pivot_bounds hp'
  apply (satisfies_cons_iff R (pivot R x) x).mpr
  exact ⟨hz, fun l hl => h.1 _ (List.mem_map.mpr ⟨l, hl, rfl⟩),
    fun u hu => h.2 _ (List.mem_map.mpr ⟨u, hu, rfl⟩)⟩

/-- The objective is the final coordinate, retained through every projection. -/
def objective {n : ℕ} {K : Type*} (x : Fin (n+1) → K) : K := x (Fin.last n)

def baseValue (R : List (Row 1)) : ℚ :=
  high 0 ((lower R).map (fun r => r.constant))

/-- Exact rational arithmetic and comparisons only. The nonnegative objective
    constraint is imposed by the base case even if not listed among the rows. -/
def optimize : (n : ℕ) → List (Row (n+1)) → Option (Fin (n+1) → ℚ)
  | 0, R =>
    let x := Fin.cons (baseValue R) Fin.elim0
    if R.all (fun r => decide (r.eval x ≤ 0)) then some x else none
  | n+1, R => (optimize n (project R)).map (fun x => Fin.cons (pivot R x) x)

@[simp] theorem high_rat_cast (a : ℚ) (l : List ℚ) :
    ((high a l : ℚ) : ℝ) = high (a : ℝ) (l.map (fun b : ℚ => (b : ℝ))) := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa only [high, List.foldr_cons, List.map_cons, Rat.cast_max] using congrArg (max (b : ℝ)) ih

@[simp] theorem eval_empty {K : Type*} [Field K] (r : Row 0) (x : Fin 0 → K) :
    r.eval x = r.constant := by simp [Row.eval]

 theorem one_cons {K : Type*} (y : Fin 1 → K) :
    y = Fin.cons (objective y) Fin.elim0 := by
  ext i
  rw [Fin.eq_zero i]
  rfl

 theorem baseValue_nonneg (R : List (Row 1)) : 0 ≤ baseValue R :=
  ((high_le_iff 0 (baseValue R) _).mp (le_refl _)).1

 theorem baseValue_minimal (R : List (Row 1)) (y : Fin 1 → ℝ)
    (hy : 0 ≤ objective y) (hR : Satisfies R y) :
    (baseValue R : ℝ) ≤ objective y := by
  rw [one_cons y, satisfies_cons_iff] at hR
  rw [baseValue, high_rat_cast, high_le_iff]
  refine ⟨by simpa only [Rat.cast_zero] using hy, ?_⟩
  intro b hb
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  simpa only [eval_empty] using hR.2.1 r hr

 theorem baseValue_feasible (R : List (Row 1)) (y : Fin 1 → ℝ)
    (hy : 0 ≤ objective y) (hR : Satisfies R y) :
    Satisfies R (Fin.cons (baseValue R) (Fin.elim0 : Fin 0 → ℚ)) := by
  have hmin := baseValue_minimal R y hy hR
  rw [one_cons y, satisfies_cons_iff] at hR
  apply (satisfies_cons_iff R _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    have h := hR.1 r hr
    simp only [eval_empty] at h ⊢
    exact_mod_cast h
  · intro r hr
    simp only [eval_empty]
    exact ((high_le_iff 0 (baseValue R) _).mp (le_refl _)).2
      r.constant (List.mem_map.mpr ⟨r, hr, rfl⟩)
  · intro r hr
    have h := le_trans hmin (hR.2.2 r hr)
    simp only [eval_empty] at h ⊢
    exact_mod_cast h

@[simp] theorem objective_cons {n : ℕ} {K : Type*} (a : K) (x : Fin (n+1) → K) :
    objective (Fin.cons a x) = objective x := Fin.cons_last (n := n) (α := fun _ => K) a x

@[simp] theorem objective_tail {n : ℕ} {K : Type*} (x : Fin (n+2) → K) :
    objective (Fin.tail x) = objective x := rfl

/-- The exact finite rational optimizer succeeds whenever the rational rows
have a real feasible point with nonnegative objective; its rational output is
feasible and minimizes the objective against every such real point. -/
theorem optimize_rational_attainment (n : ℕ) (R : List (Row (n+1)))
    (H : ∃ y : Fin (n+1) → ℝ, 0 ≤ objective y ∧ Satisfies R y) :
    ∃ x : Fin (n+1) → ℚ, optimize n R = some x ∧
      0 ≤ objective x ∧ Satisfies R x ∧
      ∀ y : Fin (n+1) → ℝ, 0 ≤ objective y → Satisfies R y →
        ((objective x : ℚ) : ℝ) ≤ objective y := by
  induction n with
  | zero =>
    obtain ⟨y, hy, hR⟩ := H
    have hb := baseValue_feasible R y hy hR
    have ht : R.all (fun r => decide (r.eval (Fin.cons (baseValue R) Fin.elim0) ≤ 0)) = true := by
      rw [List.all_eq_true]
      intro r hr
      exact decide_eq_true (hb r hr)
    refine ⟨Fin.cons (baseValue R) Fin.elim0, ?_, baseValue_nonneg R, hb, ?_⟩
    · simp only [optimize, ht, ↓reduceIte]
    · exact fun y hy hR => baseValue_minimal R y hy hR
  | succ n ih =>
    have HP : ∃ y : Fin (n+1) → ℝ, 0 ≤ objective y ∧ Satisfies (project R) y := by
      obtain ⟨y, hy, hR⟩ := H
      exact ⟨Fin.tail y, hy, project_of_satisfies R y hR⟩
    obtain ⟨x, hx, hn, hs, hm⟩ := ih (project R) HP
    refine ⟨Fin.cons (pivot R x) x, ?_, ?_, satisfies_pivot R x hs, ?_⟩
    · simp only [optimize, hx, Option.map_some]
    · simpa only [objective_cons] using hn
    · intro y hy hR
      simpa only [objective_cons, objective_tail] using
        hm (Fin.tail y) hy (project_of_satisfies R y hR)

end UniformKServer.FourierMotzkin

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OfflineDynamic
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.OfflineDynamic
variable {n k : ℕ} [NeZero k]

def minimum (c : Fin k → ℚ) : ℚ :=
  (Finset.univ.image c).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)

def optRat (d : RationalMetric n) : Configuration n k → List (Fin n) → ℚ
  | _, [] => 0
  | s, r::w => minimum (fun j => d.distance (s j) r + optRat d (serve s r j) w)

theorem minimum_le (c : Fin k → ℚ) (j : Fin k) : minimum c ≤ c j := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

theorem minimum_attained (c : Fin k → ℚ) : ∃ j, minimum c = c j := by
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp (Finset.min'_mem (Finset.univ.image c)
    (Finset.image_nonempty.mpr Finset.univ_nonempty))
  exact ⟨j, he.symm⟩

theorem optRat_attained (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) :
    ∃ h : History n k, h.map Prod.fst = w ∧ costAlong d s h = (optRat d s w : ℝ) := by
  induction w generalizing s with
  | nil => exact ⟨[], rfl, by simp [costAlong,optRat]⟩
  | cons r w ih =>
    obtain ⟨j,hj⟩ := minimum_attained (fun j => d.distance (s j) r + optRat d (serve s r j) w)
    obtain ⟨h,hh,hcost⟩ := ih (serve s r j)
    refine ⟨(r,j)::h, by simp only [List.map_cons,hh], ?_⟩
    simp only [optRat, hj, costAlong, Rat.cast_add, hcost]

theorem optRat_lower (d : RationalMetric n) (s : Configuration n k) (h : History n k) :
    (optRat d s (h.map Prod.fst) : ℝ) ≤ costAlong d s h := by
  induction h generalizing s with
  | nil => simp [optRat,costAlong]
  | cons a h ih =>
    rcases a with ⟨r,j⟩
    have hj := minimum_le (fun j => d.distance (s j) r + optRat d (serve s r j) (h.map Prod.fst)) j
    have hj' : (minimum (fun j => d.distance (s j) r + optRat d (serve s r j) (h.map Prod.fst)) : ℝ) ≤
      (d.distance (s j) r : ℝ)+(optRat d (serve s r j) (h.map Prod.fst) : ℝ) := by exact_mod_cast hj
    exact hj'.trans (add_le_add (le_refl _) (ih (serve s r j)))

theorem offline_eq_optRat (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) :
    offlineCost d s w = (optRat d s w : ℝ) := by
  obtain ⟨h,hh,hcost⟩ := optRat_attained d s w
  apply le_antisymm
  · apply csInf_le
    · refine ⟨(optRat d s w : ℝ), ?_⟩
      rintro c ⟨g,hg,rfl⟩
      rw [← hg]
      exact optRat_lower d s g
    · exact ⟨h,hh,hcost.symm⟩
  · apply le_csInf
    · exact ⟨costAlong d s h, h, hh, rfl⟩
    · rintro c ⟨g,hg,rfl⟩
      rw [← hg]
      exact optRat_lower d s g

end UniformKServer.OfflineDynamic

/-!
Exact rational minimization used by uniform-computation Section 02,
Proposition `prop:finite-table`, paragraph "Exact rational attainment".
An affine row is constrained to be ≤ 0. The last coordinate is the
nonnegative objective a; all other coordinates are eliminated in order.
The algorithm is executable rational arithmetic; no real optimization oracle.
-/

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LinearProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.EffectiveLP
open FourierMotzkin

/-- Computable increasing-code enumeration. No finite-choice oracle. -/
def enumerate {A : Type*} [Fintype A] [Encodable A] : List A :=
  letI : LinearOrder A := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  Finset.univ.sort (· ≤ ·)

def index (A : Type*) [Fintype A] [Encodable A] : A ≃ Fin (Fintype.card A) :=
  letI : LinearOrder A := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  (Fintype.orderIsoFinOfCardEq A rfl).toEquiv.symm

theorem mem_enumerate {A : Type*} [Fintype A] [Encodable A] (a : A) :
    a ∈ (enumerate : List A) := by
  simp [enumerate]


/-- Exactly the finite source word-prefix set, explicitly enumerated. -/
def words (n : ℕ) : ℕ → Finset (List (Fin n))
  | 0 => {[]}
  | H+1 => insert [] (Finset.univ.biUnion fun r => (words n H).image (r::·))

def Word (n H : ℕ) := {w : List (Fin n) // w ∈ words n H}
instance instFintypeWord (n H : ℕ) : Fintype (Word n H) := inferInstanceAs (Fintype {w // w ∈ words n H})
instance instDecidableEqWord (n H : ℕ) : DecidableEq (Word n H) := inferInstanceAs (DecidableEq {w // w ∈ words n H})
instance instEncodableWord (n H : ℕ) : Encodable (Word n H) := inferInstanceAs (Encodable {w // w ∈ words n H})

def Config (n k : ℕ) := {c : Configuration n k // Function.Injective c}
instance instFintypeConfig (n k : ℕ) : Fintype (Config n k) := inferInstanceAs (Fintype {c : Configuration n k // Function.Injective c})
instance instDecidableEqConfig (n k : ℕ) : DecidableEq (Config n k) := inferInstanceAs (DecidableEq {c : Configuration n k // Function.Injective c})
instance instEncodableConfig (n k : ℕ) : Encodable (Config n k) := inferInstanceAs (Encodable {c : Configuration n k // Function.Injective c})

/-- The source allowed-label set, not a relaxed transition relation. -/
def labels {n k : ℕ} (c : Config n k) (r : Fin n) : Finset (Fin k) :=
  if ∃ j, c.val j = r then Finset.univ.filter (fun j => c.val j = r) else Finset.univ

def Label {n k : ℕ} (c : Config n k) (r : Fin n) := {j : Fin k // j ∈ labels c r}
instance instFintypeLabel {n k : ℕ} (c : Config n k) (r : Fin n) : Fintype (Label c r) :=
  inferInstanceAs (Fintype {j // j ∈ labels c r})
instance instDecidableEqLabel {n k : ℕ} (c : Config n k) (r : Fin n) : DecidableEq (Label c r) :=
  inferInstanceAs (DecidableEq {j // j ∈ labels c r})
instance instEncodableLabel {n k : ℕ} (c : Config n k) (r : Fin n) : Encodable (Label c r) :=
  inferInstanceAs (Encodable {j // j ∈ labels c r})

def Short (n H : ℕ) := {w : Word n H // w.val.length < H}
instance instFintypeShort (n H : ℕ) : Fintype (Short n H) := inferInstanceAs (Fintype {w : Word n H // w.val.length < H})
instance instDecidableEqShort (n H : ℕ) : DecidableEq (Short n H) := inferInstanceAs (DecidableEq {w : Word n H // w.val.length < H})
instance instEncodableShort (n H : ℕ) : Encodable (Short n H) := inferInstanceAs (Encodable {w : Word n H // w.val.length < H})

-- A finite free variable for each displayed source p and allowed f.
abbrev Edge (n k H : ℕ) := (_ : Short n H) × (r : Fin n) × (c : Config n k) × Label c r
abbrev Variable (n k H : ℕ) := (Word n H × Config n k) ⊕ Edge n k H

structure BoundedFlow (n k H : ℕ) (K : Type*) where
  mass : Word n H → Config n k → K
  flow : (w : Short n H) → (r : Fin n) → (c : Config n k) → Label c r → K

def toAssignment {n k H : ℕ} {K : Type*} (F : BoundedFlow n k H K) : Variable n k H → K
  | .inl (w,c) => F.mass w c
  | .inr ⟨w,r,c,j⟩ => F.flow w r c j

def ofAssignment {n k H : ℕ} {K : Type*} (x : Variable n k H → K) : BoundedFlow n k H K where
  mass w c := x (.inl (w,c))
  flow w r c j := x (.inr ⟨w,r,c,j⟩)

namespace Form
variable {V : Type*} [Fintype V] [DecidableEq V] [Encodable V]

abbrev RowV (V : Type*) [Fintype V] := _root_.OAI.UniformKServer.FourierMotzkin.Row (Fintype.card V + 1)

def var (v : V) : RowV V :=
  ⟨0, fun i => if i = (index V v).castSucc then 1 else 0⟩
def objective : RowV V := ⟨0, fun i => if i = Fin.last (Fintype.card V) then 1 else 0⟩
def constant (a : ℚ) : RowV V := ⟨a, fun _ => 0⟩
def sum {I : Type*} (S : Finset I) (f : I → RowV V) : RowV V :=
  ⟨∑ i ∈ S, (f i).constant, fun j => ∑ i ∈ S, (f i).coefficient j⟩

def eqRows (f : RowV V) : List (RowV V) := [f, f.scale (-1)]
def vector {K : Type*} (x : V → K) (a : K) : Fin (Fintype.card V + 1) → K :=
  Fin.lastCases a (fun i => x ((index V).symm i))
def recover {K : Type*} (x : Fin (Fintype.card V + 1) → K) : V → K :=
  fun v => x ((index V v).castSucc)
end Form

theorem mem_words {n H : ℕ} (w : List (Fin n)) : w ∈ words n H ↔ w.length ≤ H := by
  induction H generalizing w with
  | zero => simp [words]
  | succ H ih =>
    cases w with
    | nil => simp [words]
    | cons r w =>
      simp only [words, Finset.mem_insert, List.cons_ne_nil, false_or, Finset.mem_biUnion,
        Finset.mem_univ, true_and, Finset.mem_image, List.cons.injEq, List.length_cons]
      constructor
      · rintro ⟨r',w',hw',hr,hw⟩
        subst r'; subst w'
        exact Nat.succ_le_succ ((ih w).mp hw')
      · intro hw
        exact ⟨r,w,(ih w).mpr (Nat.le_of_succ_le_succ hw),rfl,rfl⟩

theorem label_injective {n k : ℕ} (c : Config n k) (r : Fin n) (j : Label c r) :
    Function.Injective (serve c.val r j.val) := by
  classical
  have hj := j.property
  unfold labels at hj
  split_ifs at hj with hh
  · have he : c.val j.val = r := (Finset.mem_filter.mp hj).2
    have hs : serve c.val r j.val = c.val := by
      unfold serve
      conv_lhs => arg 3; rw [← he]
      exact Function.update_eq_self _ _
    rw [hs]
    exact c.property
  · intro a b hab
    by_cases ha : a = j.val
    · subst a
      by_cases hb : b = j.val
      · exact hb.symm
      · simp only [serve, Function.update_self, Function.update_of_ne hb] at hab
        exact (hh ⟨b,hab.symm⟩).elim
    · by_cases hb : b = j.val
      · subst b
        simp only [serve, Function.update_self, Function.update_of_ne ha] at hab
        exact (hh ⟨a,hab⟩).elim
      · simp only [serve, Function.update_of_ne ha, Function.update_of_ne hb] at hab
        exact c.property hab

def step {n k : ℕ} (c : Config n k) (r : Fin n) (j : Label c r) : Config n k :=
  ⟨serve c.val r j.val, label_injective c r j⟩

def rootWord (n H : ℕ) : Word n H := ⟨[], (mem_words []).mpr (Nat.zero_le _)⟩
def extend {n H : ℕ} (w : Short n H) (r : Fin n) : Word n H :=
  ⟨w.val.val++[r], (mem_words _).mpr (by simpa using w.property)⟩

def prefixNode {n H : ℕ} (w : Word n H) (i : Fin w.val.length) : Short n H :=
  ⟨⟨w.val.take i, (mem_words _).mpr
    (by simp only [List.length_take]; exact (Nat.min_le_right _ _).trans ((mem_words _).mp w.property))⟩,
    by have hw := (mem_words _).mp w.property
       simp only [List.length_take]
       omega⟩

abbrev Row (n k H : ℕ) := FourierMotzkin.Row (Fintype.card (Variable n k H)+1)

def massRow {n k H : ℕ} (w : Word n H) (c : Config n k) : Row n k H :=
  Form.var (.inl (w,c))
def flowRow {n k H : ℕ} (w : Short n H) (r : Fin n)
    (c : Config n k) (j : Label c r) : Row n k H :=
  Form.var (.inr ⟨w,r,c,j⟩)

def costRow {n k H : ℕ} (d : RationalMetric n) (w : Word n H) : Row n k H :=
  Form.sum Finset.univ fun i : Fin w.val.length =>
    Form.sum Finset.univ fun c : Config n k =>
      Form.sum Finset.univ fun j : Label c w.val[i] =>
        (flowRow (prefixNode w i) w.val[i] c j).scale (d.distance (c.val j.val) w.val[i])

namespace Form
variable {V : Type*} [Fintype V] {K : Type*}

theorem recover_vector [Encodable V] (x : V → K) (a : K) : recover (vector x a) = x := by
  funext v
  simp [recover, vector]

theorem objective_vector [Encodable V] (x : V → K) (a : K) :
    FourierMotzkin.objective (vector x a) = a := by
  simp [FourierMotzkin.objective, vector]

variable [Field K]

theorem eval_var [Encodable V] (v : V) (x : Fin (Fintype.card V+1) → K) :
    (var v).eval x = recover x v := by
  classical
  simp [var, FourierMotzkin.Row.eval, recover, ite_mul, apply_ite]

theorem eval_objective (x : Fin (Fintype.card V+1) → K) :
    (objective (V := V)).eval x = FourierMotzkin.objective x := by
  simp [objective, FourierMotzkin.objective, FourierMotzkin.Row.eval, ite_mul, apply_ite]

theorem eval_constant (a : ℚ) (x : Fin (Fintype.card V+1) → K) :
    (constant (V := V) a).eval x = (a : K) := by
  simp [constant, FourierMotzkin.Row.eval]

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem eval_sum {I : Type*} (S : Finset I) (f : I → RowV V)
    (x : Fin (Fintype.card V+1) → K) :
    (sum S f).eval x = ∑ i ∈ S, (f i).eval x := by
  simp only [sum, FourierMotzkin.Row.eval, Rat.cast_sum, Finset.sum_mul,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]

theorem eqRows_iff (f : RowV V) (x : Fin (Fintype.card V+1) → K) :
    Satisfies (eqRows f) x ↔ f.eval x = 0 := by
  simp only [Satisfies, eqRows, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, FourierMotzkin.Row.eval_scale,
    Rat.cast_neg, Rat.cast_one, neg_one_mul]
  constructor
  · rintro ⟨ha,hb⟩
    exact le_antisymm ha (neg_nonpos.mp hb)
  · intro hh
    simp [hh]

end Form

theorem satisfies_append {m : ℕ} {K : Type*} [Field K] [LE K]
    (R S : List (FourierMotzkin.Row m)) (x : Fin m → K) :
    Satisfies (R++S) x ↔ Satisfies R x ∧ Satisfies S x := by
  constructor
  · intro h
    exact ⟨fun r hr => h r (List.mem_append_left S hr), fun r hr => h r (List.mem_append_right R hr)⟩
  · rintro ⟨hR,hS⟩ r hr
    exact (List.mem_append.mp hr).elim (hR r) (hS r)

theorem satisfies_flatMap {m : ℕ} {I K : Type*} [Fintype I] [Encodable I] [Field K] [LE K]
    (f : I → List (FourierMotzkin.Row m)) (x : Fin m → K) :
    Satisfies (enumerate.flatMap f) x ↔ ∀ i, Satisfies (f i) x := by
  simp only [Satisfies, List.mem_flatMap, mem_enumerate, true_and, forall_exists_index]
  exact forall_comm

theorem satisfies_singleton {m : ℕ} {K : Type*} [Field K] [LE K]
    (r : FourierMotzkin.Row m) (x : Fin m → K) : Satisfies [r] x ↔ r.eval x ≤ 0 := by
  simp [Satisfies]

theorem eval_costRow {n k H : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (d : RationalMetric n) (w : Word n H) (x : Fin (Fintype.card (Variable n k H)+1) → K) :
    (costRow d w).eval x =
      ∑ i : Fin w.val.length, ∑ c, ∑ j : Label c w.val[i],
        (ofAssignment (Form.recover x)).flow (prefixNode w i) w.val[i] c j *
          (d.distance (c.val j.val) w.val[i] : K) := by
  simp only [costRow, Form.eval_sum, FourierMotzkin.Row.eval_scale, flowRow, Form.eval_var,
    ofAssignment]
  congr 1
  funext i
  congr 1
  funext c
  congr 1
  funext j
  exact mul_comm _ _

theorem eval_if {m : ℕ} {K : Type*} [Field K] (p : Prop) [Decidable p]
    (f g : FourierMotzkin.Row m) (x : Fin m → K) :
    (if p then f else g).eval x = if p then f.eval x else g.eval x := by
  split_ifs <;> rfl

end UniformKServer.EffectiveLP


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ExactOptimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.EffectiveLP

variable {n k H : ℕ} [NeZero k]

theorem labels_inhabited (c : Config n k) (r : Fin n) : (labels c r).Nonempty := by
  unfold labels
  split_ifs with hh
  · obtain ⟨j,hj⟩ := hh
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  · exact Finset.univ_nonempty

def chosen (c : Config n k) (r : Fin n) : Label c r :=
  ⟨(labels c r).min' (labels_inhabited c r), Finset.min'_mem _ _⟩

def lazyRun (u : Config n k) (w : List (Fin n)) : Config n k :=
  w.foldl (fun c r => step c r (chosen c r)) u

@[simp] theorem lazyRun_nil (u : Config n k) : lazyRun u [] = u := rfl

@[simp] theorem lazyRun_append (u : Config n k) (w : List (Fin n)) (r : Fin n) :
    lazyRun u (w++[r]) = step (lazyRun u w) r (chosen (lazyRun u w) r) := by
  simp [lazyRun, List.foldl_append]


omit [NeZero k] in
theorem history_nonneg (d : RationalMetric n) (s : Configuration n k) (h : History n k) :
    0 ≤ costAlong d s h := by
  induction h generalizing s with
  | nil => exact le_rfl
  | cons a h ih => exact add_nonneg (by exact_mod_cast d.nonneg _ _) (ih _)

theorem opt_nonneg (d : RationalMetric n) (s : Configuration n k) (w : List (Fin n)) :
    0 ≤ (OfflineDynamic.optRat d s w : ℝ) := by
  obtain ⟨h,hh,hcost⟩ := OfflineDynamic.optRat_attained d s w
  rw [← hcost]
  exact history_nonneg d s h

end UniformKServer.EffectiveLP

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.FiniteFlow
variable {R C J : Type*} [Fintype C] [Fintype J] [DecidableEq C] [DecidableEq J]

structure Data (R C J : Type*) where
  mass : List R → C → ℚ
  flow : List R → R → C → J → ℚ

structure Valid (F : Data R C J) (T : C → R → J → C)
    (allowed : C → R → J → Prop) (initial : C) (H : ℕ) : Prop where
  mass_nonneg : ∀ w, w.length ≤ H → ∀ c, 0 ≤ F.mass w c
  mass_total : ∀ w, w.length ≤ H → ∑ c, F.mass w c = 1
  initial : ∀ c, F.mass [] c = if c = initial then 1 else 0
  flow_nonneg : ∀ w, w.length < H → ∀ r c j, 0 ≤ F.flow w r c j
  support : ∀ w, w.length < H → ∀ r c j, ¬allowed c r j → F.flow w r c j = 0
  outflow : ∀ w, w.length < H → ∀ r c, ∑ j, F.flow w r c j = F.mass w c
  inflow : ∀ w, w.length < H → ∀ r c',
    ∑ c, ∑ j, (if T c r j = c' then F.flow w r c j else 0) = F.mass (w++[r]) c'

/-- All rows are explicitly defined, even outside the construction horizon. -/
def row (F : Data R C J) (fallback : C → R → J) (H : ℕ)
    (w : List R) (r : R) (c : C) (j : J) : ℚ :=
  if w.length < H ∧ F.mass w c ≠ 0 then F.flow w r c j / F.mass w c
  else if j = fallback c r then 1 else 0

def cost (q : List R → R → C → J → ℚ) (T : C → R → J → C)
    (d : C → R → J → ℚ) : List R → C → List R → ℚ
  | _, _, [] => 0
  | w, c, r :: rs => ∑ j, q w r c j * (d c r j + cost q T d (w++[r]) (T c r j) rs)

def flowCost (F : Data R C J) (d : C → R → J → ℚ) : List R → List R → ℚ
  | _, [] => 0
  | w, r :: rs => (∑ c, ∑ j, F.flow w r c j*d c r j) + flowCost F d (w++[r]) rs

-- PROOFS

variable (F : Data R C J) (T : C → R → J → C)
  (allowed : C → R → J → Prop) (initial : C) (H : ℕ)
  (fallback : C → R → J)
  (hF : Valid F T allowed initial H)

include hF

omit [DecidableEq J] in
theorem zero_flow (w : List R) (hw : w.length < H) (r : R) (c : C)
    (hp : F.mass w c = 0) (j : J) : F.flow w r c j = 0 := by
  have hn := hF.flow_nonneg w hw r c j
  have hs := Finset.single_le_sum (fun j _ => hF.flow_nonneg w hw r c j) (Finset.mem_univ j)
  rw [hF.outflow w hw r c, hp] at hs
  exact le_antisymm hs hn

theorem row_nonneg (w : List R) (r : R) (c : C) (j : J) :
    0 ≤ row F fallback H w r c j := by
  unfold row
  split_ifs with hh hzero
  · exact div_nonneg (hF.flow_nonneg w hh.1 r c j) (hF.mass_nonneg w hh.1.le c)
  all_goals norm_num

theorem row_support (hfallback : ∀ c r, allowed c r (fallback c r))
    (w : List R) (r : R) (c : C) (j : J) (hj : ¬allowed c r j) :
    row F fallback H w r c j = 0 := by
  have hne : j ≠ fallback c r := by intro he; subst j; exact hj (hfallback c r)
  unfold row
  split_ifs with hh
  · rw [hF.support w hh.1 r c j hj, zero_div]
  all_goals simp_all

omit [DecidableEq J] in
theorem inflow_average (w : List R) (hw : w.length < H) (r : R) (v : C → ℚ) :
    (∑ c, ∑ j, F.flow w r c j*v (T c r j)) = ∑ c', F.mass (w++[r]) c'*v c' := by
  simp_rw [← hF.inflow w hw r]
  symm
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [ite_mul]

end UniformKServer.FiniteFlow


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteTable
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.FiniteTable
open EffectiveLP

/-- The source's least allowed serving label, including zero marginal rows. -/
def fallback {n k : ℕ} [NeZero k] (c : Config n k) (r : Fin n) : Fin k :=
  if h : (labels c r).Nonempty then (labels c r).min' h else 0

def next {n k : ℕ} (c : Config n k) (r : Fin n) (j : Fin k) : Config n k :=
  if h : j ∈ labels c r then step c r ⟨j,h⟩ else c

def globalFlow {n k H : ℕ} (F : BoundedFlow n k H ℚ) :
    FiniteFlow.Data (Fin n) (Config n k) (Fin k) where
  mass w c := if h : w.length ≤ H then F.mass ⟨w,(mem_words w).mpr h⟩ c else 0
  flow w r c j := if h : w.length < H then
    if hj : j ∈ labels c r then
      F.flow ⟨⟨w,(mem_words w).mpr h.le⟩,h⟩ r c ⟨j,hj⟩ else 0 else 0

def charge {n k : ℕ} (d : RationalMetric n) (c : Config n k) (r : Fin n) (j : Fin k) : ℚ :=
  d.distance (c.val j) r

def row {n k H : ℕ} [NeZero k] (F : BoundedFlow n k H ℚ) :
    List (Fin n) → Fin n → Config n k → Fin k → ℚ :=
  FiniteFlow.row (globalFlow F) fallback H

theorem labels_nonempty {n k : ℕ} [NeZero k] (c : Config n k) (r : Fin n) :
    (labels c r).Nonempty := by
  unfold labels
  split_ifs with h
  · obtain ⟨j,hj⟩ := h
    exact ⟨j, by simp [hj]⟩
  · exact Finset.univ_nonempty

theorem sum_labels {n k : ℕ} {K : Type*} [AddCommMonoid K]
    (c : Config n k) (r : Fin n) (f : Label c r → K) :
    (∑ j, if hj : j ∈ labels c r then f ⟨j,hj⟩ else 0) = ∑ j, f j := by
  exact (Finset.sum_attach_eq_sum_dite (labels c r) f).symm

theorem flowCost_prefix {R C J : Type*} [Fintype C] [Fintype J]
    (F : FiniteFlow.Data R C J) (d : C → R → J → ℚ) (pre w : List R) :
    FiniteFlow.flowCost F d pre w =
      ∑ i : Fin w.length, ∑ c, ∑ j, F.flow (pre++w.take i) w[i] c j * d c w[i] j := by
  induction w generalizing pre with
  | nil => simp [FiniteFlow.flowCost]
  | cons r w ih =>
    simp only [FiniteFlow.flowCost, List.length_cons]
    rw [Fin.sum_univ_succ, ih]
    simp [Fin.getElem_fin, List.append_assoc]

end UniformKServer.FiniteTable



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ComputedInstance
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace UniformKServer.ComputedInstance
open EffectiveLP EpochShadow EpochPartition

variable {n k : ℕ}

def allDistances (d : RationalMetric n) : Finset ℚ :=
  Finset.univ.image (fun p : Fin n × Fin n => d.distance p.1 p.2)

def positiveDistances (d : RationalMetric n) : Finset ℚ :=
  (allDistances d).filter (0 < ·)

theorem allDistances_nonempty (hn : 2 ≤ n) (d : RationalMetric n) :
    (allDistances d).Nonempty := by
  exact ⟨d.distance ⟨0,by omega⟩ ⟨1,by omega⟩,
    Finset.mem_image.mpr ⟨(⟨0,by omega⟩,⟨1,by omega⟩), Finset.mem_univ _, rfl⟩⟩

theorem positiveDistances_nonempty (hn : 2 ≤ n) (d : RationalMetric n) :
    (positiveDistances d).Nonempty := by
  let x : Fin n := ⟨0,by omega⟩
  let y : Fin n := ⟨1,by omega⟩
  have hxy : x ≠ y := by intro h; have := congrArg Fin.val h; simp [x,y] at this
  have hp : 0 < d.distance x y := lt_of_le_of_ne (d.nonneg x y)
    (Ne.symm (fun h => hxy ((d.eq_zero x y).mp h)))
  exact ⟨d.distance x y, Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨(x,y), Finset.mem_univ _, rfl⟩, hp⟩⟩

def diameter (hn : 2 ≤ n) (d : RationalMetric n) : ℚ :=
  (allDistances d).max' (allDistances_nonempty hn d)

def separation (hn : 2 ≤ n) (d : RationalMetric n) : ℚ :=
  (positiveDistances d).min' (positiveDistances_nonempty hn d)

def restart (hn : 2 ≤ n) (d : RationalMetric n) (k : ℕ) : ℕ :=
  ⌈(k:ℚ)*diameter hn d / separation hn d⌉₊

def cap (hn : 2 ≤ n) (d : RationalMetric n) (k : ℕ) : ℕ :=
  ⌈(restart hn d k : ℚ)*(k+1)*diameter hn d / separation hn d⌉₊

/-- Exact instance parameters and canonical start in the manuscript. -/
theorem parameters (hn : 2 ≤ n) (hk : 0 < k) (d : RationalMetric n) :
    0 ≤ (diameter hn d : ℝ) ∧ 0 < (separation hn d : ℝ) ∧
    (∀ x y, (d.distance x y : ℝ) ≤ diameter hn d) ∧
    (∀ x y, x ≠ y → (separation hn d : ℝ) ≤ d.distance x y) ∧
    0 < restart hn d k ∧
    (k:ℝ)*diameter hn d ≤ (restart hn d k : ℝ)*separation hn d ∧
    (restart hn d k : ℝ)*(k+1)*diameter hn d ≤
      ((cap hn d k : ℝ)+1)*separation hn d := by
  have hsQ : 0 < separation hn d :=
    (Finset.mem_filter.mp (Finset.min'_mem _ (positiveDistances_nonempty hn d))).2
  have hdiamQ : ∀ x y, d.distance x y ≤ diameter hn d := by
    intro x y
    exact Finset.le_max' (allDistances d) (d.distance x y)
      (Finset.mem_image.mpr ⟨(x,y),Finset.mem_univ _,rfl⟩)
  have hsepQ : ∀ x y, x ≠ y → separation hn d ≤ d.distance x y := by
    intro x y hxy
    apply Finset.min'_le
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(x,y),Finset.mem_univ _,rfl⟩, ?_⟩
    exact lt_of_le_of_ne (d.nonneg x y)
      (Ne.symm (fun h => hxy ((d.eq_zero x y).mp h)))
  have hsd : separation hn d ≤ diameter hn d := by
    obtain ⟨p,hp⟩ := positiveDistances_nonempty hn d
    have hm := Finset.min'_le _ p hp
    have hx : p ≤ diameter hn d :=
      Finset.le_max' _ _ (Finset.mem_filter.mp hp).1
    exact hm.trans hx
  have hdQ : 0 < diameter hn d := hsQ.trans_le hsd
  have hR : 0 < restart hn d k := by
    apply Nat.ceil_pos.mpr
    exact div_pos (mul_pos (by exact_mod_cast hk) hdQ) hsQ
  have hRDQ : (k:ℚ)*diameter hn d ≤ (restart hn d k : ℚ)*separation hn d := by
    apply (div_le_iff₀ hsQ).mp
    exact Nat.le_ceil _
  have hMQ : (restart hn d k : ℚ)*(k+1)*diameter hn d ≤
      (cap hn d k : ℚ)*separation hn d := by
    apply (div_le_iff₀ hsQ).mp
    exact Nat.le_ceil _
  have hcapQ : (restart hn d k : ℚ)*(k+1)*diameter hn d ≤
      ((cap hn d k : ℚ)+1)*separation hn d := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, hR, ?_, ?_⟩
  · exact_mod_cast hdQ.le
  · exact_mod_cast hsQ
  · intro x y; exact_mod_cast hdiamQ x y
  · intro x y hxy; exact_mod_cast hsepQ x y hxy
  · exact_mod_cast hRDQ
  · exact_mod_cast hcapQ

/-- Prefix requests before deterministic activation use source label 1
(zero in Fin k); the raw suffix then uses the computed exact-bit epochs. -/
def prefixTrace [NeZero k] (w : List (Fin n)) : History n k :=
  w.map (fun r => (r,⟨0,NeZero.pos k⟩))

end UniformKServer.ComputedInstance

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawAccepted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.RawAccepted
open RawArithmetic RawTable RawCertificate

structure Numbers (k : ℕ) (v : Certificate) : Prop where
  ell_eq : ell v=Nat.clog 2 (k+1)
  restart_pos : 0 < restart v
  sep_pos : 0<value (sep v)
  restart_bound : (k:ℚ)*value (diam v)≤(restart v:ℚ)*value (sep v)
  cap_bound : (restart v:ℚ)*(k+1)*value (diam v)≤(cap v+1:ℚ)*value (sep v)

theorem numbers_spec {k : ℕ} {v : Certificate} (h : numbersOK k v=true) : Numbers k v := by
  simp only [numbersOK,Bool.and_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨h0,hlo⟩,hhi⟩,hr⟩,hδ⟩,hc⟩,hm⟩:=h
  have h0:=of_decide_eq_true h0
  have hlo:=of_decide_eq_true hlo
  have hhi:=of_decide_eq_true hhi
  have hl := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mpr hlo
  have hu := (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr hhi
  refine ⟨by omega,of_decide_eq_true hr,?_,?_,?_⟩
  · unfold value
    have hp : 0<(sep v).1 := of_decide_eq_true hδ
    positivity
  · have hh:=(le_iff _ _).mp (of_decide_eq_true hc)
    simpa only [value_mul,value_natural] using hh
  · have hh:=(le_iff _ _).mp (of_decide_eq_true hm)
    simpa only [value_mul,value_natural,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_assoc] using hh

theorem bounds_spec {n : ℕ} (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    {D δ : Q} (h : boundsOK n draw D δ=true) :
    (∀x y,d.distance x y≤value D) ∧ (∀x y,x≠y→value δ≤d.distance x y) := by
  have hxy : ∀x y : Fin n,le (dist n draw x.val y.val) D ∧
      (x.val=y.val ∨ le δ (dist n draw x.val y.val)) := by
    intro x y
    have hh:=List.all_eq_true.mp (List.all_eq_true.mp h x.val (List.mem_range.mpr x.isLt)) y.val (List.mem_range.mpr y.isLt)
    have ha:=Bool.and_eq_true_iff.mp hh
    refine ⟨of_decide_eq_true ha.1,?_⟩
    rcases Bool.or_eq_true_iff.mp ha.2 with he|he
    · exact Or.inl (of_decide_eq_true he)
    · exact Or.inr (of_decide_eq_true he)
  constructor
  · intro x y;rw [←hd];exact (le_iff _ _).mp (hxy x y).1
  · intro x y hxy'
    have hn : x.val≠y.val := fun h=>hxy' (Fin.ext h)
    rw [←hd]
    exact (le_iff _ _).mp ((hxy x y).2.resolve_left hn)

structure Params {n k : ℕ} (mult : ℕ) (d : RationalMetric n) (draw : List Q)
    (v : Certificate) : Prop where
  numbers : Numbers k v
  diam_bound : ∀x y,d.distance x y≤value (diam v)
  sep_bound : ∀x y,x≠y→value (sep v)≤d.distance x y
  rows : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true
  budget : tableOK n k (UniformKServer.horizon k (cap v)) (bits v) (mult*(ell v)^2)
    (restart v) draw (diam v) (sep v) (table v)=true

theorem spec {n k mult : ℕ} (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    {v : Certificate} (h : verify mult (n,k,draw) v=true) : Params (k:=k) mult d draw v := by
  simp only [verify,Bool.and_eq_true_iff,RawMetric.horizon_eq] at h
  obtain ⟨⟨⟨hn,hb⟩,hr⟩,ht⟩:=h
  exact ⟨numbers_spec hn,(bounds_spec d draw hd hb).1,(bounds_spec d draw hd hb).2,hr,ht⟩

end UniformKServer.RawAccepted

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RealFlowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                     
section

namespace UniformKServer.RealFlow
open Finset
variable {R C J : Type*} [Fintype C] [Fintype J] [DecidableEq C]
  {F : Data R C J} {T : C→R→J→C} {allowed : C→R→J→Prop} {s : C} {H : ℕ}

theorem mass_le_one (hF : Valid F T allowed s H) (w : List R) (hw : w.length≤H) (c : C) :
    F.mass w c≤1 := by
  have h := single_le_sum (fun c _=>hF.mass_nonneg w hw c) (mem_univ c)
  rw [hF.mass_total w hw] at h
  exact h

theorem flow_le_one (hF : Valid F T allowed s H) (w : List R) (hw : w.length<H) (r : R) (c : C) (j : J) :
    F.flow w r c j≤1 := by
  have h := single_le_sum (fun j _=>hF.flow_nonneg w hw r c j) (mem_univ j)
  rw [hF.outflow w hw r c] at h
  exact h.trans (mass_le_one hF w hw.le c)

theorem flowCost_nonneg (hF : Valid F T allowed s H) (d : C→R→J→ℝ)
    (hd : ∀c r j,0≤d c r j) (w u : List R) (hu : w.length+u.length≤H) :
    0≤flowCost F d w u := by
  induction u generalizing w with
  | nil => exact le_rfl
  | cons r u ih =>
    apply add_nonneg
    · exact sum_nonneg fun c _=>sum_nonneg fun j _=>
        mul_nonneg (hF.flow_nonneg w (by simp only [List.length_cons] at hu; omega) r c j) (hd c r j)
    · exact ih _ (by simp only [List.length_append,List.length_cons,List.length_nil] at *; omega)

theorem flowCost_prefix (hF : Valid F T allowed s H) (d : C→R→J→ℝ)
    (hd : ∀c r j,0≤d c r j) (u v : List R) (hv : v.length≤H) (hu : u.IsPrefix v) :
    flowCost F d [] u≤flowCost F d [] v := by
  obtain ⟨a,rfl⟩ := hu
  rw [flowCost_append]
  apply le_add_of_nonneg_right
  apply flowCost_nonneg hF d hd
  simpa only [List.length_append,List.nil_append] using hv

end UniformKServer.RealFlow

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RealFlowConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Convexity is at the actual causal flow level, not at the nonlinear row
normalization level. -/
namespace UniformKServer.RealFlow
open Finset
open scoped Classical
variable {R C J : Type*} [Fintype C] [Fintype J]

def combine (a b : ℝ) (F G : Data R C J) : Data R C J where
  mass w c := a*F.mass w c+b*G.mass w c
  flow w r c j := a*F.flow w r c j+b*G.flow w r c j

theorem combine_valid (F G : Data R C J) (T : C→R→J→C)
    (allowed : C→R→J→Prop) (s : C) (H : ℕ)
    (hF : Valid F T allowed s H) (hG : Valid G T allowed s H)
    (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    Valid (combine a b F G) T allowed s H := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro w hw c
    exact add_nonneg (mul_nonneg ha (hF.mass_nonneg w hw c)) (mul_nonneg hb (hG.mass_nonneg w hw c))
  · intro w hw
    simp only [combine,sum_add_distrib,←mul_sum,hF.mass_total w hw,hG.mass_total w hw,mul_one,hab]
  · intro c
    simp only [combine,hF.initial,hG.initial]
    split_ifs <;> simp only [mul_one,hab,mul_zero,add_zero]
  · intro w hw r c j
    exact add_nonneg (mul_nonneg ha (hF.flow_nonneg w hw r c j)) (mul_nonneg hb (hG.flow_nonneg w hw r c j))
  · intro w hw r c j hj
    simp only [combine,hF.support w hw r c j hj,hG.support w hw r c j hj,mul_zero,add_zero]
  · intro w hw r c
    simp only [combine,sum_add_distrib,←mul_sum,hF.outflow w hw,hG.outflow w hw]
  · intro w hw r c'
    have he (c : C) (j : J) : (if T c r j=c' then (combine a b F G).flow w r c j else 0)=
        a*(if T c r j=c' then F.flow w r c j else 0)+
        b*(if T c r j=c' then G.flow w r c j else 0) := by
      split_ifs <;> simp only [combine,mul_zero,add_zero]
    simp_rw [he]
    simp only [sum_add_distrib,←mul_sum,hF.inflow w hw,hG.inflow w hw,combine]

theorem combine_cost (F G : Data R C J) (a b : ℝ) (d : C→R→J→ℝ) (w u : List R) :
    flowCost (combine a b F G) d w u=a*flowCost F d w u+b*flowCost G d w u := by
  induction u generalizing w with
  | nil => simp only [flowCost,mul_zero,add_zero]
  | cons r u ih =>
    rw [flowCost,ih,flowCost,flowCost]
    simp only [combine,add_mul,mul_assoc,sum_add_distrib,←mul_sum]
    ring

end UniformKServer.RealFlow

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteFlowSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A literal finite coordinate model of all horizon-H causal flows. Compactness
comes from their probability bounds, not from assuming a minimax input. -/
namespace UniformKServer.FiniteFlowSpace
open Finset RealFlow
open scoped Classical
variable {R C J : Type} {H : ℕ}

abbrev Word (R : Type) (H : ℕ) := (m : Fin (H+1)) × (Fin m.val→R)
def letters (w : Word R H) : List R := List.ofFn w.2
def code (w : List R) (hw : w.length≤H) : Word R H := ⟨⟨w.length,by omega⟩,fun i=>w[i]⟩

theorem letters_code (w : List R) (hw : w.length≤H) : letters (code w hw)=w := by
  change List.ofFn w.get = w
  exact List.ofFn_get w

theorem letters_length (w : Word R H) : (letters w).length=w.1.val := List.length_ofFn

theorem letters_bound (w : Word R H) : (letters w).length≤H := by
  rw [letters_length]
  have := w.1.isLt
  omega

abbrev Index (R C J : Type) (H : ℕ) := (Word R H×C) ⊕ (Word R H×R×C×J)
abbrev Space (R C J : Type) (H : ℕ) := Index R C J H→ℝ

def decode (x : Space R C J H) : Data R C J where
  mass w c := if hw : w.length≤H then x (.inl (code w hw,c)) else 0
  flow w r c j := if hw : w.length<H then x (.inr (code w hw.le,r,c,j)) else 0

def encode (F : Data R C J) : Space R C J H
  | .inl (w,c) => F.mass (letters w) c
  | .inr (w,r,c,j) => if (letters w).length<H then F.flow (letters w) r c j else 0

section
variable [Fintype C] [Fintype J]

theorem encode_bounds (F : Data R C J) (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C)
    (hF : Valid F T allowed s H) : encode (H:=H) F∈Set.Icc (0:Space R C J H) 1 := by
  constructor
  · intro i
    rcases i with ⟨w,c⟩|⟨w,r,c,j⟩
    · exact hF.mass_nonneg _ (letters_bound w) c
    · change 0≤(if (letters w).length<H then F.flow (letters w) r c j else 0)
      split_ifs with hw
      · exact hF.flow_nonneg _ hw r c j
      · exact le_rfl
  · intro i
    rcases i with ⟨w,c⟩|⟨w,r,c,j⟩
    · exact mass_le_one hF _ (letters_bound w) c
    · change (if (letters w).length<H then F.flow (letters w) r c j else 0)≤1
      split_ifs with hw
      · exact flow_le_one hF _ hw r c j
      · norm_num

end

theorem decode_combine (a b : ℝ) (x y : Space R C J H) :
    decode (a • x+b • y)=combine a b (decode x) (decode y) := by
  unfold decode combine
  congr 1
  · funext w c
    by_cases hw : w.length≤H <;> simp [hw]
  · funext w r c j
    by_cases hw : w.length<H <;> simp [hw]

end UniformKServer.FiniteFlowSpace

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteFlowCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.FiniteFlowSpace
open Finset RealFlow
open scoped Classical
variable {R C J : Type} [Fintype C] [Fintype J] {H : ℕ}

theorem closed_forall {A : Type*} {I : Sort*} [TopologicalSpace A] (p : I→A→Prop)
    (h : ∀i,IsClosed {x|p i x}) : IsClosed {x|∀i,p i x} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter h

def feasible (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C) : Set (Space R C J H) :=
  Set.Icc 0 1 ∩ {x | Valid (decode x) T allowed s H}

theorem feasible_convex (T : C→R→J→C) (allowed : C→R→J→Prop) (s : C) :
    Convex ℝ (feasible (H:=H) T allowed s) := by
  apply (convex_Icc _ _).inter
  intro x hx y hy a b ha hb hab
  change Valid (decode (a • x+b • y)) T allowed s H
  rw [decode_combine]
  exact combine_valid _ _ T allowed s H hx hy a b ha hb hab

end UniformKServer.FiniteFlowSpace

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The exact finite separation step, with normalization and the empty-index
case handled from the stated hypotheses. No minimax theorem is assumed. -/
namespace UniformKServer.FiniteSeparation
open Finset
open scoped Classical
variable {I : Type} [Fintype I]

theorem dual_sum (f : StrongDual ℝ (I→ℝ)) (x : I→ℝ) :
    f x=∑i,f (Pi.single i 1)*x i := by
  have hx : x=∑i,x i • (Pi.single i (1:ℝ)) := by
    ext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  calc
    f x=f (∑i,x i • (Pi.single i (1:ℝ))) := congrArg f hx
    _=∑i,f (Pi.single i 1)*x i := by
      simp only [map_sum,map_smul,smul_eq_mul,mul_comm]

end UniformKServer.FiniteSeparation

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteFlowMinimax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite-law removal on the literal compact causal-flow polytope. -/
namespace UniformKServer.FiniteFlowSpace
open Finset RealFlow
open scoped Classical
variable {R C J : Type} [Fintype R] [Fintype C] [Fintype J] {H : ℕ}

def costVector (d : C→R→J→ℝ) (q : Word R H→ℝ) (x : Space R C J H) : Word R H→ℝ :=
  fun v=>flowCost (decode x) d [] (letters v)-q v

omit [Fintype R] in
theorem costVector_combo (d : C→R→J→ℝ) (q : Word R H→ℝ)
    (a b : ℝ) (hab : a+b=1) (x y : Space R C J H) :
    costVector d q (a • x+b • y)=a • costVector d q x+b • costVector d q y := by
  funext v
  simp only [costVector,decode_combine,combine_cost,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  linear_combination (q v)*hab

end UniformKServer.FiniteFlowSpace

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_UniformParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The source's freely chosen small constants are fixed once and for all.
The parent construction has one absolute squared-log coefficient. -/
namespace UniformKServer.PartitionTree
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X]

def fixedShift : ℝ := 1/(10:ℝ)^20

def metricRadius : ℝ := 1+∑ x : X,∑ y : X,dist x y

theorem metricRadius_pos : 0 < metricRadius (X:=X) := by
  have hh : 0≤∑ x : X,∑ y : X,dist x y := sum_nonneg fun x _=>sum_nonneg fun y _=>dist_nonneg
  unfold metricRadius
  linarith

theorem metricRadius_bounds (x y : X) : dist x y≤40*metricRadius (X:=X) := by
  have h₁ := single_le_sum (fun y _=>show 0≤dist x y from dist_nonneg) (mem_univ y)
  have h₂ : (∑ y : X,dist x y)≤∑ x : X,∑ y : X,dist x y := single_le_sum (fun x _=>sum_nonneg (fun y _=>show 0≤dist x y from dist_nonneg)) (mem_univ x)
  have hn : 0≤∑ x : X,∑ y : X,dist x y := sum_nonneg fun x _=>sum_nonneg fun y _=>dist_nonneg
  unfold metricRadius
  linarith

omit [Fintype X] [MetricSpace X]

def driftScalar : ℝ := (6/5)*132*(2+7/Real.log 2)

theorem driftScalar_pos : 0<driftScalar := by
  have hh : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold driftScalar
  positivity

def logFactor : ℝ := 1+1/Real.log 2

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteLawFinance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The assembled finite-law bound: the policy is a legal causal flow, the
coefficient is absolute squared-logarithmic, and the additive quantity knows
neither the horizon nor the request law. -/
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
def flowServe (c : Fin k→X) (r : X) (j : Fin k) : Fin k→X := Function.update c j r
local instance ixFF (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairFF_reed5be_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
local instance configEqFF : DecidableEq (Fin k→X) := fun a b=>Classical.propDecidable (a=b)

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_MetricRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! The exact rational input metric realized as Mathlib's metric; no geometry
assumptions are added at the interface. -/
namespace UniformKServer.RationalMetric
variable {n : ℕ}

@[instance_reducible] def metric (d : RationalMetric n) : MetricSpace (Fin n) where
  dist x y := (d.distance x y : ℝ)
  dist_self x := by exact_mod_cast (d.eq_zero x x).mpr rfl
  dist_comm x y := by exact_mod_cast d.symm x y
  dist_triangle x y z := by exact_mod_cast d.triangle x y z
  eq_of_dist_eq_zero := by
    intro x y h
    exact (d.eq_zero x y).mp (by exact_mod_cast h)

end UniformKServer.RationalMetric

end


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OfflineLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! No hidden-trajectory hypothesis is added: an optimal finite serving history
is selected for each atom of an arbitrary finite request law. -/

namespace UniformKServer.PartitionTree
open Finset TreeRounding
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance configEqOL : DecidableEq (Fin k→X) := fun a b=>Classical.propDecidable (a=b)

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetLP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

/-! A finite additive-offset variant of the same exact rational flow system.
The source permits an arbitrarily large instance-dependent initialization delay.
This auxiliary system allows its horizon-independent finite-law endpoint to be
absorbed in a sufficiently long restart epoch; no main conclusion is assumed.
All original source definitions and their coefficient optimizer are unchanged. -/
namespace UniformKServer.OffsetLP
open EffectiveLP FourierMotzkin
def constraints {n k H : ℕ} [NeZero k] (d : RationalMetric n)
    (u : Config n k) (A : ℚ) : List (EffectiveLP.Row n k H) :=
  [Form.objective.scale (-1)] ++
  (enumerate.flatMap fun wc : Word n H × Config n k => [(massRow wc.1 wc.2).scale (-1)]) ++
  (enumerate.flatMap fun w : Word n H =>
    Form.eqRows ((Form.sum Finset.univ (massRow w)).sub (Form.constant 1))) ++
  (enumerate.flatMap fun c : Config n k =>
    Form.eqRows ((massRow (rootWord n H) c).sub (Form.constant (if c = u then 1 else 0)))) ++
  (enumerate.flatMap fun e : Edge n k H => [(flowRow e.1 e.2.1 e.2.2.1 e.2.2.2).scale (-1)]) ++
  (enumerate.flatMap fun w : Short n H =>
    enumerate.flatMap fun r : Fin n =>
      enumerate.flatMap fun c : Config n k =>
        Form.eqRows ((Form.sum Finset.univ (flowRow w r c)).sub (massRow w.val c))) ++
  (enumerate.flatMap fun w : Short n H =>
    enumerate.flatMap fun r : Fin n =>
      enumerate.flatMap fun c' : Config n k =>
        Form.eqRows ((Form.sum Finset.univ fun c : Config n k =>
          Form.sum Finset.univ fun j : Label c r =>
            if EffectiveLP.step c r j = c' then flowRow w r c j else Form.constant 0).sub (massRow (extend w r) c')) ) ++
  (enumerate.flatMap fun w : Word n H =>
    [((costRow d w).sub (Form.constant (A * OfflineDynamic.optRat d u.val w.val))).sub Form.objective])

-- Exact interpretation of the source constraints, over either rationals or reals.
def Valid {n k H : ℕ} {K : Type*} [Field K] [LinearOrder K]
    (d : RationalMetric n) (u : Config n k) (A : ℚ) (F : BoundedFlow n k H K) (a : K)
    [NeZero k] : Prop :=
  0 ≤ a ∧
  (∀ w c, 0 ≤ F.mass w c) ∧
  (∀ w, ∑ c, F.mass w c = 1) ∧
  (∀ c, F.mass (rootWord n H) c = if c = u then 1 else 0) ∧
  (∀ w r c j, 0 ≤ F.flow w r c j) ∧
  (∀ w r c, ∑ j, F.flow w r c j = F.mass w.val c) ∧
  (∀ w r c', (∑ c, ∑ j, if EffectiveLP.step c r j = c' then F.flow w r c j else 0) = F.mass (extend w r) c') ∧
  (∀ w, (∑ i : Fin w.val.length, ∑ c, ∑ j : Label c w.val[i],
     F.flow (prefixNode w i) w.val[i] c j * (d.distance (c.val j.val) w.val[i] : K)) ≤
       (A : K) * (OfflineDynamic.optRat d u.val w.val : K) + a)

theorem constraints_iff {n k H : ℕ} [NeZero k] {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (d : RationalMetric n) (u : Config n k) (A : ℚ)
    (x : Fin (Fintype.card (Variable n k H)+1) → K) :
    Satisfies (constraints d u A) x ↔
      Valid d u A (ofAssignment (Form.recover x)) (FourierMotzkin.objective x) := by
  classical
  unfold constraints
  simp only [satisfies_append, satisfies_flatMap, satisfies_singleton, Form.eqRows_iff]
  simp only [and_assoc]
  change _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  apply and_congr
  · simp only [FourierMotzkin.Row.eval_scale, Form.eval_objective,
      Rat.cast_neg, Rat.cast_one, neg_one_mul, neg_nonpos]
  apply and_congr
  · simp only [Prod.forall, FourierMotzkin.Row.eval_scale, Rat.cast_neg,
      Rat.cast_one, neg_one_mul, neg_nonpos, massRow, Form.eval_var, ofAssignment]
  apply and_congr
  · simp only [FourierMotzkin.Row.eval_sub, Form.eval_sum, Form.eval_constant,
      Rat.cast_one, sub_eq_zero, massRow, Form.eval_var, ofAssignment]
  apply and_congr
  · apply forall_congr'
    intro c
    by_cases hc : c = u <;>
      simp only [hc, ite_true, if_true, ite_false, if_false, FourierMotzkin.Row.eval_sub,
        Form.eval_constant, sub_eq_zero, massRow, Form.eval_var, ofAssignment,
        Rat.cast_one, Rat.cast_zero]
  apply and_congr
  · simp only [Sigma.forall, FourierMotzkin.Row.eval_scale, Rat.cast_neg,
      Rat.cast_one, neg_one_mul, neg_nonpos, flowRow, Form.eval_var, ofAssignment]
  apply and_congr
  · simp only [FourierMotzkin.Row.eval_sub, Form.eval_sum, sub_eq_zero,
      massRow, flowRow, Form.eval_var, ofAssignment]
  apply and_congr
  · simp only [FourierMotzkin.Row.eval_sub, Form.eval_sum, sub_eq_zero,
      massRow, flowRow, Form.eval_var, ofAssignment, eval_if, Form.eval_constant,
      Rat.cast_zero]
  · simp only [FourierMotzkin.Row.eval_sub, eval_costRow, sub_nonpos,
      Form.eval_constant, Rat.cast_mul, Form.eval_objective]
    constructor <;> intro h w <;> have := h w <;> linarith

theorem rational_attainment {n k H : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ)
    (h : ∃ (F : BoundedFlow n k H ℝ) (a : ℝ), Valid d u A F a) :
    ∃ x : Fin (Fintype.card (Variable n k H)+1) → ℚ,
      optimize (Fintype.card (Variable n k H)) (constraints d u A) = some x ∧
      Valid d u A (ofAssignment (Form.recover x)) (FourierMotzkin.objective x) ∧
      ∀ (F : BoundedFlow n k H ℝ) (a : ℝ), Valid d u A F a →
        ((FourierMotzkin.objective x : ℚ) : ℝ) ≤ a := by
  have build (F : BoundedFlow n k H ℝ) (a : ℝ) (hF : Valid d u A F a) :
      Satisfies (constraints d u A) (Form.vector (toAssignment F) a) := by
    apply (constraints_iff d u A _).mpr
    simpa only [Form.recover_vector, Form.objective_vector, toAssignment, ofAssignment] using hF
  obtain ⟨F,a,ha⟩ := h
  have hex : ∃ y : Fin (Fintype.card (Variable n k H)+1) → ℝ,
      0 ≤ FourierMotzkin.objective y ∧ Satisfies (constraints d u A) y :=
    ⟨Form.vector (toAssignment F) a, by simpa only [Form.objective_vector] using ha.1, build F a ha⟩
  obtain ⟨x,hx,hn,hs,hm⟩ := optimize_rational_attainment _ (constraints d u A) hex
  refine ⟨x,hx,(constraints_iff d u A x).mp hs, ?_⟩
  intro F a ha
  simpa only [Form.objective_vector] using hm (Form.vector (toAssignment F) a)
    (by simpa only [Form.objective_vector] using ha.1) (build F a ha)


end UniformKServer.OffsetLP

end


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Restrict the law-independent strongly-lazy real flow to exactly the source
injective configuration and admissible-label LP, with no support assumption. -/
namespace UniformKServer.OffsetLP
open Finset EffectiveLP TreeRounding RealFlow
open scoped Classical
variable {n k H : ℕ} [NeZero k]

 local instance configEqOB_reed5be_1 : DecidableEq (Configuration n k) :=
  fun first second => Classical.propDecidable (first = second)
theorem sum_restrict {A : Type*} [Fintype A] (P : A→Prop)
    [Fintype {a//P a}] (f : A→ℝ)
    (hz : ∀a,¬P a→f a=0) : (∑a,f a)=∑a : {a//P a},f a.val := by
  classical
  calc
    _ = ∑a ∈ univ.filter P,f a := by
      symm
      apply sum_subset (filter_subset _ _)
      intro a ha hp
      exact hz a (by simpa using hp)
    _ = _ := Finset.sum_subtype _ (by simp) _

 theorem flowCost_prefix {R C J : Type*} [Fintype C] [Fintype J]
    (F : Data R C J) (d : C→R→J→ℝ) (pre w : List R) :
    flowCost F d pre w =
      ∑i : Fin w.length,∑c,∑j,F.flow (pre++w.take i) w[i] c j*d c w[i] j := by
  induction w generalizing pre with
  | nil => simp [flowCost]
  | cons r w ih =>
    simp only [flowCost,List.length_cons]
    rw [Fin.sum_univ_succ,ih]
    simp [Fin.getElem_fin,List.append_assoc]

end UniformKServer.OffsetLP

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.OffsetTable
open EffectiveLP
open OffsetLP

def assignment {n k H : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ) :
    Fin (Fintype.card (Variable n k H)+1) → ℚ :=
  (FourierMotzkin.optimize (Fintype.card (Variable n k H)) (OffsetLP.constraints d u A)).getD (fun _ => 0)

def flow {n k H : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ) :
    BoundedFlow n k H ℚ := ofAssignment (Form.recover (assignment d u A))

def offset {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ) (H : ℕ) : ℚ :=
  FourierMotzkin.objective (assignment (H:=H) d u A)

abbrev State (n k : ℕ) := List (Fin n) × Config n k

def qrow {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ) (H : ℕ)
    (s : State n k) (r : Fin n) (j : Fin k) : ℚ :=
  FiniteTable.row (flow (H:=H) d u A) s.1 r s.2 j

def next {n k : ℕ} (s : State n k) (r : Fin n) (j : Fin k) : State n k :=
  (s.1 ++ [r], FiniteTable.next s.2 r j)

def bitWidth (k H : ℕ) : ℕ := Nat.clog 2 (k * H^2)

def counts {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ) (H : ℕ)
    (s : State n k) (r : Fin n) (j : Fin k) : ℕ :=
  ExecutableDyadic.numerators (qrow d u A H s r) (FiniteTable.fallback s.2 r) (2^(bitWidth k H)) j

end UniformKServer.OffsetTable

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                       
section

/-! Terminating rational search for the restart length. The uniform finite-law
endpoint is used only to prove termination, never supplied to the constructor. -/
namespace UniformKServer.OffsetParameters
open EffectiveLP ComputedInstance
variable {n k : ℕ} [NeZero k]

def cap (hn : 2 ≤ n) (d : RationalMetric n) (R : ℕ) : ℕ :=
  ⌈(R:ℚ)*(k+1)*diameter hn d / separation hn d⌉₊

def acceptable (hn : 2 ≤ n) (d : RationalMetric n) (u : Config n k) (A : ℚ) (R : ℕ) : Prop :=
  0 < R ∧ (k:ℚ)*diameter hn d ≤ (R:ℚ)*separation hn d ∧
    OffsetTable.offset d u A (horizon k (cap (k:=k) hn d R)) ≤ (R:ℚ)*separation hn d

instance acceptableDecidable (hn : 2 ≤ n) (d : RationalMetric n) (u : Config n k)
    (A : ℚ) (R : ℕ) : Decidable (acceptable hn d u A R) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end UniformKServer.OffsetParameters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_UniformSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                   
section

/-! An executable rational squared-binary-log slope with an absolute real
comparison coefficient. Its fixed integer multiplier is chosen once globally. -/
namespace UniformKServer.OffsetLP
open PartitionTree

def slope (mult k : ℕ) : ℚ := mult*(Nat.clog 2 (k+1))^2

end UniformKServer.OffsetLP

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetInstance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                     
section

/-! Uniform absolute squared-log cost for the exact rational-search/dyadic
suffix, with arbitrary repeated starts and arbitrary finite activation delay.
The literal bit-machine implementation is deliberately not asserted here. -/
namespace UniformKServer.OffsetInstance

open EffectiveLP ComputedInstance
variable (mult : ℕ)
variable {n k : ℕ} [NeZero k]

def slope (k : ℕ) : ℚ := OffsetLP.slope mult k

noncomputable def coefficient : ℝ := 4*(mult : ℝ)*(2/Real.log 2)^2+4/(Real.log 2)^2

end UniformKServer.OffsetInstance

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                        
section

namespace UniformKServer.RawRepresentation
open RawArithmetic RawWords RawTable RawTyped

abbrev Index (n k H : ℕ) := EffectiveLP.Word n H × Configuration n k × Fin n × Fin k

def indexKey {n k H : ℕ} (i : Index n k H) :=
  key (requests i.1.val) (config i.2.1) i.2.2.1.val i.2.2.2.val

end UniformKServer.RawRepresentation

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

/-! A stack is physically stored at a tape head. Padding is literal blank
cells, not a unit-cost unbounded register. Each push/pop uses at most two
transitions. -/
namespace UniformKServer.StackTape

def encode (s : List Bool) (l r : ℕ) : BitTape :=
  match s with
  | [] => ⟨List.replicate l none,none,List.replicate r none⟩
  | b::bs => ⟨List.replicate l none,some b,bs.map some ++ List.replicate r none⟩

def Rep (s : List Bool) (t : BitTape) : Prop := ∃ l r,t=encode s l r

def push (b : Bool) (t : BitTape) : BitTape :=
  {t.shift .left with head:=some b}

def pop (t : BitTape) : BitTape :=
  if t.head=none then t else ({t with head:=none}).shift .right

end UniformKServer.StackTape

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite-control, finite-alphabet stack processors, compiled to the exact
binary multitape model. There is no unit-cost arithmetic oracle. -/
namespace UniformKServer.StackCompiler
open scoped Classical

instance instFintypeHeadMove : Fintype HeadMove := ⟨{.left,.stay,.right},by intro x;cases x <;> simp⟩

inductive Op (g : ℕ) where
  | keep | push (a : Fin g) | pop
  deriving DecidableEq,Fintype

structure Action (q m g : ℕ) where
  control : Fin q
  inputMove : HeadMove
  stackOp : Fin m → Op g
  emit : Option Bool
  yield : Bool
  deriving Fintype

structure Processor (q m g : ℕ) where
  start : Fin q
  transition : Fin q → Option Bool → (Fin m → Option (Fin g)) → Bool → Action q m g

structure State (q m g : ℕ) where
  control : Fin q
  input : BitTape
  store : Fin m → List (Fin g)
  outputRev : List Bool
  yielded : Bool

def applyOp {g : ℕ} (o : Op g) (s : List (Fin g)) : List (Fin g) :=
  match o with
  | .keep => s
  | .push a => a::s
  | .pop => s.tail

def step {q m g : ℕ} (P : Processor q m g) (s : State q m g) (coin : Bool) : State q m g :=
  if s.yielded then s else
  let a:=P.transition s.control s.input.head (fun i=>(s.store i).head?) coin
  ⟨a.control,s.input.shift a.inputMove,fun i=>applyOp (a.stackOp i) (s.store i),
    match a.emit with | none=>s.outputRev | some b=>b::s.outputRev,a.yield⟩

def initial {q m g : ℕ} (P : Processor q m g) (input : List Bool) : State q m g :=
  ⟨P.start,BitTape.ofWord input,fun _=>[],[],false⟩

def install {q m g : ℕ} (s : State q m g) (input : List Bool) : State q m g :=
  {s with input:=BitTape.ofWord input,outputRev:=[],yielded:=false}

def code {g : ℕ} (a j : Fin g) : Bool := decide (a=j)

def decode {g : ℕ} (v : Fin g → Option Bool) : Option (Fin g) :=
  if h : ∃ a,∀j,v j=some (code a j) then some (Classical.choose h) else none

abbrev controls (q m g : ℕ) := Sum (Fin q) (Action q m g)
def ctl (q m g : ℕ) : controls q m g ≃ Fin (Fintype.card (controls q m g)) := Fintype.equivFin _
def wire (m g : ℕ) : (Fin m × Fin g) ≃ Fin (Fintype.card (Fin m × Fin g)) := Fintype.equivFin _

def machine {q m g : ℕ} (P : Processor q m g) : BitMachine where
  controls := Fintype.card (controls q m g)
  tapes := Fintype.card (Fin m × Fin g)
  start := ctl q m g (.inl P.start)
  transition := fun c input work coin=>
    match (ctl q m g).symm c with
    | .inl c =>
      let a:=P.transition c input (fun i=>decode (fun j=>work (wire m g (i,j)))) coin
      {control:=ctl q m g (.inr a),inputMove:=a.inputMove,
        write:=fun v=> let i:=((wire m g).symm v).1
          match a.stackOp i with
          | .pop=>none
          | _=>work v,
        workMove:=fun v=>let i:=((wire m g).symm v).1
          match a.stackOp i with
          | .push _ => .left
          | .keep=>.stay
          | .pop=>if work v=none then .stay else .right,
        emit:=none,yield:=false}
    | .inr a =>
      {control:=ctl q m g (.inl a.control),inputMove:=.stay,
        write:=fun v=>let ij:=(wire m g).symm v
          match a.stackOp ij.1 with
          | .push a=>some (code a ij.2)
          | _=>work v,
        workMove:=fun _=>.stay,emit:=a.emit,yield:=a.yield}

structure Matches {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) : Prop where
  control : z.control=ctl q m g (.inl s.control)
  input : z.input=s.input
  output : z.outputRev=s.outputRev
  yielded : z.yielded=s.yielded
  work : ∀i j,StackTape.Rep ((s.store i).map (fun a=>code a j)) (z.work (wire m g (i,j)))

end UniformKServer.StackCompiler

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.StackCompiler
open scoped Classical

def beginOp {g : ℕ} (o : Op g) (t : BitTape) : BitTape :=
  match o with
  | .keep=>t
  | .push _=>t.shift .left
  | .pop=>StackTape.pop t

def finishOp {g : ℕ} (o : Op g) (j : Fin g) (t : BitTape) : BitTape :=
  match o with
  | .push a=>{t with head:=some (code a j)}
  | _=>t

def middle {q m g : ℕ} (P : Processor q m g) (a : Action q m g)
    (z : MachineState (machine P)) : MachineState (machine P) where
  control:=ctl q m g (.inr a)
  input:=z.input.shift a.inputMove
  work:=fun v=>beginOp (a.stackOp (((wire m g).symm v).1)) (z.work v)
  outputRev:=z.outputRev
  yielded:=false

def last {q m g : ℕ} (P : Processor q m g) (a : Action q m g)
    (z : MachineState (machine P)) : MachineState (machine P) where
  control:=ctl q m g (.inl a.control)
  input:=z.input
  work:=fun v=>finishOp (a.stackOp (((wire m g).symm v).1)) (((wire m g).symm v).2) (z.work v)
  outputRev:=match a.emit with | none=>z.outputRev | some b=>b::z.outputRev
  yielded:=a.yield

end UniformKServer.StackCompiler

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.StackCompiler

def run {q m g : ℕ} (P : Processor q m g) (s : State q m g) (coins : List Bool) : State q m g :=
  coins.foldl (step P) s

def padded : List Bool → List Bool
  | []=>[]
  | b::bs=>b::false::padded bs

theorem run_append {q m g : ℕ} (P : Processor q m g) (s : State q m g) (xs ys : List Bool) :
    run P s (xs++ys)=run P (run P s xs) ys := List.foldl_append

theorem run_cons {q m g : ℕ} (P : Processor q m g) (s : State q m g) (b : Bool) (bs : List Bool) :
    run P s (b::bs)=run P (step P s b) bs := rfl

end UniformKServer.StackCompiler

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FlatTM2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Flatten Mathlib's finitely supported TM2 programs into literal single
stack primitives. Every variable type and alphabet in this compiler is finite.
In particular a TM2 expression's arithmetic is not counted as one bit step. -/
namespace UniformKServer.FlatTM2
open Turing StackCompiler
open scoped Classical
variable {K Γ Λ V : Type} [Fintype K] [Fintype Γ] [Fintype V]
  [DecidableEq K] [Inhabited Λ]
variable (M : Λ → TM2.Stmt (fun _ : K=>Γ) Λ V) (S : Finset Λ) (hs : TM2.Supports M S)

abbrev Node := {x : Option (TM2.Stmt (fun _ : K=>Γ) Λ V) // x∈TM2.stmts M S}
abbrev Local := Node M S × V

def nodes : Local M S ≃ Fin (Fintype.card (Local M S)) := Fintype.equivFin _
def keys : K ≃ Fin (Fintype.card K) := Fintype.equivFin _
def letters : Γ ≃ Fin (Fintype.card Γ) := Fintype.equivFin _

def done : Node M S := ⟨none,by simp [TM2.stmts]⟩

def root (l : Λ) (hl : l∈S) : Node M S :=
  ⟨some (M l),Finset.some_mem_insertNone.mpr (Finset.mem_biUnion.mpr
    ⟨l,hl,TM2.stmts₁_self⟩)⟩

def sub {s t : TM2.Stmt (fun _ : K=>Γ) Λ V} (ht : t∈TM2.stmts₁ s)
    (hs : some s∈TM2.stmts M S) : Node M S := ⟨some t,TM2.stmts_trans ht hs⟩

/-- The action is allowed to inspect only stack heads and the finite local
variable. Its maps have finite domain and finite range. -/
def action (x : Local M S) (hds : Fin (Fintype.card K) → Option (Fin (Fintype.card Γ))) :
    Action (Fintype.card (Local M S)) (Fintype.card K) (Fintype.card Γ) :=
  let make (y : Node M S) (v : V) (ops : K → Op (Fintype.card Γ)) :=
    { control:=nodes M S (y,v),inputMove:=HeadMove.stay,
      stackOp:=fun i=>ops (keys.symm i),emit:=none,yield:=y.val.isNone }
  match x.1 with
  | ⟨none,_⟩=>make (done M S) x.2 (fun _=>.keep)
  | ⟨some (.push k f q),h⟩=>make (sub M S (t:=q) (by simp [TM2.stmts₁,TM2.stmts₁_self]) h) x.2
      (fun i=>if i=k then .push (letters (f x.2)) else .keep)
  | ⟨some (.peek k f q),h⟩=>make (sub M S (t:=q) (by simp [TM2.stmts₁,TM2.stmts₁_self]) h)
      (f x.2 ((hds (keys k)).map letters.symm)) (fun _=>.keep)
  | ⟨some (.pop k f q),h⟩=>make (sub M S (t:=q) (by simp [TM2.stmts₁,TM2.stmts₁_self]) h)
      (f x.2 ((hds (keys k)).map letters.symm)) (fun i=>if i=k then .pop else .keep)
  | ⟨some (.load f q),h⟩=>make (sub M S (t:=q) (by simp [TM2.stmts₁,TM2.stmts₁_self]) h) (f x.2) (fun _=>.keep)
  | ⟨some (.branch f q₁ q₂),h⟩=>if f x.2 then
      make (sub M S (t:=q₁) (by simp [TM2.stmts₁,TM2.stmts₁_self]) h) x.2 (fun _=>.keep)
    else make (sub M S (t:=q₂) (by simp [TM2.stmts₁,TM2.stmts₁_self]) h) x.2 (fun _=>.keep)
  | ⟨some (.goto f),h⟩=>make (root M S (f x.2) (TM2.stmts_supportsStmt hs h x.2)) x.2
      (fun _=>.keep)
  | ⟨some .halt,_⟩=>make (done M S) x.2 (fun _=>.keep)

/-- A finitely supported Mathlib TM2 has an actual finite-control processor.
It will be initialized with its input on its designated stack. -/
def processor (v₀ : V) : Processor (Fintype.card (Local M S)) (Fintype.card K) (Fintype.card Γ) where
  start:=nodes M S (root M S default hs.1,v₀)
  transition:=fun c _ h _=>action M S hs ((nodes M S).symm c) h

end UniformKServer.FlatTM2

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FlatOperational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.FlatTM2
open Turing StackCompiler
open scoped Classical
variable {K Γ Λ V : Type} [Fintype K] [Fintype Γ] [Fintype V]
  [DecidableEq K] [Inhabited Λ]
variable (M : Λ → TM2.Stmt (fun _ : K=>Γ) Λ V) (S : Finset Λ) (hs : TM2.Supports M S)

structure Runtime where
  pc : Option (TM2.Stmt (fun _ : K=>Γ) Λ V)
  var : V
  store : K → List Γ

/-- Exactly one primitive; the AST is not evaluated in a unit-cost StackCompiler.step. -/
def advance (x : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V)) : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V) :=
  match x.pc with
  | none=>x
  | some (.push k f q)=>⟨some q,x.var,Function.update x.store k (f x.var::x.store k)⟩
  | some (.peek k f q)=>⟨some q,f x.var (x.store k).head?,x.store⟩
  | some (.pop k f q)=>⟨some q,f x.var (x.store k).head?,Function.update x.store k (x.store k).tail⟩
  | some (.load f q)=>⟨some q,f x.var,x.store⟩
  | some (.branch f q₁ q₂)=>⟨some (if f x.var then q₁ else q₂),x.var,x.store⟩
  | some (.goto f)=>⟨some (M (f x.var)),x.var,x.store⟩
  | some .halt=>⟨none,x.var,x.store⟩

include hs in
omit [Fintype K] [Fintype Γ] [Fintype V] in
theorem advance_supported (x : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V))
    (hx : x.pc∈TM2.stmts M S) : (advance M x).pc∈TM2.stmts M S := by
  rcases x with ⟨pc,v,st⟩
  cases pc with
  | none=>exact hx
  | some q=>
    cases q with
    | push k f q | peek k f q | pop k f q | load f q=>
      exact TM2.stmts_trans (by simp [TM2.stmts₁,TM2.stmts₁_self]) hx
    | branch f q₁ q₂=>
      cases h : f v <;> simp only [advance,h,Bool.false_eq_true,↓reduceIte] <;>
        exact TM2.stmts_trans (by simp [TM2.stmts₁,TM2.stmts₁_self]) hx
    | goto f=>
      exact (root M S (f v) (TM2.stmts_supportsStmt hs hx v)).property
    | halt=>exact (done M S).property

def encode (x : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V)) (hx : x.pc∈TM2.stmts M S) :
    State (Fintype.card (Local M S)) (Fintype.card K) (Fintype.card Γ) :=
  ⟨nodes M S (⟨x.pc,hx⟩,x.var),BitTape.blank,
    fun i=>(x.store (keys.symm i)).map letters,[],x.pc.isNone⟩

theorem encode_step (v₀ : V) (x : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V))
    (hx : x.pc∈TM2.stmts M S) :
    StackCompiler.step (processor M S hs v₀) (encode M S x hx) false =
      encode M S (advance M x) (advance_supported M S hs x hx) := by
  rcases x with ⟨pc,v,st⟩
  cases pc with
  | none=>rfl
  | some q=>
    cases q with
    | push k f q=>
      simp only [StackCompiler.step,encode,Option.isNone_some,Bool.false_eq_true,↓reduceIte,
        processor,Equiv.symm_apply_apply,action,advance,sub]
      congr 1
      · funext i
        by_cases h : keys.symm i=k
        · simp [h,applyOp]
        · simp [h,applyOp,Function.update_of_ne]
    | pop k f q=>
      simp only [StackCompiler.step,encode,Option.isNone_some,Bool.false_eq_true,↓reduceIte,
        processor,Equiv.symm_apply_apply,action,advance,sub,List.head?_map,Option.map_map,
        Function.comp_def,Equiv.symm_apply_apply,Option.map_id']
      congr 1
      · funext i
        by_cases h : keys.symm i=k
        · simp [h,applyOp,List.map_tail]
        · simp [h,applyOp,Function.update_of_ne]
    | peek k f q=>
      simp [StackCompiler.step,encode,processor,action,advance,applyOp,BitTape.shift,sub]
    | load f q=>
      simp [StackCompiler.step,encode,processor,action,advance,applyOp,BitTape.shift,sub]
    | branch f q₁ q₂=>
      cases h:f v <;> simp [StackCompiler.step,encode,processor,action,advance,h,applyOp,BitTape.shift,sub]
    | goto f=>
      simp [StackCompiler.step,encode,processor,action,advance,applyOp,BitTape.shift,root]
    | halt=>
      simp [StackCompiler.step,encode,processor,action,advance,applyOp,BitTape.shift,done]

end UniformKServer.FlatTM2

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FlatTermination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.FlatTM2
open Turing StackCompiler
open scoped Classical
variable {K Γ Λ V : Type} [Fintype K] [Fintype Γ] [Fintype V]
  [DecidableEq K] [Inhabited Λ]
variable (M : Λ → TM2.Stmt (fun _ : K=>Γ) Λ V) (S : Finset Λ) (hs : TM2.Supports M S)

def fromCfg (c : TM2.Cfg (fun _ : K=>Γ) Λ V) : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V) :=
  ⟨c.l.map M,c.var,c.stk⟩

omit [Fintype K] [Fintype Γ] [Fintype V] [Inhabited Λ] in
/-- Every Mathlib TM2 macro-step is a finite sequence of literal primitives. -/
theorem advances_aux (q : TM2.Stmt (fun _ : K=>Γ) Λ V) (v : V) (st : K → List Γ) :
    ∃t : ℕ,(advance M)^[t] ⟨some q,v,st⟩=fromCfg M (TM2.stepAux q v st) := by
  induction q generalizing v st with
  | push k f q ih=>
    obtain ⟨t,ht⟩:=ih v (Function.update st k (f v::st k))
    exact ⟨t+1,by simpa [Function.iterate_succ_apply,advance] using ht⟩
  | peek k f q ih=>
    obtain ⟨t,ht⟩:=ih (f v (st k).head?) st
    exact ⟨t+1,by simpa [Function.iterate_succ_apply,advance] using ht⟩
  | pop k f q ih=>
    obtain ⟨t,ht⟩:=ih (f v (st k).head?) (Function.update st k (st k).tail)
    exact ⟨t+1,by simpa [Function.iterate_succ_apply,advance] using ht⟩
  | load f q ih=>
    obtain ⟨t,ht⟩:=ih (f v) st
    exact ⟨t+1,by simpa [Function.iterate_succ_apply,advance] using ht⟩
  | branch f q₁ q₂ ih₁ ih₂=>
    cases h:f v with
    | false=>
      obtain ⟨t,ht⟩:=ih₂ v st
      exact ⟨t+1,by simpa [Function.iterate_succ_apply,advance,h] using ht⟩
    | true=>
      obtain ⟨t,ht⟩:=ih₁ v st
      exact ⟨t+1,by simpa [Function.iterate_succ_apply,advance,h] using ht⟩
  | goto f=>exact ⟨1,rfl⟩
  | halt=>exact ⟨1,rfl⟩

omit [Fintype K] [Fintype Γ] [Fintype V] [Inhabited Λ] in
theorem advances_step (c c' : TM2.Cfg (fun _ : K=>Γ) Λ V) (h : c'∈TM2.step M c) :
    ∃t : ℕ,(advance M)^[t] (fromCfg M c)=fromCfg M c' := by
  rcases c with ⟨l,v,st⟩
  cases l with
  | none=>simp [TM2.step] at h
  | some l=>
    have he : c'=TM2.stepAux (M l) v st := by simpa [TM2.step,Option.mem_def] using (show TM2.stepAux (M l) v st = c' from by simpa [TM2.step,Option.mem_def] using h).symm
    subst c'
    exact advances_aux M (M l) v st

omit [Fintype K] [Fintype Γ] [Fintype V] [Inhabited Λ] in
theorem advances_reaches (c c' : TM2.Cfg (fun _ : K=>Γ) Λ V) (h : TM2.Reaches M c c') :
    ∃t : ℕ,(advance M)^[t] (fromCfg M c)=fromCfg M c' := by
  induction h with
  | refl=>exact ⟨0,rfl⟩
  | @tail b c' hab hbc ih=>
    obtain ⟨t,ht⟩:=ih
    obtain ⟨u,hu⟩:=advances_step M b c' hbc
    exact ⟨u+t,by rw [Function.iterate_add_apply,ht,hu]⟩

include hs in
omit [Fintype K] [Fintype Γ] [Fintype V] in
theorem iterate_supported (x : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V))
    (hx : x.pc∈TM2.stmts M S) (t : ℕ) : ((advance M)^[t] x).pc∈TM2.stmts M S := by
  induction t generalizing x with
  | zero=>exact hx
  | succ t ih=>
    rw [Function.iterate_succ_apply]
    exact ih _ (advance_supported M S hs x hx)

theorem encode_run (v₀ : V) (x : Runtime (K:=K) (Γ:=Γ) (Λ:=Λ) (V:=V))
    (hx : x.pc∈TM2.stmts M S) (t : ℕ) :
    run (processor M S hs v₀) (encode M S x hx) (List.replicate t false)=
      encode M S ((advance M)^[t] x) (iterate_supported M S hs x hx t) := by
  induction t generalizing x with
  | zero=>rfl
  | succ t ih=>
    rw [List.replicate_succ,run_cons,encode_step]
    exact ih _ (advance_supported M S hs x hx)

omit [Fintype K] [Fintype Γ] [Fintype V] [DecidableEq K] [Inhabited Λ] in
theorem fromCfg_supported (c : TM2.Cfg (fun _ : K=>Γ) Λ V)
    (hc : c.l∈Finset.insertNone S) : (fromCfg M c).pc∈TM2.stmts M S := by
  rcases c with ⟨l,v,st⟩
  cases l with
  | none=>exact (done M S).property
  | some l=>exact (root M S l (Finset.some_mem_insertNone.mp hc)).property

/-- Halting is inherited by the actual finite-control stack processor. -/
theorem processor_halts (v₀ : V) (c c' : TM2.Cfg (fun _ : K=>Γ) Λ V)
    (hc : c.l∈Finset.insertNone S) (h : TM2.Reaches M c c') (hhalt : c'.l=none) :
    ∃t : ℕ, (run (processor M S hs v₀)
      (encode M S (fromCfg M c) (fromCfg_supported M S c hc)) (List.replicate t false)).yielded=true ∧
      ∀i, (run (processor M S hs v₀)
      (encode M S (fromCfg M c) (fromCfg_supported M S c hc)) (List.replicate t false)).store i=
        (c'.stk (keys.symm i)).map letters := by
  obtain ⟨t,ht⟩:=advances_reaches M c c' h
  refine ⟨t,?_,?_⟩
  · rw [encode_run]
    change ((advance M)^[t] (fromCfg M c)).pc.isNone=true
    rw [ht]
    simp [fromCfg,hhalt]
  · intro i
    rw [encode_run]
    change (((advance M)^[t] (fromCfg M c)).store (keys.symm i)).map letters=_
    rw [ht]
    rfl

end UniformKServer.FlatTM2

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LiteralPartrec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.LiteralPartrec
open Turing Turing.ToPartrec Turing.PartrecToTM2 StackCompiler
open scoped Classical

instance instFintypeK'_solutions : Fintype K' := ⟨{.main,.rev,.aux,.stack},by intro i;cases i <;> simp⟩

def supp (c : Code) := codeSupp c Cont'.halt

def processor (c : Code) : Processor
    (Fintype.card (FlatTM2.Local tr (supp c))) (Fintype.card K') (Fintype.card Γ') :=
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  FlatTM2.processor tr (supp c) (tr_supports c Cont'.halt) none

def input (c : Code) (v : List ℕ) : State
    (Fintype.card (FlatTM2.Local tr (supp c))) (Fintype.card K') (Fintype.card Γ') :=
  FlatTM2.encode tr (supp c) (FlatTM2.fromCfg tr (PartrecToTM2.init c v))
    (FlatTM2.fromCfg_supported tr (supp c) (PartrecToTM2.init c v)
      (by simp only [PartrecToTM2.init];exact Finset.some_mem_insertNone.mpr (tr_supports c Cont'.halt).1))

theorem halts {c : Code} {v w : List ℕ} (hw : w∈Code.eval c v) :
    ∃t : ℕ,(run (processor c) (input c v) (List.replicate t false)).yielded=true ∧
      ∀i,(run (processor c) (input c v) (List.replicate t false)).store i=
        ((PartrecToTM2.halt w).stk (FlatTM2.keys.symm i)).map FlatTM2.letters := by
  let : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have hh : PartrecToTM2.halt w∈StateTransition.eval (TM2.step tr) (PartrecToTM2.init c v) := by
    rw [PartrecToTM2.tr_eval]
    exact (Part.mem_map_iff _).mpr ⟨w,hw,rfl⟩
  exact FlatTM2.processor_halts tr (supp c) (tr_supports c Cont'.halt) none
    (PartrecToTM2.init c v) (PartrecToTM2.halt w)
    (by simp only [PartrecToTM2.init];exact Finset.some_mem_insertNone.mpr (tr_supports c Cont'.halt).1)
    (StateTransition.mem_eval.mp hh).1 rfl

end UniformKServer.LiteralPartrec

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackPrimitive
attribute [-instance] _root_.OAI.UniformKServer.EpochControl.instFiniteBList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.StackPrimitive
open StackCompiler Primrec
open scoped Classical

abbrev Config (q m g : ℕ) := Fin q × (Fin m→List (Fin g)) × Bool

def ofState {q m g : ℕ} (s : State q m g) : Config q m g :=
  (s.control,s.store,s.yielded)

def data {q m g : ℕ} (P : Processor q m g)
    (x : Fin q × (Fin m→Option (Fin g))) : Fin q × (Fin m→Option (Option (Fin g))) × Bool :=
  let a:=P.transition x.1 none x.2 false
  (a.control,(fun i=>match a.stackOp i with | .keep=>none | .pop=>some none | .push b=>some (some b)),a.yield)

def apply {alphabetSize : ℕ} (a : Option (Option (Fin alphabetSize)))
    (s : List (Fin alphabetSize)) : List (Fin alphabetSize) :=
  match a with | none=>s | some none=>s.tail | some (some b)=>b::s

def advance {q m g : ℕ} (P : Processor q m g) (s : Config q m g) : Config q m g :=
  bif s.2.2 then s else
    let a:=data P (s.1,fun i=>(s.2.1 i).head?)
    (a.1,(fun i=>apply (a.2.1 i) (s.2.1 i)),a.2.2)

def Deterministic {q m g : ℕ} (P : Processor q m g) : Prop :=
  ∀c input h coin,P.transition c input h coin=P.transition c none h false

 theorem ofState_step {q m g : ℕ} (P : Processor q m g) (hp : Deterministic P)
    (s : State q m g) (b : Bool) :
    ofState (StackCompiler.step P s b)=advance P (ofState s) := by
  unfold StackCompiler.step advance ofState
  rw [Bool.cond_eq_ite]
  split_ifs with hy
  · rfl
  · rw [hp]
    dsimp only [data]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        simp only [applyOp]
        cases (P.transition s.control none (fun i=> (s.store i).head?) false).stackOp i <;> rfl
      · rfl

 theorem apply_primitive {alphabetSize : ℕ} : Primrec₂ (@apply alphabetSize) := by
  have h : Primrec (fun p : ((Option (Option (Fin alphabetSize)))×List (Fin alphabetSize))×Option (Fin alphabetSize)=>
      Option.casesOn (motive:=fun _=>List (Fin alphabetSize)) p.2 p.1.2.tail (fun b=>b::p.1.2)) := by
    exact Primrec.option_casesOn Primrec.snd (Primrec.list_tail.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).to₂
  have h₀:=Primrec.option_casesOn Primrec.fst Primrec.snd h.to₂
  refine h₀.of_eq ?_
  intro p
  rcases p with ⟨a,s⟩
  cases a with
  | none=>rfl
  | some a=>cases a <;> rfl

 theorem advance_primitive {q m g : ℕ} (P : Processor q m g) : Primrec (advance P) := by
  have hd : Primrec (fun s : Config q m g=>data P (s.1,fun i=>(s.2.1 i).head?)) := by
    apply (Primrec.dom_finite (data P)).comp
    apply Primrec.pair Primrec.fst
    apply Primrec.fin_curry.mpr
    exact Primrec.list_head?.comp (Primrec.fin_app.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  unfold advance
  apply Primrec.cond (Primrec.snd.comp Primrec.snd) Primrec.id
  apply Primrec.pair (Primrec.fst.comp hd)
  apply Primrec.pair
  · apply Primrec.fin_curry.mpr
    exact apply_primitive.comp
      (Primrec.fin_app.comp (Primrec.fst.comp (Primrec.snd.comp (hd.comp Primrec.fst))) Primrec.snd)
      (Primrec.fin_app.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  · exact Primrec.snd.comp (Primrec.snd.comp hd)

 theorem iter_primitive {q m g : ℕ} (P : Processor q m g) :
    Primrec₂ (fun t : ℕ=>fun s : Config q m g=>(advance P)^[t] s) :=
  Primrec.nat_iterate Primrec.fst Primrec.snd ((advance_primitive P).comp Primrec.snd).to₂

 theorem ofState_run {q m g : ℕ} (P : Processor q m g) (hp : Deterministic P)
    (s : State q m g) (bs : List Bool) :
    ofState (run P s bs)=(advance P)^[bs.length] (ofState s) := by
  induction bs generalizing s with
  | nil=>rfl
  | cons b bs ih=>
    rw [run_cons,ih,ofState_step P hp,List.length_cons,Function.iterate_succ_apply]

 theorem literal_deterministic (c : Turing.ToPartrec.Code) :
    Deterministic (LiteralPartrec.processor c) := by intro c input h coin;rfl

end UniformKServer.StackPrimitive

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LiteralInput
attribute [-instance] _root_.OAI.UniformKServer.EpochControl.instFiniteBList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.LiteralInput
open Turing Turing.PartrecToTM2 Primrec StackCompiler
open scoped Classical

 theorem primitive_trNat : Primrec (fun a : ℕ=>(trNat a).map (FlatTM2.letters (Γ:=Γ'))) := by
  have h : Primrec (fun a : ℕ=>a.bits.map (fun b=>FlatTM2.letters (RawBits.letter b))) :=
    Primrec.list_map RawBits.primitive_bits ((Primrec.dom_finite (fun b : Bool=>FlatTM2.letters (RawBits.letter b))).comp Primrec.snd).to₂
  exact h.of_eq (by intro a;rw [RawBits.trNat_bits,List.map_map];rfl)

 theorem primitive_trList : Primrec (fun xs : List ℕ=>(trList xs).map (FlatTM2.letters (Γ:=Γ'))) := by
  have h : Primrec (fun xs : List ℕ=>xs.foldr (fun a s=>
      (trNat a).map FlatTM2.letters++FlatTM2.letters Γ'.cons::s) []) :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      (Primrec.list_append.comp (primitive_trNat.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_cons.comp (Primrec.const (FlatTM2.letters Γ'.cons)) (Primrec.snd.comp Primrec.snd))).to₂
  exact h.of_eq (by
    intro xs
    induction xs with
    | nil=>rfl
    | cons a xs ih=>simp only [List.foldr_cons,trList,List.map_append,List.map_cons,ih])

 theorem input_config (c : Turing.ToPartrec.Code) (v : List ℕ) :
    StackPrimitive.ofState (LiteralPartrec.input c v)=
      ((LiteralPartrec.processor c).start,
        (fun i : Fin (Fintype.card K')=>if i=FlatTM2.keys K'.main then (trList v).map FlatTM2.letters else []),false) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext i
      change ((K'.elim (trList v) [] [] []) (FlatTM2.keys.symm i)).map FlatTM2.letters=_
      have he : (i=FlatTM2.keys K'.main) ↔ FlatTM2.keys.symm i=K'.main := by
        constructor
        · rintro rfl;exact Equiv.symm_apply_apply _ _
        · intro h;exact (Equiv.apply_symm_apply _ i).symm.trans (congrArg FlatTM2.keys h)
      dsimp only
      simp only [he]
      cases FlatTM2.keys.symm i <;> simp [K'.elim]
    · rfl

 theorem primitive_input (c : Turing.ToPartrec.Code) :
    Primrec (fun v=>StackPrimitive.ofState (LiteralPartrec.input c v)) := by
  have h : Primrec (fun v : List ℕ=>
      (((LiteralPartrec.processor c).start,
        (fun i : Fin (Fintype.card K')=>if i=FlatTM2.keys K'.main then (trList v).map FlatTM2.letters else []),false) :
        StackPrimitive.Config _ (Fintype.card K') (Fintype.card Γ'))) := by
    apply Primrec.pair (Primrec.const _)
    apply Primrec.pair _ (Primrec.const false)
    apply Primrec.fin_curry.mpr
    apply Primrec.ite
    · exact (Primrec.eq.comp Primrec.snd (Primrec.const (FlatTM2.keys K'.main)))
    · exact primitive_trList.comp Primrec.fst
    · exact Primrec.const []
  exact h.of_eq (fun v=>(input_config c v).symm)

end UniformKServer.LiteralInput

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LiteralVector
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                    
section

namespace UniformKServer.LiteralVector
open Turing Turing.ToPartrec

/-- Compile a tuple-valued total primitive recursive map without changing its
binary list interface by an additional unbounded encoding oracle. -/
theorem code_exists {n m : ℕ} (f : List.Vector ℕ n→List.Vector ℕ m) (hf : Primrec f) :
    ∃c : Code,∀v,Code.eval c v.val=Part.some (f v).val := by
  induction m with
  | zero=>
    refine ⟨.nil,?_⟩
    intro v
    have h : (f v).val=[] := List.eq_nil_of_length_eq_zero (f v).property
    simp [h]
  | succ m ih=>
    have hh : Partrec (fun v=>(Part.some ((f v).head))) :=
      (Primrec.vector_head.comp hf).to_comp
    obtain ⟨a,ha⟩:=Code.exists_code (Nat.Partrec'.part_iff.mpr hh)
    obtain ⟨b,hb⟩:=ih (fun v=>(f v).tail) (Primrec.vector_tail.comp hf)
    refine ⟨.cons a b,?_⟩
    intro v
    simp only [Code.cons_eval,ha,hb,Part.map_eq_map,Part.map_some,Part.bind_eq_bind,Part.bind_some,Part.pure_eq_some]
    congr 1
    exact congrArg Subtype.val (List.Vector.cons_head_tail (f v))

end UniformKServer.LiteralVector

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawFinite
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.RawFinite
open RawProgram RawCertificate
open scoped Classical

def requestToken (r : ℕ) : ℕ := RawBinary.value (natCode (r+1)++[true])

end UniformKServer.RawFinite

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RuntimeCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.RuntimeCertificate
open RawProgram RawCertificate RawFinite Primrec
open scoped Classical
abbrev Cert := List ℕ×ℕ

def has (S : List ℕ) (u : ℕ) : Bool := S.any (fun x=>decide (x=u))

section Primitive
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_has (S : α→List ℕ) (u : α→ℕ) (hS : Primrec S) (hu : Primrec u) :
    Primrec (fun x=>has (S x) (u x)) := by unfold has;fun_prop
@[fun_prop] theorem primitive_requestToken (r : α→ℕ) (hr : Primrec r) :
    Primrec (fun x=>requestToken (r x)) := by unfold requestToken;fun_prop
end Primitive

@[simp] theorem has_iff (S : List ℕ) (u : ℕ) : has S u=true ↔ u∈S := by
  simp [has,List.any_eq_true]

end UniformKServer.RuntimeCertificate

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LiteralPartial
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                     
section

namespace UniformKServer.LiteralVector
open Turing Turing.ToPartrec

/-- A partial tuple-valued program compiles on every successful input. -/
theorem partial_code_exists {n m : ℕ} (f : List.Vector ℕ n→.List.Vector ℕ m) (hf : Partrec f) :
    ∃c : Code,∀v w,w∈f v→w.val∈Code.eval c v.val := by
  induction m with
  | zero=>
    refine ⟨.nil,?_⟩
    intro v w hw
    have h : w.val=[] := List.eq_nil_of_length_eq_zero w.property
    simp [h]
  | succ m ih=>
    have hh : Partrec (fun v=>(f v).map List.Vector.head) :=
      hf.map (Primrec.vector_head.comp Primrec.snd).to_comp.to₂
    obtain ⟨a,ha⟩:=Code.exists_code (Nat.Partrec'.part_iff.mpr hh)
    have ht : Partrec (fun v=>(f v).map List.Vector.tail) :=
      hf.map (Primrec.vector_tail.comp Primrec.snd).to_comp.to₂
    obtain ⟨b,hb⟩:=ih (fun v=>(f v).map List.Vector.tail) ht
    refine ⟨.cons a b,?_⟩
    intro v w hw
    have h₁ : [w.head]∈Code.eval a v.val := by
      rw [ha]
      exact (Part.mem_map_iff _).mpr ⟨w.head,(Part.mem_map_iff _).mpr ⟨w,hw,rfl⟩,rfl⟩
    have h₂ : w.tail.val∈Code.eval b v.val := hb v w.tail ((Part.mem_map_iff _).mpr ⟨w,hw,rfl⟩)
    rw [Code.cons_eval]
    apply Part.mem_bind_iff.mpr
    refine ⟨[w.head],h₁,?_⟩
    apply Part.mem_bind_iff.mpr
    refine ⟨w.tail.val,h₂,?_⟩
    change w.val∈Part.some (w.head::w.tail.val)
    apply Part.mem_some_iff.mpr
    exact (congrArg Subtype.val (List.Vector.cons_head_tail w)).symm

end UniformKServer.LiteralVector

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ConstructorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.ConstructorProgram
open RawCertificate
open scoped Classical

def read (a : ℕ) : Input := RawBinary.input a.bits

end UniformKServer.ConstructorProgram

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochCut
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                               
section

namespace UniformKServer.EpochCut
open EpochShadow BoundaryPartition

def cut {n : ℕ} (k R : ℕ) : Finset (Fin n) → ℕ → List (Fin n) → List (Fin n) × List (Fin n)
  | _,_,[] => ([],[])
  | seen,c,r::w =>
    if k<(insert r seen).card ∧ c+1=R then ([r],w)
    else
      let q := cut k R (bookStep (k:=k) seen r) (c+if k<(insert r seen).card then 1 else 0) w
      (r::q.1,q.2)

end UniformKServer.EpochCut

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawControllerCost
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                        
section

namespace UniformKServer.RawControllerCost
open RawArithmetic RawCertificate EpochExpectation
variable {n k mult : ℕ}
  [NeZero k]
  (hk : 2≤k)
  (hkn : k≤n)
  (d : RationalMetric n)
  (draw : List Q)
  (hd : ∀x y : Fin n,value (RawTable.dist n draw x.val y.val)=d.distance x y)
  (v : Certificate)
  (hv : verify mult (n,k,draw) v=true)

def slope : ℝ := (mult:ℝ)*(ell v)^2

def endpoint : ℝ := (2*slope (mult:=mult) v+1)*k*(value (diam v):ℝ)+
  2*(restart v)*(value (sep v):ℝ)+2*(value (diam v):ℝ)

end UniformKServer.RawControllerCost

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackCoins
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.StackCompiler

def alternate : List Bool→List Bool
  | []=>[]
  | [a]=>[a]
  | a::_::xs=>a::alternate xs

 theorem alternate_length (xs : List Bool) : (alternate xs).length=(xs.length+1)/2 := by
  fun_induction alternate xs <;> simp_all only [List.length_nil,List.length_cons]
  omega

end UniformKServer.StackCompiler

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TypedStack
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
open StackCompiler
open scoped Classical

structure Action (Q K : Type*) (g : ℕ) where
  control : Q
  inputMove : HeadMove := .stay
  stackOp : K→Op g := fun _=>.keep
  emit : Option Bool := none
  yield : Bool := false
structure Processor (Q K : Type*) (g : ℕ) where
  start : Q
  transition : Q→Option Bool→(K→Option (Fin g))→Bool→Action Q K g
structure State (Q K : Type*) (g : ℕ) where
  control : Q
  input : BitTape
  store : K→List (Fin g)
  outputRev : List Bool
  yielded : Bool

variable {Q K : Type*} {g : ℕ}

def step (P : Processor Q K g) (s : State Q K g) (coin : Bool) : State Q K g :=
  if s.yielded then s else
  let a:=P.transition s.control s.input.head (fun i=>(s.store i).head?) coin
  ⟨a.control,s.input.shift a.inputMove,fun i=>applyOp (a.stackOp i) (s.store i),
    match a.emit with | none=>s.outputRev | some b=>b::s.outputRev,a.yield⟩
def install (s : State Q K g) (input : List Bool) : State Q K g :=
  {s with input:=BitTape.ofWord input,outputRev:=[],yielded:=false}

def eqv (A : Type*) [Fintype A] : A≃Fin (Fintype.card A) := Fintype.equivFin A

def compile [Fintype Q] [Fintype K] (P : Processor Q K g) :
    StackCompiler.Processor (Fintype.card Q) (Fintype.card K) g where
  start:=eqv Q P.start
  transition:=fun q inp h b=>
    let a:=P.transition ((eqv Q).symm q) inp (fun k=>h (eqv K k)) b
    ⟨eqv Q a.control,a.inputMove,fun i=>a.stackOp ((eqv K).symm i),a.emit,a.yield⟩
def encode [Fintype Q] [Fintype K] (s : State Q K g) :
    StackCompiler.State (Fintype.card Q) (Fintype.card K) g :=
  ⟨eqv Q s.control,s.input,fun i=>s.store ((eqv K).symm i),s.outputRev,s.yielded⟩

end UniformKServer.TypedStack

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_UniformWrapper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2
open TypedStack
open scoped Classical

abbrev g := Fintype.card Γ'

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

def tape (l : List (Option Bool)) : List Bool→BitTape
  | []=>⟨l,none,[]⟩
  | b::bs=>⟨l,some b,bs.map some⟩
@[simp] theorem ofWord_tape (w : List Bool) : BitTape.ofWord w=tape [] w := by cases w <;> rfl
@[simp] theorem tape_shift (l : List (Option Bool)) (b : Bool) (w : List Bool) :
    (tape l (b::w)).shift .right=tape (some b::l) w := by cases w <;> rfl

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
variable {Q K : Type*} {g : ℕ}

def retape (s : State Q K g) (i : BitTape) : State Q K g := {s with input:=i}

def SlowLink (P : Processor Q K g) (s z : State Q K g) : Prop :=
  z.yielded=true ∧ z.outputRev=[] ∧ ∀w coin,step P (install s w) coin=retape z (BitTape.ofWord w)

structure Prefix (P : Processor Q K g) (a z : State Q K g) (d : ℕ) where
  state : ℕ→State Q K g
  start : state 0=a
  finish : state d=z
  next : ∀j<d,SlowLink P (state j) (state (j+1))

end UniformKServer.TypedStack

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
open scoped Classical
variable {Q K : Type*} [Fintype Q] [Fintype K] {g : ℕ}

def frame (s : State Q K g) (i : BitTape) (out : List Bool) : State Q K g :=
  {s with input:=i,outputRev:=out,yielded:=true}

def CoreRep (P : Processor Q K g) (s : State Q K g)
    (z : MachineState (StackCompiler.machine (compile P))) : Prop :=
  ∃i out,StackCompiler.Matches (compile P) (encode (frame s i out)) z

end UniformKServer.TypedStack

end

end OAI
end


