-- Prove2me | Definitions.Def_OAIQ040C000
-- name    : OAIQ040C000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T00:41:56.449004+00:00
-- url     : https://prove2.me/theorems/3dd7c30a-d033-4723-825b-f910da942cce
-- title:
--   Definitions bundle OAIQ040C000 of the split of OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 690 declarations of OpenAI's Lean: 332 definitions, 13 inductive types or structures, 4 instances and 341 theorems. The definitions and types are `OAI.Percolation.Adj`, `OAI.Percolation.Along`, `OAI.Percolation.BadPieceEvent`, `OAI.Percolation.CappedBadGoodness`, `OAI.Percolation.CappedBadGoodnessEvent`, `OAI.Percolation.CappedGoodness`, `OAI.Percolation.CappedLocalLoad`, `OAI.Percolation.CappedLocalLoad.kernel`, `OAI.Percolation.CappedLocalLoad.row`, `OAI.Percolation.CappedLocalLoad.truncate`, `OAI.Percolation.CappedRadiusEvent`, `OAI.Percolation.ClusterSupportIn`, `OAI.Percolation.ClusterWindow`, `OAI.Percolation.Connected`, `OAI.Percolation.CutExists`, `OAI.Percolation.DisjointOccurrence`, `OAI.Percolation.EdgeQueryTree`, `OAI.Percolation.EdgeQueryTree.Valid`, `OAI.Percolation.EdgeQueryTree.eval`, `OAI.Percolation.EdgeQueryTree.forget`, `OAI.Percolation.EdgeQueryTree.leaf`, `OAI.Percolation.EdgeQueryTree.queryCount`, `OAI.Percolation.EdgeQueryTree.readSet`, `OAI.Percolation.EdgeQueryTree.reads`, `OAI.Percolation.EdgeQueryTree.revealment`, `OAI.Percolation.EdgeQueryTree.score`, `OAI.Percolation.EdgeQueryTree.value`, `OAI.Percolation.EndpointProfile`, `OAI.Percolation.EndpointProfile.H`, `OAI.Percolation.EndpointProfile.U`, `OAI.Percolation.EndpointProfile.cost`, `OAI.Percolation.EndpointProfile.geometricScale`, `OAI.Percolation.EndpointProfile.m`, `OAI.Percolation.EndpointProfile.potentialScale`, `OAI.Percolation.EscapeLabel`, `OAI.Percolation.EscapeLabel.autMap`, `OAI.Percolation.EscapeLabel.mass`, `OAI.Percolation.EscapeLabel.reverse`, `OAI.Percolation.EscapeLabel.reverseRootedEquiv`, `OAI.Percolation.FiniteChoiceTraceIndex` and 305 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/UnimodularPercolation, in whole or in part: `UnimodularPercolation_Cayley_Folner`, `UnimodularPercolation_Cayley_Geometry`, `UnimodularPercolation_Clusters_ExteriorMoments`, `UnimodularPercolation_Clusters_KernelMoments`, `UnimodularPercolation_Clusters_LargeContacts`, `UnimodularPercolation_Clusters_Resampling`, `UnimodularPercolation_Clusters_Uniqueness`, `UnimodularPercolation_Criticality_ClusterCount`, `UnimodularPercolation_Criticality_Sharpness`, `UnimodularPercolation_Criticality_Susceptibility`, `UnimodularPercolation_Deformation_AveragedDecrease`, `UnimodularPercolation_Deformation_Calibration`, `UnimodularPercolation_Deformation_ClusterProducts`, `UnimodularPercolation_Deformation_Corridors`, `UnimodularPercolation_Encounter_Geometry`, `UnimodularPercolation_Encounter_IntrinsicDistance`, `UnimodularPercolation_Encounter_Measurability`, `UnimodularPercolation_Encounter_Vertices`, `UnimodularPercolation_Escape_CollisionTails`, `UnimodularPercolation_Escape_Labels`, `UnimodularPercolation_Escape_PathSelection`, `UnimodularPercolation_Exploration_FractionalMoments`, `UnimodularPercolation_Exploration_Goodness`, `UnimodularPercolation_Exploration_Marked`, `UnimodularPercolation_Exploration_Moments`, `UnimodularPercolation_Exploration_TailBounds`, `UnimodularPercolation_Graph_Basic`, `UnimodularPercolation_Graph_Paths`, `UnimodularPercolation_Kernel_Amplification`, `UnimodularPercolation_Kernel_Bounds`, `UnimodularPercolation_Kernel_Connections`, `UnimodularPercolation_Kernel_ContactTrace`, `UnimodularPercolation_Kernel_Covariance`, `UnimodularPercolation_Kernel_DistinctMoments`, `UnimodularPercolation_Kernel_RussoRows`, `UnimodularPercolation_Kernel_ScaleBudget`, `UnimodularPercolation_Kernel_Spectral`, `UnimodularPercolation_Kernel_Sprinkling`, `UnimodularPercolation_Kernel_TraceBounds`, `UnimodularPercolation_ProductMeasure_Association`, `UnimodularPercolation_Splicing_EndpointMoments`, `UnimodularPercolation_Splicing_GapCodes`, `UnimodularPercolation_Splicing_Geometry`, `UnimodularPercolation_Splicing_MomentBounds`, `UnimodularPercolation_Splicing_ReferenceLaws`, `UnimodularPercolation_Splicing_Replay`, `UnimodularPercolation_Transport_EndpointKernels`, `UnimodularPercolation_Transport_TrajectoryMass`.
--
--   **Imports.** It imports the published bundle `Def_CayleyPercolation`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ040C002`; the statements `OAI_Percolation_critical_rootTriangleSqrt_derivative`, `OAI.Percolation.infinitely_many_of_pc_lt_lt_pu` and `OAI.Percolation.mainConclusion_of_strict_gap`; the proof of `OAI_Percolation_critical_rootTriangleSqrt_derivative`.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/UnimodularPercolation at commit adc7f12

import Mathlib
import Definitions.Def_CayleyPercolation

section
-- module Solutions.OAIQ040_CM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Graph_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed bond graphs, connectivity, percolation laws, kernels and countability. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}


def Adj (G : BondGraph V E) (x y : V) : Prop := ∃ e, G e = s(x, y)

 
def LocallyFinite (G : BondGraph V E) : Prop := ∀ x, {e | x ∈ G e}.Finite

 
def Connected (G : BondGraph V E) : Prop :=
  ∀ x y, Relation.ReflTransGen (Adj G) x y

 
def IsAut (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E) : Prop :=
  ∀ e, G (b e) = (G e).map a

 
def QuasiTransitive (G : BondGraph V E) : Prop :=
  ∃ representatives : Finset V, ∀ x, ∃ o ∈ representatives,
    ∃ a : V ≃ V, ∃ b : E ≃ E, IsAut G a b ∧ a o = x


noncomputable def operatorNorm (G : BondGraph V E) (p : unitInterval) : ℝ≥0∞ := by
  classical
  exact sInf {r | ∃ A : Hilbert V →L[ℂ] Hilbert V,
    HasKernel G p A ∧ r = ENNReal.ofReal ‖A‖}


def MainConclusion (G : BondGraph V E) : Prop :=
  (sSup {r | ∃ p : unitInterval, p < pc G ∧ r = operatorNorm G p} =
    operatorNorm G (pc G)) ∧
  operatorNorm G (pc G) < ⊤ ∧
  pc G < ptwo G ∧ ptwo G ≤ pu G ∧
  ∃ p₁ p₂ : unitInterval, pc G < p₁ ∧ p₁ < p₂ ∧ p₂ < 1 ∧
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)),
      ∀ p ∈ Set.Icc p₁ p₂, (infiniteClusters G (openEdges labels p)).Infinite

 

section Deterministic
variable (G : BondGraph V E) (ω : Set E)

@[simp] theorem conn_refl (x : V) : Conn G ω x x :=
  Relation.ReflTransGen.refl

theorem conn_trans {x y z : V} (hxy : Conn G ω x y) (hyz : Conn G ω y z) :
    Conn G ω x z := hxy.trans hyz

theorem conn_symm {x y : V} (h : Conn G ω x y) : Conn G ω y x := by
  induction h with
  | refl => exact conn_refl G ω _
  | @tail y z _ hyz ih =>
    rcases hyz with ⟨e, he, hlink⟩
    exact (Relation.ReflTransGen.single ⟨e, he, hlink.trans (Sym2.eq_swap ..)⟩).trans ih

theorem conn_mono {ω₁ ω₂ : Set E} (hω : ω₁ ⊆ ω₂) {x y : V}
    (h : Conn G ω₁ x y) : Conn G ω₂ x y := by
  apply Relation.ReflTransGen.mono (r := fun a b => ∃ e ∈ ω₁, G e = s(a, b)) ?_ x y h
  rintro a b ⟨e, he, hab⟩
  exact ⟨e, hω he, hab⟩

@[simp] theorem mem_cluster_self (x : V) : x ∈ cluster G ω x := conn_refl G ω x

@[simp] theorem conn_empty_iff (x y : V) : Conn G ∅ x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ he _ => rcases he with ⟨e, he, _⟩; exact he.elim
  · rintro rfl
    exact conn_refl G ∅ _

@[simp] theorem cluster_empty (x : V) : cluster G ∅ x = {x} := by
  ext y
  simp [cluster, eq_comm]

@[simp] theorem infiniteClusters_empty : infiniteClusters G ∅ = ∅ := by
  ext C
  simp only [infiniteClusters, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    not_and, not_exists]
  intro h x hx
  subst C
  simp at h

end Deterministic

section Probability
variable (G : BondGraph V E)

instance law_isProbabilityMeasure (p : unitInterval) :
    IsProbabilityMeasure (law p : Measure (Set E)) := by
  dsimp [law]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

@[simp] theorem law_zero : (law 0 : Measure (Set E)) = Measure.dirac ∅ := by
  simp [law]

@[simp] theorem law_one : (law 1 : Measure (Set E)) = Measure.dirac Set.univ := by
  simp [law]

@[simp] theorem twoPoint_self (p : unitInterval) (x : V) : twoPoint G p x x = 1 := by
  simp [twoPoint]

theorem twoPoint_nonneg (p : unitInterval) (x y : V) : 0 ≤ twoPoint G p x y :=
  ENNReal.toReal_nonneg

@[simp] theorem twoPoint_zero [Countable E] [DecidableEq V] (x y : V) :
    twoPoint G 0 x y = if x = y then 1 else 0 := by
  rw [twoPoint, law_zero, Measure.dirac_apply]
  by_cases h : x = y
  · simp [h]
  · rw [Set.indicator_of_notMem (by simpa using h)]
    simp [h]

end Probability

section Countability

 
theorem finite_neighbors {G : BondGraph V E} (hG : LocallyFinite G) (x : V) :
    {y | Adj G x y}.Finite := by
  classical
  have hends (e : E) : {y | y ∈ G e}.Finite := by
    apply (G e).toFinset.finite_toSet.subset
    intro y hy
    exact Sym2.mem_toFinset.mpr hy
  have hs : (⋃ e ∈ {e | x ∈ G e}, {y | y ∈ G e}).Finite :=
    (hG x).biUnion (fun e _ => hends e)
  apply hs.subset
  rintro y ⟨e, he⟩
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨e, he ▸ by simp, he ▸ by simp⟩

 
def reachBall (G : BondGraph V E) (x : V) : ℕ → Set V
  | 0 => {x}
  | n + 1 => reachBall G x n ∪ ⋃ y ∈ reachBall G x n, {z | Adj G y z}

theorem finite_reachBall {G : BondGraph V E} (hG : LocallyFinite G) (x : V) :
    ∀ n, (reachBall G x n).Finite := by
  intro n
  induction n with
  | zero => exact Set.finite_singleton x
  | succ n hn =>
    exact hn.union (hn.biUnion (fun y _ => finite_neighbors hG y))

end Countability

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel domination, monotone couplings and endpoint bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section KernelLimits
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable

 
noncomputable def finiteEmbedding : (V →₀ ℂ) →ₗ[ℂ] Hilbert V :=
  Finsupp.linearCombination ℂ (fun y => lp.single 2 y (1 : ℂ))

@[simp] theorem finiteEmbedding_single (y : V) (c : ℂ) :
    finiteEmbedding (Finsupp.single y c) = lp.single 2 y c := by
  simp [finiteEmbedding, ← lp.single_smul]

end KernelLimits

section Measurability

 

theorem measurableSet_conn [Countable V] [Countable E]
    (G : BondGraph V E) (x y : V) : MeasurableSet {ω | Conn G ω x y} := by
  classical
  have hedge (a b : V) : MeasurableSet {ω : Set E | ∃ e ∈ ω, G e = s(a, b)} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro e
    by_cases he : G e = s(a, b)
    · simpa [he] using (measurableSet_setOfPred.mpr (measurable_set_mem e))
    · simp [he]
  have hlist (l : List V) : MeasurableSet {ω : Set E |
      l.IsChain (fun a b => ∃ e ∈ ω, G e = s(a, b))} := by
    induction l with
    | nil => simp
    | cons a l ih =>
      cases l with
      | nil => simp
      | cons b l =>
        simpa only [List.isChain_cons_cons, Set.ofPred_and] using (hedge a b).inter ih
  have he : {ω | Conn G ω x y} = ⋃ l : List V,
      {ω | (x :: l).IsChain (fun a b => ∃ e ∈ ω, G e = s(a, b)) ∧
        (x :: l).getLast (by simp) = y} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨List.exists_isChain_cons_of_relationReflTransGen,
      fun ⟨l, hl, hy⟩ => List.relationReflTransGen_of_exists_isChain_cons l hl hy⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  by_cases hlast : (x :: l).getLast (by simp) = y
  · simpa [hlast] using hlist (x :: l)
  · simp [hlast]

end Measurability

section KernelDomination
attribute [local instance] Classical.propDecidable

@[simp] theorem finiteEmbedding_apply (f : V →₀ ℂ) (x : V) :
    finiteEmbedding f x = f x := by
  simp only [finiteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    ← lp.single_smul, lp.coeFn_sum, lp.coeFn_single]
  rw [Finset.sum_apply, Finset.sum_pi_single]
  split_ifs with h
  · simp
  · exact (Finsupp.notMem_support_iff.mp h).symm

 
noncomputable def positivePart (f : Hilbert V) : Hilbert V :=
  ⟨fun x => (‖f x‖ : ℂ), (lp.memℓp f).mono' (by intro x; simp)⟩

@[simp] theorem positivePart_apply (f : Hilbert V) (x : V) :
    positivePart f x = (‖f x‖ : ℂ) := rfl

@[simp] theorem norm_positivePart (f : Hilbert V) : ‖positivePart f‖ = ‖f‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro x
    simp
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro x
    simp



end KernelDomination

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_ProductMeasure_Association
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Association, disjoint witnesses and the BK inequality. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section WitnessAssociation
attribute [local instance] Classical.propDecidable
open Filter Topology

 
def FiniteWitness (A : Set (Set E)) : Prop :=
  ∀ ω ∈ A, ∃ s : Finset E, (s : Set E) ⊆ ω ∧ (s : Set E) ∈ A

end WitnessAssociation

section ClusterEvents
attribute [local instance] Classical.propDecidable
open Filter Topology


def clusterLarge (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ t : Finset V, n ≤ t.card ∧ ∀ y ∈ t, Conn G ω x y}

end ClusterEvents

section Automorphisms
attribute [local instance] Classical.propDecidable

theorem measurable_set_preimage (b : E ≃ E) :
    Measurable (fun ω : Set E => b ⁻¹' ω) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_pi_apply (b e)).comp MeasurableEquiv.setOfPred.symm.measurable))

 
theorem law_map_preimage_equiv (p : unitInterval) (b : E ≃ E) :
    (law p : Measure (Set E)).map (fun ω => b ⁻¹' ω) = law p := by
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map (measurable_set_preimage b) measurable_setOfPred]
  have he : (fun ω : Set E => b ⁻¹' ω) ∘ (fun f : E → Prop => {e | f e}) =
      (fun f : E → Prop => {e | f e}) ∘
        MeasurableEquiv.piCongrLeft (fun _ : E => Prop) b.symm := by
    funext f
    ext e
    simp only [Function.comp_apply, Set.mem_preimage, Set.mem_ofPred_eq]
    have hh := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : E => Prop) b.symm f (b e)
    exact iff_of_eq (by simpa only [Equiv.symm_apply_apply] using hh.symm)
  rw [he, ← Measure.map_map measurable_setOfPred (MeasurableEquiv.measurable _)]
  simp only [Set.mem_univ]
  congr 1
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : E => unitInterval.toNNReal p • Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False) b.symm

theorem isAut_symm (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) : IsAut G a.symm b.symm := by
  intro e
  have hh := congrArg (Sym2.map a.symm) (h (b.symm e))
  simpa only [Equiv.apply_symm_apply, Sym2.map_map, Equiv.symm_comp_self,
    Sym2.map_id', id_eq] using hh.symm

theorem conn_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) {ω : Set E} {x y : V} (hc : Conn G ω x y) :
    Conn G (b '' ω) (a x) (a y) := by
  induction hc with
  | refl => exact conn_refl G _ _
  | @tail v w hvw hed ih =>
    obtain ⟨e, he, hGe⟩ := hed
    exact ih.tail ⟨b e, Set.mem_image_of_mem _ he, by rw [h e, hGe, Sym2.map_mk]⟩

theorem conn_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (ω : Set E) (x y : V) :
    Conn G (b ⁻¹' ω) x y ↔ Conn G ω (a x) (a y) := by
  constructor
  · intro hc
    simpa only [Set.image_preimage_eq _ b.surjective] using conn_aut G h hc
  · intro hc
    have he : b.symm '' ω = b ⁻¹' ω := by
      ext e
      simp
    simpa only [Equiv.symm_apply_apply, he] using
      conn_aut G (isAut_symm G h) hc

theorem cluster_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (ω : Set E) (x : V) :
    a '' cluster G (b ⁻¹' ω) x = cluster G ω (a x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (conn_aut_iff G h ω x z).mp hz
  · intro hy
    change Conn G ω (a x) y at hy
    refine ⟨a.symm y, ?_, by simp⟩
    exact (conn_aut_iff G h ω x (a.symm y)).mpr (by simpa only [Equiv.apply_symm_apply] using hy)

end Automorphisms

section DisjointWitness
attribute [local instance] Classical.propDecidable

 
def DisjointOccurrence (A B : Set (Set E)) : Set (Set E) :=
  {ω | ∃ s t : Finset E, (s : Set E) ⊆ ω ∧ (t : Set E) ⊆ ω ∧
    Disjoint s t ∧ (s : Set E) ∈ A ∧ (t : Set E) ∈ B}

end DisjointWitness

section ORLift
attribute [local instance] Classical.propDecidable

noncomputable abbrev bitLaw (q : unitInterval) : Measure Prop :=
  unitInterval.toNNReal q • Measure.dirac True +
    unitInterval.toNNReal (unitInterval.symm q) • Measure.dirac False

end ORLift

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_Uniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cluster events, invariant covers and uniqueness thresholds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section InfiniteOrbits
attribute [local instance] Classical.propDecidable

def vertexOrbit (G : BondGraph V E) (x : V) : Set V :=
  {y | ∃ a : V ≃ V, ∃ b : E ≃ E, IsAut G a b ∧ a x = y}

theorem adj_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) {x y : V} (hxy : Adj G x y) : Adj G (a x) (a y) := by
  obtain ⟨e, he⟩ := hxy
  exact ⟨b e, by rw [h e, he, Sym2.map_mk]⟩

theorem mem_reachBall_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) {x y : V} {n : ℕ} (hy : y ∈ reachBall G x n) :
    a y ∈ reachBall G (a x) n := by
  induction n generalizing y with
  | zero => simpa only [reachBall, Set.mem_singleton_iff, Equiv.apply_eq_iff_eq] using hy
  | succ n ih =>
    rcases hy with hy | hy
    · exact Or.inl (ih hy)
    · change a y ∈ reachBall G (a x) n ∪ ⋃ z ∈ reachBall G (a x) n, {w | Adj G z w}
      apply Or.inr
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hy ⊢
      obtain ⟨z, hz, hzy⟩ := hy
      exact ⟨a z, ih hz, adj_aut G h hzy⟩



end InfiniteOrbits

section FinitePairBound
attribute [local instance] Classical.propDecidable
open scoped ComplexConjugate

noncomputable def deltaSum (F : Finset V) : Hilbert V := ∑ x ∈ F, lp.single 2 x (1 : ℂ)

@[simp] theorem deltaSum_apply (F : Finset V) (x : V) :
    deltaSum F x = if x ∈ F then 1 else 0 := by
  simp only [deltaSum, lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  simp

@[simp] theorem inner_deltaSum (F : Finset V) (f : Hilbert V) :
    inner ℂ (deltaSum F) f = ∑ x ∈ F, f x := by
  simp [deltaSum, lp.inner_single_left]

end FinitePairBound

section CoupledCovers
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]


def TouchedCover (G : BondGraph V E) (p q : unitInterval) (n : ℕ)
    (labels : E → unitInterval) : Prop :=
  ∃ f : Fin n → V, ∀ x, (cluster G (openEdges labels p) x).Infinite →
    ∃ i, Conn G (openEdges labels q) x (f i)

end CoupledCovers

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Graph_Paths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bond paths, degree bounds and positivity of the critical parameter. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section BondPaths
attribute [local instance] Classical.propDecidable

 
inductive Along (G : BondGraph V E) : V → List E → V → Prop
  | nil (x : V) : Along G x [] x
  | cons {x z y : V} {l : List E} (e : E) (he : G e = s(x,z))
      (tail : Along G z l y) : Along G x (e :: l) y

 theorem Along.conn {G : BondGraph V E} {x y : V} {l : List E} (h : Along G x l y)
    {ω : Set E} (ho : ∀ e ∈ l, e ∈ ω) : Conn G ω x y := by
  induction h with
  | nil => exact conn_refl G ω _
  | @cons x z y l e he ht ih =>
    exact (Relation.ReflTransGen.single ⟨e, ho e (by simp), he⟩).trans
      (ih (fun e' he' => ho e' (by simp [he'])))

 def openSimpleGraph (G : BondGraph V E) (ω : Set E) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ e ∈ ω, G e = s(x,y)
  symm := ⟨by
    rintro x y ⟨hxy, e, he, h⟩
    exact ⟨hxy.symm, e, he, h.trans (Sym2.eq_swap ..)⟩⟩
  loopless := ⟨by simp⟩

 theorem conn_iff_reachable (G : BondGraph V E) (ω : Set E) (x y : V) :
    Conn G ω x y ↔ (openSimpleGraph G ω).Reachable x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨.nil⟩
    | @tail z y h hy ih =>
      obtain ⟨w⟩ := ih
      by_cases hzy : z = y
      · subst y; exact ⟨w⟩
      · exact ⟨w.concat ⟨hzy, hy⟩⟩
  · rintro ⟨w⟩
    induction w with
    | nil => exact conn_refl G ω _
    | @cons x z y hadj w ih =>
      exact (Relation.ReflTransGen.single hadj.2).trans ih

 theorem walk_lift_bonds (G : BondGraph V E) (ω : Set E) {x y : V}
    (w : (openSimpleGraph G ω).Walk x y) :
    ∃ l : List E, Along G x l y ∧ l.map G = w.edges ∧ ∀ e ∈ l, e ∈ ω := by
  induction w with
  | nil => exact ⟨[], .nil _, rfl, by simp⟩
  | @cons x z y hadj w ih =>
    obtain ⟨e, he, heq⟩ := hadj.2
    obtain ⟨l, hl, hmap, hopen⟩ := ih
    refine ⟨e :: l, .cons e heq hl, ?_, ?_⟩
    · simp [hmap, heq]
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact he
      · exact hopen e' he'

 
 theorem conn_exists_bond_trail (G : BondGraph V E) {ω : Set E} {x y : V}
    (h : Conn G ω x y) :
    ∃ l : List E, Along G x l y ∧ l.Nodup ∧ ∀ e ∈ l, e ∈ ω := by
  obtain ⟨w⟩ := (conn_iff_reachable G ω x y).mp h
  obtain ⟨l, hl, hmap, hopen⟩ := walk_lift_bonds G ω (w.toPath : (openSimpleGraph G ω).Walk x y)
  refine ⟨l, hl, ?_, hopen⟩
  apply List.Nodup.of_map (f := G)
  rw [hmap]
  exact w.toPath.property.isTrail.edges_nodup

end BondPaths

section DegreeBound
attribute [local instance] Classical.propDecidable

 def Step (G : BondGraph V E) (x : V) := {ey : E × V // G ey.1 = s(x,ey.2)}

end DegreeBound

section SmallParameter
attribute [local instance] Classical.propDecidable

def TrailLength (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ y l, Along G x l y ∧ l.Nodup ∧ l.length = n ∧ ∀ e ∈ l, e ∈ ω}

 theorem Along.mem_reachBall {G : BondGraph V E} {x y : V} {l : List E}
    (h : Along G x l y) : y ∈ reachBall G x l.length := by
  induction h with
  | nil => exact Set.mem_singleton _
  | @cons x z y l e he ht ih =>
    have hadj : Adj G x z := ⟨e,he⟩
    have hstep : ∀ n, reachBall G z n ⊆ reachBall G x (n+1) := by
      intro n
      induction n with
      | zero =>
        rintro w rfl
        exact Or.inr (Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨Set.mem_singleton _, hadj⟩⟩)
      | succ n ih =>
        rintro w (hw | hw)
        · exact Or.inl (ih hw)
        · right
          simp only [Set.mem_iUnion] at hw ⊢
          obtain ⟨v,hv,hvw⟩ := hw
          exact ⟨v,ih hv,hvw⟩
    exact hstep _ ih

end SmallParameter

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Sprinkling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sprinkling estimates for finite and infinite graph operators. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section ColoredSprinkling
attribute [local instance] Classical.propDecidable

 def colorInclusion (m : ℕ) : E × Fin m ↪ E × Fin (m+1) :=
  Function.Embedding.prodMap (Function.Embedding.refl E) Fin.castSuccEmb

 def baseColors (m : ℕ) : Set (E × Fin (m+1)) := Set.range (colorInclusion (E := E) m)

 def baseField (m : ℕ) (ω : Set (E × Fin (m+1))) : Set E :=
  Prod.fst '' (colorInclusion m ⁻¹' ω)

 noncomputable def dartSource (G : BondGraph V E) (d : E × Bool) : V :=
   if d.2 then (G d.1).out.1 else (G d.1).out.2
 noncomputable def dartTarget (G : BondGraph V E) (d : E × Bool) : V :=
   if d.2 then (G d.1).out.2 else (G d.1).out.1

end ColoredSprinkling

section FiniteGraphOperators
attribute [local instance] Classical.propDecidable

 noncomputable def adjacencyOperator [Fintype E] (G : BondGraph V E) :
    Hilbert V →L[ℂ] Hilbert V :=
  ∑ d : E × Bool, (lp.singleContinuousLinearMap ℂ (fun _ : V => ℂ) 2 (dartSource G d)).comp
    (lp.evalCLM ℂ (fun _ : V => ℂ) 2 (dartTarget G d))

end FiniteGraphOperators

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Sharpness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Russo formulae, exterior exposure and subcritical sharpness. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteRusso
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

 
noncomputable def bernoulliPolynomial (s : Finset E) (f : Finset E → ℝ) (p : ℝ) : ℝ :=
  ∑ t ∈ s.powerset, f t * p ^ t.card * (1-p) ^ (s.card-t.card)

@[simp] theorem bernoulliPolynomial_empty (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial ∅ f p = f ∅ := by simp [bernoulliPolynomial]

theorem bernoulliPolynomial_insert (s : Finset E) (e : E) (he : e ∉ s)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial (insert e s) f p =
      (1-p)*bernoulliPolynomial s f p + p*bernoulliPolynomial s (fun t => f (insert e t)) p := by
  have hd : Disjoint s.powerset (s.powerset.image (insert e)) := by
    apply Finset.disjoint_left.mpr
    intro t ht himg
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp himg
    exact he ((Finset.mem_powerset.mp ht) (by simp))
  have hinj : Set.InjOn (insert e) (↑s.powerset : Set (Finset E)) := by
    intro t ht r hr h
    have ht' : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    have hr' : e ∉ r := fun h => he (Finset.mem_powerset.mp hr h)
    have hh := congrArg (fun t : Finset E => t.erase e) h
    simpa [ht', hr'] using hh
  simp only [bernoulliPolynomial, Finset.powerset_insert, Finset.sum_union hd,
    Finset.sum_image hinj, Finset.mul_sum, Finset.card_insert_of_notMem he]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    have hcard := Finset.card_le_card (Finset.mem_powerset.mp ht)
    have hexp : s.card+1-t.card = (s.card-t.card)+1 := by omega
    rw [hexp, pow_succ]
    ring
  · apply Finset.sum_congr rfl
    intro t ht
    have het : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    simp only [Finset.card_insert_of_notMem het, Nat.add_sub_add_right, pow_succ]
    ring


@[simp] theorem bernoulliPolynomial_zero (s : Finset E) (p : ℝ) :
    bernoulliPolynomial s (fun _ => 0) p = 0 := by simp [bernoulliPolynomial]

theorem bernoulliPolynomial_const (s : Finset E) (c p : ℝ) :
    bernoulliPolynomial s (fun _ => c) p = c := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih => rw [bernoulliPolynomial_insert s e he]; simp only [ih]; ring


def closedPivotal (A : Set (Set E)) (e : E) : Set (Set E) :=
  {ω | e ∉ ω ∧ ω ∉ A ∧ insert e ω ∈ A}

end FiniteRusso

section ExteriorExposure
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

 
theorem conn_insert_iff (G : BondGraph V E) (ω : Set E) (e : E) (a b x y : V)
    (he : G e = s(a,b)) :
    Conn G (insert e ω) x y ↔ Conn G ω x y ∨
      (Conn G ω x a ∧ Conn G ω b y) ∨ (Conn G ω x b ∧ Conn G ω a y) := by
  constructor
  · intro hh
    induction hh with
    | refl => exact Or.inl (conn_refl G ω x)
    | @tail u v huv huv' ih =>
      obtain ⟨f,hf,hfuv⟩ := huv'
      rcases Set.mem_insert_iff.mp hf with rfl | hf
      · have hp : s(a,b) = s(u,v) := he.symm.trans hfuv
        rcases Sym2.eq_iff.mp hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · rcases ih with h | ⟨hxa,hba⟩ | ⟨hxb,haa⟩
          · exact Or.inr (Or.inl ⟨h,conn_refl G ω b⟩)
          · exact Or.inr (Or.inl ⟨hxa,conn_refl G ω b⟩)
          · exact Or.inl hxb
        · rcases ih with h | ⟨hxa,hbb⟩ | ⟨hxb,hab⟩
          · exact Or.inr (Or.inr ⟨h,conn_refl G ω a⟩)
          · exact Or.inl hxa
          · exact Or.inr (Or.inr ⟨hxb,conn_refl G ω a⟩)
      · have huvω : Conn G ω u v := .single ⟨f,hf,hfuv⟩
        rcases ih with h | ⟨hxa,hbu⟩ | ⟨hxb,hau⟩
        · exact Or.inl (h.trans huvω)
        · exact Or.inr (Or.inl ⟨hxa,hbu.trans huvω⟩)
        · exact Or.inr (Or.inr ⟨hxb,hau.trans huvω⟩)
  · intro hh
    have hm : ω ⊆ insert e ω := Set.subset_insert e ω
    have hab : Conn G (insert e ω) a b := .single ⟨e,Set.mem_insert e ω,he⟩
    rcases hh with h | ⟨hxa,hby⟩ | ⟨hxb,hay⟩
    · exact conn_mono G hm h
    · exact (conn_mono G hm hxa).trans (hab.trans (conn_mono G hm hby))
    · exact (conn_mono G hm hxb).trans ((conn_symm G _ hab).trans (conn_mono G hm hay))

 
def internalEdges (G : BondGraph V E) (S : Set V) : Set E :=
  {e | ∀ x ∈ G e, x ∈ S}

@[simp] theorem mem_internalEdges_of_ends (G : BondGraph V E) (S : Set V)
    (e : E) (a b : V) (he : G e = s(a,b)) :
    e ∈ internalEdges G S ↔ a ∈ S ∧ b ∈ S := by
  simp [internalEdges, he]

 
def unexposed (G : BondGraph V E) (Λ : Set V) (ω : Set E) : Set V :=
  {x | ∀ y, Conn G ω x y → y ∈ Λ}

theorem unexposed_subset (G : BondGraph V E) (Λ : Set V) (ω : Set E) :
    unexposed G Λ ω ⊆ Λ := fun x hx => hx x (conn_refl G ω x)


def escapeEvent (G : BondGraph V E) (Λ : Set V) (x : V) : Set (Set E) :=
  {ω | x ∉ unexposed G Λ ω}

attribute [local instance] Classical.decEq


noncomputable def unexposedRegion (G : BondGraph V E) (Λ : Finset V) (ω : Set E) : Finset V :=
  ((Set.toFinite (Λ : Set V)).subset (unexposed_subset G (Λ : Set V) ω)).toFinset

@[simp] theorem coe_unexposedRegion (G : BondGraph V E) (Λ : Finset V) (ω : Set E) :
    (unexposedRegion G Λ ω : Set V) = unexposed G (Λ : Set V) ω := by
  simp [unexposedRegion]


noncomputable def internalSupport (G : BondGraph V E) (S : Set V) (F : Finset E) : Finset E :=
  F.filter (fun e => e ∈ internalEdges G S)


def crossingReach (G : BondGraph V E) (S : Set V) (x : V) (ω : Set E) (e : E) : Prop :=
  ∃ a b, G e = s(a,b) ∧ a ∈ S ∧ b ∉ S ∧ Conn G ω x a

noncomputable def crossingCount (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) (ω : Set E) : ℝ :=
  ∑ e ∈ F, if crossingReach G S x ω e then (1:ℝ) else 0

 
noncomputable def boundaryExpectation (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) (p : ℝ) : ℝ :=
  bernoulliPolynomial (internalSupport G S F)
    (fun t => crossingCount G S x F (t : Set E)) p

noncomputable def closedEscapeCount (G : BondGraph V E) (Λ : Set V) (x : V)
    (F : Finset E) (ω : Set E) : ℝ :=
  ∑ e ∈ F, if ω ∈ closedPivotal (escapeEvent G Λ x) e then (1:ℝ) else 0

end ExteriorExposure

section SharpnessBridge
attribute [local instance] Classical.propDecidable Classical.decEq
open Filter Topology


noncomputable def incidentSupport (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) : Finset E := Λ.biUnion (fun x => (hloc x).toFinset)

@[simp] theorem mem_incidentSupport (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (e : E) : e ∈ incidentSupport G hloc Λ ↔ ∃ x ∈ Λ, x ∈ G e := by
  simp [incidentSupport]

theorem incidentSupport_mono (G : BondGraph V E) (hloc : LocallyFinite G)
    {S Λ : Finset V} (hS : S ⊆ Λ) : incidentSupport G hloc S ⊆ incidentSupport G hloc Λ := by
  intro e he
  obtain ⟨x,hx,hxe⟩ := (mem_incidentSupport G hloc S e).mp he
  exact (mem_incidentSupport G hloc Λ e).mpr ⟨x,hS hx,hxe⟩


noncomputable def boundaryCost (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (p : ℝ) : ℝ :=
  p*boundaryExpectation G S x (incidentSupport G hloc S) p

theorem incidentSupport_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (S : Finset V) :
    incidentSupport G hloc (S.map a.toEmbedding) =
      (incidentSupport G hloc S).map b.toEmbedding := by
  ext e
  obtain ⟨d,rfl⟩ := b.surjective e
  simp only [mem_incidentSupport,Finset.mem_map,Equiv.toEmbedding_apply,
    b.injective.eq_iff,exists_eq_right]
  constructor
  · rintro ⟨x,⟨y,hy,rfl⟩,hx⟩
    rw [h d,Sym2.mem_map] at hx
    obtain ⟨z,hz,hzy⟩ := hx
    have hz' : z = y := a.injective hzy
    exact ⟨y,hy,hz' ▸ hz⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨a x,⟨x,hx,rfl⟩,by rw [h d]; exact Sym2.mem_map.mpr ⟨x,he,rfl⟩⟩

end SharpnessBridge

section SharpnessSusceptibility
open Filter Topology
attribute [local instance] Classical.propDecidable Classical.decEq


theorem conn_internal_endpoint (G : BondGraph V E) (S : Set V) {ω : Set E} {x y : V}
    (hx : x ∈ S) (h : Conn G (ω ∩ internalEdges G S) x y) : y ∈ S := by
  induction h with
  | refl => exact hx
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    exact ((mem_internalEdges_of_ends G S e a b heq).mp he.2).2

def CutExists (G : BondGraph V E) (S : Set V) (e : E) : Prop :=
  ∃ a b, G e = s(a,b) ∧ a ∈ S ∧ b ∉ S

noncomputable def cutInside [Nonempty V] (G : BondGraph V E) (S : Set V) (e : E) : V :=
  if h : CutExists G S e then h.choose else Classical.arbitrary V

noncomputable def cutOutside [Nonempty V] (G : BondGraph V E) (S : Set V) (e : E) : V :=
  if h : CutExists G S e then h.choose_spec.choose else Classical.arbitrary V

end SharpnessSusceptibility

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_Marked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked decision trees, graph searches and pivotal geometry. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MarkedExploration


inductive ProbeTree where
  | done (success : Bool)
  | edge (closed open_ : ProbeTree)
  | mark (unmarked marked : ProbeTree)

namespace ProbeTree

@[reducible] def Leaf : ProbeTree → Type
  | .done _ => Unit
  | .edge t₀ t₁ => Leaf t₀ ⊕ Leaf t₁
  | .mark t₀ t₁ => Leaf t₀ ⊕ Leaf t₁

instance leafFintype : (t : ProbeTree) → Fintype t.Leaf
  | .done _ => inferInstanceAs (Fintype Unit)
  | .edge t₀ t₁ => @instFintypeSum _ _ (leafFintype t₀) (leafFintype t₁)
  | .mark t₀ t₁ => @instFintypeSum _ _ (leafFintype t₀) (leafFintype t₁)

noncomputable def weight (p h : ℝ) : (t : ProbeTree) → t.Leaf → ℝ
  | .done _, _ => 1
  | .edge t₀ _, .inl l => (1-p)*weight p h t₀ l
  | .edge _ t₁, .inr l => p*weight p h t₁ l
  | .mark t₀ _, .inl l => (1-h)*weight p h t₀ l
  | .mark _ t₁, .inr l => h*weight p h t₁ l

noncomputable def score (p : ℝ) : (t : ProbeTree) → t.Leaf → ℝ
  | .done _, _ => 0
  | .edge t₀ _, .inl l => score p t₀ l-p
  | .edge _ t₁, .inr l => score p t₁ l+(1-p)
  | .mark t₀ _, .inl l => score p t₀ l
  | .mark _ t₁, .inr l => score p t₁ l

def queries : (t : ProbeTree) → t.Leaf → ℕ
  | .done _, _ => 0
  | .edge t₀ _, .inl l => queries t₀ l+1
  | .edge _ t₁, .inr l => queries t₁ l+1
  | .mark t₀ _, .inl l => queries t₀ l
  | .mark _ t₁, .inr l => queries t₁ l

@[reducible] def outcome : (t : ProbeTree) → t.Leaf → Bool
  | .done b, _ => b
  | .edge t₀ _, .inl l => outcome t₀ l
  | .edge _ t₁, .inr l => outcome t₁ l
  | .mark t₀ _, .inl l => outcome t₀ l
  | .mark _ t₁, .inr l => outcome t₁ l

noncomputable def successWeight (p h : ℝ) (t : ProbeTree) (l : t.Leaf) : ℝ :=
  if outcome t l then weight p h t l else 0

noncomputable def successMass (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, successWeight p h t l

noncomputable def successScore (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, successWeight p h t l * score p t l

noncomputable def successQueries (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, successWeight p h t l * queries t l

noncomputable def dweight (p h : ℝ) : (t : ProbeTree) → t.Leaf → ℝ
  | .done _, _ => 0
  | .edge t₀ _, .inl l => -weight p h t₀ l+(1-p)*dweight p h t₀ l
  | .edge _ t₁, .inr l => weight p h t₁ l+p*dweight p h t₁ l
  | .mark t₀ _, .inl l => (1-h)*dweight p h t₀ l
  | .mark _ t₁, .inr l => h*dweight p h t₁ l


inductive IsMarkSearch : ProbeTree → Prop
  | fail : IsMarkSearch (.done false)
  | edge {t₀ t₁} : IsMarkSearch t₀ → IsMarkSearch t₁ → IsMarkSearch (.edge t₀ t₁)
  | mark {t₀} : IsMarkSearch t₀ → IsMarkSearch (.mark t₀ (.done true))

def marks : (t : ProbeTree) → t.Leaf → ℕ
  | .done _, _ => 0
  | .edge t₀ _, .inl l => marks t₀ l
  | .edge _ t₁, .inr l => marks t₁ l
  | .mark t₀ _, .inl l => marks t₀ l+1
  | .mark _ t₁, .inr l => marks t₁ l+1

noncomputable def successMarks (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, successWeight p h t l * marks t l

@[simp] lemma successMass_done (p h : ℝ) (b : Bool) :
    successMass p h (.done b) = if b then 1 else 0 := by
  cases b <;> simp [successMass,successWeight,outcome,weight]

@[simp] lemma successMarks_done (p h : ℝ) (b : Bool) : successMarks p h (.done b) = 0 := by
  simp [successMarks,marks]


end ProbeTree
end MarkedExploration

section LabelledExploration
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

inductive LabelledTree (V E : Type*) where
  | done (success : Bool)
  | edge (e : E) (closed opened : LabelledTree V E)
  | mark (v : V) (unmarked marked : LabelledTree V E)

namespace LabelledTree

def forget : LabelledTree V E → ProbeTree
  | .done b => .done b
  | .edge _ t₀ t₁ => .edge t₀.forget t₁.forget
  | .mark _ t₀ t₁ => .mark t₀.forget t₁.forget

@[reducible] noncomputable def eval (ω : Finset E) (m : Finset V) : LabelledTree V E → Bool
  | .done b => b
  | .edge e t₀ t₁ => if e ∈ ω then eval ω m t₁ else eval ω m t₀
  | .mark v t₀ t₁ => if v ∈ m then eval ω m t₁ else eval ω m t₀

def Valid (Q : Finset E) (F : Finset V) : LabelledTree V E → Prop
  | .done _ => True
  | .edge e t₀ t₁ => e ∈ Q ∧ Valid (Q.erase e) F t₀ ∧ Valid (Q.erase e) F t₁
  | .mark v t₀ t₁ => v ∈ F ∧ Valid Q (F.erase v) t₀ ∧ Valid Q (F.erase v) t₁

end LabelledTree

end LabelledExploration

section GraphMarkedSearch
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

 
def SearchCrossing (G : BondGraph V E) (Q : Finset E) (R : Finset V) : Prop :=
  ∃ t : E × V × V, t.1 ∈ Q ∧ t.2.1 ∈ R ∧ t.2.2 ∉ R ∧ G t.1 = s(t.2.1,t.2.2)

noncomputable def searchCrossing (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (h : SearchCrossing G Q R) : E × V × V := Classical.choose h


def SearchAvailable (G : BondGraph V E) (Q : Finset E) (R F : Finset V) : Prop :=
  ∀ e ∈ Q, ∀ v ∈ G e, v ∈ R ∨ v ∈ F

noncomputable def clusterSearch (G : BondGraph V E) : ℕ → Finset E → Finset V → LabelledTree V E
  | 0, _, _ => .done false
  | n+1, Q, R =>
    if hc : SearchCrossing G Q R then
      let t := searchCrossing G Q R hc
      .edge t.1 (clusterSearch G n (Q.erase t.1) R)
        (.mark t.2.2 (clusterSearch G n (Q.erase t.1) (insert t.2.2 R)) (.done true))
    else .done false


def SeedMarked (G : BondGraph V E) (ω : Set E) (R m : Finset V) : Prop :=
  ∃ a ∈ R, ∃ b ∈ m, Conn G ω a b

end GraphMarkedSearch

section GraphSearchCost
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace ProbeTree

def Budget (t : ProbeTree) (K d : ℕ) : Prop := ∀ l, queries t l ≤ K+d*marks t l

end ProbeTree


end GraphSearchCost

section MarkedFirstMoment
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


noncomputable def markedOpenPivotals (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (m : Finset V) : Finset E :=
  Q.filter fun e => e ∈ ω ∧ (∃ y ∈ m, Conn G (ω : Set E) x y) ∧
      ¬ ∃ y ∈ m, Conn G (ω.erase e : Set E) x y


end MarkedFirstMoment

section PivotalGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
def MarkedEvent (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V) : Prop :=
  ∃ y ∈ m, Conn G ω x y

 
def OpenMarkedPivotal (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    (e : E) : Prop :=
  e ∈ ω ∧ MarkedEvent G ω m x ∧ ¬MarkedEvent G (ω \ {e}) m x

theorem edge_cluster_sides (G : BondGraph V E) (ω : Set E) (x : V)
    {e : E} {a b : V} (he : e ∈ ω) (hab : G e = s(a,b)) :
    a ∈ cluster G ω x ↔ b ∈ cluster G ω x := by
  have hc : Conn G ω a b := .single ⟨e,he,hab⟩
  exact ⟨fun h => h.trans hc,fun h => h.trans (conn_symm G ω hc)⟩

 
theorem conn_restrict_cluster_compl (G : BondGraph V E) (ω : Set E) (x : V)
    {a b : V} (ha : a ∉ cluster G ω x) (hab : Conn G ω a b) :
    Conn G (ω ∩ internalEdges G (cluster G ω x)ᶜ) a b := by
  induction hab with
  | refl => exact conn_refl G _ a
  | @tail u v hau huv ih =>
    obtain ⟨e,he,heq⟩ := huv
    have hu : u ∉ cluster G ω x := fun h => ha (h.trans (conn_symm G ω hau))
    have hv : v ∉ cluster G ω x := fun h => hu ((edge_cluster_sides G ω x he heq).mpr h)
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e u v heq).mpr ⟨hu,hv⟩⟩,heq⟩

theorem conn_restrict_cluster (G : BondGraph V E) (ω : Set E) (x : V)
    {a b : V} (ha : a ∈ cluster G ω x) (hab : Conn G ω a b) :
    Conn G (ω ∩ internalEdges G (cluster G ω x)) a b := by
  induction hab with
  | refl => exact conn_refl G _ a
  | @tail u v hau huv ih =>
    obtain ⟨e,he,heq⟩ := huv
    have hu : u ∈ cluster G ω x := ha.trans hau
    have hv : v ∈ cluster G ω x := (edge_cluster_sides G ω x he heq).mp hu
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e u v heq).mpr ⟨hu,hv⟩⟩,heq⟩

 
theorem openMarkedPivotal_oriented (G : BondGraph V E) (ω : Set E) (m : Set V)
    (x : V) {e : E} (he : OpenMarkedPivotal G ω m x e) :
    ∃ a b, G e = s(a,b) ∧ Conn G (ω \ {e}) x a ∧
      ¬Conn G (ω \ {e}) x b ∧ MarkedEvent G (ω \ {e}) m b := by
  obtain ⟨y,hy,hxy⟩ := he.2.1
  obtain ⟨a,b,hab⟩ : ∃ a b, G e = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G e)
    exact ⟨a,b,h.symm⟩
  have heq : insert e (ω \ {e}) = ω := by
    have heω : e ∈ ω := he.1
    ext d
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    by_cases h : d = e <;> simp_all
  rw [← heq,conn_insert_iff G _ e a b x y hab] at hxy
  rcases hxy with hxy | ⟨hxa,hby⟩ | ⟨hxb,hay⟩
  · exact (he.2.2 ⟨y,hy,hxy⟩).elim
  · exact ⟨a,b,hab,hxa,fun hxb => he.2.2 ⟨y,hy,hxb.trans hby⟩,y,hy,hby⟩
  · exact ⟨b,a,hab.trans (Sym2.eq_swap ..),hxb,
      fun hxa => he.2.2 ⟨y,hy,hxa.trans hay⟩,y,hy,hay⟩


theorem conn_delete_internal_of_outside (G : BondGraph V E) (ω : Set E) (x : V)
    {f : E} {a b : V} (hf : f ∈ internalEdges G (cluster G ω x))
    (ha : a ∉ cluster G ω x) (hab : Conn G ω a b) : Conn G (ω \ {f}) a b := by
  apply conn_mono G _ (conn_restrict_cluster_compl G ω x ha hab)
  intro e he
  refine ⟨he.1,?_⟩
  intro hef
  have hef' : e = f := Set.mem_singleton_iff.mp hef
  subst e
  obtain ⟨u,v,heq⟩ : ∃ u v, G f = s(u,v) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G f)
    exact ⟨a,b,h.symm⟩
  exact ((mem_internalEdges_of_ends G _ f u v heq).mp he.2).1
    ((mem_internalEdges_of_ends G _ f u v heq).mp hf).1

 
theorem pivotal_other_sides (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    {e f : E} (_he : OpenMarkedPivotal G ω m x e)
    (hf : OpenMarkedPivotal G ω m x f) (hne : f ≠ e) :
    f ∈ internalEdges G (cluster G (ω \ {e}) x) ∨
      f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ := by
  obtain ⟨a,b,hab⟩ : ∃ a b, G f = s(a,b) := by
    obtain ⟨⟨a,b⟩,h⟩ := Quot.exists_rep (G f)
    exact ⟨a,b,h.symm⟩
  have hop : f ∈ ω \ {e} := ⟨hf.1,hne⟩
  have hiff := edge_cluster_sides G (ω \ {e}) x hop hab
  by_cases ha : a ∈ cluster G (ω \ {e}) x
  · exact Or.inl ((mem_internalEdges_of_ends G _ f a b hab).mpr ⟨ha,hiff.mp ha⟩)
  · exact Or.inr ((mem_internalEdges_of_ends G _ f a b hab).mpr ⟨ha,fun hb => ha (hiff.mpr hb)⟩)

 
theorem conn_delete_exterior_of_inside (G : BondGraph V E) (ω : Set E) (x : V)
    {f : E} {a b : V} (hf : f ∈ internalEdges G (cluster G ω x)ᶜ)
    (ha : a ∈ cluster G ω x) (hab : Conn G ω a b) : Conn G (ω \ {f}) a b := by
  apply conn_mono G _ (conn_restrict_cluster G ω x ha hab)
  intro e he
  refine ⟨he.1,?_⟩
  intro hef
  have hef' : e = f := Set.mem_singleton_iff.mp hef
  subst e
  obtain ⟨⟨u,v⟩,heq⟩ := Quot.exists_rep (G f)
  exact ((mem_internalEdges_of_ends G _ f u v heq.symm).mp hf).1
    ((mem_internalEdges_of_ends G _ f u v heq.symm).mp he.2).1

 
theorem pivotal_rootSide_ssubset (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    {e f : E} (he : OpenMarkedPivotal G ω m x e) (hne : e ≠ f)
    (hf : f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ) :
    cluster G (ω \ {e}) x ⊂ cluster G (ω \ {f}) x := by
  have hsub : cluster G (ω \ {e}) x ⊆ cluster G (ω \ {f}) x := by
    intro y hy
    exact conn_mono G (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_exterior_of_inside G (ω \ {e}) x hf (conn_refl G _ x) hy)
  refine ⟨hsub,?_⟩
  obtain ⟨a,b,hab,hxa,hxb,_⟩ := openMarkedPivotal_oriented G ω m x he
  intro hback
  apply hxb
  apply hback
  exact (hsub hxa).tail ⟨e,⟨he.1,hne⟩,hab⟩

 
theorem pivotal_rootSides_nested (G : BondGraph V E) (ω : Set E) (m : Set V) (x : V)
    {e f : E} (he : OpenMarkedPivotal G ω m x e)
    (hf : OpenMarkedPivotal G ω m x f) (hne : e ≠ f) :
    cluster G (ω \ {e}) x ⊂ cluster G (ω \ {f}) x ∨
      cluster G (ω \ {f}) x ⊂ cluster G (ω \ {e}) x := by
  rcases pivotal_other_sides G ω m x he hf hne.symm with hinside | houtside
  · obtain ⟨a,b,hab,_,hxb,hbm⟩ := openMarkedPivotal_oriented G ω m x he
    obtain ⟨y,hy,hby⟩ := hbm
    have hby' : Conn G (ω \ {f}) b y := conn_mono G (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_internal_of_outside G (ω \ {e}) x hinside hxb hby)
    have hb : b ∉ cluster G (ω \ {f}) x := fun h => hf.2.2 ⟨y,hy,h.trans hby'⟩
    have ha : a ∉ cluster G (ω \ {f}) x := fun h =>
      hb ((edge_cluster_sides G (ω \ {f}) x ⟨he.1,hne⟩ hab).mp h)
    exact Or.inr (pivotal_rootSide_ssubset G ω m x hf hne.symm
      ((mem_internalEdges_of_ends G _ e a b hab).mpr ⟨ha,hb⟩))
  · exact Or.inl (pivotal_rootSide_ssubset G ω m x he hne houtside)

 
theorem conn_restrict_cluster_compl_of_subset (G : BondGraph V E) (ω : Set E) (x : V)
    {η : Set E} (hη : η ⊆ ω) {a b : V} (ha : a ∉ cluster G ω x)
    (hab : Conn G η a b) : Conn G (η ∩ internalEdges G (cluster G ω x)ᶜ) a b := by
  induction hab with
  | refl => exact conn_refl G _ a
  | @tail u v hau huv ih =>
    obtain ⟨e,he,heq⟩ := huv
    have hu : u ∉ cluster G ω x := fun h => ha (h.trans (conn_symm G ω (conn_mono G hη hau)))
    have hv : v ∉ cluster G ω x := fun h => hu ((edge_cluster_sides G ω x (hη he) heq).mpr h)
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e u v heq).mpr ⟨hu,hv⟩⟩,heq⟩



theorem cluster_finite_of_finite_edges (G : BondGraph V E) {ω : Set E}
    (hω : ω.Finite) (x : V) : (cluster G ω x).Finite := by
  let F : Finset V := insert x (hω.toFinset.biUnion fun e => (G e).toFinset)
  apply F.finite_toSet.subset
  intro y hxy
  induction hxy with
  | refl => exact Finset.mem_insert_self x _
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    exact ⟨e,hω.mem_toFinset.mpr he,by simp [heq]⟩

 
noncomputable def pivotalRank (G : BondGraph V E) (ω : Set E) (x : V) (e : E) : ℕ :=
  (cluster G (ω \ {e}) x).ncard

end PivotalGeometry

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recursive marked moments and exponential estimates. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section MarkedRecursion
attribute [local instance] Classical.propDecidable Classical.decEq


@[simp] theorem mem_markedOpenPivotals (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (m : Finset V) (e : E) :
    e ∈ markedOpenPivotals G Q x ω m ↔ e ∈ Q ∧ OpenMarkedPivotal G ω m x e := by
  simp only [markedOpenPivotals,Finset.mem_filter,OpenMarkedPivotal,MarkedEvent,Finset.coe_erase,
    Finset.mem_coe]

 
noncomputable def markedMomentValue (G : BondGraph V E) (Q : Finset E) (x : V)
    (i : ℕ) (ω : Finset E) (m : Finset V) : ℝ :=
  if MarkedEvent G ω m x then ((markedOpenPivotals G Q x ω m).card.choose i : ℝ) else 0


@[simp] theorem markedMomentValue_zero (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (m : Finset V) :
    markedMomentValue G Q x 0 ω m = if MarkedEvent G ω m x then 1 else 0 := by
  simp only [markedMomentValue,Nat.choose_zero_right,Nat.cast_one]

@[simp] theorem markedMomentValue_one (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (m : Finset V) :
    markedMomentValue G Q x 1 ω m = ((markedOpenPivotals G Q x ω m).card : ℝ) := by
  by_cases h : MarkedEvent G ω m x
  · simp [markedMomentValue,h]
  · have he : markedOpenPivotals G Q x ω m = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact h ((mem_markedOpenPivotals G Q x ω m e).mp he).2.2.1
    simp [markedMomentValue,h,he]


noncomputable def exteriorBonds (G : BondGraph V E) (Q : Finset E) (W : Set V) : Finset E :=
  Q.filter fun e => e ∈ internalEdges G Wᶜ

noncomputable def exteriorMarks (m : Finset V) (W : Set V) : Finset V :=
  m.filter fun x => x ∉ W

@[simp] theorem coe_exteriorBonds (G : BondGraph V E) (Q : Finset E) (W : Set V) :
    (exteriorBonds G Q W : Set E) = (Q : Set E) ∩ internalEdges G Wᶜ := by
  ext e; simp [exteriorBonds]

@[simp] theorem coe_exteriorMarks (m : Finset V) (W : Set V) :
    (exteriorMarks m W : Set V) = (m : Set V) ∩ Wᶜ := by
  ext x; simp [exteriorMarks]


end MarkedRecursion

section PointwiseRecursion
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

noncomputable def finiteRootComponent (G : BondGraph V E) (ω : Finset E) (x : V) : Finset V :=
  (cluster_finite_of_finite_edges G ω.finite_toSet x).toFinset

omit [Nonempty V] in
@[simp]
theorem coe_finiteRootComponent (G : BondGraph V E) (ω : Finset E) (x : V) :
    (finiteRootComponent G ω x : Set V) = cluster G ω x := by simp [finiteRootComponent]

end PointwiseRecursion

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_Goodness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pruning, finite and infinite goodness events and uniform bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteCappedRadius
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def pairOpenPivotals (G : BondGraph V E) (Q : Finset E) (x y : V)
    (ω : Finset E) : Finset E :=
  Q.filter fun e => e ∈ ω ∧ Conn G (ω : Set E) x y ∧ ¬Conn G (ω.erase e : Set E) x y

 
def CappedRadiusEvent (G : BondGraph V E) (Q : Finset E) (x : V) (M r : ℕ)
    (ω : Finset E) : Prop :=
  (finiteRootComponent G ω x).card ≤ M ∧
    ∃ y, Conn G (ω : Set E) x y ∧ r ≤ (pairOpenPivotals G Q x y ω).card

end FiniteCappedRadius

section PruningGeometry
attribute [local instance] Classical.propDecidable Classical.decEq


noncomputable def internalBonds (G : BondGraph V E) (ω : Finset E) (W : Set V) : Finset E :=
  ω.filter fun e => e ∈ internalEdges G W

@[simp] theorem coe_internalBonds (G : BondGraph V E) (ω : Finset E) (W : Set V) :
    (internalBonds G ω W : Set E) = (ω : Set E) ∩ internalEdges G W := by
  ext e; simp [internalBonds]


end PruningGeometry

section GoodnessGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] theorem mem_pairOpenPivotals (G : BondGraph V E) (Q : Finset E) (x y : V)
    (ω : Finset E) (e : E) : e ∈ pairOpenPivotals G Q x y ω ↔
      e ∈ Q ∧ OpenMarkedPivotal G (ω : Set E) {y} x e := by
  simp only [pairOpenPivotals,Finset.mem_filter,OpenMarkedPivotal,MarkedEvent,
    Set.mem_singleton_iff,exists_eq_left,Finset.coe_erase,Finset.mem_coe]


noncomputable def openContacts (G : BondGraph V E) (ω : Finset E) (W : Set V) : Finset E :=
  ω.filter fun e => CutExists G W e

 
def BadPieceEvent (G : BondGraph V E) (Q : Finset E) (x : V) (M K : ℕ) (L : ℝ)
    (ω : Finset E) : Prop :=
  (finiteRootComponent G ω x).card ≤ M ∧ ∃ W : Finset V,
    W ⊆ finiteRootComponent G ω x ∧
    (∀ a ∈ W, ∀ b ∈ W, Conn G (internalBonds G ω (W : Set V) : Set E) a b) ∧
    (openContacts G ω (W : Set V)).card = K ∧
    ∃ a ∈ W, ∃ b ∈ W, (K:ℝ)*L < (pairOpenPivotals G Q a b (internalBonds G ω (W : Set V))).card


noncomputable def incidentBonds (G : BondGraph V E) (Q : Finset E) (W : Finset V) : Finset E :=
  W.biUnion fun v => Q.filter fun e => v ∈ G e

@[simp] theorem mem_incidentBonds (G : BondGraph V E) (Q : Finset E) (W : Finset V) (e : E) :
    e ∈ incidentBonds G Q W ↔ e ∈ Q ∧ ∃ v ∈ W, v ∈ G e := by
  simp only [incidentBonds,Finset.mem_biUnion,Finset.mem_filter]
  aesop

end GoodnessGeometry

section FiniteInverseCost
attribute [local instance] Classical.propDecidable Classical.decEq

 
def bernoulliWeight (Q ω : Finset E) (p : ℝ) : ℝ :=
  p^ω.card*(1-p)^(Q.card-ω.card)

theorem bernoulliWeight_nonneg (Q ω : Finset E) (p : unitInterval) :
    0 ≤ bernoulliWeight Q ω p := mul_nonneg (pow_nonneg p.2.1 _) (pow_nonneg (sub_nonneg.mpr p.2.2) _)


end FiniteInverseCost

section FiniteGoodnessProbability
attribute [local instance] Classical.propDecidable Classical.decEq



def FiniteGoodForScale (G : BondGraph V E) (Q : Finset E) (x : V) (L : ℝ) (ω : Finset E) : Prop :=
  ∀ W : Finset V, W ⊆ finiteRootComponent G ω x →
    (∀ a ∈ W, ∀ b ∈ W, Conn G (internalBonds G ω (W : Set V) : Set E) a b) →
    0 < (openContacts G ω (W : Set V)).card →
    ∀ a ∈ W, ∀ b ∈ W,
      (pairOpenPivotals G Q a b (internalBonds G ω (W : Set V))).card ≤
        ((openContacts G ω (W : Set V)).card:ℝ)*L

def CappedBadGoodnessEvent (G : BondGraph V E) (Q : Finset E) (x : V) (M : ℕ) (L : ℝ)
    (ω : Finset E) : Prop :=
  (finiteRootComponent G ω x).card ≤ M ∧ ¬FiniteGoodForScale G Q x L ω

end FiniteGoodnessProbability

section ClusterLocality
attribute [local instance] Classical.propDecidable Classical.decEq

theorem reachBall_le_step (G : BondGraph V E) (x : V) (n : ℕ) :
    reachBall G x n ⊆ reachBall G x (n+1) := fun _ h => Or.inl h

theorem reachBall_mono_local (G : BondGraph V E) (x : V) : Monotone (reachBall G x) :=
  monotone_nat_of_le_succ (reachBall_le_step G x)

theorem walk_mem_reachBall (G : BondGraph V E) (ω : Set E) {a b x : V}
    (w : (openSimpleGraph G ω).Walk a b) (n : ℕ) (ha : a ∈ reachBall G x n) :
    b ∈ reachBall G x (n+w.length) := by
  induction w generalizing n with
  | nil => simpa using ha
  | @cons a z b hz w ih =>
    have hz' : z ∈ reachBall G x (n+1) := by
      apply Or.inr
      simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
      obtain ⟨e,he,hend⟩ := hz.2
      exact ⟨a,ha,e,hend⟩
    simpa only [SimpleGraph.Walk.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      using ih (n+1) hz'

 
theorem finite_cluster_subset_reachBall (G : BondGraph V E) (ω : Set E) (x : V)
    (hfin : (cluster G ω x).Finite) (M : ℕ) (hM : (cluster G ω x).ncard ≤ M) :
    cluster G ω x ⊆ reachBall G x M := by
  intro y hy
  obtain ⟨w⟩ := (conn_iff_reachable G ω x y).mp hy
  let q := w.toPath
  have hs : q.val.support.toFinset ⊆ hfin.toFinset := by
    intro z hz
    have hz' : z ∈ q.val.support := List.mem_toFinset.mp hz
    exact hfin.mem_toFinset.mpr ((conn_iff_reachable G ω x z).mpr ⟨q.val.takeUntil z hz'⟩)
  have hc : q.val.length+1 ≤ (cluster G ω x).ncard := by
    have hc := Finset.card_le_card hs
    rwa [List.toFinset_card_of_nodup q.property.support_nodup,
      SimpleGraph.Walk.length_support,← Set.ncard_eq_toFinset_card _ hfin] at hc
  have hr := walk_mem_reachBall G ω q.val 0 (Set.mem_singleton x)
  simp only [Nat.zero_add] at hr
  exact reachBall_mono_local G x (by omega) hr

 

theorem cluster_restrict_incident_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (ω : Set E) (x : V)
    (hsub : cluster G (ω ∩ (incidentSupport G hloc Λ : Set E)) x ⊆ Λ) :
    cluster G (ω ∩ (incidentSupport G hloc Λ : Set E)) x = cluster G ω x := by
  apply Set.Subset.antisymm
  · exact fun _ h => conn_mono G Set.inter_subset_left h
  · intro y hy
    induction hy with
    | refl => exact conn_refl G _ x
    | @tail a b _ hab ih =>
      obtain ⟨e,he,hend⟩ := hab
      have heQ : e ∈ incidentSupport G hloc Λ :=
        (mem_incidentSupport G hloc Λ e).mpr ⟨a,hsub ih,by simp [hend]⟩
      exact ih.tail ⟨e,⟨he,heQ⟩,hend⟩

theorem cluster_restrict_incident_of_full (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (ω : Set E) (x : V) (hsub : cluster G ω x ⊆ Λ) :
    cluster G (ω ∩ (incidentSupport G hloc Λ : Set E)) x = cluster G ω x := by
  apply cluster_restrict_incident_eq G hloc Λ ω x
  exact (fun _ h => hsub (conn_mono G Set.inter_subset_left h))

 
theorem capped_cluster_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (ω : Set E) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    ((cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M) ↔
      ((cluster G (ω ∩ (Q : Set E)) x).Finite ∧
        (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ M) := by
  dsimp only
  let Λ := (finite_reachBall hloc x M).toFinset
  let Q := incidentSupport G hloc Λ
  constructor
  · rintro ⟨hfin,hcap⟩
    have hsub : cluster G ω x ⊆ Λ := by
      simpa only [Λ,Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hfin M hcap
    rw [cluster_restrict_incident_of_full G hloc Λ ω x hsub]
    exact ⟨hfin,hcap⟩
  · rintro ⟨hfin,hcap⟩
    have hsub : cluster G (ω ∩ (Q : Set E)) x ⊆ Λ := by
      simpa only [Λ,Set.Finite.coe_toFinset] using
        finite_cluster_subset_reachBall G (ω ∩ (Q : Set E)) x hfin M hcap
    have heq := cluster_restrict_incident_eq G hloc Λ ω x hsub
    rw [heq] at hfin hcap
    exact ⟨hfin,hcap⟩

end ClusterLocality

section InfiniteGoodness
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def pivotalDistance (G : BondGraph V E) (ω : Set E) (a b : V) : ℕ :=
  {e | OpenMarkedPivotal G ω {b} a e}.ncard

 
def contactSet (G : BondGraph V E) (ω : Set E) (W : Set V) : Set E :=
  {e | e ∈ ω ∧ CutExists G W e}

 
def GoodForScale (G : BondGraph V E) (ω : Set E) (x : V) (L : ℝ) : Prop :=
  ∀ W : Finset V, (W : Set V) ⊆ cluster G ω x →
    (∀ a ∈ W, ∀ b ∈ W, Conn G (ω ∩ internalEdges G (W : Set V)) a b) →
    0 < (contactSet G ω (W : Set V)).ncard →
    ∀ a ∈ W, ∀ b ∈ W,
      (pivotalDistance G (ω ∩ internalEdges G (W : Set V)) a b : ℝ) ≤
        (contactSet G ω (W : Set V)).ncard*L

 
def CappedBadGoodness (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) (L : ℝ) : Prop :=
  (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M ∧ ¬GoodForScale G ω x L


theorem internal_config_eq_of_incident (G : BondGraph V E) (ω η : Set E) (C W : Set V)
    (hW : W ⊆ C) (he : ∀ e, (∃ v ∈ C, v ∈ G e) → (e ∈ ω ↔ e ∈ η)) :
    ω ∩ internalEdges G W = η ∩ internalEdges G W := by
  ext e
  by_cases hi : e ∈ internalEdges G W
  · have hinc : ∃ v ∈ C, v ∈ G e :=
      ⟨(G e).out.1,hW (hi _ (Sym2.out_fst_mem _)),Sym2.out_fst_mem _⟩
    simp only [Set.mem_inter_iff,hi,and_true,he e hinc]
  · simp only [Set.mem_inter_iff,hi,and_false]

theorem contacts_eq_of_incident (G : BondGraph V E) (ω η : Set E) (C W : Set V)
    (hW : W ⊆ C) (he : ∀ e, (∃ v ∈ C, v ∈ G e) → (e ∈ ω ↔ e ∈ η)) :
    contactSet G ω W = contactSet G η W := by
  ext e
  by_cases hi : CutExists G W e
  · obtain ⟨a,b,hab,ha,_⟩ := hi
    have hinc : ∃ v ∈ C, v ∈ G e := ⟨a,hW ha,by simp [hab]⟩
    simp only [contactSet,Set.mem_ofPred_eq,he e hinc]
  · simp only [contactSet,Set.mem_ofPred_eq,hi,and_false]

 
theorem goodForScale_congr (G : BondGraph V E) (ω η : Set E) (x : V) (L : ℝ)
    (hC : cluster G ω x = cluster G η x)
    (he : ∀ e, (∃ v ∈ cluster G ω x, v ∈ G e) → (e ∈ ω ↔ e ∈ η)) :
    GoodForScale G ω x L ↔ GoodForScale G η x L := by
  unfold GoodForScale
  apply forall_congr'
  intro W
  rw [← hC]
  apply forall_congr'
  intro hW
  rw [internal_config_eq_of_incident G ω η _ _ hW he,contacts_eq_of_incident G ω η _ _ hW he]

theorem goodForScale_restrict_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (ω : Set E) (x : V) (L : ℝ) (hsub : cluster G ω x ⊆ Λ) :
    GoodForScale G ω x L ↔ GoodForScale G (ω ∩ (incidentSupport G hloc Λ : Set E)) x L := by
  apply goodForScale_congr G ω _ x L
    (cluster_restrict_incident_of_full G hloc Λ ω x hsub).symm
  intro e he
  obtain ⟨v,hv,hve⟩ := he
  have hQ := (mem_incidentSupport G hloc Λ e).mpr ⟨v,hsub hv,hve⟩
  simp only [Set.mem_inter_iff,Finset.mem_coe,hQ,and_true]

 
theorem cappedBadGoodness_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (M : ℕ) (L : ℝ) (ω : Set E) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    CappedBadGoodness G ω x M L ↔ CappedBadGoodness G (ω ∩ (Q : Set E)) x M L := by
  let Λ := (finite_reachBall hloc x M).toFinset
  let Q := incidentSupport G hloc Λ
  change CappedBadGoodness G ω x M L ↔ CappedBadGoodness G (ω ∩ (Q : Set E)) x M L
  have hcap := capped_cluster_local G hloc x M ω
  change ((cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M) ↔
    ((cluster G (ω ∩ (Q : Set E)) x).Finite ∧ (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ M) at hcap
  have hg : ((cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M) →
      (GoodForScale G ω x L ↔ GoodForScale G (ω ∩ (Q : Set E)) x L) := by
    rintro ⟨hfin,hM⟩
    apply goodForScale_restrict_incident G hloc Λ ω x L
    simpa only [Λ,Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hfin M hM
  constructor
  · rintro ⟨hfin,hM,hbad⟩
    exact ⟨(hcap.mp ⟨hfin,hM⟩).1,(hcap.mp ⟨hfin,hM⟩).2,fun hh => hbad ((hg ⟨hfin,hM⟩).mpr hh)⟩
  · rintro ⟨hfin,hM,hbad⟩
    have hc := hcap.mpr ⟨hfin,hM⟩
    exact ⟨hc.1,hc.2,fun hh => hbad ((hg hc).mp hh)⟩

end InfiniteGoodness

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isoperimetric energy, symmetric walks and invariant operator traces. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section IsoperimetricEnergy
attribute [local instance] Classical.propDecidable


noncomputable def neighbors (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Finset V := (finite_neighbors hloc x).toFinset

@[simp] theorem mem_neighbors (G : BondGraph V E) (hloc : LocallyFinite G) (x y : V) :
    y ∈ neighbors G hloc x ↔ Adj G x y := by simp [neighbors]

noncomputable def finiteAdjPairs (G : BondGraph V E) (K : Finset V) : Finset (V × V) :=
  (K ×ˢ K).filter (fun e => Adj G e.1 e.2)

@[simp] theorem mem_finiteAdjPairs (G : BondGraph V E) (K : Finset V) (e : V × V) :
    e ∈ finiteAdjPairs G K ↔ e.1 ∈ K ∧ e.2 ∈ K ∧ Adj G e.1 e.2 := by
  simp [finiteAdjPairs,and_assoc]

end IsoperimetricEnergy

section FiniteQuadraticForms
attribute [local instance] Classical.propDecidable

@[simp] theorem finiteEmbedding_inner_left (f : V →₀ ℂ) (g : Hilbert V) :
    inner ℂ (finiteEmbedding f) g = ∑ x ∈ f.support, star (f x) * g x := by
  simp [finiteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    lp.inner_single_left, mul_comm]

@[simp] theorem finiteEmbedding_inner_right (f : Hilbert V) (g : V →₀ ℂ) :
    inner ℂ f (finiteEmbedding g) = ∑ x ∈ g.support, star (f x) * g x := by
  simp [finiteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    lp.inner_single_right, mul_comm]

@[simp] theorem finiteEmbedding_norm_sq (f : V →₀ ℂ) :
    ‖finiteEmbedding f‖^2 = ∑ x ∈ f.support, ‖f x‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [finiteEmbedding_inner_left]
  simp only [map_sum, finiteEmbedding_apply]
  apply Finset.sum_congr rfl
  intro x _
  simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

end FiniteQuadraticForms

section InvariantOperatorTrace
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable
local instance spectralRealOperatorScalarTower :
    IsScalarTower ℝ (Hilbert V →L[ℂ] Hilbert V) (Hilbert V →L[ℂ] Hilbert V) where
  smul_assoc scalar first second := by
    ext vector vertex
    rfl
local instance spectralRealOperatorSMulCommClass :
    SMulCommClass ℝ (Hilbert V →L[ℂ] Hilbert V) (Hilbert V →L[ℂ] Hilbert V) where
  smul_comm scalar first second := by
    apply ContinuousLinearMap.ext
    intro vector
    exact (first.map_smul_of_tower scalar (second vector)).symm
noncomputable def permuteHilbert (a : V ≃ V) : Hilbert V ≃ₗᵢ[ℂ] Hilbert V where
  toFun f := ⟨fun x => f (a.symm x), by
    apply memℓp_gen
    exact a.symm.summable_iff.mpr (lp.memℓp f |>.summable (by norm_num))⟩
  invFun f := ⟨fun x => f (a x), by
    apply memℓp_gen
    exact a.summable_iff.mpr (lp.memℓp f |>.summable (by norm_num))⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact a.symm.tsum_eq (fun x => ‖f x‖ ^ (2:ℝ≥0∞).toReal)

@[simp] theorem permuteHilbert_apply (a : V ≃ V) (f : Hilbert V) (x : V) :
    permuteHilbert a f x = f (a.symm x) := rfl

@[simp] theorem permuteHilbert_single (a : V ≃ V) (x : V) (c : ℂ) :
    permuteHilbert a (lp.single 2 x c) = lp.single 2 (a x) c := by
  ext y
  simp only [permuteHilbert_apply, lp.coeFn_single]
  simp [Pi.single_apply, eq_comm, Equiv.eq_symm_apply]

noncomputable def matrixCoeff (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) : ℂ :=
  A (lp.single 2 y (1:ℂ)) x

@[simp] theorem matrixCoeff_eq_inner (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff A x y = inner ℂ (lp.single 2 x (1:ℂ)) (A (lp.single 2 y (1:ℂ))) := by
  simp [matrixCoeff,lp.inner_single_left]

@[simp] theorem matrixCoeff_adjoint (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff (star A) x y = star (matrixCoeff A y x) := by
  rw [matrixCoeff_eq_inner, matrixCoeff_eq_inner]
  change inner ℂ _ ((ContinuousLinearMap.adjoint A) _) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  simpa only [RCLike.star_def] using
    (inner_conj_symm (A (lp.single 2 x (1:ℂ))) (lp.single 2 y (1:ℂ))).symm


section RootTrace
variable {ι : Type*} [Fintype ι]
variable (root : ι → V) (weight : ι → ℝ)

noncomputable def rootTrace (A : Hilbert V →L[ℂ] Hilbert V) : ℂ :=
  ∑ i, (weight i : ℂ) * matrixCoeff A (root i) (root i)

@[simp] theorem rootTrace_add (A B : Hilbert V →L[ℂ] Hilbert V) :
    rootTrace root weight (A+B) = rootTrace root weight A + rootTrace root weight B := by
  simp [rootTrace, matrixCoeff, add_apply, mul_add, Finset.sum_add_distrib]

@[simp] theorem rootTrace_smul (c : ℂ) (A : Hilbert V →L[ℂ] Hilbert V) :
    rootTrace root weight (c • A) = c * rootTrace root weight A := by
  simp [rootTrace, matrixCoeff, smul_apply, ← Finset.mul_sum, mul_left_comm]

@[simp] theorem rootTrace_one (hw : ∑ i, weight i = 1) :
    rootTrace root weight (1 : Hilbert V →L[ℂ] Hilbert V) = 1 := by
  simpa [rootTrace, matrixCoeff, lp.coeFn_single, ← Complex.ofReal_sum] using
    congrArg (fun t : ℝ => (t : ℂ)) hw

 
def KernelInvariant (Γ : Set (V ≃ V)) (A : Hilbert V →L[ℂ] Hilbert V) : Prop :=
  ∀ a ∈ Γ, ∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y



def RootTransport (Γ : Set (V ≃ V)) : Prop :=
  ∀ m : V → V → ℂ,
    (∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y) →
    (∀ x, Summable (m x)) → (∀ y, Summable (fun x => m x y)) →
    (∑ i, (weight i : ℂ) * ∑' y, m (root i) y) =
    (∑ i, (weight i : ℂ) * ∑' x, m x (root i))

@[simp] theorem rootTrace_real_smul (c : ℝ) (A : Hilbert V →L[ℂ] Hilbert V) :
    rootTrace root weight (c • A) = (c : ℂ) * rootTrace root weight A := by
  simp [rootTrace, matrixCoeff, smul_apply, Complex.real_smul,
    ← Finset.mul_sum, mul_left_comm]

end RootTrace

end InvariantOperatorTrace

section InvariantPercolationOperators
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable


theorem twoPoint_aut [Countable V] [Countable E] (G : BondGraph V E) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (x y : V) :
    twoPoint G p (a x) (a y) = twoPoint G p x y := by
  have he : {ω | Conn G ω (a x) (a y)} =
      (fun ω => b ⁻¹' ω) ⁻¹' {ω | Conn G ω x y} := by
    ext ω
    exact (conn_aut_iff G h ω x y).symm
  unfold twoPoint
  rw [he, ← Measure.map_apply (measurable_set_preimage b)
    (measurableSet_conn G x y), law_map_preimage_equiv]

end InvariantPercolationOperators

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical parameters and the geometry, selection and traces of splices. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SpliceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 

def exchangeOn (mask ω η : Set E) : Set E := (ω \ mask) ∪ (η ∩ mask)

@[simp] theorem mem_exchangeOn {mask ω η : Set E} {e : E} :
    e ∈ exchangeOn mask ω η ↔ if e ∈ mask then e ∈ η else e ∈ ω := by
  by_cases h : e ∈ mask <;> simp [exchangeOn,h]

theorem exchangeOn_involutive (mask ω η : Set E) :
    exchangeOn mask (exchangeOn mask ω η) (exchangeOn mask η ω) = ω := by
  ext e
  by_cases h : e ∈ mask <;> simp [h]

 

def spliceMask (G : BondGraph V E) (S B : Set V) (e : E) : Set E :=
  insert e {f | (∃ b ∈ B, b ∈ G f) ∧ f ∈ internalEdges G Sᶜ}

def spliceField (G : BondGraph V E) (S B : Set V) (e : E) (ω η : Set E) : Set E :=
  exchangeOn (spliceMask G S B e) ω η

theorem slit_cluster_subset (G : BondGraph V E) (S : Set V) (η : Set E)
    (y : V) (hy : y ∉ S) : cluster G (η ∩ internalEdges G Sᶜ) y ⊆ Sᶜ := by
  exact fun z hz => conn_internal_endpoint G Sᶜ hy hz

theorem spliceMask_not_internal (G : BondGraph V E) (S B : Set V) (e : E)
    (a b : V) (he : G e = s(a,b)) (hb : b ∉ S) {f : E}
    (hf : f ∈ internalEdges G S) : f ∉ spliceMask G S B e := by
  rintro (rfl | ⟨_,hout⟩)
  · exact hb (((mem_internalEdges_of_ends G S f a b he).mp hf).2)
  · exact (hout _ (Sym2.out_fst_mem _)) (hf _ (Sym2.out_fst_mem _))

theorem spliceMask_of_internal_piece (G : BondGraph V E) (S B : Set V) (e : E)
    (hB : B ⊆ Sᶜ) {f : E} (hf : f ∈ internalEdges G B) : f ∈ spliceMask G S B e := by
  right
  exact ⟨⟨(G f).out.1,hf _ (Sym2.out_fst_mem _),Sym2.out_fst_mem _⟩,
    fun v hv => hB (hf v hv)⟩

 
theorem splice_internal_fields (G : BondGraph V E) (S B : Set V) (e : E)
    (ω η : Set E) (a b : V) (he : G e = s(a,b)) (hb : b ∉ S) (hB : B ⊆ Sᶜ) :
    spliceField G S B e ω η ∩ internalEdges G S = ω ∩ internalEdges G S ∧
    spliceField G S B e ω η ∩ internalEdges G B = η ∩ internalEdges G B := by
  constructor
  · ext f
    by_cases hf : f ∈ internalEdges G S
    · simp only [Set.mem_inter_iff,hf,and_true,spliceField,mem_exchangeOn,
        ite_eq_right (spliceMask_not_internal G S B e a b he hb hf)]
    · simp only [Set.mem_inter_iff,hf,and_false]
  · ext f
    by_cases hf : f ∈ internalEdges G B
    · simp only [Set.mem_inter_iff,hf,and_true,spliceField,mem_exchangeOn,
        ite_eq_left (spliceMask_of_internal_piece G S B e hB hf)]
    · simp only [Set.mem_inter_iff,hf,and_false]

 
theorem splice_crossing_unique (G : BondGraph V E) (ω η : Set E) (x : V)
    (B : Set V) (e : E) {f : E} {a b : V}
    (hf : f ∈ spliceField G (cluster G ω x) B e ω η)
    (hab : G f = s(a,b)) (ha : a ∈ cluster G ω x) (hb : b ∉ cluster G ω x) : f = e := by
  have hno : f ∉ ω := fun h => hb ((edge_cluster_sides G ω x h hab).mp ha)
  have hm : f ∈ spliceMask G (cluster G ω x) B e := by
    by_contra h
    have hh := hf
    simp only [spliceField,mem_exchangeOn,ite_eq_right h] at hh
    exact hno hh
  rcases hm with rfl | ⟨_,hout⟩
  · rfl
  · exact ((((mem_internalEdges_of_ends G _ f a b hab).mp hout).1) ha).elim

 

theorem splice_cluster (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    cluster G (spliceField G S B e ω η) x = S ∪ B := by
  let S := cluster G ω x
  let ζ := η ∩ internalEdges G Sᶜ
  let B := cluster G ζ y
  let ω' := spliceField G S B e ω η
  change cluster G ω' x = S ∪ B
  have hB : B ⊆ Sᶜ := slit_cluster_subset G S η y hy
  have hbS : b ∉ S := hB hb
  have hfields := splice_internal_fields G S B e ω η a b he hbS hB
  have he' : e ∈ ω' := by
    change e ∈ exchangeOn (spliceMask G S B e) ω η
    rw [mem_exchangeOn,ite_eq_left (show e ∈ spliceMask G S B e from Set.mem_insert _ _)]
    exact heη
  have hSconn (z : V) (hz : z ∈ S) : Conn G ω' x z := by
    have h := conn_restrict_cluster G ω x (mem_cluster_self G ω x) hz
    apply conn_mono G _ h
    intro f hf
    exact (hfields.1.symm ▸ hf).1
  have hBconn (u v : V) (hu : u ∈ B) (hv : v ∈ B) : Conn G ω' u v := by
    have h := conn_restrict_cluster G ζ y hu (conn_trans G ζ (conn_symm G ζ hu) hv)
    apply conn_mono G _ h
    intro f hf
    exact (hfields.2.symm ▸ (show f ∈ η ∩ internalEdges G B from ⟨hf.1.1,hf.2⟩)).1
  apply Set.Subset.antisymm
  · intro z hz
    induction hz with
    | refl => exact Or.inl (mem_cluster_self G ω x)
    | @tail u v hxu huv ih =>
      obtain ⟨f,hf,hfv⟩ := huv
      by_cases hvS : v ∈ S
      · exact Or.inl hvS
      · rcases ih with huS | huB
        · have hfe := splice_crossing_unique G ω η x B e hf hfv huS hvS
          subst f
          have hends := Sym2.eq_iff.mp (he.symm.trans hfv)
          rcases hends with ⟨hau,hbv⟩ | ⟨hav,hbu⟩
          · exact Or.inr (hbv ▸ hb)
          · exact (hvS (hav ▸ ha)).elim
        · have huS : u ∉ S := hB huB
          have hm : f ∈ spliceMask G S B e := by
            right
            exact ⟨⟨u,huB,by simp [hfv]⟩,(mem_internalEdges_of_ends G _ f u v hfv).mpr ⟨huS,hvS⟩⟩
          have hfη : f ∈ η := by
            change f ∈ exchangeOn (spliceMask G S B e) ω η at hf
            rwa [mem_exchangeOn,ite_eq_left hm] at hf
          exact Or.inr ((edge_cluster_sides G ζ y
            ⟨hfη,(mem_internalEdges_of_ends G _ f u v hfv).mpr ⟨huS,hvS⟩⟩ hfv).mp huB)
  · intro z hz
    rcases hz with hz | hz
    · exact hSconn z hz
    · exact ((hSconn a ha).tail ⟨e,he',he⟩).trans (hBconn b z hb hz)


end SpliceGeometry

section SpliceInverse
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem splice_close_seam_cluster (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (_heη : e ∈ η) (_ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    cluster G (spliceField G S B e ω η \ {e}) x = S := by
  let S := cluster G ω x
  let B := cluster G (η ∩ internalEdges G Sᶜ) y
  let ω' := spliceField G S B e ω η
  have hB := slit_cluster_subset G S η y hy
  have hf := (splice_internal_fields G S B e ω η a b he (hB hb) hB).1
  apply Set.Subset.antisymm
  · intro v hxv
    induction hxv with
    | refl => exact mem_cluster_self G ω x
    | @tail u v _ huv ih =>
      obtain ⟨f,hf,hfv⟩ := huv
      by_contra hvS
      have hfe := splice_crossing_unique G ω η x B e hf.1 hfv ih hvS
      exact hf.2 (Set.mem_singleton_iff.mpr hfe)
  · intro z hz
    have hc := conn_restrict_cluster G ω x (mem_cluster_self G ω x) hz
    apply conn_mono G _ hc
    intro f hfin
    refine ⟨(hf.symm ▸ hfin).1,?_⟩
    intro hfe
    have hfe' := Set.mem_singleton_iff.mp hfe
    subst f
    exact hB hb (((mem_internalEdges_of_ends G S e a b he).mp hfin.2).2)

 
theorem splice_recover_piece (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    let ω' := spliceField G S B e ω η
    cluster G ω' x \ cluster G (ω' \ {e}) x = B := by
  dsimp only
  rw [splice_cluster G ω η x y hy e a b he heη ha hb,
    splice_close_seam_cluster G ω η x y hy e a b he heη ha hb]
  have hB := slit_cluster_subset G (cluster G ω x) η y hy
  ext z
  constructor
  · rintro ⟨hz,hzS⟩
    exact hz.resolve_left hzS
  · intro hz
    exact ⟨Or.inr hz,hB hz⟩

 
def recoveredMask (G : BondGraph V E) (ω' : Set E) (x : V) (e : E) : Set E :=
  spliceMask G (cluster G (ω' \ {e}) x)
    (cluster G ω' x \ cluster G (ω' \ {e}) x) e

theorem recoveredMask_splice (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hy : y ∉ cluster G ω x) (e : E) (a b : V)
    (he : G e = s(a,b)) (heη : e ∈ η) (ha : a ∈ cluster G ω x)
    (hb : b ∈ cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) :
    let S := cluster G ω x
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    recoveredMask G (spliceField G S B e ω η) x e = spliceMask G S B e := by
  unfold recoveredMask
  dsimp only
  rw [splice_recover_piece G ω η x y hy e a b he heη ha hb,
    splice_close_seam_cluster G ω η x y hy e a b he heη ha hb]


end SpliceInverse

section FiniteExchange
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def finiteExchange (M ω η : Finset E) : Finset E := (ω \ M) ∪ (η ∩ M)

@[simp] theorem coe_finiteExchange (M ω η : Finset E) :
    (finiteExchange M ω η : Set E) = exchangeOn (M:Set E) (ω:Set E) (η:Set E) := by
  simp only [finiteExchange,exchangeOn,Finset.coe_union,Finset.coe_sdiff,Finset.coe_inter]

end FiniteExchange

section SpliceSelection
attribute [local instance] Classical.propDecidable Classical.decEq



theorem cluster_eq_of_incident_agreement (G : BondGraph V E) (ω η : Set E) (x : V)
    (he : ∀ e, (∃ v ∈ cluster G ω x, v ∈ G e) → (e ∈ ω ↔ e ∈ η)) :
    cluster G η x = cluster G ω x := by
  have hforward : cluster G ω x ⊆ cluster G η x := by
    intro y hy
    induction hy with
    | refl => exact conn_refl G _ _
    | @tail a b hxa hab ih =>
      obtain ⟨e,heω,hab⟩ := hab
      exact ih.tail ⟨e,(he e ⟨a,hxa,by simp [hab]⟩).mp heω,hab⟩
  apply Set.Subset.antisymm _ hforward
  intro y hy
  induction hy with
  | refl => exact conn_refl G _ _
  | @tail a b _ hab ih =>
    obtain ⟨e,heη,hab⟩ := hab
    exact ih.tail ⟨e,(he e ⟨a,ih,by simp [hab]⟩).mpr heη,hab⟩

 

theorem spliceMask_avoids_prefix (G : BondGraph V E) (S B R : Set V) (hRS : R ⊆ S)
    (e : E) (a b : V) (hab : G e = s(a,b)) (ha : a ∉ R) (hb : b ∉ S)
    {f : E} (hf : ∃ v ∈ R, v ∈ G f) : f ∉ spliceMask G S B e := by
  rintro (rfl | ⟨_,hfo⟩)
  · obtain ⟨v,hv,hvf⟩ := hf
    rw [hab] at hvf
    rcases Sym2.mem_iff.mp hvf with rfl | rfl
    · exact ha hv
    · exact hb (hRS hv)
  · obtain ⟨v,hv,hvf⟩ := hf
    exact hfo v hvf (hRS hv)

 

theorem splice_preserves_prefix_cut (G : BondGraph V E) (ω η : Set E) (x : V)
    (B : Set V) (e f : E) (a b : V) (hab : G e = s(a,b))
    (ha : a ∉ cluster G (ω \ {f}) x) (hb : b ∉ cluster G ω x) :
    cluster G ((spliceField G (cluster G ω x) B e ω η) \ {f}) x =
      cluster G (ω \ {f}) x := by
  apply cluster_eq_of_incident_agreement
  intro g hg
  have hRS : cluster G (ω \ {f}) x ⊆ cluster G ω x := fun _ h => conn_mono G Set.sdiff_subset h
  have hno := spliceMask_avoids_prefix G _ B _ hRS e a b hab ha hb hg
  simp only [Set.mem_sdiff,spliceField,mem_exchangeOn,ite_eq_right hno]

end SpliceSelection

section SpliceTrace
attribute [local instance] Classical.propDecidable Classical.decEq

 

inductive SpliceTrace (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V) (k : ℕ) :
    ℕ → Set E → List (ℕ × E) → Set E → Prop
  | stop (j : ℕ) (ω : Set E) (hstop : y k ∈ cluster G ω x) :
      SpliceTrace G x η y k j ω [] ω
  | step (j i : ℕ) (ω : Set E) (e : E) (a b : V) (rest : List (ℕ × E)) (ωf : Set E)
      (hnot : y k ∉ cluster G ω x) (hji : j < i) (hik : i ≤ k)
      (hmax : ∀ l, i < l → l ≤ k → Disjoint (cluster G (η l) (y l)) (cluster G ω x))
      (hy : y i ∉ cluster G ω x) (he : e ∈ η i) (hab : G e = s(a,b))
      (ha : a ∈ cluster G ω x)
      (hb : b ∈ cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i))
      (htail : SpliceTrace G x η y k i
        (spliceField G (cluster G ω x)
          (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) e ω (η i)) rest ωf) :
      SpliceTrace G x η y k j ω ((i,e)::rest) ωf



theorem SpliceTrace.preserve_cut (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) (f : E)
    (havoid : ∀ l, j < l → l ≤ k →
      Disjoint (cluster G (η l) (y l)) (cluster G (ω \ {f}) x)) :
    cluster G (ωf \ {f}) x = cluster G (ω \ {f}) x := by
  induction h with
  | stop => rfl
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    have hBC : b ∈ cluster G (η i) (y i) := conn_mono G Set.inter_subset_left hb
    have haC : a ∈ cluster G (η i) (y i) := (edge_cluster_sides G (η i) (y i) he hab).mpr hBC
    have haR : a ∉ cluster G (ω \ {f}) x := fun hh => Set.disjoint_left.mp (havoid i hji hik) haC hh
    have hbS : b ∉ cluster G ω x := slit_cluster_subset G _ (η i) (y i) hy hb
    have heq := splice_preserves_prefix_cut G ω (η i) x
      (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) e f a b hab haR hbS
    rw [ih]
    · exact heq
    · intro l hil hlk
      rw [heq]
      exact havoid l (hji.trans hil) hlk

 
theorem SpliceTrace.endpoint (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) : y k ∈ cluster G ωf x := by
  induction h with
  | stop _ _ hs => exact hs
  | step => assumption

 

theorem SpliceTrace.seams_pivotal (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ q ∈ steps, OpenMarkedPivotal G ωf {y k} x q.2 := by
  induction h with
  | stop => simp
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · let S := cluster G ω x
      let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
      let ω' := spliceField G S B e ω (η i)
      have hcut : cluster G (ω' \ {e}) x = S :=
        splice_close_seam_cluster G ω (η i) x (y i) hy e a b hab he ha hb
      have hfinal : cluster G (ωf \ {e}) x = S := by
        rw [SpliceTrace.preserve_cut G x η y k i ω' ωf rest ht e]
        · exact hcut
        · intro l hil hlk
          rw [hcut]
          exact hmax l hil hlk
      have hconn := SpliceTrace.endpoint G x η y k i ω' ωf rest ht
      have hno : ¬Conn G (ωf \ {e}) x (y k) := by
        intro hc
        have : y k ∈ cluster G (ωf \ {e}) x := hc
        rw [hfinal] at this
        exact hn this
      have heω : e ∈ ωf := by
        by_contra heω
        have heq : ωf \ {e} = ωf := by
          ext f
          constructor
          · exact fun hh => hh.1
          · intro hh
            exact ⟨hh,fun hfe => heω ((Set.mem_singleton_iff.mp hfe) ▸ hh)⟩
        exact hno (heq.symm ▸ hconn)
      exact ⟨heω,⟨y k,rfl,hconn⟩,by simpa only [MarkedEvent,Set.mem_singleton_iff,exists_eq_left] using hno⟩
    · exact ih q hq

end SpliceTrace

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_GapCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gap Codes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceExecution
attribute [local instance] Classical.propDecidable Classical.decEq

 

abbrev SpliceState (E : Type v) := Set E × (ℕ → Set E)

 

def exchangeState (mask : Set E) (i : ℕ) (s : SpliceState E) : SpliceState E :=
  (exchangeOn mask s.1 (s.2 i), Function.update s.2 i (exchangeOn mask (s.2 i) s.1))

@[simp] theorem exchangeState_first (mask : Set E) (i : ℕ) (s : SpliceState E) :
    (exchangeState mask i s).1 = exchangeOn mask s.1 (s.2 i) := rfl

@[simp] theorem exchangeState_at (mask : Set E) (i : ℕ) (s : SpliceState E) :
    (exchangeState mask i s).2 i = exchangeOn mask (s.2 i) s.1 := by
  simp [exchangeState]

theorem exchangeState_away (mask : Set E) (i l : ℕ) (s : SpliceState E) (hli : l ≠ i) :
    (exchangeState mask i s).2 l = s.2 l := by
  simp [exchangeState, Function.update_of_ne hli]

theorem exchangeState_involutive (mask : Set E) (i : ℕ) :
    Function.Involutive (exchangeState mask i (E := E)) := by
  intro s
  apply Prod.ext
  · simp only [exchangeState_first, exchangeState_at]
    exact exchangeOn_involutive mask s.1 (s.2 i)
  · funext l
    by_cases hli : l = i
    · subst l
      simp only [exchangeState_at, exchangeState_first]
      exact exchangeOn_involutive mask (s.2 i) s.1
    · rw [exchangeState_away _ _ _ _ hli, exchangeState_away _ _ _ _ hli]

 

def undoState (G : BondGraph V E) (x : V) (q : ℕ × E) (s : SpliceState E) :
    SpliceState E := exchangeState (recoveredMask G s.1 x q.2) q.1 s

 

def ValidSpliceStep (G : BondGraph V E) (x : V) (s : SpliceState E)
    (q : ℕ × E) (s' : SpliceState E) : Prop :=
  ∃ y a b,
    y ∉ cluster G s.1 x ∧ q.2 ∈ s.2 q.1 ∧ G q.2 = s(a,b) ∧
    a ∈ cluster G s.1 x ∧
    b ∈ cluster G (s.2 q.1 ∩ internalEdges G (cluster G s.1 x)ᶜ) y ∧
    s' = exchangeState
      (spliceMask G (cluster G s.1 x)
        (cluster G (s.2 q.1 ∩ internalEdges G (cluster G s.1 x)ᶜ) y) q.2) q.1 s

theorem undoState_of_valid (G : BondGraph V E) (x : V) (s s' : SpliceState E)
    (q : ℕ × E) (h : ValidSpliceStep G x s q s') : undoState G x q s' = s := by
  obtain ⟨y,a,b,hy,he,hab,ha,hb,rfl⟩ := h
  unfold undoState
  rw [show recoveredMask G
      (exchangeState (spliceMask G (cluster G s.1 x)
        (cluster G (s.2 q.1 ∩ internalEdges G (cluster G s.1 x)ᶜ) y) q.2) q.1 s).1 x q.2 =
      spliceMask G (cluster G s.1 x)
        (cluster G (s.2 q.1 ∩ internalEdges G (cluster G s.1 x)ᶜ) y) q.2 from
    recoveredMask_splice G s.1 (s.2 q.1) x y hy q.2 a b hab he ha hb]
  exact exchangeState_involutive _ _ s

 
inductive SpliceExecution (G : BondGraph V E) (x : V) :
    SpliceState E → List (ℕ × E) → SpliceState E → Prop
  | nil (s) : SpliceExecution G x s [] s
  | cons (s s' s'') (q qs)
      (hstep : ValidSpliceStep G x s q s')
      (hrest : SpliceExecution G x s' qs s'') : SpliceExecution G x s (q::qs) s''

 
def undoExecution (G : BondGraph V E) (x : V) :
    List (ℕ × E) → SpliceState E → SpliceState E
  | [], s => s
  | q::qs, s => undoState G x q (undoExecution G x qs s)

theorem SpliceExecution.undo (G : BondGraph V E) (x : V)
    (s s' : SpliceState E) (code : List (ℕ × E))
    (h : SpliceExecution G x s code s') : undoExecution G x code s' = s := by
  induction h with
  | nil => rfl
  | cons s s' s'' q qs hstep hrest ih =>
    change undoState G x q (undoExecution G x qs s'') = s
    rw [ih]
    exact undoState_of_valid G x s s' q hstep

 

theorem SpliceExecution.input_unique (G : BondGraph V E) (x : V)
    (s₁ s₂ out : SpliceState E) (code : List (ℕ × E))
    (h₁ : SpliceExecution G x s₁ code out) (h₂ : SpliceExecution G x s₂ code out) :
    s₁ = s₂ := by
  exact (h₁.undo G x s₁ out code).symm.trans (h₂.undo G x s₂ out code)



end SpliceExecution

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgeCode
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem pivotal_mem_trail (G : BondGraph V E) (ω : Set E) (x z : V)
    (l : List E) (hl : Along G x l z) (hopen : ∀ e ∈ l, e ∈ ω)
    {e : E} (he : OpenMarkedPivotal G ω {z} x e) : e ∈ l := by
  by_contra hnot
  apply he.2.2
  refine ⟨z,rfl,hl.conn ?_⟩
  intro f hf
  exact ⟨hopen f hf,fun hfe => hnot ((Set.mem_singleton_iff.mp hfe) ▸ hf)⟩

 
theorem finite_separatingBonds (G : BondGraph V E) (ω : Set E) (x z : V) :
    {e | OpenMarkedPivotal G ω {z} x e}.Finite := by
  by_cases hc : Conn G ω x z
  · obtain ⟨l,hl,_,ho⟩ := conn_exists_bond_trail G hc
    exact l.toFinset.finite_toSet.subset fun e he =>
      List.mem_toFinset.mpr (pivotal_mem_trail G ω x z l hl ho he)
  · have hempty : {e | OpenMarkedPivotal G ω {z} x e} = ∅ := by
      ext e
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      rintro ⟨_,⟨y,hy,hxy⟩,_⟩
      exact hc ((Set.mem_singleton_iff.mp hy) ▸ hxy)
    rw [hempty]
    exact Set.finite_empty

noncomputable def separatingBonds (G : BondGraph V E) (ω : Set E) (x z : V) : Finset E :=
  (finite_separatingBonds G ω x z).toFinset

@[simp] theorem mem_separatingBonds (G : BondGraph V E) (ω : Set E) (x z : V) (e : E) :
    e ∈ separatingBonds G ω x z ↔ OpenMarkedPivotal G ω {z} x e := by
  exact (finite_separatingBonds G ω x z).mem_toFinset

 
theorem pivotalRank_injective_of_cluster_finite (G : BondGraph V E) (ω : Set E)
    (m : Set V) (x : V) (hC : (cluster G ω x).Finite) :
    Set.InjOn (pivotalRank G ω x) {e | OpenMarkedPivotal G ω m x e} := by
  have hcut (f : E) : (cluster G (ω \ {f}) x).Finite :=
    hC.subset (fun _ h => conn_mono G Set.sdiff_subset h)
  intro e he f hf heq
  by_contra hne
  rcases pivotal_rootSides_nested G ω m x he hf hne with h | h
  · exact (Nat.ne_of_lt (Set.ncard_lt_ncard h (hcut f))) heq
  · exact (Nat.ne_of_lt (Set.ncard_lt_ncard h (hcut e))) heq.symm

 

noncomputable def bridgeIndex (G : BondGraph V E) (ω : Set E) (x z : V) (e : E) : ℕ :=
  ((separatingBonds G ω x z).filter fun f => pivotalRank G ω x f ≤ pivotalRank G ω x e).card

theorem bridgeIndex_lt_of_rank_lt (G : BondGraph V E) (ω : Set E) (x z : V) {e f : E}
    (hf : OpenMarkedPivotal G ω {z} x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f) :
    bridgeIndex G ω x z e < bridgeIndex G ω x z f := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro d hd
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1,
      (Finset.mem_filter.mp hd).2.trans (Nat.le_of_lt hlt)⟩
  · intro heq
    have hmem : f ∈ (separatingBonds G ω x z).filter
        (fun d => pivotalRank G ω x d ≤ pivotalRank G ω x f) :=
      Finset.mem_filter.mpr ⟨(mem_separatingBonds G ω x z f).mpr hf,le_refl _⟩
    rw [← heq] at hmem
    exact (Nat.not_le_of_lt hlt) (Finset.mem_filter.mp hmem).2

theorem bridgeIndex_injective (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) :
    Set.InjOn (bridgeIndex G ω x z) {e | OpenMarkedPivotal G ω {z} x e} := by
  intro e he f hf heq
  apply pivotalRank_injective_of_cluster_finite G ω {z} x hC he hf
  rcases lt_trichotomy (pivotalRank G ω x e) (pivotalRank G ω x f) with h | h | h
  · exact ((Nat.ne_of_lt (bridgeIndex_lt_of_rank_lt G ω x z hf h)) heq).elim
  · exact h
  · exact ((Nat.ne_of_lt (bridgeIndex_lt_of_rank_lt G ω x z he h)) heq.symm).elim

 
noncomputable def ordinalSpliceCode (G : BondGraph V E) (ω : Set E) (x z : V)
    (code : List (ℕ × E)) : List (ℕ × ℕ) :=
  code.map fun q => (q.1,bridgeIndex G ω x z q.2)

theorem ordinalSpliceCode_injective (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) (c₁ c₂ : List (ℕ × E))
    (h₁ : ∀ q ∈ c₁, OpenMarkedPivotal G ω {z} x q.2)
    (h₂ : ∀ q ∈ c₂, OpenMarkedPivotal G ω {z} x q.2)
    (heq : ordinalSpliceCode G ω x z c₁ = ordinalSpliceCode G ω x z c₂) : c₁ = c₂ := by
  induction c₁ generalizing c₂ with
  | nil =>
    cases c₂ with
    | nil => rfl
    | cons q qs => simp [ordinalSpliceCode] at heq
  | cons q qs ih =>
    cases c₂ with
    | nil => simp [ordinalSpliceCode] at heq
    | cons r rs =>
      have heq' := List.cons.inj heq
      have hqr : q = r := by
        apply Prod.ext
        · exact congrArg (fun t : ℕ × ℕ => t.1) heq'.1
        · exact bridgeIndex_injective G ω x z hC (h₁ q (by simp)) (h₂ r (by simp))
            (congrArg Prod.snd heq'.1)
      exact congrArg₂ List.cons hqr (ih rs
        (fun a ha => h₁ a (List.mem_cons_of_mem _ ha))
        (fun a ha => h₂ a (List.mem_cons_of_mem _ ha)) heq'.2)

 

theorem SpliceTrace.input_unique_of_ordinalCode (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j : ℕ) (ω₁ ω₂ ωf : Set E)
    (c₁ c₂ : List (ℕ × E))
    (ht₁ : SpliceTrace G x η₁ y₁ k j ω₁ c₁ ωf)
    (ht₂ : SpliceTrace G x η₂ y₂ k j ω₂ c₂ ωf)
    (hz : y₁ k = y₂ k) (hC : (cluster G ωf x).Finite)
    (heq : ordinalSpliceCode G ωf x (y₁ k) c₁ = ordinalSpliceCode G ωf x (y₁ k) c₂)
    (θf : ℕ → Set E)
    (he₁ : SpliceExecution G x (ω₁,η₁) c₁ (ωf,θf))
    (he₂ : SpliceExecution G x (ω₂,η₂) c₂ (ωf,θf)) :
    (ω₁,η₁) = (ω₂,η₂) := by
  have hc : c₁ = c₂ := ordinalSpliceCode_injective G ωf x (y₁ k) hC c₁ c₂
    (ht₁.seams_pivotal G x η₁ y₁ k j ω₁ ωf c₁)
    (by simpa only [hz] using ht₂.seams_pivotal G x η₂ y₂ k j ω₂ ωf c₂) heq
  subst c₂
  exact he₁.input_unique G x (ω₁,η₁) (ω₂,η₂) (ωf,θf) c₁ he₂

end BridgeCode

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceWeight
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def domainBits (Q : Finset E) (ω : Set E) : Finset E := Q.filter (· ∈ ω)

@[simp] theorem mem_domainBits (Q : Finset E) (ω : Set E) (e : E) :
    e ∈ domainBits Q ω ↔ e ∈ Q ∧ e ∈ ω := Finset.mem_filter

theorem domainBits_subset (Q : Finset E) (ω : Set E) : domainBits Q ω ⊆ Q :=
  Finset.filter_subset _ _

end SpliceWeight

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgeGapGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem pivotalRank_lt_iff_of_cluster_finite (G : BondGraph V E) (ω : Set E)
    (m : Set V) (x : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω m x e) (hf : OpenMarkedPivotal G ω m x f) :
    pivotalRank G ω x e < pivotalRank G ω x f ↔
      f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ := by
  have hcut (q : E) : (cluster G (ω \ {q}) x).Finite :=
    hC.subset (fun _ h => conn_mono G Set.sdiff_subset h)
  have hexterior (hout : f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ) : e ≠ f := by
    obtain ⟨a,b,hab,hxa,_,_⟩ := openMarkedPivotal_oriented G ω m x he
    intro h; subst f
    exact ((mem_internalEdges_of_ends G _ e a b hab).mp hout).1 hxa
  constructor
  · intro hlt
    have hne : e ≠ f := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
    rcases pivotal_other_sides G ω m x he hf hne.symm with hinside | hout
    · obtain ⟨a,b,hab,_,hxb,hbm⟩ := openMarkedPivotal_oriented G ω m x he
      obtain ⟨y,hy,hby⟩ := hbm
      have hby' : Conn G (ω \ {f}) b y := conn_mono G
        (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩)
        (conn_delete_internal_of_outside G (ω \ {e}) x hinside hxb hby)
      have hb : b ∉ cluster G (ω \ {f}) x := fun h => hf.2.2 ⟨y,hy,h.trans hby'⟩
      have ha : a ∉ cluster G (ω \ {f}) x := fun h =>
        hb ((edge_cluster_sides G (ω \ {f}) x ⟨he.1,hne⟩ hab).mp h)
      have hs := pivotal_rootSide_ssubset G ω m x hf hne.symm
        ((mem_internalEdges_of_ends G _ e a b hab).mpr ⟨ha,hb⟩)
      have hrev := Set.ncard_lt_ncard hs (hcut e)
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hrev) hlt).elim
    · exact hout
  · intro hout
    exact Set.ncard_lt_ncard (pivotal_rootSide_ssubset G ω m x he (hexterior hout) hout) (hcut f)

theorem pivotal_internal_of_rank_lt (G : BondGraph V E) (ω : Set E)
    (m : Set V) (x : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω m x e) (hf : OpenMarkedPivotal G ω m x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f) :
    e ∈ internalEdges G (cluster G (ω \ {f}) x) := by
  have hne : e ≠ f := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
  rcases pivotal_other_sides G ω m x hf he hne with h | h
  · exact h
  · have hr := (pivotalRank_lt_iff_of_cluster_finite G ω m x hC hf he).mpr h
    omega

 
theorem conn_far_end_avoids_later_pivotal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e g : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hg : OpenMarkedPivotal G ω {z} x g)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x g)
    (a b : V) (hab : G e = s(a,b)) (ha : Conn G (ω \ {e}) x a) :
    Conn G (ω \ {g}) x b := by
  have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC he hg).mp hlt
  have hne : e ≠ g := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
  have hc : Conn G (ω \ {g}) x a :=
    conn_mono G (ω₁ := (ω \ {e}) \ {g}) (ω₂ := ω \ {g}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_exterior_of_inside G (ω \ {e}) x hout (conn_refl G _ x) ha)
  exact hc.tail ⟨e,⟨he.1,hne⟩,hab⟩

 
theorem conn_near_end_avoids_earlier_pivotal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {f g : E}
    (hf : OpenMarkedPivotal G ω {z} x f) (hg : OpenMarkedPivotal G ω {z} x g)
    (hlt : pivotalRank G ω x g < pivotalRank G ω x f)
    (c d : V) (hcd : G f = s(c,d)) (hd : ¬Conn G (ω \ {f}) x d)
    (hdz : Conn G (ω \ {f}) d z) : Conn G (ω \ {g}) c z := by
  have hin := pivotal_internal_of_rank_lt G ω {z} x hC hg hf hlt
  have hne : f ≠ g := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h.symm)
  have hc : Conn G (ω \ {g}) d z :=
    conn_mono G (ω₁ := (ω \ {f}) \ {g}) (ω₂ := ω \ {g}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_internal_of_outside G (ω \ {f}) x hin hd hdz)
  exact (Relation.ReflTransGen.single ⟨f,⟨hf.1,hne⟩,hcd⟩).trans hc

 

theorem pivotal_between_is_internal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e f g : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {z} x f)
    (hg : OpenMarkedPivotal G ω {z} x g)
    (heg : pivotalRank G ω x e < pivotalRank G ω x g)
    (hgf : pivotalRank G ω x g < pivotalRank G ω x f)
    (a b c d : V) (hab : G e = s(a,b)) (hcd : G f = s(c,d))
    (ha : Conn G (ω \ {e}) x a) (hd : ¬Conn G (ω \ {f}) x d)
    (hdz : Conn G (ω \ {f}) d z)
    (hbc : Conn G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c) :
    OpenMarkedPivotal G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) {c} b g := by
  have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC he hg).mp heg
  have hin := pivotal_internal_of_rank_lt G ω {z} x hC hg hf hgf
  refine ⟨⟨hg.1,fun v hv => ⟨hin v hv,hout v hv⟩⟩,⟨c,rfl,hbc⟩,?_⟩
  rintro ⟨w,hw,hbw⟩
  have hbc' : Conn G (ω \ {g}) b c := by
    have hw' : w = c := Set.mem_singleton_iff.mp hw
    subst w
    apply conn_mono G ?_ hbw
    intro q hq
    exact ⟨hq.1.1,hq.2⟩
  apply hg.2.2
  exact ⟨z,rfl,(conn_far_end_avoids_later_pivotal G ω x z hC he hg heg a b hab ha).trans
    (hbc'.trans (conn_near_end_avoids_earlier_pivotal G ω x z hC hf hg hgf c d hcd hd hdz))⟩

 
theorem pivotal_after_is_internal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e g : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hg : OpenMarkedPivotal G ω {z} x g)
    (heg : pivotalRank G ω x e < pivotalRank G ω x g)
    (a b : V) (hab : G e = s(a,b)) (ha : Conn G (ω \ {e}) x a)
    (hbz : Conn G (ω ∩ internalEdges G
      (cluster G ω x \ cluster G (ω \ {e}) x)) b z) :
    OpenMarkedPivotal G (ω ∩ internalEdges G
      (cluster G ω x \ cluster G (ω \ {e}) x)) {z} b g := by
  have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC he hg).mp heg
  have hin : g ∈ internalEdges G (cluster G ω x) := by
    obtain ⟨u,v,huv,hxu,_,_⟩ := openMarkedPivotal_oriented G ω {z} x hg
    have hu : u ∈ cluster G ω x := conn_mono G Set.sdiff_subset hxu
    exact (mem_internalEdges_of_ends G _ g u v huv).mpr
      ⟨hu,(edge_cluster_sides G ω x hg.1 huv).mp hu⟩
  refine ⟨⟨hg.1,fun v hv => ⟨hin v hv,hout v hv⟩⟩,⟨z,rfl,hbz⟩,?_⟩
  rintro ⟨w,hw,hbw⟩
  have hbz' : Conn G (ω \ {g}) b z := by
    have hw' : w = z := Set.mem_singleton_iff.mp hw
    subst w
    apply conn_mono G ?_ hbw
    intro q hq
    exact ⟨hq.1.1,hq.2⟩
  exact hg.2.2 ⟨z,rfl,
    (conn_far_end_avoids_later_pivotal G ω x z hC he hg heg a b hab ha).trans hbz'⟩

end BridgeGapGeometry

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgeGapCount
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] theorem separatingBonds_card (G : BondGraph V E) (ω : Set E) (x z : V) :
    (separatingBonds G ω x z).card = pivotalDistance G ω x z := by
  exact Set.ncard_coe_finset (separatingBonds G ω x z) |>.symm.trans (by
    congr 1
    ext e
    exact mem_separatingBonds G ω x z e)

 
noncomputable def bridgeInterval (G : BondGraph V E) (ω : Set E) (x z : V) (e f : E) : Finset E :=
  (separatingBonds G ω x z).filter fun g =>
    pivotalRank G ω x e < pivotalRank G ω x g ∧ pivotalRank G ω x g < pivotalRank G ω x f

theorem bridgeIndex_interval_identity (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) {e f : E}
    (hf : OpenMarkedPivotal G ω {z} x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f) :
    bridgeIndex G ω x z f = bridgeIndex G ω x z e + (bridgeInterval G ω x z e f).card + 1 := by
  let P := separatingBonds G ω x z
  let A := P.filter fun g => pivotalRank G ω x g ≤ pivotalRank G ω x e
  let B := bridgeInterval G ω x z e f
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro g hgA hgB
    have h₁ := (Finset.mem_filter.mp hgA).2
    have h₂ := (Finset.mem_filter.mp hgB).2.1
    omega
  have hnot : f ∉ A ∪ B := by
    intro hh
    rcases Finset.mem_union.mp hh with h | h
    · have hr := (Finset.mem_filter.mp h).2
      omega
    · exact (Nat.lt_irrefl _) (Finset.mem_filter.mp h).2.2
  have hset : P.filter (fun g => pivotalRank G ω x g ≤ pivotalRank G ω x f) = insert f (A ∪ B) := by
    ext g
    constructor
    · intro hg
      obtain ⟨hgP,hgf⟩ := Finset.mem_filter.mp hg
      by_cases hge : g = f
      · exact Finset.mem_insert.mpr (Or.inl hge)
      · apply Finset.mem_insert.mpr
        apply Or.inr
        by_cases hga : pivotalRank G ω x g ≤ pivotalRank G ω x e
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgP,hga⟩)
        · apply Finset.mem_union_right
          apply Finset.mem_filter.mpr
          refine ⟨hgP,Nat.lt_of_not_ge hga,?_⟩
          apply lt_of_le_of_ne hgf
          intro hr
          exact hge (pivotalRank_injective_of_cluster_finite G ω {z} x hC
            ((mem_separatingBonds G ω x z g).mp hgP) hf hr)
    · intro hg
      rcases Finset.mem_insert.mp hg with heq | hg
      · subst g
        exact Finset.mem_filter.mpr ⟨(mem_separatingBonds G ω x z f).mpr hf,le_refl _⟩
      · rcases Finset.mem_union.mp hg with hg | hg
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,
            (Finset.mem_filter.mp hg).2.trans (Nat.le_of_lt hlt)⟩
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,
            Nat.le_of_lt (Finset.mem_filter.mp hg).2.2⟩
  change (P.filter _).card = A.card+B.card+1
  rw [hset,Finset.card_insert_of_notMem hnot,Finset.card_union_of_disjoint hdis]

theorem bridgeInterval_card_le (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {z} x f)
    (a b c d : V) (hab : G e = s(a,b)) (hcd : G f = s(c,d))
    (ha : Conn G (ω \ {e}) x a) (hd : ¬Conn G (ω \ {f}) x d)
    (hdz : Conn G (ω \ {f}) d z)
    (hbc : Conn G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c) :
    (bridgeInterval G ω x z e f).card ≤ pivotalDistance G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c := by
  rw [← separatingBonds_card]
  apply Finset.card_le_card
  intro g hg
  obtain ⟨hgP,heg,hgf⟩ := Finset.mem_filter.mp hg
  apply (mem_separatingBonds _ _ _ _ _).mpr
  exact pivotal_between_is_internal G ω x z hC he hf
    ((mem_separatingBonds G ω x z g).mp hgP) heg hgf a b c d hab hcd ha hd hdz hbc

 
theorem bridge_gap_le_internal_distance (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {z} x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f)
    (a b c d : V) (hab : G e = s(a,b)) (hcd : G f = s(c,d))
    (ha : Conn G (ω \ {e}) x a) (hd : ¬Conn G (ω \ {f}) x d)
    (hdz : Conn G (ω \ {f}) d z)
    (hbc : Conn G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c) :
    bridgeIndex G ω x z f - bridgeIndex G ω x z e ≤
      1 + pivotalDistance G (ω ∩ internalEdges G
        (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c := by
  have hid := bridgeIndex_interval_identity G ω x z hC hf hlt
  have hle := bridgeInterval_card_le G ω x z hC he hf a b c d hab hcd ha hd hdz hbc
  omega

 
theorem bridge_terminal_gap_le_internal_distance (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e : E}
    (he : OpenMarkedPivotal G ω {z} x e)
    (a b : V) (hab : G e = s(a,b)) (ha : Conn G (ω \ {e}) x a)
    (hbz : Conn G (ω ∩ internalEdges G
      (cluster G ω x \ cluster G (ω \ {e}) x)) b z) :
    (separatingBonds G ω x z).card + 1 - bridgeIndex G ω x z e ≤
      1 + pivotalDistance G (ω ∩ internalEdges G
        (cluster G ω x \ cluster G (ω \ {e}) x)) b z := by
  let P := separatingBonds G ω x z
  let A := P.filter fun g => pivotalRank G ω x g ≤ pivotalRank G ω x e
  let B := P.filter fun g => pivotalRank G ω x e < pivotalRank G ω x g
  have hid : A.card + B.card = P.card := by
    simpa only [A,B,not_le] using Finset.card_filter_add_card_filter_not
      (s := P) (fun g => pivotalRank G ω x g ≤ pivotalRank G ω x e)
  have hle : B.card ≤ pivotalDistance G (ω ∩ internalEdges G
      (cluster G ω x \ cluster G (ω \ {e}) x)) b z := by
    rw [← separatingBonds_card]
    apply Finset.card_le_card
    intro g hg
    obtain ⟨hgP,heg⟩ := Finset.mem_filter.mp hg
    apply (mem_separatingBonds _ _ _ _ _).mpr
    exact pivotal_after_is_internal G ω x z hC he
      ((mem_separatingBonds G ω x z g).mp hgP) heg a b hab ha hbz
  change P.card+1-A.card ≤ _
  omega

 
theorem pivotalDistance_le_cluster_card (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) :
    pivotalDistance G ω x z ≤ (cluster G ω x).ncard - 1 := by
  rw [← separatingBonds_card]
  let N := (cluster G ω x).ncard
  have hm : Set.MapsTo (pivotalRank G ω x) (separatingBonds G ω x z : Set E)
      (Finset.Ico 1 N : Set ℕ) := by
    intro e he
    have he' := (mem_separatingBonds G ω x z e).mp he
    have hfin : (cluster G (ω \ {e}) x).Finite :=
      hC.subset (fun _ h => conn_mono G Set.sdiff_subset h)
    have hpos : 0 < pivotalRank G ω x e :=
      (Set.ncard_pos hfin).mpr ⟨x,conn_refl G _ x⟩
    have hlt : pivotalRank G ω x e < N := by
      apply Set.ncard_lt_ncard _ hC
      refine Set.ssubset_iff_subset_ne.mpr ⟨fun v hv => conn_mono G Set.sdiff_subset hv,?_⟩
      intro heq
      obtain ⟨v,hv,hxv⟩ := he'.2.1
      apply he'.2.2
      refine ⟨v,hv,?_⟩
      change v ∈ cluster G (ω \ {e}) x
      rw [heq]
      exact hxv
    exact Finset.mem_Ico.mpr ⟨hpos,hlt⟩
  have hi : Set.InjOn (pivotalRank G ω x) (separatingBonds G ω x z : Set E) := by
    intro e he f hf h
    exact pivotalRank_injective_of_cluster_finite G ω {z} x hC
      ((mem_separatingBonds G ω x z e).mp he) ((mem_separatingBonds G ω x z f).mp hf) h
  simpa only [Nat.card_Ico,N] using Finset.card_le_card_of_injOn (pivotalRank G ω x) hm hi

 

theorem inverse_contact_weight_le (K l : ℕ) (L : ℝ) (hK : 1 ≤ K) (hl : 1 ≤ l)
    (hL : 1 ≤ L) (hgap : (l:ℝ) ≤ 1 + K*L) :
    (K:ℝ)⁻¹ ≤ min 1 (2*L/l) := by
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hlr : (1:ℝ) ≤ l := by exact_mod_cast hl
  have hKpos : (0:ℝ) < K := lt_of_lt_of_le zero_lt_one hKr
  have hlpos : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one hlr
  apply le_min
  · exact inv_le_one_of_one_le₀ hKr
  · apply (le_div_iff₀ hlpos).mpr
    apply (inv_mul_le_iff₀ hKpos).mpr
    by_cases h1 : l = 1
    · simp only [h1,Nat.cast_one]
      nlinarith
    · have h2 : (2:ℝ) ≤ l := by exact_mod_cast (show 2 ≤ l by omega)
      nlinarith

end BridgeGapCount

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgePiecePath
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem conn_restrict_cluster_of_subset (G : BondGraph V E) (ω : Set E) (x : V)
    {η : Set E} (hη : η ⊆ ω) {a b : V} (ha : a ∈ cluster G ω x)
    (hab : Conn G η a b) : Conn G (η ∩ internalEdges G (cluster G ω x)) a b := by
  induction hab with
  | refl => exact conn_refl G _ a
  | @tail u v hau huv ih =>
    obtain ⟨e,he,heq⟩ := huv
    have hu : u ∈ cluster G ω x := ha.trans (conn_mono G hη hau)
    have hv : v ∈ cluster G ω x := (edge_cluster_sides G ω x (hη he) heq).mp hu
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e u v heq).mpr ⟨hu,hv⟩⟩,heq⟩

 

theorem conn_between_pivotals_internal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {z} x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f)
    (a b c d : V) (hab : G e = s(a,b)) (hcd : G f = s(c,d))
    (ha : Conn G (ω \ {e}) x a) (hb : ¬Conn G (ω \ {e}) x b)
    (hc : Conn G (ω \ {f}) x c) :
    Conn G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c := by
  have hne : e ≠ f := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
  have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC he hf).mp hlt
  have hcnot : c ∉ cluster G (ω \ {e}) x :=
    ((mem_internalEdges_of_ends G _ f c d hcd).mp hout).1
  have hins : insert e ((ω \ {e}) \ {f}) = ω \ {f} := by
    ext q
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨⟨hq,hqe⟩,hqf⟩)
      · exact ⟨he.1,hne⟩
      · exact ⟨hq,hqf⟩
    · rintro ⟨hq,hqf⟩
      by_cases hqe : q = e
      · exact Or.inl hqe
      · exact Or.inr ⟨⟨hq,hqe⟩,hqf⟩
  have hbc : Conn G ((ω \ {e}) \ {f}) b c := by
    rw [← hins,conn_insert_iff G _ e a b x c hab] at hc
    rcases hc with h | ⟨_,h⟩ | ⟨h,_⟩
    · exact (hcnot (conn_mono G Set.sdiff_subset h)).elim
    · exact h
    · exact (hb (conn_mono G Set.sdiff_subset h)).elim
  have hbo : b ∈ cluster G (ω \ {f}) x :=
    conn_far_end_avoids_later_pivotal G ω x z hC he hf hlt a b hab ha
  have hp := conn_restrict_cluster_compl_of_subset G (ω \ {e}) x Set.sdiff_subset hb hbc
  have hp' := conn_restrict_cluster_of_subset G (ω \ {f}) x
    (η := ((ω \ {e}) \ {f}) ∩ internalEdges G (cluster G (ω \ {e}) x)ᶜ)
    (fun _ h => ⟨h.1.1.1,h.1.2⟩) hbo hp
  apply conn_mono G ?_ hp'
  intro q hq
  exact ⟨hq.1.1.1.1,fun v hv => ⟨hq.2 v hv,hq.1.2 v hv⟩⟩

 
theorem conn_after_pivotal_internal (G : BondGraph V E) (ω : Set E)
    (x z : V) {e : E} (he : OpenMarkedPivotal G ω {z} x e)
    (a b : V) (hab : G e = s(a,b)) (ha : Conn G (ω \ {e}) x a)
    (hb : ¬Conn G (ω \ {e}) x b) (hbz : Conn G (ω \ {e}) b z) :
    Conn G (ω ∩ internalEdges G (cluster G ω x \ cluster G (ω \ {e}) x)) b z := by
  have hbo : b ∈ cluster G ω x :=
    (conn_mono G Set.sdiff_subset ha).tail ⟨e,he.1,hab⟩
  have hp := conn_restrict_cluster_compl G (ω \ {e}) x hb hbz
  have hp' := conn_restrict_cluster_of_subset G ω x
    (η := (ω \ {e}) ∩ internalEdges G (cluster G (ω \ {e}) x)ᶜ)
    (fun _ h => h.1.1) hbo hp
  apply conn_mono G ?_ hp'
  intro q hq
  exact ⟨hq.1.1.1,fun v hv => ⟨hq.2 v hv,hq.1.2 v hv⟩⟩

 
theorem pivotalDistance_le_induced_card (G : BondGraph V E) (ω : Set E)
    (B : Set V) (hB : B.Finite) {a b : V} (ha : a ∈ B) :
    pivotalDistance G (ω ∩ internalEdges G B) a b ≤ B.ncard-1 := by
  have hsub : cluster G (ω ∩ internalEdges G B) a ⊆ B :=
    fun _ h => conn_internal_endpoint G B ha h
  exact (pivotalDistance_le_cluster_card G (ω ∩ internalEdges G B) a b (hB.subset hsub)).trans
    (Nat.sub_le_sub_right (Set.ncard_le_ncard hsub hB) 1)

end BridgePiecePath

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SplicePieceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem conn_after_pivotal_of_orientation (G : BondGraph V E) (ω : Set E)
    (x z : V) {e : E} (he : OpenMarkedPivotal G ω {z} x e)
    (a b : V) (hab : G e = s(a,b)) (hb : ¬Conn G (ω \ {e}) x b) :
    Conn G (ω \ {e}) b z := by
  have hins : insert e (ω \ {e}) = ω := by
    ext q
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    by_cases hqe : q = e <;> simp_all [he.1]
  obtain ⟨w,hw,hxw⟩ := he.2.1
  have hw' : w = z := Set.mem_singleton_iff.mp hw
  subst w
  rw [← hins,conn_insert_iff G _ e a b x z hab] at hxw
  rcases hxw with h | ⟨_,h⟩ | ⟨h,_⟩
  · exact (he.2.2 ⟨z,rfl,h⟩).elim
  · exact h
  · exact (hb h).elim

 
theorem SpliceTrace.internal_agreement (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ q ∈ internalEdges G (cluster G ω x), q ∈ ωf ↔ q ∈ ω := by
  induction h with
  | stop => exact fun _ _ => Iff.rfl
  | @step j i ω e a b rest ωf _ _ _ _ hy he hab ha hb ht ih =>
    intro q hq
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    have hB : B ⊆ Sᶜ := slit_cluster_subset G S (η i) (y i) hy
    have hbS : b ∉ S := hB hb
    have hqq : q ∈ internalEdges G (cluster G ω' x) := by
      rw [splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb]
      exact fun v hv => Or.inl (hq v hv)
    rw [ih q hqq]
    change q ∈ internalEdges G S at hq
    have hh := (splice_internal_fields G S B e ω (η i) a b hab hbS hB).1
    exact Iff.of_eq (show (q ∈ ω') = (q ∈ ω) from by
      have := congrArg (fun A : Set E => q ∈ A) hh
      simpa only [Set.mem_inter_iff,hq,and_true] using this)

 
theorem SpliceTrace.head_cut (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j i : ℕ) (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf) :
    cluster G (ωf \ {e}) x = cluster G ω x := by
  cases h with
  | step j i ω e a b rest ωf _ _ _ hmax hy he hab ha hb ht =>
    have hc := splice_close_seam_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    rw [SpliceTrace.preserve_cut G x η y k i _ ωf rest ht e]
    · exact hc
    · intro l hil hlk
      rw [hc]
      exact hmax l hil hlk

 
theorem contactSet_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (B : Set V) (hB : B.Finite) : (contactSet G ω B).Finite := by
  let W := hB.toFinset
  have hWB : (W : Set V) = B := hB.coe_toFinset
  apply (incidentSupport G hloc W).finite_toSet.subset
  rintro e ⟨_,a,b,hab,ha,_⟩
  apply (mem_incidentSupport G hloc W e).mpr
  refine ⟨a,?_,?_⟩
  · change a ∈ (W : Set V)
    rw [hWB]
    exact ha
  · simp [hab]

 

theorem goodForScale_piece (G : BondGraph V E) (ω : Set E) (x : V) (L : ℝ)
    (hg : GoodForScale G ω x L) (B : Set V) (hB : B.Finite)
    (hBC : B ⊆ cluster G ω x)
    (hconn : ∀ a ∈ B, ∀ b ∈ B, Conn G (ω ∩ internalEdges G B) a b)
    (hK : 0 < (contactSet G ω B).ncard) {a b : V} (ha : a ∈ B) (hb : b ∈ B) :
    (pivotalDistance G (ω ∩ internalEdges G B) a b : ℝ) ≤
      (contactSet G ω B).ncard*L := by
  let W := hB.toFinset
  have hWB : (W : Set V) = B := hB.coe_toFinset
  have hh := hg W (by simpa only [hWB] using hBC)
    (by simpa only [← Finset.mem_coe,hWB] using hconn)
    (by simpa only [hWB] using hK) a (by simpa only [← Finset.mem_coe,hWB] using ha)
    b (by simpa only [← Finset.mem_coe,hWB] using hb)
  simpa only [hWB] using hh

 
theorem slit_piece_connected (G : BondGraph V E) (η : Set E) (S : Set V) (y : V)
    (_hy : y ∉ S) :
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    ∀ a ∈ B, ∀ b ∈ B, Conn G (η ∩ internalEdges G B) a b := by
  intro B a ha b hb
  have hc := conn_restrict_cluster G (η ∩ internalEdges G Sᶜ) y ha
    (conn_trans G _ (conn_symm G _ ha) hb)
  apply conn_mono G ?_ hc
  exact fun _ h => ⟨h.1.1,h.2⟩

end SplicePieceGeometry

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceGapBound
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def traceHeadGap (G : BondGraph V E) (ωf : Set E) (x z : V)
    (e : E) (rest : List (ℕ × E)) : ℕ :=
  (match rest with
    | [] => (separatingBonds G ωf x z).card + 1
    | (_,f)::_ => bridgeIndex G ωf x z f) - bridgeIndex G ωf x z e

 

theorem SpliceTrace.head_gap_bounds (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j i M : ℕ)
    (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf)
    (hCf : (cluster G ωf x).Finite)
    (hCi : (cluster G (η i) (y i)).Finite)
    (hM : (cluster G (η i) (y i)).ncard ≤ M)
    (L : ℝ) (hgood : GoodForScale G (η i) (y i) L) :
    let B := cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)
    let K := (contactSet G (η i) B).ncard
    let l := traceHeadGap G ωf x (y k) e rest
    1 ≤ K ∧ 1 ≤ l ∧ l ≤ M ∧ (l:ℝ) ≤ 1 + K*L := by
  have hfull := h
  cases h with
  | step j i ω e a b rest ωf hn _ _ _ hy he hab ha hb ht =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    let K := (contactSet G (η i) B).ncard
    change 1 ≤ K ∧ 1 ≤ traceHeadGap G ωf x (y k) e rest ∧
      traceHeadGap G ωf x (y k) e rest ≤ M ∧
      (traceHeadGap G ωf x (y k) e rest:ℝ) ≤ 1+K*L
    have hBo : B ⊆ Sᶜ := slit_cluster_subset G S (η i) (y i) hy
    have hBC : B ⊆ cluster G (η i) (y i) := fun _ h => conn_mono G Set.inter_subset_left h
    have hB : B.Finite := hCi.subset hBC
    have hKB : (contactSet G (η i) B).Finite := contactSet_finite G hloc (η i) B hB
    have heK : e ∈ contactSet G (η i) B :=
      ⟨he,b,a,hab.trans (Sym2.eq_swap ..),hb,fun h => hBo h ha⟩
    have hK : 0 < K := (Set.ncard_pos hKB).mpr ⟨e,heK⟩
    have hBpos : 0 < B.ncard := (Set.ncard_pos hB).mpr ⟨b,hb⟩
    have hBM : B.ncard ≤ M := (Set.ncard_le_ncard hBC hCi).trans hM
    have hcluster : cluster G ω' x = S ∪ B :=
      splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    have hcut : cluster G (ωf \ {e}) x = S :=
      SpliceTrace.head_cut G x η y k j i ω ωf e rest hfull
    have hpe : OpenMarkedPivotal G ωf {y k} x e :=
      SpliceTrace.seams_pivotal G x η y k j ω ωf ((i,e)::rest) hfull (i,e) (by simp)
    have hxa : Conn G (ωf \ {e}) x a := by
      change a ∈ cluster G (ωf \ {e}) x
      rw [hcut]
      exact ha
    have hxb : ¬Conn G (ωf \ {e}) x b := by
      change b ∉ cluster G (ωf \ {e}) x
      rw [hcut]
      exact hBo hb
    have hbits : ωf ∩ internalEdges G B = η i ∩ internalEdges G B := by
      have hii := (splice_internal_fields G S B e ω (η i) a b hab (hBo hb) hBo).2
      ext q
      by_cases hq : q ∈ internalEdges G B
      · have hq' : q ∈ internalEdges G (cluster G ω' x) := by
          rw [hcluster]
          exact fun v hv => Or.inr (hq v hv)
        have hiff := SpliceTrace.internal_agreement G x η y k i ω' ωf rest ht q hq'
        have hbit := congrArg (fun A : Set E => q ∈ A) hii
        simpa only [Set.mem_inter_iff,hq,and_true,hiff] using Iff.of_eq hbit
      · simp only [Set.mem_inter_iff,hq,and_false]
    have hconn := slit_piece_connected G (η i) S (y i) hy
    have finish (l : ℕ) (c : V) (hc : c ∈ B) (hl : 1 ≤ l)
        (hg : l ≤ 1 + pivotalDistance G (ωf ∩ internalEdges G B) b c) :
        1 ≤ l ∧ l ≤ M ∧ (l:ℝ) ≤ 1+K*L := by
      rw [hbits] at hg
      have hp := pivotalDistance_le_induced_card G (η i) B hB hb (b := c)
      have hg' : (l:ℝ) ≤ 1+(pivotalDistance G (η i ∩ internalEdges G B) b c:ℝ) := by
        exact_mod_cast hg
      have hgood' := goodForScale_piece G (η i) (y i) L hgood B hB hBC hconn hK hb hc
      refine ⟨hl,by omega,?_⟩
      change (l:ℝ) ≤ 1+(contactSet G (η i) B).ncard*L
      linarith
    refine ⟨hK,?_⟩
    cases rest with
    | nil =>
      have hfω : ωf = ω' := by cases ht; rfl
      have hdiff : cluster G ωf x \ cluster G (ωf \ {e}) x = B := by
        rw [hcut,hfω,hcluster]
        ext v
        constructor
        · rintro ⟨hv,hnv⟩
          exact hv.resolve_left hnv
        · intro hv
          exact ⟨Or.inr hv,hBo hv⟩
      have hyk : y k ∈ B := by
        have hz := SpliceTrace.endpoint G x η y k j ω ωf [(i,e)] hfull
        rw [hfω,hcluster] at hz
        exact hz.resolve_left hn
      have hconnz := conn_after_pivotal_of_orientation G ωf x (y k) hpe a b hab hxb
      have hp := conn_after_pivotal_internal G ωf x (y k) hpe a b hab hxa hxb hconnz
      have hg := bridge_terminal_gap_le_internal_distance G ωf x (y k) hCf hpe a b hab hxa hp
      rw [hdiff] at hg
      apply finish _ (y k) hyk _ hg
      have hcard : bridgeIndex G ωf x (y k) e ≤ (separatingBonds G ωf x (y k)).card :=
        Finset.card_filter_le _ _
      omega
    | cons q more =>
      obtain ⟨l,f⟩ := q
      have hcutf : cluster G (ωf \ {f}) x = S ∪ B := by
        rw [SpliceTrace.head_cut G x η y k i l ω' ωf f more ht,hcluster]
      have hss : cluster G (ωf \ {e}) x ⊂ cluster G (ωf \ {f}) x := by
        rw [hcut,hcutf]
        exact Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_union_left,fun heq =>
          hBo hb (heq.symm ▸ (show b ∈ S ∪ B from Or.inr hb))⟩
      have hfFin : (cluster G (ωf \ {f}) x).Finite :=
        hCf.subset (fun _ h => conn_mono G Set.sdiff_subset h)
      have hr : pivotalRank G ωf x e < pivotalRank G ωf x f := Set.ncard_lt_ncard hss hfFin
      have hpf : OpenMarkedPivotal G ωf {y k} x f :=
        SpliceTrace.seams_pivotal G x η y k j ω ωf ((i,e)::(l,f)::more) hfull (l,f) (by simp)
      obtain ⟨c,d,hcd,hxc,hxd,hdyk⟩ := openMarkedPivotal_oriented G ωf {y k} x hpf
      have hdy : Conn G (ωf \ {f}) d (y k) := by
        simpa only [MarkedEvent,Set.mem_singleton_iff,exists_eq_left] using hdyk
      have hdiff : cluster G (ωf \ {f}) x \ cluster G (ωf \ {e}) x = B := by
        rw [hcut,hcutf]
        ext v
        constructor
        · rintro ⟨hv,hnv⟩
          exact hv.resolve_left hnv
        · intro hv
          exact ⟨Or.inr hv,hBo hv⟩
      have hc : c ∈ B := by
        have hfout := (pivotalRank_lt_iff_of_cluster_finite G ωf {y k} x hCf hpe hpf).mp hr
        have hcnot := ((mem_internalEdges_of_ends G _ f c d hcd).mp hfout).1
        rw [hcut] at hcnot
        change c ∈ cluster G (ωf \ {f}) x at hxc
        rw [hcutf] at hxc
        exact hxc.resolve_left hcnot
      have hp := conn_between_pivotals_internal G ωf x (y k) hCf hpe hpf hr
        a b c d hab hcd hxa hxb (by change c ∈ cluster G (ωf \ {f}) x; rw [hcutf]; exact Or.inr hc)
      have hg := bridge_gap_le_internal_distance G ωf x (y k) hCf hpe hpf hr
        a b c d hab hcd hxa hxd hdy hp
      rw [hdiff] at hg
      apply finish _ c hc _ hg
      have hind := bridgeIndex_interval_identity G ωf x (y k) hCf hpf hr
      omega

end SpliceGapBound

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GapCode
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem SpliceTrace.seam_data (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ q ∈ steps, j < q.1 ∧ q.1 ≤ k ∧ q.2 ∈ η q.1 ∧
      q.2 ∈ internalEdges G (cluster G (η q.1) (y q.1)) := by
  induction h with
  | stop => simp
  | @step j i ω e a b rest ωf _ hji hik _ _ he hab _ hb ht ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · have hb' : b ∈ cluster G (η i) (y i) := conn_mono G Set.inter_subset_left hb
      exact ⟨hji,hik,he,(mem_internalEdges_of_ends G _ e a b hab).mpr
        ⟨(edge_cluster_sides G (η i) (y i) he hab).mpr hb',hb'⟩⟩
    · obtain ⟨hqi,hqk,hqe,hqC⟩ := ih q hq
      exact ⟨hji.trans hqi,hqk,hqe,hqC⟩

 
theorem SpliceTrace.head_index_lt (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j i : ℕ) (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf)
    (hC : (cluster G ωf x).Finite) :
    ∀ q ∈ rest, bridgeIndex G ωf x (y k) e < bridgeIndex G ωf x (y k) q.2 := by
  have hfull := h
  have hc := SpliceTrace.head_cut G x η y k j i ω ωf e rest h
  have hseams := SpliceTrace.seams_pivotal G x η y k j ω ωf ((i,e)::rest) h
  cases h with
  | step j i ω e a b rest ωf _ _ _ hmax _ _ _ _ _ ht =>
    intro q hq
    obtain ⟨hqi,hqk,_,hqC⟩ := SpliceTrace.seam_data G x η y k i _ ωf rest ht q hq
    have hout : q.2 ∈ internalEdges G (cluster G (ωf \ {e}) x)ᶜ := by
      rw [hc]
      intro v hv hvS
      exact Set.disjoint_left.mp (hmax q.1 hqi hqk) (hqC v hv) hvS
    have hpe := hseams (i,e) (by simp)
    have hpq := hseams q (List.mem_cons_of_mem _ hq)
    exact bridgeIndex_lt_of_rank_lt G ωf x (y k) hpq
      ((pivotalRank_lt_iff_of_cluster_finite G ωf {y k} x hC hpe hpq).mpr hout)

 
noncomputable def gapSpliceCode (G : BondGraph V E) (ωf : Set E) (x z : V) :
    List (ℕ × E) → List (ℕ × ℕ)
  | [] => []
  | (i,e)::rest => (i,traceHeadGap G ωf x z e rest)::gapSpliceCode G ωf x z rest

 
def decodeGapOrdinals (N : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (i,l)::rest =>
    let decoded := decodeGapOrdinals N rest
    (i, (match decoded with | [] => N+1 | (_,r)::_ => r)-l)::decoded

 
theorem SpliceTrace.decode_gap_code (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) (hC : (cluster G ωf x).Finite) :
    decodeGapOrdinals (separatingBonds G ωf x (y k)).card
      (gapSpliceCode G ωf x (y k) steps) = ordinalSpliceCode G ωf x (y k) steps := by
  induction steps generalizing j ω with
  | nil => rfl
  | cons q rest ih =>
    obtain ⟨i,e⟩ := q
    have hlater := SpliceTrace.head_index_lt G x η y k j i ω ωf e rest h hC
    cases h with
    | step j i ω e a b rest ωf _ _ _ _ _ _ _ _ _ ht =>
      have ih' := ih i _ ht
      simp only [gapSpliceCode,decodeGapOrdinals,ih',ordinalSpliceCode,List.map_cons]
      congr 2
      cases rest with
      | nil =>
        simp only [List.map_nil,traceHeadGap]
        have hle : bridgeIndex G ωf x (y k) e ≤ (separatingBonds G ωf x (y k)).card :=
          Finset.card_filter_le _ _
        omega
      | cons q qs =>
        obtain ⟨l,f⟩ := q
        have hle := hlater (l,f) (by simp)
        change bridgeIndex G ωf x (y k) e < bridgeIndex G ωf x (y k) f at hle
        simp only [List.map_cons,traceHeadGap]
        omega

 
theorem SpliceTrace.input_unique_of_gapCode (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j : ℕ) (ω₁ ω₂ ωf : Set E)
    (c₁ c₂ : List (ℕ × E))
    (ht₁ : SpliceTrace G x η₁ y₁ k j ω₁ c₁ ωf)
    (ht₂ : SpliceTrace G x η₂ y₂ k j ω₂ c₂ ωf)
    (hz : y₁ k = y₂ k) (hC : (cluster G ωf x).Finite)
    (heq : gapSpliceCode G ωf x (y₁ k) c₁ = gapSpliceCode G ωf x (y₁ k) c₂)
    (θf : ℕ → Set E)
    (he₁ : SpliceExecution G x (ω₁,η₁) c₁ (ωf,θf))
    (he₂ : SpliceExecution G x (ω₂,η₂) c₂ (ωf,θf)) :
    (ω₁,η₁) = (ω₂,η₂) := by
  apply SpliceTrace.input_unique_of_ordinalCode G x η₁ η₂ y₁ y₂ k j ω₁ ω₂ ωf
    c₁ c₂ ht₁ ht₂ hz hC _ θf he₁ he₂
  rw [← SpliceTrace.decode_gap_code G x η₁ y₁ k j ω₁ ωf c₁ ht₁ hC,
    heq,hz,SpliceTrace.decode_gap_code G x η₂ y₂ k j ω₂ ωf c₂ ht₂ hC]

end GapCode

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section InverseCodeMass
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def gapWeight (L : ℝ) (l : ℕ) : ℝ := min 1 (2*L/l)

 
noncomputable def inverseCodeMass (M : ℕ) (L : ℝ) : ℝ :=
  1 + ∑ l ∈ Finset.Icc 1 M, gapWeight L l

 
noncomputable def gapLetterWeight (L : ℝ) (l : ℕ) : ℝ := if l = 0 then 1 else gapWeight L l

theorem gapWeight_nonneg (L : ℝ) (hL : 0 ≤ L) (l : ℕ) : 0 ≤ gapWeight L l := by
  exact le_min zero_le_one (by positivity)

theorem gapLetterWeight_nonneg (L : ℝ) (hL : 0 ≤ L) (l : ℕ) : 0 ≤ gapLetterWeight L l := by
  unfold gapLetterWeight
  split_ifs
  · exact zero_le_one
  · exact gapWeight_nonneg L hL l

theorem sum_fin_succ_eq_Icc (M : ℕ) (f : ℕ → ℝ) :
    ∑ l : Fin M, f (l.val+1) = ∑ l ∈ Finset.Icc 1 M, f l := by
  rw [Fin.sum_univ_eq_sum_range (fun l => f (l+1)) M]
  apply Finset.sum_bij (fun l _ => l+1)
  · intro l hl
    exact Finset.mem_Icc.mpr ⟨by omega,by have := Finset.mem_range.mp hl; omega⟩
  · intro l hl m hm h
    omega
  · intro l hl
    obtain ⟨h1,hM⟩ := Finset.mem_Icc.mp hl
    exact ⟨l-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intros
    rfl

theorem sum_gapLetterWeight (M : ℕ) (L : ℝ) :
    ∑ l : Fin (M+1), gapLetterWeight L l.val = inverseCodeMass M L := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,gapLetterWeight,Fin.val_succ,Nat.add_eq_zero_iff,
    Nat.one_ne_zero,and_false,ite_false]
  exact congrArg (1+·) (sum_fin_succ_eq_Icc M (gapWeight L))

 

theorem total_gap_code_mass (k M : ℕ) (L : ℝ) :
    ∑ c : Fin k → Fin (M+1), ∏ i : Fin k, gapLetterWeight L (c i).val =
      inverseCodeMass M L ^ k := by
  rw [← Fintype.prod_sum (fun (_ : Fin k) (l : Fin (M+1)) => gapLetterWeight L l.val)]
  simp only [sum_gapLetterWeight,Finset.prod_const,Finset.card_univ,Fintype.card_fin]


def contactInterval (K a : ℕ) : Set unitInterval :=
  {u | (a:ℝ)/K ≤ (u:ℝ) ∧ (u:ℝ) < (a+1:ℕ)/K}

end InverseCodeMass

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_Replay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replay for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SparseGapCode
attribute [local instance] Classical.propDecidable Classical.decEq

 

def ValidSparseGapCode (k M : ℕ) (c : List (ℕ × ℕ)) : Prop :=
  c.Pairwise (fun q r => q.1 < r.1) ∧
    ∀ q ∈ c, 1 ≤ q.1 ∧ q.1 ≤ k ∧ 1 ≤ q.2 ∧ q.2 ≤ M

def sparseGapValue : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (j,l)::c, i => if i = j then l else sparseGapValue c i

theorem sparseGapValue_zero (c : List (ℕ × ℕ)) (i : ℕ)
    (h : ∀ q ∈ c, i ≠ q.1) : sparseGapValue c i = 0 := by
  induction c with
  | nil => rfl
  | cons q c ih =>
    obtain ⟨j,l⟩ := q
    rw [sparseGapValue,ite_eq_right (h (j,l) (by simp))]
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem sparseGapValue_bound (k M : ℕ) (c : List (ℕ × ℕ))
    (h : ValidSparseGapCode k M c) (i : ℕ) : sparseGapValue c i ≤ M := by
  induction c with
  | nil => exact Nat.zero_le _
  | cons q c ih =>
    obtain ⟨j,l⟩ := q
    rw [sparseGapValue]
    split_ifs
    · exact (h.2 (j,l) (by simp)).2.2.2
    · exact ih ⟨(List.pairwise_cons.mp h.1).2,fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

 
theorem sparseGapValue_injective (c d : List (ℕ × ℕ))
    (hc : c.Pairwise (fun q r => q.1 < r.1))
    (hd : d.Pairwise (fun q r => q.1 < r.1))
    (hpc : ∀ q ∈ c, 0 < q.2) (hpd : ∀ q ∈ d, 0 < q.2)
    (heq : ∀ i, sparseGapValue c i = sparseGapValue d i) : c = d := by
  induction c generalizing d with
  | nil =>
    cases d with
    | nil => rfl
    | cons q d =>
      obtain ⟨j,l⟩ := q
      have hh := heq j
      simp [sparseGapValue] at hh
      have := hpd (j,l) (by simp)
      omega
  | cons q c ih =>
    obtain ⟨i,l⟩ := q
    cases d with
    | nil =>
      have hh := heq i
      simp [sparseGapValue] at hh
      have := hpc (i,l) (by simp)
      omega
    | cons q d =>
      obtain ⟨j,m⟩ := q
      obtain ⟨hc0,hc1⟩ := List.pairwise_cons.mp hc
      obtain ⟨hd0,hd1⟩ := List.pairwise_cons.mp hd
      have hij : i = j := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hij | hji
        · have hz : sparseGapValue ((j,m)::d) i = 0 := by
            apply sparseGapValue_zero
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact hne
            · have := hd0 q hq
              change j < q.1 at this
              omega
          have hh := heq i
          rw [hz] at hh
          simp [sparseGapValue] at hh
          have := hpc (i,l) (by simp)
          omega
        · have hz : sparseGapValue ((i,l)::c) j = 0 := by
            apply sparseGapValue_zero
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact Ne.symm hne
            · have := hc0 q hq
              change i < q.1 at this
              omega
          have hh := heq j
          rw [hz] at hh
          simp [sparseGapValue] at hh
          have := hpd (j,m) (by simp)
          omega
      subst j
      have hlm : l = m := by simpa [sparseGapValue] using heq i
      subst m
      congr 1
      apply ih d hc1 hd1
        (fun q hq => hpc q (List.mem_cons_of_mem _ hq))
        (fun q hq => hpd q (List.mem_cons_of_mem _ hq))
      intro r
      by_cases hr : r = i
      · subst r
        rw [sparseGapValue_zero c i (fun q hq => (hc0 q hq).ne),
          sparseGapValue_zero d i (fun q hq => (hd0 q hq).ne)]
      · simpa only [sparseGapValue,ite_eq_right hr] using heq r

 
def sparseGapArray (k M : ℕ) (c : List (ℕ × ℕ)) (h : ValidSparseGapCode k M c) :
    Fin k → Fin (M+1) :=
  fun i => ⟨sparseGapValue c (i.val+1),Nat.lt_succ_of_le (sparseGapValue_bound k M c h _)⟩

theorem sparseGapArray_injective (k M : ℕ) (c d : List (ℕ × ℕ))
    (hc : ValidSparseGapCode k M c) (hd : ValidSparseGapCode k M d)
    (heq : sparseGapArray k M c hc = sparseGapArray k M d hd) : c = d := by
  apply sparseGapValue_injective c d hc.1 hd.1
    (fun q hq => (hc.2 q hq).2.2.1) (fun q hq => (hd.2 q hq).2.2.1)
  intro i
  by_cases hi : 1 ≤ i ∧ i ≤ k
  · have he := congrArg (fun f => (f ⟨i-1,by omega⟩).val) heq
    simpa only [sparseGapArray,show i-1+1 = i by omega] using he
  · rw [sparseGapValue_zero c i, sparseGapValue_zero d i]
    · intro q hq he
      have h := hd.2 q hq
      omega
    · intro q hq he
      have h := hc.2 q hq
      omega

 

theorem SpliceTrace.valid_gap_code (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j M : ℕ) (ω ωf : Set E)
    (steps : List (ℕ × E)) (h : SpliceTrace G x η y k j ω steps ωf)
    (hCf : (cluster G ωf x).Finite) (L : ℝ)
    (hgood : ∀ i, 1 ≤ i → i ≤ k → (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M ∧ GoodForScale G (η i) (y i) L) :
    ValidSparseGapCode k M (gapSpliceCode G ωf x (y k) steps) ∧
      ∀ q ∈ gapSpliceCode G ωf x (y k) steps, j < q.1 := by
  induction steps generalizing j ω with
  | nil => simp [ValidSparseGapCode,gapSpliceCode]
  | cons q rest ih =>
    obtain ⟨i,e⟩ := q
    have hs := h.seam_data G x η y k j ω ωf ((i,e)::rest) (i,e) (by simp)
    have hi : 1 ≤ i := by omega
    obtain ⟨hCi,hMi,hGi⟩ := hgood i hi hs.2.1
    have hg := h.head_gap_bounds G hloc x η y k j i M ω ωf e rest hCf hCi hMi L hGi
    change 1 ≤ _ ∧ 1 ≤ traceHeadGap G ωf x (y k) e rest ∧
      traceHeadGap G ωf x (y k) e rest ≤ M ∧ _ at hg
    cases h with
    | step j i ω e a b rest ωf _ _ _ _ _ _ _ _ _ ht =>
      obtain ⟨⟨hpair,hbounds⟩,hlater⟩ := ih i _ ht
      simp only [gapSpliceCode]
      refine ⟨⟨List.pairwise_cons.mpr ⟨?_,hpair⟩,?_⟩,?_⟩
      · exact hlater
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨hi,hs.2.1,hg.2.1,hg.2.2.1⟩
        · exact hbounds q hq
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hs.1
        · exact hs.1.trans (hlater q hq)

end SparseGapCode

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TraceContactMass
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def seamContactCount (G : BondGraph V E) (η : ℕ → Set E)
    (y : ℕ → V) (ωf : Set E) (x : V) (i : ℕ) (e : E) : ℕ :=
  (contactSet G (η i)
    (cluster G (η i ∩ internalEdges G (cluster G (ωf \ {e}) x)ᶜ) (y i))).ncard

 
noncomputable def traceContactCount (G : BondGraph V E) (η : ℕ → Set E)
    (y : ℕ → V) (ωf : Set E) (x : V) : List (ℕ × E) → ℕ → ℕ
  | [], _ => 1
  | (j,e)::c, i => if i = j then seamContactCount G η y ωf x j e
      else traceContactCount G η y ωf x c i

 
theorem SpliceTrace.contact_weight_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j M : ℕ) (ω ωf : Set E)
    (steps : List (ℕ × E)) (h : SpliceTrace G x η y k j ω steps ωf)
    (hCf : (cluster G ωf x).Finite) (L : ℝ) (hL : 1 ≤ L)
    (hgood : ∀ i, 1 ≤ i → i ≤ k → (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M ∧ GoodForScale G (η i) (y i) L) :
    ∀ i, 1 ≤ traceContactCount G η y ωf x steps i ∧
      (traceContactCount G η y ωf x steps i : ℝ)⁻¹ ≤
        gapLetterWeight L (sparseGapValue (gapSpliceCode G ωf x (y k) steps) i) := by
  induction steps generalizing j ω with
  | nil => simp [traceContactCount,gapSpliceCode,sparseGapValue,gapLetterWeight]
  | cons q rest ih =>
    obtain ⟨i,e⟩ := q
    have hs := h.seam_data G x η y k j ω ωf ((i,e)::rest) (i,e) (by simp)
    have hi : 1 ≤ i := by omega
    obtain ⟨hCi,hMi,hGi⟩ := hgood i hi hs.2.1
    have hg := h.head_gap_bounds G hloc x η y k j i M ω ωf e rest hCf hCi hMi L hGi
    have hcut := h.head_cut G x η y k j i ω ωf e rest
    change 1 ≤ _ ∧ 1 ≤ traceHeadGap G ωf x (y k) e rest ∧
      traceHeadGap G ωf x (y k) e rest ≤ M ∧ _ at hg
    have hk : seamContactCount G η y ωf x i e =
      (contactSet G (η i) (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i))).ncard := by
      unfold seamContactCount
      rw [hcut]
    rw [← hk] at hg
    cases h with
    | step j i ω e a b rest ωf _ _ _ _ _ _ _ _ _ ht =>
      intro r
      by_cases hr : r = i
      · subst r
        simp only [traceContactCount,gapSpliceCode,sparseGapValue,ite_true]
        refine ⟨hg.1,?_⟩
        rw [gapLetterWeight,ite_eq_right (by omega)]
        exact inverse_contact_weight_le _ _ L hg.1 hg.2.1 hL hg.2.2.2
      · simpa only [traceContactCount,gapSpliceCode,sparseGapValue,ite_eq_right hr] using ih i _ ht r



theorem SpliceTrace.code_unique_of_gapCode (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j : ℕ) (ω₁ ω₂ ωf : Set E)
    (c₁ c₂ : List (ℕ × E))
    (ht₁ : SpliceTrace G x η₁ y₁ k j ω₁ c₁ ωf)
    (ht₂ : SpliceTrace G x η₂ y₂ k j ω₂ c₂ ωf)
    (hz : y₁ k = y₂ k) (hC : (cluster G ωf x).Finite)
    (heq : gapSpliceCode G ωf x (y₁ k) c₁ = gapSpliceCode G ωf x (y₁ k) c₂) : c₁ = c₂ := by
  apply ordinalSpliceCode_injective G ωf x (y₁ k) hC c₁ c₂
    (ht₁.seams_pivotal G x η₁ y₁ k j ω₁ ωf c₁)
    (by simpa only [hz] using ht₂.seams_pivotal G x η₂ y₂ k j ω₂ ωf c₂)
  rw [← ht₁.decode_gap_code G x η₁ y₁ k j ω₁ ωf c₁ hC,heq,hz,
    ht₂.decode_gap_code G x η₂ y₂ k j ω₂ ωf c₂ hC]

end TraceContactMass

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RemoteSpliceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 

def GraphSeparated (G : BondGraph V E) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬Adj G a b

end RemoteSpliceGeometry

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RemoteReplay
attribute [local instance] Classical.propDecidable Classical.decEq

 

def replaySplice (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V) :
    List (ℕ × E) → Set E → Set E
  | [], ω => ω
  | (i,e)::rest, ω =>
    replaySplice G x η y rest (spliceField G (cluster G ω x)
      (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) e ω (η i))

 
def replayMasks (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V) :
    List (ℕ × E) → Set E → List (ℕ × Set E)
  | [], _ => []
  | (i,e)::rest, ω =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    (i,spliceMask G S B e)::replayMasks G x η y rest (spliceField G S B e ω (η i))

 
def replayContacts (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V) :
    List (ℕ × E) → Set E → List (Set E)
  | [], _ => []
  | (i,e)::rest, ω =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    contactSet G (η i) B::replayContacts G x η y rest (spliceField G S B e ω (η i))

end RemoteReplay

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeterministicReplay
attribute [local instance] Classical.propDecidable Classical.decEq

 

def FollowsContactRule (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (choose : ℕ → Set E → E) (steps : List (ℕ × E)) (ω : Set E) : Prop :=
  List.Forall₂ (fun q K => choose q.1 K = q.2) steps (replayContacts G x η y steps ω)

end DeterministicReplay

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section MaskExecution
attribute [local instance] Classical.propDecidable Classical.decEq

 
def runMasks : List (ℕ × Set E) → SpliceState E → SpliceState E
  | [], s => s
  | (i,M)::ms, s => runMasks ms (exchangeState M i s)



theorem SpliceTrace.runMasks_first (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ θ : ℕ → Set E, (∀ l, j < l → l ≤ k → θ l = η l) →
    (runMasks (replayMasks G x η y steps ω) (ω,θ)).1 = ωf := by
  induction h with
  | stop => exact fun _ _ => rfl
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    intro θ hθ
    have hθi := hθ i hji hik
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let M := spliceMask G S B e
    let ω' := spliceField G S B e ω (η i)
    let θ' := Function.update θ i (exchangeOn M (θ i) ω)
    have hstep : exchangeState M i (ω,θ) = (ω',θ') := by
      apply Prod.ext
      · change exchangeOn M ω (θ i) = exchangeOn M ω (η i)
        rw [hθi]
      · rfl
    change (runMasks (replayMasks G x η y rest ω') (exchangeState M i (ω,θ))).1 = ωf
    rw [hstep]
    apply ih θ'
    intro l hil hlk
    rw [show θ' l = θ l from Function.update_of_ne (by omega) _ _]
    exact hθ l (hji.trans hil) hlk


end MaskExecution

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointWeight
attribute [local instance] Classical.propDecidable Classical.decEq

 

abbrev JointSpliceState (E : Type v) := Set E × (ℕ → Set E) × (ℕ → Set E)

noncomputable def jointTupleWeight (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (s : JointSpliceState E) : ℝ :=
  bernoulliWeight Q (domainBits Q s.1) p *
    (∏ i ∈ J₁, bernoulliWeight Q (domainBits Q (s.2.1 i)) p) *
    ∏ i ∈ J₂, bernoulliWeight Q (domainBits Q (s.2.2 i)) p

theorem replayMasks_indices (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (c : List (ℕ × E)) (ω : Set E) :
    (replayMasks G x η y c ω).map Prod.fst = c.map Prod.fst := by
  induction c generalizing ω with
  | nil => rfl
  | cons q c ih =>
    obtain ⟨i,e⟩ := q
    simp only [replayMasks,List.map_cons,ih]

end JointWeight

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_ReferenceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference Laws for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectorySupport
attribute [local instance] Classical.propDecidable Classical.decEq

 
def trajectoryUnion (G : BondGraph V E) (η : ℕ → Set E) (y : ℕ → V) : ℕ → Set V
  | 0 => ∅
  | k+1 => trajectoryUnion G η y k ∪ cluster G (η (k+1)) (y (k+1))

theorem mem_trajectoryUnion (G : BondGraph V E) (η : ℕ → Set E) (y : ℕ → V)
    (k : ℕ) (v : V) : v ∈ trajectoryUnion G η y k ↔
      ∃ i, 1 ≤ i ∧ i ≤ k ∧ v ∈ cluster G (η i) (y i) := by
  induction k with
  | zero => simp [trajectoryUnion]
  | succ k ih =>
    simp only [trajectoryUnion,Set.mem_union,ih]
    constructor
    · rintro (⟨i,hi,hik,hv⟩ | hv)
      · exact ⟨i,hi,by omega,hv⟩
      · exact ⟨k+1,by omega,by omega,hv⟩
    · rintro ⟨i,hi,hik,hv⟩
      by_cases he : i = k+1
      · exact Or.inr (he ▸ hv)
      · exact Or.inl ⟨i,hi,by omega,hv⟩

theorem trajectoryUnion_finite_cap (G : BondGraph V E) (η : ℕ → Set E) (y : ℕ → V)
    (k M : ℕ) (hcaps : ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (η i) (y i)).Finite ∧ (cluster G (η i) (y i)).ncard ≤ M) :
    (trajectoryUnion G η y k).Finite ∧ (trajectoryUnion G η y k).ncard ≤ k*M := by
  induction k with
  | zero => simp [trajectoryUnion]
  | succ k ih =>
    obtain ⟨hf,hc⟩ := ih (fun i hi hik => hcaps i hi (by omega))
    obtain ⟨hf',hc'⟩ := hcaps (k+1) (by omega) (by omega)
    refine ⟨hf.union hf',?_⟩
    calc
      _ ≤ (trajectoryUnion G η y k).ncard + (cluster G (η (k+1)) (y (k+1))).ncard := Set.ncard_union_le ..
      _ ≤ k*M+M := Nat.add_le_add hc hc'
      _ = (k+1)*M := by ring

 

theorem SpliceTrace.added_subset_trajectory (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) :
    cluster G ωf x \ cluster G ω x ⊆ trajectoryUnion G η y k := by
  induction h with
  | stop => exact fun _ hv => (hv.2 hv.1).elim
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    have hC : cluster G ω' x = S ∪ B := splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    intro v hv
    by_cases hv' : v ∈ cluster G ω' x
    · rw [hC] at hv'
      have hvB := hv'.resolve_left hv.2
      exact (mem_trajectoryUnion G η y k v).mpr
        ⟨i,by omega,hik,conn_mono G Set.inter_subset_left hvB⟩
    · exact ih ⟨hv.1,hv'⟩



end TrajectorySupport

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteReferenceLaw
attribute [local instance] Classical.propDecidable Classical.decEq

 
abbrev FiniteField (Q : Finset E) := ↥Q.powerset

def finiteFieldSet (Q : Finset E) (ω : FiniteField Q) : Set E := (ω.val : Set E)

noncomputable def finiteFieldWeight (Q : Finset E) (p : ℝ) (ω : FiniteField Q) : ℝ :=
  bernoulliWeight Q ω.val p

@[simp] theorem domainBits_finiteFieldSet (Q : Finset E) (ω : FiniteField Q) :
    domainBits Q (finiteFieldSet Q ω) = ω.val := by
  ext e
  have hs := Finset.mem_powerset.mp ω.property
  simp only [mem_domainBits,finiteFieldSet,Finset.mem_coe]
  exact ⟨fun h => h.2,fun h => ⟨hs h,h⟩⟩

theorem finiteFieldWeight_nonneg (Q : Finset E) (p : unitInterval) (ω : FiniteField Q) :
    0 ≤ finiteFieldWeight Q p ω := bernoulliWeight_nonneg _ _ p

theorem sum_finiteFieldWeight (Q : Finset E) (p : ℝ) :
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω = 1 := by
  rw [show (fun ω : FiniteField Q => finiteFieldWeight Q p ω) =
    (fun ω : FiniteField Q => bernoulliWeight Q ω.val p) from rfl,Finset.sum_coe_sort Q.powerset (fun ω => bernoulliWeight Q ω p)]
  simpa only [bernoulliPolynomial,bernoulliWeight,mul_one,one_mul] using bernoulliPolynomial_const Q 1 p

 

def finiteFieldFamily (Q : Finset E) (J : Finset ℕ) (η : ↥J → FiniteField Q) : ℕ → Set E :=
  fun i => if hi : i ∈ J then finiteFieldSet Q (η ⟨i,hi⟩) else ∅

@[simp] theorem finiteFieldFamily_at (Q : Finset E) (J : Finset ℕ)
    (η : ↥J → FiniteField Q) (i : ↥J) :
    finiteFieldFamily Q J η i = finiteFieldSet Q (η i) := by
  simp [finiteFieldFamily,i.property]

noncomputable def finiteFamilyWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (η : ↥J → FiniteField Q) : ℝ := ∏ i, finiteFieldWeight Q p (η i)

theorem finiteFamilyWeight_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (η : ↥J → FiniteField Q) : 0 ≤ finiteFamilyWeight Q J p η :=
  Finset.prod_nonneg fun _ _ => finiteFieldWeight_nonneg Q p _

theorem sum_finiteFamilyWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ) :
    ∑ η : ↥J → FiniteField Q, finiteFamilyWeight Q J p η = 1 := by
  unfold finiteFamilyWeight
  rw [← Fintype.prod_sum]
  simp only [sum_finiteFieldWeight,Finset.prod_const_one]

theorem prod_fieldFamilyWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (η : ↥J → FiniteField Q) :
    (∏ i ∈ J, bernoulliWeight Q (domainBits Q (finiteFieldFamily Q J η i)) p) =
      finiteFamilyWeight Q J p η := by
  rw [← Finset.prod_coe_sort J]
  simp only [finiteFieldFamily_at,domainBits_finiteFieldSet,finiteFamilyWeight,finiteFieldWeight]

abbrev FiniteJointData (Q : Finset E) (J₁ J₂ : Finset ℕ) :=
  FiniteField Q × (↥J₁ → FiniteField Q) × (↥J₂ → FiniteField Q)

theorem finiteFieldSet_injective (Q : Finset E) : Function.Injective (finiteFieldSet Q) := by
  intro a b he
  exact Subtype.ext (Finset.coe_injective he)

theorem finiteFieldFamily_injective (Q : Finset E) (J : Finset ℕ) :
    Function.Injective (finiteFieldFamily Q J) := by
  intro a b he
  funext i
  apply finiteFieldSet_injective Q
  simpa only [finiteFieldFamily_at] using congrFun he i

end FiniteReferenceLaw

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteReferenceFactor
attribute [local instance] Classical.propDecidable Classical.decEq



theorem exchangeOn_subset (M ω η Q : Set E) (hω : ω ⊆ Q) (hη : η ⊆ Q) :
    exchangeOn M ω η ⊆ Q := by
  rintro e (⟨he,_⟩ | ⟨he,_⟩)
  · exact hω he
  · exact hη he

end FiniteReferenceFactor

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformContactSelector
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def uniformRank (K : ℕ) (hK : 0 < K) (t : unitInterval) : Fin K :=
  ⟨min ⌊(K:ℝ)*(t:ℝ)⌋₊ (K-1), lt_of_le_of_lt (min_le_right ..) (by omega)⟩



noncomputable def uniformContact (K : Finset E) (hK : K.Nonempty)
    (t : unitInterval) : E :=
  ((K.equivFin).symm (uniformRank K.card (Finset.card_pos.mpr hK) t)).val



noncomputable def chooseContact [Nonempty E] (seed : ℕ → unitInterval)
    (i : ℕ) (K : Set E) : E :=
  if hf : K.Finite then if hn : K.Nonempty then
    uniformContact hf.toFinset (by simpa using hn) (seed i)
  else Classical.arbitrary E else Classical.arbitrary E

end UniformContactSelector
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_MomentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteTraceDistribution
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finite_bounded_lists {A : Type*} (Q : Finset A) (k : ℕ) :
    {c : List A | c.length ≤ k ∧ ∀ q ∈ c, q ∈ Q}.Finite := by
  have hf := (List.finite_length_le ↥Q k).image (List.map Subtype.val)
  apply hf.subset
  rintro c ⟨hc,hQ⟩
  let d : List ↥Q := c.attach.map (fun q => ⟨q.val,hQ q.val q.property⟩)
  refine ⟨d,?_,?_⟩
  · simpa only [d,List.length_map,List.length_attach,Set.mem_ofPred_eq] using hc
  · simp [d,List.map_map]

noncomputable def boundedTraceCodes (Q : Finset E) (k : ℕ) : Finset (List (ℕ × E)) :=
  (finite_bounded_lists ((Finset.Icc 1 k) ×ˢ Q) k).toFinset

@[simp] theorem mem_boundedTraceCodes (Q : Finset E) (k : ℕ) (c : List (ℕ × E)) :
    c ∈ boundedTraceCodes Q k ↔ c.length ≤ k ∧ ∀ q ∈ c, 1 ≤ q.1 ∧ q.1 ≤ k ∧ q.2 ∈ Q := by
  simp [boundedTraceCodes,Finset.mem_product,and_assoc]



noncomputable def finiteTraceCodes (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω : Set E) (Q : Finset E) : Finset (List (ℕ × E)) :=
  (boundedTraceCodes Q k).filter (fun c =>
    SpliceTrace G x η y k j ω c (replaySplice G x η y c ω))

theorem mem_finiteTraceCodes_iff (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω : Set E) (Q : Finset E) (c : List (ℕ × E)) :
    c ∈ finiteTraceCodes G x η y k j ω Q ↔ c ∈ boundedTraceCodes Q k ∧
      SpliceTrace G x η y k j ω c (replaySplice G x η y c ω) := by
  simp [finiteTraceCodes]



end FiniteTraceDistribution
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteSpliceState
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem SpliceTrace.runMasks_execution (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) :
    ∀ θ : ℕ → Set E, (∀ l, j < l → l ≤ k → θ l = η l) →
      SpliceExecution G x (ω,θ) c (runMasks (replayMasks G x η y c ω) (ω,θ)) := by
  induction h with
  | stop => intro θ _; exact SpliceExecution.nil _
  | @step j i ω e a b c ωf hn hji hik hm hy he hab ha hb ht ih =>
    intro θ hθ
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let M := spliceMask G S B e
    let ω' := spliceField G S B e ω (η i)
    let θ' := Function.update θ i (exchangeOn M (θ i) ω)
    have hθi := hθ i hji hik
    have hstep : exchangeState M i (ω,θ) = (ω',θ') := by
      apply Prod.ext
      · change exchangeOn M ω (θ i) = exchangeOn M ω (η i)
        rw [hθi]
      · rfl
    change SpliceExecution G x (ω,θ) ((i,e)::c)
      (runMasks (replayMasks G x η y c ω') (exchangeState M i (ω,θ)))
    rw [hstep]
    refine SpliceExecution.cons (ω,θ) (ω',θ') _ (i,e) c ?_ ?_
    · refine ⟨y i,a,b,hy,?_,hab,ha,?_,?_⟩
      · simpa only [hθi] using he
      · simpa only [hθi] using hb
      · simpa only [hθi] using hstep.symm
    · apply ih θ'
      intro l hil hlk
      rw [show θ' l = θ l from Function.update_of_ne (by omega) _ _]
      exact hθ l (hji.trans hil) hlk

abbrev FiniteSpliceData (Q : Finset E) (J : Finset ℕ) :=
  FiniteField Q × (↥J → FiniteField Q)

def encodeFiniteSplice (Q : Finset E) (J : Finset ℕ)
    (s : FiniteSpliceData Q J) : SpliceState E :=
  (finiteFieldSet Q s.1,finiteFieldFamily Q J s.2)

noncomputable def finiteSpliceDomain (Q : Finset E) (J : Finset ℕ) : Finset (SpliceState E) :=
  Finset.univ.image (encodeFiniteSplice Q J)


theorem mem_finiteSpliceDomain_iff (Q : Finset E) (J : Finset ℕ) (s : SpliceState E) :
    s ∈ finiteSpliceDomain Q J ↔ s.1 ⊆ (Q : Set E) ∧
      (∀ i, s.2 i ⊆ (Q : Set E)) ∧ ∀ i ∉ J, s.2 i = ∅ := by
  constructor
  · intro hs
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hs
    refine ⟨?_,?_,?_⟩
    · exact Finset.coe_subset.mpr (Finset.mem_powerset.mp a.1.property)
    · intro i
      by_cases hi : i ∈ J
      · simpa only [encodeFiniteSplice,finiteFieldFamily,dite_eq_left hi,finiteFieldSet] using
          Finset.coe_subset.mpr (Finset.mem_powerset.mp (a.2 ⟨i,hi⟩).property)
      · simp [encodeFiniteSplice,finiteFieldFamily,hi]
    · intro i hi
      simp [encodeFiniteSplice,finiteFieldFamily,hi]
  · rintro ⟨hω,hη,hz⟩
    let desc (ω : Set E) : FiniteField Q := ⟨domainBits Q ω,Finset.mem_powerset.mpr (domainBits_subset Q ω)⟩
    have he (ω : Set E) (h : ω ⊆ (Q : Set E)) : finiteFieldSet Q (desc ω) = ω := by
      ext e
      simp only [finiteFieldSet,desc,Finset.mem_coe,mem_domainBits]
      exact ⟨fun hh => hh.2,fun hh => ⟨h hh,hh⟩⟩
    refine Finset.mem_image.mpr ⟨(desc s.1,fun i => desc (s.2 i)),Finset.mem_univ _,?_⟩
    apply Prod.ext (he s.1 hω)
    funext i
    by_cases hi : i ∈ J
    · simp only [encodeFiniteSplice,finiteFieldFamily,dite_eq_left hi,he _ (hη i)]
    · simp only [encodeFiniteSplice,finiteFieldFamily,dite_eq_right hi,hz i hi]

theorem exchangeState_mem_finiteSpliceDomain (Q : Finset E) (J : Finset ℕ)
    (s : SpliceState E) (hs : s ∈ finiteSpliceDomain Q J) (i : ℕ) (hi : i ∈ J) (M : Set E) :
    exchangeState M i s ∈ finiteSpliceDomain Q J := by
  obtain ⟨hω,hη,hz⟩ := (mem_finiteSpliceDomain_iff Q J s).mp hs
  apply (mem_finiteSpliceDomain_iff Q J _).mpr
  refine ⟨exchangeOn_subset M _ _ _ hω (hη i),?_,?_⟩
  · intro l
    by_cases hli : l = i
    · simpa only [hli,exchangeState_at] using exchangeOn_subset M _ _ _ (hη i) hω
    · rw [exchangeState_away _ _ _ _ hli]
      exact hη l
  · intro l hl
    have hli : l ≠ i := by intro he; subst l; exact hl hi
    rw [exchangeState_away _ _ _ _ hli]
    exact hz l hl

theorem runMasks_mem_finiteSpliceDomain (Q : Finset E) (J : Finset ℕ)
    (s : SpliceState E) (hs : s ∈ finiteSpliceDomain Q J) (ms : List (ℕ × Set E))
    (hJ : ∀ q ∈ ms, q.1 ∈ J) : runMasks ms s ∈ finiteSpliceDomain Q J := by
  induction ms generalizing s with
  | nil => exact hs
  | cons q ms ih =>
    apply ih _ (exchangeState_mem_finiteSpliceDomain Q J s hs q.1 (hJ q (by simp)) q.2)
    exact fun q hq => hJ q (by simp [hq])

end FiniteSpliceState

end Percolation

 
open MeasureTheory
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteSwitchDensity
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def finiteInverseLoad {I : Type*} [Fintype I]
    (out : I → SpliceState E) (mass : I → ℝ) (t : SpliceState E) : ℝ :=
  ∑ a, if out a = t then mass a else 0

theorem finiteInverseLoad_nonneg {I : Type*} [Fintype I]
    (out : I → SpliceState E) (mass : I → ℝ) (hm : ∀ a, 0 ≤ mass a) (t : SpliceState E) :
    0 ≤ finiteInverseLoad out mass t := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hm a
  · exact le_refl 0



end FiniteSwitchDensity

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteForwardDensity
attribute [local instance] Classical.propDecidable Classical.decEq

 

abbrev FiniteTraceIndex (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V) :=
  (s : ↥A) × ↥(finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q)

def traceIndexInput (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) : SpliceState E := a.1.val

def traceIndexCode (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) : List (ℕ × E) := a.2.val

def traceIndexOutput (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) : SpliceState E :=
  runMasks (replayMasks G x a.1.val.2 (y a.1.val) a.2.val a.1.val.1) a.1.val

theorem traceIndex_valid (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) :
    SpliceTrace G x a.1.val.2 (y a.1.val) k 0 a.1.val.1 a.2.val
      (traceIndexOutput G x k Q A y a).1 ∧
    SpliceExecution G x a.1.val a.2.val (traceIndexOutput G x k Q A y a) := by
  have ht := ((mem_finiteTraceCodes_iff G x a.1.val.2 (y a.1.val) k 0 a.1.val.1 Q a.2.val).mp
    a.2.property).2
  have hf := ht.runMasks_first G x a.1.val.2 (y a.1.val) k 0 a.1.val.1 _ a.2.val
    a.1.val.2 (by intros; rfl)
  refine ⟨?_,?_⟩
  · simpa only [traceIndexOutput,hf] using ht
  · exact ht.runMasks_execution G x a.1.val.2 (y a.1.val) k 0 a.1.val.1 _ a.2.val
      a.1.val.2 (by intros; rfl)

theorem traceIndex_injective (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V) :
    Function.Injective (fun a : FiniteTraceIndex G x k Q A y =>
      (traceIndexInput G x k Q A y a,traceIndexCode G x k Q A y a)) := by
  rintro ⟨a,c⟩ ⟨b,d⟩ he
  have hah : a = b := Subtype.ext (congrArg Prod.fst he)
  subst b
  have hcd : c = d := Subtype.ext (congrArg Prod.snd he)
  subst d
  rfl

theorem traceIndexOutput_mem (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (hA : A ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (a : FiniteTraceIndex G x k Q A y) :
    traceIndexOutput G x k Q A y a ∈ finiteSpliceDomain Q (Finset.Icc 1 k) := by
  apply runMasks_mem_finiteSpliceDomain Q (Finset.Icc 1 k) a.1.val (hA a.1.property)
  intro q hq
  have hmap : q.1 ∈ (replayMasks G x a.1.val.2 (y a.1.val) a.2.val a.1.val.1).map Prod.fst :=
    List.mem_map.mpr ⟨q,hq,rfl⟩
  rw [replayMasks_indices] at hmap
  obtain ⟨r,hr,her⟩ := List.mem_map.mp hmap
  have h := (traceIndex_valid G x k Q A y a).1.seam_data G x a.1.val.2 (y a.1.val)
    k 0 a.1.val.1 _ a.2.val r hr
  exact her ▸ Finset.mem_Icc.mpr ⟨h.1,h.2.1⟩

 

noncomputable def traceIndexMass (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) : ℝ :=
  ∏ i : Fin k, (traceContactCount G a.1.val.2 (y a.1.val)
    (traceIndexOutput G x k Q A y a).1 x a.2.val (i.val+1):ℝ)⁻¹

end FiniteForwardDensity

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteRootLoad
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def finiteRootLoad (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : SpliceState E → ℝ) (ω : FiniteField Q) : ℝ :=
  ∑ η : ↥J → FiniteField Q, finiteFamilyWeight Q J p η *
    f (finiteFieldSet Q ω,finiteFieldFamily Q J η)

theorem finiteRootLoad_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (f : SpliceState E → ℝ) (hf : ∀ s ∈ finiteSpliceDomain Q J, 0 ≤ f s)
    (ω : FiniteField Q) : 0 ≤ finiteRootLoad Q J p f ω := by
  apply Finset.sum_nonneg
  intro η _
  apply mul_nonneg (finiteFamilyWeight_nonneg Q J p η)
  exact hf _ (Finset.mem_image.mpr ⟨(ω,η),Finset.mem_univ _,rfl⟩)

theorem finiteRootLoad_le (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (f : SpliceState E → ℝ) (C : ℝ)
    (hf : ∀ s ∈ finiteSpliceDomain Q J, f s ≤ C)
    (ω : FiniteField Q) : finiteRootLoad Q J p f ω ≤ C := by
  calc
    _ ≤ ∑ η : ↥J → FiniteField Q, finiteFamilyWeight Q J p η * C := by
      apply Finset.sum_le_sum
      intro η _
      apply mul_le_mul_of_nonneg_left _ (finiteFamilyWeight_nonneg Q J p η)
      exact hf _ (Finset.mem_image.mpr ⟨(ω,η),Finset.mem_univ _,rfl⟩)
    _ = C := by rw [← Finset.sum_mul,sum_finiteFamilyWeight,one_mul]


end FiniteRootLoad

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FinitePairLoad
attribute [local instance] Classical.propDecidable Classical.decEq

 
def pairSpliceOutput (s t : SpliceState E) : JointSpliceState E := (s.1,s.2,t.2)

end FinitePairLoad

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Transport_TrajectoryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trajectory Mass for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OldPathWeight
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def oldPathWeight (k : ℕ) (q : Set E → V → V → ℝ)
    (y : ℕ → V) (η : ℕ → Set E) : ℝ :=
  ∏ i : ↥(Finset.Icc 1 k), q (η i) (y i) (y (i.val-1))



theorem oldPathWeight_support (G : BondGraph V E) (k M : ℕ) (L : ℝ)
    (q : Set E → V → V → ℝ)
    (hs : ∀ ω a b, q ω a b ≠ 0 → b ∈ cluster G ω a ∧
      (cluster G ω a).Finite ∧ (cluster G ω a).ncard ≤ M ∧ GoodForScale G ω a L)
    (y : ℕ → V) (η : ℕ → Set E) (hy : oldPathWeight k q y η ≠ 0) :
    ∀ i, 1 ≤ i → i ≤ k → y (i-1) ∈ cluster G (η i) (y i) ∧
      (cluster G (η i) (y i)).Finite ∧ (cluster G (η i) (y i)).ncard ≤ M ∧
      GoodForScale G (η i) (y i) L := by
  intro i hi hik
  apply hs
  have h := (Finset.prod_ne_zero_iff.mp hy) ⟨i, Finset.mem_Icc.mpr ⟨hi,hik⟩⟩ (Finset.mem_univ _)
  exact h

end OldPathWeight

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteOldRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {W : Type*}

 
def oldRunConsEquiv (k : ℕ) : (Fin (k+1) → W) ≃ W × (Fin k → W) where
  toFun y := (y 0, Fin.tail y)
  invFun y := Fin.cons y.1 y.2
  left_inv := Fin.cons_self_tail
  right_inv y := by simp

 

noncomputable def oldRunWeight (K : ℕ → W → W → ℝ) : (k : ℕ) → W → (Fin k → W) → ℝ
  | 0, _, _ => 1
  | k+1, z, y => K (k+1) z (y 0) * oldRunWeight K k (y 0) (Fin.tail y)

theorem oldRunWeight_nonneg (K : ℕ → W → W → ℝ) (hK : ∀ i a b, 0 ≤ K i a b)
    (k : ℕ) (z : W) (y : Fin k → W) : 0 ≤ oldRunWeight K k z y := by
  induction k generalizing z with
  | zero => exact zero_le_one
  | succ k ih => exact mul_nonneg (hK _ _ _) (ih _ _)

theorem sum_oldRunWeight_succ [Fintype W] (K : ℕ → W → W → ℝ) (k : ℕ) (z : W) :
    (∑ y : Fin (k+1) → W, oldRunWeight K (k+1) z y) =
      ∑ a : W, K (k+1) z a * ∑ y : Fin k → W, oldRunWeight K k a y := by
  rw [Fintype.sum_equiv (oldRunConsEquiv k) _
    (fun y => K (k+1) z y.1 * oldRunWeight K k y.1 y.2) (by intro y; rfl),
    Fintype.sum_prod_type]
  simp only [Finset.mul_sum]

 

theorem sum_oldRunWeight_le [Fintype W] (K : ℕ → W → W → ℝ)
    (hK : ∀ i a b, 0 ≤ K i a b) (u : ℝ) (hu : 0 ≤ u)
    (hrow : ∀ i a, ∑ b, K i a b ≤ u) (k : ℕ) (z : W) :
    (∑ y : Fin k → W, oldRunWeight K k z y) ≤ u^k := by
  induction k generalizing z with
  | zero => simp [oldRunWeight]
  | succ k ih =>
    rw [sum_oldRunWeight_succ]
    calc
      _ ≤ ∑ a : W, K (k+1) z a * u^k := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (ih a) (hK _ _ _)
      _ = (∑ a : W, K (k+1) z a) * u^k := (Finset.sum_mul _ _ _).symm
      _ ≤ u * u^k := mul_le_mul_of_nonneg_right (hrow _ _) (pow_nonneg hu _)
      _ = u^(k+1) := by ring



def oldRunVertices : (k : ℕ) → W → (Fin k → W) → ℕ → W
  | 0, z, _ => fun _ => z
  | k+1, z, y => fun i => if i ≤ k then oldRunVertices k (y 0) (Fin.tail y) i else z

@[simp] theorem oldRunVertices_last (k : ℕ) (z : W) (y : Fin k → W) :
    oldRunVertices k z y k = z := by
  cases k <;> simp [oldRunVertices]

theorem oldRunVertices_succ_of_le (k : ℕ) (z : W) (y : Fin (k+1) → W)
    (i : ℕ) (hi : i ≤ k) :
    oldRunVertices (k+1) z y i = oldRunVertices k (y 0) (Fin.tail y) i := by
  simp only [oldRunVertices, ite_eq_left hi]

 

theorem oldPathWeight_oldRunVertices (k : ℕ) (q : Set E → W → W → ℝ)
    (η : ℕ → Set E) (z : W) (y : Fin k → W) :
    oldPathWeight k q (oldRunVertices k z y) η =
      oldRunWeight (fun i => q (η i)) k z y := by
  induction k generalizing z with
  | zero =>
    unfold oldPathWeight
    rw [Finset.prod_coe_sort (Finset.Icc 1 0)
      (fun i => q (η i) (oldRunVertices 0 z y i) (oldRunVertices 0 z y (i-1)))]
    simp [oldRunWeight]
  | succ k ih =>
    unfold oldPathWeight
    rw [Finset.prod_coe_sort (Finset.Icc 1 (k+1))
      (fun i => q (η i) (oldRunVertices (k+1) z y i) (oldRunVertices (k+1) z y (i-1))),
      Finset.prod_Icc_succ_top (by omega)]
    have he : (∏ i ∈ Finset.Icc 1 k,
        q (η i) (oldRunVertices (k+1) z y i) (oldRunVertices (k+1) z y (i-1))) =
        oldPathWeight k q (oldRunVertices k (y 0) (Fin.tail y)) η := by
      unfold oldPathWeight
      rw [Finset.prod_coe_sort (Finset.Icc 1 k)
        (fun i => q (η i) (oldRunVertices k (y 0) (Fin.tail y) i)
          (oldRunVertices k (y 0) (Fin.tail y) (i-1)))]
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      rw [oldRunVertices_succ_of_le _ _ _ _ hi'.2,
        oldRunVertices_succ_of_le _ _ _ _ (by omega)]
    rw [he, ih, oldRunVertices_last, Nat.add_sub_cancel,
      oldRunVertices_succ_of_le _ _ _ _ (le_refl _), oldRunVertices_last]
    exact mul_comm _ _

end FiniteOldRun

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedCodeFiber
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem sum_comp_le_sum_of_injective {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ a, w (f a)) ≤ ∑ b, w b := by
  rw [← Finset.sum_image hf.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun b _ _ => hw b)

 
theorem finite_sum_group_weight {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (m : A → ℝ) (w : B → ℝ) :
    (∑ a, m a * w (f a)) = ∑ b, w b * ∑ a, if f a = b then m a else 0 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact mul_comm _ _

 

theorem finite_choice_fiber_le {A B C P : Type*} [Fintype A] [Fintype P]
    (f : A → B) (ctx : A → C) (choice : A → P)
    (hir : Function.Injective (fun a => (ctx a,choice a,f a)))
    (hctx : ∀ a b, f a = f b → ctx a = ctx b)
    (q : C → P → ℝ) (hq : ∀ c p, 0 ≤ q c p)
    (hrow : ∀ c, ∑ p, q c p ≤ 1) (b : B) :
    (∑ a, if f a = b then q (ctx a) (choice a) else 0) ≤ 1 := by
  let J := {a : A // f a = b}
  by_cases hne : Nonempty J
  · let a₀ : J := Classical.choice hne
    have hc (a : J) : ctx a.val = ctx a₀.val := hctx _ _ (a.property.trans a₀.property.symm)
    have hi : Function.Injective (fun a : J => choice a.val) := by
      intro a a' he
      apply Subtype.ext
      apply hir
      exact Prod.ext (hctx _ _ (a.property.trans a'.property.symm))
        (Prod.ext he (a.property.trans a'.property.symm))
    have hb := sum_comp_le_sum_of_injective (fun a : J => choice a.val) hi
      (q (ctx a₀.val)) (hq _)
    have he : (∑ a, if f a = b then q (ctx a) (choice a) else 0) =
        ∑ a : J, q (ctx a) (choice a) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by intro a; simp) _
    rw [he]
    simpa only [hc] using hb.trans (hrow (ctx a₀.val))
  · have hn (a : A) : f a ≠ b := fun h => hne ⟨⟨a,h⟩⟩
    simp only [ite_eq_right (hn _),Finset.sum_const_zero,zero_le_one]

 

theorem finite_weighted_code_mass_le {A B C P : Type*} [Fintype A] [Fintype B] [Fintype P]
    (f : A → B) (ctx : A → C) (choice : A → P)
    (hir : Function.Injective (fun a => (ctx a,choice a,f a)))
    (hctx : ∀ a b, f a = f b → ctx a = ctx b)
    (q : C → P → ℝ) (hq : ∀ c p, 0 ≤ q c p) (hrow : ∀ c, ∑ p, q c p ≤ 1)
    (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ a, q (ctx a) (choice a) * w (f a)) ≤ ∑ b, w b := by
  rw [finite_sum_group_weight]
  apply Finset.sum_le_sum
  intro b _
  calc
    _ ≤ w b * 1 := mul_le_mul_of_nonneg_left
      (finite_choice_fiber_le f ctx choice hir hctx q hq hrow b) (hw b)
    _ = w b := mul_one _

end WeightedCodeFiber
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedInverseLoad
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finiteInverseLoad_weighted_le {I P : Type*} [Fintype I] [Fintype P]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x z : V) (k M : ℕ)
    (L : ℝ) (hL : 1 ≤ L)
    (inp out : I → SpliceState E) (steps : I → List (ℕ × E)) (y : I → ℕ → V)
    (choice : I → P) (hir : Function.Injective (fun a => (inp a,choice a,steps a)))
    (q : SpliceState E → P → ℝ) (hq : ∀ s b, 0 ≤ q s b)
    (hrow : ∀ s, ∑ b, q s b ≤ 1)
    (htrace : ∀ a, SpliceTrace G x (inp a).2 (y a) k 0 (inp a).1 (steps a) (out a).1)
    (hex : ∀ a, SpliceExecution G x (inp a) (steps a) (out a))
    (hz : ∀ a, y a k = z) (hfin : ∀ a, (cluster G (out a).1 x).Finite)
    (hgood : ∀ a i, 1 ≤ i → i ≤ k → (cluster G ((inp a).2 i) (y a i)).Finite ∧
      (cluster G ((inp a).2 i) (y a i)).ncard ≤ M ∧ GoodForScale G ((inp a).2 i) (y a i) L)
    (t : SpliceState E) :
    finiteInverseLoad out (fun a => q (inp a) (choice a) * ∏ i : Fin k,
      (traceContactCount G (inp a).2 (y a) (out a).1 x (steps a) (i.val+1):ℝ)⁻¹) t ≤
      inverseCodeMass M L ^ k := by
  let J := {a : I // out a = t}
  let c (a : J) := gapSpliceCode G (out a.val).1 x z (steps a.val)
  have hvalid (a : J) : ValidSparseGapCode k M (c a) := by
    have hv := (htrace a.val).valid_gap_code G hloc x (inp a.val).2 (y a.val) k 0 M
      (inp a.val).1 (out a.val).1 (steps a.val) (hfin a.val) L (hgood a.val)
    simpa only [c,hz a.val] using hv.1
  let arr (a : J) := sparseGapArray k M (c a) (hvalid a)
  let ctx (a : J) := (inp a.val,steps a.val)
  have hc (a b : J) (he : arr a = arr b) : ctx a = ctx b := by
    have ho : out a.val = out b.val := a.property.trans b.property.symm
    have hcode : c a = c b := sparseGapArray_injective k M (c a) (c b)
      (hvalid a) (hvalid b) he
    have htB : SpliceTrace G x (inp b.val).2 (y b.val) k 0
        (inp b.val).1 (steps b.val) (out a.val).1 := by
      rw [ho]
      exact htrace b.val
    have heB : SpliceExecution G x (inp b.val) (steps b.val) (out a.val) := ho.symm ▸ hex b.val
    have hg : gapSpliceCode G (out a.val).1 x (y a.val k) (steps a.val) =
        gapSpliceCode G (out a.val).1 x (y a.val k) (steps b.val) := by
      simpa only [c,hz a.val,ho] using hcode
    have hze : y a.val k = y b.val k := (hz a.val).trans (hz b.val).symm
    have hs := (htrace a.val).code_unique_of_gapCode G x (inp a.val).2 (inp b.val).2
      (y a.val) (y b.val) k 0 (inp a.val).1 (inp b.val).1 (out a.val).1
      (steps a.val) (steps b.val) htB hze (hfin a.val) hg
    have hi := (htrace a.val).input_unique_of_gapCode G x (inp a.val).2 (inp b.val).2
      (y a.val) (y b.val) k 0 (inp a.val).1 (inp b.val).1 (out a.val).1
      (steps a.val) (steps b.val) htB hze (hfin a.val) hg (out a.val).2 (hex a.val) heB
    exact Prod.ext hi hs
  have hi : Function.Injective (fun a : J => (ctx a,choice a.val,arr a)) := by
    intro a b he
    apply Subtype.ext
    apply hir
    have hec := congrArg Prod.fst he
    have hin : inp a.val = inp b.val := congrArg (fun s : SpliceState E × List (ℕ × E) => s.1) hec
    have hst : steps a.val = steps b.val := congrArg (fun s : SpliceState E × List (ℕ × E) => s.2) hec
    exact Prod.ext hin (Prod.ext (congrArg (fun z => z.2.1) he) hst)
  let w (b : Fin k → Fin (M+1)) := ∏ i, gapLetterWeight L (b i).val
  have hb := finite_weighted_code_mass_le arr ctx (fun a : J => choice a.val) hi hc
    (fun s b => q s.1 b) (fun s => hq s.1) (fun s => hrow s.1) w
    (fun b => Finset.prod_nonneg (fun i _ => gapLetterWeight_nonneg L (by linarith) _))
  change (∑ a : J, q (inp a.val) (choice a.val) * w (arr a)) ≤ ∑ b, w b at hb
  have he : finiteInverseLoad out (fun a => q (inp a) (choice a) * ∏ i : Fin k,
      (traceContactCount G (inp a).2 (y a) (out a).1 x (steps a) (i.val+1):ℝ)⁻¹) t =
      ∑ a : J, q (inp a.val) (choice a.val) * ∏ i : Fin k,
      (traceContactCount G (inp a.val).2 (y a.val) (out a.val).1 x (steps a.val) (i.val+1):ℝ)⁻¹ := by
    rw [finiteInverseLoad,← Finset.sum_filter]
    exact Finset.sum_subtype _ (by intro a; simp) _
  rw [he]
  calc
    _ ≤ ∑ a : J, q (inp a.val) (choice a.val) * w (arr a) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (hq _ _)
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro i _
      have h := ((htrace a.val).contact_weight_bound G hloc x (inp a.val).2 (y a.val)
        k 0 M (inp a.val).1 (out a.val).1 (steps a.val) (hfin a.val) L hL
        (hgood a.val) (i.val+1)).2
      simpa only [w,arr,sparseGapArray,c,hz a.val] using h
    _ ≤ ∑ b, w b := hb
    _ = _ := total_gap_code_mass k M L

end WeightedInverseLoad
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ChoiceForwardDensity
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P : Type*}

 

abbrev FiniteChoiceTraceIndex (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V) :=
  (r : P) × FiniteTraceIndex G x k Q (A r) (y r)

def choiceTraceInput (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (a : FiniteChoiceTraceIndex G x k Q A y) : SpliceState E :=
  traceIndexInput G x k Q (A a.1) (y a.1) a.2

def choiceTraceOutput (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (a : FiniteChoiceTraceIndex G x k Q A y) : SpliceState E :=
  traceIndexOutput G x k Q (A a.1) (y a.1) a.2

def choiceTraceCode (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (a : FiniteChoiceTraceIndex G x k Q A y) : List (ℕ × E) :=
  traceIndexCode G x k Q (A a.1) (y a.1) a.2

noncomputable def choiceTraceMass (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (q : SpliceState E → P → ℝ) (a : FiniteChoiceTraceIndex G x k Q A y) : ℝ :=
  q (choiceTraceInput G x k Q A y a) a.1 *
    traceIndexMass G x k Q (A a.1) (y a.1) a.2

theorem choiceTrace_injective (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V) :
    Function.Injective (fun a : FiniteChoiceTraceIndex G x k Q A y =>
      (choiceTraceInput G x k Q A y a,a.1,choiceTraceCode G x k Q A y a)) := by
  rintro ⟨r,a⟩ ⟨r',b⟩ he
  have hr : r = r' := congrArg (fun z => z.2.1) he
  subst r'
  have hin : traceIndexInput G x k Q (A r) (y r) a =
      traceIndexInput G x k Q (A r) (y r) b :=
    congrArg (fun z : SpliceState E × P × List (ℕ × E) => z.1) he
  have hcode : traceIndexCode G x k Q (A r) (y r) a =
      traceIndexCode G x k Q (A r) (y r) b :=
    congrArg (fun z : SpliceState E × P × List (ℕ × E) => z.2.2) he
  have hab : a = b := traceIndex_injective G x k Q (A r) (y r) (Prod.ext hin hcode)
  subst b
  rfl

noncomputable def finiteChoiceForwardLoad [Fintype P]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (q : SpliceState E → P → ℝ) : SpliceState E → ℝ :=
  finiteInverseLoad (choiceTraceOutput G x k Q A y) (choiceTraceMass G x k Q A y q)

 
theorem finiteChoiceForwardLoad_bounds [Fintype P]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x z : V) (k M : ℕ)
    (L : ℝ) (hL : 1 ≤ L) (Q : Finset E)
    (A : P → Finset (SpliceState E)) (y : P → SpliceState E → ℕ → V)
    (q : SpliceState E → P → ℝ) (hq : ∀ s r, 0 ≤ q s r)
    (hrow : ∀ s, ∑ r, q s r ≤ 1)
    (hA : ∀ r, A r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hz : ∀ r s, s ∈ A r → y r s k = z)
    (hgood : ∀ r s, s ∈ A r → ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (s.2 i) (y r s i)).Finite ∧
      (cluster G (s.2 i) (y r s i)).ncard ≤ M ∧ GoodForScale G (s.2 i) (y r s i) L)
    (t : SpliceState E) :
    0 ≤ finiteChoiceForwardLoad G x k Q A y q t ∧
      finiteChoiceForwardLoad G x k Q A y q t ≤ inverseCodeMass M L ^ k := by
  constructor
  · apply finiteInverseLoad_nonneg
    intro a
    exact mul_nonneg (hq _ _) (Finset.prod_nonneg (fun _ _ => by positivity))
  · apply finiteInverseLoad_weighted_le G hloc x z k M L hL
      (choiceTraceInput G x k Q A y) (choiceTraceOutput G x k Q A y)
      (choiceTraceCode G x k Q A y) (fun a => y a.1 a.2.1.val) Sigma.fst
      (choiceTrace_injective G x k Q A y) q hq hrow
      (fun a => (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).1)
      (fun a => (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).2)
      (fun a => hz a.1 _ a.2.1.property) _
      (fun a => hgood a.1 _ a.2.1.property) t
    intro a
    have hs := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) _).mp
      (traceIndexOutput_mem G x k Q (A a.1) (y a.1) (hA a.1) a.2)
    exact cluster_finite_of_finite_edges G (Q.finite_toSet.subset hs.1) x



end ChoiceForwardDensity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointRootMass
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def auxiliaryTupleWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (s : SpliceState E) : ℝ := ∏ i ∈ J, bernoulliWeight Q (domainBits Q (s.2 i)) p


theorem finiteRootLoad_eq_sum {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E) (m : I → ℝ)
    (hs : ∀ a, out a ∈ finiteSpliceDomain Q J) (ω : FiniteField Q) :
    finiteRootLoad Q J p (finiteInverseLoad out m) ω =
      ∑ a, if (out a).1 = finiteFieldSet Q ω then auxiliaryTupleWeight Q J p (out a) * m a else 0 := by
  simp only [finiteRootLoad,finiteInverseLoad,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  obtain ⟨⟨r,η⟩,_,ha⟩ := Finset.mem_image.mp (hs a)
  change (finiteFieldSet Q r,finiteFieldFamily Q J η) = out a at ha
  rw [← ha]
  have he (θ : ↥J → FiniteField Q) :
      (finiteFieldSet Q r,finiteFieldFamily Q J η) = (finiteFieldSet Q ω,finiteFieldFamily Q J θ) ↔
      r = ω ∧ η = θ := by
    constructor
    · intro h
      exact ⟨finiteFieldSet_injective Q (congrArg Prod.fst h),
        finiteFieldFamily_injective Q J (congrArg Prod.snd h)⟩
    · rintro ⟨rfl,rfl⟩; rfl
  simp only [he]
  by_cases hr : r = ω
  · subst r
    simp only [true_and,ite_true,Finset.sum_ite_eq,Finset.mem_univ]
    rw [auxiliaryTupleWeight,prod_fieldFamilyWeight]
  · have hr' : finiteFieldSet Q r ≠ finiteFieldSet Q ω := fun h => hr (finiteFieldSet_injective Q h)
    simp [hr,hr']



end EndpointRootMass
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NonnegativeTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

theorem mem_reachBall_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (ha : IsAut G a b) (x y : V) (n : ℕ) :
    a y ∈ reachBall G (a x) n ↔ y ∈ reachBall G x n := by
  constructor
  · intro h
    simpa only [Equiv.symm_apply_apply] using mem_reachBall_aut G (isAut_symm G ha) h
  · exact mem_reachBall_aut G ha


end NonnegativeTransport

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Transport_EndpointKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Kernels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalEndpointRule
attribute [local instance] Classical.propDecidable Classical.decEq

 

structure LocalEndpointRule (G : BondGraph V E) (hloc : LocallyFinite G)
    (O : Set V) (M : ℕ) (L : ℝ) where
  mass : Set E → V → V → ℝ
  radius : ℕ
  nonneg : ∀ ω x y, 0 ≤ mass ω x y
  row_le_one : ∀ ω x, (∑' y, mass ω x y) ≤ 1
  support : ∀ ω x y, mass ω x y ≠ 0 → x ∈ O ∧ y ∈ O ∧ Conn G ω x y ∧
    (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M ∧ GoodForScale G ω x L
  locality : ∀ ω x y, mass ω x y =
    mass (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x radius).toFinset : Set E)) x y
  covariance : ∀ (a : V ≃ V) (b : E ≃ E), IsAut G a b → ∀ ω x y,
    mass (b ⁻¹' ω) x y = mass ω (a x) (a y)

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

theorem outside_ball_zero (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x y : V)
    (hy : y ∉ reachBall G x M) : q.mass ω x y = 0 := by
  by_contra h
  obtain ⟨_,_,hc,hfin,hcap,_⟩ := q.support ω x y h
  exact hy (finite_cluster_subset_reachBall G ω x hfin M hcap hc)

theorem summable_mass (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) :
    Summable (q.mass ω x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro y hy
  apply q.outside_ball_zero ω x y
  simpa only [Set.Finite.mem_toFinset] using hy



noncomputable def kernel (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V) : ℝ :=
  ∫ ω, q.mass ω x y ∂law p

end LocalEndpointRule
end LocalEndpointRule

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalEndpointKernel
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}



noncomputable def successProbability (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) : ℝ :=
  ∑' y, q.kernel p x y

end LocalEndpointRule
end LocalEndpointKernel

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointSchur
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}


noncomputable def normalizedKernel (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval) (x y : V) : ℝ :=
  (q.successProbability p o)⁻¹ * q.kernel p x y



end LocalEndpointRule
end EndpointSchur

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
section FiniteLocalIntegral
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def finiteFieldEquiv (Q : Finset E) : FiniteField Q ≃ Set (Q : Set E) where
  toFun ω := Subtype.val ⁻¹' finiteFieldSet Q ω
  invFun η := ⟨η.toFinset.map ⟨Subtype.val,Subtype.val_injective⟩, by
    apply Finset.mem_powerset.mpr
    intro e he
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp he
    exact a.property⟩
  left_inv ω := by
    apply Subtype.ext
    apply Finset.coe_injective
    ext e
    simp only [Finset.coe_map,Set.mem_image,finiteFieldSet,Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨a,ha,rfl⟩
      have ha' : a ∈ (Subtype.val ⁻¹' (ω.val : Set E) : Set (Q : Set E)) := Set.mem_toFinset.mp ha
      exact ha'
    · intro he
      exact ⟨⟨e,Finset.mem_powerset.mp ω.property he⟩,Set.mem_toFinset.mpr he,rfl⟩
  right_inv η := by
    ext e
    simp only [Set.mem_preimage,finiteFieldSet,Finset.coe_map,Set.coe_toFinset,
      Set.mem_image,Function.Embedding.coeFn_mk,Subtype.val_injective.eq_iff,exists_eq_right]

@[simp] theorem finiteFieldEquiv_apply (Q : Finset E) (ω : FiniteField Q) :
    finiteFieldEquiv Q ω = Subtype.val ⁻¹' finiteFieldSet Q ω := rfl

@[simp] theorem finiteFieldEquiv_image (Q : Finset E) (ω : FiniteField Q) :
    Subtype.val '' finiteFieldEquiv Q ω = finiteFieldSet Q ω := by
  rw [finiteFieldEquiv_apply]
  apply Set.image_preimage_eq_of_subset
  intro e he
  exact ⟨⟨e,Finset.mem_powerset.mp ω.property he⟩,rfl⟩



end FiniteLocalIntegral

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GoodnessCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem internalEdges_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (W : Set V) :
    internalEdges G (a ⁻¹' W) = b ⁻¹' internalEdges G W := by
  ext e
  simp only [internalEdges,Set.mem_ofPred_eq,Set.mem_preimage,hab e,Sym2.mem_map]
  constructor
  · intro h y hy
    obtain ⟨z,hz,rfl⟩ := hy
    exact h z hz
  · intro h z hz
    exact h (a z) ⟨z,hz,rfl⟩

theorem cutExists_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (W : Set V) (e : E) :
    CutExists G (a ⁻¹' W) e ↔ CutExists G W (b e) := by
  constructor
  · rintro ⟨u,v,he,hu,hv⟩
    exact ⟨a u,a v,by rw [hab e,he,Sym2.map_mk],hu,hv⟩
  · rintro ⟨u,v,he,hu,hv⟩
    refine ⟨a.symm u,a.symm v,?_,by simpa using hu,by simpa using hv⟩
    have h := congrArg (Sym2.map a.symm) he
    simpa only [hab e,Sym2.map_map,Equiv.symm_comp_self,id_eq,Sym2.map_id',Sym2.map_mk] using h

theorem contactSet_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (W : Set V) :
    contactSet G (b ⁻¹' ω) (a ⁻¹' W) = b ⁻¹' contactSet G ω W := by
  ext e
  simp only [contactSet,Set.mem_ofPred_eq,Set.mem_preimage,cutExists_aut_preimage G hab]

theorem openMarkedPivotal_pair_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) (e : E) :
    OpenMarkedPivotal G (b ⁻¹' ω) {y} x e ↔
      OpenMarkedPivotal G ω {a y} (a x) (b e) := by
  have he : (b ⁻¹' ω) \ {e} = b ⁻¹' (ω \ {b e}) := by
    ext f
    simp only [Set.mem_sdiff,Set.mem_preimage,Set.mem_singleton_iff,b.injective.eq_iff]
  simp only [OpenMarkedPivotal,MarkedEvent,Set.mem_singleton_iff,exists_eq_left,
    Set.mem_preimage,he,conn_aut_iff G hab]

theorem pivotalDistance_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) :
    pivotalDistance G (b ⁻¹' ω) x y = pivotalDistance G ω (a x) (a y) := by
  have he : {e | OpenMarkedPivotal G (b ⁻¹' ω) {y} x e} =
      b ⁻¹' {e | OpenMarkedPivotal G ω {a y} (a x) e} := by
    ext e
    exact openMarkedPivotal_pair_aut G hab ω x y e
  rw [pivotalDistance,he,Set.ncard_preimage_of_injective_subset_range b.injective]
  · rfl
  · exact fun e _ => b.surjective e

theorem goodForScale_aut_pullback (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) (L : ℝ)
    (hg : GoodForScale G ω (a x) L) : GoodForScale G (b ⁻¹' ω) x L := by
  intro W hW hconn hpos u hu v hv
  let W' := W.map a.toEmbedding
  have hpre : a ⁻¹' (W' : Set V) = (W : Set V) := by
    ext z
    simp [W']
  have hcfg : b ⁻¹' (ω ∩ internalEdges G (W' : Set V)) =
      (b ⁻¹' ω) ∩ internalEdges G (W : Set V) := by
    rw [Set.preimage_inter,← internalEdges_aut_preimage G hab,hpre]
  have hcontact : (contactSet G (b ⁻¹' ω) (W : Set V)).ncard =
      (contactSet G ω (W' : Set V)).ncard := by
    rw [← hpre,contactSet_aut_preimage G hab,
      Set.ncard_preimage_of_injective_subset_range b.injective]
    exact fun e _ => b.surjective e
  have hW' : (W' : Set V) ⊆ cluster G ω (a x) := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hz
    exact (conn_aut_iff G hab ω x w).mp (hW hw)
  have hc' : ∀ w ∈ W', ∀ z ∈ W', Conn G (ω ∩ internalEdges G (W' : Set V)) w z := by
    intro w hw z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hz
    apply (conn_aut_iff G hab _ u v).mp
    rw [hcfg]
    exact hconn u hu v hv
  have H := hg W' hW' hc' (by rwa [← hcontact]) (a u)
    (Finset.mem_map.mpr ⟨u,hu,rfl⟩) (a v) (Finset.mem_map.mpr ⟨v,hv,rfl⟩)
  rw [← pivotalDistance_aut_preimage G hab,hcfg,← hcontact] at H
  exact H

theorem goodForScale_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) (L : ℝ) :
    GoodForScale G (b ⁻¹' ω) x L ↔ GoodForScale G ω (a x) L := by
  constructor
  · intro h
    have H := goodForScale_aut_pullback G (isAut_symm G hab) (b ⁻¹' ω) (a x) L
      (by simpa only [Equiv.symm_apply_apply] using h)
    simpa only [← Set.preimage_comp,Equiv.self_comp_symm,Set.preimage_id_eq,id_eq] using H
  · exact goodForScale_aut_pullback G hab ω x L

end GoodnessCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CappedGoodLocality
attribute [local instance] Classical.propDecidable Classical.decEq

def CappedGoodness (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) (L : ℝ) : Prop :=
  (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M ∧ GoodForScale G ω x L

theorem cappedGoodness_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (L : ℝ) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    CappedGoodness G ω x M L ↔ CappedGoodness G (ω ∩ (Q : Set E)) x M L := by
  have he (η : Set E) : CappedGoodness G η x M L ↔
      ((cluster G η x).Finite ∧ (cluster G η x).ncard ≤ M) ∧ ¬CappedBadGoodness G η x M L := by
    constructor
    · rintro ⟨hf,hM,hg⟩
      exact ⟨⟨hf,hM⟩,fun h => h.2.2 hg⟩
    · rintro ⟨⟨hf,hM⟩,hbad⟩
      refine ⟨hf,hM,?_⟩
      by_contra hn
      exact hbad ⟨hf,hM,hn⟩
  dsimp only
  have hbad := cappedBadGoodness_local G hloc x M L ω
  have hcap := capped_cluster_local G hloc x M ω
  dsimp only at hbad hcap
  rw [he,he,hbad,hcap]

theorem cappedGoodness_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) (M : ℕ) (L : ℝ) :
    CappedGoodness G (b ⁻¹' ω) x M L ↔ CappedGoodness G ω (a x) M L := by
  have hf : (cluster G (b ⁻¹' ω) x).Finite ↔ (cluster G ω (a x)).Finite := by
    rw [← cluster_aut G hab ω x]
    exact (Set.finite_image_iff a.injective.injOn).symm
  have hn : (cluster G (b ⁻¹' ω) x).ncard = (cluster G ω (a x)).ncard := by
    rw [← cluster_aut G hab ω x,Set.ncard_image_of_injective _ a.injective]
  simp only [CappedGoodness,hf,hn,goodForScale_aut_iff G hab]

theorem incidentSupport_ball_mono (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) {r R : ℕ} (h : r ≤ R) :
    incidentSupport G hloc (finite_reachBall hloc x r).toFinset ⊆
      incidentSupport G hloc (finite_reachBall hloc x R).toFinset := by
  apply incidentSupport_mono
  intro z hz
  simp only [Set.Finite.mem_toFinset] at hz ⊢
  exact reachBall_mono_local G x h hz

theorem finite_local_of_subset (Q S : Finset E) (hQS : Q ⊆ S) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) (ω : Set E) :
    f ω = f (ω ∩ (S : Set E)) := by
  rw [hf ω,hf (ω ∩ (S : Set E))]
  congr 1
  exact (Set.inter_assoc _ _ _).trans (congrArg (ω ∩ ·) (Set.inter_eq_right.mpr hQS)) |>.symm

end CappedGoodLocality

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CappedLocalLoad
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_prop_local_of_subset (Q S : Finset E) (hQS : Q ⊆ S) (P : Set E → Prop)
    (hf : ∀ ω, P ω ↔ P (ω ∩ (Q : Set E))) (ω : Set E) :
    P ω ↔ P (ω ∩ (S : Set E)) := by
  have he : (ω ∩ (S : Set E)) ∩ (Q : Set E) = ω ∩ (Q : Set E) :=
    (Set.inter_assoc _ _ _).trans (congrArg (ω ∩ ·) (Set.inter_eq_right.mpr hQS))
  exact (hf ω).trans ((he ▸ hf (ω ∩ (S : Set E))).symm)

 

structure CappedLocalLoad (G : BondGraph V E) (hloc : LocallyFinite G) (O : Set V) (M : ℕ) where
  mass : Set E → V → V → ℝ
  radius : ℕ
  nonneg : ∀ ω x y, 0 ≤ mass ω x y
  support : ∀ ω x y, mass ω x y ≠ 0 → x ∈ O ∧ y ∈ O ∧ Conn G ω x y ∧
    (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M
  locality : ∀ ω x y, mass ω x y =
    mass (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x radius).toFinset : Set E)) x y
  covariance : ∀ (a : V ≃ V) (b : E ≃ E), IsAut G a b → ∀ ω x y,
    mass (b ⁻¹' ω) x y = mass ω (a x) (a y)

namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

noncomputable def row (q : CappedLocalLoad G hloc O M) (ω : Set E) (x : V) : ℝ :=
  ∑' y, q.mass ω x y

theorem row_locality (q : CappedLocalLoad G hloc O M) (ω : Set E) (x : V) :
    q.row ω x = q.row
      (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x q.radius).toFinset : Set E)) x :=
  tsum_congr (q.locality ω x)

theorem row_covariance (q : CappedLocalLoad G hloc O M) (a : V ≃ V) (b : E ≃ E)
    (hab : IsAut G a b) (ω : Set E) (x : V) : q.row (b ⁻¹' ω) x = q.row ω (a x) := by
  unfold row
  simp_rw [q.covariance a b hab]
  exact a.tsum_eq _



noncomputable def truncate (q : CappedLocalLoad G hloc O M) (b : ℝ) (hb : 0 < b) (L : ℝ) :
    LocalEndpointRule G hloc O M L where
  mass ω x y := if q.row ω x ≤ b ∧ CappedGoodness G ω x M L then b⁻¹ * q.mass ω x y else 0
  radius := max q.radius M
  nonneg ω x y := by split_ifs; exact mul_nonneg (inv_nonneg.mpr hb.le) (q.nonneg ω x y); rfl
  row_le_one ω x := by
    by_cases h : q.row ω x ≤ b ∧ CappedGoodness G ω x M L
    · simp only [h,and_self,ite_true,tsum_mul_left]
      exact (mul_le_mul_of_nonneg_left h.1 (inv_nonneg.mpr hb.le)).trans_eq (inv_mul_cancel₀ hb.ne')
    · simp only [h,ite_false,tsum_zero,zero_le_one]
  support ω x y h := by
    split_ifs at h with hkeep
    · have hm : q.mass ω x y ≠ 0 := fun he => h (by rw [he,mul_zero])
      obtain ⟨hx,hy,hc,_,_⟩ := q.support ω x y hm
      exact ⟨hx,hy,hc,hkeep.2⟩
    · exact (h rfl).elim
  locality ω x y := by
    let S := incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset
    have hm := finite_local_of_subset _ S
      (incidentSupport_ball_mono G hloc x (le_max_left q.radius M))
      (fun η => q.mass η x y) (q.locality · x y) ω
    have hr := finite_local_of_subset _ S
      (incidentSupport_ball_mono G hloc x (le_max_left q.radius M))
      (fun η => q.row η x) (q.row_locality · x) ω
    have hg := finite_prop_local_of_subset _ S
      (incidentSupport_ball_mono G hloc x (le_max_right q.radius M))
      (fun η => CappedGoodness G η x M L) (fun η => cappedGoodness_local G hloc η x M L) ω
    simp only [hm,hr,hg]
    rfl
  covariance a c hac ω x y := by
    simp only [q.row_covariance a c hac,q.covariance a c hac,cappedGoodness_aut_iff G hac]

end CappedLocalLoad
end CappedLocalLoad

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CategoricalAmplificationInput
attribute [local instance] Classical.propDecidable Classical.decEq

 

def amplificationVertices (B : Finset V) (k : ℕ) (z : ↥B) (r : Fin k → ↥B) : ℕ → V :=
  fun i => (oldRunVertices k z r i).val

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def amplificationWeight (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (z : ↥B) (s : SpliceState E) (r : Fin k → ↥B) : ℝ :=
  oldRunWeight (fun i a b => q.mass (s.2 i) a.val b.val) k z r

theorem amplificationWeight_eq (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (z : ↥B) (s : SpliceState E) (r : Fin k → ↥B) :
    q.amplificationWeight B k z s r = oldPathWeight k q.mass (amplificationVertices B k z r) s.2 := by
  exact (oldPathWeight_oldRunVertices k (fun ω a b => q.mass ω a.val b.val) s.2 z r).symm

theorem amplificationWeight_nonneg (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (z : ↥B) (s : SpliceState E) (r : Fin k → ↥B) :
    0 ≤ q.amplificationWeight B k z s r :=
  oldRunWeight_nonneg (fun i (a b : ↥B) => q.mass (s.2 i) a.val b.val)
    (fun i a b => q.nonneg (s.2 i) a.val b.val) k z r

theorem amplificationWeight_row (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (z : ↥B) (s : SpliceState E) :
    (∑ r, q.amplificationWeight B k z s r) ≤ 1 := by
  have hr (i : ℕ) (a : ↥B) : (∑ b : ↥B, q.mass (s.2 i) a.val b.val) ≤ 1 := by
    rw [Finset.sum_coe_sort B]
    exact ((q.summable_mass _ _).sum_le_tsum B (fun y _ => q.nonneg _ _ y)).trans (q.row_le_one _ _)
  simpa only [one_pow,amplificationWeight] using sum_oldRunWeight_le
    (fun i (a b : ↥B) => q.mass (s.2 i) a.val b.val)
    (fun _ a b => q.nonneg _ a.val b.val) 1 zero_le_one hr k z

 

noncomputable def amplificationInputs (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) : Finset (SpliceState E) :=
  (finiteSpliceDomain Q (Finset.Icc 1 k)).filter fun s =>
    x ∈ O ∧ z.val ∈ O ∧ n ≤ (cluster G s.1 x).ncard ∧ (cluster G s.1 x).ncard < 2*n ∧
      amplificationVertices B k z r 0 ∈ cluster G s.1 x ∧ q.amplificationWeight B k z s r ≠ 0

theorem mem_amplificationInputs (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) (s : SpliceState E) :
    s ∈ q.amplificationInputs Q B x k n z r ↔
      s ∈ finiteSpliceDomain Q (Finset.Icc 1 k) ∧
      x ∈ O ∧ z.val ∈ O ∧ n ≤ (cluster G s.1 x).ncard ∧ (cluster G s.1 x).ncard < 2*n ∧
      amplificationVertices B k z r 0 ∈ cluster G s.1 x ∧ q.amplificationWeight B k z s r ≠ 0 :=
  Finset.mem_filter

theorem amplificationInputs_subset (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) :
    q.amplificationInputs Q B x k n z r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k) :=
  Finset.filter_subset _ _

theorem amplificationInputs_chain (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) (s : SpliceState E)
    (hs : s ∈ q.amplificationInputs Q B x k n z r) :
    ∀ i, 1 ≤ i → i ≤ k →
      Conn G (s.2 i) (amplificationVertices B k z r i) (amplificationVertices B k z r (i-1)) ∧
      (cluster G (s.2 i) (amplificationVertices B k z r i)).Finite ∧
      (cluster G (s.2 i) (amplificationVertices B k z r i)).ncard ≤ M ∧
      GoodForScale G (s.2 i) (amplificationVertices B k z r i) L := by
  apply oldPathWeight_support G k M L q.mass
  · intro ω a b h
    exact (q.support ω a b h).2.2
  · exact (q.amplificationWeight_eq B k z s r) ▸ ((q.mem_amplificationInputs Q B x k n z r s).mp hs).2.2.2.2.2.2

 

theorem amplificationTrace_support (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) (s : SpliceState E)
    (hs : s ∈ q.amplificationInputs Q B x k n z r) (c : List (ℕ × E)) (ωf : Set E)
    (ht : SpliceTrace G x s.2 (amplificationVertices B k z r) k 0 s.1 c ωf) :
    x ∈ O ∧ z.val ∈ O ∧ Conn G ωf x z.val ∧ (cluster G ωf x).Finite ∧
      (cluster G ωf x).ncard ≤ 2*n+k*M := by
  obtain ⟨hdom,hx,hz,_,hbin,_,_⟩ := (q.mem_amplificationInputs Q B x k n z r s).mp hs
  have hc := q.amplificationInputs_chain Q B x k n z r s hs
  have hroot : (cluster G s.1 x).Finite :=
    cluster_finite_of_finite_edges G (Q.finite_toSet.subset
      ((mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) s).mp hdom).1) x
  obtain ⟨hf,hcap⟩ := trajectoryUnion_finite_cap G s.2 (amplificationVertices B k z r) k M
    (fun i hi hik => ⟨(hc i hi hik).2.1,(hc i hi hik).2.2.1⟩)
  have hsub : cluster G ωf x ⊆ cluster G s.1 x ∪ trajectoryUnion G s.2 (amplificationVertices B k z r) k := by
    intro v hv
    by_cases hv' : v ∈ cluster G s.1 x
    · exact Or.inl hv'
    · exact Or.inr (ht.added_subset_trajectory G x s.2 (amplificationVertices B k z r) k 0 s.1 ωf c ⟨hv,hv'⟩)
  refine ⟨hx,hz,?_,(hroot.union hf).subset hsub,?_⟩
  · simpa only [amplificationVertices,oldRunVertices_last,cluster,Set.mem_ofPred_eq] using
      ht.endpoint G x s.2 (amplificationVertices B k z r) k 0 s.1 ωf c
  · exact (Set.ncard_le_ncard hsub (hroot.union hf)).trans
      ((Set.ncard_union_le ..).trans (Nat.add_le_add (by omega) hcap))

end LocalEndpointRule
end CategoricalAmplificationInput

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AmplificationMarginal
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def restrictFiniteField (Q : Finset E) (ω : Set E) : FiniteField Q :=
  ⟨domainBits Q ω,Finset.mem_powerset.mpr (domainBits_subset Q ω)⟩

@[simp] theorem finiteFieldSet_restrict (Q : Finset E) (ω : Set E) :
    finiteFieldSet Q (restrictFiniteField Q ω) = ω ∩ (Q : Set E) := by
  ext e
  simp [restrictFiniteField,domainBits,finiteFieldSet,and_comm]

@[simp] theorem restrictFiniteField_fieldSet (Q : Finset E) (ω : FiniteField Q) :
    restrictFiniteField Q (finiteFieldSet Q ω) = ω := by
  apply Subtype.ext
  exact domainBits_finiteFieldSet Q ω

theorem cluster_restrict_of_cap (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (ω : Set E) (x : V) (C : ℕ)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x C).toFinset ⊆ Q)
    (hf : (cluster G (ω ∩ (Q : Set E)) x).Finite)
    (hC : (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ C) :
    cluster G (ω ∩ (Q : Set E)) x = cluster G ω x := by
  apply Set.Subset.antisymm
  · exact fun _ h => conn_mono G Set.inter_subset_left h
  · intro y hy
    induction hy with
    | refl => exact conn_refl G _ x
    | @tail a b _ hab ih =>
      obtain ⟨e,he,hab⟩ := hab
      have ha := finite_cluster_subset_reachBall G (ω ∩ (Q : Set E)) x hf C hC ih
      have heQ := hQ ((mem_incidentSupport G hloc _ e).mpr
        ⟨a,by simpa only [Set.Finite.mem_toFinset] using ha,by simp [hab]⟩)
      exact ih.tail ⟨e,⟨he,heQ⟩,hab⟩

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

noncomputable def amplificationMarginal (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E) : ℝ :=
  finiteRootLoad Q (Finset.Icc 1 k) p
    (finiteChoiceForwardLoad G x k Q (q.amplificationInputs Q B x k n z)
      (fun r _ => amplificationVertices B k z r) (q.amplificationWeight B k z)) (restrictFiniteField Q ω)

theorem amplificationMarginal_local (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E) :
    q.amplificationMarginal Q B x k n z p ω =
      q.amplificationMarginal Q B x k n z p (ω ∩ (Q : Set E)) := by
  unfold amplificationMarginal
  congr 1
  apply (finiteFieldSet_injective Q)
  simp only [finiteFieldSet_restrict,Set.inter_assoc,Set.inter_self]

theorem amplificationMarginal_bounds (q : LocalEndpointRule G hloc O M L) (hL : 1 ≤ L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E) :
    0 ≤ q.amplificationMarginal Q B x k n z p ω ∧
      q.amplificationMarginal Q B x k n z p ω ≤ inverseCodeMass M L ^ k := by
  have hb := finiteChoiceForwardLoad_bounds G hloc x z.val k M L hL Q
    (q.amplificationInputs Q B x k n z) (fun r _ => amplificationVertices B k z r)
    (q.amplificationWeight B k z) (q.amplificationWeight_nonneg B k z)
    (q.amplificationWeight_row B k z) (q.amplificationInputs_subset Q B x k n z)
    (fun _ _ _ => congrArg Subtype.val (oldRunVertices_last ..))
    (fun r s hs i hi hik => (q.amplificationInputs_chain Q B x k n z r s hs i hi hik).2)
  exact ⟨finiteRootLoad_nonneg _ _ p _ (fun s _ => (hb s).1) _,
    finiteRootLoad_le _ _ p _ _ (fun s _ => (hb s).2) _⟩

theorem amplificationMarginal_support (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E)
    (h : q.amplificationMarginal Q B x k n z p ω ≠ 0) :
    x ∈ O ∧ z.val ∈ O ∧ Conn G (ω ∩ (Q : Set E)) x z.val ∧
      (cluster G (ω ∩ (Q : Set E)) x).Finite ∧
      (cluster G (ω ∩ (Q : Set E)) x).ncard ≤ 2*n+k*M := by
  let A := q.amplificationInputs Q B x k n z
  let y := fun r (_ : SpliceState E) => amplificationVertices B k z r
  let I := FiniteChoiceTraceIndex G x k Q A y
  let out := choiceTraceOutput G x k Q A y
  have ho (a : I) : out a ∈ finiteSpliceDomain Q (Finset.Icc 1 k) :=
    traceIndexOutput_mem G x k Q (A a.1) (y a.1) (q.amplificationInputs_subset Q B x k n z a.1) a.2
  have he := finiteRootLoad_eq_sum Q (Finset.Icc 1 k) p out
    (choiceTraceMass G x k Q A y (q.amplificationWeight B k z)) ho (restrictFiniteField Q ω)
  have ha : ∃ a : I, (out a).1 = ω ∩ (Q : Set E) := by
    by_contra hn
    push Not at hn
    apply h
    change finiteRootLoad Q (Finset.Icc 1 k) p (finiteInverseLoad out _) _ = 0
    rw [he,finiteFieldSet_restrict]
    simp only [hn,ite_false,Finset.sum_const_zero]
  obtain ⟨a,ha⟩ := ha
  have ht := (traceIndex_valid G x k Q (A a.1) (y a.1) a.2).1
  have hs := q.amplificationTrace_support Q B x k n z a.1 a.2.1.val a.2.1.property
    (choiceTraceCode G x k Q A y a) (out a).1 ht
  rwa [ha] at hs

theorem amplificationMarginal_physical_support (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x (2*n+k*M)).toFinset ⊆ Q)
    (h : q.amplificationMarginal Q B x k n z p ω ≠ 0) :
    x ∈ O ∧ z.val ∈ O ∧ Conn G ω x z.val ∧ (cluster G ω x).Finite ∧
      (cluster G ω x).ncard ≤ 2*n+k*M := by
  obtain ⟨hx,hz,hc,hf,hcap⟩ := q.amplificationMarginal_support Q B x k n z p ω h
  have he := cluster_restrict_of_cap G hloc Q ω x (2*n+k*M) hQ hf hcap
  exact ⟨hx,hz,conn_mono G Set.inter_subset_left hc,he ▸ hf,he ▸ hcap⟩



end LocalEndpointRule
end AmplificationMarginal

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinConnection
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def binConnectionMass (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) : ℝ :=
  if (cluster G ω x).Finite ∧ n ≤ (cluster G ω x).ncard ∧
    (cluster G ω x).ncard < 2*n ∧ Conn G ω x y then 1 else 0

noncomputable def binConnection (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V) : ℝ :=
  ∫ ω, binConnectionMass G n ω x y ∂law p

end BinConnection

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PositivePathOperator
attribute [local instance] Classical.propDecidable Classical.decEq

 
def PositiveRealMatrix (A : Hilbert V →L[ℂ] Hilbert V) : Prop :=
  ∀ x y, (matrixCoeff A x y).im = 0 ∧ 0 ≤ (matrixCoeff A x y).re

end PositivePathOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrbitBinOperator
attribute [local instance] Classical.propDecidable Classical.decEq

theorem isAut_trans (G : BondGraph V E) {a c : V ≃ V} {b d : E ≃ E}
    (hab : IsAut G a b) (hcd : IsAut G c d) : IsAut G (a.trans c) (b.trans d) := by
  intro e
  change G (d (b e)) = (G e).map (c ∘ a)
  rw [hcd,hab,Sym2.map_map]

theorem mem_vertexOrbit_aut_iff (G : BondGraph V E) (o : V) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) : a x ∈ vertexOrbit G o ↔ x ∈ vertexOrbit G o := by
  constructor
  · rintro ⟨c,d,hcd,hc⟩
    refine ⟨c.trans a.symm,d.trans b.symm,isAut_trans G hcd (isAut_symm G hab),?_⟩
    simp only [Equiv.trans_apply,hc,Equiv.symm_apply_apply]
  · rintro ⟨c,d,hcd,rfl⟩
    exact ⟨c.trans a,d.trans b,isAut_trans G hcd hab,rfl⟩


noncomputable def orbitBinConnection (G : BondGraph V E) (p : unitInterval) (o : V)
    (n : ℕ) (x y : V) : ℝ :=
  if x ∈ vertexOrbit G o ∧ y ∈ vertexOrbit G o then binConnection G p n x y else 0

noncomputable def binOrbitRow (G : BondGraph V E) (p : unitInterval) (o : V) (n : ℕ) : ℝ :=
  ∑' y, orbitBinConnection G p o n o y

end OrbitBinOperator

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterVisitKernel
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def conditionalSuccess (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) : ℝ :=
  ∑' y, q.mass ω x y



noncomputable def clusterVisitMass (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x a : V) : ℝ :=
  if a ∈ cluster G ω x then q.conditionalSuccess ω x else 0

noncomputable def clusterVisitKernel (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (x a : V) : ℝ := ∫ ω, q.clusterVisitMass ω x a ∂law p

end LocalEndpointRule
end ClusterVisitKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section VisitEnvelope
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

noncomputable def visitEnvelope (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) : ℕ → V → V → ℝ
  | 0, _, _ => 0
  | k+1, x, a => q.successProbability p o ^ k * q.clusterVisitKernel p x a +
      ∑' y, q.kernel p x y * q.visitEnvelope o p k y a

end LocalEndpointRule
end VisitEnvelope

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Splicing_EndpointMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointHit
attribute [local instance] Classical.propDecidable Classical.decEq



noncomputable def allAmplificationVertices (B : Finset V) (k : ℕ)
    (r : ↥B × (Fin k → ↥B)) (_η : ℕ → Set E) : ℕ → V :=
  amplificationVertices B k r.1 r.2

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def allAmplificationWeight (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (r : ↥B × (Fin k → ↥B)) (η : ℕ → Set E) : ℝ :=
  oldRunWeight (fun i (a b : ↥B) => q.mass (η i) a.val b.val) k r.1 r.2

noncomputable def allAmplificationInputs (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ)
    (r : ↥B × (Fin k → ↥B)) : Finset (SpliceState E) :=
  q.amplificationInputs Q B x k n r.1 r.2

end LocalEndpointRule
end AllEndpointHit

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointMarginal
attribute [local instance] Classical.propDecidable Classical.decEq


namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

abbrev AmplificationIndex (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) :=
  FiniteChoiceTraceIndex G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2)

noncomputable def amplificationOutput (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) : q.AmplificationIndex Q B x k n → SpliceState E :=
  choiceTraceOutput G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2)

noncomputable def amplificationInput (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) : q.AmplificationIndex Q B x k n → SpliceState E :=
  choiceTraceInput G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2)

noncomputable def amplificationCode (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) : q.AmplificationIndex Q B x k n → List (ℕ × E) :=
  choiceTraceCode G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2)

noncomputable def amplificationMass (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) : q.AmplificationIndex Q B x k n → ℝ :=
  choiceTraceMass G x k Q (q.allAmplificationInputs Q B x k n)
    (fun r s => allAmplificationVertices B k r s.2) (fun s r => q.allAmplificationWeight B k r s.2)

noncomputable def amplificationRow (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : Set E) : ℝ :=
  ∑ z : ↥B, q.amplificationMarginal Q B x k n z p ω

end LocalEndpointRule
end AllEndpointMarginal

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NoSwitchDensity
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] theorem SpliceExecution.nil_iff (G : BondGraph V E) (x : V) (s t : SpliceState E) :
    SpliceExecution G x s [] t ↔ s = t := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact SpliceExecution.nil s

end NoSwitchDensity

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AllEndpointNil
attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def amplificationNilRow (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) (ω : FiniteField Q) : ℝ :=
  finiteRootLoad Q (Finset.Icc 1 k) p
    (finiteInverseLoad (q.amplificationOutput Q B x k n)
      (fun a => if q.amplificationCode Q B x k n a = [] then q.amplificationMass Q B x k n a else 0)) ω



end LocalEndpointRule
end AllEndpointNil

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AllEndpointNear
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def amplificationAdded (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (a : q.AmplificationIndex Q B x k n) : Set V :=
  cluster G (q.amplificationOutput Q B x k n a).1 x \ cluster G (q.amplificationInput Q B x k n a).1 x

noncomputable def amplificationNearPairMass (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (p : unitInterval) : ℝ :=
  ∑ a : q.AmplificationIndex Q B x k n, ∑ b : q.AmplificationIndex Q B x k n,
    if (q.amplificationOutput Q B x k n a).1 = (q.amplificationOutput Q B x k n b).1 ∧
      q.amplificationCode Q B x k n a ≠ [] ∧ q.amplificationCode Q B x k n b ≠ [] ∧
      ¬GraphSeparated G (q.amplificationAdded Q B x k n a) (q.amplificationAdded Q B x k n b)
    then jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (pairSpliceOutput (q.amplificationOutput Q B x k n a) (q.amplificationOutput Q B x k n b)) *
        q.amplificationMass Q B x k n a * q.amplificationMass Q B x k n b else 0



end LocalEndpointRule
end AllEndpointNear

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteThreeClass
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def commonRootPairMass {I : Type*} [Fintype I]
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (out : I → SpliceState E)
    (m : I → ℝ) (P : I → I → Prop) : ℝ :=
  ∑ a, ∑ b, if (out a).1 = (out b).1 ∧ P a b then
    jointTupleWeight Q J J p (pairSpliceOutput (out a) (out b)) * m a * m b else 0



end FiniteThreeClass

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SpliceCovarianceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    cluster G (b ⁻¹' ω) x = a ⁻¹' cluster G ω (a x) := by
  ext y
  exact conn_aut_iff G hab ω x y

theorem exchangeOn_preimage (b : E ≃ E) (mask ω η : Set E) :
    exchangeOn (b ⁻¹' mask) (b ⁻¹' ω) (b ⁻¹' η) = b ⁻¹' exchangeOn mask ω η := by
  rfl

theorem spliceMask_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (S B : Set V) (e : E) :
    spliceMask G (a ⁻¹' S) (a ⁻¹' B) e = b ⁻¹' spliceMask G S B (b e) := by
  ext f
  simp only [spliceMask,Set.mem_insert_iff,Set.mem_ofPred_eq,Set.mem_preimage,b.injective.eq_iff]
  apply or_congr_right
  have hi : internalEdges G (a ⁻¹' S)ᶜ = b ⁻¹' internalEdges G Sᶜ :=
    internalEdges_aut_preimage G hab Sᶜ
  rw [hi]
  apply and_congr_left
  intro _
  constructor
  · rintro ⟨v,hv,hvf⟩
    refine ⟨a v,hv,?_⟩
    rw [hab f]
    exact Sym2.mem_map.mpr ⟨v,hvf,rfl⟩
  · rintro ⟨v,hv,hvf⟩
    rw [hab f] at hvf
    obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hvf
    exact ⟨w,hv,hw⟩

theorem spliceField_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (S B : Set V) (e : E) (ω η : Set E) :
    spliceField G (a ⁻¹' S) (a ⁻¹' B) e (b ⁻¹' ω) (b ⁻¹' η) =
      b ⁻¹' spliceField G S B (b e) ω η := by
  rw [spliceField,spliceMask_aut_preimage G hab,exchangeOn_preimage]
  rfl

theorem seamContactCount_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (η : ℕ → Set E) (y : ℕ → V) (ωf : Set E) (x : V) (i : ℕ) (e : E) :
    seamContactCount G (fun j => b ⁻¹' η j) y (b ⁻¹' ωf) x i e =
      seamContactCount G η (fun j => a (y j)) ωf (a x) i (b e) := by
  have he : (b ⁻¹' ωf) \ {e} = b ⁻¹' (ωf \ {b e}) := by
    ext f
    simp only [Set.mem_sdiff,Set.mem_preimage,Set.mem_singleton_iff,b.injective.eq_iff]
  unfold seamContactCount
  rw [he,cluster_aut_preimage G hab]
  rw [show (a ⁻¹' cluster G (ωf \ {b e}) (a x))ᶜ =
    a ⁻¹' (cluster G (ωf \ {b e}) (a x))ᶜ from rfl]
  rw [internalEdges_aut_preimage G hab,← Set.preimage_inter,cluster_aut_preimage G hab,
    contactSet_aut_preimage G hab,Set.ncard_preimage_of_injective_subset_range b.injective]
  exact fun f _ => b.surjective f

end SpliceCovarianceGeometry

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SpliceCovarianceTrace
attribute [local instance] Classical.propDecidable Classical.decEq

 

def edgeFieldEquiv (b : E ≃ E) : Set E ≃ Set E where
  toFun ω := b.symm ⁻¹' ω
  invFun ω := b ⁻¹' ω
  left_inv ω := by ext e; simp
  right_inv ω := by ext e; simp

def spliceStateEquiv (b : E ≃ E) : SpliceState E ≃ SpliceState E :=
  (edgeFieldEquiv b).prodCongr (Equiv.piCongrRight fun _ => edgeFieldEquiv b)

def spliceCodeEquiv (b : E ≃ E) : List (ℕ × E) ≃ List (ℕ × E) :=
  Equiv.listEquivOfEquiv ((Equiv.refl ℕ).prodCongr b)

@[simp] theorem edgeFieldEquiv_apply (b : E ≃ E) (ω : Set E) :
    edgeFieldEquiv b ω = b.symm ⁻¹' ω := rfl

@[simp] theorem spliceCodeEquiv_apply (b : E ≃ E) (c : List (ℕ × E)) :
    spliceCodeEquiv b c = c.map (Prod.map id b) := rfl

theorem cluster_edgeFieldEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    cluster G (edgeFieldEquiv b ω) (a x) = a.symm ⁻¹' cluster G ω x := by
  simpa only [edgeFieldEquiv_apply,Equiv.symm_apply_apply] using
    cluster_aut_preimage G (isAut_symm G hab) ω (a x)

theorem slitCluster_edgeFieldEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω η : Set E) (x y : V) :
    cluster G (edgeFieldEquiv b η ∩ internalEdges G (cluster G (edgeFieldEquiv b ω) (a x))ᶜ) (a y) =
      a.symm ⁻¹' cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y := by
  rw [cluster_edgeFieldEquiv G hab]
  rw [show (a.symm ⁻¹' cluster G ω x)ᶜ = a.symm ⁻¹' (cluster G ω x)ᶜ from rfl]
  rw [internalEdges_aut_preimage G (isAut_symm G hab),edgeFieldEquiv_apply,← Set.preimage_inter,
    cluster_aut_preimage G (isAut_symm G hab),Equiv.symm_apply_apply]

theorem spliceStep_edgeFieldEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω η : Set E) (x y : V) (e : E) :
    spliceField G (cluster G (edgeFieldEquiv b ω) (a x))
      (cluster G (edgeFieldEquiv b η ∩ internalEdges G (cluster G (edgeFieldEquiv b ω) (a x))ᶜ) (a y))
      (b e) (edgeFieldEquiv b ω) (edgeFieldEquiv b η) =
    edgeFieldEquiv b (spliceField G (cluster G ω x)
      (cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) e ω η) := by
  rw [slitCluster_edgeFieldEquiv G hab,cluster_edgeFieldEquiv G hab]
  rw [edgeFieldEquiv_apply,edgeFieldEquiv_apply,
    spliceField_aut_preimage G (isAut_symm G hab),Equiv.symm_apply_apply]
  rfl

 

theorem SpliceTrace.aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ)
    (ω ωf : Set E) (c : List (ℕ × E)) (ht : SpliceTrace G x η y k j ω c ωf) :
    SpliceTrace G (a x) (fun i => edgeFieldEquiv b (η i)) (fun i => a (y i)) k j
      (edgeFieldEquiv b ω) (spliceCodeEquiv b c) (edgeFieldEquiv b ωf) := by
  induction ht with
  | stop j ω hs =>
    apply SpliceTrace.stop
    simpa only [cluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hs
  | step j i ω e v w rest ωf hn hji hik hmax hy he hev hv hw ht ih =>
    change SpliceTrace G (a x) _ _ k j _ ((i,b e)::spliceCodeEquiv b rest) _
    refine SpliceTrace.step j i _ (b e) (a v) (a w) _ _ ?_ hji hik ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [cluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hn
    · intro l hil hlk
      rw [cluster_edgeFieldEquiv G hab,cluster_edgeFieldEquiv G hab,
        Set.disjoint_preimage_iff a.symm.surjective]
      exact hmax l hil hlk
    · simpa only [cluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hy
    · simpa only [edgeFieldEquiv_apply,Set.mem_preimage,Equiv.symm_apply_apply] using he
    · rw [hab e,hev,Sym2.map_mk]
    · simpa only [cluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hv
    · simpa only [slitCluster_edgeFieldEquiv G hab,Set.mem_preimage,Equiv.symm_apply_apply] using hw
    · rw [spliceStep_edgeFieldEquiv G hab]
      exact ih

end SpliceCovarianceTrace

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SpliceCovarianceReplay
attribute [local instance] Classical.propDecidable Classical.decEq

theorem spliceStepMask_edgeFieldEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω η : Set E) (x y : V) (e : E) :
    spliceMask G (cluster G (edgeFieldEquiv b ω) (a x))
      (cluster G (edgeFieldEquiv b η ∩ internalEdges G (cluster G (edgeFieldEquiv b ω) (a x))ᶜ) (a y))
      (b e) =
    edgeFieldEquiv b (spliceMask G (cluster G ω x)
      (cluster G (η ∩ internalEdges G (cluster G ω x)ᶜ) y) e) := by
  rw [slitCluster_edgeFieldEquiv G hab,cluster_edgeFieldEquiv G hab,
    spliceMask_aut_preimage G (isAut_symm G hab),Equiv.symm_apply_apply]
  rfl

theorem exchangeState_aut_map (b : E ≃ E) (mask : Set E) (i : ℕ) (s : SpliceState E) :
    exchangeState (edgeFieldEquiv b mask) i (spliceStateEquiv b s) =
      spliceStateEquiv b (exchangeState mask i s) := by
  apply Prod.ext
  · rfl
  · funext j
    by_cases hji : j = i
    · subst j
      rw [exchangeState_at]
      change _ = edgeFieldEquiv b ((exchangeState mask i s).2 i)
      rw [exchangeState_at]
      rfl
    · rw [exchangeState_away _ _ _ _ hji]
      change edgeFieldEquiv b (s.2 j) = edgeFieldEquiv b ((exchangeState mask i s).2 j)
      rw [exchangeState_away _ _ _ _ hji]

theorem replaySplice_aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (c : List (ℕ × E)) (ω : Set E) :
    replaySplice G (a x) (fun i => edgeFieldEquiv b (η i)) (fun i => a (y i))
      (spliceCodeEquiv b c) (edgeFieldEquiv b ω) =
    edgeFieldEquiv b (replaySplice G x η y c ω) := by
  induction c generalizing ω with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨i,e⟩
    change replaySplice G (a x) _ _ (spliceCodeEquiv b c) _ = _
    rw [spliceStep_edgeFieldEquiv G hab,ih]
    rfl

theorem replayMasks_aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (c : List (ℕ × E)) (ω : Set E) :
    replayMasks G (a x) (fun i => edgeFieldEquiv b (η i)) (fun i => a (y i))
      (spliceCodeEquiv b c) (edgeFieldEquiv b ω) =
    (replayMasks G x η y c ω).map (Prod.map id (edgeFieldEquiv b)) := by
  induction c generalizing ω with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨i,e⟩
    simp only [spliceCodeEquiv_apply,List.map_cons,Prod.map_apply,id_eq,replayMasks]
    rw [spliceStepMask_edgeFieldEquiv G hab,spliceStep_edgeFieldEquiv G hab]
    exact congrArg (List.cons _) (ih _)

theorem runMasks_aut_map (b : E ≃ E) (c : List (ℕ × Set E)) (s : SpliceState E) :
    runMasks (c.map (Prod.map id (edgeFieldEquiv b))) (spliceStateEquiv b s) =
      spliceStateEquiv b (runMasks c s) := by
  induction c generalizing s with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨i,mask⟩
    simp only [List.map_cons,Prod.map_apply,id_eq,runMasks]
    rw [exchangeState_aut_map,ih]

theorem seamContactCount_aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (η : ℕ → Set E) (y : ℕ → V) (ωf : Set E) (x : V) (i : ℕ) (e : E) :
    seamContactCount G (fun j => edgeFieldEquiv b (η j)) (fun j => a (y j))
      (edgeFieldEquiv b ωf) (a x) i (b e) = seamContactCount G η y ωf x i e := by
  simpa only [edgeFieldEquiv_apply,Equiv.symm_apply_apply] using
    seamContactCount_aut_preimage G (isAut_symm G hab) η (fun j => a (y j)) ωf (a x) i (b e)

theorem traceContactCount_aut_map (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (η : ℕ → Set E) (y : ℕ → V) (ωf : Set E) (x : V)
    (c : List (ℕ × E)) (i : ℕ) :
    traceContactCount G (fun j => edgeFieldEquiv b (η j)) (fun j => a (y j))
      (edgeFieldEquiv b ωf) (a x) (spliceCodeEquiv b c) i =
      traceContactCount G η y ωf x c i := by
  induction c with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨j,e⟩
    simp only [spliceCodeEquiv_apply,List.map_cons,Prod.map_apply,id_eq,traceContactCount]
    split_ifs
    · exact seamContactCount_aut_map G hab η y ωf x j e
    · exact ih

end SpliceCovarianceReplay

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Covariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteTraceCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] theorem edgeFieldEquiv_symm_edgeFieldEquiv (b : E ≃ E) (ω : Set E) :
    edgeFieldEquiv b.symm (edgeFieldEquiv b ω) = ω := by
  ext e
  simp only [edgeFieldEquiv_apply,Set.mem_preimage,Equiv.symm_symm,Equiv.symm_apply_apply]

@[simp] theorem spliceStateEquiv_symm_spliceStateEquiv (b : E ≃ E) (s : SpliceState E) :
    spliceStateEquiv b.symm (spliceStateEquiv b s) = s := by
  apply Prod.ext
  · exact edgeFieldEquiv_symm_edgeFieldEquiv b s.1
  · funext i
    exact edgeFieldEquiv_symm_edgeFieldEquiv b (s.2 i)

@[simp] theorem spliceCodeEquiv_symm_spliceCodeEquiv (b : E ≃ E) (c : List (ℕ × E)) :
    spliceCodeEquiv b.symm (spliceCodeEquiv b c) = c := by
  induction c with
  | nil => rfl
  | cons q c ih =>
    rcases q with ⟨i,e⟩
    simpa only [spliceCodeEquiv_apply,List.map_cons,Prod.map_apply,id_eq,Equiv.symm_apply_apply] using
      congrArg (List.cons (i,e)) ih

theorem spliceTrace_aut_map_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ)
    (ω ωf : Set E) (c : List (ℕ × E)) :
    SpliceTrace G (a x) (fun i => edgeFieldEquiv b (η i)) (fun i => a (y i)) k j
      (edgeFieldEquiv b ω) (spliceCodeEquiv b c) (edgeFieldEquiv b ωf) ↔
    SpliceTrace G x η y k j ω c ωf := by
  constructor
  · intro ht
    have hh := ht.aut_map G (isAut_symm G hab) (a x) (fun i => edgeFieldEquiv b (η i))
      (fun i => a (y i)) k j (edgeFieldEquiv b ω) (edgeFieldEquiv b ωf) (spliceCodeEquiv b c)
    simpa only [Equiv.symm_apply_apply,edgeFieldEquiv_symm_edgeFieldEquiv,
      spliceCodeEquiv_symm_spliceCodeEquiv] using hh
  · exact SpliceTrace.aut_map G hab x η y k j ω ωf c

theorem boundedTraceCodes_aut_map_iff (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (k : ℕ) (c : List (ℕ × E)) :
    spliceCodeEquiv b c ∈ boundedTraceCodes Q' k ↔ c ∈ boundedTraceCodes Q k := by
  simp only [mem_boundedTraceCodes,spliceCodeEquiv_apply,List.length_map]
  apply and_congr_right
  intro _
  constructor
  · intro h q hq
    have hh := h (q.1,b q.2) (List.mem_map.mpr ⟨q,hq,rfl⟩)
    exact ⟨hh.1,hh.2.1,(hQ q.2).mpr hh.2.2⟩
  · intro h r hr
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    exact ⟨(h q hq).1,(h q hq).2.1,(hQ q.2).mp (h q hq).2.2⟩

theorem finiteTraceCodes_aut_map_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (Q Q' : Finset E) (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q')
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω : Set E) (c : List (ℕ × E)) :
    spliceCodeEquiv b c ∈ finiteTraceCodes G (a x) (fun i => edgeFieldEquiv b (η i))
      (fun i => a (y i)) k j (edgeFieldEquiv b ω) Q' ↔
      c ∈ finiteTraceCodes G x η y k j ω Q := by
  rw [mem_finiteTraceCodes_iff,mem_finiteTraceCodes_iff,boundedTraceCodes_aut_map_iff b Q Q' hQ,
    replaySplice_aut_map G hab,spliceTrace_aut_map_iff G hab]


end FiniteTraceCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteIndexCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

def finiteTraceIndexEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E) (A A' : Finset (SpliceState E))
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (hA : ∀ s, s ∈ A ↔ spliceStateEquiv b s ∈ A')
    (y y' : SpliceState E → ℕ → V) (hy : ∀ s i, y' (spliceStateEquiv b s) i = a (y s i)) :
    FiniteTraceIndex G x k Q A y ≃ FiniteTraceIndex G (a x) k Q' A' y' :=
  Equiv.sigmaCongr ((spliceStateEquiv b).subtypeEquiv hA) (fun s =>
    (spliceCodeEquiv b).subtypeEquiv (fun c => by
      have hy' : y' (spliceStateEquiv b s.val) = fun i => a (y s.val i) := funext (hy s.val)
      change c ∈ finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q ↔
        spliceCodeEquiv b c ∈ finiteTraceCodes G (a x) (fun i => edgeFieldEquiv b (s.val.2 i))
          (y' (spliceStateEquiv b s.val)) k 0 (edgeFieldEquiv b s.val.1) Q'
      rw [hy']
      exact (finiteTraceCodes_aut_map_iff G hab Q Q' hQ x s.val.2 (y s.val) k 0 s.val.1 c).symm))

namespace FiniteTraceIndexEquiv
variable (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E) (A A' : Finset (SpliceState E))
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (hA : ∀ s, s ∈ A ↔ spliceStateEquiv b s ∈ A')
    (y y' : SpliceState E → ℕ → V) (hy : ∀ s i, y' (spliceStateEquiv b s) i = a (y s i))

@[simp] theorem input (t : FiniteTraceIndex G x k Q A y) :
    traceIndexInput G (a x) k Q' A' y' (finiteTraceIndexEquiv G hab x k Q Q' A A' hQ hA y y' hy t) =
      spliceStateEquiv b (traceIndexInput G x k Q A y t) := rfl

@[simp] theorem code (t : FiniteTraceIndex G x k Q A y) :
    traceIndexCode G (a x) k Q' A' y' (finiteTraceIndexEquiv G hab x k Q Q' A A' hQ hA y y' hy t) =
      spliceCodeEquiv b (traceIndexCode G x k Q A y t) := rfl

@[simp] theorem output (t : FiniteTraceIndex G x k Q A y) :
    traceIndexOutput G (a x) k Q' A' y' (finiteTraceIndexEquiv G hab x k Q Q' A A' hQ hA y y' hy t) =
      spliceStateEquiv b (traceIndexOutput G x k Q A y t) := by
  have hy' : y' (spliceStateEquiv b t.1.val) = fun i => a (y t.1.val i) := funext (hy t.1.val)
  change runMasks (replayMasks G (a x) (fun i => edgeFieldEquiv b (t.1.val.2 i))
    (y' (spliceStateEquiv b t.1.val)) (spliceCodeEquiv b t.2.val) (edgeFieldEquiv b t.1.val.1))
      (spliceStateEquiv b t.1.val) = _
  rw [hy',replayMasks_aut_map G hab,runMasks_aut_map]
  rfl

@[simp] theorem mass (t : FiniteTraceIndex G x k Q A y) :
    traceIndexMass G (a x) k Q' A' y' (finiteTraceIndexEquiv G hab x k Q Q' A A' hQ hA y y' hy t) =
      traceIndexMass G x k Q A y t := by
  unfold traceIndexMass
  rw [output G hab x k Q Q' A A' hQ hA y y' hy t]
  apply Finset.prod_congr rfl
  intro i _
  have hy' : y' (spliceStateEquiv b t.1.val) = fun i => a (y t.1.val i) := funext (hy t.1.val)
  change (traceContactCount G (fun j => edgeFieldEquiv b (t.1.val.2 j))
    (y' (spliceStateEquiv b t.1.val)) (edgeFieldEquiv b (traceIndexOutput G x k Q A y t).1)
    (a x) (spliceCodeEquiv b t.2.val) (i.val+1):ℝ)⁻¹ = _
  rw [hy',traceContactCount_aut_map G hab]

end FiniteTraceIndexEquiv



end FiniteIndexCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteFieldCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finset_aut_eq_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') : Q' = Q.map b.toEmbedding := by
  ext e
  simpa only [Finset.mem_map_equiv,b.apply_symm_apply] using (hQ (b.symm e)).symm

noncomputable def finiteFieldAutEquiv (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') : FiniteField Q ≃ FiniteField Q' :=
  (Equiv.finsetCongr b).subtypeEquiv (fun ω => by
    simp only [Finset.mem_powerset]
    change ω ⊆ Q ↔ ω.map b.toEmbedding ⊆ Q'
    rw [finset_aut_eq_map b Q Q' hQ,Finset.map_subset_map])

@[simp] theorem finiteFieldSet_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (ω : FiniteField Q) :
    finiteFieldSet Q' (finiteFieldAutEquiv b Q Q' hQ ω) = edgeFieldEquiv b (finiteFieldSet Q ω) := by
  change (ω.val.map b.toEmbedding : Set E) = b.symm ⁻¹' (ω.val : Set E)
  rw [Finset.coe_map]
  exact b.image_eq_preimage_symm _

@[simp] theorem finiteFieldWeight_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (p : ℝ) (ω : FiniteField Q) :
    finiteFieldWeight Q' p (finiteFieldAutEquiv b Q Q' hQ ω) = finiteFieldWeight Q p ω := by
  change p^(ω.val.map b.toEmbedding).card * (1-p)^(Q'.card-(ω.val.map b.toEmbedding).card) = _
  simp only [Finset.card_map,finset_aut_eq_map b Q Q' hQ]
  rfl

noncomputable def finiteFamilyEquiv (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) :
    (↥J → FiniteField Q) ≃ (↥J → FiniteField Q') :=
  Equiv.piCongrRight fun _ => finiteFieldAutEquiv b Q Q' hQ

@[simp] theorem finiteFieldFamily_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) (η : ↥J → FiniteField Q) (i : ℕ) :
    finiteFieldFamily Q' J (finiteFamilyEquiv b Q Q' hQ J η) i =
      edgeFieldEquiv b (finiteFieldFamily Q J η i) := by
  unfold finiteFieldFamily
  split_ifs with hi
  · exact finiteFieldSet_aut_map b Q Q' hQ (η ⟨i,hi⟩)
  · rfl

@[simp] theorem finiteFamilyWeight_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) (p : ℝ) (η : ↥J → FiniteField Q) :
    finiteFamilyWeight Q' J p (finiteFamilyEquiv b Q Q' hQ J η) = finiteFamilyWeight Q J p η := by
  apply Finset.prod_congr rfl
  intro i _
  exact finiteFieldWeight_aut_map b Q Q' hQ p (η i)

@[simp] theorem restrictFiniteField_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (ω : Set E) :
    restrictFiniteField Q' (edgeFieldEquiv b ω) = finiteFieldAutEquiv b Q Q' hQ (restrictFiniteField Q ω) := by
  apply finiteFieldSet_injective Q'
  rw [finiteFieldSet_aut_map,finiteFieldSet_restrict,finiteFieldSet_restrict]
  ext e
  change (b.symm e ∈ ω ∧ e ∈ Q') ↔ (b.symm e ∈ ω ∧ b.symm e ∈ Q)
  rw [hQ (b.symm e),b.apply_symm_apply]

 

theorem finiteRootLoad_aut_map (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) (p : ℝ)
    (f f' : SpliceState E → ℝ) (hf : ∀ s, f' (spliceStateEquiv b s) = f s)
    (ω : FiniteField Q) :
    finiteRootLoad Q' J p f' (finiteFieldAutEquiv b Q Q' hQ ω) = finiteRootLoad Q J p f ω := by
  unfold finiteRootLoad
  rw [← (finiteFamilyEquiv b Q Q' hQ J).sum_comp]
  apply Finset.sum_congr rfl
  intro η _
  rw [finiteFamilyWeight_aut_map,finiteFieldSet_aut_map]
  have he : finiteFieldFamily Q' J (finiteFamilyEquiv b Q Q' hQ J η) =
      fun i => edgeFieldEquiv b (finiteFieldFamily Q J η i) :=
    funext (finiteFieldFamily_aut_map b Q Q' hQ J η)
  rw [he]
  exact congrArg (fun t => finiteFamilyWeight Q J p η * t)
    (hf (finiteFieldSet Q ω,finiteFieldFamily Q J η))

end FiniteFieldCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section ChoiceIndexCovariance
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P P' : Type*}

def finiteChoiceTraceIndexEquiv (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (e : P ≃ P')
    (A : P → Finset (SpliceState E)) (A' : P' → Finset (SpliceState E))
    (hA : ∀ r s, s ∈ A r ↔ spliceStateEquiv b s ∈ A' (e r))
    (y : P → SpliceState E → ℕ → V) (y' : P' → SpliceState E → ℕ → V)
    (hy : ∀ r s i, y' (e r) (spliceStateEquiv b s) i = a (y r s i)) :
    FiniteChoiceTraceIndex G x k Q A y ≃ FiniteChoiceTraceIndex G (a x) k Q' A' y' :=
  Equiv.sigmaCongr e (fun r => finiteTraceIndexEquiv G hab x k Q Q' (A r) (A' (e r)) hQ (hA r)
    (y r) (y' (e r)) (hy r))

namespace FiniteChoiceTraceIndexEquiv
variable (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (e : P ≃ P')
    (A : P → Finset (SpliceState E)) (A' : P' → Finset (SpliceState E))
    (hA : ∀ r s, s ∈ A r ↔ spliceStateEquiv b s ∈ A' (e r))
    (y : P → SpliceState E → ℕ → V) (y' : P' → SpliceState E → ℕ → V)
    (hy : ∀ r s i, y' (e r) (spliceStateEquiv b s) i = a (y r s i))

@[simp] theorem input (t : FiniteChoiceTraceIndex G x k Q A y) :
    choiceTraceInput G (a x) k Q' A' y' (finiteChoiceTraceIndexEquiv G hab x k Q Q' hQ e A A' hA y y' hy t) =
      spliceStateEquiv b (choiceTraceInput G x k Q A y t) := rfl

@[simp] theorem output (t : FiniteChoiceTraceIndex G x k Q A y) :
    choiceTraceOutput G (a x) k Q' A' y' (finiteChoiceTraceIndexEquiv G hab x k Q Q' hQ e A A' hA y y' hy t) =
      spliceStateEquiv b (choiceTraceOutput G x k Q A y t) :=
  FiniteTraceIndexEquiv.output G hab x k Q Q' (A t.1) (A' (e t.1)) hQ (hA t.1)
    (y t.1) (y' (e t.1)) (hy t.1) t.2

@[simp] theorem mass (q : SpliceState E → P → ℝ) (q' : SpliceState E → P' → ℝ)
    (hq : ∀ s r, q' (spliceStateEquiv b s) (e r) = q s r)
    (t : FiniteChoiceTraceIndex G x k Q A y) :
    choiceTraceMass G (a x) k Q' A' y' q'
      (finiteChoiceTraceIndexEquiv G hab x k Q Q' hQ e A A' hA y y' hy t) =
      choiceTraceMass G x k Q A y q t := by
  unfold choiceTraceMass
  rw [input G hab x k Q Q' hQ e A A' hA y y' hy]
  change q' (spliceStateEquiv b (choiceTraceInput G x k Q A y t)) (e t.1) * _ = _
  rw [hq]
  exact congrArg (fun m => q (choiceTraceInput G x k Q A y t) t.1 * m)
    (FiniteTraceIndexEquiv.mass G hab x k Q Q' (A t.1) (A' (e t.1)) hQ (hA t.1)
      (y t.1) (y' (e t.1)) (hy t.1) t.2)

end FiniteChoiceTraceIndexEquiv

theorem finiteChoiceForwardLoad_aut_map [Fintype P] [Fintype P']
    (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (x : V) (k : ℕ) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (e : P ≃ P')
    (A : P → Finset (SpliceState E)) (A' : P' → Finset (SpliceState E))
    (hA : ∀ r s, s ∈ A r ↔ spliceStateEquiv b s ∈ A' (e r))
    (y : P → SpliceState E → ℕ → V) (y' : P' → SpliceState E → ℕ → V)
    (hy : ∀ r s i, y' (e r) (spliceStateEquiv b s) i = a (y r s i))
    (q : SpliceState E → P → ℝ) (q' : SpliceState E → P' → ℝ)
    (hq : ∀ s r, q' (spliceStateEquiv b s) (e r) = q s r) (s : SpliceState E) :
    finiteChoiceForwardLoad G (a x) k Q' A' y' q' (spliceStateEquiv b s) =
      finiteChoiceForwardLoad G x k Q A y q s := by
  unfold finiteChoiceForwardLoad finiteInverseLoad
  rw [← (finiteChoiceTraceIndexEquiv G hab x k Q Q' hQ e A A' hA y y' hy).sum_comp]
  apply Finset.sum_congr rfl
  intro t _
  rw [FiniteChoiceTraceIndexEquiv.output,FiniteChoiceTraceIndexEquiv.mass G hab x k Q Q' hQ e A A' hA y y' hy q q' hq]
  simp only [(spliceStateEquiv b).injective.eq_iff]

end ChoiceIndexCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AmplificationCovarianceInput
attribute [local instance] Classical.propDecidable Classical.decEq

theorem edgeField_subset_aut_iff (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (ω : Set E) :
    edgeFieldEquiv b ω ⊆ (Q' : Set E) ↔ ω ⊆ (Q : Set E) := by
  constructor
  · intro h e he
    exact (hQ e).mpr (h (by simpa using he : b e ∈ edgeFieldEquiv b ω))
  · intro h e he
    have hh := (hQ (b.symm e)).mp (h he)
    simpa only [b.apply_symm_apply,Finset.mem_coe] using hh

theorem finiteSpliceDomain_aut_map_iff (b : E ≃ E) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (J : Finset ℕ) (s : SpliceState E) :
    spliceStateEquiv b s ∈ finiteSpliceDomain Q' J ↔ s ∈ finiteSpliceDomain Q J := by
  rw [mem_finiteSpliceDomain_iff,mem_finiteSpliceDomain_iff]
  change (edgeFieldEquiv b s.1 ⊆ (Q':Set E) ∧
    (∀ i,edgeFieldEquiv b (s.2 i) ⊆ (Q':Set E)) ∧ ∀ i ∉ J,edgeFieldEquiv b (s.2 i)=∅) ↔ _
  have hz (η : Set E) : edgeFieldEquiv b η = ∅ ↔ η = ∅ := by
    change edgeFieldEquiv b η = edgeFieldEquiv b ∅ ↔ _
    exact (edgeFieldEquiv b).injective.eq_iff
  simp only [edgeField_subset_aut_iff b Q Q' hQ,hz]

theorem oldRunVertices_map {W W' : Type*} (f : W → W') (k : ℕ) (z : W)
    (r : Fin k → W) (i : ℕ) :
    oldRunVertices k (f z) (fun j => f (r j)) i = f (oldRunVertices k z r i) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    simp only [oldRunVertices]
    split_ifs with hi
    · exact ih (r 0) (Fin.tail r)
    · rfl

theorem oldRunWeight_map {W W' : Type*} (f : W → W')
    (K : ℕ → W → W → ℝ) (K' : ℕ → W' → W' → ℝ)
    (hK : ∀ i a b, K' i (f a) (f b) = K i a b) (k : ℕ) (z : W) (r : Fin k → W) :
    oldRunWeight K' k (f z) (fun i => f (r i)) = oldRunWeight K k z r := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    simp only [oldRunWeight,hK]
    rw [show Fin.tail (fun i => f (r i)) = (fun i => f (Fin.tail r i)) from rfl,ih]

def finiteVertexEquiv (a : V ≃ V) (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B') : ↥B ≃ ↥B' :=
  a.subtypeEquiv hB

def finiteRunEquiv (a : V ≃ V) (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B') (k : ℕ) :
    (Fin k → ↥B) ≃ (Fin k → ↥B') :=
  Equiv.piCongrRight fun _ => finiteVertexEquiv a B B' hB

theorem amplificationVertices_aut_map (a : V ≃ V) (B B' : Finset V)
    (hB : ∀ x, x ∈ B ↔ a x ∈ B') (k : ℕ) (z : ↥B) (r : Fin k → ↥B) (i : ℕ) :
    amplificationVertices B' k (finiteVertexEquiv a B B' hB z) (finiteRunEquiv a B B' hB k r) i =
      a (amplificationVertices B k z r i) :=
  congrArg Subtype.val (oldRunVertices_map (finiteVertexEquiv a B B' hB) k z r i)

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

theorem mass_aut_map (q : LocalEndpointRule G hloc O M L) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) :
    q.mass (edgeFieldEquiv b ω) (a x) (a y) = q.mass ω x y := by
  simpa only [Equiv.symm_apply_apply,edgeFieldEquiv_apply] using
    q.covariance a.symm b.symm (isAut_symm G hab) ω (a x) (a y)

theorem amplificationWeight_aut_map (q : LocalEndpointRule G hloc O M L) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B')
    (k : ℕ) (z : ↥B) (s : SpliceState E) (r : Fin k → ↥B) :
    q.amplificationWeight B' k (finiteVertexEquiv a B B' hB z) (spliceStateEquiv b s)
      (finiteRunEquiv a B B' hB k r) = q.amplificationWeight B k z s r := by
  apply oldRunWeight_map (finiteVertexEquiv a B B' hB)
  intro i v w
  exact q.mass_aut_map hab (s.2 i) v.val w.val

theorem amplificationInputs_aut_map_iff (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B')
    (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) (s : SpliceState E) :
    spliceStateEquiv b s ∈ q.amplificationInputs Q' B' (a x) k n
      (finiteVertexEquiv a B B' hB z) (finiteRunEquiv a B B' hB k r) ↔
      s ∈ q.amplificationInputs Q B x k n z r := by
  rw [q.mem_amplificationInputs,q.mem_amplificationInputs]
  have hn : (cluster G (edgeFieldEquiv b s.1) (a x)).ncard = (cluster G s.1 x).ncard := by
    rw [cluster_edgeFieldEquiv G hab,← a.image_eq_preimage_symm,Set.ncard_image_of_injective _ a.injective]
  change (spliceStateEquiv b s ∈ finiteSpliceDomain Q' (Finset.Icc 1 k) ∧
    a x ∈ vertexOrbit G o ∧ a z.val ∈ vertexOrbit G o ∧
    n ≤ (cluster G (edgeFieldEquiv b s.1) (a x)).ncard ∧
    (cluster G (edgeFieldEquiv b s.1) (a x)).ncard < 2*n ∧
    amplificationVertices B' k (finiteVertexEquiv a B B' hB z) (finiteRunEquiv a B B' hB k r) 0 ∈
      cluster G (edgeFieldEquiv b s.1) (a x) ∧ _) ↔ _
  rw [finiteSpliceDomain_aut_map_iff b Q Q' hQ,mem_vertexOrbit_aut_iff G o hab,
    mem_vertexOrbit_aut_iff G o hab,hn,amplificationVertices_aut_map,
    cluster_edgeFieldEquiv G hab,q.amplificationWeight_aut_map hab B B' hB]
  simp only [Set.mem_preimage,Equiv.symm_apply_apply]

end LocalEndpointRule
end AmplificationCovarianceInput

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section AmplificationCovarianceMarginal
attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem amplificationMarginal_aut_map (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (Q Q' : Finset E)
    (hQ : ∀ e, e ∈ Q ↔ b e ∈ Q') (B B' : Finset V) (hB : ∀ x, x ∈ B ↔ a x ∈ B')
    (x : V) (k n : ℕ) (z : ↥B) (p : unitInterval) (ω : Set E) :
    q.amplificationMarginal Q' B' (a x) k n (finiteVertexEquiv a B B' hB z) p (edgeFieldEquiv b ω) =
      q.amplificationMarginal Q B x k n z p ω := by
  unfold amplificationMarginal
  rw [restrictFiniteField_aut_map b Q Q' hQ]
  apply finiteRootLoad_aut_map
  intro s
  apply finiteChoiceForwardLoad_aut_map G hab x k Q Q' hQ (finiteRunEquiv a B B' hB k)
  · intro r s
    exact (q.amplificationInputs_aut_map_iff o hab Q Q' hQ B B' hB x k n z r s).symm
  · intro r s i
    exact amplificationVertices_aut_map a B B' hB k z r i
  · intro s r
    exact q.amplificationWeight_aut_map hab B B' hB k z s r

end LocalEndpointRule

theorem mem_incidentSupport_aut_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (B B' : Finset V)
    (hB : ∀ x, x ∈ B ↔ a x ∈ B') (e : E) :
    b e ∈ incidentSupport G hloc B' ↔ e ∈ incidentSupport G hloc B := by
  rw [finset_aut_eq_map a B B' hB,incidentSupport_aut G hloc hab]
  simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply]

theorem finiteBall_aut_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x y : V) (R : ℕ) :
    y ∈ (finite_reachBall hloc x R).toFinset ↔ a y ∈ (finite_reachBall hloc (a x) R).toFinset := by
  simpa only [Set.Finite.mem_toFinset] using (mem_reachBall_aut_iff G hab x y R).symm

theorem localBondBall_aut_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) (R : ℕ) (e : E) :
    e ∈ incidentSupport G hloc (finite_reachBall hloc x R).toFinset ↔
      b e ∈ incidentSupport G hloc (finite_reachBall hloc (a x) R).toFinset :=
  (mem_incidentSupport_aut_iff G hloc hab _ _ (fun y => finiteBall_aut_iff G hloc hab x y R) e).symm

end AmplificationCovarianceMarginal

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section CanonicalAmplificationLoad
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

def amplificationRadius (q : LocalEndpointRule G hloc O M L) (k n : ℕ) : ℕ :=
  2*n+k*M+max q.radius M

noncomputable def amplificationBall (_q : LocalEndpointRule G hloc O M L) (k n : ℕ) (x : V) : Finset V :=
  (finite_reachBall hloc x (2*n+k*M)).toFinset

noncomputable def amplificationBonds (q : LocalEndpointRule G hloc O M L) (k n : ℕ) (x : V) : Finset E :=
  incidentSupport G hloc (finite_reachBall hloc x (q.amplificationRadius k n)).toFinset

 

noncomputable def amplifiedMass (q : LocalEndpointRule G hloc O M L) (k n : ℕ) (p : unitInterval)
    (ω : Set E) (x z : V) : ℝ :=
  if hz : z ∈ q.amplificationBall k n x then
    q.amplificationMarginal (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n ⟨z,hz⟩ p ω / n
  else 0

theorem amplifiedMass_nonneg (q : LocalEndpointRule G hloc O M L) (hL : 1 ≤ L)
    (k n : ℕ) (p : unitInterval) (ω : Set E) (x z : V) : 0 ≤ q.amplifiedMass k n p ω x z := by
  unfold amplifiedMass
  split_ifs
  · exact div_nonneg (q.amplificationMarginal_bounds hL _ _ _ _ _ _ _ _).1 (Nat.cast_nonneg _)
  · exact le_rfl

theorem amplifiedMass_support (q : LocalEndpointRule G hloc O M L)
    (k n : ℕ) (p : unitInterval) (ω : Set E) (x z : V) (h : q.amplifiedMass k n p ω x z ≠ 0) :
    x ∈ O ∧ z ∈ O ∧ Conn G ω x z ∧ (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ 2*n+k*M := by
  unfold amplifiedMass at h
  split_ifs at h with hz
  · apply q.amplificationMarginal_physical_support (q.amplificationBonds k n x) (q.amplificationBall k n x) x k n ⟨z,hz⟩ p ω
    · exact incidentSupport_ball_mono G hloc x (Nat.le_add_right (2*n+k*M) (max q.radius M))
    · intro he
      exact h (by rw [he,zero_div])
  · exact (h rfl).elim

theorem amplifiedMass_local (q : LocalEndpointRule G hloc O M L)
    (k n : ℕ) (p : unitInterval) (ω : Set E) (x z : V) :
    q.amplifiedMass k n p ω x z =
      q.amplifiedMass k n p (ω ∩ (q.amplificationBonds k n x : Set E)) x z := by
  unfold amplifiedMass
  split_ifs
  · exact congrArg (fun t : ℝ => t / n) (q.amplificationMarginal_local _ _ _ _ _ _ _ _)
  · rfl

theorem amplifiedMass_aut_map (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (k n : ℕ) (p : unitInterval)
    (ω : Set E) (x z : V) :
    q.amplifiedMass k n p (edgeFieldEquiv b ω) (a x) (a z) = q.amplifiedMass k n p ω x z := by
  have hB (y : V) : y ∈ q.amplificationBall k n x ↔ a y ∈ q.amplificationBall k n (a x) :=
    finiteBall_aut_iff G hloc hab x y (2*n+k*M)
  have hQ (e : E) : e ∈ q.amplificationBonds k n x ↔ b e ∈ q.amplificationBonds k n (a x) :=
    localBondBall_aut_iff G hloc hab x (q.amplificationRadius k n) e
  unfold amplifiedMass
  by_cases hz : z ∈ q.amplificationBall k n x
  · simp only [dite_eq_left hz,dite_eq_left ((hB z).mp hz)]
    exact congrArg (fun t : ℝ => t / n)
      (q.amplificationMarginal_aut_map o hab _ _ hQ _ _ hB x k n ⟨z,hz⟩ p ω)
  · simp only [dite_eq_right hz,dite_eq_right (mt (hB z).mpr hz)]

 

noncomputable def amplificationLoad (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (hL : 1 ≤ L) (k n : ℕ) (p : unitInterval) :
    CappedLocalLoad G hloc (vertexOrbit G o) (2*n+k*M) where
  mass := q.amplifiedMass k n p
  radius := q.amplificationRadius k n
  nonneg := q.amplifiedMass_nonneg hL k n p
  support := q.amplifiedMass_support k n p
  locality := q.amplifiedMass_local k n p
  covariance := by
    intro a b hab ω x z
    simpa only [Equiv.symm_apply_apply,edgeFieldEquiv_apply,Equiv.symm_symm] using
      q.amplifiedMass_aut_map o (isAut_symm G hab) k n p ω (a x) (a z)

end LocalEndpointRule
end CanonicalAmplificationLoad

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

open MeasureTheory
section AmplificationLoadOperator
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

noncomputable def kernel (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x y : V) : ℝ :=
  ∫ ω, q.mass ω x y ∂law p

end CappedLocalLoad


end AmplificationLoadOperator

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Connections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connections for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterWindowLaw
attribute [local instance] Classical.propDecidable Classical.decEq

def ClusterWindow (G : BondGraph V E) (x : V) (lo hi : ℕ) (ω : Set E) : Prop :=
  (cluster G ω x).Finite ∧ lo ≤ (cluster G ω x).ncard ∧ (cluster G ω x).ncard < hi

noncomputable def clusterWindowProbability (G : BondGraph V E) (p : unitInterval)
    (x : V) (lo hi : ℕ) : ℝ := (law p).real {ω | ClusterWindow G x lo hi ω}

end ClusterWindowLaw
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section QuantitativeAmplificationMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def amplificationMomentFactor (k M d : ℕ) (c a t : ℝ) : ℝ :=
  4 + (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ) + (2*c*(k*M:ℕ))^2*t/a

end QuantitativeAmplificationMoment
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectionAdjustedRule
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def cappedConnectionMass (G : BondGraph V E) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ) (ω : Set E) (x y : V) : ℝ :=
  if CappedGoodness G ω x M L ∧ Conn G ω x y then c*S x y/twoPoint G p x y else 0

theorem cappedConnectionMass_nonneg (G : BondGraph V E) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (hc : 0 ≤ c) (hS : ∀ x y, 0 ≤ S x y)
    (M : ℕ) (L : ℝ) (ω : Set E) (x y : V) : 0 ≤ cappedConnectionMass G p S c M L ω x y := by
  unfold cappedConnectionMass
  split_ifs
  · exact div_nonneg (mul_nonneg hc (hS x y)) (twoPoint_nonneg G p x y)
  · rfl

theorem cappedConnectionMass_support (G : BondGraph V E) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ) (ω : Set E) (x y : V)
    (h : cappedConnectionMass G p S c M L ω x y ≠ 0) :
    S x y ≠ 0 ∧ CappedGoodness G ω x M L ∧ Conn G ω x y := by
  unfold cappedConnectionMass at h
  split_ifs at h with hh
  · refine ⟨?_,hh⟩
    intro hz
    simp only [hz,mul_zero,zero_div] at h
    exact h rfl
  · exact (h rfl).elim

theorem cappedConnectionMass_le (G : BondGraph V E) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (hc : 0 < c) (hS : ∀ x y, 0 ≤ S x y)
    (hτ : ∀ x y, S x y ≠ 0 → c ≤ twoPoint G p x y)
    (M : ℕ) (L : ℝ) (ω : Set E) (x y : V) : cappedConnectionMass G p S c M L ω x y ≤ S x y := by
  by_cases hs : S x y = 0
  · simp only [cappedConnectionMass,hs,mul_zero,zero_div,ite_self,le_refl]
  · unfold cappedConnectionMass
    split_ifs
    · apply (div_le_iff₀ (hc.trans_le (hτ x y hs))).mpr
      exact (mul_le_mul_of_nonneg_right (hτ x y hs) (hS x y)).trans_eq (mul_comm _ _)
    · exact hS x y

theorem cappedConnectionMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ) (ω : Set E) (x y : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    cappedConnectionMass G p S c M L ω x y = cappedConnectionMass G p S c M L (ω ∩ (Q:Set E)) x y := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
  change cappedConnectionMass G p S c M L ω x y = cappedConnectionMass G p S c M L (ω ∩ (Q:Set E)) x y
  have hg := cappedGoodness_local G hloc ω x M L
  change CappedGoodness G ω x M L ↔ CappedGoodness G (ω ∩ (Q:Set E)) x M L at hg
  unfold cappedConnectionMass
  apply if_congr _ rfl rfl
  constructor
  · rintro ⟨h,hxy⟩
    have h' := hg.mp h
    have he := cluster_restrict_of_cap G hloc Q ω x M (Finset.Subset.refl _) h'.1 h'.2.1
    refine ⟨h',?_⟩
    change y ∈ cluster G (ω ∩ (Q:Set E)) x
    rw [he]
    exact hxy
  · rintro ⟨h,hxy⟩
    exact ⟨hg.mpr h,conn_mono G Set.inter_subset_left hxy⟩

theorem cappedConnectionMass_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b)
    (hS : ∀ x y, S (a x) (a y) = S x y) (ω : Set E) (x y : V) :
    cappedConnectionMass G p S c M L (b ⁻¹' ω) x y = cappedConnectionMass G p S c M L ω (a x) (a y) := by
  simp only [cappedConnectionMass,cappedGoodness_aut_iff G hab,conn_aut_iff G hab,
    hS,twoPoint_aut G p hab]

noncomputable def connectionAdjustedRule [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (O : Set V) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (hc : 0 < c) (hS : ∀ x y, 0 ≤ S x y)
    (hSsum : ∀ x, Summable (S x)) (hrow : ∀ x, ∑' y, S x y ≤ 1)
    (hτ : ∀ x y, S x y ≠ 0 → c ≤ twoPoint G p x y)
    (hO : ∀ x y, S x y ≠ 0 → x ∈ O ∧ y ∈ O)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, S (a x) (a y) = S x y)
    (M : ℕ) (L : ℝ) : LocalEndpointRule G hloc O M L where
  mass := cappedConnectionMass G p S c M L
  radius := M
  nonneg := cappedConnectionMass_nonneg G p S c hc.le hS M L
  support := by
    intro ω x y h
    obtain ⟨hs,hg,hxy⟩ := cappedConnectionMass_support G p S c M L ω x y h
    exact ⟨(hO x y hs).1,(hO x y hs).2,hxy,hg⟩
  locality := fun ω x y => cappedConnectionMass_local G hloc p S c M L ω x y
  covariance := fun a b hab ω x y => cappedConnectionMass_covariant G p S c M L a b hab (hcov a b hab) ω x y
  row_le_one := by
    intro ω x
    have hs : Summable (cappedConnectionMass G p S c M L ω x) := by
      apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
      intro y hy
      by_contra hn
      obtain ⟨_,hg,hxy⟩ := cappedConnectionMass_support G p S c M L ω x y hn
      apply hy
      simp only [Set.Finite.mem_toFinset]
      exact finite_cluster_subset_reachBall G ω x hg.1 M hg.2.1 hxy
    exact (hs.tsum_le_tsum (cappedConnectionMass_le G p S c hc hS hτ M L ω x) (hSsum x)).trans (hrow x)

end ConnectionAdjustedRule

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinOrbitRowMass
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binSizeMass (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V) : ℝ :=
  ∑' y, binConnectionMass G n ω x y

noncomputable def binOrbitRowMass (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V) : ℝ :=
  ∑' y, if y ∈ vertexOrbit G x then binConnectionMass G n ω x y else 0

end BinOrbitRowMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BinOrbitTransport
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binOrbitTransportMass (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) : ℝ :=
  binConnectionMass G n ω x y * binOrbitRowMass G n ω y / binSizeMass G n ω x

end BinOrbitTransport

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_ScaleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale Budget for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AveragedBinOrbitTransport
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binOrbitTransport (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V) : ℝ :=
  ∫ ω, binOrbitTransportMass G n ω x y ∂law p

end AveragedBinOrbitTransport

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section EndpointProfile

 

structure EndpointProfile (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (s : ℝ) where
  cap : ℕ
  rule : LocalEndpointRule G hloc (vertexOrbit G o) cap ((cap:ℝ)^s)
  success_pos : 0 < rule.successProbability p o
  op : Hilbert V →L[ℂ] Hilbert V
  norm_pos : 0 < ‖op‖
  coeff : ∀ x y, matrixCoeff op x y = (rule.normalizedKernel o p x y : ℂ)

namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p : unitInterval} {o : V} {s : ℝ}

noncomputable def U (q : EndpointProfile G hloc p o s) : ℝ := Real.log (1/q.rule.successProbability p o)
noncomputable def m (q : EndpointProfile G hloc p o s) : ℝ := Real.log q.cap
noncomputable def H (q : EndpointProfile G hloc p o s) : ℝ := Real.log (1/‖q.op‖)
noncomputable def cost (q : EndpointProfile G hloc p o s) (ξ : ℝ) : ℝ := q.U+(s+ξ)*q.m

end EndpointProfile

end EndpointProfile

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section AmplificationContraction

noncomputable def amplificationContraction (β s ξ : ℝ) : ℝ :=
  (β+ξ+(s+ξ)*(1+ξ))/(1-ξ)

end AmplificationContraction

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_Resampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resampling for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ShortBoundaryPivotal
attribute [local instance] Classical.propDecidable Classical.decEq

 

def ShortClosedBoundary (G : BondGraph V E) (ω : Set E) (x z : V) (M : ℕ) (e : E) : Prop :=
  e ∉ ω ∧ ¬Conn G ω x z ∧ ∃ a b : V, ∃ l : List E,
    G e = s(a,b) ∧ Along G x l a ∧ (∀ f ∈ l, f ∈ ω) ∧ l.length < M ∧ Conn G ω b z

end ShortBoundaryPivotal

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_KernelMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointDifference
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}
variable (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)

noncomputable def kernelDifference (p r : unitInterval) (x y : V) : ℝ :=
  |q.normalizedKernel o p x y - q.normalizedKernel o r x y|
noncomputable def differenceRow (p r : unitInterval) : ℝ := ∑' y, q.kernelDifference o p r o y

end LocalEndpointRule
end EndpointDifference
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterMassMoments
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def clusterMass (G : BondGraph V E) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, if Conn G ω x y then 1 else 0

end ClusterMassMoments
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section SusceptibilityTypes
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def susceptibility (G : BondGraph V E) (p : unitInterval) (x : V) : ℝ :=
  ∑' y, twoPoint G p x y

noncomputable def rootSusceptibility (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (p : unitInterval) : ℝ :=
  ∑ i, weight i * susceptibility G p (root i)

end SusceptibilityTypes
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BinClusterSlice
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binClusterSlice (G : BondGraph V E) (o : V) (n : ℕ)
    (ω : Set E) (x : V) : Finset V :=
  if h : ClusterWindow G x n (2*n) ω then h.1.toFinset.filter (fun y => y ∈ vertexOrbit G o) else ∅

end BinClusterSlice
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteClassTransport
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def finiteClassTransport (S : V → Finset V) (t : V → ℝ)
    (K : V → V → ℝ) (x y : V) : ℝ :=
  if y ∈ S x then t x / (S x).card * ∑ z ∈ S x, K x z else 0

end FiniteClassTransport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BinDiagonalClass
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binOrbitClass (G : BondGraph V E) (o : V) (n : ℕ)
    (ω : Set E) (x : V) : Finset V :=
  if x ∈ vertexOrbit G o then binClusterSlice G o n ω x else ∅

end BinDiagonalClass
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinDiagonalTransport
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binDiagonalMass (G : BondGraph V E) (o : V) (n : ℕ)
    (K : V → V → ℝ) (ω : Set E) (x y : V) : ℝ :=
  finiteClassTransport (binOrbitClass G o n ω) (fun x => binSizeMass G n ω x ^ 2) K x y

end BinDiagonalTransport
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_ExteriorMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinDiagonalLoss
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binDiagonalKernel (G : BondGraph V E) (p : unitInterval)
    (o : V) (n : ℕ) (K : V → V → ℝ) (x y : V) : ℝ :=
  ∫ ω, binDiagonalMass G o n K ω x y ∂law p

end BinDiagonalLoss
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_DistinctMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectedMomentLoss
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def connectedClusterMoment (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ :=
  ∫ ω, (if Conn G ω x y then ((cluster G ω x).ncard:ℝ)^2 else 0) ∂law p

end ConnectedMomentLoss
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section MapScaleBudget
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p₀ : unitInterval} {o : V} {s : ℝ}

noncomputable def potentialScale (q : EndpointProfile G hloc p₀ o s) (p : unitInterval) : ℝ :=
  (q.rule.successProbability p o)⁻¹*(1+(1-(p:ℝ))/p*q.cap)

noncomputable def geometricScale (q : EndpointProfile G hloc p₀ o s) : ℝ := 2*q.potentialScale p₀

end EndpointProfile
end MapScaleBudget
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Susceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Susceptibility for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrientedPivotalConnections
attribute [local instance] Classical.propDecidable Classical.decEq

 

def orientedPivotalEvent (G : BondGraph V E) (x y a b : V) : Set (Set E) :=
  {ω | Conn G ω x a ∧ Conn G ω b y ∧ ¬ Conn G ω a b}

end OrientedPivotalConnections
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ActualSusceptibilityRightSlope
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realRootSusceptibility (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (t : ℝ) : ℝ :=
  rootSusceptibility G root weight (Set.projIcc 0 1 zero_le_one t)

@[simp] theorem realRootSusceptibility_coe (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (p : unitInterval) :
    realRootSusceptibility G root weight (p:ℝ) = rootSusceptibility G root weight p := by
  simp only [realRootSusceptibility, Set.projIcc_val]

end ActualSusceptibilityRightSlope
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_FractionalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {E : Type v}
section DecisionCovarianceAlgebra
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def coordinateAverage (e : E) (p : ℝ) (f : Finset E → ℝ) (ω : Finset E) : ℝ :=
  (1-p)*f ω+p*f (insert e ω)

noncomputable def coordinateVariation (Q : Finset E) (p : ℝ) (f : Finset E → ℝ) (e : E) : ℝ :=
  bernoulliPolynomial (Q.erase e) (fun ω => |f (insert e ω)-f ω|) p

end DecisionCovarianceAlgebra
end Percolation


namespace Percolation
universe v
variable {E : Type v}
section EdgeDecisionTrees
attribute [local instance] Classical.propDecidable Classical.decEq

 
inductive EdgeQueryTree (E : Type v) where
  | done (b : Bool)
  | query (e : E) (closed opened : EdgeQueryTree E)

namespace EdgeQueryTree

def Valid (Q : Finset E) : EdgeQueryTree E → Prop
  | .done _ => True
  | .query e t₀ t₁ => e ∈ Q ∧ Valid (Q.erase e) t₀ ∧ Valid (Q.erase e) t₁

noncomputable def eval (ω : Finset E) : EdgeQueryTree E → Bool
  | .done b => b
  | .query e t₀ t₁ => if e ∈ ω then eval ω t₁ else eval ω t₀

noncomputable def value (t : EdgeQueryTree E) (ω : Finset E) : ℝ := if t.eval ω then 1 else 0

noncomputable def reads (ω : Finset E) (i : E) : EdgeQueryTree E → Prop
  | .done _ => False
  | .query e t₀ t₁ => i = e ∨ if e ∈ ω then reads ω i t₁ else reads ω i t₀

noncomputable def revealment (p : ℝ) (i : E) : EdgeQueryTree E → ℝ
  | .done _ => 0
  | .query e t₀ t₁ => if i = e then 1 else (1-p)*revealment p i t₀+p*revealment p i t₁

end EdgeQueryTree
end EdgeDecisionTrees
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_TailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe v
variable {E : Type v}
section QueryTranscriptLaw
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EdgeQueryTree

@[reducible] def forget : EdgeQueryTree E → ProbeTree
  | .done b => .done b
  | .query _ t₀ t₁ => .edge t₀.forget t₁.forget

noncomputable def leaf (ω : Finset E) : (t : EdgeQueryTree E) → t.forget.Leaf
  | .done _ => ()
  | .query e t₀ t₁ => if e ∈ ω then Sum.inr (t₁.leaf ω) else Sum.inl (t₀.leaf ω)

noncomputable def score (p : ℝ) (t : EdgeQueryTree E) (ω : Finset E) : ℝ :=
  ProbeTree.score p t.forget (t.leaf ω)

noncomputable def queryCount (t : EdgeQueryTree E) (ω : Finset E) : ℕ :=
  ProbeTree.queries t.forget (t.leaf ω)


end EdgeQueryTree
end QueryTranscriptLaw
end Percolation


namespace Percolation
universe v
variable {E : Type v}
section QueryScoreSets
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EdgeQueryTree

noncomputable def readSet (t : EdgeQueryTree E) (Q ω : Finset E) : Finset E :=
  Q.filter (fun e => t.reads ω e)

@[simp] theorem mem_readSet (t : EdgeQueryTree E) (Q ω : Finset E) (e : E) :
    e ∈ t.readSet Q ω ↔ e ∈ Q ∧ t.reads ω e := Finset.mem_filter

end EdgeQueryTree
end QueryScoreSets
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IncidenceExploration
attribute [local instance] Classical.propDecidable Classical.decEq

 

def IncidencePending (G : BondGraph V E) (Q : Finset E) (R : Finset V) : Prop :=
  ∃ t : E × V × V, t.1 ∈ Q ∧ t.2.1 ∈ R ∧ G t.1 = s(t.2.1,t.2.2)



structure IncidenceInvariant (G : BondGraph V E) (Q ω : Finset E) (R C : Finset V) : Prop where
  discovered : R ⊆ C
  closed : ∀ a ∈ C, ∀ e ∈ ω, ∀ b, G e = s(a,b) → b ∈ C
  reachable : ∀ y ∈ C, ∃ r ∈ R, Conn G ((ω ∩ Q : Finset E):Set E) r y

end IncidenceExploration
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ClosedClusterContacts
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def contactBonds (G : BondGraph V E) (Q : Finset E) (A B : Finset V) : Finset E :=
  Q.filter (fun e => ∃ a ∈ A, ∃ b ∈ B, G e = s(a,b))

end ClosedClusterContacts
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_LargeContacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Large Contacts for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ContactBinFirstMoment
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterContactBin (G : BondGraph V E) (Q : Finset E)
    (x v : V) (n m : ℕ) (ω : Finset E) : ℝ :=
  if ¬Conn G (ω:Set E) x v ∧
    n ≤ min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ∧
    min (finiteRootComponent G ω x).card (finiteRootComponent G ω v).card ≤ m
  then (contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card else 0



end ContactBinFirstMoment
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section InfiniteContacts
attribute [local instance] Classical.propDecidable Classical.decEq

 
def closedContactSet (G : BondGraph V E) (A B : Set V) : Set E :=
  {e | ∃ a ∈ A, ∃ b ∈ B, G e = s(a,b)}

noncomputable def clusterContactCount (G : BondGraph V E) (ω : Set E) (x v : V) : ℕ :=
  (closedContactSet G (cluster G ω x) (cluster G ω v)).ncard

end InfiniteContacts
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FullLargeContacts
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def fullLargeContact (G : BondGraph V E) (x v : V) (L : ℕ) (ω : Set E) : ℝ :=
  if ¬Conn G ω x v ∧ L ≤ min (cluster G ω x).ncard (cluster G ω v).ncard
  then clusterContactCount G ω x v else 0

end FullLargeContacts
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterAveraging
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterAveragingKernel (G : BondGraph V E) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if Conn G ω x y then ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ else 0

end ClusterAveraging
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PositiveClusterPairs
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterPairKernel (G : BondGraph V E) (ω : Set E)
    (J : V → V → ℝ≥0∞) (x y : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, if Conn G ω x a ∧ Conn G ω y b then J a b else 0

 

noncomputable def clusterPairDensity (G : BondGraph V E) (ω : Set E)
    (F : V → V → ℝ≥0∞) (x : V) : ℝ≥0∞ :=
  ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ *
    ∑' y, ((cluster G ω y).ncard:ℝ≥0∞)⁻¹ * (if ¬Conn G ω x y then F x y else 0)

noncomputable def clusterPairFunctional (G : BondGraph V E) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (F : Set E → V → V → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, clusterPairDensity G ω (F ω) (root i) ∂law p

end PositiveClusterPairs
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PairReversal
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterPairMass (G : BondGraph V E) (ω : Set E)
    (F : V → V → ℝ≥0∞) (x y : V) : ℝ≥0∞ :=
  ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ * ((cluster G ω y).ncard:ℝ≥0∞)⁻¹ *
    (if ¬Conn G ω x y then F x y else 0)

end PairReversal
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_ContactTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contact Trace for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactSquareTrace
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def contactSquareLarge (G : BondGraph V E) (L : ℕ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if L ≤ min (cluster G ω x).ncard (cluster G ω y).ncard then
    (clusterContactCount G ω x y:ℝ≥0∞)^2 else 0

end ContactSquareTrace
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ContactRealCutoff
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def contactSquareLargeReal (G : BondGraph V E) (L : ℝ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if L ≤ min ((cluster G ω x).ncard:ℝ) ((cluster G ω y).ncard:ℝ) then
    (clusterContactCount G ω x y:ℝ≥0∞)^2 else 0

end ContactRealCutoff
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PairMeasure
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterPairMeasure [MeasurableSpace V]
    {ι : Type*} [MeasurableSpace ι] (G : BondGraph V E) (p : unitInterval)
    (root : ι → V) (weight : ι → ℝ) : Measure (Set E × (ι × V)) :=
  ((law p).prod Measure.count).withDensity (fun t => ENNReal.ofReal (weight t.2.1) *
    clusterPairMass G t.1 (fun _ _ => 1) (root t.2.1) t.2.2)

end PairMeasure
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_RussoRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Russo Rows for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section UniformContactError
attribute [local instance] Classical.propDecidable Classical.decEq

def ClusterSupportIn (G : BondGraph V E) (Q : Finset E) (ω : Set E) (x : V) : Prop :=
  ∀ a, Conn G ω x a → ∀ e, a ∈ G e → e ∈ Q

noncomputable def contactApproxError (G : BondGraph V E) (Q : Finset E) (d : ℕ)
    (x y : V) (ω : Set E) : ℝ :=
  if ClusterSupportIn G Q ω x ∧ ClusterSupportIn G Q ω y then 0
  else (d:ℝ)*(cluster G ω x).ncard

end UniformContactError
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section PointwiseRussoLimit
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realContactExpectation (G : BondGraph V E) (x y : V) (t : ℝ) : ℝ :=
  ∫ ω, fullLargeContact G x y 0 ω ∂law (Set.projIcc 0 1 zero_le_one t)

@[simp] theorem realContactExpectation_coe (G : BondGraph V E) (x y : V) (p : unitInterval) :
    realContactExpectation G x y (p:ℝ) = ∫ ω, fullLargeContact G x y 0 ω ∂law p := by
  simp only [realContactExpectation,Set.projIcc_val]

noncomputable def realTwoPoint (G : BondGraph V E) (x y : V) (t : ℝ) : ℝ :=
  twoPoint G (Set.projIcc 0 1 zero_le_one t) x y

@[simp] theorem realTwoPoint_coe (G : BondGraph V E) (x y : V) (p : unitInterval) :
    realTwoPoint G x y (p:ℝ) = twoPoint G p x y := by
  simp only [realTwoPoint,Set.projIcc_val]

end PointwiseRussoLimit
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_TraceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u
section ChronologicalErasure
open List
variable {V : Type u}
attribute [local instance] Classical.propDecidable Classical.decEq

 

inductive HoldingWalk (H : SimpleGraph V) : ℕ → V → V → Type u
  | nil (x : V) : HoldingWalk H 0 x x
  | hold {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : HoldingWalk H (k+1) x y
  | step {k : ℕ} {x z y : V} (h : H.Adj x z) (w : HoldingWalk H k z y) :
      HoldingWalk H (k+1) x y

namespace HoldingWalk
variable {H : SimpleGraph V} {k : ℕ} {x y : V}

def withoutHolds : {k : ℕ} → {x y : V} → HoldingWalk H k x y → H.Walk x y
  | _,_,_,.nil _ => .nil
  | _,_,_,.hold w => w.withoutHolds
  | _,_,_,.step h w => .cons h w.withoutHolds

def vertices : {k : ℕ} → {x y : V} → HoldingWalk H k x y → List V
  | _,x,_,.nil _ => [x]
  | _,x,_,.hold w => x :: w.vertices
  | _,x,_,.step _ w => x :: w.vertices

noncomputable def mass (P : V → V → ℝ) : {k : ℕ} → {x y : V} → HoldingWalk H k x y → ℝ
  | _,_,_,.nil _ => 1
  | _,x,_,.hold w => P x x * w.mass P
  | _,x,_,.step (z := z) _ w => P x z * w.mass P



noncomputable def erase (w : HoldingWalk H k x y) : H.Walk x y :=
  w.withoutHolds.reverse.bypass.reverse

end HoldingWalk
end ChronologicalErasure
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorMonotonicity
attribute [local instance] Classical.propDecidable Classical.decEq

 

def corridorCounted (G : BondGraph V E) (retained blockers : Set E)
    (D : Set V) (ω : Set E) (x y : V) : Prop :=
  Conn G (ω ∩ internalEdges G D) x y ∧
    (∀ e ∈ retained, e ∈ ω ∩ internalEdges G D ∧
      ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x y) ∧
    Disjoint blockers (ω ∩ internalEdges G D)

end CorridorMonotonicity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section LiteralCorridors
attribute [local instance] Classical.propDecidable Classical.decEq

instance HoldingWalk.countable [Countable V] (H : SimpleGraph V) (k : ℕ) (x y : V) :
    Countable (HoldingWalk H k x y) := by
  induction k generalizing x y with
  | zero =>
    apply Function.Injective.countable (f := fun _ : HoldingWalk H 0 x y => ())
    intro a b _
    cases a
    cases b
    rfl
  | succ k ih =>
    let (a b : V) : Countable (HoldingWalk H k a b) := ih a b
    let f : HoldingWalk H (k+1) x y →
        HoldingWalk H k x y ⊕ (Σ z : {z // H.Adj x z}, HoldingWalk H k z.val y)
      | .hold w => .inl w
      | .step (z := z) h w => .inr ⟨⟨z,h⟩,w⟩
    apply Function.Injective.countable (f := f)
    intro a b hab
    cases a with
    | hold a =>
      cases b with
      | hold b => exact congrArg HoldingWalk.hold (Sum.inl.inj hab)
      | step h b => cases hab
    | @step _ _ z _ h a =>
      cases b with
      | hold b => cases hab
      | @step _ _ z' _ h' b =>
        have he := Sum.inr.inj hab
        have hz := congrArg (fun t => t.1.val) he
        change z = z' at hz
        subst z'
        have hab' : a = b := by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using he
        subst b
        rfl

 
abbrev RawCorridor (G : BondGraph V E) (k : ℕ) :=
  Σ x y : V, HoldingWalk (openSimpleGraph G Set.univ) k x y

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

def base (w : RawCorridor G k) : V := w.1
def endpoint (w : RawCorridor G k) : V := w.2.1
noncomputable def path (w : RawCorridor G k) :
    (openSimpleGraph G Set.univ).Walk w.base w.endpoint := w.2.2.erase
noncomputable def interior (w : RawCorridor G k) : Finset V :=
  w.path.support.toFinset \ {w.base,w.endpoint}
def retained (w : RawCorridor G k) : Set E := {e | G e ∈ w.path.edges}
noncomputable def blockers (w : RawCorridor G k) : Set E :=
  {e | ∃ z ∈ w.interior, z ∈ G e} \ w.retained
noncomputable def probability (P : V → V → ℝ) (w : RawCorridor G k) : ℝ := w.2.2.mass P
noncomputable def weight (P : V → V → ℝ) (p : ℝ) (w : RawCorridor G k) : ℝ :=
  w.probability P * (p^w.path.length)⁻¹ * ((1-p)^w.blockers.ncard)⁻¹

theorem retained_finite (hG : Function.Injective G) (w : RawCorridor G k) : w.retained.Finite :=
  (List.finite_toSet w.path.edges).preimage hG.injOn

theorem blockers_finite (hloc : LocallyFinite G) (w : RawCorridor G k) : w.blockers.Finite := by
  apply Set.Finite.subset (s := (incidentSupport G hloc w.interior : Set E)) (Finset.finite_toSet _)
  intro e he
  exact (mem_incidentSupport G hloc w.interior e).mpr he.1

end RawCorridor
end LiteralCorridors
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_Corridors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corridors for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExactCorridorPattern
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

def calibrationEvent (w : RawCorridor G k) : Set (Set E) :=
  {ω | w.retained ⊆ ω ∧ Disjoint w.blockers ω}

end RawCorridor
end ExactCorridorPattern
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorContraction
attribute [local instance] Classical.propDecidable Classical.decEq



namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

def exterior (w : RawCorridor G k) (ω : Set E) : Set E :=
  ω ∩ internalEdges G (w.interior : Set V)ᶜ

def attachment (w : RawCorridor G k) (ω : Set E) : Set V :=
  {z | z ∈ w.path.support ∨ Conn G (w.exterior ω) w.base z ∨ Conn G (w.exterior ω) w.endpoint z}

end RawCorridor
end CorridorContraction
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CorridorBKCalibration
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

def exteriorOrientations (w : RawCorridor G k) (x y : V) : Set (Set E) :=
  orientedPivotalEvent G x y w.base w.endpoint ∪ orientedPivotalEvent G x y w.endpoint w.base

end RawCorridor
end CorridorBKCalibration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawPathIntegration
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev RawFrom (H : SimpleGraph V) (k : ℕ) (x : V) := Σ y : V, HoldingWalk H k x y

namespace RawFrom
variable {H : SimpleGraph V}

def zeroEquiv (x : V) : RawFrom H 0 x ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨x,.nil x⟩
  left_inv w := by rcases w with ⟨y,w⟩; cases w; rfl
  right_inv _ := rfl

def succEquiv (k : ℕ) (x : V) : RawFrom H (k+1) x ≃
    RawFrom H k x ⊕ (Σ z : H.neighborSet x, RawFrom H k z.val) where
  toFun
    | ⟨y,.hold w⟩ => .inl ⟨y,w⟩
    | ⟨y,.step (z := z) h w⟩ => .inr ⟨⟨z,h⟩,y,w⟩
  invFun
    | .inl ⟨y,w⟩ => ⟨y,.hold w⟩
    | .inr ⟨⟨z,h⟩,y,w⟩ => ⟨y,.step h w⟩
  left_inv w := by rcases w with ⟨y,w⟩; cases w <;> rfl
  right_inv w := by rcases w with ⟨y,w⟩ | ⟨⟨z,h⟩,y,w⟩ <;> rfl

instance finite [∀ x, Finite (H.neighborSet x)] (k : ℕ) (x : V) : Finite (RawFrom H k x) := by
  induction k generalizing x with
  | zero => exact Finite.of_equiv Unit (zeroEquiv x).symm
  | succ k ih =>
    let (z : V) : Finite (RawFrom H k z) := ih z
    exact Finite.of_equiv _ (succEquiv k x).symm

noncomputable def integral (P : V → V → ℝ) (k : ℕ) (x : V) (f : V → ℝ) : ℝ :=
  ∑' w : RawFrom H k x, w.2.mass P * f w.1

end RawFrom

end RawPathIntegration
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorSum
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

def counted (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) : Prop :=
  3 ≤ w.path.length ∧ (∀ z ∈ w.path.support, z ∈ D) ∧
    corridorCounted G w.retained w.blockers D ω x y

end RawCorridor

end CorridorSum
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ActualCorridorPenalty
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def corridorPenaltyTerm (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    {k : ℕ} (D : Set V) (ω : Set E) (x y : V) (w : RawCorridor G k) : ℝ :=
  if w.counted D ω x y then w.weight P p else 0

noncomputable def corridorPenalty (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (D : Set V) (ω : Set E) (x y : V) : ℝ :=
  ∑' w : RawCorridor G k, corridorPenaltyTerm G P p D ω x y w

end ActualCorridorPenalty
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ActualWeightedConnections
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def deformedConnection (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) : ℝ :=
  if x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y then
    Real.exp (-t * corridorPenalty G P p k D ω x y) else 0

noncomputable def deformedKernel (G : BondGraph V E) (P : V → V → ℝ) (p : unitInterval)
    (k : ℕ) (t : ℝ) (D : Set V) (x y : V) : ℝ :=
  ∫ ω, deformedConnection G P p k t D ω x y ∂law p

end ActualWeightedConnections
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_ClusterProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cluster Products for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeletionGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
def closedBondNeighborhood (G : BondGraph V E) (A : Set V) : Set V :=
  {z | z ∈ A ∨ ∃ e, z ∈ G e ∧ ∃ a ∈ G e, a ∈ A}

def SimpleVisit (G : BondGraph V E) (S : Set E) (A : Set V) (x y : V) : Prop :=
  ∃ q : (openSimpleGraph G S).Walk x y, q.IsPath ∧ ∃ z ∈ q.support, z ∈ A

end DeletionGeometry
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DeformedSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def deformedSusceptibility (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x : V) : ℝ :=
  ∑' y, deformedKernel G P p k t D x y

end DeformedSusceptibility
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExactComponentRestriction
attribute [local instance] Classical.propDecidable Classical.decEq

 
def OpenClosed (G : BondGraph V E) (ω : Set E) (A : Set V) : Prop :=
  ∀ e ∈ ω, ∀ z ∈ G e, z ∈ A → ∀ a ∈ G e, a ∈ A

end ExactComponentRestriction
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_Calibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibration for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u u' v
section ErasureNaturality
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {V' : Type u'} {H : SimpleGraph V} {H' : SimpleGraph V'}

namespace HoldingWalk

def map (f : H →g H') : {k : ℕ} → {x y : V} → HoldingWalk H k x y → HoldingWalk H' k (f x) (f y)
  | _,_,_,.nil _ => .nil _
  | _,_,_,.hold w => .hold (w.map f)
  | _,_,_,.step h w => .step (f.map_rel h) (w.map f)

end HoldingWalk
end ErasureNaturality
end Percolation

 
namespace Percolation
universe u u' u'' v
section RawWalkMaps
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {V' : Type u'} {V'' : Type u''}
  {H : SimpleGraph V} {H' : SimpleGraph V'} {H'' : SimpleGraph V''}
namespace HoldingWalk

theorem map_map (f : H →g H') (g : H' →g H'')
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : (w.map f).map g = w.map (g.comp f) := by
  induction w with
  | nil => rfl
  | hold w ih => exact congrArg hold ih
  | step h w ih => exact congrArg (step _) ih

theorem map_id {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.map ((SimpleGraph.Hom.id : H →g H)) = w := by
  induction w with
  | nil => rfl
  | hold w ih => exact congrArg hold ih
  | step h w ih => exact congrArg (step _) ih

end HoldingWalk

def rawWalkMap (f : H →g H') (k : ℕ) (w : Σ x y, HoldingWalk H k x y) :
    Σ x y, HoldingWalk H' k x y := ⟨f w.1,f w.2.1,w.2.2.map f⟩

theorem rawWalkMap_comp (f : H →g H') (g : H' →g H'') (k : ℕ)
    (w : Σ x y, HoldingWalk H k x y) : rawWalkMap g k (rawWalkMap f k w) = rawWalkMap (g.comp f) k w := by
  cases w with
  | mk x w =>
    cases w with
    | mk y w =>
      simp only [rawWalkMap,HoldingWalk.map_map]
      rfl

theorem rawWalkMap_id (k : ℕ) (w : Σ x y, HoldingWalk H k x y) :
    rawWalkMap ((SimpleGraph.Hom.id : H →g H)) k w = w := by
  cases w with
  | mk x w =>
    cases w with
    | mk y w =>
      simp only [rawWalkMap,HoldingWalk.map_id]
      rfl

def rawWalkEquiv (f : H ≃g H') (k : ℕ) :
    (Σ x y, HoldingWalk H k x y) ≃ (Σ x y, HoldingWalk H' k x y) where
  toFun := rawWalkMap f.toHom k
  invFun := rawWalkMap f.symm.toHom k
  left_inv w := by
    rw [rawWalkMap_comp]
    have he : f.symm.toHom.comp f.toHom = (SimpleGraph.Hom.id : H →g H) := by
      ext x
      exact f.symm_apply_apply x
    rw [he,rawWalkMap_id]
  right_inv w := by
    rw [rawWalkMap_comp]
    have he : f.toHom.comp f.symm.toHom = (SimpleGraph.Hom.id : H' →g H') := by
      ext x
      exact f.apply_symm_apply x
    rw [he,rawWalkMap_id]

end RawWalkMaps
section GraphAutWalks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {E : Type v}

theorem openSimpleGraph_univ_adj (G : BondGraph V E) (x y : V) :
    (openSimpleGraph G Set.univ).Adj x y ↔ x ≠ y ∧ Adj G x y := by
  simp only [openSimpleGraph,Adj,Set.mem_univ,true_and]

def autSimpleGraph (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) :
    openSimpleGraph G Set.univ ≃g openSimpleGraph G Set.univ where
  toEquiv := a
  map_rel_iff' := by
    intro x y
    simp only [openSimpleGraph_univ_adj,a.injective.ne_iff]
    exact and_congr_right (fun _ => ⟨fun h => by simpa using adj_aut G (isAut_symm G hab) h,
      adj_aut G hab⟩)

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}
def autEquiv {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) : RawCorridor G k ≃ RawCorridor G k :=
  rawWalkEquiv (autSimpleGraph G hab) k

end RawCorridor
end GraphAutWalks
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Deformation_AveragedDecrease
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaged Decrease for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AveragedDerivative
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]



noncomputable def averagedDeformedSusceptibility (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (root : ι → V) (weight : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, weight i * deformedSusceptibility G P p k t Set.univ (root i)

end AveragedDerivative
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredSegments
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]

 
def segmentOrbit (G : BondGraph V E) (γ : I → V) : Set (I → V) :=
  {s | ∃ a : V ≃ V, ∃ b : E ≃ E, IsAut G a b ∧ s = a ∘ γ}

omit [Fintype I] in
theorem segmentOrbit_aut_iff (G : BondGraph V E) (γ s : I → V)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) :
    a ∘ s ∈ segmentOrbit G γ ↔ s ∈ segmentOrbit G γ := by
  constructor
  · rintro ⟨c,d,hcd,he⟩
    refine ⟨c.trans a.symm,d.trans b.symm,isAut_trans G hcd (isAut_symm G h),?_⟩
    funext i
    have hh := congrFun he i
    simpa only [Function.comp_apply,Equiv.trans_apply,Equiv.symm_apply_apply] using congrArg a.symm hh
  · rintro ⟨c,d,hcd,rfl⟩
    exact ⟨c.trans a,d.trans b,isAut_trans G hcd h,rfl⟩

theorem finite_segmentAnchors (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) :
    {s ∈ segmentOrbit G γ | s i = x}.Finite := by
  apply (Set.Finite.pi' (fun _ : I => finite_reachBall hloc x n)).subset
  rintro s ⟨⟨a,b,hab,rfl⟩,hx⟩ j
  have hh := mem_reachBall_aut G hab (hdiam i j)
  change a (γ i) = x at hx
  simpa only [hx,Function.comp_apply] using hh

noncomputable def segmentAnchors (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i : I) (x : V) : Finset (I → V) :=
  (finite_segmentAnchors G hloc γ n hdiam i x).toFinset

end AnchoredSegments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AnchoredPositionKernels
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I : Type*} [Fintype I]



noncomputable def anchoredPositionKernel (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (i j : I) (x y : V) : ℝ :=
  ∑ s ∈ segmentAnchors G hloc γ n hdiam i x,
    if y = s j then ((segmentAnchors G hloc γ n hdiam i x).card : ℝ)⁻¹ else 0

end AnchoredPositionKernels
end Percolation


namespace Percolation
universe u
variable {V : Type u}
section RawReversal
namespace HoldingWalk
variable {H : SimpleGraph V}

 
def snocHold : {k : ℕ} → {x y : V} → HoldingWalk H k x y → HoldingWalk H (k+1) x y
  | _,_,_,.nil x => .hold (.nil x)
  | _,_,_,.hold w => .hold (snocHold w)
  | _,_,_,.step h w => .step h (snocHold w)

 
def snocStep : {k : ℕ} → {x y z : V} → HoldingWalk H k x y → H.Adj y z → HoldingWalk H (k+1) x z
  | _,_,_,z,.nil _,h => .step h (.nil z)
  | _,_,_,_,.hold w,h => .hold (snocStep w h)
  | _,_,_,_,.step h' w,h => .step h' (snocStep w h)

 

def reverse : {k : ℕ} → {x y : V} → HoldingWalk H k x y → HoldingWalk H k y x
  | _,_,_,.nil x => .nil x
  | _,_,_,.hold w => snocHold (reverse w)
  | _,_,_,.step h w => snocStep (reverse w) h.symm

theorem reverse_snocHold {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    w.snocHold.reverse = w.reverse.hold := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [snocHold,reverse,ih]
  | step h w ih => simp only [snocHold,reverse,ih,snocStep]

theorem reverse_snocStep {k : ℕ} {x y z : V} (w : HoldingWalk H k x y) (h : H.Adj y z) :
    (w.snocStep h).reverse = .step h.symm w.reverse := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [snocStep,reverse,ih,snocHold]
  | step h' w ih => simp only [snocStep,reverse,ih]

theorem reverse_reverse {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.reverse.reverse = w := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [reverse,reverse_snocHold,ih]
  | step h w ih => simp only [reverse,reverse_snocStep,ih]

end HoldingWalk
end RawReversal
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_Labels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section LabeledEscapeExperiment

 

structure EscapeLabel (G : BondGraph V E) (γ : I → V) (endpoint negative : I) (L m : ℕ) where
  first : I → V
  first_mem : first ∈ segmentOrbit G γ
  last : I → V
  last_mem : last ∈ segmentOrbit G γ
  middle : HoldingWalk (openSimpleGraph G Set.univ) L (first endpoint) (last endpoint)
  leftTail : RawFrom (openSimpleGraph G Set.univ) m (first negative)
  rightTail : RawFrom (openSimpleGraph G Set.univ) m (last negative)

namespace EscapeLabel
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

def reverse (ξ : EscapeLabel G γ ep neg L m) : EscapeLabel G γ ep neg L m where
  first := ξ.last
  first_mem := ξ.last_mem
  last := ξ.first
  last_mem := ξ.first_mem
  middle := ξ.middle.reverse
  leftTail := ξ.rightTail
  rightTail := ξ.leftTail

theorem reverse_reverse (ξ : EscapeLabel G γ ep neg L m) : ξ.reverse.reverse = ξ := by
  cases ξ
  simp only [reverse,HoldingWalk.reverse_reverse]

noncomputable def mass (P : V → V → ℝ) (ξ : EscapeLabel G γ ep neg L m) : ℝ :=
  ξ.middle.mass P * ξ.leftTail.2.mass P * ξ.rightTail.2.mass P



def reverseRootedEquiv (center : I) (x y : V) :
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x ∧ ξ.last center = y} ≃
    {ξ : EscapeLabel G γ ep neg L m // ξ.first center = y ∧ ξ.last center = x} where
  toFun ξ := ⟨ξ.1.reverse,ξ.2.2,ξ.2.1⟩
  invFun ξ := ⟨ξ.1.reverse,ξ.2.2,ξ.2.1⟩
  left_inv ξ := Subtype.ext (reverse_reverse ξ.1)
  right_inv ξ := Subtype.ext (reverse_reverse ξ.1)

end EscapeLabel
end LabeledEscapeExperiment
end Percolation

 
namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section FiniteRootedLabels
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

noncomputable def RootedLabelCode (G : BondGraph V E) (hloc : LocallyFinite G)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) : Type (max u w) :=
  Σ s : (segmentAnchors G hloc γ n hdiam center x),
    Σ mid : RawFrom (openSimpleGraph G Set.univ) L (s.val ep),
      Σ h : (segmentAnchors G hloc γ n hdiam ep mid.1),
        RawFrom (openSimpleGraph G Set.univ) m (s.val neg) ×
          RawFrom (openSimpleGraph G Set.univ) m (h.val neg)

end FiniteRootedLabels
end Percolation


namespace Percolation
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
theorem isAut_refl (G : BondGraph V E) : IsAut G (Equiv.refl V) (Equiv.refl E) := by
  intro e
  simp

namespace EscapeLabel
variable {G : BondGraph V E} {γ : I → V} {ep neg : I} {L m : ℕ}

def autMap {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) : EscapeLabel G γ ep neg L m where
  first := a ∘ ξ.first
  first_mem := (segmentOrbit_aut_iff G γ ξ.first hab).mpr ξ.first_mem
  last := a ∘ ξ.last
  last_mem := (segmentOrbit_aut_iff G γ ξ.last hab).mpr ξ.last_mem
  middle := ξ.middle.map (autSimpleGraph G hab).toHom
  leftTail := ⟨a ξ.leftTail.1,ξ.leftTail.2.map (autSimpleGraph G hab).toHom⟩
  rightTail := ⟨a ξ.rightTail.1,ξ.rightTail.2.map (autSimpleGraph G hab).toHom⟩

theorem autMap_trans {a c : V ≃ V} {b d : E ≃ E} (hab : IsAut G a b) (hcd : IsAut G c d)
    (ξ : EscapeLabel G γ ep neg L m) :
    autMap hcd (autMap hab ξ) = autMap (isAut_trans G hab hcd) ξ := by
  cases ξ
  dsimp only [autMap,autSimpleGraph]
  simp only [HoldingWalk.map_map]
  rfl

theorem autMap_refl (ξ : EscapeLabel G γ ep neg L m) :
    autMap (isAut_refl G) ξ = ξ := by
  cases ξ with
  | mk f hf l hl mid α β =>
    change EscapeLabel.mk f hf l hl (mid.map SimpleGraph.Hom.id)
      ⟨α.1,α.2.map SimpleGraph.Hom.id⟩ ⟨β.1,β.2.map SimpleGraph.Hom.id⟩ = _
    simp only [HoldingWalk.map_id]

theorem autMap_symm {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (ξ : EscapeLabel G γ ep neg L m) :
    autMap (isAut_symm G hab) (autMap hab ξ) = ξ := by
  rw [autMap_trans]
  have ha : a.trans a.symm = Equiv.refl V := by ext x; exact a.symm_apply_apply x
  have hb : b.trans b.symm = Equiv.refl E := by ext x; exact b.symm_apply_apply x
  generalize hp : isAut_trans G hab (isAut_symm G hab) = h
  clear hp
  revert h
  rw [ha,hb]
  intro h
  exact autMap_refl ξ

end EscapeLabel
end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
namespace HoldingWalk
variable {H : SimpleGraph V}

 

def append : {k l : ℕ} → {x y z : V} → HoldingWalk H k x y → HoldingWalk H l y z → HoldingWalk H (l+k) x z
  | _,_,_,_,_,.nil _,v => v
  | _,_,_,_,_,.hold w,v => .hold (w.append v)
  | _,_,_,_,_,.step h w,v => .step h (w.append v)

end HoldingWalk
end Percolation


namespace Percolation
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}

 

def position : {k : ℕ} → {x y : V} → HoldingWalk H k x y → ℕ → V
  | _,x,_,.nil _,_ => x
  | _,x,_,.hold _,0 => x
  | _,_,_,.hold w,n+1 => w.position n
  | _,x,_,.step _ _,0 => x
  | _,_,_,.step _ w,n+1 => w.position n

@[simp] theorem position_zero {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.position 0 = x := by
  cases w <;> rfl

@[simp] theorem position_length {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.position k = y := by
  induction w with
  | nil => rfl
  | hold w ih => exact ih
  | step h w ih => exact ih

end HoldingWalk
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_CollisionTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collision Tails for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u
variable {V : Type u}
namespace HoldingWalk
variable {H : SimpleGraph V}

 

def fromPositions : (k : ℕ) → (f : Fin (k+1) → V) →
    (∀ i : Fin k, H.Adj (f i.castSucc) (f i.succ)) →
    HoldingWalk H k (f 0) (f (Fin.last k))
  | 0,f,_ => .nil (f 0)
  | k+1,f,h => .step (h 0) (fromPositions k (fun i => f i.succ) (fun i => h i.succ))

end HoldingWalk
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Escape_PathSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection of geometrically separated paths from labelled escape events. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section EscapeGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}


noncomputable def neighborhood (hloc : LocallyFinite G) (w : RawCorridor G k) : Finset V :=
  w.interior ∪ w.interior.biUnion (neighbors G hloc)


def HasEscape (hloc : LocallyFinite G) (p : unitInterval) (j : ℕ) (t : ℝ)
    (w : RawCorridor G k) (x : V) : Prop :=
  ∃ z, ∃ q : (openSimpleGraph G Set.univ).Walk x z,
    q.IsPath ∧ q.length ≤ j ∧ (∀ v ∈ q.support, v ∉ w.interior) ∧
      (∑ b ∈ w.neighborhood hloc, twoPoint G p z b) ≤ t

 
def Selected (hloc : LocallyFinite G) (p : unitInterval) (j : ℕ) (t : ℝ)
    (w : RawCorridor G k) : Prop :=
  3 ≤ w.path.length ∧ w.HasEscape hloc p j t w.base ∧ w.HasEscape hloc p j t w.endpoint

end RawCorridor



end EscapeGeometry
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Cayley_Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cayley graphs, translation symmetries and root transport. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v

section GroupGeometry
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def cayleyEdgeTranslation (S : Finset Λ) (a : Λ) : CayleyEdge S ≃ CayleyEdge S where
  toFun e := ⟨e.val.map (fun x => a * x), by
    obtain ⟨e, x, s, hs, rfl⟩ := e
    exact ⟨a * x, s, hs, by simp [mul_assoc]⟩⟩
  invFun e := ⟨e.val.map (fun x => a⁻¹ * x), by
    obtain ⟨e, x, s, hs, rfl⟩ := e
    exact ⟨a⁻¹ * x, s, hs, by simp [mul_assoc]⟩⟩
  left_inv e := by
    apply Subtype.ext
    simp [Sym2.map_map]
  right_inv e := by
    apply Subtype.ext
    simp [Sym2.map_map]

end GroupGeometry
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Cayley_Folner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The group Følner criterion and nonamenable Cayley graphs. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u
section GroupGeometry
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def rightTranslate (A : Finset Λ) (g : Λ) : Finset Λ :=
  A.image (fun x => x * g)

@[simp] lemma card_rightTranslate (A : Finset Λ) (g : Λ) :
    (rightTranslate A g).card = A.card :=
  Finset.card_image_of_injective _ (Equiv.mulRight g).injective

end GroupGeometry
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_ClusterCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exclusion of positive finite critical cluster counts. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def InfiniteCover (G : BondGraph V E) (R : Finset V) (ω : Set E) : Prop :=
  ∀ y, (cluster G ω y).Infinite → ∃ z ∈ R, Conn G ω y z

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cut vertices and connected branches. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open SimpleGraph
universe u w
variable {V : Type u} {W : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

def cutVertex (H : SimpleGraph V) (x : V) : SimpleGraph V where
  Adj a b := H.Adj a b ∧ a ≠ x ∧ b ≠ x
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun a h => H.loopless.irrefl a h.1⟩

noncomputable def branchCount (H : SimpleGraph V) (S : Finset V) (x : V) : ℕ :=
  ((S.erase x).image (cutVertex H x).connectedComponentMk).card

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_IntrinsicDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic distance and closest vertices in percolation clusters. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def closest (H : SimpleGraph V) (A : Set V) (x : V) : Set V :=
  {y | y ∈ A ∧ H.Reachable x y ∧ ∀ z ∈ A, H.Reachable x z → H.dist x y ≤ H.dist x z}

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_Vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Encounter vertices and infinite open branches. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

def cutConfig (G : BondGraph V E) (ω : Set E) (x : V) : Set E :=
  {e | e ∈ ω ∧ x ∉ G e}

def IsEncounter (G : BondGraph V E) (ω : Set E) (x : V) : Prop :=
  ∃ a b c : V,
    Conn G ω x a ∧ Conn G ω x b ∧ Conn G ω x c ∧
    (cluster G (cutConfig G ω x) a).Infinite ∧
    (cluster G (cutConfig G ω x) b).Infinite ∧
    (cluster G (cutConfig G ω x) c).Infinite ∧
    ¬ Conn G (cutConfig G ω x) a b ∧
    ¬ Conn G (cutConfig G ω x) a c ∧
    ¬ Conn G (cutConfig G ω x) b c

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_Measurability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of branches and finite clusters. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def clusterFinset (G : BondGraph V E) (ω : Set E) (x : V) : Finset V :=
  if h : (cluster G ω x).Finite then h.toFinset else ∅

end Percolation

end OAI
end


