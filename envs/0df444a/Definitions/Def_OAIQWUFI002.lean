-- Prove2me | Definitions.Def_OAIQWUFI002
-- name    : OAIQWUFI002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T19:44:52.027461+00:00
-- url     : https://prove2.me/theorems/237af257-b9c1-41e3-a2b4-23b054265098
-- title:
--   OpenAI universal F∞ group split: simplicial realizations and Milnor's construction (definitions bundle 3 of 9)
-- statement:
--   The definitions behind the Milnor and Brown statements of the split of OpenAI's proof that a single group of type $F_\infty$ contains every finitely presented group (OpenAI, *A universal group of type F∞*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). They are ported to Lean 4.33.1 and Mathlib 0df444a, and the bundle uses only Mathlib.
--
--   - **Realizations.** `Simplicial.Space K` is the geometric realization of a simplicial complex $K$ (Mathlib's `PreAbstractSimplicialComplex`). Its points are finitely supported weights summing to $1$ with support a face, and its topology is coinduced from the standard simplices (`SimplexDisk.Simplex`, `Simplicial.faceMap`). `Simplicial.inclusion` is the realization of an inclusion of complexes.
--   - **Milnor's complex.** `Milnor.complex G` is the complex on $\mathbb N \times G$ whose faces have at most one vertex at each level, and `Milnor.Space G` is its realization.
--   - **Shapes and stages.** `Milnor.Shapes G` are finite sets of finite subsets of $\mathbb N \times G$. `Milnor.stage G S` is the subcomplex spanned by the left translates of the shapes in $S \cup \{\{(0,1)\}\}$, and `Milnor.stageIncl` is the inclusion of stages.
--   - **Lemmas.** The bundle also contains the lemmas and instances these definitions use in their bodies (for example `weight_nonneg`, `weight_sum`, `continuous_inclusion`, `stage_mono`), and one small definition of OpenAI's, `Higman.RecognizingStack.support`, that the carver links to `Simplicial.Space`.
--
--   Modules: `HigmanEmbedding.lean`, `HomotopyProducts.lean`, `Milnor.lean`, `MilnorControl.lean`, `SimplexDisk.lean`, `Simplicial.lean`.
--
--   The statements `OAI.UniversalFInfinity.Milnor.contractible` (Milnor's construction is contractible) and `OAI.UniversalFInfinity.Brown.geometric_lifted_of_uniform` (OpenAI's variant of Brown's criterion) import only this bundle and, for the second, `Def_UniversalFInfinity`. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/UniversalGroup at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_UniversalFInfinity.HigmanEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

noncomputable section
namespace Higman.RecognizingStack
open Turing ToPartrec PartrecToTM2 Function Relation
variable {G : Type} [Group G]

def support (c : Code) := codeSupp c Cont'.halt

end Higman.RecognizingStack

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.SimplexDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
namespace UniversalFInfinity.SimplexDisk
noncomputable section

def Simplex (A : Type*) [Fintype A] : Set (A → ℝ) :=
  {x | (∀ a, 0 ≤ x a) ∧ ∑ a, x a = 1}

instance instCompactSpaceElemForallRealSimplex (A : Type*) [Fintype A] : CompactSpace (Simplex A) := by
  apply isCompact_iff_compactSpace.mp
  have closed : IsClosed (Simplex A) := by
    have description : Simplex A =
        (⋂ index, {point | (0 : ℝ) ≤ point index}) ∩ {point | ∑ index, point index = 1} := by
      ext point
      simp [Simplex]
    rw [description]
    exact (isClosed_iInter fun index => isClosed_le continuous_const (continuous_apply index)).inter
      (isClosed_eq (continuous_finsetSum _ fun index _ => continuous_apply index) continuous_const)
  apply (isCompact_Icc (a := (0 : A → ℝ)) (b := 1)).of_isClosed_subset closed
  intro point membership
  refine ⟨membership.1, fun index => ?_⟩
  change point index ≤ (1 : ℝ)
  rw [← membership.2]
  exact Finset.single_le_sum (fun other _ => membership.1 other) (Finset.mem_univ index)

end
end UniversalFInfinity.SimplexDisk

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Simplicial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators

namespace UniversalFInfinity.Simplicial

section
universe u v
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

def Space := {w : V →₀ ℝ | (∀ v, 0 ≤ w v) ∧ w.sum (fun _ r => r) = 1 ∧ w.support ∈ K}
abbrev Face := {s : Finset V // s ∈ K}

lemma support_nonempty {w : V →₀ ℝ} (h : w.sum (fun _ r => r) = 1) : w.support.Nonempty := by
  classical
  by_contra hn
  have hz : w = 0 := by
    apply Finsupp.support_eq_empty.mp
    exact Finset.not_nonempty_iff_eq_empty.mp hn
  simp [hz] at h

noncomputable def weight (s : Finset V) (x : SimplexDisk.Simplex s) : V →₀ ℝ :=
  Finsupp.embDomain (Function.Embedding.subtype (· ∈ s)) (Finsupp.equivFunOnFinite.symm x.1)

lemma weight_apply (s : Finset V) (x : SimplexDisk.Simplex s) (v : s) :
    weight s x v = x.1 v := by
  exact Finsupp.embDomain_apply_self _ _ _

lemma weight_apply_not (s : Finset V) (x : SimplexDisk.Simplex s) {v : V} (hv : v ∉ s) :
    weight s x v = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨w,hw⟩
  exact hv (hw ▸ w.2)

lemma weight_nonneg (s : Finset V) (x : SimplexDisk.Simplex s) (v : V) : 0 ≤ weight s x v := by
  classical
  by_cases hv : v ∈ s
  · exact (weight_apply s x ⟨v,hv⟩) ▸ x.2.1 ⟨v,hv⟩
  · rw [weight_apply_not _ _ hv]

lemma weight_sum (s : Finset V) (x : SimplexDisk.Simplex s) : (weight s x).sum (fun _ r => r) = 1 := by
  rw [weight,Finsupp.sum_embDomain,Finsupp.sum_fintype _ _ (fun _ => rfl)]
  exact x.2.2

lemma weight_support_subset (s : Finset V) (x : SimplexDisk.Simplex s) : (weight s x).support ⊆ s := by
  classical
  intro v hv
  by_contra hn
  exact Finsupp.mem_support_iff.mp hv (weight_apply_not _ _ hn)

noncomputable def faceMap (s : Face K) (x : SimplexDisk.Simplex s.1) : Space K :=
  ⟨weight s.1 x,weight_nonneg _ _,weight_sum _ _,
    K.isRelLowerSet_faces.mem_of_le s.2 (weight_support_subset _ _) (support_nonempty (weight_sum _ _))⟩

noncomputable def quotient (x : Σ s : Face K, SimplexDisk.Simplex s.1) : Space K := faceMap K x.1 x.2

instance instTopologicalSpaceElemFinsuppRealSpace : TopologicalSpace (Space K) := TopologicalSpace.coinduced (quotient K) inferInstance

lemma continuous_iff {Y : Type v} [TopologicalSpace Y] (f : Space K → Y) :
    Continuous f ↔ ∀ s : Face K, Continuous (f ∘ faceMap K s) := by
  rw [continuous_coinduced_dom]
  exact continuous_sigma_iff

lemma continuous_faceMap (s : Face K) : Continuous (faceMap K s) :=
  (continuous_coinduced_rng : Continuous (quotient K)).comp (continuous_sigmaMk (i := s))

end

open Set Metric Topology BigOperators
open scoped Classical
universe u
variable {V : Type u} (K L : PreAbstractSimplicialComplex V) (hKL : ∀ s ∈ K, s ∈ L)

def inclusion (x : Space K) : Space L := ⟨x.1,x.2.1,x.2.2.1,hKL _ x.2.2.2⟩

lemma continuous_inclusion : Continuous (inclusion K L hKL) := by
  rw [continuous_iff]
  intro s
  exact continuous_faceMap L ⟨s.1,hKL _ s.2⟩

end UniversalFInfinity.Simplicial

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.Milnor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators

namespace UniversalFInfinity.Milnor
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
local instance (priority := 2000) instDecidableEq_solutions_rb899b5_1 (α : Type*) : DecidableEq α := Classical.decEq α
variable (G : Type u)

def complex : PreAbstractSimplicialComplex (ℕ × G) where
  faces := {s | s.Nonempty ∧ Set.InjOn Prod.fst (s : Set (ℕ × G))}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1,fun t hts ht => ⟨ht,hs.2.mono hts⟩⟩

abbrev Space := Simplicial.Space (complex G)

end UniversalFInfinity.Milnor

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.MilnorControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Milnor

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical
universe u v
variable {G : Type u} [Group G]
local instance (priority := 2000) instDecidableEqProdNat_solutions_1 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def translate (g : G) (s : Finset (ℕ × G)) : Finset (ℕ × G) := s.image (fun v => (v.1,g*v.2))

def orbitSpan (S : Finset (Finset (ℕ × G))) : PreAbstractSimplicialComplex (ℕ × G) where
  faces := {t | t ∈ complex G ∧ ∃ g : G, ∃ s ∈ S, t ⊆ translate g s}
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨ht.1.1,?_⟩
    intro u hut hu
    obtain ⟨g,s,hs,hts⟩ := ht.2
    exact ⟨(complex G).isRelLowerSet_faces.mem_of_le ht.1 hut hu,g,s,hs,hut.trans hts⟩

lemma orbitSpan_mono {S T : Finset (Finset (ℕ × G))} (h : S ⊆ T) : orbitSpan S ≤ orbitSpan T := by
  intro t ht
  obtain ⟨g,s,hs,hts⟩ := ht.2
  exact ⟨ht.1,g,s,h hs,hts⟩

end
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
end UniversalFInfinity.Milnor

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.HomotopyProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Milnor

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy
universe u v
variable (G : Type u) [Group G]
local instance (priority := 2000) instDecidableEqProdNat_solutions_4 (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

abbrev Shapes := Finset (Finset (ℕ × G))
def basedShapes (S : Shapes G) : Shapes G := insert {(0,1)} S
def stage (S : Shapes G) := orbitSpan (basedShapes G S)

lemma stage_mono {S T : Shapes G} (h : S ⊆ T) : stage G S ≤ stage G T :=
  orbitSpan_mono (Finset.insert_subset_insert _ h)

def stageIncl (S T : Shapes G) (h : S ⊆ T) : C(Simplicial.Space (stage G S),Simplicial.Space (stage G T)) :=
  ⟨inclusion _ _ (fun _ hs => stage_mono G h hs),continuous_inclusion _ _ _⟩

end

open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical
universe u v
end UniversalFInfinity.Milnor

open Set Metric Topology

end

end OAI
end


