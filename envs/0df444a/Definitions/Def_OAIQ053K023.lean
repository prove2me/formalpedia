-- Prove2me | Definitions.Def_OAIQ053K023
-- name    : OAIQ053K023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:57:21.222561+00:00
-- url     : https://prove2.me/theorems/53f0c5b6-a82d-4760-8221-a0cc7e1d57ac
-- title:
--   Definitions bundle OAIQ053K023 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 77 declarations of OpenAI's Lean: 33 definitions, 1 inductive type or structure, 3 instances and 40 theorems. The definitions and types are `OAI.MetricKMedian.PCP.AlphabetReduction.interiorBound`, `OAI.MetricKMedian.PCP.AlphabetReduction.interiorEmbed`, `OAI.MetricKMedian.PCP.AlphabetReduction.nodeEmbed`, `OAI.MetricKMedian.PCP.AlphabetReduction.paddedBinary`, `OAI.MetricKMedian.PCP.AlphabetReduction.positionEmbed`, `OAI.MetricKMedian.PCP.BinaryCSP.mapVertices`, `OAI.MetricKMedian.PCP.CloudCopies.Active`, `OAI.MetricKMedian.PCP.CloudCopies.Copy`, `OAI.MetricKMedian.PCP.CloudCopies.Incident`, `OAI.MetricKMedian.PCP.CloudCopies.Node`, `OAI.MetricKMedian.PCP.CloudCopies.depth`, `OAI.MetricKMedian.PCP.CloudCopies.endpoint`, `OAI.MetricKMedian.PCP.CloudCopies.equalityGraph`, `OAI.MetricKMedian.PCP.CloudCopies.equalityRotate`, `OAI.MetricKMedian.PCP.CloudCopies.owner`, `OAI.MetricKMedian.PCP.ExpanderFamily.base`, `OAI.MetricKMedian.PCP.ExpanderFamily.baseVertexEquiv`, `OAI.MetricKMedian.PCP.ExpanderFamily.graph`, `OAI.MetricKMedian.PCP.PortCSP`, `OAI.MetricKMedian.PCP.PortCSP.Bad`, `OAI.MetricKMedian.PCP.PortCSP.extendedAllowed`, `OAI.MetricKMedian.PCP.PortGraph.Walk.cast`, `OAI.MetricKMedian.PCP.PortGraph.Walk.centerEquiv`, `OAI.MetricKMedian.PCP.PortGraph.Walk.concat`, `OAI.MetricKMedian.PCP.PortGraph.Walk.splitEquiv`, `OAI.MetricKMedian.PCP.PortGraph.extend`, `OAI.MetricKMedian.PCP.Walsh.baseGenerators`, `OAI.MetricKMedian.PCP.Walsh.baseGraph`, `OAI.MetricKMedian.PCP.Walsh.bias`, `OAI.MetricKMedian.PCP.Walsh.cayley`, `OAI.MetricKMedian.PCP.Walsh.cayleyRotate`, `OAI.MetricKMedian.PCP.Walsh.character`, `OAI.MetricKMedian.PCP.Walsh.coefficient`, `OAI.MetricKMedian.PCP.Walsh.sign`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_PaddedAlphabet`, `KMedian_Amplification_PoweringMean`, `KMedian_Amplification_PoweringObjects`, `KMedian_Expanders_Cayley`, `KMedian_Expanders_CloudCopies`, `KMedian_Expanders_ExpanderFamily`, `KMedian_Expanders_GraphExtend`, `KMedian_Expanders_Rademacher`, `KMedian_Expanders_SmallBias`, `KMedian_Expanders_WalkSegments`, `KMedian_Expanders_Walsh`, `KMedian_Machines_VertexMap`, `KMedian_PCP_BinaryReduction`, `KMedian_PCP_FiniteTest`, `KMedian_PCP_Hadamard`, `KMedian_PCP_LocalReduction`, `KMedian_PCP_Queries`, `KMedian_Rounding_MarginalRounding`.
--
--   **Imports.** It imports the bundles `OAIQ053K000`, `OAIQ053K001`, `OAIQ053K002`, `OAIQ053K005`, `OAIQ053K008` and `OAIQ053K009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K034`, `OAIQ053K035`, `OAIQ053K036` and `OAIQ053K037`; the statements `OAI.MetricKMedian.PCP.AlphabetReduction.padded_complete_s53` and `OAI.MetricKMedian.PCP.ExpanderFamily.graph_contracts_s53`; the proofs of `OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec_s53` and `OAI.MetricKMedian.PCP.ExpanderFamily.graph_contracts_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K001
import Definitions.Def_OAIQ053K002
import Definitions.Def_OAIQ053K005
import Definitions.Def_OAIQ053K008
import Definitions.Def_OAIQ053K009

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_FiniteTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteTest

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Rates
variable {S T : Type} [Fintype S] [Fintype T]

theorem testRate_congr {p q : S → Prop} (h : ∀ s, p s ↔ q s) : testRate p = testRate q := by
  classical
  apply expect_congr rfl
  intro s _
  simp only [h s]

theorem testRate_mono {p q : S → Prop} (h : ∀ s, p s → q s) : testRate p ≤ testRate q := by
  classical
  apply expect_le_expect
  intro s _
  by_cases hp : p s
  · simp [hp, h s hp]
  · simp only [ite_eq_right hp]; split_ifs <;> norm_num

theorem testRate_true [Nonempty S] : testRate (fun _ : S => True) = 1 := by
  classical
  simp [testRate]

theorem testRate_complement (p : S → Prop) [Nonempty S] :
    testRate p + testRate (fun s => ¬ p s) = 1 := by
  classical
  unfold testRate
  rw [← expect_add_distrib]
  convert Fintype.expect_one (ι := S) (M := ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  apply expect_congr rfl
  intro s _
  by_cases hp : p s <;> simp [hp]

theorem testRate_equiv (e : S ≃ T) (p : T → Prop) :
    testRate (fun s => p (e s)) = testRate p := by
  classical
  exact Fintype.expect_equiv e _ _ (fun _ => rfl)

end Rates

end MetricKMedian.PCP

end Inline_PCPFiniteTest

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Hadamard
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.QuadraticSystem.combination_add _root_.OAI.MetricKMedian.PCP.QuadraticSystem.combination_single _root_.OAI.MetricKMedian.PCP.QuadraticSystem.combination_zero _root_.OAI.MetricKMedian.PCP.QuadraticSystem.dot_combination _root_.OAI.MetricKMedian.PCP.QuadraticSystem.equationDiscrepancy_single _root_.OAI.MetricKMedian.PCP.RelationEncoding.witness_left _root_.OAI.MetricKMedian.PCP.RelationEncoding.witness_right _root_.OAI.MetricKMedian.PCP.dot_liftQuery _root_.OAI.MetricKMedian.PCP.dot_single _root_.OAI.MetricKMedian.PCP.dot_smul _root_.OAI.MetricKMedian.PCP.dot_sum _root_.OAI.MetricKMedian.PCP.dot_unitForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPHadamard

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

theorem bit_cases (b : Bit) : b = 0 ∨ b = 1 := by
  have hlt := ZMod.val_lt b
  have hb : b.val = 0 ∨ b.val = 1 := by omega
  rcases hb with hb | hb
  · left; apply ZMod.val_injective 2; simpa using hb
  · right; apply ZMod.val_injective 2; change b.val = 1; exact hb

theorem bit_add_one_ne_zero (b : Bit) : b + 1 ≠ 0 ↔ b = 0 := by
  rcases bit_cases b with rfl | rfl <;> decide

section Balance
variable {G : Type} [AddCommGroup G] [Fintype G]

theorem linear_nonzero_rate (g : G →+ Bit) (z : G) (hz : g z ≠ 0) :
    testRate (fun x => g x ≠ 0) = 1/2 := by
  have hg : g z = 1 := (bit_cases (g z)).resolve_left hz
  have he := testRate_equiv (Equiv.addRight z) (fun x => g x ≠ 0)
  have hc : testRate (fun x => g (x + z) ≠ 0) =
      testRate (fun x => ¬ (g x ≠ 0)) := by
    apply testRate_congr
    intro x
    simp only [map_add, hg, bit_add_one_ne_zero, not_not]
  have hcomp := testRate_complement (fun x => g x ≠ 0)
  change testRate (fun x => g (x + z) ≠ 0) = _ at he
  linarith

end Balance

end MetricKMedian.PCP

end Inline_PCPHadamard

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_LocalReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLocalReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace LocalRelation
variable {K : Type} [Fintype K] [DecidableEq K]

variable (R : Relation K) [DecidablePred (· ∈ R)]

instance instDecidableEqEqs : DecidableEq (Eqs R) := by
  letI : DecidableEq (Allowed R) := inferInstance
  infer_instance

end LocalRelation
end MetricKMedian.PCP

end Inline_PCPLocalReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Queries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPQueries

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace LocalRelation
variable {K : Type} [Fintype K] [DecidableEq K]
variable (R : Relation K) [DecidablePred (· ∈ R)]

instance sampleFintype (i : Fin 6) : Fintype (Sample R i) :=
  match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
  | 3 => inferInstance
  | 4 => inferInstance
  | 5 => inferInstance

end LocalRelation
end MetricKMedian.PCP

end Inline_PCPQueries

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_VertexMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPVertexMap
namespace MetricKMedian.PCP.BinaryCSP
open scoped Classical

variable {V W E A : Type} [Fintype E] [DecidableEq A]
variable (C : BinaryCSP V E A) (e : V ↪ W)
def mapVertices : BinaryCSP W E A where
  left t := e (C.left t)
  right t := e (C.right t)
  allowed := C.allowed
end MetricKMedian.PCP.BinaryCSP

end Inline_PCPVertexMap

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_BinaryReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBinaryReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace AlphabetReduction
variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]
variable (C : BinaryCSP V E (BitVector K))

noncomputable def interiorBound (K : Type) [Fintype K] [DecidableEq K] : ℕ :=
  ∑ R : Relations K, Fintype.card (BitVector (LocalRelation.Vars (R : LocalRelation.Relation K)) ⊕
    BitVector (LocalRelation.Vars (R : LocalRelation.Relation K) ×
      LocalRelation.Vars (R : LocalRelation.Relation K)))

end AlphabetReduction
end MetricKMedian.PCP

end Inline_PCPBinaryReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PaddedAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPaddedAlphabet
namespace MetricKMedian.PCP.AlphabetReduction
open Finset
open scoped BigOperators Classical

variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]
noncomputable instance paddedNodeFintype : Fintype (PaddedNode V E K) := by
  classical
  letI : Fintype (PaddedPosition V E K) := inferInstance
  letI : Fintype (E × EdgeSample K) := inferInstance
  exact inferInstanceAs (Fintype (PaddedPosition V E K ⊕ (E × EdgeSample K)))
variable (C : BinaryCSP V E (BitVector K))
def interiorEmbed : ((e : E) × Interior C e) ↪ (E × UniversalInterior K) :=
  (Function.Embedding.sigmaMap (Function.Embedding.refl E)
    (fun e => Function.Embedding.sigmaMk (β := RelationInterior) (C.allowed e))).trans (Equiv.sigmaEquivProd _ _).toEmbedding
def positionEmbed : Position C ↪ PaddedPosition V E K :=
  Function.Embedding.sumMap (Function.Embedding.refl _) (interiorEmbed C)
def nodeEmbed : (Position C ⊕ Test (E := E) (K := K)) ↪ PaddedNode V E K :=
  Function.Embedding.sumMap (positionEmbed C) (Function.Embedding.refl _)
def paddedBinary : BinaryCSP (PaddedNode V E K) (Test (E := E) (K := K) × Fin 4) IncidenceReduction.Label :=
  (binary C).mapVertices (nodeEmbed C)
end MetricKMedian.PCP.AlphabetReduction

end Inline_PCPPaddedAlphabet

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_WalkSegments
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_succ _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_zero _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPWalkSegments

namespace MetricKMedian.PCP.PortGraph
open Finset
open scoped BigOperators

variable {V D : Type} {G : PortGraph V D}
namespace Walk
variable {n m : ℕ}

def concat (p : G.Walk n) (q : G.Walk m) (h : p.vertex (Fin.last n) = q.vertex 0) : G.Walk (n+m) where
  vertex := catVertex p q
  port := catPort p q
  chain i := by
    by_cases hi : i.val < n
    · dsimp only [catVertex,catPort,Fin.val_castSucc,Fin.val_succ]
      simp only [dite_eq_left hi, dite_eq_left (by omega : i.val ≤ n), dite_eq_left (by omega : i.val+1 ≤ n)]
      exact p.chain ⟨i.val,hi⟩
    · by_cases he : i.val = n
      · dsimp only [catVertex,catPort,Fin.val_castSucc,Fin.val_succ]
        simp only [dite_eq_right hi, dite_eq_left (by omega : i.val ≤ n), dite_eq_right (by omega : ¬ i.val+1 ≤ n)]
        have hn : 0 < m := by omega
        have hl : p.vertex ⟨i.val,by omega⟩ = q.vertex 0 := by
          convert h using 1; congr 1; exact Fin.ext he
        rw [hl]
        convert q.chain ⟨0,hn⟩ using 1 <;> congr 2 <;> first | exact Fin.ext (by dsimp; omega) | (dsimp; omega)
      · dsimp only [catVertex,catPort,Fin.val_castSucc,Fin.val_succ]
        simp only [dite_eq_right hi, dite_eq_right (by omega : ¬ i.val ≤ n), dite_eq_right (by omega : ¬ i.val+1 ≤ n)]
        convert q.chain ⟨i.val-n,by omega⟩ using 1 <;> congr 1
        apply Fin.ext
        simp
        omega

@[simp] theorem concat_start (p : G.Walk n) (q : G.Walk m) (h) :
    (p.concat q h).vertex 0 = p.vertex 0 := by simp [concat,catVertex]

@[simp] theorem concat_end (p : G.Walk n) (q : G.Walk m) (h) :
    (p.concat q h).vertex (Fin.last (n+m)) = q.vertex (Fin.last m) := by
  by_cases hm : m=0
  · subst m
    simpa [concat,catVertex,Fin.last] using h
  · simp [concat,catVertex,Fin.last,show ¬ n+m ≤ n by omega]

@[simp] theorem segment_concat_left (p : G.Walk n) (q : G.Walk m) (h) :
    (p.concat q h).segment 0 n (by omega) = p := by
  apply Walk.ext
  · funext i
    simp [segment,concat,catVertex,show i.val ≤ n by omega]
  · funext i
    simp [segment,concat,catPort]

@[simp] theorem segment_concat_right (p : G.Walk n) (q : G.Walk m) (h) :
    (p.concat q h).segment n m (by omega) = q := by
  apply Walk.ext
  · funext i
    by_cases hi : i.val=0
    · have hei : i=0 := Fin.ext hi
      subst i
      simpa [segment,concat,catVertex,Fin.last] using h
    · dsimp only [segment,concat,catVertex]
      rw [dite_eq_right (by omega : ¬ n+i.val ≤ n)]
      congr 1
      exact Fin.ext (by simp)
  · funext i
    simp [segment,concat,catPort]

theorem concat_segments (p : G.Walk (n+m)) :
    (p.segment 0 n (by omega)).concat (p.segment n m (by omega)) (by simp [segment]) = p := by
  apply Walk.ext
  · funext i
    dsimp [concat,catVertex,segment]
    split_ifs with hi
    · congr 1; apply Fin.ext; simp
    · congr 1; apply Fin.ext; simp; omega
  · funext i
    dsimp [concat,catPort,segment]
    split_ifs with hi
    · congr 1; apply Fin.ext; simp
    · congr 1; apply Fin.ext; simp; omega

def splitEquiv (n m : ℕ) : G.Walk (n+m) ≃ G.Walk n × (Fin m → D) where
  toFun p := (p.segment 0 n (by omega), (p.segment n m (by omega)).port)
  invFun z := z.1.concat (ofWord (z.1.vertex (Fin.last n)) z.2) (by simp [ofWord])
  left_inv p := by
    have hq : ofWord ((p.segment 0 n (by omega)).vertex (Fin.last n))
        (p.segment n m (by omega)).port = p.segment n m (by omega) := by
      apply Walk.ext
      · have hb : (p.segment 0 n (by omega)).vertex (Fin.last n) =
            (p.segment n m (by omega)).vertex 0 := by simp [segment]
        change G.trace m ((p.segment 0 n (by omega)).vertex (Fin.last n)) _ = _
        rw [hb]
        exact (vertex_eq_trace (p.segment n m (by omega))).symm
      · rfl
    simp only [hq,concat_segments]
  right_inv z := by simp [ofWord]

end Walk
end MetricKMedian.PCP.PortGraph

end Inline_PCPWalkSegments

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringObjects
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_succ _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_zero _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringObjects

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph.Walk
variable {V D : Type} {G : PortGraph V D} {n : ℕ}

@[simp] theorem reverse_end (p : G.Walk n) : p.reverse.vertex (Fin.last n) = p.vertex 0 := by
  simp [reverse]

def centerEquiv (n m : ℕ) : G.Walk (n+(m+1)) ≃ (V × (Fin n → D)) × (D × (Fin m → D)) :=
  (splitEquiv n (m+1)).trans (Equiv.prodCongr
    ((reverseEquiv (G := G) (n := n)).trans wordEquiv)
    (Fin.consEquiv (fun _ : Fin (m+1) => D)).symm)

@[simp] theorem center_vertex (n m : ℕ) (p : G.Walk (n+(m+1))) :
    (centerEquiv n m p).1.1 = p.vertex ⟨n,by omega⟩ := by
  simp [centerEquiv, splitEquiv, reverseEquiv, wordEquiv, segment, reverse]

@[simp] theorem center_port (n m : ℕ) (p : G.Walk (n+(m+1))) :
    (centerEquiv n m p).2.1 = p.port ⟨n,by omega⟩ := by
  simp [centerEquiv, splitEquiv, Fin.consEquiv, segment]

@[simp] theorem center_left_end (n m : ℕ) (s : (V × (Fin n → D)) × (D × (Fin m → D))) :
    ((centerEquiv (G := G) n m).symm s).vertex 0 =
      (ofWord (G := G) s.1.1 s.1.2).vertex (Fin.last n) := by
  simp [centerEquiv, splitEquiv, reverseEquiv, wordEquiv]

@[simp] theorem center_right_end (n m : ℕ) (s : (V × (Fin n → D)) × (D × (Fin m → D))) :
    ((centerEquiv (G := G) n m).symm s).vertex (Fin.last (n+(m+1))) =
      (ofWord (G := G) (G.step s.1.1 s.2.1) s.2.2).vertex (Fin.last m) := by
  change ((ofWord (G := G) s.1.1 s.1.2).reverse.concat
    (ofWord ((ofWord (G := G) s.1.1 s.1.2).reverse.vertex (Fin.last n))
      (Fin.cons s.2.1 s.2.2)) (by simp [ofWord])).vertex (Fin.last (n+(m+1))) = _
  rw [concat_end, reverse_end]
  change G.trace (m+1) (G.trace n s.1.1 s.1.2 0)
    (Fin.cons s.2.1 s.2.2) (Fin.last m).succ = _
  simp only [PortGraph.trace_zero, PortGraph.trace_succ, Fin.cons_zero, Fin.cons_succ]
  rfl

end PortGraph.Walk

structure PortCSP {V D : Type} (G : PortGraph V D) (A : Type) where
  allowed : V × D → Finset (A × A)
  symmetric : ∀ p a b, (a,b) ∈ allowed (G.rotate p) ↔ (b,a) ∈ allowed p

namespace PortCSP
variable {V D A : Type} {G : PortGraph V D}
variable [DecidableEq A] (C : PortCSP G A)

def Bad (x : V → A) (p : V × D) : Prop := (x p.1,x (G.step p.1 p.2)) ∉ C.allowed p

end PortCSP

end MetricKMedian.PCP

end Inline_PCPPoweringObjects

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringMean

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph.Walk
variable {V D : Type} {G : PortGraph V D}
def cast {n m : ℕ} (h : n=m) (p : G.Walk n) : G.Walk m := h ▸ p
end PortGraph.Walk

end MetricKMedian.PCP

end Inline_PCPPoweringMean

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_Walsh
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.QuadraticSystem.dot_combination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPWalsh

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Walsh
noncomputable def sign (b : Bit) : ℝ := if b=0 then 1 else -1
@[simp] lemma sign_zero : sign 0=1 := by simp [sign]
@[simp] lemma sign_one : sign 1= -1 := by norm_num [sign]
lemma sign_cases (b : Bit) : sign b=1 ∨ sign b= -1 := by
  rcases bit_cases b with rfl | rfl <;> simp
@[simp] lemma sign_sq (b : Bit) : sign b ^ 2=1 := by
  rcases sign_cases b with h | h <;> rw [h] <;> norm_num

variable {I : Type} [Fintype I]
noncomputable def character (b x : BitVector I) : ℝ := sign (dot b x)
@[simp] lemma character_zero (x : BitVector I) : character 0 x=1 := by simp [character]
@[simp] lemma character_sq (b x : BitVector I) : character b x^2=1 := by simp [character]
lemma character_cases (b x : BitVector I) : character b x=1 ∨ character b x= -1 := sign_cases _

variable [DecidableEq I]

lemma character_mean (b : BitVector I) : (𝔼 x, character b x) = if b=0 then 1 else 0 := by
  classical
  by_cases hb : b=0
  · subst b; simp
  rw [ite_eq_right hb]
  obtain ⟨i,hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    exact hb (funext h)
  have hd : dot b (Pi.single i 1) ≠ 0 := by simpa only [dot_single] using hi
  have hbalance := linear_nonzero_rate (dotHom b) (Pi.single i 1) hd
  have he (x : BitVector I) : character b x=1-2*(if dot b x ≠ 0 then (1:ℝ) else 0) := by
    unfold character sign
    split_ifs <;> norm_num; simp_all
  simp_rw [he]
  rw [expect_sub_distrib, ← mul_expect, Fintype.expect_const]
  have hh : (𝔼 x : BitVector I, if dot b x ≠ 0 then (1:ℝ) else 0) =
      testRate (fun x => dotHom b x ≠ 0) := by
    unfold testRate
    apply expect_congr rfl
    intro x _
    by_cases hx : dot b x ≠ 0 <;> simp [dotHom,hx]
  rw [hh,hbalance]
  norm_num

noncomputable def coefficient (f : BitVector I → ℝ) (b : BitVector I) : ℝ :=
  pairing f (character b)

@[simp] lemma coefficient_zero (f : BitVector I → ℝ) : coefficient f 0=𝔼 x, f x := by
  simp [coefficient,pairing]

end Walsh
end MetricKMedian.PCP

end Inline_PCPWalsh

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_Cayley
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_right_end _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step _root_.OAI.MetricKMedian.PCP.QuadraticSystem.dot_combination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCayley

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Walsh
variable {I D : Type} [Fintype I] [DecidableEq I]

def cayleyRotate (g : D → BitVector I) (p : BitVector I × D) : BitVector I × D :=
  (p.1+g p.2,p.2)
omit [Fintype I] [DecidableEq I] in
lemma cayleyRotate_involutive (g : D → BitVector I) : Function.Involutive (cayleyRotate g) := by
  rintro ⟨v,d⟩
  unfold cayleyRotate
  congr 1
  have hg : g d+g d=0 := funext (fun i => CharTwo.add_self_eq_zero (g d i))
  rw [add_assoc,hg,add_zero]

def cayley (g : D → BitVector I) : PortGraph (BitVector I) D where
  rotate := { toFun := cayleyRotate g
              invFun := cayleyRotate g
              left_inv := cayleyRotate_involutive g
              right_inv := cayleyRotate_involutive g }
  involutive := cayleyRotate_involutive g

omit [Fintype I] [DecidableEq I] in
@[simp] lemma cayley_step (g : D → BitVector I) (v : BitVector I) (d : D) :
    (cayley g).step v d=v+g d := rfl

variable [Fintype D] [Nonempty D]
noncomputable def bias (g : D → BitVector I) (b : BitVector I) : ℝ := 𝔼 d, character b (g d)

end Walsh
end MetricKMedian.PCP

end Inline_PCPCayley

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_Rademacher
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRademacher

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Rademacher
variable {S : Type} [Fintype S] [Nonempty S] (f : S → ℝ)
variable (hf : ∀ x, f x = 1 ∨ f x = -1) (hmean : (𝔼 x, f x)=0)

include hf hmean

theorem large_sum_rate (n : ℕ) (a : ℝ) (ha : 0 < a) :
    testRate (fun c : Fin n → S => a ≤ |wordSum f n c|) * a^10 ≤ 945*(n:ℝ)^5 := by
  classical
  have hm : testRate (fun c : Fin n → S => a ≤ |wordSum f n c|) * a^10 ≤ moment f n 10 := by
    unfold testRate moment
    rw [expect_mul]
    apply expect_le_expect
    intro c _
    dsimp only
    by_cases hc : a ≤ |wordSum f n c|
    · rw [ite_eq_left hc, one_mul]
      have hpow := pow_le_pow_left₀ (le_of_lt ha) hc 10
      simpa only [Even.pow_abs (by decide : Even 10)] using hpow
    · rw [ite_eq_right hc, zero_mul]
      exact Even.pow_nonneg (by decide : Even 10) _
  exact hm.trans (moments_bound f hf hmean n).2.2.2.2

end Rademacher
end MetricKMedian.PCP

end Inline_PCPRademacher

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_SmallBias
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.QuadraticSystem.dot_combination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSmallBias

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

lemma testRate_exists_le_sum {S B : Type} [Fintype S] [Fintype B] (p : B → S → Prop) :
    testRate (fun s => ∃ b, p b s) ≤ ∑ b, testRate (p b) := by
  classical
  unfold testRate
  rw [← expect_sum_comm]
  apply expect_le_expect
  intro s _
  by_cases h : ∃ b, p b s
  · rw [ite_eq_left h]
    obtain ⟨b,hb⟩ := h
    calc
      (1:ℝ) = (if p b s then 1 else 0) := by rw [ite_eq_left hb]
      _ ≤ ∑ b, if p b s then (1:ℝ) else 0 :=
        single_le_sum (f := fun b => if p b s then (1:ℝ) else 0)
          (fun b _ => by split_ifs <;> norm_num) (mem_univ b)
  · rw [ite_eq_right h]
    exact sum_nonneg (fun b _ => by split_ifs <;> norm_num)

namespace Walsh
variable {I : Type} [Fintype I] [DecidableEq I]

lemma small_bias_word_bound (b : BitVector I) (n : ℕ) (ρ : ℝ) (hn : 0 < n) (hρ : 0 < ρ) :
    testRate (fun g : Fin n → BitVector I => b≠0 ∧ ρ ≤ |bias g b|) * ((n:ℝ)*ρ)^10 ≤
      945*(n:ℝ)^5 := by
  classical
  by_cases hb : b=0
  · subst b
    have he : testRate (fun g : Fin n → BitVector I => (0:BitVector I)≠0 ∧ ρ ≤ |bias g 0|)=0 := by
      simp [testRate]
    rw [he,zero_mul]
    positivity
  have hbmean : (𝔼 x, character b x)=0 := by rw [character_mean,ite_eq_right hb]
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hh := Rademacher.large_sum_rate (character b) (character_cases b) hbmean n ((n:ℝ)*ρ)
    (mul_pos hnR hρ)
  have hi : testRate (fun g : Fin n → BitVector I => b≠0 ∧ ρ ≤ |bias g b|) ≤
      testRate (fun g : Fin n → BitVector I => (n:ℝ)*ρ ≤ |Rademacher.wordSum (character b) n g|) := by
    apply testRate_mono
    intro g hg
    unfold bias at hg
    rw [Fintype.expect_eq_sum_div_card] at hg
    simp only [Fintype.card_fin,abs_div,abs_of_pos hnR] at hg
    change (n:ℝ)*ρ ≤ |∑ i, character b (g i)|
    have ht := (le_div_iff₀ hnR).mp hg.2
    simpa only [mul_comm] using ht
  exact (mul_le_mul_of_nonneg_right hi (by positivity)).trans hh

theorem exists_small_bias (n : ℕ) (ρ : ℝ) (hn : 0 < n) (hρ : 0 < ρ)
    (hsize : (Fintype.card (BitVector I):ℝ)*945*(n:ℝ)^5 < ((n:ℝ)*ρ)^10) :
    ∃ g : Fin n → BitVector I, ∀ b, b≠0 → |bias g b| < ρ := by
  classical
  let p (b : BitVector I) (g : Fin n → BitVector I) := b≠0 ∧ ρ ≤ |bias g b|
  have hu := testRate_exists_le_sum p
  have hbound : testRate (fun g : Fin n → BitVector I => ∃ b, p b g) * ((n:ℝ)*ρ)^10 ≤
      (Fintype.card (BitVector I):ℝ)*945*(n:ℝ)^5 := by
    calc
      _ ≤ (∑ b, testRate (p b))*((n:ℝ)*ρ)^10 := mul_le_mul_of_nonneg_right hu (by positivity)
      _ = ∑ b, testRate (p b)*((n:ℝ)*ρ)^10 := sum_mul _ _ _
      _ ≤ ∑ _b : BitVector I, 945*(n:ℝ)^5 := sum_le_sum (fun b _ => small_bias_word_bound b n ρ hn hρ)
      _ = _ := by simp; ring
  have hlt : testRate (fun g : Fin n → BitVector I => ∃ b, p b g) < 1 := by
    have hh := hbound.trans_lt hsize
    have hw : 0 < ((n:ℝ)*ρ)^10 := pow_pos (mul_pos (Nat.cast_pos.mpr hn) hρ) _
    nlinarith
  by_contra h
  push Not at h
  have hall : ∀ g : Fin n → BitVector I, ∃ b, p b g := by
    intro g
    obtain ⟨b,hb,hbad⟩ := h g
    exact ⟨b,hb,hbad⟩
  have he : testRate (fun g : Fin n → BitVector I => ∃ b, p b g)=1 := by
    rw [testRate_congr (fun g => iff_true_intro (hall g)),testRate_true]
  linarith

theorem exists_base_generators : ∃ g : Fin (2^44) → BitVector (Fin 176),
    ∀ b, b≠0 → |bias g b| ≤ 1/10 := by
  obtain ⟨g,hg⟩ := exists_small_bias (I := Fin 176) (2^44) (1/10) (by positivity) (by norm_num)
    (by simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card]; norm_num)
  exact ⟨g,fun b hb => le_of_lt (hg b hb)⟩

noncomputable def baseGenerators : Fin (2^44) → BitVector (Fin 176) :=
  Classical.choose exists_base_generators
noncomputable def baseGraph : PortGraph (BitVector (Fin 176)) (Fin (2^44)) := cayley baseGenerators

end Walsh
end MetricKMedian.PCP

end Inline_PCPSmallBias

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderFamily
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.QuadraticSystem.dot_combination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderFamily

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace ExpanderFamily

noncomputable def baseVertexEquiv : BitVector (Fin 176) ≃ Branch :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card,Fintype.card_prod]
    norm_num)

noncomputable def base : PortGraph Branch SmallPort :=
  Walsh.baseGraph.relabel baseVertexEquiv (Equiv.refl SmallPort)

noncomputable def graph : (n : ℕ) → PortGraph (Vertex n) Degree
  | 0 => { rotate := Equiv.refl _
           involutive := fun _ => rfl }
  | n+1 => (graph n).square.zigzag base

end ExpanderFamily
end MetricKMedian.PCP

end Inline_PCPExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudCopies
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_right_end _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloudCopies

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace CloudCopies
variable {V E A : Type} [Fintype V] [Fintype E]
variable (C : BinaryCSP V E A)

def endpoint (d : Dart (E := E)) : V := if d.2 then C.right d.1 else C.left d.1
abbrev Active := Set.range (endpoint C)
def owner (d : Dart (E := E)) : Active C := ⟨endpoint C d,Set.mem_range_self d⟩

abbrev Incident (v : Active C) := {d : Dart (E := E) // owner C d=v}

noncomputable def depth (v : Active C) := ExpanderFamily.level (Fintype.card (Incident C v)-1)
abbrev Copy (v : Active C) := ExpanderFamily.Vertex (depth C v)
abbrev Node := (v : Active C) × Copy C v

noncomputable def equalityRotate (p : Node C × ExpanderFamily.Degree) : Node C × ExpanderFamily.Degree :=
  (⟨p.1.1,(ExpanderFamily.graph (depth C p.1.1)).step p.1.2 p.2⟩,
    (ExpanderFamily.graph (depth C p.1.1)).back p.1.2 p.2)

omit [Fintype V] in
lemma equalityRotate_involutive : Function.Involutive (equalityRotate C) := by
  rintro ⟨⟨v,w⟩,d⟩
  simp only [equalityRotate,PortGraph.step_back,PortGraph.back_back]

noncomputable def equalityGraph : PortGraph (Node C) ExpanderFamily.Degree where
  rotate := { toFun := equalityRotate C
              invFun := equalityRotate C
              left_inv := equalityRotate_involutive C
              right_inv := equalityRotate_involutive C }
  involutive := equalityRotate_involutive C

omit [Fintype V] in
@[simp] lemma equality_step (v : Active C) (w : Copy C v) (d : ExpanderFamily.Degree) :
    (equalityGraph C).step ⟨v,w⟩ d=⟨v,(ExpanderFamily.graph (depth C v)).step w d⟩ := rfl

end CloudCopies
end MetricKMedian.PCP

end Inline_PCPCloudCopies

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_GraphExtend
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_succ _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_zero _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGraphExtend

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortGraph
variable {V W D : Type} [Fintype V] [Fintype D] [DecidableEq W] [DecidableEq D]
variable (G : PortGraph V D) (e : V ↪ W)

def extend : PortGraph W D where
  rotate := Equiv.Perm.viaFintypeEmbedding G.rotate (portEmbed e)
  involutive := extend_involutive _ G.involutive _

@[simp] lemma extend_rotate_image (p : V × D) :
    (G.extend e).rotate (e p.1,p.2)=(e (G.rotate p).1,(G.rotate p).2) :=
  Equiv.Perm.viaFintypeEmbedding_apply_image _ _ p

@[simp] lemma extend_step_image (v : V) (d : D) :
    (G.extend e).step (e v) d=e (G.step v d) :=
  congrArg Prod.fst (G.extend_rotate_image e (v,d))

lemma extend_rotate_outside (p : W × D) (hp : p.1 ∉ Set.range e) : (G.extend e).rotate p=p :=
  Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ (fun h => hp ((portEmbed_range e p).mp h))

end PortGraph

namespace PortCSP
variable {V W D A : Type} [Fintype V] [Fintype D] [DecidableEq W] [DecidableEq D]
  [Fintype A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) (e : V ↪ W)

noncomputable def extendedAllowed (p : W × D) : Finset (A × A) :=
  if h : p ∈ Set.range (PortGraph.portEmbed e) then
    C.allowed ((PortGraph.portEmbed e).toEquivRange.symm ⟨p,h⟩) else univ

end PortCSP
end MetricKMedian.PCP

end Inline_PCPGraphExtend

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_MarginalRounding
attribute [-simp] _root_.OAI.MetricKMedian.RationalWeightedStep.real_fractional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.MarginalRounding

variable {I : Type*} [Fintype I]

theorem second_fractional {p : I → ℝ} {K : ℕ} (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i = K) {i : I} (hi : i ∈ fractional p) :
    ∃ j ∈ fractional p, j ≠ i := by
  classical
  by_contra h
  push Not at h
  have hother : ∀ j, j ≠ i → j ∉ fractional p := by
    intro j hji hj
    exact hji (h j hj)
  have hi0 := (mem_fractional p i).mp hi
  have hpoint : ∀ j, p j = (if p j=1 then (1:ℝ) else 0)+(if j=i then p i else 0) := by
    intro j
    by_cases hji : j=i
    · subst j
      rw [ite_eq_right (ne_of_lt hi0.2), ite_eq_left rfl, zero_add]
    · rw [ite_eq_right hji, add_zero]
      rcases nonfractional_integral hp hp1 (hother j hji) with hj | hj <;> simp [hj]
  let S := Finset.univ.filter (fun j => p j=1)
  have hid : (∑ j, p j) = (S.card:ℝ)+p i := by
    conv_lhs => arg 2; ext j; rw [hpoint j]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    congr 1
    rw [← Finset.sum_filter]
    simp only [S, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hlow : S.card < K := by
    have hh : (S.card:ℝ) < K := by linarith only [hi0.1, hid, hsum]
    exact_mod_cast hh
  have hhigh : K < S.card+1 := by
    have hh : (K:ℝ) < (S.card+1:ℕ) := by push_cast; linarith only [hi0.2, hid, hsum]
    exact_mod_cast hh
  omega

end MetricKMedian.MarginalRounding
end
end

end OAI
end


