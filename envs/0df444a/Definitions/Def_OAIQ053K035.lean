-- Prove2me | Definitions.Def_OAIQ053K035
-- name    : OAIQ053K035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:01:40.754664+00:00
-- url     : https://prove2.me/theorems/9ea5aae0-a65c-49f8-a5be-9a0ca8aeab1f
-- title:
--   Definitions bundle OAIQ053K035 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 55 declarations of OpenAI's Lean: 29 definitions, 6 instances and 20 theorems. The definitions and types are `OAI.MetricKMedian.PCP.CloudCopies.dartEmbed`, `OAI.MetricKMedian.PCP.CloudCopies.decoded`, `OAI.MetricKMedian.PCP.CloudCopies.incidentEmbed`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.S`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.allowed`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.nodeEquiv`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleIndex`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.self_represents`, `OAI.MetricKMedian.PCP.Compiler.Expander.next`, `OAI.MetricKMedian.PCP.Compiler.Expander.rotate`, `OAI.MetricKMedian.PCP.Compiler.PowerProgram.Test`, `OAI.MetricKMedian.PCP.Compiler.PowerProgram.relation`, `OAI.MetricKMedian.PCP.Compiler.ProjectionTable.indexed`, `OAI.MetricKMedian.PCP.Compiler.TableauDirectory.rawAccept`, `OAI.MetricKMedian.PCP.InitialAlphabet.decode`, `OAI.MetricKMedian.PCP.InitialAlphabet.oneHot`, `OAI.MetricKMedian.PCP.PortCSP.CutAccept`, `OAI.MetricKMedian.PCP.PortCSP.Legal`, `OAI.MetricKMedian.PCP.PortCSP.PathAccept`, `OAI.MetricKMedian.PCP.PortCSP.PowerEdge`, `OAI.MetricKMedian.PCP.PortCSP.always`, `OAI.MetricKMedian.PCP.PortCSP.blend`, `OAI.MetricKMedian.PCP.PortCSP.powered`, `OAI.MetricKMedian.PCP.PortCSP.repair`, `OAI.MetricKMedian.PCP.PortCSP.stoppedPath`, `OAI.MetricKMedian.PCP.Tableau.boundedSystem`, `OAI.MetricKMedian.PCP.Tableau.relation`, `OAI.MetricKMedian.PCP.Tableau.system`, `OAI.MetricKMedian.RationalPhysicalKernel.rationalPhysicalDriftCopyOrder`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_CSPMix`, `KMedian_Amplification_PowerCompleteness`, `KMedian_Amplification_PoweringConstruction`, `KMedian_Amplification_PoweringMean`, `KMedian_Amplification_PoweringObjects`, `KMedian_CookLevin_InitialAlphabet`, `KMedian_CookLevin_TableauBoundary`, `KMedian_CookLevin_TableauRelationProgram`, `KMedian_CookLevin_TableauSystem`, `KMedian_Expanders_CloudCopies`, `KMedian_Expanders_ExpanderStep`, `KMedian_Machines_AlphabetIndex`, `KMedian_Machines_CutLaws`, `KMedian_Machines_RawCSP`, `KMedian_PCP_PathTable`, `KMedian_Projection_CSPProjection`, `KMedian_Projection_Tables`, `KMedian_Rounding_RationalPhysicalDrift`.
--
--   **Imports.** It imports the bundles `OAIQ053K015`, `OAIQ053K020`, `OAIQ053K023`, `OAIQ053K024` and `OAIQ053K025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K042` and `OAIQ053K043`; the statements `OAI.MetricKMedian.PCP.PortCSP.powered_amplification_s53` and `OAI.MetricKMedian.PCP.PortCSP.powered_sound_s53`; the proof of `OAI.MetricKMedian.PCP.PortCSP.powered_amplification_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K015
import Definitions.Def_OAIQ053K020
import Definitions.Def_OAIQ053K023
import Definitions.Def_OAIQ053K024
import Definitions.Def_OAIQ053K025

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringObjects
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringObjects

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortCSP
variable {V D A : Type} {G : PortGraph V D}
variable [DecidableEq A] (C : PortCSP G A)

instance badDecidable (x : V → A) : DecidablePred (C.Bad x) := fun _ => inferInstanceAs (Decidable (_ ∉ _))

end PortCSP

end MetricKMedian.PCP

end Inline_PCPPoweringObjects

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_CSPMix
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCSPMix

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortCSP
variable {V D S A : Type} [Fintype A] [DecidableEq A]
variable {G : PortGraph V D} {H : PortGraph V S}
variable (C : PortCSP G A) (K : PortCSP H A)

noncomputable def blend : PortCSP (G.blend H) A where
  allowed p := if p.2.1=0 then C.allowed (p.1,p.2.2.1) else K.allowed (p.1,p.2.2.2)
  symmetric := by
    rintro ⟨v,i,d,s⟩ a b
    change (a,b) ∈ (if (PortGraph.blendRotate G H (v,i,d,s)).2.1=0 then
      C.allowed ((PortGraph.blendRotate G H (v,i,d,s)).1,(PortGraph.blendRotate G H (v,i,d,s)).2.2.1)
      else K.allowed ((PortGraph.blendRotate G H (v,i,d,s)).1,(PortGraph.blendRotate G H (v,i,d,s)).2.2.2)) ↔ _
    by_cases hi : i=0
    · simpa only [PortGraph.blendRotate,hi,ite_true,PortGraph.step,PortGraph.back,Prod.eta] using C.symmetric (v,d) a b
    · simpa only [PortGraph.blendRotate,hi,ite_false,PortGraph.step,PortGraph.back,Prod.eta] using K.symmetric (v,s) a b

omit [Fintype A] [DecidableEq A] in
@[simp] lemma blend_bad (a : V → A) (v : V) (i : Fin 3) (d : D) (s : S) :
    (C.blend K).Bad a (v,i,d,s) ↔ if i=0 then C.Bad a (v,d) else K.Bad a (v,s) := by
  unfold Bad
  rw [PortGraph.blend_step]
  change _ ∉ (if i=0 then _ else _) ↔ _
  by_cases hi : i=0 <;> simp only [hi,ite_true,ite_false]

end PortCSP

namespace PortCSP
variable {V D A : Type} [Fintype A] [DecidableEq A] (G : PortGraph V D)
def always : PortCSP G A where
  allowed _ := univ
  symmetric _ _ _ := by simp

end PortCSP
end MetricKMedian.PCP

end Inline_PCPCSPMix

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringMean
attribute [-simp] _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
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
@[simp] lemma cast_rfl {n : ℕ} (p : G.Walk n) : p.cast rfl = p := rfl
@[simp] lemma cast_vertex {n m : ℕ} (h : n=m) (p : G.Walk n) (i : Fin (m+1)) :
    (p.cast h).vertex i = p.vertex ⟨i.val,by omega⟩ := by subst m; rfl
@[simp] lemma cast_port {n m : ℕ} (h : n=m) (p : G.Walk n) (i : Fin m) :
    (p.cast h).port i = p.port ⟨i.val,by omega⟩ := by subst m; rfl
end PortGraph.Walk

end MetricKMedian.PCP

end Inline_PCPPoweringMean

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringConstruction
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BinaryCSP.mapLabels_allowed _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringConstruction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph.Walk
variable {V D : Type} {G : PortGraph V D}
@[simp] lemma cast_start {n m : ℕ} (h : n=m) (p : G.Walk n) :
    (p.cast h).vertex 0 = p.vertex 0 := by subst m; rfl
@[simp] lemma cast_end {n m : ℕ} (h : n=m) (p : G.Walk n) :
    (p.cast h).vertex (Fin.last m) = p.vertex (Fin.last n) := by subst m; rfl
end PortGraph.Walk

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}
open PortGraph

def CutAccept (i j : ℕ) (p : G.Walk (i+(j+1))) (b c : Advice D A cap) : Prop :=
  let z := Walk.centerEquiv i j p
  (b.get i (Walk.ofWord (G := G) z.1.1 z.1.2).reverse.port,
   c.get j (Walk.ofWord (G := G) (G.step z.1.1 z.2.1) z.2.2).reverse.port) ∈ C.allowed (z.1.1,z.2.1)

def PathAccept (n : ℕ) (p : G.Walk n) (b c : Advice D A cap) : Prop :=
  ∀ i j : Fin (cap+1), ∀ h : n=i.val+(j.val+1), C.CutAccept i.val j.val (p.cast h) b c

noncomputable def stoppedPath (t : ℕ) (z : (Fin cap → Fin (t+1)) × G.Walk cap) :
    G.Walk (Stopped.length t cap z.1) :=
  z.2.segment 0 (Stopped.length t cap z.1) (by have := Stopped.length_le t cap z.1; omega)

abbrev PowerEdge (t cap : ℕ) := (Fin cap → Fin (t+1)) × G.Walk cap

noncomputable def powered (t : ℕ) : BinaryCSP V (PowerEdge (G := G) t cap) (Advice D A cap) := by
  classical
  exact {
    left z := (stoppedPath t z).vertex 0
    right z := (stoppedPath t z).vertex (Fin.last (Stopped.length t cap z.1))
    allowed z := univ.filter (fun bc => C.PathAccept _ (stoppedPath t z) bc.1 bc.2) }

omit [Fintype V] [Nonempty V] [Nonempty D] [DecidableEq A] in
@[simp] lemma powered_allowed (t : ℕ) (z : PowerEdge (G := G) t cap) (b c : Advice D A cap) :
    (b,c) ∈ (C.powered (cap := cap) t).allowed z ↔ C.PathAccept _ (stoppedPath t z) b c := by
  classical
  simp [powered]

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweringConstruction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PowerCompleteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPowerCompleteness
namespace MetricKMedian.PCP
open scoped Classical

namespace PortCSP
variable {V D K : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
variable [Fintype K] [DecidableEq K] {G : PortGraph V D}
variable (C : PortCSP G (BitVector K)) (t cap : ℕ)
variable [Fintype (Advice.BitIndex D K cap)] [DecidableEq (Advice.BitIndex D K cap)]
instance powerEdge_nonempty : Nonempty (PowerEdge (G := G) t cap) :=
  ⟨(fun _ => 0,PortGraph.Walk.ofWord (Classical.arbitrary V) (fun _ => Classical.arbitrary D))⟩
end PortCSP
end MetricKMedian.PCP

end Inline_PCPPowerCompleteness

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudCopies
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
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

omit [Fintype V] [Fintype E] in
lemma owner_surjective : Function.Surjective (owner C) := by
  rintro ⟨v,d,hd⟩
  exact ⟨d,Subtype.ext hd⟩

instance incidentNonempty (v : Active C) : Nonempty (Incident C v) := by
  obtain ⟨d,hd⟩ := owner_surjective C v
  exact ⟨⟨d,hd⟩⟩

omit [Fintype V] in
lemma copy_card_lower (v : Active C) : Fintype.card (Incident C v) ≤ Fintype.card (Copy C v) := by
  have h := ExpanderFamily.padding_lower (Fintype.card (Incident C v)-1)
  have hp := Fintype.card_pos (α := Incident C v)
  simp only [← Nat.card_eq_fintype_card] at hp
  simpa only [Copy,depth,← Nat.card_eq_fintype_card,Nat.sub_add_cancel hp] using h

omit [Fintype V] in
lemma copy_card_upper (v : Active C) : Fintype.card (Copy C v) ≤
    ExpanderFamily.growth*Fintype.card (Incident C v) := by
  have h := ExpanderFamily.padding_upper (Fintype.card (Incident C v)-1)
  have hp := Fintype.card_pos (α := Incident C v)
  simp only [← Nat.card_eq_fintype_card] at hp
  simpa only [Copy,depth,← Nat.card_eq_fintype_card,Nat.sub_add_cancel hp] using h

noncomputable def incidentEmbed (v : Active C) : Incident C v ↪ Copy C v :=
  (Fintype.equivFin _).toEmbedding.trans ((Fin.castLEEmb (copy_card_lower C v)).trans
    (Fintype.equivFin _).symm.toEmbedding)

noncomputable def dartEmbed : Dart (E := E) ↪ Node C where
  toFun d := ⟨owner C d, incidentEmbed C (owner C d) ⟨d,rfl⟩⟩
  inj' := by
    intro d e h
    have ho : owner C d=owner C e := congrArg Sigma.fst h
    have hh : (⟨owner C d,⟨d,rfl⟩⟩ : (v : Active C) × Incident C v) =
        ⟨owner C e,⟨e,rfl⟩⟩ := by
      apply (Function.Embedding.sigmaMap (Function.Embedding.refl _) (incidentEmbed C)).injective
      exact h
    exact congrArg (fun p : (v : Active C) × Incident C v => p.2.val) hh

omit [Fintype V] in
lemma node_card_upper : Fintype.card (Node C) ≤ 2*ExpanderFamily.growth*Fintype.card E := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ v : Active C, ExpanderFamily.growth*Fintype.card (Incident C v) :=
      sum_le_sum (fun v _ => copy_card_upper C v)
    _ = ExpanderFamily.growth*Fintype.card ((v : Active C) × Incident C v) := by
      rw [← mul_sum,Fintype.card_sigma]
    _ = _ := by
      rw [Fintype.card_congr (Equiv.sigmaFiberEquiv (owner C)),Fintype.card_prod,Fintype.card_bool]
      ring

noncomputable instance activeNonempty [Nonempty E] : Nonempty (Active C) :=
  ⟨owner C (Classical.arbitrary E,false)⟩

noncomputable instance nodeNonempty [Nonempty E] : Nonempty (Node C) := by
  let v := Classical.arbitrary (Active C)
  exact ⟨⟨v,Classical.arbitrary (Copy C v)⟩⟩

variable [Fintype A] [Inhabited A] [DecidableEq A]
noncomputable def decoded (a : Node C → A) (v : V) : A :=
  if h : v ∈ Set.range (endpoint C) then
    PortGraph.majorityLabel (fun w : Copy C ⟨v,h⟩ => a ⟨⟨v,h⟩,w⟩) else default

end CloudCopies
end MetricKMedian.PCP

end Inline_PCPCloudCopies

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_InitialAlphabet
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInitialAlphabet

namespace MetricKMedian.PCP
open Function Finset
open scoped Classical

namespace InitialAlphabet
variable (A : Type) [Fintype A] [DecidableEq A] [Nonempty A]
def oneHot (a : A) : BitVector A := fun b => if b=a then 1 else 0
noncomputable def decode : BitVector A → A := invFun (oneHot A)
variable {V E : Type} [Fintype V] [Fintype E]
variable (C : BinaryCSP V E A)
variable [Nonempty E]
noncomputable instance edgeNonempty : Nonempty (AlphabetReduction.Test (E := E) (K := A) × Fin 4) :=
  inferInstance
end InitialAlphabet
end MetricKMedian.PCP

end Inline_PCPInitialAlphabet

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauSystem
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauSystem

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)

def relation (T L : ℕ) (test : Clause (K := K) T L) (z : Query M → Value M) : Prop :=
  match test with
  | .shape _ k _ => (z (q0 M)).2.2 k=none → (z (q1 M)).2.2 k=none
  | .end _ k => (z (q0 M)).2.2 k=none
  | .prefix _ => PrefixRelation M (z (q0 M)).1
      (fun k i => (z (qtop M k i)).2.2 k) (z (q1 M)).2.1
  | .control _ => (z (q0 M)).1=(z (q1 M)).2.1.1
  | .update _ k i => (z (q1 M)).2.2 k=cellTable M k (category M i.val) ((z (q0 M)).2.1.2 k)
      (fun h => (z (qwin M h)).2.2 k)
noncomputable def system (T L : ℕ) : FiniteCSP (Var (K := K) T L) (Clause (K := K) T L) (Query M) (Value M) where
  query := query M T L
  accept t := univ.filter (relation M T L t)
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauSystem

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauBoundary
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauBoundary

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function Finset
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)]
variable (M : Λ → Stmt Γ Λ σ)
noncomputable def boundedSystem (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (T L : ℕ) :
    FiniteCSP (Var (K := K) T L) (Clause (K := K) T L ⊕ BoundaryClause (K := K) L) (Query M) (Value M) where
  query := Sum.elim (query M T L) (boundaryQuery M T L)
  accept := Sum.elim ((system M T L).accept) (fun b => univ.filter (boundaryRelation M B L b))
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauBoundary

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential FixedBatch Analytic CopyState
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
local instance rationalPhysicalDriftCopyOrder : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawCSP
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRawCSP
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace CSPTable
variable {A : Type} [Fintype A] [DecidableEq A]
variable {V E : Type} [Fintype V] [Fintype E]
omit [Fintype A] [DecidableEq A] [Fintype V] in
lemma Represents.wellFormed [Nonempty E] {t : CSPTable A} {C : BinaryCSP V E A}
    (r : t.Represents C) : t.WellFormed := by
  constructor
  · have h := Fintype.card_pos (α := E)
    have he := Fintype.card_congr r.edge
    simp only [Fintype.card_fin] at he
    omega
  · intro e he
    obtain ⟨i,hi,hi'⟩ := List.mem_iff_getElem.mp he
    obtain ⟨j,hj⟩ := r.edge.surjective ⟨i,hi⟩
    have hr := r.row j
    simp only [hj] at hr
    rw [← hi',hr]
    exact ⟨(r.vertex (C.left j)).isLt,(r.vertex (C.right j)).isLt⟩
noncomputable def self_represents (t : CSPTable A) (h : t.WellFormed) : t.Represents (t.csp h) :=
  ⟨Equiv.refl _,Equiv.refl _,fun _ => rfl⟩
end CSPTable
end MetricKMedian.PCP.Compiler

end Inline_PCPRawCSP

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_TableauRelationProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableauRelationProgram
namespace MetricKMedian.PCP.Compiler.TableauDirectory
open Binary Binary.Automatic Tableau Turing.TM2
open scoped Classical

variable {K : Type} {Γ : K→Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀k,Fintype (Γ k)]
variable (M : Λ→Stmt Γ Λ σ) (k0 : K)
noncomputable def rawAccept (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (test : TC (K := K)) : RelationSet M :=
  let k := test.2.2.1
  let i := test.2.2.2
  if test.1=0 then Finset.univ.filter (fun z => (z (q0 M)).2.2 k=none → (z (q1 M)).2.2 k=none)
  else if test.1=1 then Finset.univ.filter (fun z => (z (q0 M)).2.2 k=none)
  else if test.1=2 then Finset.univ.filter (fun z => PrefixRelation M (z (q0 M)).1 (fun k i => (z (qtop M k i)).2.2 k) (z (q1 M)).2.1)
  else if test.1=3 then Finset.univ.filter (fun z => (z (q0 M)).1=(z (q1 M)).2.1.1)
  else if test.1=4 then Finset.univ.filter (fun z => (z (q1 M)).2.2 k=cellTable M k (category M i) ((z (q0 M)).2.1.2 k) (fun h => (z (qwin M h)).2.2 k))
  else if test.1=5 then firstControlSet M B
  else if test.1=6 then lastControlSet M B
  else if test.1=7 then firstCellSet M B k i
  else lastCellSet M B k i
lemma rawAccept_boundary (L : ℕ) (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (b : BoundaryClause (K := K) L) :
    rawAccept M B (boundaryCode k0 b)=Finset.univ.filter (boundaryRelation M B L b) := by
  rcases b with ⟨side,b⟩
  cases side <;> rcases b with b|⟨k,i⟩ <;> ext z
  all_goals simp [rawAccept,boundaryCode,boundaryRelation,firstControlSet,lastControlSet,firstCellSet,lastCellSet]
  all_goals rfl
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauRelationProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderStep
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderStep

namespace MetricKMedian.PCP.Compiler.Expander
open Binary Binary.Automatic ExpanderFamily RotationTable
open scoped Classical

noncomputable def rotate (R : Raw) (v : ℕ) (b : Branch) (d : Degree) : ℕ × Degree :=
  let h1 := base.rotate (b,d.1)
  let q1 := lookup R v h1.1.1
  let q2 := lookup R q1.1 h1.1.2
  let h2 := base.rotate ((q2.2,q1.2),d.2)
  (nodeIndex q2.1 h2.1,(h2.2,h1.2))
noncomputable def next (R : Raw) : Raw :=
  (List.range R.length).flatMap (fun v => (ports (D := Branch)).map (fun b =>
    (ports (D := Degree)).map (rotate R v b)))
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderStep

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_AlphabetIndex
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAlphabetIndex
namespace MetricKMedian.PCP.Compiler.AlphabetProgram
open AlphabetReduction Binary Binary.Automatic
open scoped Classical

variable (K : Type) [Fintype K] [DecidableEq K]
noncomputable def S : ℕ := Fintype.card (EdgeSample K)
noncomputable def sampleIndex (b : EdgeSample K) : ℕ := (Fintype.equivFin _ b).val
noncomputable def nodeEquiv (nv ne : ℕ) : PaddedNode (Fin nv) (Fin ne) K ≃
    Fin ((nv*B K+ne*I K)+ne*S K) :=
  (Equiv.sumCongr
    ((Equiv.sumCongr
      ((Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin _)).trans finProdFinEquiv)
      ((Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin _)).trans finProdFinEquiv)).trans finSumFinEquiv)
    ((Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin _)).trans finProdFinEquiv)).trans finSumFinEquiv
noncomputable def allowed (R : Relations K) (z : Tag K) : Finset (Label × Label) :=
  Finset.univ.filter (fun p => (LocalRelation.query (R : LocalRelation.Relation K) z.1.1
    (z.1.2 R z.1.1)).accept p.1=true ∧ p.1 z.2=p.2 0)
end MetricKMedian.PCP.Compiler.AlphabetProgram

end Inline_PCPAlphabetIndex

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_CutLaws
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCutLaws
namespace MetricKMedian.PCP.PortGraph.Walk
variable {V D : Type} {G : PortGraph V D}
lemma center_left_walk (i j : ℕ) (p : G.Walk (i+(j+1))) :
    ofWord (G := G) (centerEquiv i j p).1.1 (centerEquiv i j p).1.2=
      (p.segment 0 i (by omega)).reverse := by
  change wordEquiv.symm (wordEquiv ((p.segment 0 i (by omega)).reverse))=_
  exact wordEquiv.symm_apply_apply _
lemma center_right_word (i j : ℕ) (p : G.Walk (i+(j+1))) :
    (centerEquiv i j p).2.2=(p.segment (i+1) j (by omega)).port := by
  funext k
  simp only [centerEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,splitEquiv,Fin.consEquiv,
    segment,Equiv.coe_fn_mk]
  change p.port ⟨i+(k.val+1),_⟩=p.port ⟨i+1+k.val,_⟩
  congr 1
  apply Fin.ext
  change i+(k.val+1)=i+1+k.val
  omega
lemma center_right_walk (i j : ℕ) (p : G.Walk (i+(j+1))) :
    ofWord (G := G) (G.step (centerEquiv i j p).1.1 (centerEquiv i j p).2.1)
      (centerEquiv i j p).2.2=p.segment (i+1) j (by omega) := by
  rw [center_vertex,center_port,center_right_word]
  have hc : G.step (p.vertex ⟨i,by omega⟩) (p.port ⟨i,by omega⟩)=p.vertex ⟨i+1,by omega⟩ := p.chain ⟨i,by omega⟩
  rw [hc]
  change wordEquiv.symm (wordEquiv (p.segment (i+1) j (by omega)))=_
  exact wordEquiv.symm_apply_apply _
end MetricKMedian.PCP.PortGraph.Walk
namespace MetricKMedian.PCP.PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A] {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}
open PortGraph

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] [DecidableEq A] in
lemma cut_literal (i j : ℕ) (p : G.Walk (i+(j+1))) (b c : Advice D A cap) :
    C.CutAccept i j p b c ↔
    (b.get i (p.segment 0 i (by omega)).port,
     c.get j (p.segment (i+1) j (by omega)).reverse.port) ∈
      C.allowed (p.vertex ⟨i,by omega⟩,p.port ⟨i,by omega⟩) := by
  unfold CutAccept
  dsimp only
  rw [Walk.center_left_walk,Walk.reverse_reverse,Walk.center_right_walk,
    Walk.center_vertex,Walk.center_port]
end MetricKMedian.PCP.PortCSP

end Inline_PCPCutLaws

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_PathTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPathTable
namespace MetricKMedian.PCP.Compiler.PowerProgram
open scoped Classical

variable {D A : Type} [Fintype D] [Fintype A] [Inhabited A] [DecidableEq A]
def Test (cap : ℕ) (n : Fin (cap+1)) (w back : Fin cap → D)
    (rels : Fin cap → Finset (A × A)) (b c : Advice D A cap) : Prop :=
  ∀ (i j : Fin (cap+1)) (h : n.val=i.val+(j.val+1)),
    (b.get i.val (fun k => w ⟨k.val,by omega⟩),
     c.get j.val (fun k => back ⟨i.val+1+k.rev.val,by have := k.rev.isLt; omega⟩)) ∈
       rels ⟨i.val,by omega⟩
noncomputable def relation (cap : ℕ) (n : Fin (cap+1)) (w back : Fin cap → D)
    (rels : Fin cap → Finset (A × A)) : Finset (Advice D A cap × Advice D A cap) :=
  Finset.univ.filter (fun bc => Test cap n w back rels bc.1 bc.2)
variable {V : Type} [Fintype V] [Nonempty V] [Nonempty D]
  {G : PortGraph V D} (C : PortCSP G A)
omit [Fintype D] [Fintype A] [DecidableEq A] [Fintype V] [Nonempty V] [Nonempty D] in
lemma cut_prefix (cap i j : ℕ) (h : i+(j+1) ≤ cap) (p : G.Walk cap) (b c : Advice D A cap) :
    C.CutAccept i j (p.segment 0 (i+(j+1)) (by omega)) b c ↔
    (b.get i (fun k => p.port ⟨k.val,by omega⟩),
     c.get j (fun k => G.back (p.vertex ⟨i+1+k.rev.val,by have := k.rev.isLt; omega⟩)
       (p.port ⟨i+1+k.rev.val,by have := k.rev.isLt; omega⟩))) ∈
      C.allowed (p.vertex ⟨i,by omega⟩,p.port ⟨i,by omega⟩) := by
  rw [C.cut_literal]
  simp only [PortGraph.Walk.segment,PortGraph.Walk.reverse,Nat.zero_add,Fin.val_castSucc]
omit [Fintype D] [Fintype A] [DecidableEq A] [Fintype V] [Nonempty V] [Nonempty D] in
lemma path_literal (cap : ℕ) (p : G.Walk cap) (n : Fin (cap+1)) (b c : Advice D A cap) :
    C.PathAccept n.val (p.segment 0 n.val (by omega)) b c ↔
      Test cap n p.port (fun k => G.back (p.vertex k.castSucc) (p.port k))
        (fun k => C.allowed (p.vertex k.castSucc,p.port k)) b c := by
  unfold PortCSP.PathAccept Test
  apply forall_congr'
  intro i
  apply forall_congr'
  intro j
  apply forall_congr'
  intro h
  have he : (p.segment 0 n.val (by omega)).cast h=p.segment 0 (i.val+(j.val+1)) (by omega) := by
    have cast_segment (n m : ℕ) (hn : 0+n ≤ cap) (h : n=m) :
        (p.segment 0 n hn).cast h=p.segment 0 m (by omega) := by
      subst m
      rfl
    exact cast_segment _ _ _ h
  rw [he]
  exact cut_prefix C cap i.val j.val (by omega) p b c
omit [DecidableEq A] [Fintype V] [Nonempty V] [Nonempty D] in
lemma relation_correct (cap : ℕ) (p : G.Walk cap) (n : Fin (cap+1)) :
    relation cap n p.port (fun k => G.back (p.vertex k.castSucc) (p.port k))
      (fun k => C.allowed (p.vertex k.castSucc,p.port k)) =
    Finset.univ.filter (fun bc : Advice D A cap × Advice D A cap =>
      C.PathAccept n.val (p.segment 0 n.val (by omega)) bc.1 bc.2) := by
  apply Finset.ext
  intro bc
  simp only [relation,Finset.mem_filter,Finset.mem_univ,true_and]
  exact (path_literal C cap p n bc.1 bc.2).symm
end MetricKMedian.PCP.Compiler.PowerProgram

end Inline_PCPPathTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_CSPProjection
attribute [-instance] _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCSPProjection

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortCSP
variable {V D A : Type} {G : PortGraph V D} [DecidableEq A]
variable (C : PortCSP G A)
def Legal (p : V × D) (a : A × A) : Prop :=
  a ∈ C.allowed p ∧ ((G.rotate p).1=p.1 → a.1=a.2)
variable (chosen : V × D → A × A) (hchosen : ∀ p, C.Legal p (chosen p))
noncomputable def repair (p : V × D) (a : A × A) : A × A := if C.Legal p a then a else chosen p
end PortCSP
end MetricKMedian.PCP

end Inline_PCPCSPProjection

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Tables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionTables
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace ProjectionTable
variable {U V D S A B : Type} [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
variable (G : BiProjection U V D S A B) {nu : ℕ} (ue : U≃Fin nu) (vo : Ordered V) (so : Ordered S)
variable (ao : Ordered A) (bo : Ordered B)
noncomputable def indexed := G.reindex ue vo.equiv (Fintype.equivFin D) so.equiv ao.equiv bo.equiv
end ProjectionTable
end MetricKMedian.PCP.Compiler

end Inline_PCPProjectionTables

end OAI
end


