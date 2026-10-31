-- Prove2me | Definitions.Def_OAIQ107D000
-- name    : OAIQ107D000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:37:52.368453+00:00
-- url     : https://prove2.me/theorems/aec26df6-6f79-4c9c-a7bc-6f2331888378
-- title:
--   Definitions bundle OAIQ107D000 of the split of OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 296 declarations of OpenAI's Lean: 213 definitions, 16 inductive types or structures, 11 instances and 56 theorems. The definitions and types are `OAI.CycleClique.AmountProfile`, `OAI.CycleClique.BallCertificate`, `OAI.CycleClique.BallCertificate.Valid`, `OAI.CycleClique.BallCertificate.radius`, `OAI.CycleClique.BallCertificate.size`, `OAI.CycleClique.BallCertificate.weight`, `OAI.CycleClique.BreadthFirstParent`, `OAI.CycleClique.ChainAmounts`, `OAI.CycleClique.ClosedChain`, `OAI.CycleClique.Excluded`, `OAI.CycleClique.FiniteCertificate`, `OAI.CycleClique.FiniteCertificate.Valid`, `OAI.CycleClique.FiniteHyp`, `OAI.CycleClique.ForbiddenMatrix`, `OAI.CycleClique.FourHyp`, `OAI.CycleClique.FourHyp.overlapClasses`, `OAI.CycleClique.Frame`, `OAI.CycleClique.Frame.Q`, `OAI.CycleClique.Frame.U`, `OAI.CycleClique.Frame.reindex`, `OAI.CycleClique.Frame.triangle`, `OAI.CycleClique.Improvement`, `OAI.CycleClique.LabelCycleValid`, `OAI.CycleClique.LabelState`, `OAI.CycleClique.LabelState.extendedFunction`, `OAI.CycleClique.LabelState.imageLabels`, `OAI.CycleClique.LabelState.system`, `OAI.CycleClique.LabelState.vertices`, `OAI.CycleClique.LabelValid`, `OAI.CycleClique.LargeSystem`, `OAI.CycleClique.LooseTail`, `OAI.CycleClique.MarkedCut`, `OAI.CycleClique.MinimalDensity`, `OAI.CycleClique.OriginalSystem`, `OAI.CycleClique.OutsidePath`, `OAI.CycleClique.PackingOption`, `OAI.CycleClique.PackingOption.Compatible`, `OAI.CycleClique.PackingOption.Valid`, `OAI.CycleClique.PackingOption.base`, `OAI.CycleClique.PackingOption.radiusCode` and 189 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ramsey_CycleClique_BallPacking`, `Ramsey_CycleClique_Basic`, `Ramsey_CycleClique_BreadthFirst`, `Ramsey_CycleClique_CertificateModel`, `Ramsey_CycleClique_Certificates001`, `Ramsey_CycleClique_Certificates004`, `Ramsey_CycleClique_Certificates032`, `Ramsey_CycleClique_ChainProfiles`, `Ramsey_CycleClique_ChainRearrangement`, `Ramsey_CycleClique_CycleShortening`, `Ramsey_CycleClique_Density`, `Ramsey_CycleClique_ExteriorFrames`, `Ramsey_CycleClique_ExteriorPaths`, `Ramsey_CycleClique_FiniteGraphs`, `Ramsey_CycleClique_FourCycles`, `Ramsey_CycleClique_FrameProperties`, `Ramsey_CycleClique_Independence`, `Ramsey_CycleClique_LargeSystems`, `Ramsey_CycleClique_MarkedChains`, `Ramsey_CycleClique_OptimalSystems`, `Ramsey_CycleClique_PathSystems`, `Ramsey_CycleClique_PatternReduction`, `Ramsey_CycleClique_SystemInsertion`, `Ramsey_CycleClique_ThreeCycles`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ107D008`, `OAIQ107D009`, `OAIQ107D010`, `OAIQ107D011`, `OAIQ107D012`, `OAIQ107D013`, `OAIQ107D014`, `OAIQ107D015`, `OAIQ107D016`, `OAIQ107D017`, `OAIQ107D018`, `OAIQ107D019`, `OAIQ107D020`, `OAIQ107D021`, `OAIQ107D022`, `OAIQ107D023`, `OAIQ107D024`, `OAIQ107D025`, `OAIQ107D026`, `OAIQ107D027`, `OAIQ107D028`, `OAIQ107D029`, `OAIQ107D030`, `OAIQ107D031`, `OAIQ107D032`, `OAIQ107D033`, `OAIQ107D034`, `OAIQ107D035`, `OAIQ107D036`, `OAIQ107D037`, `OAIQ107D038`, `OAIQ107D039`, `OAIQ107D040`, `OAIQ107D041`, `OAIQ107D042`, `OAIQ107D043`, `OAIQ107D044`, `OAIQ107D045`, `OAIQ107D046`, `OAIQ107D047`, `OAIQ107D048`, `OAIQ107D049`, `OAIQ107D050`, `OAIQ107D051`, `OAIQ107D052`, `OAIQ107D053`, `OAIQ107D054`, `OAIQ107D055`, `OAIQ107D056`, `OAIQ107D057`, `OAIQ107D058`, `OAIQ107D059`, `OAIQ107D060`, `OAIQ107D061`, `OAIQ107D062`, `OAIQ107D063`, `OAIQ107D064`, `OAIQ107D065`, `OAIQ107D066`, `OAIQ107D067`, `OAIQ107D068`, `OAIQ107D069`, `OAIQ107D070`, `OAIQ107D071`, `OAIQ107D072`, `OAIQ107D073`, `OAIQ107D074`, `OAIQ107D075`, `OAIQ107D076`, `OAIQ107D077`, `OAIQ107D078`, `OAIQ107D079`, `OAIQ107D080`, `OAIQ107D081`, `OAIQ107D082`, `OAIQ107D083`, `OAIQ107D084`, `OAIQ107D085`, `OAIQ107D086`, `OAIQ107D087`, `OAIQ107D088`, `OAIQ107D089`, `OAIQ107D090`, `OAIQ107D091`, `OAIQ107D092`, `OAIQ107D093`, `OAIQ107D094`, `OAIQ107D095`, `OAIQ107D096`, `OAIQ107D097`, `OAIQ107D098`, `OAIQ107D099`, `OAIQ107D100`, `OAIQ107D101`, `OAIQ107D102`, `OAIQ107D103`, `OAIQ107D104`, `OAIQ107D105`, `OAIQ107D106`, `OAIQ107D107`, `OAIQ107D108`, `OAIQ107D109`, `OAIQ107D110`, `OAIQ107D111`, `OAIQ107D112`, `OAIQ107D113`, `OAIQ107D114`, `OAIQ107D115`, `OAIQ107D116`, `OAIQ107D117`, `OAIQ107D118`, `OAIQ107D119`, `OAIQ107D120`, `OAIQ107D121`, `OAIQ107D122`, `OAIQ107D123`, `OAIQ107D124` and `OAIQ107D125`; the statements `OAI.CycleClique.finite_patterns_10_5`, `OAI.CycleClique.finite_patterns_11_5`, `OAI.CycleClique.finite_patterns_11_6`, `OAI.CycleClique.finite_patterns_12_6`, `OAI.CycleClique.finite_patterns_13_6`, `OAI.CycleClique.finite_patterns_13_7`, `OAI.CycleClique.finite_patterns_14_7`, `OAI.CycleClique.finite_patterns_14_8`, `OAI.CycleClique.finite_patterns_15_7`, `OAI.CycleClique.finite_patterns_15_8`, `OAI.CycleClique.finite_patterns_16_8`, `OAI.CycleClique.finite_patterns_17_8`, `OAI.CycleClique.finite_patterns_9_4`, `OAI.CycleClique.finite_range_verified`, `OAI.CycleClique.patterns_13_6_0_verified`, `OAI.CycleClique.patterns_15_7_0_verified`, `OAI.CycleClique.patterns_15_7_13_verified`, `OAI.CycleClique.patterns_15_7_1_verified`, `OAI.CycleClique.patterns_15_7_4_verified`, `OAI.CycleClique.patterns_16_8_7_verified`, `OAI.CycleClique.patterns_16_8_8_verified`, `OAI.CycleClique.patterns_17_8_0_verified`, `OAI.CycleClique.patterns_17_8_11_verified`, `OAI.CycleClique.patterns_17_8_12_verified`, `OAI.CycleClique.patterns_17_8_15_verified`, `OAI.CycleClique.patterns_17_8_16_verified`, `OAI.CycleClique.patterns_17_8_17_verified`, `OAI.CycleClique.patterns_17_8_1_verified`, `OAI.CycleClique.patterns_17_8_23_verified`, `OAI.CycleClique.patterns_17_8_24_verified`, `OAI.CycleClique.patterns_17_8_25_verified`, `OAI.CycleClique.patterns_17_8_26_verified`, `OAI.CycleClique.patterns_17_8_32_verified`, `OAI.CycleClique.patterns_17_8_35_verified`, `OAI.CycleClique.patterns_17_8_36_verified`, `OAI.CycleClique.patterns_17_8_39_verified`, `OAI.CycleClique.patterns_17_8_40_verified`, `OAI.CycleClique.patterns_17_8_41_verified`, `OAI.CycleClique.patterns_17_8_42_verified`, `OAI.CycleClique.patterns_17_8_51_verified`, `OAI.CycleClique.patterns_17_8_52_verified`, `OAI.CycleClique.patterns_17_8_53_verified` and `OAI.CycleClique.patterns_17_8_6_verified`.
-- source:
--   OpenAI, Cycle-clique Ramsey numbers, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 189; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ107_CC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph


def closedNeighborhood {V : Type*} (G : SimpleGraph V) (I : Set V) : Set V :=
  I ∪ {v | ∃ u ∈ I, G.Adj u v}


end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Independence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def independence {V : Type*} (G : SimpleGraph V) (S : Set V) : ℕ :=
  (G.induce S).indepNum

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def MinimalDensity {V : Type*} (G : SimpleGraph V) (s ε : ℕ) : Prop :=
  (s * G.indepNum + ε ≤ Nat.card V) ∧
  ∀ T : Set V, T.Nonempty → T.ncard < Nat.card V →
    T.ncard < s * independence G T + ε


end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_BreadthFirst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph



structure BreadthFirstParent {V : Type*} (G : SimpleGraph V) (r : V) where
  parent : V → V
  step : ∀ v, G.Reachable r v → v ≠ r →
    G.Adj v (parent v) ∧ G.Reachable r (parent v) ∧
      G.dist r (parent v) + 1 = G.dist r v

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CycleShortening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph


def bypassIndex {n : ℕ} (hn : 3 ≤ n) (i : Fin (n - 1)) : Fin n :=
  ⟨if i.val = 0 then 0 else i.val + 1, by split_ifs <;> omega⟩

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_ExteriorPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph


def OutsidePath {V : Type*} (G : SimpleGraph V) (X : Set V) (x y : V) (d : ℕ) : Prop :=
  x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ ∃ p : G.Walk x y,
    p.IsPath ∧ p.length = d + 1 ∧ ∀ v ∈ p.support, v ∈ X → v = x ∨ v = y

 

def outsideBall {V : Type*} (G : SimpleGraph V) (X : Set V) (x : V) : ℕ → Set V
  | 0 => G.neighborSet x \ X
  | r + 1 => closedNeighborhood G (outsideBall G X x r) \ X

attribute [local instance] Classical.propDecidable

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_PathSystems
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

structure PathSystem {V : Type*} (G : SimpleGraph V) (Q : Set V) where
  chains : List (List V)
  nonempty : ∀ c ∈ chains, c ≠ []
  nodup : chains.flatten.Nodup
  edges : ∀ c ∈ chains, c.IsChain G.Adj
  positive : ∀ c ∈ chains, c.IsChain (fun u v => u ∉ Q ∨ v ∉ Q)
  ends : ∀ c ∈ chains, (∀ x ∈ c.head?, x ∈ Q) ∧ (∀ x ∈ c.getLast?, x ∈ Q)
  cover : ∀ x ∈ Q, x ∈ chains.flatten



theorem flatten_singletons {V : Type*} (l : List V) :
    (l.map (fun v => [v])).flatten = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.flatten_cons, ih, List.singleton_append]

noncomputable def PathSystem.empty {V : Type*} [Fintype V]
    (G : SimpleGraph V) (Q : Set V) : PathSystem G Q := by
  classical
  refine ⟨Q.toFinset.toList.map (fun v => [v]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    simp
  · rw [flatten_singletons]
    exact Q.toFinset.nodup_toList
  · intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    exact .singleton _
  · intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    exact .singleton _
  · intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    have hvQ : v ∈ Q := by simpa using hv
    simpa using And.intro hvQ hvQ
  · intro x hx
    simpa using hx

noncomputable def PathSystem.amount {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) : ℕ :=
  P.chains.flatten.length - Q.ncard

noncomputable def PathSystem.edgeCount {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) : ℕ :=
  Q.ncard - P.chains.length

noncomputable def PathSystem.singletons {V : Type*}
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) : List (List V) := by
  classical
  exact P.chains.filter (fun c => c.length = 1)

noncomputable def PathSystem.usedChains {V : Type*}
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) : List (List V) := by
  classical
  exact P.chains.filter (fun c => c.length ≠ 1)

noncomputable def PathSystem.incident {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) : ℕ :=
  Q.ncard - P.singletons.length

@[simp] theorem PathSystem.empty_amount {V : Type*} [Fintype V]
    (G : SimpleGraph V) (Q : Set V) : (PathSystem.empty G Q).amount = 0 := by
  classical
  simp [PathSystem.amount, PathSystem.empty, flatten_singletons, Set.ncard_eq_toFinset_card']

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_OptimalSystems
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

def PathSystem.Optimal {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    (k : ℕ) (P : PathSystem G Q) : Prop :=
  P.amount < k + 1 - Q.ncard ∧
  (∀ R : PathSystem G Q, R.amount < k + 1 - Q.ncard → R.amount ≤ P.amount) ∧
  (∀ R : PathSystem G Q, R.amount = P.amount → P.edgeCount ≤ R.edgeCount)

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_MarkedChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

noncomputable def markedReps {V : Type*} (Q : Set V) (b : Bool) : List V → List V
  | [] => []
  | a :: l => (if b then [a] else []) ++ markedReps Q (decide (a ∈ Q)) l



def MarkedCut {V : Type*} (Q : Set V) (b : Bool) (A : List V) : Prop :=
  (A = [] ∧ b = true) ∨ (A ≠ [] ∧ ∀ a ∈ A.getLast?, a ∈ Q)

noncomputable def PathSystem.reps {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : List V := (P.chains.map (markedReps Q true)).flatten

structure ClosedChain {V : Type*} (G : SimpleGraph V) (Q : Set V) (c : List V) : Prop where
  nonempty : c ≠ []
  edges : c.IsChain G.Adj
  positive : c.IsChain (fun a b => a ∉ Q ∨ b ∉ Q)
  ends : (∀ a ∈ c.head?, a ∈ Q) ∧ (∀ a ∈ c.getLast?, a ∈ Q)

structure LooseTail {V : Type*} (G : SimpleGraph V) (Q : Set V) (c : List V) : Prop where
  edges : c.IsChain G.Adj
  positive : c.IsChain (fun a b => a ∉ Q ∨ b ∉ Q)
  end_mem : ∀ a ∈ c.getLast?, a ∈ Q

abbrev PathSystem.vertices {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : Set V := {v | v ∈ P.chains.flatten}

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_ChainProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

inductive ChainAmounts {V : Type*} (Q : Set V) : List V → List ℕ → Prop
  | singleton (x : V) (hx : x ∈ Q) : ChainAmounts Q [x] []
  | step (x y : V) (I B : List V) (A : List ℕ) (hx : x ∈ Q)
      (hI : I ≠ []) (hout : ∀ z ∈ I, z ∉ Q)
      (tail : ChainAmounts Q (y :: B) A) :
      ChainAmounts Q (x :: (I ++ y :: B)) (I.length :: A)

theorem ChainAmounts.count {V : Type*} {Q : Set V} {c : List V} {A : List ℕ}
    (h : ChainAmounts Q c A) :
    c.countP (fun v => decide (v ∈ Q)) = A.length + 1 ∧
    c.length = A.sum + A.length + 1 ∧ ∀ a ∈ A, 1 ≤ a := by
  classical
  induction h with
  | singleton x hx => simp [hx]
  | step x y I B A hx hI hout htail ih =>
    have hcI : I.countP (fun v => decide (v ∈ Q)) = 0 := by
      apply List.countP_eq_zero.mpr
      simpa using hout
    have hi : 1 ≤ I.length := List.length_pos_iff.mpr hI
    rcases ih with ⟨hc, hl, hp⟩
    constructor
    · simp only [List.countP_cons, List.countP_append, hcI, hx, decide_true,
        ite_true, if_true, List.length_cons] at hc ⊢
      omega
    constructor
    · simp only [List.length_cons, List.length_append, List.sum_cons] at hl ⊢
      omega
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hi
      · exact hp a ha


def AmountProfile {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (A : List ℕ) : Prop :=
  ∃ blocks : List (List ℕ), List.Forall₂ (ChainAmounts Q) P.chains blocks ∧ blocks.flatten.Perm A

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_SystemInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

abbrev PathSystem.representatives {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : Set V := {v | v ∈ P.reps}

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_ChainRearrangement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

noncomputable def flipChain {V : Type*} (b : Bool) (c : List V) : List V :=
  if b then c.reverse else c

@[simp] theorem flipChain_length {V : Type*} (b : Bool) (c : List V) :
    (flipChain b c).length = c.length := by cases b <;> simp [flipChain]

theorem flipChain_perm {V : Type*} (b : Bool) (c : List V) :
    (flipChain b c).Perm c := by cases b <;> simp [flipChain]

theorem flipChains_flatten_perm {V : Type*} (f : List V → Bool) (C : List (List V)) :
    (C.map (fun c => flipChain (f c) c)).flatten.Perm C.flatten := by
  induction C with
  | nil => simp
  | cons c C ih => exact (flipChain_perm (f c) c).append ih

noncomputable def PathSystem.orient {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (f : List V → Bool) : PathSystem G Q := by
  classical
  let C := P.chains.map (fun c => flipChain (f c) c)
  have hp : C.flatten.Perm P.chains.flatten := flipChains_flatten_perm f P.chains
  refine {
    chains := C
    nonempty := ?_
    nodup := hp.nodup_iff.mpr P.nodup
    edges := ?_
    positive := ?_
    ends := ?_
    cover := fun v hv => hp.mem_iff.mpr (P.cover v hv) }
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have hn := P.nonempty d hd
    cases hf : f d <;> simpa [flipChain, hf] using hn
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have he := P.edges d hd
    cases hf : f d
    · simpa [flipChain, hf] using he
    · simpa [flipChain, hf] using List.isChain_reverse.mpr (he.imp (fun _ _ h => h.symm))
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have he := P.positive d hd
    cases hf : f d
    · simpa [flipChain, hf] using he
    · simpa [flipChain, hf] using List.isChain_reverse.mpr (he.imp (fun _ _ h => h.symm))
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have he := P.ends d hd
    cases hf : f d
    · simpa [flipChain, hf] using he
    · simpa [flipChain, hf] using And.intro he.2 he.1

@[simp] theorem PathSystem.orient_chains {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (f : List V → Bool) :
    (P.orient f).chains = P.chains.map (fun c => flipChain (f c) c) := rfl

@[simp] theorem PathSystem.orient_edgeCount {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (f : List V → Bool) :
    (P.orient f).edgeCount = P.edgeCount := by simp [PathSystem.edgeCount]

@[simp] theorem PathSystem.orient_singletons_length {V : Type*}
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (f : List V → Bool) :
    (P.orient f).singletons.length = P.singletons.length := by
  classical
  simp only [PathSystem.singletons, orient_chains, List.filter_map, List.length_map]
  congr 2
  funext c
  simp only [Function.comp_apply, flipChain_length]

@[simp] theorem PathSystem.orient_incident {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (f : List V → Bool) :
    (P.orient f).incident = P.incident := by simp [PathSystem.incident]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_LargeSystems
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable



structure LargeSystem {V : Type*} [Fintype V] (G : SimpleGraph V) (Q : Set V)
    (k : ℕ) (P : PathSystem G Q) : Prop where
  optimal : P.Optimal k
  clique : G.IsClique Q
  no_cycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G
  nine : 9 ≤ Q.ncard
  le_k : Q.ncard ≤ k
  k_le : k ≤ 2 * Q.ncard + 1
  maximal : G.cliqueNum ≤ Q.ncard
  independent : G.indepNum ≤ k
  expansion : ∀ I : Set V, G.IsIndepSet I → I.Nonempty →
    k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard

abbrev PathSystem.missing {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : Set V := {x | [x] ∈ P.chains}

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_FiniteGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

noncomputable def chosenChain {V : Type*} (Q : Set V) (c : List V) : List V :=
  if c.length = 4 then c.tail.dropLast else (markedReps Q true c).filter (fun x => x ∉ Q)

noncomputable def PathSystem.chosen {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : List V := (P.chains.map (chosenChain Q)).flatten

end CycleClique

namespace CycleClique
open scoped SimpleGraph

 

structure FiniteHyp {V : Type*} [Fintype V] (G : SimpleGraph V) (k t : ℕ) : Prop where
  hk : 5 ≤ k
  ht : 3 ≤ t
  htk : t ≤ k
  hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G
  hclique : G.cliqueNum ≤ t
  hα : G.indepNum ≤ k
  hexp : ∀ I : Set V, G.IsIndepSet I → I.Nonempty →
    k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard


def labelAdj (E : List (ℕ × ℕ)) (a b : ℕ) : Prop := (a,b) ∈ E ∨ (b,a) ∈ E
instance instDecidableLabelAdj (E : List (ℕ × ℕ)) (a b : ℕ) : Decidable (labelAdj E a b) := by
  unfold labelAdj
  infer_instance

 
def LabelValid (n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ)) (C : List (List ℕ)) : Prop :=
  C.flatten.Nodup ∧ (∀ i ∈ C.flatten, i < n) ∧
  (∀ c ∈ C, c ≠ [] ∧ c.IsChain (labelAdj E) ∧
    c.IsChain (fun a b => a ∉ q ∨ b ∉ q) ∧
    (∀ x ∈ c.head?, x ∈ q) ∧ (∀ x ∈ c.getLast?, x ∈ q)) ∧
  ∀ i ∈ q, i ∈ C.flatten

instance instDecidableLabelValid (n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ)) (C : List (List ℕ)) :
    Decidable (LabelValid n q E C) := by
  unfold LabelValid
  infer_instance

structure LabelState {V : Type*} (G : SimpleGraph V) (Q : Set V)
    (n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ)) where
  f : ℕ → V
  inj : Set.InjOn f (Set.Iio n)
  qb : ∀ i ∈ q, i < n
  qimage : Q = f '' (↑q : Set ℕ)
  eb : ∀ a b, (a,b) ∈ E → a < n ∧ b < n
  edges : ∀ a b, labelAdj E a b → G.Adj (f a) (f b)

namespace LabelState
variable {V : Type*} {G : SimpleGraph V} {Q : Set V}
  {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (S : LabelState G Q n q E)

def vertices : Set V := S.f '' Set.Iio n

theorem mem_clique {i : ℕ} (hi : i < n) : S.f i ∈ Q ↔ i ∈ q := by
  constructor
  · intro hx
    have him : S.f i ∈ S.f '' (↑q : Set ℕ) := S.qimage ▸ hx
    obtain ⟨j, hj, he⟩ := him
    have hji := S.inj (S.qb j hj) hi he
    simpa only [hji, Finset.mem_coe] using hj
  · intro h
    exact Eq.mp (congrArg (fun A : Set V => S.f i ∈ A) S.qimage.symm)
      (show S.f i ∈ S.f '' (↑q : Set ℕ) from ⟨i, h, rfl⟩)

noncomputable def system {C : List (List ℕ)} (h : LabelValid n q E C) : PathSystem G Q := by
  classical
  refine {
    chains := C.map (List.map S.f)
    nonempty := ?_
    nodup := ?_
    edges := ?_
    positive := ?_
    ends := ?_
    cover := ?_ }
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    simpa using (h.2.2.1 a ha).1
  · rw [← List.map_flatten]
    exact h.1.map_on (fun a ha b hb he => S.inj (h.2.1 a ha) (h.2.1 b hb) he)
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    apply (List.isChain_map S.f).mpr
    exact (h.2.2.1 a ha).2.1.imp (fun {u v} huv => S.edges u v huv)
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    apply (List.isChain_map S.f).mpr
    apply (h.2.2.1 a ha).2.2.1.imp_of_mem_imp
    intro u v hu hv huv
    have hub := h.2.1 u (List.mem_flatten.mpr ⟨a, ha, hu⟩)
    have hvb := h.2.1 v (List.mem_flatten.mpr ⟨a, ha, hv⟩)
    simpa only [S.mem_clique hub, S.mem_clique hvb] using huv
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    constructor
    · intro x hx
      simp only [List.head?_map, Option.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact (S.mem_clique (S.qb i ((h.2.2.1 a ha).2.2.2.1 i hi))).mpr
        ((h.2.2.1 a ha).2.2.2.1 i hi)
    · intro x hx
      simp only [List.getLast?_map, Option.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact (S.mem_clique (S.qb i ((h.2.2.1 a ha).2.2.2.2 i hi))).mpr
        ((h.2.2.1 a ha).2.2.2.2 i hi)
  · intro x hx
    rw [S.qimage] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [← List.map_flatten]
    exact List.mem_map.mpr ⟨i, h.2.2.2 i hi, rfl⟩

@[simp] theorem system_chains {C : List (List ℕ)} (h : LabelValid n q E C) :
    (S.system h).chains = C.map (List.map S.f) := rfl

end LabelState

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_BallPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def pathEdges : List ℕ → List (ℕ × ℕ)
  | a :: b :: l => (a,b) :: pathEdges (b :: l)
  | _ => []

def pathLabels (n i j d : ℕ) : List ℕ := i :: (List.range' n d ++ [j])

def augmentedEdges (n : ℕ) (E : List (ℕ × ℕ)) (i j d : ℕ) : List (ℕ × ℕ) :=
  E ++ pathEdges (pathLabels n i j d)

theorem pathEdges_mem {L : List ℕ} {a b : ℕ} (hab : (a,b) ∈ pathEdges L) :
    a ∈ L ∧ b ∈ L := by
  induction L using List.twoStepInduction with
  | nil => simp [pathEdges] at hab
  | singleton x => simp [pathEdges] at hab
  | cons_cons x y L ih₀ ih =>
    simp only [pathEdges, List.mem_cons] at hab
    rcases hab with he | hab
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      simp
    · have hh := ih y hab
      exact ⟨List.mem_cons_of_mem _ hh.1, List.mem_cons_of_mem _ hh.2⟩

theorem pathEdges_sound {V : Type*} {G : SimpleGraph V} (f : ℕ → V)
    {L : List ℕ} (h : (L.map f).IsChain G.Adj) {a b : ℕ}
    (hab : (a,b) ∈ pathEdges L) : G.Adj (f a) (f b) := by
  induction L using List.twoStepInduction with
  | nil => simp [pathEdges] at hab
  | singleton x => simp [pathEdges] at hab
  | cons_cons x y L ih₀ ih =>
    simp only [pathEdges, List.mem_cons] at hab
    rcases hab with he | hab
    · have he' := Prod.mk.inj he
      obtain ⟨rfl, rfl⟩ := he'
      exact List.isChain_cons_cons.mp h |>.1
    · exact ih y (List.IsChain.tail h) hab

namespace LabelState
variable {V : Type*} {G : SimpleGraph V} {Q : Set V}
  {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (S : LabelState G Q n q E)

def extendedFunction (I : List V) (i : ℕ) : V :=
  if i < n then S.f i else I[i-n]?.getD (S.f 0)

end LabelState

 
def LabelCycleValid (n k : ℕ) (E : List (ℕ × ℕ)) (L : List ℕ) : Prop :=
  L.Nodup ∧ L.length = k + 1 ∧ (∀ i ∈ L, i < n) ∧
  L.IsChain (labelAdj E) ∧ ∀ x ∈ L.head?, ∀ y ∈ L.getLast?, labelAdj E y x
instance instDecidableLabelCycleValid (n k : ℕ) (E : List (ℕ × ℕ)) (L : List ℕ) :
    Decidable (LabelCycleValid n k E L) := by
  unfold LabelCycleValid
  infer_instance



structure OriginalSystem {V : Type*} [Fintype V] (G : SimpleGraph V) (Q : Set V)
    (k t L e : ℕ) where
  P : PathSystem G Q
  optimal : P.Optimal k
  clique : G.IsClique Q
  card : Q.ncard = t
  amount : P.amount = L
  edges : P.edgeCount = e

 

def Improvement (k t L e : ℕ) (C : List (List ℕ)) : Prop :=
  let A := C.flatten.length - t
  let N := t - C.length
  let v := t - (C.filter (fun c => c.length = 1)).length
  (A < k + 1 - t ∧ (L < A ∨ (L = A ∧ N < e))) ∨
  (k + 1 - t ≤ A ∧ A ≤ k + 1 - v)
instance instDecidableImprovement (k t L e : ℕ) (C : List (List ℕ)) : Decidable (Improvement k t L e C) := by
  unfold Improvement
  infer_instance

abbrev ForbiddenMatrix := List (ℕ × ℕ × ℕ)

def matrixEntry (M : ForbiddenMatrix) (i j d : ℕ) : Prop :=
  (i,j,d) ∈ M ∨ (j,i,d) ∈ M
instance instDecidableMatrixEntry (M : ForbiddenMatrix) (i j d : ℕ) : Decidable (matrixEntry M i j d) := by
  unfold matrixEntry
  infer_instance

structure ValidMatrix {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (S : LabelState G Q n q E)
    (M : ForbiddenMatrix) : Prop where
  bounds : ∀ c ∈ M, c.1 < n ∧ c.2.1 < n
  forbidden : ∀ c ∈ M, ¬ OutsidePath G S.vertices (S.f c.1) (S.f c.2.1) c.2.2


def Excluded (n : ℕ) (M : ForbiddenMatrix) (i lo hi : ℕ) (Z : Finset ℕ) : Prop :=
  (∀ j ∈ Z, j < n ∧ j ≠ i) ∧
  ∀ j ∈ Z, ∀ d ∈ Finset.Icc lo hi, matrixEntry M i j d
instance instDecidableExcluded (n : ℕ) (M : ForbiddenMatrix) (i lo hi : ℕ) (Z : Finset ℕ) :
    Decidable (Excluded n M i lo hi Z) := by
  unfold Excluded
  infer_instance

namespace LabelState
variable {V : Type*} {G : SimpleGraph V} {Q : Set V}
  {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (S : LabelState G Q n q E)

def imageLabels (Z : Finset ℕ) : Set V := S.f '' (↑Z : Set ℕ)

end LabelState

 

inductive BallCertificate where
  | zero (Z : Finset ℕ) (b u : ℕ)
  | succ (previous : BallCertificate) (Z : Finset ℕ) (b u : ℕ)
  deriving DecidableEq
namespace BallCertificate

def radius : BallCertificate → ℕ
  | .zero _ _ _ => 0
  | .succ p _ _ _ => p.radius + 1

def size : BallCertificate → ℕ
  | .zero _ b _ => b
  | .succ _ _ b _ => b

def weight : BallCertificate → ℕ
  | .zero _ _ u => u
  | .succ _ _ _ u => u

def Valid (k t n : ℕ) (M : ForbiddenMatrix) (i : ℕ) : BallCertificate → Prop
  | .zero Z b u => Excluded n M i 0 0 Z ∧ 0 < b ∧ n + b ≤ k + 1 + Z.card ∧
      1 ≤ u ∧ (u ≤ 1 ∨ (u ≤ 2 ∧ t ≤ b))
  | .succ p Z b u => p.Valid k t n M i ∧ Excluded n M i 1 (p.radius+1) Z ∧
      (b ≤ p.size ∨ n + b ≤ k * p.weight + 1 + Z.card) ∧ 1 ≤ u ∧
      (u ≤ p.weight ∨ (u ≤ 2 ∧ t < b) ∨ (u ≤ 3 ∧ max k (2*t) < b) ∨
        (u ≤ 2 ∧ t ≤ p.size ∧ n + t ≤ k + 1 + Z.card))

instance instDecidableValid (k t n : ℕ) (M : ForbiddenMatrix) (i : ℕ) (B : BallCertificate) :
    Decidable (B.Valid k t n M i) :=
  match B with
  | .zero Z b u => by unfold Valid; infer_instance
  | .succ p Z b u => by
    unfold Valid
    exact @instDecidableAnd _ _ (instDecidableValid k t n M i p) inferInstance

end BallCertificate

inductive PackingOption where
  | singleton (i : ℕ)
  | ball (i : ℕ) (B : BallCertificate)
  deriving DecidableEq

namespace PackingOption

def base : PackingOption → ℕ
  | .singleton i | .ball i _ => i

def radiusCode : PackingOption → ℕ
  | .singleton _ => 0
  | .ball _ B => B.radius + 1

def weight : PackingOption → ℕ
  | .singleton _ => 1
  | .ball _ B => B.weight

def Valid (k t n : ℕ) (M : ForbiddenMatrix) : PackingOption → Prop
  | .singleton i => i < n
  | .ball i B => i < n ∧ B.radius ≤ 2 ∧ B.Valid k t n M i
instance instDecidableValid (k t n : ℕ) (M : ForbiddenMatrix) (o : PackingOption) :
    Decidable (o.Valid k t n M) := by
  cases o <;> unfold Valid <;> infer_instance

def Compatible (M : ForbiddenMatrix) (a b : PackingOption) : Prop :=
  a.base ≠ b.base ∧
  if a.radiusCode + b.radiusCode = 0 then matrixEntry M a.base b.base 0
  else ∀ d ∈ Finset.Icc 1 (a.radiusCode+b.radiusCode), matrixEntry M a.base b.base d
instance instDecidableCompatible (M : ForbiddenMatrix) (a b : PackingOption) : Decidable (Compatible M a b) := by
  unfold Compatible
  infer_instance

def vertices {V : Type*} (G : SimpleGraph V) (X : Set V) (f : ℕ → V) : PackingOption → Set V
  | .singleton i => {f i}
  | .ball i B => outsideBall G X (f i) B.radius

end PackingOption

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CertificateModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def PackingValid (k t n : ℕ) (M : ForbiddenMatrix) (P : Finset PackingOption) : Prop :=
  (∀ o ∈ P, o.Valid k t n M) ∧
  (∀ a ∈ P, ∀ b ∈ P, a ≠ b → a.Compatible M b) ∧ k < ∑ o ∈ P, o.weight
instance instDecidablePackingValid (k t n : ℕ) (M : ForbiddenMatrix) (P : Finset PackingOption) :
    Decidable (PackingValid k t n M P) := by
  unfold PackingValid
  infer_instance



inductive FiniteCertificate where
  | system (C : List (List ℕ))
  | cycle (C : List ℕ)
  | packing (P : Finset PackingOption)
  | edge (i j : ℕ)
  | forbid (i j d : ℕ) (reason next : FiniteCertificate)
  deriving DecidableEq
namespace FiniteCertificate

def Valid (k t n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ)) (L e : ℕ)
    (M : ForbiddenMatrix) : FiniteCertificate → Prop
  | .system C => LabelValid n q E C ∧ Improvement k t L e C
  | .cycle C => LabelCycleValid n k E C
  | .packing P => PackingValid k t n M P
  | .edge i j => i < n ∧ j < n ∧ labelAdj E i j ∧ matrixEntry M i j 0
  | .forbid i j d R N => i < n ∧ j < n ∧
      R.Valid k t (n+d) q (augmentedEdges n E i j d) L e M ∧
      N.Valid k t n q E L e ((i,j,d)::M)

instance instDecidableValid (k t n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ))
    (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    Decidable (C.Valid k t n q E L e M) :=
  match C with
  | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold Valid; infer_instance
  | .forbid i j d R N => by
    unfold Valid
    exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ (instDecidableValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
        (instDecidableValid k t n q E L e ((i,j,d)::M) N)))

end FiniteCertificate
open scoped SimpleGraph

 
def normalizedChain (A : List ℕ) : List ℕ := min A A.reverse

def canonicalPattern (D : List (List ℕ)) : List (List ℕ) :=
  (D.map normalizedChain).mergeSort (fun a b => decide (a ≤ b))


def chainOrder (A : List ℕ) : ℕ := A.sum + A.length + 1

def chainClique (b : ℕ) : List ℕ → List ℕ
  | [] => [b]
  | a::A => b :: chainClique (b+a+1) A

def patternChainsFrom (b : ℕ) : List (List ℕ) → List (List ℕ)
  | [] => []
  | A::D => List.range' b (chainOrder A) :: patternChainsFrom (b+chainOrder A) D

def patternCliqueFrom (b : ℕ) : List (List ℕ) → List ℕ
  | [] => []
  | A::D => chainClique b A ++ patternCliqueFrom (b+chainOrder A) D

def patternOrder (D : List (List ℕ)) : ℕ := (D.map chainOrder).sum

def patternClique (D : List (List ℕ)) : Finset ℕ := (patternCliqueFrom 0 D).toFinset

def patternEdges (D : List (List ℕ)) : List (ℕ × ℕ) :=
  (patternChainsFrom 0 D).flatMap pathEdges ++
    ((patternCliqueFrom 0 D).product (patternCliqueFrom 0 D)).filter (fun p => p.1 < p.2)

def patternAmount (D : List (List ℕ)) : ℕ := D.flatten.sum

def patternEdgeCount (D : List (List ℕ)) : ℕ := D.flatten.length

@[simp] theorem patternOrder_nil : patternOrder [] = 0 := rfl
@[simp] theorem patternOrder_cons (A : List ℕ) (D : List (List ℕ)) :
    patternOrder (A::D) = chainOrder A + patternOrder D := rfl

@[simp] theorem patternChainsFrom_length (b : ℕ) (D : List (List ℕ)) :
    (patternChainsFrom b D).length = D.length := by
  induction D generalizing b with
  | nil => rfl
  | cons A D ih => simp [patternChainsFrom, ih]

theorem patternChainsFrom_flatten (b : ℕ) (D : List (List ℕ)) :
    (patternChainsFrom b D).flatten = List.range' b (patternOrder D) := by
  induction D generalizing b with
  | nil => simp [patternChainsFrom]
  | cons A D ih =>
    simp only [patternChainsFrom, List.flatten_cons, ih, patternOrder_cons]
    simpa only [Nat.one_mul] using (List.range'_append (step := 1) (s := b) (m := chainOrder A) (n := patternOrder D))

theorem chainClique_bounds {b i : ℕ} {A : List ℕ} (hi : i ∈ chainClique b A) :
    b ≤ i ∧ i < b + chainOrder A := by
  induction A generalizing b with
  | nil => simp only [chainClique, List.mem_singleton] at hi; subst i; simp [chainOrder]
  | cons a A ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · simp [chainOrder]
    · obtain ⟨hl,hu⟩ := ih hi
      simp only [chainOrder, List.sum_cons, List.length_cons] at *
      omega

theorem patternCliqueFrom_bounds {b i : ℕ} {D : List (List ℕ)}
    (hi : i ∈ patternCliqueFrom b D) : b ≤ i ∧ i < b + patternOrder D := by
  induction D generalizing b with
  | nil => simp [patternCliqueFrom] at hi
  | cons A D ih =>
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨hl,hu⟩ := chainClique_bounds hi
      exact ⟨hl,by simp only [patternOrder_cons]; omega⟩
    · obtain ⟨hl,hu⟩ := ih hi
      exact ⟨by omega,by simp only [patternOrder_cons]; omega⟩

theorem map_range_getD {V : Type*} (c : List V) (v : V) :
    (List.range' 0 c.length).map (fun i => c.getD i v) = c := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_range', Nat.one_mul, Nat.zero_add]
  exact c.getD_eq_getElem v hi'

theorem ChainAmounts.clique_map {V : Type*} {Q : Set V} [DecidablePred (· ∈ Q)] {c : List V} {A : List ℕ}
    (hA : ChainAmounts Q c A) (f : ℕ → V) {b : ℕ}
    (hmap : (List.range' b (chainOrder A)).map f = c) :
    (chainClique b A).map f = c.filter (fun v => decide (v ∈ Q)) := by
  induction hA generalizing b with
  | singleton x hx =>
    simpa [chainOrder, chainClique, hx] using hmap
  | step x y I B A hx hI hout htail ih =>
    have hh := congrArg List.head? hmap
    have hhead : f b = x := by
      simpa only [chainOrder, List.sum_cons, List.length_cons, List.range'_succ,
        List.map_cons, List.head?_cons, Option.some.injEq] using hh
    have hd := congrArg (List.drop (I.length+1)) hmap
    rw [← List.map_drop, List.drop_range'] at hd
    have hlen : chainOrder (I.length::A) - (I.length+1) = chainOrder A := by
      simp only [chainOrder, List.sum_cons, List.length_cons]
      omega
    simp only [Nat.mul_one, hlen, List.drop_succ_cons, List.drop_left] at hd
    have htailmap : (List.range' (b+I.length+1) (chainOrder A)).map f = y::B := by
      simpa only [Nat.add_assoc] using hd
    have hIfilter : I.filter (fun v => decide (v ∈ Q)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      simpa using hout
    rw [chainClique, List.map_cons, hhead, ih htailmap]
    conv_rhs => rw [List.filter_cons]
    simp only [hx, decide_true, ↓reduceIte, List.filter_append, hIfilter, List.nil_append]

theorem amounts_order {V : Type*} {Q : Set V} {C : List (List V)} {D : List (List ℕ)}
    (h : List.Forall₂ (ChainAmounts Q) C D) : C.flatten.length = patternOrder D := by
  induction h with
  | nil => rfl
  | @cons c A C D hc h ih =>
    simp only [List.flatten_cons, List.length_append, patternOrder_cons, ←ih]
    exact congrArg (· + C.flatten.length) hc.count.2.1

theorem amounts_shape {V : Type*} {Q : Set V} [DecidablePred (· ∈ Q)] {C : List (List V)} {D : List (List ℕ)}
    (h : List.Forall₂ (ChainAmounts Q) C D) (f : ℕ → V) {b : ℕ}
    (hmap : (List.range' b (patternOrder D)).map f = C.flatten) :
    (patternChainsFrom b D).map (List.map f) = C ∧
    (patternCliqueFrom b D).map f = C.flatten.filter (fun v => decide (v ∈ Q)) := by
  induction h generalizing b with
  | nil => simp [patternChainsFrom,patternCliqueFrom]
  | @cons c A C D hc h ih =>
    have hsplit : (List.range' b (chainOrder A)).map f ++
        (List.range' (b+chainOrder A) (patternOrder D)).map f = c ++ C.flatten := by
      rw [←List.map_append]
      rw [show List.range' b (chainOrder A) ++ List.range' (b+chainOrder A) (patternOrder D) =
        List.range' b ((chainOrder A)+(patternOrder D)) by simp]
      exact hmap
    obtain ⟨hfirst,hrest⟩ := List.append_inj hsplit (by simpa [chainOrder] using hc.count.2.1.symm)
    obtain ⟨hshape,hclique⟩ := ih hrest
    constructor
    · simp only [patternChainsFrom, List.map_cons, hfirst, hshape]
    · simp only [patternCliqueFrom, List.map_append, hc.clique_map f hfirst, hclique,
        List.flatten_cons, List.filter_append]

 

noncomputable def PathSystem.labelState {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (hQ : G.IsClique Q)
    {D : List (List ℕ)} (hD : List.Forall₂ (ChainAmounts Q) P.chains D) (v : V) :
    LabelState G Q (patternOrder D) (patternClique D) (patternEdges D) := by
  classical
  let f : ℕ → V := fun i => P.chains.flatten.getD i v
  have hlen := amounts_order hD
  have hmap : (List.range' 0 (patternOrder D)).map f = P.chains.flatten := by
    rw [←hlen]
    exact map_range_getD _ _
  obtain ⟨hshape,hclique⟩ := amounts_shape hD f hmap
  have hq : Q = f '' (↑(patternClique D) : Set ℕ) := by
    ext x
    constructor
    · intro hx
      have hm : x ∈ (patternCliqueFrom 0 D).map f := by
        rw [hclique]
        exact List.mem_filter.mpr ⟨P.cover x hx, by simpa using hx⟩
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
      exact ⟨i, List.mem_toFinset.mpr hi, rfl⟩
    · rintro ⟨i,hi,rfl⟩
      have hm : f i ∈ (patternCliqueFrom 0 D).map f :=
        List.mem_map.mpr ⟨i,List.mem_toFinset.mp hi,rfl⟩
      rw [hclique] at hm
      simpa using (List.mem_filter.mp hm).2
  have hinj : Set.InjOn f (Set.Iio (patternOrder D)) := by
    intro i hi j hj he
    have hi' : i < P.chains.flatten.length := hlen ▸ hi
    have hj' : j < P.chains.flatten.length := hlen ▸ hj
    simp only [f, List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at he
    exact (P.nodup.getElem_inj_iff).mp he
  have hqb : ∀ i ∈ patternClique D, i < patternOrder D := by
    intro i hi
    simpa using (patternCliqueFrom_bounds (List.mem_toFinset.mp hi)).2
  have heb : ∀ a b, (a,b) ∈ patternEdges D → a < patternOrder D ∧ b < patternOrder D := by
    intro a b hab
    rcases List.mem_append.mp hab with hab | hab
    · obtain ⟨c,hc,hab⟩ := List.mem_flatMap.mp hab
      obtain ⟨ha,hb⟩ := pathEdges_mem hab
      have hal : a ∈ (patternChainsFrom 0 D).flatten := List.mem_flatten.mpr ⟨c,hc,ha⟩
      have hbl : b ∈ (patternChainsFrom 0 D).flatten := List.mem_flatten.mpr ⟨c,hc,hb⟩
      rw [patternChainsFrom_flatten] at hal hbl
      simp only [List.mem_range'] at hal hbl
      exact ⟨by omega, by omega⟩
    · obtain ⟨hab,_⟩ := List.mem_filter.mp hab
      obtain ⟨ha,hb⟩ := List.mem_product.mp hab
      exact ⟨hqb a (List.mem_toFinset.mpr ha), hqb b (List.mem_toFinset.mpr hb)⟩
  have hadj : ∀ a b, (a,b) ∈ patternEdges D → G.Adj (f a) (f b) := by
    intro a b hab
    rcases List.mem_append.mp hab with hab | hab
    · obtain ⟨c,hc,hab⟩ := List.mem_flatMap.mp hab
      have hcm : c.map f ∈ P.chains := by
        rw [←hshape]
        exact List.mem_map.mpr ⟨c,hc,rfl⟩
      exact pathEdges_sound f (P.edges _ hcm) hab
    · obtain ⟨hab,hlt⟩ := List.mem_filter.mp hab
      obtain ⟨ha,hb⟩ := List.mem_product.mp hab
      have hai := hqb a (List.mem_toFinset.mpr ha)
      have hbi := hqb b (List.mem_toFinset.mpr hb)
      apply hQ
      · rw [hq]; exact ⟨a,List.mem_toFinset.mpr ha,rfl⟩
      · rw [hq]; exact ⟨b,List.mem_toFinset.mpr hb,rfl⟩
      · intro he
        have hh := hinj hai hbi he
        have hh' : a < b := of_decide_eq_true hlt
        omega
  exact {
    f := f
    inj := hinj
    qb := hqb
    qimage := hq
    eb := heb
    edges := fun a b hab => hab.elim (hadj a b) (fun h => (hadj b a h).symm) }

@[simp] theorem patternAmount_cons (A : List ℕ) (D : List (List ℕ)) :
    patternAmount (A::D) = A.sum + patternAmount D := by
  simp [patternAmount]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_0_q : Finset ℕ := ([0,1,2] : List ℕ).toFinset
noncomputable def certificate_0_edges : List (ℕ × ℕ) := [(0,1),(0,2),(1,2)]

noncomputable def certificate_0 : FiniteCertificate := .forbid 0 1 1 (.system [[0,3,1],[2]]) (.forbid 0 1 2 (.system [[0,3,4,1],[2]]) (.forbid 0 1 3 (.system [[0,3,4,5,1],[2]]) (.forbid 0 1 4 (.system [[0,3,4,5,6,1],[2]]) (.packing {.ball 0 (.succ (.zero ∅ 3 2) ∅ 8 3), .ball 1 (.succ (.zero ∅ 3 2) ∅ 8 3)}))))

noncomputable def certificate_1_part_1 : FiniteCertificate := .forbid 1 2 2 (.system [[0],[1,4,5,2,3]]) (.forbid 1 2 3 (.system [[0],[1,4,5,6,2,3]]) (.forbid 1 2 4 (.cycle [1,2,7,6,5,4]) (.forbid 0 2 0 (.forbid 0 2 4 (.cycle [0,2,7,6,5,4]) (.packing {.ball 0 (.succ (.zero ∅ 2 1) {1,2} 4 2), .ball 1 (.succ (.zero ∅ 2 1) {0,2} 4 2), .ball 2 (.succ (.zero ∅ 2 1) {0,1} 4 2)})) (.packing {.ball 0 (.succ (.zero {2} 3 2) ∅ 7 3), .ball 2 (.zero {0} 3 2), .ball 1 (.succ (.zero ∅ 2 1) {0,2} 4 2)}))))

noncomputable def certificate_1 : FiniteCertificate := .forbid 0 1 1 (.system [[0,4,1,2,3]]) (.forbid 0 1 2 (.system [[0,4,5,1],[3]]) (.forbid 0 1 3 (.system [[0,4,5,6,1],[3]]) (.forbid 0 1 4 (.system [[0,4,5,6,7,1],[3]]) (.forbid 0 2 1 (.system [[0,4,2,1],[3]]) (.forbid 0 2 2 (.system [[0,4,5,2,1],[3]]) (.forbid 0 2 3 (.system [[0,4,5,6,2,1],[3]]) (.forbid 1 2 1 (.system [[0],[1,4,2,3]]) (certificate_1_part_1))))))))

noncomputable def certificate_10_part_2 : FiniteCertificate := .forbid 2 4 1 (.cycle [2,1,0,6,3,4,7]) (.forbid 2 5 0 (.cycle [2,1,0,6,3,4,5]) (.packing {.ball 0 (.succ (.succ (.zero {2} 1 1) {1,2,4,5} 4 2) {2} 7 3), .ball 2 (.zero {0,4,5} 3 2), .ball 4 (.zero {0,1,2} 3 2)}))

noncomputable def certificate_10_part_4 : FiniteCertificate := .forbid 2 6 0 (.cycle [2,1,0,5,4,3,6]) (.forbid 4 6 0 (.cycle [4,3,2,1,0,5,6]) (.forbid 4 6 1 (.cycle [4,3,2,1,5,6,7]) (.packing {.ball 0 (.succ (.succ (.zero {4} 1 1) {1,2,4,6} 4 2) {2} 7 3), .ball 4 (.zero {0,2,6} 3 2), .singleton 6, .singleton 2})))

noncomputable def certificate_10_part_5 : FiniteCertificate := .forbid 0 5 2 (.cycle [0,2,3,4,5,7,6]) (.forbid 0 5 3 (.cycle [0,2,1,5,8,7,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {3,4,5} 4 2) ∅ 7 3), .ball 5 (.succ (.zero ∅ 1 1) {0,3,4} 4 2), .singleton 4, .ball 3 (.zero ∅ 1 1)}))

noncomputable def certificate_10_part_7 : FiniteCertificate := .forbid 1 4 2 (.cycle [1,5,0,3,4,7,6]) (.forbid 2 4 1 (.cycle [2,1,5,0,3,4,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,4} 4 2) ∅ 7 3), .ball 1 (.succ (.zero ∅ 1 1) {0,2,4} 4 2), .singleton 2, .ball 4 (.zero ∅ 1 1)}))

noncomputable def certificate_10_part_8 : FiniteCertificate := .forbid 0 6 3 (.cycle [0,5,1,6,9,8,7]) (.forbid 2 4 0 (.cycle [2,3,6,1,0,5,4]) (.forbid 2 4 1 (.cycle [2,3,6,1,5,4,7]) (.forbid 2 6 0 (.cycle [2,1,0,5,4,3,6]) (.forbid 2 6 1 (.cycle [2,1,5,4,3,6,7]) (.forbid 4 6 0 (.cycle [4,5,0,1,2,3,6]) (.packing {.ball 0 (.succ (.succ (.zero {2} 1 1) {1,2,4,6} 4 2) {2} 7 3), .ball 2 (.zero {0,4,6} 3 2), .singleton 6, .singleton 4}))))))

noncomputable def certificate_10_part_10 : FiniteCertificate := .forbid 0 1 2 (.cycle [0,5,4,2,1,7,6]) (.packing {.ball 0 (.succ (.zero {2,3} 3 2) ∅ 7 3), .ball 3 (.zero {0,1} 3 2), .singleton 1, .ball 2 (.zero ∅ 1 1)})

noncomputable def certificate_10_part_12 : FiniteCertificate := .forbid 4 6 0 (.cycle [4,3,2,1,0,5,6]) (.forbid 4 6 1 (.cycle [4,3,2,1,5,6,7]) (.forbid 4 6 2 (.cycle [4,5,1,2,6,8,7]) (.forbid 4 6 3 (.cycle [4,3,2,6,9,8,7]) (.forbid 4 6 4 (.cycle [4,5,6,10,9,8,7]) (.packing {.ball 0 (.succ (.zero {3,4,6} 3 2) {4} 7 3), .ball 4 (.succ (.zero {0,1,6} 3 2) {0} 7 3), .ball 6 (.succ (.zero {0,1,4} 3 2) {0} 7 3)})))))

noncomputable def certificate_10_part_13 : FiniteCertificate := .forbid 2 6 0 (.cycle [2,3,4,5,0,1,6]) (.forbid 2 6 1 (.cycle [2,1,0,5,4,6,7]) (.forbid 2 6 2 (.cycle [2,1,5,4,6,8,7]) (.forbid 2 6 3 (.cycle [2,3,4,6,9,8,7]) (.forbid 2 6 4 (.cycle [2,1,6,10,9,8,7]) (.forbid 3 6 0 (.cycle [3,2,1,0,5,4,6]) (.packing {.ball 0 (.succ (.zero {2,3,6} 3 2) {2} 7 3), .ball 2 (.succ (.zero {0,5,6} 3 2) {0} 7 3), .ball 6 (.succ (.zero {0,2,3} 3 2) {0} 7 3)}))))))

noncomputable def certificate_10_part_11 : FiniteCertificate := .forbid 2 5 1 (.forbid 0 6 0 (.cycle [0,1,2,3,4,5,6]) (.forbid 0 6 1 (.cycle [0,5,4,3,2,6,7]) (.forbid 0 6 2 (.cycle [0,5,1,2,6,8,7]) (.forbid 0 6 3 (.cycle [0,1,2,6,9,8,7]) (.forbid 0 6 4 (.cycle [0,5,6,10,9,8,7]) (.forbid 1 4 0 (.cycle [1,0,5,6,2,3,4]) (.forbid 1 6 0 (.cycle [1,0,5,4,3,2,6]) (certificate_10_part_12)))))))) (.forbid 1 4 1 (.forbid 0 6 0 (.cycle [0,5,1,2,3,4,6]) (.forbid 0 6 1 (.cycle [0,1,2,3,4,6,7]) (.forbid 0 6 2 (.cycle [0,1,5,4,6,8,7]) (.forbid 0 6 3 (.cycle [0,5,1,6,9,8,7]) (.forbid 0 6 4 (.cycle [0,1,6,10,9,8,7]) (.forbid 2 5 0 (.cycle [2,3,4,6,1,0,5]) (certificate_10_part_13))))))) (.forbid 3 5 0 (.forbid 0 1 2 (.cycle [0,5,3,2,1,7,6]) (.forbid 1 4 2 (.cycle [1,0,5,3,4,7,6]) (.forbid 2 4 1 (.cycle [2,1,0,5,3,4,6]) (.packing {.ball 0 (.succ (.zero ∅ 1 1) {1,2,4} 4 2), .ball 2 (.succ (.zero ∅ 1 1) {0,1,4} 4 2), .ball 4 (.succ (.zero ∅ 1 1) {0,1,2} 4 2), .singleton 1})))) (.forbid 2 4 1 (.forbid 2 3 3 (.cycle [2,6,4,3,9,8,7]) (.packing {.ball 0 (.succ (.zero {2,3,4} 3 2) {2} 7 3), .ball 3 (.zero {0,1,5} 3 2), .ball 2 (.succ (.zero {0} 1 1) {0,1,3,5} 4 2)})) (.packing {.ball 0 (.succ (.zero {2,3} 3 2) ∅ 7 3), .ball 2 (.succ (.zero {0,4} 3 2) ∅ 7 3), .ball 4 (.succ (.zero {0,2} 3 2) ∅ 7 3)}))))

noncomputable def certificate_10_part_9 : FiniteCertificate := .forbid 2 3 1 (.system [[0],[1,2,6,3,4,5]]) (.forbid 0 4 0 (.forbid 0 1 2 (.cycle [0,4,3,2,1,7,6]) (.forbid 0 1 3 (.cycle [0,4,5,1,8,7,6]) (.forbid 0 3 4 (.cycle [0,4,3,9,8,7,6]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3} 4 2) ∅ 7 3), .ball 1 (.succ (.zero ∅ 1 1) {0,2,3} 4 2), .singleton 2, .ball 3 (.zero ∅ 1 1)})))) (.forbid 2 3 2 (.system [[0],[1,2,6,7,3,4,5]]) (.forbid 2 4 3 (.system [[0],[1,2,6,7,8,4,5]]) (.forbid 2 4 4 (.cycle [2,3,4,9,8,7,6]) (.forbid 3 4 2 (.system [[0],[1,2,3,6,7,4,5]]) (.forbid 1 3 0 (.forbid 2 4 1 (.cycle [2,3,1,0,5,4,6]) (.packing {.ball 0 (.succ (.zero ∅ 1 1) {2,3,4} 4 2), .ball 2 (.succ (.zero ∅ 1 1) {0,3,4} 4 2), .ball 4 (.succ (.zero ∅ 1 1) {0,2,3} 4 2), .singleton 3})) (.forbid 2 4 0 (certificate_10_part_10) (certificate_10_part_11))))))))

noncomputable def certificate_10_part_6 : FiniteCertificate := .forbid 0 1 5 (.system [[0,6,7,8,9,10,1],[5]]) (.forbid 1 2 1 (.system [[0],[1,6,2,3,4,5]]) (.forbid 1 2 2 (.system [[0],[1,6,7,2,3,4,5]]) (.forbid 1 4 3 (.system [[0],[1,6,7,8,4,5]]) (.forbid 0 3 0 (.forbid 0 1 2 (.cycle [0,3,4,5,1,7,6]) (.forbid 0 1 3 (.cycle [0,3,2,1,8,7,6]) (.forbid 1 4 1 (.cycle [1,2,3,0,5,4,6]) (certificate_10_part_7)))) (.forbid 1 3 1 (.forbid 0 6 1 (.cycle [0,1,5,4,3,6,7]) (.forbid 0 6 2 (.cycle [0,1,2,3,6,8,7]) (certificate_10_part_8))) (.forbid 1 3 2 (.system [[0],[1,6,7,3,4,5]]) (.forbid 1 3 3 (.system [[0],[1,6,7,8,3,4,5]]) (certificate_10_part_9))))))))

noncomputable def certificate_10_part_3 : FiniteCertificate := .forbid 3 4 1 (.system [[0],[1,2,3,6,4,5]]) (.forbid 3 5 1 (.forbid 0 4 0 (.cycle [0,1,2,3,6,5,4]) (.forbid 0 6 1 (.cycle [0,1,5,4,3,6,7]) (.forbid 0 6 2 (.cycle [0,1,2,3,6,8,7]) (.forbid 0 6 3 (.cycle [0,1,5,6,9,8,7]) (.forbid 2 4 0 (.cycle [2,1,0,5,6,3,4]) (.forbid 2 4 1 (.cycle [2,1,5,6,3,4,7]) (certificate_10_part_4))))))) (.forbid 3 5 2 (.system [[0],[1,2,3,6,7,5]]) (.forbid 3 5 3 (.system [[0],[1,2,3,6,7,8,5]]) (.forbid 4 5 1 (.system [[0],[1,2,3,4,6,5]]) (.forbid 4 5 2 (.system [[0],[1,2,3,4,6,7,5]]) (.forbid 0 2 0 (.forbid 0 3 4 (.cycle [0,2,3,9,8,7,6]) (certificate_10_part_5)) (.forbid 0 1 4 (.system [[0,6,7,8,9,1],[5]]) (certificate_10_part_6))))))))

noncomputable def certificate_10_part_1 : FiniteCertificate := .forbid 0 4 4 (.system [[0,6,7,8,9,4,5],[1]]) (.forbid 0 5 1 (.system [[0,6,5,4,3,2,1]]) (.forbid 2 4 2 (.system [[0],[1,2,6,7,4,5]]) (.forbid 0 3 1 (.forbid 0 2 0 (.cycle [0,6,3,4,5,1,2]) (.forbid 0 4 0 (.cycle [0,6,3,2,1,5,4]) (.forbid 1 4 0 (.cycle [1,2,3,6,0,5,4]) (.forbid 2 4 0 (.cycle [2,1,5,0,6,3,4]) (certificate_10_part_2))))) (.forbid 0 3 2 (.system [[0,6,7,3,2,1],[5]]) (.forbid 0 3 3 (.system [[0,6,7,8,3,2,1],[5]]) (.forbid 0 5 4 (.system [[0,6,7,8,9,5],[1]]) (.forbid 0 5 5 (.system [[0,6,7,8,9,10,5],[1]]) (certificate_10_part_3))))))))

noncomputable def certificate_10 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1,2,3,4,5]]) (.forbid 0 2 1 (.system [[0,6,2,3,4,5],[1]]) (.forbid 0 2 2 (.system [[0,6,7,2,3,4,5],[1]]) (.forbid 0 2 3 (.system [[0,6,7,8,2,1],[5]]) (.forbid 0 2 4 (.system [[0,6,7,8,9,2,1],[5]]) (.forbid 0 4 1 (.system [[0,6,4,3,2,1],[5]]) (.forbid 0 4 2 (.system [[0,6,7,4,3,2,1],[5]]) (.forbid 0 4 3 (.system [[0,6,7,8,4,5],[1]]) (certificate_10_part_1))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates004
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_100_q : Finset ℕ := ([0,2,5,7] : List ℕ).toFinset
noncomputable def certificate_100_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(0,2),(0,5),(0,7),(2,5),(2,7),(5,7)]

noncomputable def certificate_100_part_0 : FiniteCertificate := .forbid 1 3 3 (.system [[0,1,8,9,10,3,2],[5],[7]]) (.forbid 1 3 4 (.system [[0,1,8,9,10,11,3,2],[5],[7]]) (.forbid 1 3 5 (.system [[0,1,8,9,10,11,12,3,2],[5],[7]]) (.forbid 1 3 6 (.system [[0,1,8,9,10,11,12,13,3,2],[5],[7]]) (.forbid 1 4 1 (.system [[0,1,8,4,3,2],[5],[7]]) (.forbid 1 4 2 (.system [[0,1,8,9,4,3,2],[5],[7]]) (.forbid 1 4 3 (.system [[0,1,8,9,10,4,3,2],[5],[7]]) (.forbid 1 4 4 (.system [[0,1,8,9,10,11,4,3,2],[5],[7]]) (.forbid 1 4 5 (.system [[0,1,8,9,10,11,12,4,3,2],[5],[7]]) (.forbid 1 4 6 (.system [[0,1,8,9,10,11,12,13,4,5],[2],[7]]) (.forbid 3 4 1 (.system [[0,1,2,3,8,4,5],[7]]) (.forbid 3 4 2 (.system [[0],[2,3,8,9,4,5],[7]]) (.forbid 3 4 3 (.system [[0],[2,3,8,9,10,4,5],[7]]) (.forbid 3 4 4 (.system [[0],[2,3,8,9,10,11,4,5],[7]]) (.forbid 3 4 5 (.system [[0],[2,3,8,9,10,11,12,4,5],[7]]) (.forbid 3 4 6 (.system [[0],[2,3,8,9,10,11,12,13,4,5],[7]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,3,4} 5 2) ∅ 11 3), .ball 1 (.succ (.succ (.zero ∅ 2 1) {0,3,4} 5 2) ∅ 11 3), .ball 3 (.succ (.succ (.zero ∅ 2 1) {0,1,4} 5 2) ∅ 11 3), .ball 4 (.succ (.succ (.zero ∅ 2 1) {0,1,3} 5 2) ∅ 11 3)}))))))))))))))))

noncomputable def certificate_100 : FiniteCertificate := .forbid 0 1 1 (.system [[0,8,1,2,3,4,5],[7]]) (.forbid 0 1 2 (.system [[0,8,9,1,2,3,4,5],[7]]) (.forbid 0 1 3 (.system [[0,8,9,10,1,2],[5],[7]]) (.forbid 0 1 4 (.system [[0,8,9,10,11,1,2],[5],[7]]) (.forbid 0 1 5 (.system [[0,8,9,10,11,12,1,2],[5],[7]]) (.forbid 0 1 6 (.system [[0,8,9,10,11,12,13,1,2],[5],[7]]) (.forbid 0 3 1 (.system [[2,1,0,8,3,4,5],[7]]) (.forbid 0 3 2 (.system [[0,8,9,3,2],[5,6,7]]) (.forbid 0 3 3 (.system [[0,8,9,10,3,2],[5],[7]]) (.forbid 0 3 4 (.system [[0,8,9,10,11,3,2],[5],[7]]) (.forbid 0 3 5 (.system [[0,8,9,10,11,12,3,2],[5],[7]]) (.forbid 0 3 6 (.system [[0,8,9,10,11,12,13,3,2],[5],[7]]) (.forbid 0 4 1 (.system [[0,8,4,3,2],[5,6,7]]) (.forbid 0 4 2 (.system [[0,8,9,4,3,2],[5],[7]]) (.forbid 0 4 3 (.system [[0,8,9,10,4,3,2],[5],[7]]) (.forbid 0 4 4 (.system [[0,8,9,10,11,4,3,2],[5],[7]]) (.forbid 0 4 5 (.system [[0,8,9,10,11,12,4,3,2],[5],[7]]) (.forbid 0 4 6 (.system [[0,8,9,10,11,12,13,4,3,2],[5],[7]]) (.forbid 1 3 1 (.system [[0,1,8,3,2],[5,6,7]]) (.forbid 1 3 2 (.system [[0,1,8,9,3,2],[5],[7]]) (certificate_100_part_0))))))))))))))))))))

noncomputable def certificate_101_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(0,2),(0,5),(0,8),(2,5),(2,8),(5,8)]

noncomputable def certificate_101_part_0 : FiniteCertificate := .forbid 1 3 1 (.system [[0,1,9,3,2],[5,6,7,8]]) (.forbid 1 3 2 (.system [[0,1,9,10,3,2],[5,6,7,8]]) (.forbid 1 3 3 (.system [[0,1,9,10,11,3,2],[5],[8]]) (.forbid 1 3 4 (.system [[0,1,9,10,11,12,3,2],[5],[8]]) (.forbid 1 3 5 (.system [[0,1,9,10,11,12,13,3,2],[5],[8]]) (.forbid 1 3 6 (.system [[0,1,9,10,11,12,13,14,3,2],[5],[8]]) (.forbid 1 4 1 (.system [[0,1,9,4,3,2],[5,6,7,8]]) (.forbid 1 4 2 (.system [[0,1,9,10,4,3,2],[5],[8]]) (.forbid 1 4 3 (.system [[0,1,9,10,11,4,3,2],[5],[8]]) (.forbid 1 4 4 (.system [[0,1,9,10,11,12,4,3,2],[5],[8]]) (.forbid 1 4 5 (.system [[0,1,9,10,11,12,13,4,3,2],[5],[8]]) (.forbid 1 4 6 (.system [[0,1,9,10,11,12,13,14,4,5],[2],[8]]) (.forbid 2 3 1 (.system [[0],[2,9,3,4,5,6,7,8]]) (.forbid 3 4 1 (.system [[0],[2,3,9,4,5,6,7,8]]) (.forbid 3 4 2 (.system [[0,1,2,3,9,10,4,5],[8]]) (.forbid 3 4 3 (.system [[0],[2,3,9,10,11,4,5],[8]]) (.forbid 3 4 4 (.system [[0],[2,3,9,10,11,12,4,5],[8]]) (.forbid 3 4 5 (.system [[0],[2,3,9,10,11,12,13,4,5],[8]]) (.forbid 3 4 6 (.system [[0],[2,3,9,10,11,12,13,14,4,5],[8]]) (.forbid 4 5 1 (.system [[0],[2,3,4,9,5,6,7,8]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4,6} 5 2) ∅ 10 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4} 5 2) ∅ 10 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4} 5 2) ∅ 10 3), .ball 4 (.succ (.succ (.zero ∅ 1 1) {0,1,3,5} 5 2) ∅ 10 3)}))))))))))))))))))))

noncomputable def certificate_101 : FiniteCertificate := .forbid 0 1 1 (.system [[0,9,1,2,3,4,5,6,7,8]]) (.forbid 0 1 2 (.system [[0,9,10,1,2,3,4,5],[8]]) (.forbid 0 1 3 (.system [[0,9,10,11,1,2,3,4,5],[8]]) (.forbid 0 1 4 (.system [[0,9,10,11,12,1,2],[5],[8]]) (.forbid 0 1 5 (.system [[0,9,10,11,12,13,1,2],[5],[8]]) (.forbid 0 1 6 (.system [[0,9,10,11,12,13,14,1,2],[5],[8]]) (.forbid 0 3 1 (.system [[0,9,3,4,5,6,7,8],[2]]) (.forbid 0 3 2 (.system [[0,9,10,3,2],[5,6,7,8]]) (.forbid 0 3 3 (.system [[0,9,10,11,3,2],[5,6,7,8]]) (.forbid 0 3 4 (.system [[0,9,10,11,12,3,2],[5],[8]]) (.forbid 0 3 5 (.system [[0,9,10,11,12,13,3,2],[5],[8]]) (.forbid 0 3 6 (.system [[0,9,10,11,12,13,14,3,2],[5],[8]]) (.forbid 0 4 1 (.system [[0,9,4,3,2],[5,6,7,8]]) (.forbid 0 4 2 (.system [[0,9,10,4,3,2],[5,6,7,8]]) (.forbid 0 4 3 (.system [[0,9,10,11,4,3,2],[5],[8]]) (.forbid 0 4 4 (.system [[0,9,10,11,12,4,3,2],[5],[8]]) (.forbid 0 4 5 (.system [[0,9,10,11,12,13,4,3,2],[5],[8]]) (.forbid 0 4 6 (.system [[0,9,10,11,12,13,14,4,3,2],[5],[8]]) (.forbid 0 6 1 (.system [[0,9,6,7,8],[2,3,4,5]]) (.forbid 1 2 1 (.system [[0,1,9,2,3,4,5,6,7,8]]) (certificate_101_part_0))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates032
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_1000_q : Finset ℕ := ([0,2,3,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_1000_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,7),(0,10),(0,12),(2,3),(2,5),(2,7),(2,10),(2,12),(3,5),(3,7),(3,10),(3,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_1000_part_0 : FiniteCertificate := .forbid 3 6 6 (.system [[0],[2],[3,13,14,15,16,17,18,6,5],[7],[10],[12]]) (.forbid 3 8 1 (.system [[0,1,2],[7,6,5,4,3,13,8,9,10],[12]]) (.forbid 4 5 1 (.system [[0,1,2],[3,4,13,5,6,7,8,9,10],[12]]) (.forbid 4 6 1 (.system [[0,1,2],[3,4,13,6,5],[7,8,9,10],[12]]) (.forbid 4 6 2 (.system [[0],[2],[3,4,13,14,6,5],[7,8,9,10],[12]]) (.forbid 4 6 3 (.system [[0,1,2],[3,4,13,14,15,6,5],[7],[10],[12]]) (.forbid 4 6 4 (.system [[0],[2],[3,4,13,14,15,16,6,5],[7],[10],[12]]) (.forbid 4 6 5 (.system [[0],[2],[3,4,13,14,15,16,17,6,5],[7],[10],[12]]) (.forbid 4 6 6 (.system [[0],[2],[3,4,13,14,15,16,17,18,6,5],[7],[10],[12]]) (.forbid 5 6 1 (.system [[0,1,2],[3,4,5,13,6,7,8,9,10],[12]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,3,4,6,8,9} 8 2) ∅ 16 3), .ball 1 (.succ (.succ (.zero ∅ 2 1) {0,2,3,4,5,6} 8 2) ∅ 16 3), .ball 3 (.succ (.succ (.zero ∅ 2 1) {0,1,2,4,6,8} 8 2) ∅ 16 3), .ball 4 (.succ (.succ (.zero ∅ 2 1) {0,1,2,3,5,6} 8 2) ∅ 16 3), .ball 6 (.succ (.succ (.zero ∅ 2 1) {0,1,2,3,4,5} 8 2) ∅ 16 3)}))))))))))

noncomputable def certificate_1000_part_1 : FiniteCertificate := .forbid 1 6 1 (.system [[0,1,13,6,5,4,3],[2],[7,8,9,10],[12]]) (.forbid 1 6 2 (.system [[0,1,13,14,6,5],[2],[3],[7,8,9,10],[12]]) (.forbid 1 6 3 (.system [[0,1,13,14,15,6,5,4,3],[2],[7],[10],[12]]) (.forbid 1 6 4 (.system [[0,1,13,14,15,16,6,5],[2],[3],[7],[10],[12]]) (.forbid 1 6 5 (.system [[0,1,13,14,15,16,17,6,5],[2],[3],[7],[10],[12]]) (.forbid 1 6 6 (.system [[0,1,13,14,15,16,17,18,6,5],[2],[3],[7],[10],[12]]) (.forbid 2 3 1 (.system [[0,1,2,13,3,4,5,6,7,8,9,10,11,12]]) (.forbid 2 4 1 (.system [[0,1,2,13,4,3],[5,6,7,8,9,10],[12]]) (.forbid 2 6 1 (.system [[0,1,2,13,6,5,4,3],[7,8,9,10],[12]]) (.forbid 3 4 1 (.system [[0,1,2],[3,13,4,5,6,7,8,9,10],[12]]) (.forbid 3 4 2 (.system [[0,1,2],[3,13,14,4,5],[7,8,9,10],[12]]) (.forbid 3 4 3 (.system [[0],[2],[3,13,14,15,4,5],[7,8,9,10],[12]]) (.forbid 3 4 4 (.system [[0,1,2],[3,13,14,15,16,4,5],[7],[10],[12]]) (.forbid 3 4 5 (.system [[0],[2],[3,13,14,15,16,17,4,5],[7],[10],[12]]) (.forbid 3 4 6 (.system [[0],[2],[3,13,14,15,16,17,18,4,5],[7],[10],[12]]) (.forbid 3 6 1 (.system [[0,1,2],[3,13,6,5],[7,8,9,10,11,12]]) (.forbid 3 6 2 (.system [[0,1,2],[3,13,14,6,5],[7,8,9,10],[12]]) (.forbid 3 6 3 (.system [[0],[2],[3,13,14,15,6,5],[7,8,9,10],[12]]) (.forbid 3 6 4 (.system [[0,1,2],[3,13,14,15,16,6,5],[7],[10],[12]]) (.forbid 3 6 5 (.system [[0],[2],[3,13,14,15,16,17,6,5],[7],[10],[12]]) (certificate_1000_part_0))))))))))))))))))))

noncomputable def certificate_1000_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[0,13,14,15,6,5],[2],[3],[7,8,9,10],[12]]) (.forbid 0 6 4 (.system [[2,1,0,13,14,15,16,6,5],[3],[7],[10],[12]]) (.forbid 0 6 5 (.system [[0,13,14,15,16,17,6,5],[2],[3],[7],[10],[12]]) (.forbid 0 6 6 (.system [[0,13,14,15,16,17,18,6,5],[2],[3],[7],[10],[12]]) (.forbid 0 8 1 (.system [[2,1,0,13,8,9,10],[3,4,5,6,7],[12]]) (.forbid 0 9 1 (.system [[2,1,0,13,9,8,7,6,5,4,3],[10],[12]]) (.forbid 1 2 1 (.system [[0,1,13,2],[3,4,5,6,7,8,9,10],[12]]) (.forbid 1 3 1 (.system [[0,1,13,3,4,5,6,7,8,9,10],[2],[12]]) (.forbid 1 3 2 (.system [[0,1,13,14,3,4,5],[2],[7,8,9,10],[12]]) (.forbid 1 3 3 (.system [[0,1,13,14,15,3],[2],[5],[7,8,9,10],[12]]) (.forbid 1 3 4 (.system [[0,1,13,14,15,16,3,4,5],[2],[7],[10],[12]]) (.forbid 1 3 5 (.system [[0,1,13,14,15,16,17,3],[2],[5],[7],[10],[12]]) (.forbid 1 3 6 (.system [[0,1,13,14,15,16,17,18,3],[2],[5],[7],[10],[12]]) (.forbid 1 4 1 (.system [[0,1,13,4,3],[2],[5,6,7,8,9,10],[12]]) (.forbid 1 4 2 (.system [[0,1,13,14,4,3],[2],[5],[7,8,9,10],[12]]) (.forbid 1 4 3 (.system [[0,1,13,14,15,4,3],[2],[5,6,7],[10],[12]]) (.forbid 1 4 4 (.system [[0,1,13,14,15,16,4,3],[2],[5],[7],[10],[12]]) (.forbid 1 4 5 (.system [[0,1,13,14,15,16,17,4,3],[2],[5],[7],[10],[12]]) (.forbid 1 4 6 (.system [[0,1,13,14,15,16,17,18,4,3],[2],[5],[7],[10],[12]]) (.forbid 1 5 1 (.system [[0,1,13,5,4,3],[2],[7,8,9,10,11,12]]) (certificate_1000_part_1))))))))))))))))))))

noncomputable def certificate_1000 : FiniteCertificate := .forbid 0 1 1 (.system [[0,13,1,2],[3,4,5,6,7,8,9,10],[12]]) (.forbid 0 1 2 (.system [[0,13,14,1,2],[3,4,5],[7,8,9,10],[12]]) (.forbid 0 1 3 (.system [[0,13,14,15,1,2],[3],[5],[7,8,9,10],[12]]) (.forbid 0 1 4 (.system [[0,13,14,15,16,1,2],[3,4,5],[7],[10],[12]]) (.forbid 0 1 5 (.system [[0,13,14,15,16,17,1,2],[3],[5],[7],[10],[12]]) (.forbid 0 1 6 (.system [[0,13,14,15,16,17,18,1,2],[3],[5],[7],[10],[12]]) (.forbid 0 3 1 (.system [[2,1,0,13,3,4,5,6,7,8,9,10,11,12]]) (.forbid 0 3 2 (.system [[2,1,0,13,14,3,4,5],[7,8,9,10],[12]]) (.forbid 0 3 3 (.system [[2,1,0,13,14,15,3],[5],[7,8,9,10],[12]]) (.forbid 0 3 4 (.system [[0,13,14,15,16,3],[2],[5],[7,8,9,10],[12]]) (.forbid 0 3 5 (.system [[2,1,0,13,14,15,16,17,3],[5],[7],[10],[12]]) (.forbid 0 3 6 (.system [[0,13,14,15,16,17,18,3],[2],[5],[7],[10],[12]]) (.forbid 0 4 1 (.system [[2,1,0,13,4,3],[5,6,7,8,9,10],[12]]) (.forbid 0 4 2 (.system [[2,1,0,13,14,4,3],[5],[7,8,9,10],[12]]) (.forbid 0 4 3 (.system [[0,13,14,15,4,3],[2],[5],[7,8,9,10],[12]]) (.forbid 0 4 4 (.system [[2,1,0,13,14,15,16,4,3],[5],[7],[10],[12]]) (.forbid 0 4 5 (.system [[0,13,14,15,16,17,4,3],[2],[5],[7],[10],[12]]) (.forbid 0 4 6 (.system [[0,13,14,15,16,17,18,4,3],[2],[5],[7],[10],[12]]) (.forbid 0 6 1 (.system [[2,1,0,13,6,5,4,3],[7,8,9,10],[12]]) (.forbid 0 6 2 (.system [[2,1,0,13,14,6,5],[3],[7,8,9,10],[12]]) (certificate_1000_part_2))))))))))))))))))))

noncomputable def certificate_1001_q : Finset ℕ := ([0,2,3,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1001_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,10),(0,13),(2,3),(2,5),(2,7),(2,10),(2,13),(3,5),(3,7),(3,10),(3,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1001_part_0 : FiniteCertificate := .forbid 3 6 4 (.system [[0],[2],[3,14,15,16,17,6,5],[7,8,9,10],[13]]) (.forbid 3 6 5 (.system [[0,1,2],[3,14,15,16,17,18,6,5],[7],[10],[13]]) (.forbid 3 6 6 (.system [[0],[2],[3,14,15,16,17,18,19,6,5],[7],[10],[13]]) (.forbid 3 8 1 (.system [[0,1,2],[5,4,3,14,8,9,10,11,12,13],[7]]) (.forbid 3 9 1 (.system [[0,1,2],[5,4,3,14,9,8,7],[10,11,12,13]]) (.forbid 4 5 1 (.system [[0,1,2],[3,4,14,5],[7,8,9,10,11,12,13]]) (.forbid 4 6 1 (.system [[0],[2],[3,4,14,6,5],[7,8,9,10,11,12,13]]) (.forbid 4 6 2 (.system [[0,1,2],[3,4,14,15,6,5],[7,8,9,10],[13]]) (.forbid 4 6 3 (.system [[0],[2],[3,4,14,15,16,6,5],[7,8,9,10],[13]]) (.forbid 4 6 4 (.system [[0,1,2],[3,4,14,15,16,17,6,5],[7],[10],[13]]) (.forbid 4 6 5 (.system [[0],[2],[3,4,14,15,16,17,18,6,5],[7],[10],[13]]) (.forbid 4 6 6 (.system [[0],[2],[3,4,14,15,16,17,18,19,6,5],[7],[10],[13]]) (.forbid 4 7 1 (.system [[0,1,2],[3,4,14,7,8,9,10,11,12,13],[5]]) (.forbid 5 6 1 (.system [[0,1,2],[3],[5,14,6,7,8,9,10,11,12,13]]) (.forbid 6 7 1 (.system [[0,1,2],[3],[5,6,14,7,8,9,10,11,12,13]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4,6,8,9,11} 8 2) ∅ 15 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4,5,6,7} 8 2) ∅ 15 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4,6,8,9} 8 2) ∅ 15 3), .ball 4 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,5,6,7} 8 2) ∅ 15 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,4,5,7} 8 2) ∅ 15 3)})))))))))))))))

noncomputable def certificate_1001_part_1 : FiniteCertificate := .forbid 1 5 1 (.system [[0,1,14,5,4,3],[2],[7,8,9,10,11,12,13]]) (.forbid 1 6 1 (.system [[0,1,14,6,5],[2],[3],[7,8,9,10,11,12,13]]) (.forbid 1 6 2 (.system [[0,1,14,15,6,5,4,3],[2],[7,8,9,10],[13]]) (.forbid 1 6 3 (.system [[0,1,14,15,16,6,5],[2],[3],[7,8,9,10],[13]]) (.forbid 1 6 4 (.system [[0,1,14,15,16,17,6,5,4,3],[2],[7],[10],[13]]) (.forbid 1 6 5 (.system [[0,1,14,15,16,17,18,6,5],[2],[3],[7],[10],[13]]) (.forbid 1 6 6 (.system [[0,1,14,15,16,17,18,19,6,5],[2],[3],[7],[10],[13]]) (.forbid 1 7 1 (.system [[0,1,14,7,8,9,10,11,12,13],[2],[3,4,5]]) (.forbid 2 3 1 (.system [[0,1,2,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 2 4 1 (.system [[0,1,2,14,4,3],[5],[7,8,9,10,11,12,13]]) (.forbid 2 6 1 (.system [[0,1,2,14,6,5],[3],[7,8,9,10,11,12,13]]) (.forbid 3 4 1 (.system [[0,1,2],[3,14,4,5],[7,8,9,10,11,12,13]]) (.forbid 3 4 2 (.system [[0],[2],[3,14,15,4,5],[7,8,9,10,11,12,13]]) (.forbid 3 4 3 (.system [[0,1,2],[3,14,15,16,4,5],[7,8,9,10],[13]]) (.forbid 3 4 4 (.system [[0],[2],[3,14,15,16,17,4,5],[7,8,9,10],[13]]) (.forbid 3 4 5 (.system [[0,1,2],[3,14,15,16,17,18,4,5],[7],[10],[13]]) (.forbid 3 4 6 (.system [[0],[2],[3,14,15,16,17,18,19,4,5],[7],[10],[13]]) (.forbid 3 6 1 (.system [[0,1,2],[3,14,6,5],[7,8,9,10,11,12,13]]) (.forbid 3 6 2 (.system [[0],[2],[3,14,15,6,5],[7,8,9,10,11,12,13]]) (.forbid 3 6 3 (.system [[0,1,2],[3,14,15,16,6,5],[7,8,9,10],[13]]) (certificate_1001_part_0))))))))))))))))))))

noncomputable def certificate_1001_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,14,15,16,6,5],[3],[7,8,9,10],[13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5],[2],[3],[7,8,9,10],[13]]) (.forbid 0 6 5 (.system [[2,1,0,14,15,16,17,18,6,5],[3],[7],[10],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[2],[3],[7],[10],[13]]) (.forbid 0 8 1 (.system [[2,1,0,14,8,9,10,11,12,13],[3,4,5],[7]]) (.forbid 0 9 1 (.system [[2,1,0,14,9,8,7],[3,4,5],[10,11,12,13]]) (.forbid 0 11 1 (.system [[2,1,0,14,11,12,13],[3,4,5],[7,8,9,10]]) (.forbid 1 2 1 (.system [[0,1,14,2],[3,4,5],[7,8,9,10,11,12,13]]) (.forbid 1 3 1 (.system [[0,1,14,3,4,5],[2],[7,8,9,10,11,12,13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3],[2],[5],[7,8,9,10,11,12,13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3,4,5],[2],[7,8,9,10],[13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3],[2],[5],[7,8,9,10],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3,4,5],[2],[7],[10],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3],[2],[5],[7],[10],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4,3],[2],[5],[7,8,9,10,11,12,13]]) (.forbid 1 4 2 (.system [[0,1,14,15,4,3],[2],[5,6,7,8,9,10],[13]]) (.forbid 1 4 3 (.system [[0,1,14,15,16,4,3],[2],[5],[7,8,9,10],[13]]) (.forbid 1 4 4 (.system [[0,1,14,15,16,17,4,3],[2],[5,6,7],[10],[13]]) (.forbid 1 4 5 (.system [[0,1,14,15,16,17,18,4,3],[2],[5],[7],[10],[13]]) (.forbid 1 4 6 (.system [[0,1,14,15,16,17,18,19,4,3],[2],[5],[7],[10],[13]]) (certificate_1001_part_1))))))))))))))))))))

noncomputable def certificate_1001 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2],[3,4,5],[7,8,9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2],[3],[5],[7,8,9,10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2],[3,4,5],[7,8,9,10],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[3],[5],[7,8,9,10],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2],[3,4,5],[7],[10],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[3],[5],[7],[10],[13]]) (.forbid 0 3 1 (.system [[2,1,0,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[2,1,0,14,15,3],[5],[7,8,9,10,11,12,13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3],[2],[5],[7,8,9,10,11,12,13]]) (.forbid 0 3 4 (.system [[2,1,0,14,15,16,17,3],[5],[7,8,9,10],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3],[2],[5],[7,8,9,10],[13]]) (.forbid 0 3 6 (.system [[2,1,0,14,15,16,17,18,19,3],[5],[7],[10],[13]]) (.forbid 0 4 1 (.system [[2,1,0,14,4,3],[5],[7,8,9,10,11,12,13]]) (.forbid 0 4 2 (.system [[0,14,15,4,3],[2],[5],[7,8,9,10,11,12,13]]) (.forbid 0 4 3 (.system [[2,1,0,14,15,16,4,3],[5],[7,8,9,10],[13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[2],[5],[7,8,9,10],[13]]) (.forbid 0 4 5 (.system [[2,1,0,14,15,16,17,18,4,3],[5],[7],[10],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[2],[5],[7],[10],[13]]) (.forbid 0 6 1 (.system [[2,1,0,14,6,5],[3],[7,8,9,10,11,12,13]]) (.forbid 0 6 2 (.system [[0,14,15,6,5],[2],[3],[7,8,9,10,11,12,13]]) (certificate_1001_part_2))))))))))))))))))))

noncomputable def certificate_1002_q : Finset ℕ := ([0,2,3,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_1002_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,7),(0,11),(0,13),(2,3),(2,5),(2,7),(2,11),(2,13),(3,5),(3,7),(3,11),(3,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_1002_part_0 : FiniteCertificate := .forbid 3 6 4 (.system [[0],[2],[3,14,15,16,17,6,5],[7,8,9,10,11],[13]]) (.forbid 3 6 5 (.system [[0,1,2],[3,14,15,16,17,18,6,5],[7],[11],[13]]) (.forbid 3 6 6 (.system [[0],[2],[3,14,15,16,17,18,19,6,5],[7],[11],[13]]) (.forbid 3 8 1 (.system [[0,1,2],[7,6,5,4,3,14,8,9,10,11],[13]]) (.forbid 3 10 1 (.system [[0,1,2],[5,4,3,14,10,9,8,7],[11,12,13]]) (.forbid 4 5 1 (.system [[0,1,2],[3,4,14,5,6,7,8,9,10,11],[13]]) (.forbid 4 6 1 (.system [[0,1,2],[3,4,14,6,5],[7,8,9,10,11],[13]]) (.forbid 4 6 2 (.system [[0],[2],[3,4,14,15,6,5],[7,8,9,10,11],[13]]) (.forbid 4 6 3 (.system [[0],[2],[3,4,14,15,16,6,5],[7,8,9,10,11],[13]]) (.forbid 4 6 4 (.system [[0,1,2],[3,4,14,15,16,17,6,5],[7],[11],[13]]) (.forbid 4 6 5 (.system [[0],[2],[3,4,14,15,16,17,18,6,5],[7],[11],[13]]) (.forbid 4 6 6 (.system [[0],[2],[3,4,14,15,16,17,18,19,6,5],[7],[11],[13]]) (.forbid 4 7 1 (.system [[0,1,2],[3,4,14,7,8,9,10,11,12,13],[5]]) (.forbid 5 6 1 (.system [[0,1,2],[3,4,5,14,6,7,8,9,10,11],[13]]) (.forbid 6 7 1 (.system [[0,1,2],[3,4,5,6,14,7,8,9,10,11],[13]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4,6,8,10,12} 8 2) ∅ 15 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4,5,6,7} 8 2) ∅ 15 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4,6,8,10} 8 2) ∅ 15 3), .ball 4 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,5,6,7} 8 2) ∅ 15 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,4,5,7} 8 2) ∅ 15 3)})))))))))))))))

noncomputable def certificate_1002_part_1 : FiniteCertificate := .forbid 1 5 1 (.system [[0,1,14,5,4,3],[2],[7,8,9,10,11,12,13]]) (.forbid 1 6 1 (.system [[0,1,14,6,5,4,3],[2],[7,8,9,10,11],[13]]) (.forbid 1 6 2 (.system [[0,1,14,15,6,5],[2],[3],[7,8,9,10,11],[13]]) (.forbid 1 6 3 (.system [[0,1,14,15,16,6,5],[2],[3],[7,8,9,10,11],[13]]) (.forbid 1 6 4 (.system [[0,1,14,15,16,17,6,5,4,3],[2],[7],[11],[13]]) (.forbid 1 6 5 (.system [[0,1,14,15,16,17,18,6,5],[2],[3],[7],[11],[13]]) (.forbid 1 6 6 (.system [[0,1,14,15,16,17,18,19,6,5],[2],[3],[7],[11],[13]]) (.forbid 1 7 1 (.system [[0,1,14,7,8,9,10,11,12,13],[2],[3,4,5]]) (.forbid 2 3 1 (.system [[0,1,2,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 2 4 1 (.system [[0,1,2,14,4,3],[5,6,7,8,9,10,11],[13]]) (.forbid 2 6 1 (.system [[0,1,2,14,6,5,4,3],[7,8,9,10,11],[13]]) (.forbid 3 4 1 (.system [[0,1,2],[3,14,4,5,6,7,8,9,10,11],[13]]) (.forbid 3 4 2 (.system [[0,1,2],[3,14,15,4,5],[7,8,9,10,11],[13]]) (.forbid 3 4 3 (.system [[0],[2],[3,14,15,16,4,5],[7,8,9,10,11],[13]]) (.forbid 3 4 4 (.system [[0],[2],[3,14,15,16,17,4,5],[7,8,9,10,11],[13]]) (.forbid 3 4 5 (.system [[0,1,2],[3,14,15,16,17,18,4,5],[7],[11],[13]]) (.forbid 3 4 6 (.system [[0],[2],[3,14,15,16,17,18,19,4,5],[7],[11],[13]]) (.forbid 3 6 1 (.system [[0,1,2],[3,14,6,5],[7,8,9,10,11,12,13]]) (.forbid 3 6 2 (.system [[0,1,2],[3,14,15,6,5],[7,8,9,10,11],[13]]) (.forbid 3 6 3 (.system [[0],[2],[3,14,15,16,6,5],[7,8,9,10,11],[13]]) (certificate_1002_part_0))))))))))))))))))))

noncomputable def certificate_1002_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[0,14,15,16,6,5],[2],[3],[7,8,9,10,11],[13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5],[2],[3],[7,8,9,10,11],[13]]) (.forbid 0 6 5 (.system [[2,1,0,14,15,16,17,18,6,5],[3],[7],[11],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[2],[3],[7],[11],[13]]) (.forbid 0 8 1 (.system [[2,1,0,14,8,9,10,11],[3,4,5,6,7],[13]]) (.forbid 0 10 1 (.system [[2,1,0,14,10,9,8,7,6,5,4,3],[11],[13]]) (.forbid 0 12 1 (.system [[2,1,0,14,12,11,10,9,8,7],[3,4,5],[13]]) (.forbid 1 2 1 (.system [[0,1,14,2],[3,4,5,6,7,8,9,10,11],[13]]) (.forbid 1 3 1 (.system [[0,1,14,3,4,5,6,7,8,9,10,11],[2],[13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3,4,5],[2],[7,8,9,10,11],[13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3],[2],[5],[7,8,9,10,11],[13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3],[2],[5],[7,8,9,10,11],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3,4,5],[2],[7],[11],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3],[2],[5],[7],[11],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4,3],[2],[5,6,7,8,9,10,11],[13]]) (.forbid 1 4 2 (.system [[0,1,14,15,4,3],[2],[5],[7,8,9,10,11],[13]]) (.forbid 1 4 3 (.system [[0,1,14,15,16,4,3],[2],[5],[7,8,9,10,11],[13]]) (.forbid 1 4 4 (.system [[0,1,14,15,16,17,4,3],[2],[5,6,7],[11],[13]]) (.forbid 1 4 5 (.system [[0,1,14,15,16,17,18,4,3],[2],[5],[7],[11],[13]]) (.forbid 1 4 6 (.system [[0,1,14,15,16,17,18,19,4,3],[2],[5],[7],[11],[13]]) (certificate_1002_part_1))))))))))))))))))))

noncomputable def certificate_1002 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2],[3,4,5,6,7,8,9,10,11],[13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2],[3,4,5],[7,8,9,10,11],[13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2],[3],[5],[7,8,9,10,11],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[3],[5],[7,8,9,10,11],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2],[3,4,5],[7],[11],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[3],[5],[7],[11],[13]]) (.forbid 0 3 1 (.system [[2,1,0,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[2,1,0,14,15,3,4,5],[7,8,9,10,11],[13]]) (.forbid 0 3 3 (.system [[2,1,0,14,15,16,3],[5],[7,8,9,10,11],[13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3],[2],[5],[7,8,9,10,11],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3],[2],[5],[7,8,9,10,11],[13]]) (.forbid 0 3 6 (.system [[2,1,0,14,15,16,17,18,19,3],[5],[7],[11],[13]]) (.forbid 0 4 1 (.system [[2,1,0,14,4,3],[5,6,7,8,9,10,11],[13]]) (.forbid 0 4 2 (.system [[2,1,0,14,15,4,3],[5],[7,8,9,10,11],[13]]) (.forbid 0 4 3 (.system [[0,14,15,16,4,3],[2],[5],[7,8,9,10,11],[13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[2],[5],[7,8,9,10,11],[13]]) (.forbid 0 4 5 (.system [[2,1,0,14,15,16,17,18,4,3],[5],[7],[11],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[2],[5],[7],[11],[13]]) (.forbid 0 6 1 (.system [[2,1,0,14,6,5,4,3],[7,8,9,10,11],[13]]) (.forbid 0 6 2 (.system [[2,1,0,14,15,6,5],[3],[7,8,9,10,11],[13]]) (certificate_1002_part_2))))))))))))))))))))

noncomputable def certificate_1003_q : Finset ℕ := ([0,2,3,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1003_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,3),(0,5),(0,8),(0,9),(0,12),(2,3),(2,5),(2,8),(2,9),(2,12),(3,5),(3,8),(3,9),(3,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1003_part_0 : FiniteCertificate := .forbid 3 6 6 (.system [[0],[2],[3,13,14,15,16,17,18,6,5],[8],[9],[12]]) (.forbid 3 7 1 (.system [[0,1,2],[3,13,7,6,5],[8],[9,10,11,12]]) (.forbid 4 5 1 (.system [[0],[2],[3,4,13,5,6,7,8],[9,10,11,12]]) (.forbid 4 6 1 (.system [[0,1,2],[3,4,13,6,5],[8],[9,10,11,12]]) (.forbid 4 6 2 (.system [[0],[2],[3,4,13,14,6,5],[8],[9,10,11,12]]) (.forbid 4 6 3 (.system [[0,1,2],[3,4,13,14,15,6,5],[8],[9],[12]]) (.forbid 4 6 4 (.system [[0],[2],[3,4,13,14,15,16,6,5],[8],[9],[12]]) (.forbid 4 6 5 (.system [[0],[2],[3,4,13,14,15,16,17,6,5],[8],[9],[12]]) (.forbid 4 6 6 (.system [[0],[2],[3,4,13,14,15,16,17,18,6,5],[8],[9],[12]]) (.forbid 5 6 1 (.system [[0,1,2],[3],[5,13,6,7,8],[9,10,11,12]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,3,4,6,7,8} 8 2) ∅ 16 3), .ball 1 (.succ (.succ (.zero ∅ 2 1) {0,2,3,4,5,6} 8 2) ∅ 16 3), .ball 3 (.succ (.succ (.zero ∅ 2 1) {0,1,2,4,6,7} 8 2) ∅ 16 3), .ball 4 (.succ (.succ (.zero ∅ 2 1) {0,1,2,3,5,6} 8 2) ∅ 16 3), .ball 6 (.succ (.succ (.zero ∅ 2 1) {0,1,2,3,4,5} 8 2) ∅ 16 3)}))))))))))

noncomputable def certificate_1003_part_1 : FiniteCertificate := .forbid 1 6 1 (.system [[0,1,13,6,5,4,3],[2],[8],[9,10,11,12]]) (.forbid 1 6 2 (.system [[0,1,13,14,6,5],[2],[3],[8],[9,10,11,12]]) (.forbid 1 6 3 (.system [[0,1,13,14,15,6,5,4,3],[2],[8],[9],[12]]) (.forbid 1 6 4 (.system [[0,1,13,14,15,16,6,5],[2],[3],[8],[9],[12]]) (.forbid 1 6 5 (.system [[0,1,13,14,15,16,17,6,5],[2],[3],[8],[9],[12]]) (.forbid 1 6 6 (.system [[0,1,13,14,15,16,17,18,6,5],[2],[3],[8],[9],[12]]) (.forbid 2 3 1 (.system [[0,1,2,13,3,4,5,6,7,8],[9,10,11,12]]) (.forbid 2 4 1 (.system [[0],[2,13,4,3],[5,6,7,8],[9,10,11,12]]) (.forbid 2 6 1 (.system [[0,1,2,13,6,7,8],[3],[5],[9,10,11,12]]) (.forbid 3 4 1 (.system [[0],[2],[3,13,4,5,6,7,8],[9,10,11,12]]) (.forbid 3 4 2 (.system [[0,1,2],[3,13,14,4,5,6,7,8],[9],[12]]) (.forbid 3 4 3 (.system [[0],[2],[3,13,14,15,4,5,6,7,8],[9],[12]]) (.forbid 3 4 4 (.system [[0,1,2],[3,13,14,15,16,4,5],[8],[9],[12]]) (.forbid 3 4 5 (.system [[0],[2],[3,13,14,15,16,17,4,5],[8],[9],[12]]) (.forbid 3 4 6 (.system [[0],[2],[3,13,14,15,16,17,18,4,5],[8],[9],[12]]) (.forbid 3 6 1 (.system [[0,1,2],[3,13,6,7,8],[5],[9,10,11,12]]) (.forbid 3 6 2 (.system [[0,1,2],[3,13,14,6,5],[8],[9,10,11,12]]) (.forbid 3 6 3 (.system [[0],[2],[3,13,14,15,6,5],[8],[9,10,11,12]]) (.forbid 3 6 4 (.system [[0,1,2],[3,13,14,15,16,6,5],[8],[9],[12]]) (.forbid 3 6 5 (.system [[0],[2],[3,13,14,15,16,17,6,5],[8],[9],[12]]) (certificate_1003_part_0))))))))))))))))))))

noncomputable def certificate_1003_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[0,13,14,15,6,5],[2],[3],[8],[9,10,11,12]]) (.forbid 0 6 4 (.system [[2,1,0,13,14,15,16,6,5],[3],[8],[9],[12]]) (.forbid 0 6 5 (.system [[0,13,14,15,16,17,6,5],[2],[3],[8],[9],[12]]) (.forbid 0 6 6 (.system [[0,13,14,15,16,17,18,6,5],[2],[3],[8],[9],[12]]) (.forbid 0 7 1 (.system [[2,1,0,13,7,6,5],[3],[8],[9,10,11,12]]) (.forbid 0 8 1 (.system [[2,1,0,13,8,7,6,5,4,3],[9,10,11,12]]) (.forbid 1 2 1 (.system [[0,1,13,2],[3],[5,6,7,8],[9,10,11,12]]) (.forbid 1 3 1 (.system [[0,1,13,3],[2],[5,6,7,8],[9,10,11,12]]) (.forbid 1 3 2 (.system [[0,1,13,14,3,4,5,6,7,8],[2],[9],[12]]) (.forbid 1 3 3 (.system [[0,1,13,14,15,3],[2],[5,6,7,8],[9],[12]]) (.forbid 1 3 4 (.system [[0,1,13,14,15,16,3,4,5],[2],[8],[9],[12]]) (.forbid 1 3 5 (.system [[0,1,13,14,15,16,17,3],[2],[5],[8],[9],[12]]) (.forbid 1 3 6 (.system [[0,1,13,14,15,16,17,18,3],[2],[5],[8],[9],[12]]) (.forbid 1 4 1 (.system [[0,1,13,4,3],[2],[5,6,7,8],[9,10,11,12]]) (.forbid 1 4 2 (.system [[0,1,13,14,4,3],[2],[5,6,7,8],[9],[12]]) (.forbid 1 4 3 (.system [[0,1,13,14,15,4,3],[2],[5,6,7,8],[9],[12]]) (.forbid 1 4 4 (.system [[0,1,13,14,15,16,4,3],[2],[5],[8],[9],[12]]) (.forbid 1 4 5 (.system [[0,1,13,14,15,16,17,4,3],[2],[5],[8],[9],[12]]) (.forbid 1 4 6 (.system [[0,1,13,14,15,16,17,18,4,3],[2],[5],[8],[9],[12]]) (.forbid 1 5 1 (.system [[0,1,13,5,6,7,8],[2],[3],[9,10,11,12]]) (certificate_1003_part_1))))))))))))))))))))

noncomputable def certificate_1003 : FiniteCertificate := .forbid 0 1 1 (.system [[0,13,1,2],[3],[5,6,7,8],[9,10,11,12]]) (.forbid 0 1 2 (.system [[0,13,14,1,2],[3,4,5,6,7,8],[9],[12]]) (.forbid 0 1 3 (.system [[0,13,14,15,1,2],[3],[5,6,7,8],[9],[12]]) (.forbid 0 1 4 (.system [[0,13,14,15,16,1,2],[3,4,5],[8],[9],[12]]) (.forbid 0 1 5 (.system [[0,13,14,15,16,17,1,2],[3],[5],[8],[9],[12]]) (.forbid 0 1 6 (.system [[0,13,14,15,16,17,18,1,2],[3],[5],[8],[9],[12]]) (.forbid 0 3 1 (.system [[2,1,0,13,3,4,5,6,7,8],[9,10,11,12]]) (.forbid 0 3 2 (.system [[0,13,14,3],[2],[5,6,7,8],[9,10,11,12]]) (.forbid 0 3 3 (.system [[2,1,0,13,14,15,3],[5,6,7,8],[9],[12]]) (.forbid 0 3 4 (.system [[0,13,14,15,16,3],[2],[5,6,7,8],[9],[12]]) (.forbid 0 3 5 (.system [[2,1,0,13,14,15,16,17,3],[5],[8],[9],[12]]) (.forbid 0 3 6 (.system [[0,13,14,15,16,17,18,3],[2],[5],[8],[9],[12]]) (.forbid 0 4 1 (.system [[0,13,4,3],[2],[5,6,7,8],[9,10,11,12]]) (.forbid 0 4 2 (.system [[2,1,0,13,14,4,3],[5,6,7,8],[9],[12]]) (.forbid 0 4 3 (.system [[0,13,14,15,4,3],[2],[5,6,7,8],[9],[12]]) (.forbid 0 4 4 (.system [[2,1,0,13,14,15,16,4,3],[5],[8],[9],[12]]) (.forbid 0 4 5 (.system [[0,13,14,15,16,17,4,3],[2],[5],[8],[9],[12]]) (.forbid 0 4 6 (.system [[0,13,14,15,16,17,18,4,3],[2],[5],[8],[9],[12]]) (.forbid 0 6 1 (.system [[2,1,0,13,6,7,8],[3],[5],[9,10,11,12]]) (.forbid 0 6 2 (.system [[2,1,0,13,14,6,5],[3],[8],[9,10,11,12]]) (certificate_1003_part_2))))))))))))))))))))

noncomputable def certificate_1004_q : Finset ℕ := ([0,2,3,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1004_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,8),(0,9),(0,13),(2,3),(2,5),(2,8),(2,9),(2,13),(3,5),(3,8),(3,9),(3,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1004_part_0 : FiniteCertificate := .forbid 3 6 4 (.system [[0],[2],[3,14,15,16,17,6,5],[8],[9,10,11,12,13]]) (.forbid 3 6 5 (.system [[0,1,2],[3,14,15,16,17,18,6,5],[8],[9],[13]]) (.forbid 3 6 6 (.system [[0],[2],[3,14,15,16,17,18,19,6,5],[8],[9],[13]]) (.forbid 3 7 1 (.system [[0,1,2],[3,14,7,6,5],[8],[9,10,11,12,13]]) (.forbid 3 9 1 (.system [[0,1,2],[8,7,6,5,4,3,14,9,10,11,12,13]]) (.forbid 4 5 1 (.system [[0],[2],[3,4,14,5,6,7,8],[9,10,11,12,13]]) (.forbid 4 6 1 (.system [[0,1,2],[3,4,14,6,5],[8],[9,10,11,12,13]]) (.forbid 4 6 2 (.system [[0],[2],[3,4,14,15,6,5],[8],[9,10,11,12,13]]) (.forbid 4 6 3 (.system [[0],[2],[3,4,14,15,16,6,5],[8],[9,10,11,12,13]]) (.forbid 4 6 4 (.system [[0,1,2],[3,4,14,15,16,17,6,5],[8],[9],[13]]) (.forbid 4 6 5 (.system [[0],[2],[3,4,14,15,16,17,18,6,5],[8],[9],[13]]) (.forbid 4 6 6 (.system [[0],[2],[3,4,14,15,16,17,18,19,6,5],[8],[9],[13]]) (.forbid 4 7 1 (.system [[0],[2],[3,4,14,7,6,5],[8],[9,10,11,12,13]]) (.forbid 5 6 1 (.system [[0,1,2],[3],[5,14,6,7,8],[9,10,11,12,13]]) (.forbid 6 7 1 (.system [[0,1,2],[3],[5,6,14,7,8],[9,10,11,12,13]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4,6,7,8,9} 8 2) ∅ 15 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4,5,6,7} 8 2) ∅ 15 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4,6,7,9} 8 2) ∅ 15 3), .ball 4 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,5,6,7} 8 2) ∅ 15 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,4,5,7} 8 2) ∅ 15 3)})))))))))))))))

noncomputable def certificate_1004_part_1 : FiniteCertificate := .forbid 1 5 1 (.system [[0,1,14,5,6,7,8],[2],[3],[9,10,11,12,13]]) (.forbid 1 6 1 (.system [[0,1,14,6,5,4,3],[2],[8],[9,10,11,12,13]]) (.forbid 1 6 2 (.system [[0,1,14,15,6,5],[2],[3],[8],[9,10,11,12,13]]) (.forbid 1 6 3 (.system [[0,1,14,15,16,6,5],[2],[3],[8],[9,10,11,12,13]]) (.forbid 1 6 4 (.system [[0,1,14,15,16,17,6,5,4,3],[2],[8],[9],[13]]) (.forbid 1 6 5 (.system [[0,1,14,15,16,17,18,6,5],[2],[3],[8],[9],[13]]) (.forbid 1 6 6 (.system [[0,1,14,15,16,17,18,19,6,5],[2],[3],[8],[9],[13]]) (.forbid 1 7 1 (.system [[0,1,14,7,6,5],[2],[3],[8],[9,10,11,12,13]]) (.forbid 2 3 1 (.system [[0,1,2,14,3,4,5,6,7,8],[9,10,11,12,13]]) (.forbid 2 4 1 (.system [[0],[2,14,4,3],[5,6,7,8],[9,10,11,12,13]]) (.forbid 2 6 1 (.system [[0,1,2,14,6,7,8],[3],[5],[9,10,11,12,13]]) (.forbid 3 4 1 (.system [[0],[2],[3,14,4,5,6,7,8],[9,10,11,12,13]]) (.forbid 3 4 2 (.system [[0,1,2],[3,14,15,4,5],[8],[9,10,11,12,13]]) (.forbid 3 4 3 (.system [[0],[2],[3,14,15,16,4,5],[8],[9,10,11,12,13]]) (.forbid 3 4 4 (.system [[0],[2],[3,14,15,16,17,4,5,6,7,8],[9],[13]]) (.forbid 3 4 5 (.system [[0,1,2],[3,14,15,16,17,18,4,5],[8],[9],[13]]) (.forbid 3 4 6 (.system [[0],[2],[3,14,15,16,17,18,19,4,5],[8],[9],[13]]) (.forbid 3 6 1 (.system [[0,1,2],[3,14,6,7,8],[5],[9,10,11,12,13]]) (.forbid 3 6 2 (.system [[0,1,2],[3,14,15,6,5],[8],[9,10,11,12,13]]) (.forbid 3 6 3 (.system [[0],[2],[3,14,15,16,6,5],[8],[9,10,11,12,13]]) (certificate_1004_part_0))))))))))))))))))))

noncomputable def certificate_1004_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[0,14,15,16,6,5],[2],[3],[8],[9,10,11,12,13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5],[2],[3],[8],[9,10,11,12,13]]) (.forbid 0 6 5 (.system [[2,1,0,14,15,16,17,18,6,5],[3],[8],[9],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[2],[3],[8],[9],[13]]) (.forbid 0 7 1 (.system [[2,1,0,14,7,6,5],[3],[8],[9,10,11,12,13]]) (.forbid 0 8 1 (.system [[2,1,0,14,8,7,6,5,4,3],[9,10,11,12,13]]) (.forbid 0 9 1 (.system [[2,1,0,14,9,10,11,12,13],[3,4,5,6,7,8]]) (.forbid 1 2 1 (.system [[0,1,14,2],[3],[5,6,7,8],[9,10,11,12,13]]) (.forbid 1 3 1 (.system [[0,1,14,3],[2],[5,6,7,8],[9,10,11,12,13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3,4,5],[2],[8],[9,10,11,12,13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3],[2],[5],[8],[9,10,11,12,13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3],[2],[5,6,7,8],[9],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3,4,5],[2],[8],[9],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3],[2],[5],[8],[9],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4,3],[2],[5,6,7,8],[9,10,11,12,13]]) (.forbid 1 4 2 (.system [[0,1,14,15,4,3],[2],[5],[8],[9,10,11,12,13]]) (.forbid 1 4 3 (.system [[0,1,14,15,16,4,3],[2],[5,6,7,8],[9],[13]]) (.forbid 1 4 4 (.system [[0,1,14,15,16,17,4,3],[2],[5,6,7,8],[9],[13]]) (.forbid 1 4 5 (.system [[0,1,14,15,16,17,18,4,3],[2],[5],[8],[9],[13]]) (.forbid 1 4 6 (.system [[0,1,14,15,16,17,18,19,4,3],[2],[5],[8],[9],[13]]) (certificate_1004_part_1))))))))))))))))))))

noncomputable def certificate_1004 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2],[3],[5,6,7,8],[9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2],[3,4,5],[8],[9,10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2],[3],[5],[8],[9,10,11,12,13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[3],[5,6,7,8],[9],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2],[3,4,5],[8],[9],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[3],[5],[8],[9],[13]]) (.forbid 0 3 1 (.system [[2,1,0,14,3,4,5,6,7,8],[9,10,11,12,13]]) (.forbid 0 3 2 (.system [[0,14,15,3],[2],[5,6,7,8],[9,10,11,12,13]]) (.forbid 0 3 3 (.system [[2,1,0,14,15,16,3],[5],[8],[9,10,11,12,13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3],[2],[5],[8],[9,10,11,12,13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3],[2],[5,6,7,8],[9],[13]]) (.forbid 0 3 6 (.system [[2,1,0,14,15,16,17,18,19,3],[5],[8],[9],[13]]) (.forbid 0 4 1 (.system [[0,14,4,3],[2],[5,6,7,8],[9,10,11,12,13]]) (.forbid 0 4 2 (.system [[2,1,0,14,15,4,3],[5],[8],[9,10,11,12,13]]) (.forbid 0 4 3 (.system [[0,14,15,16,4,3],[2],[5],[8],[9,10,11,12,13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[2],[5,6,7,8],[9],[13]]) (.forbid 0 4 5 (.system [[2,1,0,14,15,16,17,18,4,3],[5],[8],[9],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[2],[5],[8],[9],[13]]) (.forbid 0 6 1 (.system [[2,1,0,14,6,7,8],[3],[5],[9,10,11,12,13]]) (.forbid 0 6 2 (.system [[2,1,0,14,15,6,5],[3],[8],[9,10,11,12,13]]) (certificate_1004_part_2))))))))))))))))))))

noncomputable def certificate_1005_q : Finset ℕ := ([0,2,3,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1005_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,8),(0,10),(0,13),(2,3),(2,5),(2,8),(2,10),(2,13),(3,5),(3,8),(3,10),(3,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1005_part_0 : FiniteCertificate := .forbid 3 6 4 (.system [[0],[2],[3,14,15,16,17,6,5],[8],[10,11,12,13]]) (.forbid 3 6 5 (.system [[0,1,2],[3,14,15,16,17,18,6,5],[8],[10],[13]]) (.forbid 3 6 6 (.system [[0],[2],[3,14,15,16,17,18,19,6,5],[8],[10],[13]]) (.forbid 3 7 1 (.system [[0,1,2],[3,14,7,6,5],[8,9,10,11,12,13]]) (.forbid 3 9 1 (.system [[0,1,2],[3,14,9,8,7,6,5],[10,11,12,13]]) (.forbid 4 5 1 (.system [[0,1,2],[3,4,14,5,6,7,8],[10,11,12,13]]) (.forbid 4 6 1 (.system [[0,1,2],[3,4,14,6,5],[8,9,10,11,12,13]]) (.forbid 4 6 2 (.system [[0,1,2],[3,4,14,15,6,5],[8],[10,11,12,13]]) (.forbid 4 6 3 (.system [[0],[2],[3,4,14,15,16,6,5],[8],[10,11,12,13]]) (.forbid 4 6 4 (.system [[0,1,2],[3,4,14,15,16,17,6,5],[8],[10],[13]]) (.forbid 4 6 5 (.system [[0],[2],[3,4,14,15,16,17,18,6,5],[8],[10],[13]]) (.forbid 4 6 6 (.system [[0],[2],[3,4,14,15,16,17,18,19,6,5],[8],[10],[13]]) (.forbid 4 7 1 (.system [[0,1,2],[3,4,14,7,6,5],[8],[10,11,12,13]]) (.forbid 5 6 1 (.system [[0,1,2],[3,4,5,14,6,7,8],[10,11,12,13]]) (.forbid 6 7 1 (.system [[0,1,2],[3,4,5,6,14,7,8],[10,11,12,13]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4,6,7,9,11} 8 2) ∅ 15 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4,5,6,7} 8 2) ∅ 15 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4,6,7,9} 8 2) ∅ 15 3), .ball 4 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,5,6,7} 8 2) ∅ 15 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,4,5,7} 8 2) ∅ 15 3)})))))))))))))))

noncomputable def certificate_1005_part_1 : FiniteCertificate := .forbid 1 5 1 (.system [[0,1,14,5,6,7,8,9,10,11,12,13],[2],[3]]) (.forbid 1 6 1 (.system [[0,1,14,6,5,4,3],[2],[8,9,10,11,12,13]]) (.forbid 1 6 2 (.system [[0,1,14,15,6,5,4,3],[2],[8],[10,11,12,13]]) (.forbid 1 6 3 (.system [[0,1,14,15,16,6,5],[2],[3],[8],[10,11,12,13]]) (.forbid 1 6 4 (.system [[0,1,14,15,16,17,6,5,4,3],[2],[8],[10],[13]]) (.forbid 1 6 5 (.system [[0,1,14,15,16,17,18,6,5],[2],[3],[8],[10],[13]]) (.forbid 1 6 6 (.system [[0,1,14,15,16,17,18,19,6,5],[2],[3],[8],[10],[13]]) (.forbid 1 7 1 (.system [[0,1,14,7,6,5,4,3],[2],[8],[10,11,12,13]]) (.forbid 2 3 1 (.system [[0,1,2,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 2 4 1 (.system [[0,1,2,14,4,3],[5,6,7,8],[10,11,12,13]]) (.forbid 2 6 1 (.system [[0,1,2,14,6,7,8],[3,4,5],[10,11,12,13]]) (.forbid 3 4 1 (.system [[0,1,2],[3,14,4,5,6,7,8],[10,11,12,13]]) (.forbid 3 4 2 (.system [[0],[2],[3,14,15,4,5,6,7,8],[10,11,12,13]]) (.forbid 3 4 3 (.system [[0,1,2],[3,14,15,16,4,5,6,7,8],[10],[13]]) (.forbid 3 4 4 (.system [[0],[2],[3,14,15,16,17,4,5,6,7,8],[10],[13]]) (.forbid 3 4 5 (.system [[0,1,2],[3,14,15,16,17,18,4,5],[8],[10],[13]]) (.forbid 3 4 6 (.system [[0],[2],[3,14,15,16,17,18,19,4,5],[8],[10],[13]]) (.forbid 3 6 1 (.system [[0,1,2],[5,4,3,14,6,7,8],[10,11,12,13]]) (.forbid 3 6 2 (.system [[0,1,2],[3,14,15,6,5],[8,9,10,11,12,13]]) (.forbid 3 6 3 (.system [[0,1,2],[3,14,15,16,6,5],[8],[10,11,12,13]]) (certificate_1005_part_0))))))))))))))))))))

noncomputable def certificate_1005_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,14,15,16,6,5],[3],[8],[10,11,12,13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5],[2],[3],[8],[10,11,12,13]]) (.forbid 0 6 5 (.system [[2,1,0,14,15,16,17,18,6,5],[3],[8],[10],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[2],[3],[8],[10],[13]]) (.forbid 0 7 1 (.system [[2,1,0,14,7,6,5,4,3],[8],[10,11,12,13]]) (.forbid 0 9 1 (.system [[2,1,0,14,9,8,7,6,5],[3],[10,11,12,13]]) (.forbid 0 11 1 (.system [[2,1,0,14,11,12,13],[3,4,5,6,7,8],[10]]) (.forbid 1 2 1 (.system [[0,1,14,2],[3,4,5,6,7,8],[10,11,12,13]]) (.forbid 1 3 1 (.system [[0,1,14,3,4,5,6,7,8],[2],[10,11,12,13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3],[2],[5,6,7,8],[10,11,12,13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3,4,5,6,7,8],[2],[10],[13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3],[2],[5,6,7,8],[10],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3,4,5],[2],[8],[10],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3],[2],[5],[8],[10],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4,3],[2],[5,6,7,8],[10,11,12,13]]) (.forbid 1 4 2 (.system [[0,1,14,15,4,3],[2],[5,6,7,8,9,10],[13]]) (.forbid 1 4 3 (.system [[0,1,14,15,16,4,3],[2],[5,6,7,8],[10],[13]]) (.forbid 1 4 4 (.system [[0,1,14,15,16,17,4,3],[2],[5,6,7,8],[10],[13]]) (.forbid 1 4 5 (.system [[0,1,14,15,16,17,18,4,3],[2],[5],[8],[10],[13]]) (.forbid 1 4 6 (.system [[0,1,14,15,16,17,18,19,4,3],[2],[5],[8],[10],[13]]) (certificate_1005_part_1))))))))))))))))))))

noncomputable def certificate_1005 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2],[3,4,5,6,7,8],[10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2],[3],[5,6,7,8],[10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2],[3,4,5,6,7,8],[10],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[3],[5,6,7,8],[10],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2],[3,4,5],[8],[10],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[3],[5],[8],[10],[13]]) (.forbid 0 3 1 (.system [[2,1,0,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[2,1,0,14,15,3],[5,6,7,8],[10,11,12,13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3],[2],[5,6,7,8],[10,11,12,13]]) (.forbid 0 3 4 (.system [[2,1,0,14,15,16,17,3],[5,6,7,8],[10],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3],[2],[5,6,7,8],[10],[13]]) (.forbid 0 3 6 (.system [[2,1,0,14,15,16,17,18,19,3],[5],[8],[10],[13]]) (.forbid 0 4 1 (.system [[2,1,0,14,4,3],[5,6,7,8],[10,11,12,13]]) (.forbid 0 4 2 (.system [[0,14,15,4,3],[2],[5,6,7,8],[10,11,12,13]]) (.forbid 0 4 3 (.system [[2,1,0,14,15,16,4,3],[5,6,7,8],[10],[13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[2],[5,6,7,8],[10],[13]]) (.forbid 0 4 5 (.system [[2,1,0,14,15,16,17,18,4,3],[5],[8],[10],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[2],[5],[8],[10],[13]]) (.forbid 0 6 1 (.system [[2,1,0,14,6,7,8],[3,4,5],[10,11,12,13]]) (.forbid 0 6 2 (.system [[2,1,0,14,15,6,5,4,3],[8],[10,11,12,13]]) (certificate_1005_part_2))))))))))))))))))))

noncomputable def certificate_1006_q : Finset ℕ := ([0,2,3,5,8,11,13] : List ℕ).toFinset
noncomputable def certificate_1006_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,8),(0,11),(0,13),(2,3),(2,5),(2,8),(2,11),(2,13),(3,5),(3,8),(3,11),(3,13),(5,8),(5,11),(5,13),(8,11),(8,13),(11,13)]

noncomputable def certificate_1006_part_0 : FiniteCertificate := .forbid 3 6 4 (.system [[0],[2],[3,14,15,16,17,6,5],[8,9,10,11],[13]]) (.forbid 3 6 5 (.system [[0,1,2],[3,14,15,16,17,18,6,5],[8],[11],[13]]) (.forbid 3 6 6 (.system [[0],[2],[3,14,15,16,17,18,19,6,5],[8],[11],[13]]) (.forbid 3 7 1 (.system [[0,1,2],[3,14,7,6,5],[8,9,10,11,12,13]]) (.forbid 3 9 1 (.system [[0,1,2],[8,7,6,5,4,3,14,9,10,11],[13]]) (.forbid 4 5 1 (.system [[0,1,2],[3,4,14,5,6,7,8,9,10,11],[13]]) (.forbid 4 6 1 (.system [[0,1,2],[3,4,14,6,5],[8,9,10,11,12,13]]) (.forbid 4 6 2 (.system [[0,1,2],[3,4,14,15,6,5],[8,9,10,11],[13]]) (.forbid 4 6 3 (.system [[0],[2],[3,4,14,15,16,6,5],[8,9,10,11],[13]]) (.forbid 4 6 4 (.system [[0,1,2],[3,4,14,15,16,17,6,5],[8],[11],[13]]) (.forbid 4 6 5 (.system [[0],[2],[3,4,14,15,16,17,18,6,5],[8],[11],[13]]) (.forbid 4 6 6 (.system [[0],[2],[3,4,14,15,16,17,18,19,6,5],[8],[11],[13]]) (.forbid 4 7 1 (.system [[0,1,2],[3,4,14,7,6,5],[8,9,10,11],[13]]) (.forbid 5 6 1 (.system [[0,1,2],[3,4,5,14,6,7,8,9,10,11],[13]]) (.forbid 6 7 1 (.system [[0,1,2],[3,4,5,6,14,7,8,9,10,11],[13]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4,6,7,9,10} 8 2) ∅ 15 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4,5,6,7} 8 2) ∅ 15 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4,6,7,9} 8 2) ∅ 15 3), .ball 4 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,5,6,7} 8 2) ∅ 15 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,4,5,7} 8 2) ∅ 15 3)})))))))))))))))

noncomputable def certificate_1006_part_1 : FiniteCertificate := .forbid 1 5 1 (.system [[0,1,14,5,6,7,8,9,10,11,12,13],[2],[3]]) (.forbid 1 6 1 (.system [[0,1,14,6,5,4,3],[2],[8,9,10,11,12,13]]) (.forbid 1 6 2 (.system [[0,1,14,15,6,5,4,3],[2],[8,9,10,11],[13]]) (.forbid 1 6 3 (.system [[0,1,14,15,16,6,5],[2],[3],[8,9,10,11],[13]]) (.forbid 1 6 4 (.system [[0,1,14,15,16,17,6,5,4,3],[2],[8],[11],[13]]) (.forbid 1 6 5 (.system [[0,1,14,15,16,17,18,6,5],[2],[3],[8],[11],[13]]) (.forbid 1 6 6 (.system [[0,1,14,15,16,17,18,19,6,5],[2],[3],[8],[11],[13]]) (.forbid 1 7 1 (.system [[0,1,14,7,6,5,4,3],[2],[8,9,10,11],[13]]) (.forbid 2 3 1 (.system [[0,1,2,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 2 4 1 (.system [[0,1,2,14,4,3],[5,6,7,8,9,10,11],[13]]) (.forbid 2 6 1 (.system [[0,1,2,14,6,7,8,9,10,11],[3,4,5],[13]]) (.forbid 3 4 1 (.system [[0,1,2],[3,14,4,5,6,7,8,9,10,11],[13]]) (.forbid 3 4 2 (.system [[0],[2],[3,14,15,4,5,6,7,8,9,10,11],[13]]) (.forbid 3 4 3 (.system [[0,1,2],[3,14,15,16,4,5,6,7,8],[11],[13]]) (.forbid 3 4 4 (.system [[0],[2],[3,14,15,16,17,4,5,6,7,8],[11],[13]]) (.forbid 3 4 5 (.system [[0,1,2],[3,14,15,16,17,18,4,5],[8],[11],[13]]) (.forbid 3 4 6 (.system [[0],[2],[3,14,15,16,17,18,19,4,5],[8],[11],[13]]) (.forbid 3 6 1 (.system [[0,1,2],[5,4,3,14,6,7,8,9,10,11],[13]]) (.forbid 3 6 2 (.system [[0,1,2],[3,14,15,6,5],[8,9,10,11,12,13]]) (.forbid 3 6 3 (.system [[0,1,2],[3,14,15,16,6,5],[8,9,10,11],[13]]) (certificate_1006_part_0))))))))))))))))))))

noncomputable def certificate_1006_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,14,15,16,6,5],[3],[8,9,10,11],[13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5],[2],[3],[8,9,10,11],[13]]) (.forbid 0 6 5 (.system [[2,1,0,14,15,16,17,18,6,5],[3],[8],[11],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[2],[3],[8],[11],[13]]) (.forbid 0 7 1 (.system [[2,1,0,14,7,6,5,4,3],[8,9,10,11],[13]]) (.forbid 0 9 1 (.system [[2,1,0,14,9,10,11],[3,4,5,6,7,8],[13]]) (.forbid 0 10 1 (.system [[2,1,0,14,10,9,8,7,6,5,4,3],[11],[13]]) (.forbid 1 2 1 (.system [[0,1,14,2],[3,4,5,6,7,8,9,10,11],[13]]) (.forbid 1 3 1 (.system [[0,1,14,3,4,5,6,7,8,9,10,11],[2],[13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3],[2],[5,6,7,8,9,10,11],[13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3,4,5,6,7,8],[2],[11],[13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3],[2],[5,6,7,8],[11],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3,4,5],[2],[8],[11],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3],[2],[5],[8],[11],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4,3],[2],[5,6,7,8,9,10,11],[13]]) (.forbid 1 4 2 (.system [[0,1,14,15,4,3],[2],[5,6,7,8,9,10,11],[13]]) (.forbid 1 4 3 (.system [[0,1,14,15,16,4,3],[2],[5,6,7,8],[11],[13]]) (.forbid 1 4 4 (.system [[0,1,14,15,16,17,4,3],[2],[5,6,7,8],[11],[13]]) (.forbid 1 4 5 (.system [[0,1,14,15,16,17,18,4,3],[2],[5],[8],[11],[13]]) (.forbid 1 4 6 (.system [[0,1,14,15,16,17,18,19,4,3],[2],[5],[8],[11],[13]]) (certificate_1006_part_1))))))))))))))))))))

noncomputable def certificate_1006 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2],[3,4,5,6,7,8,9,10,11],[13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2],[3],[5,6,7,8,9,10,11],[13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2],[3,4,5,6,7,8],[11],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[3],[5,6,7,8],[11],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2],[3,4,5],[8],[11],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[3],[5],[8],[11],[13]]) (.forbid 0 3 1 (.system [[2,1,0,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[2,1,0,14,15,3],[5,6,7,8,9,10,11],[13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3],[2],[5,6,7,8,9,10,11],[13]]) (.forbid 0 3 4 (.system [[2,1,0,14,15,16,17,3],[5,6,7,8],[11],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3],[2],[5,6,7,8],[11],[13]]) (.forbid 0 3 6 (.system [[2,1,0,14,15,16,17,18,19,3],[5],[8],[11],[13]]) (.forbid 0 4 1 (.system [[2,1,0,14,4,3],[5,6,7,8,9,10,11],[13]]) (.forbid 0 4 2 (.system [[0,14,15,4,3],[2],[5,6,7,8,9,10,11],[13]]) (.forbid 0 4 3 (.system [[2,1,0,14,15,16,4,3],[5,6,7,8],[11],[13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[2],[5,6,7,8],[11],[13]]) (.forbid 0 4 5 (.system [[2,1,0,14,15,16,17,18,4,3],[5],[8],[11],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[2],[5],[8],[11],[13]]) (.forbid 0 6 1 (.system [[2,1,0,14,6,7,8,9,10,11],[3,4,5],[13]]) (.forbid 0 6 2 (.system [[2,1,0,14,15,6,5,4,3],[8,9,10,11],[13]]) (certificate_1006_part_2))))))))))))))))))))

noncomputable def certificate_1007_q : Finset ℕ := ([0,2,3,5,9,10,13] : List ℕ).toFinset
noncomputable def certificate_1007_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(10,11),(11,12),(12,13),(0,2),(0,3),(0,5),(0,9),(0,10),(0,13),(2,3),(2,5),(2,9),(2,10),(2,13),(3,5),(3,9),(3,10),(3,13),(5,9),(5,10),(5,13),(9,10),(9,13),(10,13)]

noncomputable def certificate_1007_part_0 : FiniteCertificate := .forbid 3 6 4 (.system [[0],[2],[3,14,15,16,17,6,5],[9],[10,11,12,13]]) (.forbid 3 6 5 (.system [[0,1,2],[3,14,15,16,17,18,6,5],[9],[10],[13]]) (.forbid 3 6 6 (.system [[0],[2],[3,14,15,16,17,18,19,6,5],[9],[10],[13]]) (.forbid 3 8 1 (.system [[0,1,2],[3,14,8,7,6,5],[9],[10,11,12,13]]) (.forbid 3 10 1 (.system [[0,1,2],[9,8,7,6,5,4,3,14,10,11,12,13]]) (.forbid 4 5 1 (.system [[0],[2],[3,4,14,5,6,7,8,9],[10,11,12,13]]) (.forbid 4 6 1 (.system [[0],[2],[3,4,14,6,7,8,9],[5],[10,11,12,13]]) (.forbid 4 6 2 (.system [[0,1,2],[3,4,14,15,6,5],[9],[10,11,12,13]]) (.forbid 4 6 3 (.system [[0],[2],[3,4,14,15,16,6,5],[9],[10,11,12,13]]) (.forbid 4 6 4 (.system [[0,1,2],[3,4,14,15,16,17,6,5],[9],[10],[13]]) (.forbid 4 6 5 (.system [[0],[2],[3,4,14,15,16,17,18,6,5],[9],[10],[13]]) (.forbid 4 6 6 (.system [[0],[2],[3,4,14,15,16,17,18,19,6,5],[9],[10],[13]]) (.forbid 4 7 1 (.system [[0,1,2],[3,4,14,7,6,5],[9],[10,11,12,13]]) (.forbid 5 6 1 (.system [[0,1,2],[3],[5,14,6,7,8,9],[10,11,12,13]]) (.forbid 6 7 1 (.system [[0,1,2],[3],[5,6,14,7,8,9],[10,11,12,13]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4,6,8,9,10} 8 2) ∅ 15 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4,5,6,7} 8 2) ∅ 15 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4,6,8,10} 8 2) ∅ 15 3), .ball 4 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,5,6,7} 8 2) ∅ 15 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,4,5,7} 8 2) ∅ 15 3)})))))))))))))))

noncomputable def certificate_1007_part_1 : FiniteCertificate := .forbid 1 5 1 (.system [[0,1,14,5,6,7,8,9],[2],[3],[10,11,12,13]]) (.forbid 1 6 1 (.system [[0,1,14,6,7,8,9],[2],[3],[5],[10,11,12,13]]) (.forbid 1 6 2 (.system [[0,1,14,15,6,5,4,3],[2],[9],[10,11,12,13]]) (.forbid 1 6 3 (.system [[0,1,14,15,16,6,5],[2],[3],[9],[10,11,12,13]]) (.forbid 1 6 4 (.system [[0,1,14,15,16,17,6,5,4,3],[2],[9],[10],[13]]) (.forbid 1 6 5 (.system [[0,1,14,15,16,17,18,6,5],[2],[3],[9],[10],[13]]) (.forbid 1 6 6 (.system [[0,1,14,15,16,17,18,19,6,5],[2],[3],[9],[10],[13]]) (.forbid 1 7 1 (.system [[0,1,14,7,6,5,4,3],[2],[9],[10,11,12,13]]) (.forbid 2 3 1 (.system [[0,1,2,14,3,4,5,6,7,8,9],[10,11,12,13]]) (.forbid 2 4 1 (.system [[0],[2,14,4,3],[5,6,7,8,9],[10,11,12,13]]) (.forbid 2 6 1 (.system [[0,1,2,14,6,7,8,9],[3],[5],[10,11,12,13]]) (.forbid 3 4 1 (.system [[0],[2],[3,14,4,5,6,7,8,9],[10,11,12,13]]) (.forbid 3 4 2 (.system [[0,1,2],[3,14,15,4,5,6,7,8,9],[10],[13]]) (.forbid 3 4 3 (.system [[0],[2],[3,14,15,16,4,5,6,7,8,9],[10],[13]]) (.forbid 3 4 4 (.system [[0],[2],[3,14,15,16,17,4,5,6,7,8,9],[10],[13]]) (.forbid 3 4 5 (.system [[0,1,2],[3,14,15,16,17,18,4,5],[9],[10],[13]]) (.forbid 3 4 6 (.system [[0],[2],[3,14,15,16,17,18,19,4,5],[9],[10],[13]]) (.forbid 3 6 1 (.system [[0,1,2],[3,14,6,7,8,9],[5],[10,11,12,13]]) (.forbid 3 6 2 (.system [[0],[2],[3,14,15,6,7,8,9],[5],[10,11,12,13]]) (.forbid 3 6 3 (.system [[0,1,2],[3,14,15,16,6,5],[9],[10,11,12,13]]) (certificate_1007_part_0))))))))))))))))))))

noncomputable def certificate_1007_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,14,15,16,6,5],[3],[9],[10,11,12,13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5],[2],[3],[9],[10,11,12,13]]) (.forbid 0 6 5 (.system [[2,1,0,14,15,16,17,18,6,5],[3],[9],[10],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[2],[3],[9],[10],[13]]) (.forbid 0 8 1 (.system [[2,1,0,14,8,7,6,5],[3],[9],[10,11,12,13]]) (.forbid 0 9 1 (.system [[2,1,0,14,9,8,7,6,5,4,3],[10,11,12,13]]) (.forbid 0 10 1 (.system [[2,1,0,14,10,11,12,13],[3,4,5,6,7,8,9]]) (.forbid 1 2 1 (.system [[0,1,14,2],[3],[5,6,7,8,9],[10,11,12,13]]) (.forbid 1 3 1 (.system [[0,1,14,3],[2],[5,6,7,8,9],[10,11,12,13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3,4,5,6,7,8,9],[2],[10],[13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3],[2],[5,6,7,8,9],[10],[13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3],[2],[5,6,7,8,9],[10],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3,4,5],[2],[9],[10],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3],[2],[5],[9],[10],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4,3],[2],[5,6,7,8,9],[10,11,12,13]]) (.forbid 1 4 2 (.system [[0,1,14,15,4,3],[2],[5,6,7,8,9],[10],[13]]) (.forbid 1 4 3 (.system [[0,1,14,15,16,4,3],[2],[5,6,7,8,9],[10],[13]]) (.forbid 1 4 4 (.system [[0,1,14,15,16,17,4,3],[2],[5,6,7,8,9],[10],[13]]) (.forbid 1 4 5 (.system [[0,1,14,15,16,17,18,4,3],[2],[5],[9],[10],[13]]) (.forbid 1 4 6 (.system [[0,1,14,15,16,17,18,19,4,3],[2],[5],[9],[10],[13]]) (certificate_1007_part_1))))))))))))))))))))

noncomputable def certificate_1007 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2],[3],[5,6,7,8,9],[10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2],[3,4,5,6,7,8,9],[10],[13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2],[3],[5,6,7,8,9],[10],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[3],[5,6,7,8,9],[10],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2],[3,4,5],[9],[10],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[3],[5],[9],[10],[13]]) (.forbid 0 3 1 (.system [[2,1,0,14,3,4,5,6,7,8,9],[10,11,12,13]]) (.forbid 0 3 2 (.system [[0,14,15,3],[2],[5,6,7,8,9],[10,11,12,13]]) (.forbid 0 3 3 (.system [[2,1,0,14,15,16,3],[5,6,7,8,9],[10],[13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3],[2],[5,6,7,8,9],[10],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3],[2],[5,6,7,8,9],[10],[13]]) (.forbid 0 3 6 (.system [[2,1,0,14,15,16,17,18,19,3],[5],[9],[10],[13]]) (.forbid 0 4 1 (.system [[0,14,4,3],[2],[5,6,7,8,9],[10,11,12,13]]) (.forbid 0 4 2 (.system [[2,1,0,14,15,4,3],[5,6,7,8,9],[10],[13]]) (.forbid 0 4 3 (.system [[0,14,15,16,4,3],[2],[5,6,7,8,9],[10],[13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[2],[5,6,7,8,9],[10],[13]]) (.forbid 0 4 5 (.system [[2,1,0,14,15,16,17,18,4,3],[5],[9],[10],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[2],[5],[9],[10],[13]]) (.forbid 0 6 1 (.system [[2,1,0,14,6,7,8,9],[3],[5],[10,11,12,13]]) (.forbid 0 6 2 (.system [[0,14,15,6,7,8,9],[2],[3],[5],[10,11,12,13]]) (certificate_1007_part_2))))))))))))))))))))

noncomputable def certificate_1008_q : Finset ℕ := ([0,2,3,6,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1008_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,6),(0,7),(0,10),(0,13),(2,3),(2,6),(2,7),(2,10),(2,13),(3,6),(3,7),(3,10),(3,13),(6,7),(6,10),(6,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1008_part_0 : FiniteCertificate := .forbid 3 7 4 (.system [[0,1,2],[6,5,4,3,14,15,16,17,7],[10],[13]]) (.forbid 3 7 5 (.system [[0],[2],[6,5,4,3,14,15,16,17,18,7],[10],[13]]) (.forbid 3 7 6 (.system [[0,1,2],[3,14,15,16,17,18,19,7],[6],[10],[13]]) (.forbid 3 8 1 (.system [[0],[2],[6,5,4,3,14,8,9,10,11,12,13],[7]]) (.forbid 3 9 1 (.system [[0],[2],[6,5,4,3,14,9,8,7],[10,11,12,13]]) (.forbid 4 5 1 (.system [[0],[2],[3,4,14,5,6],[7,8,9,10,11,12,13]]) (.forbid 4 7 1 (.system [[0],[2],[3],[6,5,4,14,7,8,9,10,11,12,13]]) (.forbid 4 7 2 (.system [[0],[2],[3,4,14,15,7,8,9,10,11,12,13],[6]]) (.forbid 4 7 3 (.system [[0,1,2],[3,4,14,15,16,7,8,9,10],[6],[13]]) (.forbid 4 7 4 (.system [[0],[2],[3,4,14,15,16,17,7,8,9,10],[6],[13]]) (.forbid 4 7 5 (.system [[0,1,2],[3,4,14,15,16,17,18,7],[6],[10],[13]]) (.forbid 4 7 6 (.system [[0],[2],[3,4,14,15,16,17,18,19,7],[6],[10],[13]]) (.forbid 4 8 1 (.system [[0,1,2],[3,4,14,8,9,10,11,12,13],[6],[7]]) (.forbid 5 7 1 (.system [[0],[2],[3,4,5,14,7,8,9,10,11,12,13],[6]]) (.forbid 6 7 1 (.system [[0,1,2],[3,4,5,6,14,7,8,9,10,11,12,13]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4,5,6,7,8} 8 2) ∅ 15 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4,5,6,7} 8 2) ∅ 15 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4,7,8,9} 8 2) ∅ 15 3), .ball 4 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,5,7,8} 8 2) ∅ 15 3), .ball 7 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,4,5,6} 8 2) ∅ 15 3)})))))))))))))))

noncomputable def certificate_1008_part_1 : FiniteCertificate := .forbid 1 5 1 (.system [[0,1,14,5,4,3],[2],[6],[7,8,9,10,11,12,13]]) (.forbid 1 6 1 (.system [[0,1,14,6,5,4,3],[2],[7,8,9,10,11,12,13]]) (.forbid 1 7 1 (.system [[0,1,14,7,8,9,10,11,12,13],[2],[3,4,5,6]]) (.forbid 1 7 2 (.system [[0,1,14,15,7,8,9,10],[2],[3,4,5,6],[13]]) (.forbid 1 7 3 (.system [[0,1,14,15,16,7,8,9,10],[2],[3,4,5,6],[13]]) (.forbid 1 7 4 (.system [[0,1,14,15,16,17,7],[2],[3,4,5,6],[10],[13]]) (.forbid 1 7 5 (.system [[0,1,14,15,16,17,18,7],[2],[3,4,5,6],[10],[13]]) (.forbid 1 7 6 (.system [[0,1,14,15,16,17,18,19,7],[2],[3],[6],[10],[13]]) (.forbid 2 3 1 (.system [[0,1,2,14,3,4,5,6],[7,8,9,10,11,12,13]]) (.forbid 2 4 1 (.system [[0],[2,14,4,5,6],[3],[7,8,9,10,11,12,13]]) (.forbid 2 7 1 (.system [[0,1,2,14,7,8,9,10,11,12,13],[3,4,5,6]]) (.forbid 3 4 1 (.system [[0],[2],[3,14,4,5,6],[7,8,9,10,11,12,13]]) (.forbid 3 4 2 (.system [[0,1,2],[3,14,15,4,5,6],[7,8,9,10],[13]]) (.forbid 3 4 3 (.system [[0],[2],[3,14,15,16,4,5,6],[7,8,9,10],[13]]) (.forbid 3 4 4 (.system [[0,1,2],[3,14,15,16,17,4,5,6],[7],[10],[13]]) (.forbid 3 4 5 (.system [[0],[2],[3,14,15,16,17,18,4,5,6],[7],[10],[13]]) (.forbid 3 4 6 (.system [[0],[2],[3,14,15,16,17,18,19,4,5,6],[7],[10],[13]]) (.forbid 3 7 1 (.system [[0,1,2],[6,5,4,3,14,7,8,9,10,11,12,13]]) (.forbid 3 7 2 (.system [[0],[2],[6,5,4,3,14,15,7,8,9,10,11,12,13]]) (.forbid 3 7 3 (.system [[0],[2],[6,5,4,3,14,15,16,7,8,9,10],[13]]) (certificate_1008_part_0))))))))))))))))))))

noncomputable def certificate_1008_part_2 : FiniteCertificate := .forbid 0 7 1 (.system [[2,1,0,14,7,8,9,10,11,12,13],[3,4,5,6]]) (.forbid 0 7 2 (.system [[0,14,15,7,8,9,10,11,12,13],[2],[3,4,5,6]]) (.forbid 0 7 3 (.system [[0,14,15,16,7,8,9,10],[2],[3,4,5,6],[13]]) (.forbid 0 7 4 (.system [[2,1,0,14,15,16,17,7],[3,4,5,6],[10],[13]]) (.forbid 0 7 5 (.system [[0,14,15,16,17,18,7],[2],[3,4,5,6],[10],[13]]) (.forbid 0 7 6 (.system [[2,1,0,14,15,16,17,18,19,7],[3],[6],[10],[13]]) (.forbid 0 8 1 (.system [[0,14,8,9,10,11,12,13],[2],[3,4,5,6],[7]]) (.forbid 1 2 1 (.system [[0,1,14,2],[3,4,5,6],[7,8,9,10,11,12,13]]) (.forbid 1 3 1 (.system [[0,1,14,3,4,5,6],[2],[7,8,9,10,11,12,13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3,4,5,6],[2],[7,8,9,10],[13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3,4,5,6],[2],[7,8,9,10],[13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3,4,5,6],[2],[7],[10],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3,4,5,6],[2],[7],[10],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3],[2],[6],[7],[10],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4,3],[2],[6],[7,8,9,10,11,12,13]]) (.forbid 1 4 2 (.system [[0,1,14,15,4,3],[2],[6],[7,8,9,10,11,12,13]]) (.forbid 1 4 3 (.system [[0,1,14,15,16,4,3],[2],[6],[7,8,9,10],[13]]) (.forbid 1 4 4 (.system [[0,1,14,15,16,17,4,3],[2],[6],[7,8,9,10],[13]]) (.forbid 1 4 5 (.system [[0,1,14,15,16,17,18,4,3],[2],[6],[7],[10],[13]]) (.forbid 1 4 6 (.system [[0,1,14,15,16,17,18,19,4,3],[2],[6],[7],[10],[13]]) (certificate_1008_part_1))))))))))))))))))))

noncomputable def certificate_1008 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2],[3,4,5,6],[7,8,9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2],[3,4,5,6],[7,8,9,10],[13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2],[3,4,5,6],[7,8,9,10],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[3,4,5,6],[7],[10],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2],[3,4,5,6],[7],[10],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[3],[6],[7],[10],[13]]) (.forbid 0 3 1 (.system [[2,1,0,14,3,4,5,6],[7,8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[0,14,15,3,4,5,6],[2],[7,8,9,10,11,12,13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3,4,5,6],[2],[7,8,9,10],[13]]) (.forbid 0 3 4 (.system [[2,1,0,14,15,16,17,3,4,5,6],[7],[10],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3,4,5,6],[2],[7],[10],[13]]) (.forbid 0 3 6 (.system [[2,1,0,14,15,16,17,18,19,3],[6],[7],[10],[13]]) (.forbid 0 4 1 (.system [[0,14,4,5,6],[2],[3],[7,8,9,10,11,12,13]]) (.forbid 0 4 2 (.system [[0,14,15,4,3],[2],[6],[7,8,9,10,11,12,13]]) (.forbid 0 4 3 (.system [[2,1,0,14,15,16,4,3],[6],[7,8,9,10],[13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[2],[6],[7,8,9,10],[13]]) (.forbid 0 4 5 (.system [[2,1,0,14,15,16,17,18,4,3],[6],[7],[10],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[2],[6],[7],[10],[13]]) (.forbid 0 5 1 (.system [[0,14,5,4,3],[2],[6],[7,8,9,10,11,12,13]]) (.forbid 0 6 1 (.system [[2,1,0,14,6,5,4,3],[7,8,9,10,11,12,13]]) (certificate_1008_part_2))))))))))))))))))))

noncomputable def certificate_1009_q : Finset ℕ := ([0,2,3,6,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1009_edges : List (ℕ × ℕ) := [(0,1),(1,2),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,3),(0,6),(0,8),(0,10),(0,13),(2,3),(2,6),(2,8),(2,10),(2,13),(3,6),(3,8),(3,10),(3,13),(6,8),(6,10),(6,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1009_part_0 : FiniteCertificate := .forbid 3 7 4 (.system [[0],[2],[3,14,15,16,17,7,6],[8],[10,11,12,13]]) (.forbid 3 7 5 (.system [[0,1,2],[3,14,15,16,17,18,7,6],[8],[10],[13]]) (.forbid 3 7 6 (.system [[0],[2],[3,14,15,16,17,18,19,7,6],[8],[10],[13]]) (.forbid 3 9 1 (.system [[0,1,2],[6,5,4,3,14,9,8],[10,11,12,13]]) (.forbid 3 11 1 (.system [[0,1,2],[8,7,6,5,4,3,14,11,12,13],[10]]) (.forbid 4 5 1 (.system [[0,1,2],[3,4,14,5,6,7,8],[10,11,12,13]]) (.forbid 4 7 1 (.system [[0,1,2],[3,4,14,7,6],[8,9,10,11,12,13]]) (.forbid 4 7 2 (.system [[0,1,2],[3,4,14,15,7,6],[8],[10,11,12,13]]) (.forbid 4 7 3 (.system [[0],[2],[3,4,14,15,16,7,6],[8],[10,11,12,13]]) (.forbid 4 7 4 (.system [[0,1,2],[3,4,14,15,16,17,7,6],[8],[10],[13]]) (.forbid 4 7 5 (.system [[0],[2],[3,4,14,15,16,17,18,7,6],[8],[10],[13]]) (.forbid 4 7 6 (.system [[0],[2],[3,4,14,15,16,17,18,19,7,6],[8],[10],[13]]) (.forbid 4 8 1 (.system [[0,1,2],[3],[6,5,4,14,8,9,10,11,12,13]]) (.forbid 5 7 1 (.system [[0,1,2],[3,4,5,14,7,6],[8],[10,11,12,13]]) (.forbid 6 7 1 (.system [[0,1,2],[3,4,5,6,14,7,8],[10,11,12,13]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,4,5,7,9,11} 8 2) ∅ 15 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4,5,6,7} 8 2) ∅ 15 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4,7,9,11} 8 2) ∅ 15 3), .ball 4 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,5,7,8} 8 2) ∅ 15 3), .ball 7 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,4,5,6} 8 2) ∅ 15 3)})))))))))))))))

noncomputable def certificate_1009_part_1 : FiniteCertificate := .forbid 1 5 1 (.system [[0,1,14,5,4,3],[2],[6,7,8],[10,11,12,13]]) (.forbid 1 6 1 (.system [[0,1,14,6,5,4,3],[2],[8,9,10,11,12,13]]) (.forbid 1 7 1 (.system [[0,1,14,7,6,5,4,3],[2],[8],[10,11,12,13]]) (.forbid 1 7 2 (.system [[0,1,14,15,7,6,5,4,3],[2],[8,9,10],[13]]) (.forbid 1 7 3 (.system [[0,1,14,15,16,7,6,5,4,3],[2],[8],[10],[13]]) (.forbid 1 7 4 (.system [[0,1,14,15,16,17,7,6,5,4,3],[2],[8],[10],[13]]) (.forbid 1 7 5 (.system [[0,1,14,15,16,17,18,7,6],[2],[3],[8],[10],[13]]) (.forbid 1 7 6 (.system [[0,1,14,15,16,17,18,19,7,6],[2],[3],[8],[10],[13]]) (.forbid 2 3 1 (.system [[0,1,2,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 2 4 1 (.system [[0,1,2,14,4,5,6,7,8],[3],[10,11,12,13]]) (.forbid 2 7 1 (.system [[0,1,2,14,7,6,5,4,3],[8],[10,11,12,13]]) (.forbid 3 4 1 (.system [[0,1,2],[3,14,4,5,6,7,8],[10,11,12,13]]) (.forbid 3 4 2 (.system [[0,1,2],[3,14,15,4,5,6],[8],[10,11,12,13]]) (.forbid 3 4 3 (.system [[0],[2],[3,14,15,16,4,5,6],[8],[10,11,12,13]]) (.forbid 3 4 4 (.system [[0,1,2],[3,14,15,16,17,4,5,6],[8],[10],[13]]) (.forbid 3 4 5 (.system [[0],[2],[3,14,15,16,17,18,4,5,6],[8],[10],[13]]) (.forbid 3 4 6 (.system [[0],[2],[3,14,15,16,17,18,19,4,5,6],[8],[10],[13]]) (.forbid 3 7 1 (.system [[0,1,2],[6,5,4,3,14,7,8],[10,11,12,13]]) (.forbid 3 7 2 (.system [[0,1,2],[3,14,15,7,6],[8,9,10,11,12,13]]) (.forbid 3 7 3 (.system [[0,1,2],[3,14,15,16,7,6],[8],[10,11,12,13]]) (certificate_1009_part_0))))))))))))))))))))

noncomputable def certificate_1009_part_2 : FiniteCertificate := .forbid 0 7 2 (.system [[0,14,15,7,6,5,4,3],[2],[8],[10,11,12,13]]) (.forbid 0 7 3 (.system [[2,1,0,14,15,16,7,6,5,4,3],[8],[10],[13]]) (.forbid 0 7 4 (.system [[0,14,15,16,17,7,6,5,4,3],[2],[8],[10],[13]]) (.forbid 0 7 5 (.system [[2,1,0,14,15,16,17,18,7,6],[3],[8],[10],[13]]) (.forbid 0 7 6 (.system [[0,14,15,16,17,18,19,7,6],[2],[3],[8],[10],[13]]) (.forbid 0 9 1 (.system [[2,1,0,14,9,8],[3,4,5,6],[10,11,12,13]]) (.forbid 0 11 1 (.system [[2,1,0,14,11,12,13],[3,4,5,6,7,8],[10]]) (.forbid 1 2 1 (.system [[0,1,14,2],[3,4,5,6,7,8],[10,11,12,13]]) (.forbid 1 3 1 (.system [[0,1,14,3,4,5,6,7,8],[2],[10,11,12,13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3,4,5,6],[2],[8],[10,11,12,13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3,4,5,6,7,8],[2],[10],[13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3,4,5,6],[2],[8],[10],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3,4,5,6],[2],[8],[10],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3],[2],[6],[8],[10],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4,3],[2],[6,7,8,9,10,11,12,13]]) (.forbid 1 4 2 (.system [[0,1,14,15,4,3],[2],[6,7,8],[10,11,12,13]]) (.forbid 1 4 3 (.system [[0,1,14,15,16,4,3],[2],[6],[8],[10,11,12,13]]) (.forbid 1 4 4 (.system [[0,1,14,15,16,17,4,3],[2],[6,7,8],[10],[13]]) (.forbid 1 4 5 (.system [[0,1,14,15,16,17,18,4,3],[2],[6],[8],[10],[13]]) (.forbid 1 4 6 (.system [[0,1,14,15,16,17,18,19,4,3],[2],[6],[8],[10],[13]]) (certificate_1009_part_1))))))))))))))))))))

noncomputable def certificate_1009 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2],[3,4,5,6,7,8],[10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2],[3,4,5,6],[8],[10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2],[3,4,5,6,7,8],[10],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[3,4,5,6],[8],[10],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2],[3,4,5,6],[8],[10],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[3],[6],[8],[10],[13]]) (.forbid 0 3 1 (.system [[2,1,0,14,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[2,1,0,14,15,3,4,5,6],[8],[10,11,12,13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3,4,5,6],[2],[8],[10,11,12,13]]) (.forbid 0 3 4 (.system [[2,1,0,14,15,16,17,3,4,5,6],[8],[10],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3,4,5,6],[2],[8],[10],[13]]) (.forbid 0 3 6 (.system [[2,1,0,14,15,16,17,18,19,3],[6],[8],[10],[13]]) (.forbid 0 4 1 (.system [[2,1,0,14,4,5,6,7,8],[3],[10,11,12,13]]) (.forbid 0 4 2 (.system [[2,1,0,14,15,4,3],[6,7,8],[10,11,12,13]]) (.forbid 0 4 3 (.system [[2,1,0,14,15,16,4,3],[6],[8],[10,11,12,13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[2],[6],[8],[10,11,12,13]]) (.forbid 0 4 5 (.system [[2,1,0,14,15,16,17,18,4,3],[6],[8],[10],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[2],[6],[8],[10],[13]]) (.forbid 0 5 1 (.system [[2,1,0,14,5,4,3],[6,7,8],[10,11,12,13]]) (.forbid 0 7 1 (.system [[2,1,0,14,7,6,5,4,3],[8],[10,11,12,13]]) (certificate_1009_part_2))))))))))))))))))))

noncomputable def certificate_1010_q : Finset ℕ := ([0,2,4,5,7,9,11] : List ℕ).toFinset
noncomputable def certificate_1010_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(0,2),(0,4),(0,5),(0,7),(0,9),(0,11),(2,4),(2,5),(2,7),(2,9),(2,11),(4,5),(4,7),(4,9),(4,11),(5,7),(5,9),(5,11),(7,9),(7,11),(9,11)]

noncomputable def certificate_1010_part_0 : FiniteCertificate := .forbid 5 6 2 (.system [[0,1,2,3,4],[5,12,13,6,7],[9],[11]]) (.forbid 5 6 3 (.system [[0,1,2],[4],[5,12,13,14,6,7],[9],[11]]) (.forbid 5 6 4 (.system [[0],[2],[4],[5,12,13,14,15,6,7],[9],[11]]) (.forbid 5 6 5 (.system [[0],[2],[4],[5,12,13,14,15,16,6,7],[9],[11]]) (.forbid 5 6 6 (.system [[0],[2],[4],[5,12,13,14,15,16,17,6,7],[9],[11]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 3 1) {1,3,5,6,8} 8 2) ∅ 17 3), .ball 1 (.succ (.succ (.zero ∅ 3 1) {0,2,3,5,6} 8 2) ∅ 17 3), .ball 3 (.succ (.succ (.zero ∅ 3 1) {0,1,2,5,6} 8 2) ∅ 17 3), .ball 5 (.succ (.succ (.zero ∅ 3 1) {0,1,3,4,6} 8 2) ∅ 17 3), .ball 6 (.succ (.succ (.zero ∅ 3 1) {0,1,2,3,5} 8 2) ∅ 17 3)})))))

noncomputable def certificate_1010_part_1 : FiniteCertificate := .forbid 1 6 3 (.system [[0,1,12,13,14,6,5],[2],[4],[7],[9],[11]]) (.forbid 1 6 4 (.system [[0,1,12,13,14,15,6,5],[2],[4],[7],[9],[11]]) (.forbid 1 6 5 (.system [[0,1,12,13,14,15,16,6,5],[2],[4],[7],[9],[11]]) (.forbid 1 6 6 (.system [[0,1,12,13,14,15,16,17,6,5],[2],[4],[7],[9],[11]]) (.forbid 2 3 1 (.system [[0,1,2,12,3,4],[5,6,7,8,9],[11]]) (.forbid 2 6 1 (.system [[0,1,2,12,6,5],[4],[7,8,9,10,11]]) (.forbid 3 5 1 (.system [[0,1,2,3,12,5,6,7,8,9],[4],[11]]) (.forbid 3 5 2 (.system [[0,1,2,3,12,13,5,6,7],[4],[9],[11]]) (.forbid 3 5 3 (.system [[0,1,2,3,12,13,14,5],[4],[7],[9],[11]]) (.forbid 3 5 4 (.system [[0],[2,3,12,13,14,15,5],[4],[7],[9],[11]]) (.forbid 3 5 5 (.system [[0],[2,3,12,13,14,15,16,5],[4],[7],[9],[11]]) (.forbid 3 5 6 (.system [[0],[2,3,12,13,14,15,16,17,5],[4],[7],[9],[11]]) (.forbid 3 6 1 (.system [[0,1,2,3,12,6,5],[4],[7,8,9],[11]]) (.forbid 3 6 2 (.system [[0,1,2,3,12,13,6,5],[4],[7],[9],[11]]) (.forbid 3 6 3 (.system [[0],[2,3,12,13,14,6,5],[4],[7],[9],[11]]) (.forbid 3 6 4 (.system [[0],[2,3,12,13,14,15,6,5],[4],[7],[9],[11]]) (.forbid 3 6 5 (.system [[0],[2,3,12,13,14,15,16,6,5],[4],[7],[9],[11]]) (.forbid 3 6 6 (.system [[0],[2,3,12,13,14,15,16,17,6,5],[4],[7],[9],[11]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,12,5,6,7,8,9,10,11]]) (.forbid 5 6 1 (.system [[0,1,2,3,4],[5,12,6,7,8,9],[11]]) (certificate_1010_part_0))))))))))))))))))))

noncomputable def certificate_1010_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,12,13,14,6,5],[4],[7],[9],[11]]) (.forbid 0 6 4 (.system [[0,12,13,14,15,6,5],[2],[4],[7],[9],[11]]) (.forbid 0 6 5 (.system [[0,12,13,14,15,16,6,5],[2],[4],[7],[9],[11]]) (.forbid 0 6 6 (.system [[0,12,13,14,15,16,17,6,5],[2],[4],[7],[9],[11]]) (.forbid 0 8 1 (.system [[4,3,2,1,0,12,8,7,6,5],[9],[11]]) (.forbid 1 2 1 (.system [[0,1,12,2,3,4],[5,6,7,8,9],[11]]) (.forbid 1 3 1 (.system [[0,1,12,3,2],[4],[5,6,7,8,9],[11]]) (.forbid 1 3 2 (.system [[0,1,12,13,3,2],[4],[5,6,7],[9],[11]]) (.forbid 1 3 3 (.system [[0,1,12,13,14,3,2],[4],[5],[7],[9],[11]]) (.forbid 1 3 4 (.system [[0,1,12,13,14,15,3,2],[4],[5],[7],[9],[11]]) (.forbid 1 3 5 (.system [[0,1,12,13,14,15,16,3,2],[4],[5],[7],[9],[11]]) (.forbid 1 3 6 (.system [[0,1,12,13,14,15,16,17,3,2],[4],[5],[7],[9],[11]]) (.forbid 1 5 1 (.system [[0,1,12,5,6,7,8,9],[2,3,4],[11]]) (.forbid 1 5 2 (.system [[0,1,12,13,5,6,7],[2,3,4],[9],[11]]) (.forbid 1 5 3 (.system [[0,1,12,13,14,5],[2,3,4],[7],[9],[11]]) (.forbid 1 5 4 (.system [[0,1,12,13,14,15,5],[2],[4],[7],[9],[11]]) (.forbid 1 5 5 (.system [[0,1,12,13,14,15,16,5],[2],[4],[7],[9],[11]]) (.forbid 1 5 6 (.system [[0,1,12,13,14,15,16,17,5],[2],[4],[7],[9],[11]]) (.forbid 1 6 1 (.system [[0,1,12,6,5],[2,3,4],[7,8,9],[11]]) (.forbid 1 6 2 (.system [[0,1,12,13,6,5],[2,3,4],[7],[9],[11]]) (certificate_1010_part_1))))))))))))))))))))

noncomputable def certificate_1010 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1,2,3,4],[5,6,7,8,9],[11]]) (.forbid 0 1 2 (.system [[0,12,13,1,2,3,4],[5,6,7],[9],[11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1,2,3,4],[5],[7],[9],[11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1,2],[4],[5],[7],[9],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1,2],[4],[5],[7],[9],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1,2],[4],[5],[7],[9],[11]]) (.forbid 0 3 1 (.system [[0,12,3,2],[4],[5,6,7,8,9,10,11]]) (.forbid 0 3 2 (.system [[0,12,13,3,2],[4],[5,6,7,8,9],[11]]) (.forbid 0 3 3 (.system [[0,12,13,14,3,2],[4],[5,6,7],[9],[11]]) (.forbid 0 3 4 (.system [[0,12,13,14,15,3,2],[4],[5],[7],[9],[11]]) (.forbid 0 3 5 (.system [[0,12,13,14,15,16,3,2],[4],[5],[7],[9],[11]]) (.forbid 0 3 6 (.system [[0,12,13,14,15,16,17,3,2],[4],[5],[7],[9],[11]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,12,5,6,7,8,9,10,11]]) (.forbid 0 5 2 (.system [[4,3,2,1,0,12,13,5,6,7],[9],[11]]) (.forbid 0 5 3 (.system [[4,3,2,1,0,12,13,14,5],[7],[9],[11]]) (.forbid 0 5 4 (.system [[2,1,0,12,13,14,15,5],[4],[7],[9],[11]]) (.forbid 0 5 5 (.system [[0,12,13,14,15,16,5],[2],[4],[7],[9],[11]]) (.forbid 0 5 6 (.system [[0,12,13,14,15,16,17,5],[2],[4],[7],[9],[11]]) (.forbid 0 6 1 (.system [[4,3,2,1,0,12,6,5],[7,8,9],[11]]) (.forbid 0 6 2 (.system [[4,3,2,1,0,12,13,6,5],[7],[9],[11]]) (certificate_1010_part_2))))))))))))))))))))

noncomputable def certificate_1011_q : Finset ℕ := ([0,2,4,5,7,9,12] : List ℕ).toFinset
noncomputable def certificate_1011_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,5),(0,7),(0,9),(0,12),(2,4),(2,5),(2,7),(2,9),(2,12),(4,5),(4,7),(4,9),(4,12),(5,7),(5,9),(5,12),(7,9),(7,12),(9,12)]

noncomputable def certificate_1011_part_0 : FiniteCertificate := .forbid 3 6 6 (.system [[0],[2,3,13,14,15,16,17,18,6,5],[4],[7],[9],[12]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,13,5,6,7,8,9,10,11,12]]) (.forbid 4 6 1 (.system [[0,1,2,3,4,13,6,5],[7],[9,10,11,12]]) (.forbid 5 6 1 (.system [[0,1,2,3,4],[5,13,6,7],[9,10,11,12]]) (.forbid 5 6 2 (.system [[0,1,2],[4],[5,13,14,6,7],[9,10,11,12]]) (.forbid 5 6 3 (.system [[0],[2],[4],[5,13,14,15,6,7],[9,10,11,12]]) (.forbid 5 6 4 (.system [[0,1,2],[4],[5,13,14,15,16,6,7],[9],[12]]) (.forbid 5 6 5 (.system [[0],[2],[4],[5,13,14,15,16,17,6,7],[9],[12]]) (.forbid 5 6 6 (.system [[0],[2],[4],[5,13,14,15,16,17,18,6,7],[9],[12]]) (.forbid 5 8 1 (.system [[0,1,2,3,4],[5,13,8,7],[9,10,11,12]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,3,5,6,8,10} 8 2) ∅ 16 3), .ball 1 (.succ (.succ (.zero ∅ 2 1) {0,2,3,4,5,6} 8 2) ∅ 16 3), .ball 3 (.succ (.succ (.zero ∅ 2 1) {0,1,2,4,5,6} 8 2) ∅ 16 3), .ball 5 (.succ (.succ (.zero ∅ 2 1) {0,1,3,4,6,8} 8 2) ∅ 16 3), .ball 6 (.succ (.succ (.zero ∅ 2 1) {0,1,2,3,4,5} 8 2) ∅ 16 3)}))))))))))

noncomputable def certificate_1011_part_1 : FiniteCertificate := .forbid 1 6 1 (.system [[0,1,13,6,5],[2,3,4],[7],[9,10,11,12]]) (.forbid 1 6 2 (.system [[0,1,13,14,6,5],[2],[4],[7],[9,10,11,12]]) (.forbid 1 6 3 (.system [[0,1,13,14,15,6,5],[2,3,4],[7],[9],[12]]) (.forbid 1 6 4 (.system [[0,1,13,14,15,16,6,5],[2],[4],[7],[9],[12]]) (.forbid 1 6 5 (.system [[0,1,13,14,15,16,17,6,5],[2],[4],[7],[9],[12]]) (.forbid 1 6 6 (.system [[0,1,13,14,15,16,17,18,6,5],[2],[4],[7],[9],[12]]) (.forbid 2 3 1 (.system [[0,1,2,13,3,4],[5,6,7],[9,10,11,12]]) (.forbid 2 6 1 (.system [[0,1,2,13,6,5],[4],[7,8,9,10,11,12]]) (.forbid 3 4 1 (.system [[0,1,2,3,13,4],[5,6,7],[9,10,11,12]]) (.forbid 3 5 1 (.system [[0,1,2,3,13,5,6,7],[4],[9,10,11,12]]) (.forbid 3 5 2 (.system [[0,1,2,3,13,14,5],[4],[7],[9,10,11,12]]) (.forbid 3 5 3 (.system [[0],[2,3,13,14,15,5],[4],[7],[9,10,11,12]]) (.forbid 3 5 4 (.system [[0,1,2,3,13,14,15,16,5],[4],[7],[9],[12]]) (.forbid 3 5 5 (.system [[0],[2,3,13,14,15,16,17,5],[4],[7],[9],[12]]) (.forbid 3 5 6 (.system [[0],[2,3,13,14,15,16,17,18,5],[4],[7],[9],[12]]) (.forbid 3 6 1 (.system [[0,1,2,3,13,6,5],[4],[7],[9,10,11,12]]) (.forbid 3 6 2 (.system [[0],[2,3,13,14,6,5],[4],[7],[9,10,11,12]]) (.forbid 3 6 3 (.system [[0,1,2,3,13,14,15,6,5],[4],[7],[9],[12]]) (.forbid 3 6 4 (.system [[0],[2,3,13,14,15,16,6,5],[4],[7],[9],[12]]) (.forbid 3 6 5 (.system [[0],[2,3,13,14,15,16,17,6,5],[4],[7],[9],[12]]) (certificate_1011_part_0))))))))))))))))))))

noncomputable def certificate_1011_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[0,13,14,15,6,5],[2],[4],[7],[9,10,11,12]]) (.forbid 0 6 4 (.system [[2,1,0,13,14,15,16,6,5],[4],[7],[9],[12]]) (.forbid 0 6 5 (.system [[0,13,14,15,16,17,6,5],[2],[4],[7],[9],[12]]) (.forbid 0 6 6 (.system [[0,13,14,15,16,17,18,6,5],[2],[4],[7],[9],[12]]) (.forbid 0 8 1 (.system [[4,3,2,1,0,13,8,7],[5],[9,10,11,12]]) (.forbid 0 10 1 (.system [[4,3,2,1,0,13,10,11,12],[5,6,7],[9]]) (.forbid 1 2 1 (.system [[0,1,13,2,3,4],[5,6,7],[9,10,11,12]]) (.forbid 1 3 1 (.system [[0,1,13,3,2],[4],[5,6,7],[9,10,11,12]]) (.forbid 1 3 2 (.system [[0,1,13,14,3,2],[4],[5],[7],[9,10,11,12]]) (.forbid 1 3 3 (.system [[0,1,13,14,15,3,2],[4],[5,6,7],[9],[12]]) (.forbid 1 3 4 (.system [[0,1,13,14,15,16,3,2],[4],[5],[7],[9],[12]]) (.forbid 1 3 5 (.system [[0,1,13,14,15,16,17,3,2],[4],[5],[7],[9],[12]]) (.forbid 1 3 6 (.system [[0,1,13,14,15,16,17,18,3,2],[4],[5],[7],[9],[12]]) (.forbid 1 4 1 (.system [[0,1,13,4,3,2],[5,6,7],[9,10,11,12]]) (.forbid 1 5 1 (.system [[0,1,13,5,6,7],[2,3,4],[9,10,11,12]]) (.forbid 1 5 2 (.system [[0,1,13,14,5],[2,3,4],[7],[9,10,11,12]]) (.forbid 1 5 3 (.system [[0,1,13,14,15,5],[2],[4],[7],[9,10,11,12]]) (.forbid 1 5 4 (.system [[0,1,13,14,15,16,5],[2,3,4],[7],[9],[12]]) (.forbid 1 5 5 (.system [[0,1,13,14,15,16,17,5],[2],[4],[7],[9],[12]]) (.forbid 1 5 6 (.system [[0,1,13,14,15,16,17,18,5],[2],[4],[7],[9],[12]]) (certificate_1011_part_1))))))))))))))))))))

noncomputable def certificate_1011 : FiniteCertificate := .forbid 0 1 1 (.system [[0,13,1,2,3,4],[5,6,7],[9,10,11,12]]) (.forbid 0 1 2 (.system [[0,13,14,1,2,3,4],[5],[7],[9,10,11,12]]) (.forbid 0 1 3 (.system [[0,13,14,15,1,2],[4],[5],[7],[9,10,11,12]]) (.forbid 0 1 4 (.system [[0,13,14,15,16,1,2,3,4],[5],[7],[9],[12]]) (.forbid 0 1 5 (.system [[0,13,14,15,16,17,1,2],[4],[5],[7],[9],[12]]) (.forbid 0 1 6 (.system [[0,13,14,15,16,17,18,1,2],[4],[5],[7],[9],[12]]) (.forbid 0 3 1 (.system [[0,13,3,2],[4],[5,6,7,8,9,10,11,12]]) (.forbid 0 3 2 (.system [[0,13,14,3,2],[4],[5,6,7],[9,10,11,12]]) (.forbid 0 3 3 (.system [[0,13,14,15,3,2],[4],[5],[7],[9,10,11,12]]) (.forbid 0 3 4 (.system [[0,13,14,15,16,3,2],[4],[5,6,7],[9],[12]]) (.forbid 0 3 5 (.system [[0,13,14,15,16,17,3,2],[4],[5],[7],[9],[12]]) (.forbid 0 3 6 (.system [[0,13,14,15,16,17,18,3,2],[4],[5],[7],[9],[12]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,13,5,6,7,8,9,10,11,12]]) (.forbid 0 5 2 (.system [[4,3,2,1,0,13,14,5],[7],[9,10,11,12]]) (.forbid 0 5 3 (.system [[2,1,0,13,14,15,5],[4],[7],[9,10,11,12]]) (.forbid 0 5 4 (.system [[0,13,14,15,16,5],[2],[4],[7],[9,10,11,12]]) (.forbid 0 5 5 (.system [[2,1,0,13,14,15,16,17,5],[4],[7],[9],[12]]) (.forbid 0 5 6 (.system [[0,13,14,15,16,17,18,5],[2],[4],[7],[9],[12]]) (.forbid 0 6 1 (.system [[4,3,2,1,0,13,6,5],[7],[9,10,11,12]]) (.forbid 0 6 2 (.system [[2,1,0,13,14,6,5],[4],[7],[9,10,11,12]]) (certificate_1011_part_2))))))))))))))))))))

noncomputable def certificate_1012_q : Finset ℕ := ([0,2,4,5,7,9,13] : List ℕ).toFinset
noncomputable def certificate_1012_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,9),(0,13),(2,4),(2,5),(2,7),(2,9),(2,13),(4,5),(4,7),(4,9),(4,13),(5,7),(5,9),(5,13),(7,9),(7,13),(9,13)]

noncomputable def certificate_1012_part_0 : FiniteCertificate := .forbid 3 6 4 (.system [[0,1,2,3,14,15,16,17,6,5],[4],[7],[9],[13]]) (.forbid 3 6 5 (.system [[0],[2,3,14,15,16,17,18,6,5],[4],[7],[9],[13]]) (.forbid 3 6 6 (.system [[0],[2,3,14,15,16,17,18,19,6,5],[4],[7],[9],[13]]) (.forbid 3 7 1 (.system [[0,1,2,3,14,7,6,5],[4],[9,10,11,12,13]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,14,5,6,7,8,9,10,11,12,13]]) (.forbid 4 6 1 (.system [[0,1,2,3,4,14,6,5],[7],[9,10,11,12,13]]) (.forbid 5 6 1 (.system [[0,1,2,3,4],[5,14,6,7],[9,10,11,12,13]]) (.forbid 5 6 2 (.system [[0,1,2],[4],[5,14,15,6,7],[9,10,11,12,13]]) (.forbid 5 6 3 (.system [[0],[2],[4],[5,14,15,16,6,7],[9,10,11,12,13]]) (.forbid 5 6 4 (.system [[0],[2],[4],[5,14,15,16,17,6,7],[9,10,11,12,13]]) (.forbid 5 6 5 (.system [[0,1,2],[4],[5,14,15,16,17,18,6,7],[9],[13]]) (.forbid 5 6 6 (.system [[0],[2],[4],[5,14,15,16,17,18,19,6,7],[9],[13]]) (.forbid 5 8 1 (.system [[0,1,2,3,4],[5,14,8,7],[9,10,11,12,13]]) (.forbid 5 10 1 (.system [[0,1,2,3,4],[7,6,5,14,10,11,12,13],[9]]) (.forbid 6 7 1 (.system [[0,1,2,3,4],[5,6,14,7],[9,10,11,12,13]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,5,6,8,10,12} 8 2) ∅ 15 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4,5,6,7} 8 2) ∅ 15 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4,5,6,7} 8 2) ∅ 15 3), .ball 5 (.succ (.succ (.zero ∅ 1 1) {0,1,3,4,6,8,10} 8 2) ∅ 15 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,4,5,7} 8 2) ∅ 15 3)})))))))))))))))

noncomputable def certificate_1012_part_1 : FiniteCertificate := .forbid 1 5 6 (.system [[0,1,14,15,16,17,18,19,5],[2],[4],[7],[9],[13]]) (.forbid 1 6 1 (.system [[0,1,14,6,5],[2,3,4],[7],[9,10,11,12,13]]) (.forbid 1 6 2 (.system [[0,1,14,15,6,5],[2],[4],[7],[9,10,11,12,13]]) (.forbid 1 6 3 (.system [[0,1,14,15,16,6,5],[2],[4],[7],[9,10,11,12,13]]) (.forbid 1 6 4 (.system [[0,1,14,15,16,17,6,5],[2,3,4],[7],[9],[13]]) (.forbid 1 6 5 (.system [[0,1,14,15,16,17,18,6,5],[2],[4],[7],[9],[13]]) (.forbid 1 6 6 (.system [[0,1,14,15,16,17,18,19,6,5],[2],[4],[7],[9],[13]]) (.forbid 1 7 1 (.system [[0,1,14,7,6,5],[2,3,4],[9,10,11,12,13]]) (.forbid 2 3 1 (.system [[0,1,2,14,3,4],[5,6,7],[9,10,11,12,13]]) (.forbid 2 6 1 (.system [[0,1,2,14,6,5],[4],[7,8,9,10,11,12,13]]) (.forbid 3 4 1 (.system [[0,1,2,3,14,4],[5,6,7],[9,10,11,12,13]]) (.forbid 3 5 1 (.system [[0,1,2,3,14,5,6,7],[4],[9,10,11,12,13]]) (.forbid 3 5 2 (.system [[0,1,2,3,14,15,5],[4],[7],[9,10,11,12,13]]) (.forbid 3 5 3 (.system [[0],[2,3,14,15,16,5],[4],[7],[9,10,11,12,13]]) (.forbid 3 5 4 (.system [[0],[2,3,14,15,16,17,5],[4],[7],[9,10,11,12,13]]) (.forbid 3 5 5 (.system [[0,1,2,3,14,15,16,17,18,5],[4],[7],[9],[13]]) (.forbid 3 5 6 (.system [[0],[2,3,14,15,16,17,18,19,5],[4],[7],[9],[13]]) (.forbid 3 6 1 (.system [[0,1,2,3,14,6,5],[4],[7],[9,10,11,12,13]]) (.forbid 3 6 2 (.system [[0],[2,3,14,15,6,5],[4],[7],[9,10,11,12,13]]) (.forbid 3 6 3 (.system [[0],[2,3,14,15,16,6,5],[4],[7],[9,10,11,12,13]]) (certificate_1012_part_0))))))))))))))))))))

noncomputable def certificate_1012_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[0,14,15,16,6,5],[2],[4],[7],[9,10,11,12,13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5],[2],[4],[7],[9,10,11,12,13]]) (.forbid 0 6 5 (.system [[2,1,0,14,15,16,17,18,6,5],[4],[7],[9],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[2],[4],[7],[9],[13]]) (.forbid 0 8 1 (.system [[4,3,2,1,0,14,8,7],[5],[9,10,11,12,13]]) (.forbid 0 10 1 (.system [[4,3,2,1,0,14,10,11,12,13],[5,6,7],[9]]) (.forbid 0 12 1 (.system [[4,3,2,1,0,14,12,11,10,9],[5,6,7],[13]]) (.forbid 1 2 1 (.system [[0,1,14,2,3,4],[5,6,7],[9,10,11,12,13]]) (.forbid 1 3 1 (.system [[0,1,14,3,2],[4],[5,6,7],[9,10,11,12,13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3,2],[4],[5],[7],[9,10,11,12,13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3,2],[4],[5],[7],[9,10,11,12,13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3,2],[4],[5,6,7],[9],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3,2],[4],[5],[7],[9],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3,2],[4],[5],[7],[9],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4,3,2],[5,6,7],[9,10,11,12,13]]) (.forbid 1 5 1 (.system [[0,1,14,5,6,7],[2,3,4],[9,10,11,12,13]]) (.forbid 1 5 2 (.system [[0,1,14,15,5],[2,3,4],[7],[9,10,11,12,13]]) (.forbid 1 5 3 (.system [[0,1,14,15,16,5],[2],[4],[7],[9,10,11,12,13]]) (.forbid 1 5 4 (.system [[0,1,14,15,16,17,5],[2],[4],[7],[9,10,11,12,13]]) (.forbid 1 5 5 (.system [[0,1,14,15,16,17,18,5],[2,3,4],[7],[9],[13]]) (certificate_1012_part_1))))))))))))))))))))

noncomputable def certificate_1012 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2,3,4],[5,6,7],[9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2,3,4],[5],[7],[9,10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2],[4],[5],[7],[9,10,11,12,13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[4],[5],[7],[9,10,11,12,13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2,3,4],[5],[7],[9],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[4],[5],[7],[9],[13]]) (.forbid 0 3 1 (.system [[0,14,3,2],[4],[5,6,7,8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[0,14,15,3,2],[4],[5,6,7],[9,10,11,12,13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3,2],[4],[5],[7],[9,10,11,12,13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3,2],[4],[5],[7],[9,10,11,12,13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3,2],[4],[5,6,7],[9],[13]]) (.forbid 0 3 6 (.system [[0,14,15,16,17,18,19,3,2],[4],[5],[7],[9],[13]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,14,5,6,7,8,9,10,11,12,13]]) (.forbid 0 5 2 (.system [[4,3,2,1,0,14,15,5],[7],[9,10,11,12,13]]) (.forbid 0 5 3 (.system [[2,1,0,14,15,16,5],[4],[7],[9,10,11,12,13]]) (.forbid 0 5 4 (.system [[0,14,15,16,17,5],[2],[4],[7],[9,10,11,12,13]]) (.forbid 0 5 5 (.system [[0,14,15,16,17,18,5],[2],[4],[7],[9,10,11,12,13]]) (.forbid 0 5 6 (.system [[2,1,0,14,15,16,17,18,19,5],[4],[7],[9],[13]]) (.forbid 0 6 1 (.system [[4,3,2,1,0,14,6,5],[7],[9,10,11,12,13]]) (.forbid 0 6 2 (.system [[2,1,0,14,15,6,5],[4],[7],[9,10,11,12,13]]) (certificate_1012_part_2))))))))))))))))))))

noncomputable def certificate_1013_q : Finset ℕ := ([0,2,4,5,7,10,12] : List ℕ).toFinset
noncomputable def certificate_1013_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(0,2),(0,4),(0,5),(0,7),(0,10),(0,12),(2,4),(2,5),(2,7),(2,10),(2,12),(4,5),(4,7),(4,10),(4,12),(5,7),(5,10),(5,12),(7,10),(7,12),(10,12)]

noncomputable def certificate_1013_part_0 : FiniteCertificate := .forbid 3 6 6 (.system [[0],[2,3,13,14,15,16,17,18,6,5],[4],[7],[10],[12]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,13,5,6,7,8,9,10,11,12]]) (.forbid 4 6 1 (.system [[0,1,2,3,4,13,6,5],[7,8,9,10],[12]]) (.forbid 5 6 1 (.system [[0,1,2,3,4],[5,13,6,7,8,9,10],[12]]) (.forbid 5 6 2 (.system [[0,1,2],[4],[5,13,14,6,7,8,9,10],[12]]) (.forbid 5 6 3 (.system [[0],[2],[4],[5,13,14,15,6,7,8,9,10],[12]]) (.forbid 5 6 4 (.system [[0,1,2],[4],[5,13,14,15,16,6,7],[10],[12]]) (.forbid 5 6 5 (.system [[0],[2],[4],[5,13,14,15,16,17,6,7],[10],[12]]) (.forbid 5 6 6 (.system [[0],[2],[4],[5,13,14,15,16,17,18,6,7],[10],[12]]) (.forbid 5 8 1 (.system [[0,1,2,3,4],[7,6,5,13,8,9,10],[12]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,3,5,6,8,9} 8 2) ∅ 16 3), .ball 1 (.succ (.succ (.zero ∅ 2 1) {0,2,3,4,5,6} 8 2) ∅ 16 3), .ball 3 (.succ (.succ (.zero ∅ 2 1) {0,1,2,4,5,6} 8 2) ∅ 16 3), .ball 5 (.succ (.succ (.zero ∅ 2 1) {0,1,3,4,6,8} 8 2) ∅ 16 3), .ball 6 (.succ (.succ (.zero ∅ 2 1) {0,1,2,3,4,5} 8 2) ∅ 16 3)}))))))))))

noncomputable def certificate_1013_part_1 : FiniteCertificate := .forbid 1 6 1 (.system [[0,1,13,6,5],[2,3,4],[7,8,9,10],[12]]) (.forbid 1 6 2 (.system [[0,1,13,14,6,5],[2],[4],[7,8,9,10],[12]]) (.forbid 1 6 3 (.system [[0,1,13,14,15,6,5],[2,3,4],[7],[10],[12]]) (.forbid 1 6 4 (.system [[0,1,13,14,15,16,6,5],[2],[4],[7],[10],[12]]) (.forbid 1 6 5 (.system [[0,1,13,14,15,16,17,6,5],[2],[4],[7],[10],[12]]) (.forbid 1 6 6 (.system [[0,1,13,14,15,16,17,18,6,5],[2],[4],[7],[10],[12]]) (.forbid 2 3 1 (.system [[0,1,2,13,3,4],[5,6,7,8,9,10],[12]]) (.forbid 2 6 1 (.system [[0,1,2,13,6,5],[4],[7,8,9,10,11,12]]) (.forbid 3 4 1 (.system [[0,1,2,3,13,4],[5,6,7,8,9,10],[12]]) (.forbid 3 5 1 (.system [[0,1,2,3,13,5,6,7,8,9,10],[4],[12]]) (.forbid 3 5 2 (.system [[0,1,2,3,13,14,5],[4],[7,8,9,10],[12]]) (.forbid 3 5 3 (.system [[0],[2,3,13,14,15,5],[4],[7,8,9,10],[12]]) (.forbid 3 5 4 (.system [[0,1,2,3,13,14,15,16,5],[4],[7],[10],[12]]) (.forbid 3 5 5 (.system [[0],[2,3,13,14,15,16,17,5],[4],[7],[10],[12]]) (.forbid 3 5 6 (.system [[0],[2,3,13,14,15,16,17,18,5],[4],[7],[10],[12]]) (.forbid 3 6 1 (.system [[0,1,2,3,13,6,5],[4],[7,8,9,10],[12]]) (.forbid 3 6 2 (.system [[0],[2,3,13,14,6,5],[4],[7,8,9,10],[12]]) (.forbid 3 6 3 (.system [[0,1,2,3,13,14,15,6,5],[4],[7],[10],[12]]) (.forbid 3 6 4 (.system [[0],[2,3,13,14,15,16,6,5],[4],[7],[10],[12]]) (.forbid 3 6 5 (.system [[0],[2,3,13,14,15,16,17,6,5],[4],[7],[10],[12]]) (certificate_1013_part_0))))))))))))))))))))

noncomputable def certificate_1013_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[0,13,14,15,6,5],[2],[4],[7,8,9,10],[12]]) (.forbid 0 6 4 (.system [[2,1,0,13,14,15,16,6,5],[4],[7],[10],[12]]) (.forbid 0 6 5 (.system [[0,13,14,15,16,17,6,5],[2],[4],[7],[10],[12]]) (.forbid 0 6 6 (.system [[0,13,14,15,16,17,18,6,5],[2],[4],[7],[10],[12]]) (.forbid 0 8 1 (.system [[4,3,2,1,0,13,8,9,10],[5,6,7],[12]]) (.forbid 0 9 1 (.system [[4,3,2,1,0,13,9,8,7,6,5],[10],[12]]) (.forbid 1 2 1 (.system [[0,1,13,2,3,4],[5,6,7,8,9,10],[12]]) (.forbid 1 3 1 (.system [[0,1,13,3,2],[4],[5,6,7,8,9,10],[12]]) (.forbid 1 3 2 (.system [[0,1,13,14,3,2],[4],[5],[7,8,9,10],[12]]) (.forbid 1 3 3 (.system [[0,1,13,14,15,3,2],[4],[5,6,7],[10],[12]]) (.forbid 1 3 4 (.system [[0,1,13,14,15,16,3,2],[4],[5],[7],[10],[12]]) (.forbid 1 3 5 (.system [[0,1,13,14,15,16,17,3,2],[4],[5],[7],[10],[12]]) (.forbid 1 3 6 (.system [[0,1,13,14,15,16,17,18,3,2],[4],[5],[7],[10],[12]]) (.forbid 1 4 1 (.system [[0,1,13,4,3,2],[5,6,7,8,9,10],[12]]) (.forbid 1 5 1 (.system [[0,1,13,5,6,7,8,9,10],[2,3,4],[12]]) (.forbid 1 5 2 (.system [[0,1,13,14,5],[2,3,4],[7,8,9,10],[12]]) (.forbid 1 5 3 (.system [[0,1,13,14,15,5],[2],[4],[7,8,9,10],[12]]) (.forbid 1 5 4 (.system [[0,1,13,14,15,16,5],[2,3,4],[7],[10],[12]]) (.forbid 1 5 5 (.system [[0,1,13,14,15,16,17,5],[2],[4],[7],[10],[12]]) (.forbid 1 5 6 (.system [[0,1,13,14,15,16,17,18,5],[2],[4],[7],[10],[12]]) (certificate_1013_part_1))))))))))))))))))))

noncomputable def certificate_1013 : FiniteCertificate := .forbid 0 1 1 (.system [[0,13,1,2,3,4],[5,6,7,8,9,10],[12]]) (.forbid 0 1 2 (.system [[0,13,14,1,2,3,4],[5],[7,8,9,10],[12]]) (.forbid 0 1 3 (.system [[0,13,14,15,1,2],[4],[5],[7,8,9,10],[12]]) (.forbid 0 1 4 (.system [[0,13,14,15,16,1,2,3,4],[5],[7],[10],[12]]) (.forbid 0 1 5 (.system [[0,13,14,15,16,17,1,2],[4],[5],[7],[10],[12]]) (.forbid 0 1 6 (.system [[0,13,14,15,16,17,18,1,2],[4],[5],[7],[10],[12]]) (.forbid 0 3 1 (.system [[0,13,3,2],[4],[5,6,7,8,9,10,11,12]]) (.forbid 0 3 2 (.system [[0,13,14,3,2],[4],[5,6,7,8,9,10],[12]]) (.forbid 0 3 3 (.system [[0,13,14,15,3,2],[4],[5],[7,8,9,10],[12]]) (.forbid 0 3 4 (.system [[0,13,14,15,16,3,2],[4],[5,6,7],[10],[12]]) (.forbid 0 3 5 (.system [[0,13,14,15,16,17,3,2],[4],[5],[7],[10],[12]]) (.forbid 0 3 6 (.system [[0,13,14,15,16,17,18,3,2],[4],[5],[7],[10],[12]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,13,5,6,7,8,9,10,11,12]]) (.forbid 0 5 2 (.system [[4,3,2,1,0,13,14,5],[7,8,9,10],[12]]) (.forbid 0 5 3 (.system [[2,1,0,13,14,15,5],[4],[7,8,9,10],[12]]) (.forbid 0 5 4 (.system [[0,13,14,15,16,5],[2],[4],[7,8,9,10],[12]]) (.forbid 0 5 5 (.system [[2,1,0,13,14,15,16,17,5],[4],[7],[10],[12]]) (.forbid 0 5 6 (.system [[0,13,14,15,16,17,18,5],[2],[4],[7],[10],[12]]) (.forbid 0 6 1 (.system [[4,3,2,1,0,13,6,5],[7,8,9,10],[12]]) (.forbid 0 6 2 (.system [[2,1,0,13,14,6,5],[4],[7,8,9,10],[12]]) (certificate_1013_part_2))))))))))))))))))))

noncomputable def certificate_1014_q : Finset ℕ := ([0,2,4,5,7,10,13] : List ℕ).toFinset
noncomputable def certificate_1014_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,10),(0,13),(2,4),(2,5),(2,7),(2,10),(2,13),(4,5),(4,7),(4,10),(4,13),(5,7),(5,10),(5,13),(7,10),(7,13),(10,13)]

noncomputable def certificate_1014_part_0 : FiniteCertificate := .forbid 3 6 4 (.system [[0,1,2,3,14,15,16,17,6,5],[4],[7],[10],[13]]) (.forbid 3 6 5 (.system [[0],[2,3,14,15,16,17,18,6,5],[4],[7],[10],[13]]) (.forbid 3 6 6 (.system [[0],[2,3,14,15,16,17,18,19,6,5],[4],[7],[10],[13]]) (.forbid 3 7 1 (.system [[0,1,2,3,14,7,8,9,10,11,12,13],[4],[5]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,14,5,6,7,8,9,10,11,12,13]]) (.forbid 4 6 1 (.system [[0,1,2],[4,14,6,5],[7,8,9,10,11,12,13]]) (.forbid 5 6 1 (.system [[0,1,2],[4],[5,14,6,7,8,9,10,11,12,13]]) (.forbid 5 6 2 (.system [[0],[2],[4],[5,14,15,6,7,8,9,10,11,12,13]]) (.forbid 5 6 3 (.system [[0,1,2],[4],[5,14,15,16,6,7,8,9,10],[13]]) (.forbid 5 6 4 (.system [[0],[2],[4],[5,14,15,16,17,6,7,8,9,10],[13]]) (.forbid 5 6 5 (.system [[0,1,2],[4],[5,14,15,16,17,18,6,7],[10],[13]]) (.forbid 5 6 6 (.system [[0],[2],[4],[5,14,15,16,17,18,19,6,7],[10],[13]]) (.forbid 5 8 1 (.system [[0,1,2,3,4],[5,14,8,9,10,11,12,13],[7]]) (.forbid 5 9 1 (.system [[0,1,2,3,4],[5,14,9,8,7],[10,11,12,13]]) (.forbid 6 7 1 (.system [[0,1,2],[4],[5,6,14,7,8,9,10,11,12,13]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,5,6,8,9,11} 8 2) ∅ 15 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4,5,6,7} 8 2) ∅ 15 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4,5,6,7} 8 2) ∅ 15 3), .ball 5 (.succ (.succ (.zero ∅ 1 1) {0,1,3,4,6,8,9} 8 2) ∅ 15 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,4,5,7} 8 2) ∅ 15 3)})))))))))))))))

noncomputable def certificate_1014_part_1 : FiniteCertificate := .forbid 1 5 6 (.system [[0,1,14,15,16,17,18,19,5],[2],[4],[7],[10],[13]]) (.forbid 1 6 1 (.system [[0,1,14,6,5],[2],[4],[7,8,9,10,11,12,13]]) (.forbid 1 6 2 (.system [[0,1,14,15,6,5],[2,3,4],[7,8,9,10],[13]]) (.forbid 1 6 3 (.system [[0,1,14,15,16,6,5],[2],[4],[7,8,9,10],[13]]) (.forbid 1 6 4 (.system [[0,1,14,15,16,17,6,5],[2,3,4],[7],[10],[13]]) (.forbid 1 6 5 (.system [[0,1,14,15,16,17,18,6,5],[2],[4],[7],[10],[13]]) (.forbid 1 6 6 (.system [[0,1,14,15,16,17,18,19,6,5],[2],[4],[7],[10],[13]]) (.forbid 1 7 1 (.system [[0,1,14,7,8,9,10,11,12,13],[2,3,4],[5]]) (.forbid 2 3 1 (.system [[0,1,2,14,3,4],[5],[7,8,9,10,11,12,13]]) (.forbid 2 6 1 (.system [[0,1,2,14,6,5],[4],[7,8,9,10,11,12,13]]) (.forbid 3 4 1 (.system [[0,1,2,3,14,4],[5],[7,8,9,10,11,12,13]]) (.forbid 3 5 1 (.system [[0,1,2,3,14,5],[4],[7,8,9,10,11,12,13]]) (.forbid 3 5 2 (.system [[0],[2,3,14,15,5],[4],[7,8,9,10,11,12,13]]) (.forbid 3 5 3 (.system [[0,1,2,3,14,15,16,5],[4],[7,8,9,10],[13]]) (.forbid 3 5 4 (.system [[0],[2,3,14,15,16,17,5],[4],[7,8,9,10],[13]]) (.forbid 3 5 5 (.system [[0,1,2,3,14,15,16,17,18,5],[4],[7],[10],[13]]) (.forbid 3 5 6 (.system [[0],[2,3,14,15,16,17,18,19,5],[4],[7],[10],[13]]) (.forbid 3 6 1 (.system [[0],[2,3,14,6,5],[4],[7,8,9,10,11,12,13]]) (.forbid 3 6 2 (.system [[0,1,2,3,14,15,6,5],[4],[7,8,9,10],[13]]) (.forbid 3 6 3 (.system [[0],[2,3,14,15,16,6,5],[4],[7,8,9,10],[13]]) (certificate_1014_part_0))))))))))))))))))))

noncomputable def certificate_1014_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,14,15,16,6,5],[4],[7,8,9,10],[13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5],[2],[4],[7,8,9,10],[13]]) (.forbid 0 6 5 (.system [[2,1,0,14,15,16,17,18,6,5],[4],[7],[10],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[2],[4],[7],[10],[13]]) (.forbid 0 8 1 (.system [[4,3,2,1,0,14,8,9,10,11,12,13],[5],[7]]) (.forbid 0 9 1 (.system [[4,3,2,1,0,14,9,8,7],[5],[10,11,12,13]]) (.forbid 0 11 1 (.system [[4,3,2,1,0,14,11,12,13],[5],[7,8,9,10]]) (.forbid 1 2 1 (.system [[0,1,14,2,3,4],[5],[7,8,9,10,11,12,13]]) (.forbid 1 3 1 (.system [[0,1,14,3,2],[4],[5],[7,8,9,10,11,12,13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3,2],[4],[5,6,7,8,9,10],[13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3,2],[4],[5],[7,8,9,10],[13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3,2],[4],[5,6,7],[10],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3,2],[4],[5],[7],[10],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3,2],[4],[5],[7],[10],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4,3,2],[5],[7,8,9,10,11,12,13]]) (.forbid 1 5 1 (.system [[0,1,14,5],[2,3,4],[7,8,9,10,11,12,13]]) (.forbid 1 5 2 (.system [[0,1,14,15,5],[2],[4],[7,8,9,10,11,12,13]]) (.forbid 1 5 3 (.system [[0,1,14,15,16,5],[2,3,4],[7,8,9,10],[13]]) (.forbid 1 5 4 (.system [[0,1,14,15,16,17,5],[2],[4],[7,8,9,10],[13]]) (.forbid 1 5 5 (.system [[0,1,14,15,16,17,18,5],[2,3,4],[7],[10],[13]]) (certificate_1014_part_1))))))))))))))))))))

noncomputable def certificate_1014 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2,3,4],[5],[7,8,9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2],[4],[5],[7,8,9,10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2,3,4],[5],[7,8,9,10],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[4],[5],[7,8,9,10],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2,3,4],[5],[7],[10],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[4],[5],[7],[10],[13]]) (.forbid 0 3 1 (.system [[0,14,3,2],[4],[5,6,7,8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[0,14,15,3,2],[4],[5],[7,8,9,10,11,12,13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3,2],[4],[5,6,7,8,9,10],[13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3,2],[4],[5],[7,8,9,10],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3,2],[4],[5,6,7],[10],[13]]) (.forbid 0 3 6 (.system [[0,14,15,16,17,18,19,3,2],[4],[5],[7],[10],[13]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,14,5,6,7,8,9,10,11,12,13]]) (.forbid 0 5 2 (.system [[2,1,0,14,15,5],[4],[7,8,9,10,11,12,13]]) (.forbid 0 5 3 (.system [[0,14,15,16,5],[2],[4],[7,8,9,10,11,12,13]]) (.forbid 0 5 4 (.system [[2,1,0,14,15,16,17,5],[4],[7,8,9,10],[13]]) (.forbid 0 5 5 (.system [[0,14,15,16,17,18,5],[2],[4],[7,8,9,10],[13]]) (.forbid 0 5 6 (.system [[2,1,0,14,15,16,17,18,19,5],[4],[7],[10],[13]]) (.forbid 0 6 1 (.system [[2,1,0,14,6,5],[4],[7,8,9,10,11,12,13]]) (.forbid 0 6 2 (.system [[0,14,15,6,5],[2],[4],[7,8,9,10,11,12,13]]) (certificate_1014_part_2))))))))))))))))))))

noncomputable def certificate_1015_q : Finset ℕ := ([0,2,4,5,7,11,13] : List ℕ).toFinset
noncomputable def certificate_1015_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,7),(0,11),(0,13),(2,4),(2,5),(2,7),(2,11),(2,13),(4,5),(4,7),(4,11),(4,13),(5,7),(5,11),(5,13),(7,11),(7,13),(11,13)]

noncomputable def certificate_1015_part_0 : FiniteCertificate := .forbid 3 6 4 (.system [[0,1,2,3,14,15,16,17,6,5],[4],[7],[11],[13]]) (.forbid 3 6 5 (.system [[0],[2,3,14,15,16,17,18,6,5],[4],[7],[11],[13]]) (.forbid 3 6 6 (.system [[0],[2,3,14,15,16,17,18,19,6,5],[4],[7],[11],[13]]) (.forbid 3 7 1 (.system [[0,1,2,3,14,7,8,9,10,11,12,13],[4],[5]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,14,5,6,7,8,9,10,11,12,13]]) (.forbid 4 6 1 (.system [[0,1,2,3,4,14,6,5],[7,8,9,10,11],[13]]) (.forbid 5 6 1 (.system [[0,1,2,3,4],[5,14,6,7,8,9,10,11],[13]]) (.forbid 5 6 2 (.system [[0,1,2],[4],[5,14,15,6,7,8,9,10,11],[13]]) (.forbid 5 6 3 (.system [[0],[2],[4],[5,14,15,16,6,7,8,9,10,11],[13]]) (.forbid 5 6 4 (.system [[0],[2],[4],[5,14,15,16,17,6,7,8,9,10,11],[13]]) (.forbid 5 6 5 (.system [[0,1,2],[4],[5,14,15,16,17,18,6,7],[11],[13]]) (.forbid 5 6 6 (.system [[0],[2],[4],[5,14,15,16,17,18,19,6,7],[11],[13]]) (.forbid 5 8 1 (.system [[0,1,2,3,4],[7,6,5,14,8,9,10,11],[13]]) (.forbid 5 10 1 (.system [[0,1,2,3,4],[5,14,10,9,8,7],[11,12,13]]) (.forbid 6 7 1 (.system [[0,1,2,3,4],[5,6,14,7,8,9,10,11],[13]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,5,6,8,10,12} 8 2) ∅ 15 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4,5,6,7} 8 2) ∅ 15 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4,5,6,7} 8 2) ∅ 15 3), .ball 5 (.succ (.succ (.zero ∅ 1 1) {0,1,3,4,6,8,10} 8 2) ∅ 15 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,4,5,7} 8 2) ∅ 15 3)})))))))))))))))

noncomputable def certificate_1015_part_1 : FiniteCertificate := .forbid 1 5 6 (.system [[0,1,14,15,16,17,18,19,5],[2],[4],[7],[11],[13]]) (.forbid 1 6 1 (.system [[0,1,14,6,5],[2,3,4],[7,8,9,10,11],[13]]) (.forbid 1 6 2 (.system [[0,1,14,15,6,5],[2],[4],[7,8,9,10,11],[13]]) (.forbid 1 6 3 (.system [[0,1,14,15,16,6,5],[2],[4],[7,8,9,10,11],[13]]) (.forbid 1 6 4 (.system [[0,1,14,15,16,17,6,5],[2,3,4],[7],[11],[13]]) (.forbid 1 6 5 (.system [[0,1,14,15,16,17,18,6,5],[2],[4],[7],[11],[13]]) (.forbid 1 6 6 (.system [[0,1,14,15,16,17,18,19,6,5],[2],[4],[7],[11],[13]]) (.forbid 1 7 1 (.system [[0,1,14,7,8,9,10,11,12,13],[2,3,4],[5]]) (.forbid 2 3 1 (.system [[0,1,2,14,3,4],[5,6,7,8,9,10,11],[13]]) (.forbid 2 6 1 (.system [[0,1,2,14,6,5],[4],[7,8,9,10,11,12,13]]) (.forbid 3 4 1 (.system [[0,1,2,3,14,4],[5,6,7,8,9,10,11],[13]]) (.forbid 3 5 1 (.system [[0,1,2,3,14,5,6,7,8,9,10,11],[4],[13]]) (.forbid 3 5 2 (.system [[0,1,2,3,14,15,5],[4],[7,8,9,10,11],[13]]) (.forbid 3 5 3 (.system [[0],[2,3,14,15,16,5],[4],[7,8,9,10,11],[13]]) (.forbid 3 5 4 (.system [[0],[2,3,14,15,16,17,5],[4],[7,8,9,10,11],[13]]) (.forbid 3 5 5 (.system [[0,1,2,3,14,15,16,17,18,5],[4],[7],[11],[13]]) (.forbid 3 5 6 (.system [[0],[2,3,14,15,16,17,18,19,5],[4],[7],[11],[13]]) (.forbid 3 6 1 (.system [[0,1,2,3,14,6,5],[4],[7,8,9,10,11],[13]]) (.forbid 3 6 2 (.system [[0],[2,3,14,15,6,5],[4],[7,8,9,10,11],[13]]) (.forbid 3 6 3 (.system [[0],[2,3,14,15,16,6,5],[4],[7,8,9,10,11],[13]]) (certificate_1015_part_0))))))))))))))))))))

noncomputable def certificate_1015_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[0,14,15,16,6,5],[2],[4],[7,8,9,10,11],[13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5],[2],[4],[7,8,9,10,11],[13]]) (.forbid 0 6 5 (.system [[2,1,0,14,15,16,17,18,6,5],[4],[7],[11],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[2],[4],[7],[11],[13]]) (.forbid 0 8 1 (.system [[4,3,2,1,0,14,8,9,10,11],[5,6,7],[13]]) (.forbid 0 10 1 (.system [[4,3,2,1,0,14,10,9,8,7,6,5],[11],[13]]) (.forbid 0 12 1 (.system [[4,3,2,1,0,14,12,11,10,9,8,7],[5],[13]]) (.forbid 1 2 1 (.system [[0,1,14,2,3,4],[5,6,7,8,9,10,11],[13]]) (.forbid 1 3 1 (.system [[0,1,14,3,2],[4],[5,6,7,8,9,10,11],[13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3,2],[4],[5],[7,8,9,10,11],[13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3,2],[4],[5],[7,8,9,10,11],[13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3,2],[4],[5,6,7],[11],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3,2],[4],[5],[7],[11],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3,2],[4],[5],[7],[11],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4,3,2],[5,6,7,8,9,10,11],[13]]) (.forbid 1 5 1 (.system [[0,1,14,5,6,7,8,9,10,11],[2,3,4],[13]]) (.forbid 1 5 2 (.system [[0,1,14,15,5],[2,3,4],[7,8,9,10,11],[13]]) (.forbid 1 5 3 (.system [[0,1,14,15,16,5],[2],[4],[7,8,9,10,11],[13]]) (.forbid 1 5 4 (.system [[0,1,14,15,16,17,5],[2],[4],[7,8,9,10,11],[13]]) (.forbid 1 5 5 (.system [[0,1,14,15,16,17,18,5],[2,3,4],[7],[11],[13]]) (certificate_1015_part_1))))))))))))))))))))

noncomputable def certificate_1015 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2,3,4],[5,6,7,8,9,10,11],[13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2,3,4],[5],[7,8,9,10,11],[13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2],[4],[5],[7,8,9,10,11],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[4],[5],[7,8,9,10,11],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2,3,4],[5],[7],[11],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[4],[5],[7],[11],[13]]) (.forbid 0 3 1 (.system [[0,14,3,2],[4],[5,6,7,8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[0,14,15,3,2],[4],[5,6,7,8,9,10,11],[13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3,2],[4],[5],[7,8,9,10,11],[13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3,2],[4],[5],[7,8,9,10,11],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3,2],[4],[5,6,7],[11],[13]]) (.forbid 0 3 6 (.system [[0,14,15,16,17,18,19,3,2],[4],[5],[7],[11],[13]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,14,5,6,7,8,9,10,11,12,13]]) (.forbid 0 5 2 (.system [[4,3,2,1,0,14,15,5],[7,8,9,10,11],[13]]) (.forbid 0 5 3 (.system [[2,1,0,14,15,16,5],[4],[7,8,9,10,11],[13]]) (.forbid 0 5 4 (.system [[0,14,15,16,17,5],[2],[4],[7,8,9,10,11],[13]]) (.forbid 0 5 5 (.system [[0,14,15,16,17,18,5],[2],[4],[7,8,9,10,11],[13]]) (.forbid 0 5 6 (.system [[2,1,0,14,15,16,17,18,19,5],[4],[7],[11],[13]]) (.forbid 0 6 1 (.system [[4,3,2,1,0,14,6,5],[7,8,9,10,11],[13]]) (.forbid 0 6 2 (.system [[2,1,0,14,15,6,5],[4],[7,8,9,10,11],[13]]) (certificate_1015_part_2))))))))))))))))))))

noncomputable def certificate_1016_q : Finset ℕ := ([0,2,4,5,8,9,12] : List ℕ).toFinset
noncomputable def certificate_1016_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(0,2),(0,4),(0,5),(0,8),(0,9),(0,12),(2,4),(2,5),(2,8),(2,9),(2,12),(4,5),(4,8),(4,9),(4,12),(5,8),(5,9),(5,12),(8,9),(8,12),(9,12)]

noncomputable def certificate_1016_part_0 : FiniteCertificate := .forbid 3 6 6 (.system [[0],[2,3,13,14,15,16,17,18,6,5],[4],[8],[9],[12]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,13,5,6,7,8],[9,10,11,12]]) (.forbid 4 6 1 (.system [[0,1,2],[4,13,6,7,8],[5],[9,10,11,12]]) (.forbid 5 6 1 (.system [[0,1,2],[4],[5,13,6,7,8],[9,10,11,12]]) (.forbid 5 6 2 (.system [[0],[2],[4],[5,13,14,6,7,8],[9,10,11,12]]) (.forbid 5 6 3 (.system [[0,1,2],[4],[5,13,14,15,6,7,8],[9],[12]]) (.forbid 5 6 4 (.system [[0],[2],[4],[5,13,14,15,16,6,7,8],[9],[12]]) (.forbid 5 6 5 (.system [[0],[2],[4],[5,13,14,15,16,17,6,7,8],[9],[12]]) (.forbid 5 6 6 (.system [[0],[2],[4],[5,13,14,15,16,17,18,6,7,8],[9],[12]]) (.forbid 5 9 1 (.system [[0,1,2,3,4],[8,7,6,5,13,9,10,11,12]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,3,5,6,7,8} 8 2) ∅ 16 3), .ball 1 (.succ (.succ (.zero ∅ 2 1) {0,2,3,4,5,6} 8 2) ∅ 16 3), .ball 3 (.succ (.succ (.zero ∅ 2 1) {0,1,2,4,5,6} 8 2) ∅ 16 3), .ball 5 (.succ (.succ (.zero ∅ 2 1) {0,1,3,4,6,9} 8 2) ∅ 16 3), .ball 6 (.succ (.succ (.zero ∅ 2 1) {0,1,2,3,4,5} 8 2) ∅ 16 3)}))))))))))

noncomputable def certificate_1016_part_1 : FiniteCertificate := .forbid 1 6 1 (.system [[0,1,13,6,5],[2,3,4],[8],[9,10,11,12]]) (.forbid 1 6 2 (.system [[0,1,13,14,6,5],[2],[4],[8],[9,10,11,12]]) (.forbid 1 6 3 (.system [[0,1,13,14,15,6,5],[2,3,4],[8],[9],[12]]) (.forbid 1 6 4 (.system [[0,1,13,14,15,16,6,5],[2],[4],[8],[9],[12]]) (.forbid 1 6 5 (.system [[0,1,13,14,15,16,17,6,5],[2],[4],[8],[9],[12]]) (.forbid 1 6 6 (.system [[0,1,13,14,15,16,17,18,6,5],[2],[4],[8],[9],[12]]) (.forbid 2 3 1 (.system [[0],[2,13,3,4],[5,6,7,8],[9,10,11,12]]) (.forbid 2 6 1 (.system [[0,1,2,13,6,7,8],[4],[5],[9,10,11,12]]) (.forbid 3 4 1 (.system [[0],[2,3,13,4],[5,6,7,8],[9,10,11,12]]) (.forbid 3 5 1 (.system [[0],[2,3,13,5,6,7,8],[4],[9,10,11,12]]) (.forbid 3 5 2 (.system [[0,1,2,3,13,14,5,6,7,8],[4],[9],[12]]) (.forbid 3 5 3 (.system [[0],[2,3,13,14,15,5,6,7,8],[4],[9],[12]]) (.forbid 3 5 4 (.system [[0,1,2,3,13,14,15,16,5],[4],[8],[9],[12]]) (.forbid 3 5 5 (.system [[0],[2,3,13,14,15,16,17,5],[4],[8],[9],[12]]) (.forbid 3 5 6 (.system [[0],[2,3,13,14,15,16,17,18,5],[4],[8],[9],[12]]) (.forbid 3 6 1 (.system [[0,1,2,3,13,6,5],[4],[8],[9,10,11,12]]) (.forbid 3 6 2 (.system [[0],[2,3,13,14,6,5],[4],[8],[9,10,11,12]]) (.forbid 3 6 3 (.system [[0,1,2,3,13,14,15,6,5],[4],[8],[9],[12]]) (.forbid 3 6 4 (.system [[0],[2,3,13,14,15,16,6,5],[4],[8],[9],[12]]) (.forbid 3 6 5 (.system [[0],[2,3,13,14,15,16,17,6,5],[4],[8],[9],[12]]) (certificate_1016_part_0))))))))))))))))))))

noncomputable def certificate_1016_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[0,13,14,15,6,5],[2],[4],[8],[9,10,11,12]]) (.forbid 0 6 4 (.system [[2,1,0,13,14,15,16,6,5],[4],[8],[9],[12]]) (.forbid 0 6 5 (.system [[0,13,14,15,16,17,6,5],[2],[4],[8],[9],[12]]) (.forbid 0 6 6 (.system [[0,13,14,15,16,17,18,6,5],[2],[4],[8],[9],[12]]) (.forbid 0 7 1 (.system [[2,1,0,13,7,6,5],[4],[8],[9,10,11,12]]) (.forbid 0 8 1 (.system [[4,3,2,1,0,13,8,7,6,5],[9,10,11,12]]) (.forbid 1 2 1 (.system [[0,1,13,2],[4],[5,6,7,8],[9,10,11,12]]) (.forbid 1 3 1 (.system [[0,1,13,3,2],[4],[5,6,7,8],[9,10,11,12]]) (.forbid 1 3 2 (.system [[0,1,13,14,3,2],[4],[5,6,7,8],[9],[12]]) (.forbid 1 3 3 (.system [[0,1,13,14,15,3,2],[4],[5,6,7,8],[9],[12]]) (.forbid 1 3 4 (.system [[0,1,13,14,15,16,3,2],[4],[5],[8],[9],[12]]) (.forbid 1 3 5 (.system [[0,1,13,14,15,16,17,3,2],[4],[5],[8],[9],[12]]) (.forbid 1 3 6 (.system [[0,1,13,14,15,16,17,18,3,2],[4],[5],[8],[9],[12]]) (.forbid 1 4 1 (.system [[0,1,13,4],[2],[5,6,7,8],[9,10,11,12]]) (.forbid 1 5 1 (.system [[0,1,13,5,6,7,8],[2],[4],[9,10,11,12]]) (.forbid 1 5 2 (.system [[0,1,13,14,5,6,7,8],[2,3,4],[9],[12]]) (.forbid 1 5 3 (.system [[0,1,13,14,15,5,6,7,8],[2],[4],[9],[12]]) (.forbid 1 5 4 (.system [[0,1,13,14,15,16,5],[2,3,4],[8],[9],[12]]) (.forbid 1 5 5 (.system [[0,1,13,14,15,16,17,5],[2],[4],[8],[9],[12]]) (.forbid 1 5 6 (.system [[0,1,13,14,15,16,17,18,5],[2],[4],[8],[9],[12]]) (certificate_1016_part_1))))))))))))))))))))

noncomputable def certificate_1016 : FiniteCertificate := .forbid 0 1 1 (.system [[0,13,1,2],[4],[5,6,7,8],[9,10,11,12]]) (.forbid 0 1 2 (.system [[0,13,14,1,2,3,4],[5,6,7,8],[9],[12]]) (.forbid 0 1 3 (.system [[0,13,14,15,1,2],[4],[5,6,7,8],[9],[12]]) (.forbid 0 1 4 (.system [[0,13,14,15,16,1,2,3,4],[5],[8],[9],[12]]) (.forbid 0 1 5 (.system [[0,13,14,15,16,17,1,2],[4],[5],[8],[9],[12]]) (.forbid 0 1 6 (.system [[0,13,14,15,16,17,18,1,2],[4],[5],[8],[9],[12]]) (.forbid 0 3 1 (.system [[0,13,3,2],[4],[5,6,7,8],[9,10,11,12]]) (.forbid 0 3 2 (.system [[0,13,14,3,2],[4],[5,6,7,8],[9,10,11,12]]) (.forbid 0 3 3 (.system [[0,13,14,15,3,2],[4],[5,6,7,8],[9],[12]]) (.forbid 0 3 4 (.system [[0,13,14,15,16,3,2],[4],[5,6,7,8],[9],[12]]) (.forbid 0 3 5 (.system [[0,13,14,15,16,17,3,2],[4],[5],[8],[9],[12]]) (.forbid 0 3 6 (.system [[0,13,14,15,16,17,18,3,2],[4],[5],[8],[9],[12]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,13,5,6,7,8],[9,10,11,12]]) (.forbid 0 5 2 (.system [[0,13,14,5,6,7,8],[2],[4],[9,10,11,12]]) (.forbid 0 5 3 (.system [[2,1,0,13,14,15,5,6,7,8],[4],[9],[12]]) (.forbid 0 5 4 (.system [[0,13,14,15,16,5,6,7,8],[2],[4],[9],[12]]) (.forbid 0 5 5 (.system [[2,1,0,13,14,15,16,17,5],[4],[8],[9],[12]]) (.forbid 0 5 6 (.system [[0,13,14,15,16,17,18,5],[2],[4],[8],[9],[12]]) (.forbid 0 6 1 (.system [[2,1,0,13,6,7,8],[4],[5],[9,10,11,12]]) (.forbid 0 6 2 (.system [[2,1,0,13,14,6,5],[4],[8],[9,10,11,12]]) (certificate_1016_part_2))))))))))))))))))))

noncomputable def certificate_1017_q : Finset ℕ := ([0,2,4,5,8,9,13] : List ℕ).toFinset
noncomputable def certificate_1017_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,8),(0,9),(0,13),(2,4),(2,5),(2,8),(2,9),(2,13),(4,5),(4,8),(4,9),(4,13),(5,8),(5,9),(5,13),(8,9),(8,13),(9,13)]

noncomputable def certificate_1017_part_0 : FiniteCertificate := .forbid 3 6 4 (.system [[0,1,2,3,14,15,16,17,6,5],[4],[8],[9],[13]]) (.forbid 3 6 5 (.system [[0],[2,3,14,15,16,17,18,6,5],[4],[8],[9],[13]]) (.forbid 3 6 6 (.system [[0],[2,3,14,15,16,17,18,19,6,5],[4],[8],[9],[13]]) (.forbid 3 7 1 (.system [[0],[2,3,14,7,6,5],[4],[8],[9,10,11,12,13]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,14,5,6,7,8],[9,10,11,12,13]]) (.forbid 4 6 1 (.system [[0,1,2],[4,14,6,7,8],[5],[9,10,11,12,13]]) (.forbid 5 6 1 (.system [[0,1,2],[4],[5,14,6,7,8],[9,10,11,12,13]]) (.forbid 5 6 2 (.system [[0],[2],[4],[5,14,15,6,7,8],[9,10,11,12,13]]) (.forbid 5 6 3 (.system [[0],[2],[4],[5,14,15,16,6,7,8],[9,10,11,12,13]]) (.forbid 5 6 4 (.system [[0,1,2],[4],[5,14,15,16,17,6,7,8],[9],[13]]) (.forbid 5 6 5 (.system [[0],[2],[4],[5,14,15,16,17,18,6,7,8],[9],[13]]) (.forbid 5 6 6 (.system [[0],[2],[4],[5,14,15,16,17,18,19,6,7,8],[9],[13]]) (.forbid 5 9 1 (.system [[0,1,2,3,4],[8,7,6,5,14,9,10,11,12,13]]) (.forbid 5 10 1 (.system [[0,1,2],[4],[8,7,6,5,14,10,11,12,13],[9]]) (.forbid 6 7 1 (.system [[0,1,2],[4],[5,6,14,7,8],[9,10,11,12,13]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,5,6,7,8,9} 8 2) ∅ 15 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4,5,6,7} 8 2) ∅ 15 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4,5,6,7} 8 2) ∅ 15 3), .ball 5 (.succ (.succ (.zero ∅ 1 1) {0,1,3,4,6,9,10} 8 2) ∅ 15 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,4,5,7} 8 2) ∅ 15 3)})))))))))))))))

noncomputable def certificate_1017_part_1 : FiniteCertificate := .forbid 1 5 6 (.system [[0,1,14,15,16,17,18,19,5],[2],[4],[8],[9],[13]]) (.forbid 1 6 1 (.system [[0,1,14,6,5],[2,3,4],[8],[9,10,11,12,13]]) (.forbid 1 6 2 (.system [[0,1,14,15,6,5],[2],[4],[8],[9,10,11,12,13]]) (.forbid 1 6 3 (.system [[0,1,14,15,16,6,5],[2],[4],[8],[9,10,11,12,13]]) (.forbid 1 6 4 (.system [[0,1,14,15,16,17,6,5],[2,3,4],[8],[9],[13]]) (.forbid 1 6 5 (.system [[0,1,14,15,16,17,18,6,5],[2],[4],[8],[9],[13]]) (.forbid 1 6 6 (.system [[0,1,14,15,16,17,18,19,6,5],[2],[4],[8],[9],[13]]) (.forbid 1 7 1 (.system [[0,1,14,7,6,5],[2],[4],[8],[9,10,11,12,13]]) (.forbid 2 3 1 (.system [[0],[2,14,3,4],[5,6,7,8],[9,10,11,12,13]]) (.forbid 2 6 1 (.system [[0,1,2,14,6,7,8],[4],[5],[9,10,11,12,13]]) (.forbid 3 4 1 (.system [[0],[2,3,14,4],[5,6,7,8],[9,10,11,12,13]]) (.forbid 3 5 1 (.system [[0],[2,3,14,5,6,7,8],[4],[9,10,11,12,13]]) (.forbid 3 5 2 (.system [[0,1,2,3,14,15,5],[4],[8],[9,10,11,12,13]]) (.forbid 3 5 3 (.system [[0],[2,3,14,15,16,5],[4],[8],[9,10,11,12,13]]) (.forbid 3 5 4 (.system [[0],[2,3,14,15,16,17,5,6,7,8],[4],[9],[13]]) (.forbid 3 5 5 (.system [[0,1,2,3,14,15,16,17,18,5],[4],[8],[9],[13]]) (.forbid 3 5 6 (.system [[0],[2,3,14,15,16,17,18,19,5],[4],[8],[9],[13]]) (.forbid 3 6 1 (.system [[0,1,2,3,14,6,5],[4],[8],[9,10,11,12,13]]) (.forbid 3 6 2 (.system [[0],[2,3,14,15,6,5],[4],[8],[9,10,11,12,13]]) (.forbid 3 6 3 (.system [[0],[2,3,14,15,16,6,5],[4],[8],[9,10,11,12,13]]) (certificate_1017_part_0))))))))))))))))))))

noncomputable def certificate_1017_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[0,14,15,16,6,5],[2],[4],[8],[9,10,11,12,13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5],[2],[4],[8],[9,10,11,12,13]]) (.forbid 0 6 5 (.system [[2,1,0,14,15,16,17,18,6,5],[4],[8],[9],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[2],[4],[8],[9],[13]]) (.forbid 0 7 1 (.system [[2,1,0,14,7,6,5],[4],[8],[9,10,11,12,13]]) (.forbid 0 8 1 (.system [[4,3,2,1,0,14,8,7,6,5],[9,10,11,12,13]]) (.forbid 0 9 1 (.system [[4,3,2,1,0,14,9,10,11,12,13],[5,6,7,8]]) (.forbid 1 2 1 (.system [[0,1,14,2],[4],[5,6,7,8],[9,10,11,12,13]]) (.forbid 1 3 1 (.system [[0,1,14,3,2],[4],[5,6,7,8],[9,10,11,12,13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3,2],[4],[5],[8],[9,10,11,12,13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3,2],[4],[5,6,7,8],[9],[13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3,2],[4],[5,6,7,8],[9],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3,2],[4],[5],[8],[9],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3,2],[4],[5],[8],[9],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4],[2],[5,6,7,8],[9,10,11,12,13]]) (.forbid 1 5 1 (.system [[0,1,14,5,6,7,8],[2],[4],[9,10,11,12,13]]) (.forbid 1 5 2 (.system [[0,1,14,15,5],[2,3,4],[8],[9,10,11,12,13]]) (.forbid 1 5 3 (.system [[0,1,14,15,16,5],[2],[4],[8],[9,10,11,12,13]]) (.forbid 1 5 4 (.system [[0,1,14,15,16,17,5,6,7,8],[2],[4],[9],[13]]) (.forbid 1 5 5 (.system [[0,1,14,15,16,17,18,5],[2,3,4],[8],[9],[13]]) (certificate_1017_part_1))))))))))))))))))))

noncomputable def certificate_1017 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2],[4],[5,6,7,8],[9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2,3,4],[5],[8],[9,10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2],[4],[5],[8],[9,10,11,12,13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[4],[5,6,7,8],[9],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2,3,4],[5],[8],[9],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[4],[5],[8],[9],[13]]) (.forbid 0 3 1 (.system [[0,14,3,2],[4],[5,6,7,8],[9,10,11,12,13]]) (.forbid 0 3 2 (.system [[0,14,15,3,2],[4],[5,6,7,8],[9,10,11,12,13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3,2],[4],[5],[8],[9,10,11,12,13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3,2],[4],[5,6,7,8],[9],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3,2],[4],[5,6,7,8],[9],[13]]) (.forbid 0 3 6 (.system [[0,14,15,16,17,18,19,3,2],[4],[5],[8],[9],[13]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,14,5,6,7,8],[9,10,11,12,13]]) (.forbid 0 5 2 (.system [[0,14,15,5,6,7,8],[2],[4],[9,10,11,12,13]]) (.forbid 0 5 3 (.system [[2,1,0,14,15,16,5],[4],[8],[9,10,11,12,13]]) (.forbid 0 5 4 (.system [[0,14,15,16,17,5],[2],[4],[8],[9,10,11,12,13]]) (.forbid 0 5 5 (.system [[0,14,15,16,17,18,5,6,7,8],[2],[4],[9],[13]]) (.forbid 0 5 6 (.system [[2,1,0,14,15,16,17,18,19,5],[4],[8],[9],[13]]) (.forbid 0 6 1 (.system [[2,1,0,14,6,7,8],[4],[5],[9,10,11,12,13]]) (.forbid 0 6 2 (.system [[2,1,0,14,15,6,5],[4],[8],[9,10,11,12,13]]) (certificate_1017_part_2))))))))))))))))))))

noncomputable def certificate_1018_q : Finset ℕ := ([0,2,4,5,8,10,13] : List ℕ).toFinset
noncomputable def certificate_1018_edges : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(0,2),(0,4),(0,5),(0,8),(0,10),(0,13),(2,4),(2,5),(2,8),(2,10),(2,13),(4,5),(4,8),(4,10),(4,13),(5,8),(5,10),(5,13),(8,10),(8,13),(10,13)]

noncomputable def certificate_1018_part_0 : FiniteCertificate := .forbid 3 6 4 (.system [[0,1,2,3,14,15,16,17,6,5],[4],[8],[10],[13]]) (.forbid 3 6 5 (.system [[0],[2,3,14,15,16,17,18,6,5],[4],[8],[10],[13]]) (.forbid 3 6 6 (.system [[0],[2,3,14,15,16,17,18,19,6,5],[4],[8],[10],[13]]) (.forbid 3 7 1 (.system [[0,1,2,3,14,7,6,5],[4],[8],[10,11,12,13]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,14,5,6,7,8,9,10,11,12,13]]) (.forbid 4 6 1 (.system [[0,1,2,3,4,14,6,7,8],[5],[10,11,12,13]]) (.forbid 5 6 1 (.system [[0,1,2,3,4],[5,14,6,7,8],[10,11,12,13]]) (.forbid 5 6 2 (.system [[0,1,2],[4],[5,14,15,6,7,8],[10,11,12,13]]) (.forbid 5 6 3 (.system [[0],[2],[4],[5,14,15,16,6,7,8],[10,11,12,13]]) (.forbid 5 6 4 (.system [[0,1,2],[4],[5,14,15,16,17,6,7,8],[10],[13]]) (.forbid 5 6 5 (.system [[0],[2],[4],[5,14,15,16,17,18,6,7,8],[10],[13]]) (.forbid 5 6 6 (.system [[0],[2],[4],[5,14,15,16,17,18,19,6,7,8],[10],[13]]) (.forbid 5 9 1 (.system [[0,1,2],[4],[8,7,6,5,14,9,10,11,12,13]]) (.forbid 5 11 1 (.system [[0,1,2,3,4],[8,7,6,5,14,11,12,13],[10]]) (.forbid 6 7 1 (.system [[0,1,2,3,4],[5,6,14,7,8],[10,11,12,13]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,3,5,6,7,9,11} 8 2) ∅ 15 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,4,5,6,7} 8 2) ∅ 15 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,4,5,6,7} 8 2) ∅ 15 3), .ball 5 (.succ (.succ (.zero ∅ 1 1) {0,1,3,4,6,9,11} 8 2) ∅ 15 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3,4,5,7} 8 2) ∅ 15 3)})))))))))))))))

noncomputable def certificate_1018_part_1 : FiniteCertificate := .forbid 1 5 6 (.system [[0,1,14,15,16,17,18,19,5],[2],[4],[8],[10],[13]]) (.forbid 1 6 1 (.system [[0,1,14,6,5],[2,3,4],[8,9,10,11,12,13]]) (.forbid 1 6 2 (.system [[0,1,14,15,6,5],[2,3,4],[8],[10,11,12,13]]) (.forbid 1 6 3 (.system [[0,1,14,15,16,6,5],[2],[4],[8],[10,11,12,13]]) (.forbid 1 6 4 (.system [[0,1,14,15,16,17,6,5],[2,3,4],[8],[10],[13]]) (.forbid 1 6 5 (.system [[0,1,14,15,16,17,18,6,5],[2],[4],[8],[10],[13]]) (.forbid 1 6 6 (.system [[0,1,14,15,16,17,18,19,6,5],[2],[4],[8],[10],[13]]) (.forbid 1 7 1 (.system [[0,1,14,7,6,5],[2,3,4],[8],[10,11,12,13]]) (.forbid 2 3 1 (.system [[0,1,2,14,3,4],[5,6,7,8],[10,11,12,13]]) (.forbid 2 6 1 (.system [[0,1,2,14,6,7,8,9,10,11,12,13],[4],[5]]) (.forbid 3 4 1 (.system [[0,1,2,3,14,4],[5,6,7,8],[10,11,12,13]]) (.forbid 3 5 1 (.system [[0,1,2,3,14,5,6,7,8],[4],[10,11,12,13]]) (.forbid 3 5 2 (.system [[0],[2,3,14,15,5,6,7,8],[4],[10,11,12,13]]) (.forbid 3 5 3 (.system [[0,1,2,3,14,15,16,5,6,7,8],[4],[10],[13]]) (.forbid 3 5 4 (.system [[0],[2,3,14,15,16,17,5,6,7,8],[4],[10],[13]]) (.forbid 3 5 5 (.system [[0,1,2,3,14,15,16,17,18,5],[4],[8],[10],[13]]) (.forbid 3 5 6 (.system [[0],[2,3,14,15,16,17,18,19,5],[4],[8],[10],[13]]) (.forbid 3 6 1 (.system [[0,1,2,3,14,6,5],[4],[8,9,10,11,12,13]]) (.forbid 3 6 2 (.system [[0,1,2,3,14,15,6,5],[4],[8],[10,11,12,13]]) (.forbid 3 6 3 (.system [[0],[2,3,14,15,16,6,5],[4],[8],[10,11,12,13]]) (certificate_1018_part_0))))))))))))))))))))

noncomputable def certificate_1018_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,14,15,16,6,5],[4],[8],[10,11,12,13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5],[2],[4],[8],[10,11,12,13]]) (.forbid 0 6 5 (.system [[2,1,0,14,15,16,17,18,6,5],[4],[8],[10],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[2],[4],[8],[10],[13]]) (.forbid 0 7 1 (.system [[4,3,2,1,0,14,7,6,5],[8],[10,11,12,13]]) (.forbid 0 9 1 (.system [[2,1,0,14,9,8,7,6,5],[4],[10,11,12,13]]) (.forbid 0 11 1 (.system [[4,3,2,1,0,14,11,12,13],[5,6,7,8],[10]]) (.forbid 1 2 1 (.system [[0,1,14,2,3,4],[5,6,7,8],[10,11,12,13]]) (.forbid 1 3 1 (.system [[0,1,14,3,2],[4],[5,6,7,8],[10,11,12,13]]) (.forbid 1 3 2 (.system [[0,1,14,15,3,2],[4],[5,6,7,8,9,10],[13]]) (.forbid 1 3 3 (.system [[0,1,14,15,16,3,2],[4],[5,6,7,8],[10],[13]]) (.forbid 1 3 4 (.system [[0,1,14,15,16,17,3,2],[4],[5,6,7,8],[10],[13]]) (.forbid 1 3 5 (.system [[0,1,14,15,16,17,18,3,2],[4],[5],[8],[10],[13]]) (.forbid 1 3 6 (.system [[0,1,14,15,16,17,18,19,3,2],[4],[5],[8],[10],[13]]) (.forbid 1 4 1 (.system [[0,1,14,4,3,2],[5,6,7,8],[10,11,12,13]]) (.forbid 1 5 1 (.system [[0,1,14,5,6,7,8],[2,3,4],[10,11,12,13]]) (.forbid 1 5 2 (.system [[0,1,14,15,5,6,7,8],[2],[4],[10,11,12,13]]) (.forbid 1 5 3 (.system [[0,1,14,15,16,5,6,7,8],[2,3,4],[10],[13]]) (.forbid 1 5 4 (.system [[0,1,14,15,16,17,5,6,7,8],[2],[4],[10],[13]]) (.forbid 1 5 5 (.system [[0,1,14,15,16,17,18,5],[2,3,4],[8],[10],[13]]) (certificate_1018_part_1))))))))))))))))))))

noncomputable def certificate_1018 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2,3,4],[5,6,7,8],[10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1,2],[4],[5,6,7,8],[10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2,3,4],[5,6,7,8],[10],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1,2],[4],[5,6,7,8],[10],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1,2,3,4],[5],[8],[10],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2],[4],[5],[8],[10],[13]]) (.forbid 0 3 1 (.system [[0,14,3,2],[4],[5,6,7,8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[0,14,15,3,2],[4],[5,6,7,8],[10,11,12,13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3,2],[4],[5,6,7,8,9,10],[13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3,2],[4],[5,6,7,8],[10],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3,2],[4],[5,6,7,8],[10],[13]]) (.forbid 0 3 6 (.system [[0,14,15,16,17,18,19,3,2],[4],[5],[8],[10],[13]]) (.forbid 0 5 1 (.system [[4,3,2,1,0,14,5,6,7,8,9,10,11,12,13]]) (.forbid 0 5 2 (.system [[2,1,0,14,15,5,6,7,8],[4],[10,11,12,13]]) (.forbid 0 5 3 (.system [[0,14,15,16,5,6,7,8],[2],[4],[10,11,12,13]]) (.forbid 0 5 4 (.system [[2,1,0,14,15,16,17,5,6,7,8],[4],[10],[13]]) (.forbid 0 5 5 (.system [[0,14,15,16,17,18,5,6,7,8],[2],[4],[10],[13]]) (.forbid 0 5 6 (.system [[2,1,0,14,15,16,17,18,19,5],[4],[8],[10],[13]]) (.forbid 0 6 1 (.system [[4,3,2,1,0,14,6,7,8],[5],[10,11,12,13]]) (.forbid 0 6 2 (.system [[4,3,2,1,0,14,15,6,5],[8],[10,11,12,13]]) (certificate_1018_part_2))))))))))))))))))))

noncomputable def certificate_1019_part_0 : FiniteCertificate := .forbid 3 7 6 (.system [[0],[2,3,13,14,15,16,17,18,7],[4],[6],[9],[12]]) (.forbid 4 5 1 (.system [[0,1,2,3,4,13,5,6],[7],[9,10,11,12]]) (.forbid 5 7 1 (.system [[0,1,2,3,4,5,13,7],[6],[9,10,11,12]]) (.forbid 5 7 2 (.system [[0,1,2],[4,5,13,14,7],[6],[9,10,11,12]]) (.forbid 5 7 3 (.system [[0],[2],[4,5,13,14,15,7],[6],[9,10,11,12]]) (.forbid 5 7 4 (.system [[0,1,2],[4,5,13,14,15,16,7],[6],[9],[12]]) (.forbid 5 7 5 (.system [[0],[2],[4,5,13,14,15,16,17,7],[6],[9],[12]]) (.forbid 5 7 6 (.system [[0],[2],[4,5,13,14,15,16,17,18,7],[6],[9],[12]]) (.forbid 6 7 1 (.system [[0,1,2,3,4,5,6,13,7,8,9,10,11,12]]) (.forbid 7 8 1 (.system [[0,1,2,3,4],[6],[7,13,8,9,10,11,12]]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,3,5,7,8,10} 8 2) ∅ 16 3), .ball 1 (.succ (.succ (.zero ∅ 2 1) {0,2,3,4,5,7} 8 2) ∅ 16 3), .ball 3 (.succ (.succ (.zero ∅ 2 1) {0,1,2,4,5,7} 8 2) ∅ 16 3), .ball 5 (.succ (.succ (.zero ∅ 2 1) {0,1,2,3,4,7} 8 2) ∅ 16 3), .ball 7 (.succ (.succ (.zero ∅ 2 1) {0,1,3,5,6,8} 8 2) ∅ 16 3)}))))))))))

noncomputable def certificate_1019_part_1 : FiniteCertificate := .forbid 1 7 1 (.system [[0,1,13,7],[2,3,4,5,6],[9,10,11,12]]) (.forbid 1 7 2 (.system [[0,1,13,14,7],[2,3,4],[6],[9,10,11,12]]) (.forbid 1 7 3 (.system [[0,1,13,14,15,7],[2],[4],[6],[9,10,11,12]]) (.forbid 1 7 4 (.system [[0,1,13,14,15,16,7],[2,3,4],[6],[9],[12]]) (.forbid 1 7 5 (.system [[0,1,13,14,15,16,17,7],[2],[4],[6],[9],[12]]) (.forbid 1 7 6 (.system [[0,1,13,14,15,16,17,18,7],[2],[4],[6],[9],[12]]) (.forbid 2 3 1 (.system [[0,1,2,13,3,4,5,6],[7],[9,10,11,12]]) (.forbid 2 5 1 (.system [[0,1,2,13,5,4],[6],[7,8,9,10,11,12]]) (.forbid 3 4 1 (.system [[0,1,2,3,13,4,5,6],[7],[9,10,11,12]]) (.forbid 3 5 1 (.system [[0,1,2,3,13,5,4],[6],[7],[9,10,11,12]]) (.forbid 3 5 2 (.system [[0],[2,3,13,14,5,4],[6],[7],[9,10,11,12]]) (.forbid 3 5 3 (.system [[0,1,2,3,13,14,15,5,4],[6],[7],[9],[12]]) (.forbid 3 5 4 (.system [[0],[2,3,13,14,15,16,5,4],[6],[7],[9],[12]]) (.forbid 3 5 5 (.system [[0],[2,3,13,14,15,16,17,5,4],[6],[7],[9],[12]]) (.forbid 3 5 6 (.system [[0],[2,3,13,14,15,16,17,18,5,4],[6],[7],[9],[12]]) (.forbid 3 7 1 (.system [[0,1,2,3,13,7],[4,5,6],[9,10,11,12]]) (.forbid 3 7 2 (.system [[0,1,2,3,13,14,7],[4],[6],[9,10,11,12]]) (.forbid 3 7 3 (.system [[0],[2,3,13,14,15,7],[4],[6],[9,10,11,12]]) (.forbid 3 7 4 (.system [[0,1,2,3,13,14,15,16,7],[4],[6],[9],[12]]) (.forbid 3 7 5 (.system [[0],[2,3,13,14,15,16,17,7],[4],[6],[9],[12]]) (certificate_1019_part_0))))))))))))))))))))

noncomputable def certificate_1019_part_2 : FiniteCertificate := .forbid 0 7 3 (.system [[2,1,0,13,14,15,7],[4],[6],[9,10,11,12]]) (.forbid 0 7 4 (.system [[0,13,14,15,16,7],[2],[4],[6],[9,10,11,12]]) (.forbid 0 7 5 (.system [[2,1,0,13,14,15,16,17,7],[4],[6],[9],[12]]) (.forbid 0 7 6 (.system [[0,13,14,15,16,17,18,7],[2],[4],[6],[9],[12]]) (.forbid 0 8 1 (.system [[4,3,2,1,0,13,8,7],[6],[9,10,11,12]]) (.forbid 0 10 1 (.system [[6,5,4,3,2,1,0,13,10,11,12],[7],[9]]) (.forbid 1 2 1 (.system [[0,1,13,2,3,4,5,6],[7],[9,10,11,12]]) (.forbid 1 3 1 (.system [[0,1,13,3,2],[4,5,6],[7],[9,10,11,12]]) (.forbid 1 3 2 (.system [[0,1,13,14,3,2],[4],[6],[7],[9,10,11,12]]) (.forbid 1 3 3 (.system [[0,1,13,14,15,3,2],[4,5,6],[7],[9],[12]]) (.forbid 1 3 4 (.system [[0,1,13,14,15,16,3,2],[4],[6],[7],[9],[12]]) (.forbid 1 3 5 (.system [[0,1,13,14,15,16,17,3,2],[4],[6],[7],[9],[12]]) (.forbid 1 3 6 (.system [[0,1,13,14,15,16,17,18,3,2],[4],[6],[7],[9],[12]]) (.forbid 1 4 1 (.system [[0,1,13,4,3,2],[6],[7,8,9,10,11,12]]) (.forbid 1 5 1 (.system [[0,1,13,5,4,3,2],[6],[7],[9,10,11,12]]) (.forbid 1 5 2 (.system [[0,1,13,14,5,4],[2],[6],[7],[9,10,11,12]]) (.forbid 1 5 3 (.system [[0,1,13,14,15,5,4,3,2],[6],[7],[9],[12]]) (.forbid 1 5 4 (.system [[0,1,13,14,15,16,5,4],[2],[6],[7],[9],[12]]) (.forbid 1 5 5 (.system [[0,1,13,14,15,16,17,5,4],[2],[6],[7],[9],[12]]) (.forbid 1 5 6 (.system [[0,1,13,14,15,16,17,18,5,4],[2],[6],[7],[9],[12]]) (certificate_1019_part_1))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_ExteriorFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

open scoped SimpleGraph


def extNeighbors {V : Type*} (G : SimpleGraph V) (Q : Set V) (x : V) : Set V :=
  {u | G.Adj x u ∧ u ∉ Q}


structure Frame {V : Type*} (G : SimpleGraph V) (t : ℕ) where
  q : Fin t ↪ V
  adj : ∀ i j, i ≠ j → G.Adj (q i) (q j)

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_FrameProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

namespace Frame
variable {V : Type*} {G : SimpleGraph V} {t : ℕ} (T : Frame G t)

def Q : Set V := Set.range T.q

def U (i : Fin t) : Set V := extNeighbors G T.Q (T.q i)

def reindex (e : Fin t ≃ Fin t) : Frame G t where
  q := e.toEmbedding.trans T.q
  adj i j hij := T.adj (e i) (e j) (fun he => hij (e.injective he))


def triangle {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : Frame G 3 where
  q := ⟨![a,b,c], by
    intro i j he
    fin_cases i <;> fin_cases j <;> aesop⟩
  adj i j hij := by
    change G.Adj (![a,b,c] i) (![a,b,c] j)
    fin_cases i <;> fin_cases j <;> simp_all [SimpleGraph.adj_comm]

end Frame


structure FourHyp {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop where
  order : Fintype.card V ≤ 17
  cycle : ¬ SimpleGraph.cycleGraph 5 ⊑ G
  clique : G.cliqueNum ≤ 3
  expansion : ∀ I, G.IsIndepSet I → I.Nonempty → 4*I.ncard+1 ≤ (closedNeighborhood G I).ncard

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_FourCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

namespace FourHyp
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (H : FourHyp G)
include H

def overlapClasses (T : Frame G 3) : Fin 4 → Set V :=
  ![T.U 0 ∩ T.U 1,T.U 0 \ T.U 1,T.U 1 \ T.U 0,T.U 2]

end FourHyp

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_PatternReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def PatternVerified (k t : ℕ) (D : List (List ℕ)) : Prop :=
  ∃ C : FiniteCertificate, C.Valid k t (patternOrder D) (patternClique D)
    (patternEdges D) (patternAmount D) (patternEdgeCount D) []

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_ThreeCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

structure ThreeHyp {V : Type*} [Fintype V] (G : SimpleGraph V) (a : ℕ) : Prop where
  order : Fintype.card V = 3*a+1
  alpha : G.indepNum ≤ a
  a_max : a ≤ 3
  cycle : ¬ SimpleGraph.cycleGraph 4 ⊑ G
  clique : G.cliqueNum ≤ 3
  expansion : ∀ I, G.IsIndepSet I → I.Nonempty → 3*I.ncard+1 ≤ (closedNeighborhood G I).ncard

namespace ThreeHyp
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {a : ℕ} (H : ThreeHyp G a)
include H


def W (T : Frame G 3) : Set V := T.Qᶜ \ ⋃ i,T.U i

end ThreeHyp

end CycleClique

end OAI
end


