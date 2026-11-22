-- Prove2me | Definitions.Def_LeanPool_Parikh_ExecutableCompiler
-- name    : LeanPool_Parikh_ExecutableCompiler
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:55:49.815796+00:00
-- url     : https://prove2.me/theorems/7d127173-5864-4a94-a8b1-bfe8cd195854
-- title:
--   Executable Compiler
-- statement:
--   Definitions and structural lemmas for Executable Compiler, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/ExecutableCompiler.lean

module
public import Definitions.Def_LeanPool_Parikh_CompilerTrees
public import Definitions.Def_LeanPool_Parikh_CompilerBounds
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Mathlib.Algebra.Order.Group.Nat
public import Theorems.Thm_Parikh_EncodedGrammar_cycleTrees_nodup
public import Theorems.Thm_Parikh_EncodedGrammar_mem_baseTrees
public import Theorems.Thm_Parikh_EncodedGrammar_mem_cycleTrees
public import Theorems.Thm_Parikh_EncodedGrammar_tree_budgets
public import Theorems.Thm_Parikh_contextActivation_correct
public import Theorems.Thm_Parikh_contextComponent_size_bounds
public import Theorems.Thm_Parikh_listComponent_denotation
public import Theorems.Thm_Parikh_treeRepresentation_correct

set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Parikh
namespace EncodedGrammar
@[expose] def activates (g : EncodedGrammar)
    (B : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1)))
    (D : List (ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1)))) : Bool :=
  letI : DecidableEq g.decode.NT := inferInstanceAs (DecidableEq (Fin
    (g.extraNonterminalCount + 1)))
  letI := ParseTree.decEq (T := Fin g.terminalCount) (N := g.decode.NT)
  contextActivation g.decode B D
theorem activates_correct (g : EncodedGrammar)
    [de : DecidableEq (ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1)))]
    (B : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1)))
    (D : List (ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))))
    (hD : ∀ C ∈ D, IsBoundedCycle g.decode C) :
    g.activates B D = true ↔ ContextsActivatable g.decode B D.toFinset := by
  classical
  let dn := instDecidableEqFin (g.extraNonterminalCount + 1)
  let dc := @ParseTree.decEq (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))
    (inferInstance) dn
  have h := @contextActivation_correct (Fin g.terminalCount) g.decode dn dc B D
    (fun C hC => (hD C hC).1)
  have hset : @List.toFinset _ dc D = @List.toFinset _ de D :=
    congrArg (fun eqDecision => @List.toFinset _ eqDecision D) (Subsingleton.elim dc de)
  exact h.trans (Iff.of_eq (congrArg (ContextsActivatable g.decode B) hset))
@[expose] def compile (g : EncodedGrammar) : Witness (Fin g.terminalCount) :=
  g.baseTrees.flatMap fun B =>
    (g.cycleTrees.sublists.filter (g.activates B)).map (listComponent B)
theorem mem_compile (g : EncodedGrammar) (c : Component (Fin g.terminalCount)) :
    c ∈ g.compile ↔ ∃ B ∈ g.baseTrees,
      ∃ D ∈ g.cycleTrees.sublists, g.activates B D = true ∧ listComponent B D = c := by
  simp only [compile, List.mem_flatMap, List.mem_map, List.mem_filter]
  tauto
theorem compile_correct (g : EncodedGrammar) :
    g.compile.denotation = image g.decode.language := by
  classical
  rw [← (treeRepresentation_correct g.decode).1]
  ext v
  change (∃ c ∈ g.compile, v ∈ c.denotation) ↔
    ∃ B : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1)),
      ∃ D : Finset (ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))),
        IsBase g.decode B ∧ (∀ C ∈ D, IsBoundedCycle g.decode C) ∧
          ContextsActivatable g.decode B D ∧ v ∈ (contextComponent B D).denotation
  constructor
  · rintro ⟨c, hc, hv⟩
    obtain ⟨B, hb, D, hd, ha, rfl⟩ := (g.mem_compile c).mp hc
    have hsub := List.mem_sublists.mp hd
    have hcycles : ∀ C ∈ D, IsBoundedCycle g.decode C :=
      fun C hC => (g.mem_cycleTrees C).mp (hsub.subset hC)
    refine ⟨B, D.toFinset, (g.mem_baseTrees B).mp hb, ?_,
      (g.activates_correct B D hcycles).mp ha, ?_⟩
    · exact fun C hC => hcycles C (List.mem_toFinset.mp hC)
    · rwa [← listComponent_denotation B D (hsub.nodup g.cycleTrees_nodup)]
  · rintro ⟨B, D, hb, hd, ha, hv⟩
    let cs := g.cycleTrees.filter (fun C => decide (C ∈ D))
    have hsub : cs.Sublist g.cycleTrees := List.filter_sublist
    have hset : cs.toFinset = D := by
      ext C
      simp only [List.mem_toFinset, cs, List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨(g.mem_cycleTrees C).mpr (hd C h), h⟩⟩
    have hcycles : ∀ C ∈ cs, IsBoundedCycle g.decode C :=
      fun C hC => (g.mem_cycleTrees C).mp (hsub.subset hC)
    have hact : g.activates B cs = true := (g.activates_correct B cs hcycles).mpr (by
      rwa [hset])
    refine ⟨listComponent B cs, (g.mem_compile _).mpr
      ⟨B, (g.mem_baseTrees B).mpr hb, cs, List.mem_sublists.mpr hsub, hact, rfl⟩, ?_⟩
    rw [listComponent_denotation B cs (hsub.nodup g.cycleTrees_nodup), hset]
    exact hv
theorem compile_length_le (g : EncodedGrammar) :
    g.compile.length ≤ g.baseTrees.length * 2 ^ g.cycleTrees.length := by
  unfold compile
  rw [List.length_flatMap]
  have bound : ∀ (l : List ℕ) (B : ℕ), (∀ n ∈ l, n ≤ B) → l.sum ≤ l.length * B := by
    intro l B
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hl
      have ha := hl a (by simp)
      have ht := ih (fun n hn => hl n (by simp [hn]))
      simp only [List.sum_cons, List.length_cons]
      rw [Nat.add_mul, one_mul]
      omega
  have hsum := bound
    (g.baseTrees.map fun B =>
      ((g.cycleTrees.sublists.filter (g.activates B)).map (listComponent B)).length)
    (2 ^ g.cycleTrees.length) (by
      intro n hn
      obtain ⟨B, _, rfl⟩ := List.mem_map.mp hn
      simpa only [List.length_map, List.length_sublists] using
        List.length_filter_le (g.activates B) g.cycleTrees.sublists)
  simpa only [List.length_map, Nat.nsmul_eq_mul] using hsum
theorem compile_bounded (g : EncodedGrammar) : WithinBounds g.size g.compile := by
  classical
  obtain ⟨hb, hc, hnorm⟩ := g.tree_budgets
  refine ⟨g.compile_length_le.trans
    (Nat.mul_le_mul hb (Nat.pow_le_pow_right (by omega) hc)), ?_⟩
  intro c hmem
  obtain ⟨B, hB, D, hD, _, rfl⟩ := (g.mem_compile c).mp hmem
  have hsub := List.mem_sublists.mp hD
  have hDlen : D.length ≤ g.size.trees := hsub.length_le.trans hc
  have hbase : norm B.weight ≤ g.size.positions :=
    hnorm B (Or.inl ((g.mem_baseTrees B).mp hB))
  have hperiod : ∀ C ∈ D, norm C.weight ≤ g.size.positions :=
    fun C hC => hnorm C (Or.inr ((g.mem_cycleTrees C).mp (hsub.subset hC)))
  have hnd := hsub.nodup g.cycleTrees_nodup
  have hbnorm := (contextComponent_size_bounds B D.toFinset g.size.positions
    hbase (fun C hC => hperiod C (List.mem_toFinset.mp hC))).2.1
  have hcard : D.toFinset.card = D.length := List.toFinset_card_of_nodup hnd
  have hbaseeq : (listComponent B D).base = (contextComponent B D.toFinset).base := by
    change B.weight + (D.map ParseTree.weight).sum = B.weight + ∑ C ∈ D.toFinset, C.weight
    rw [List.sum_toFinset ParseTree.weight hnd]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [listComponent, List.length_map] using hDlen
  · rw [hbaseeq]
    exact hbnorm.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (hcard.le.trans hDlen) 1))
  · intro p hp
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hp
    exact hperiod C hC
end EncodedGrammar
@[expose] def compiler : Compiler where
  compile := EncodedGrammar.compile
  correct := EncodedGrammar.compile_correct
  bounded := EncodedGrammar.compile_bounded
end Parikh


