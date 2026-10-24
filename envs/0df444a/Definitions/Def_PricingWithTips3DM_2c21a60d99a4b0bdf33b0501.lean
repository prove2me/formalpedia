-- Prove2me | Definitions.Def_PricingWithTips3DM_2c21a60d99a4b0bdf33b0501
-- name    : PricingWithTips3DM_2c21a60d99a4b0bdf33b0501
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:08:13.066908+00:00
-- url     : https://prove2.me/theorems/d739a801-b91a-4ae1-bcd4-87546c113447
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.Load
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_df68a6a1259aa6c41c82a32d
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Batch edge lookup: initial query loading
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

open PolyBuilder

private def loadSymbols_run (symbols graph : List CliqueSym)
    (work₁ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .loadQueries buffer₁ buffer₂ test
        (symbols.map some ++ none :: graph.map some) [] work₁ [] [] [] [])
      (some (cfg .beginQueries (some none) buffer₂ test (graph.map some) []
        (none :: (symbols.map some).reverse ++ work₁) [] [] [] []))
      (symbols.length + 1) := by
  induction symbols generalizing work₁ buffer₁ with
  | nil =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol symbols ih =>
      let after := cfg .loadQueries (some (some symbol)) buffer₂ test
        (symbols.map some ++ none :: graph.map some) []
        (some symbol :: work₁) [] [] [] []
      have first : EvalsToInTime (step program)
          (cfg .loadQueries buffer₁ buffer₂ test
            ((symbol :: symbols).map some ++ none :: graph.map some) []
            work₁ [] [] [] [])
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (work₁ := some symbol :: work₁)
        (buffer₁ := some (some symbol))
      let full := EvalsToInTime.trans (step program)
        1 (symbols.length + 1) _ after _ first rest
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Exact cost of loading the query half of the fixed-pair input. -/
def loadSteps (queries : List (Nat × Nat)) : Nat :=
  (queries.flatMap encodeCliqueEdge).length + 2

/-- Move every serialized query to work one, discard the pair separator, and
enter the repeated-query loop. -/
def load_run (queries : List (Nat × Nat)) (I : CliqueInstance) :
    EvalsToInTime (step program)
      (initialCfg program
        (pairEncoding (queries.flatMap encodeCliqueEdge)
          (encodeCliqueInstance I)))
      (some (cfg (.nextQuery true) (some none) none false
        ((encodeCliqueInstance I).map some) []
        (((queries.flatMap encodeCliqueEdge).map some).reverse) [] [] [] []))
      (loadSteps queries) := by
  let symbols := queries.flatMap encodeCliqueEdge
  have loaded := loadSymbols_run symbols (encodeCliqueInstance I) [] none none
    false
  let afterLoad := cfg .beginQueries (some none) none false
    ((encodeCliqueInstance I).map some) []
    (none :: (symbols.map some).reverse) [] [] [] []
  have loaded' : EvalsToInTime (step program)
      (initialCfg program
        (pairEncoding symbols (encodeCliqueInstance I)))
      (some afterLoad) (symbols.length + 1) := by
    simpa [symbols, afterLoad, pairEncoding, initialCfg, cfg, program,
      List.append_assoc] using loaded
  have separator : EvalsToInTime (step program) afterLoad
      (some (cfg (.nextQuery true) (some none) none false
        ((encodeCliqueInstance I).map some) []
        ((symbols.map some).reverse) [] [] [] [])) 1 :=
    ⟨⟨1, by simp [flip, afterLoad, step, program, cfg, stepOp]⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step program)
    (symbols.length + 1) 1 _ afterLoad _ loaded' separator
  convert full using 1
  all_goals
    simp [loadSteps, symbols, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  omega

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup


