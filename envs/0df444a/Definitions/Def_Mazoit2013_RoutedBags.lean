-- Prove2me | Definitions.Def_Mazoit2013_RoutedBags
-- name    : Mazoit2013_RoutedBags
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-14T01:20:54.845192+00:00
-- url     : https://prove2.me/theorems/122a0bab-4435-4bee-9b06-771108c238ca
-- title:
--   Restrict bags and route separator vertices to a root
-- statement:
--   Given tree bags, a retained vertex side R, separator S, a root, and for each separator vertex a walk from the root to a bag containing it, the routed bag at t keeps the old vertices in R and adds separator vertices whose routes pass through t. This definition does not assume the cardinality or path properties later required to preserve partial decompositions.
-- source:
--   Seymour and Thomas, Graph Searching and a Min-Max Theorem for Tree-Width, https://thomas.math.gatech.edu/PAP/search.pdf, Lemma 2.4; Mazoit arXiv:1309.2266, Lemma 1. Explicit routed-bag representation.

import Definitions.Def_Mazoit2013_PartialDecompositions
open RobertsonSeymour1986.GM5
namespace StableMSR.Recovery.PartialDecompositions
variable {V T : Type} [Fintype V] [DecidableEq V] [DecidableEq T]
noncomputable def routedBag (tree : SimpleGraph T) (bags : T → Finset V)
    (R S : Finset V) (root : T) (anchor : V → T)
    (route : ∀ v, tree.Walk root (anchor v)) (t : T) : Finset V := by
  classical exact (bags t ∩ R) ∪ S.filter (fun v => t ∈ (route v).support)
lemma mem_routedBag {tree : SimpleGraph T} {bags : T → Finset V}
    {R S : Finset V} {root : T} {anchor : V → T}
    {route : ∀ v, tree.Walk root (anchor v)} {t : T} {v : V} :
    v ∈ routedBag tree bags R S root anchor route t ↔
      (v ∈ bags t ∧ v ∈ R) ∨ (v ∈ S ∧ t ∈ (route v).support) := by
  classical simp [routedBag]
end StableMSR.Recovery.PartialDecompositions


