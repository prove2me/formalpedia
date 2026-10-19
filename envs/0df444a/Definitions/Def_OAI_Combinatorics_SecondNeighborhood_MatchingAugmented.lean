-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
-- name    : OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:46:51.493439+00:00
-- url     : https://prove2.me/theorems/7c11eaa0-9d93-412b-bc4b-90e8f0e07ac0
-- title:
--   Swapping the sides of a bipartite matching
-- statement:
--   For finite types $L,R$ and a finite set $M\subseteq L\times R$, let
--   $$
--   M^{\mathrm{sw}}=\{(r,l):(l,r)\in M\}\subseteq R\times L .
--   $$
--   Then:
--   - $(r,l)\in M^{\mathrm{sw}}$ iff $(l,r)\in M$;
--   - $|M^{\mathrm{sw}}|=|M|$ and $(M^{\mathrm{sw}})^{\mathrm{sw}}=M$;
--   - filtering commutes with swapping: $\{e\in M^{\mathrm{sw}}:p(e)\}=\{e\in M:p(e^{\mathrm{sw}})\}^{\mathrm{sw}}$, with equal cardinalities.
--
--   Swapping reuses one-sided matching arguments for the opposite side of the conflict graph.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/MatchingAugmented.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/MatchingAugmented.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SeymourSecondNeighborhood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph

namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    {E : L → R → Prop}

def swapMatching (M : Finset (L × R)) : Finset (R × L) := M.image Prod.swap

omit [Fintype L] [Fintype R] in
@[simp] theorem mem_swapMatching {M : Finset (L × R)} {e : R × L} :
    e ∈ swapMatching M ↔ e.swap ∈ M := by
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    simpa using hf
  · intro he
    exact Finset.mem_image.mpr ⟨e.swap, he, Prod.swap_swap e⟩

omit [Fintype L] [Fintype R] in
@[simp] theorem card_swapMatching (M : Finset (L × R)) :
    (swapMatching M).card = M.card := by
  exact Finset.card_image_of_injective _ Prod.swap_injective

omit [Fintype L] [Fintype R] in
@[simp] theorem swapMatching_swapMatching (M : Finset (L × R)) :
    swapMatching (swapMatching M) = M := by
  ext e
  simp

omit [Fintype L] [Fintype R] in
theorem filter_swapMatching (M : Finset (L × R))
    (p : R × L → Prop) [DecidablePred p] :
    (swapMatching M).filter p = swapMatching (M.filter (fun e => p e.swap)) := by
  ext e
  simp

omit [Fintype L] [Fintype R] in
@[simp] theorem card_filter_swapMatching (M : Finset (L × R))
    (p : R × L → Prop) [DecidablePred p] :
    ((swapMatching M).filter p).card = (M.filter (fun e => p e.swap)).card := by
  rw [filter_swapMatching, card_swapMatching]

end SeymourSecondNeighborhood.Bipartite

end OAI


