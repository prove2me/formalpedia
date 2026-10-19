-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
-- name    : OAI_Combinatorics_SecondNeighborhood_Reindex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:41:27.257439+00:00
-- url     : https://prove2.me/theorems/accdaa40-ad7c-4d53-a77a-5d940e223d25
-- title:
--   Transporting a digraph along a bijection of vertex sets
-- statement:
--   Let $e:V\to W$ be a bijection and $r$ a relation on $V$. The reindexed relation on $W$ is
--   $$
--   (e_*r)(x,y)\iff r\bigl(e^{-1}x,\,e^{-1}y\bigr).
--   $$
--   For finite $V$ and $W$, the first and second neighbourhoods of $e_*r$ at $w$ are the images under $e$ of the neighbourhoods of $r$ at $e^{-1}w$. In particular their sizes agree:
--   $$
--   |N^+_{e_*r}(w)|=|N^+_r(e^{-1}w)|,\qquad |N^{++}_{e_*r}(w)|=|N^{++}_r(e^{-1}w)|.
--   $$
--
--   This lets a counterexample on any finite vertex type be transported to the standard type $\{0,\dots,n-1\}$, and back, without changing neighbourhood sizes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/Reindex.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/Reindex.lean by skeleton subtraction
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

namespace OAI

namespace SeymourSecondNeighborhood

variable {V W : Type*}

def reindex (e : V ≃ W) (r : V → V → Prop) : W → W → Prop :=
  fun x y => r (e.symm x) (e.symm y)

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem mem_firstNeighbors_reindex (e : V ≃ W)
    (r : V → V → Prop) (v w : W) :
    w ∈ firstNeighbors (reindex e r) v ↔
      e.symm w ∈ firstNeighbors r (e.symm v) := by
  simp only [mem_firstNeighbors, reindex]

@[simp] theorem mem_secondNeighbors_reindex (e : V ≃ W)
    (r : V → V → Prop) (v w : W) :
    w ∈ secondNeighbors (reindex e r) v ↔
      e.symm w ∈ secondNeighbors r (e.symm v) := by
  simp only [mem_secondNeighbors, reindex]
  constructor
  · rintro ⟨hneq, hnot, u, hvu, huw⟩
    exact ⟨fun heq => hneq (e.symm.injective heq), hnot, e.symm u, hvu, huw⟩
  · rintro ⟨hneq, hnot, u, hvu, huw⟩
    refine ⟨fun heq => hneq (congrArg e.symm heq), hnot, e u, ?_, ?_⟩
    · simpa only [Equiv.symm_apply_apply] using hvu
    · simpa only [Equiv.symm_apply_apply] using huw

omit [DecidableEq V] [DecidableEq W] in
theorem firstNeighbors_reindex (e : V ≃ W) (r : V → V → Prop) (w : W) :
    firstNeighbors (reindex e r) w =
      (firstNeighbors r (e.symm w)).map e.toEmbedding := by
  ext v
  simp only [Finset.mem_map_equiv, mem_firstNeighbors_reindex]

theorem secondNeighbors_reindex (e : V ≃ W) (r : V → V → Prop) (w : W) :
    secondNeighbors (reindex e r) w =
      (secondNeighbors r (e.symm w)).map e.toEmbedding := by
  ext v
  simp only [Finset.mem_map_equiv, mem_secondNeighbors_reindex]

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem card_firstNeighbors_reindex (e : V ≃ W)
    (r : V → V → Prop) (w : W) :
    (firstNeighbors (reindex e r) w).card =
      (firstNeighbors r (e.symm w)).card := by
  rw [firstNeighbors_reindex, Finset.card_map]

@[simp] theorem card_secondNeighbors_reindex (e : V ≃ W)
    (r : V → V → Prop) (w : W) :
    (secondNeighbors (reindex e r) w).card =
      (secondNeighbors r (e.symm w)).card := by
  rw [secondNeighbors_reindex, Finset.card_map]

end SeymourSecondNeighborhood

end OAI


