-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
-- name    : QEC_Coding_BalancedProduct_LPSGraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:02:24.753938+00:00
-- url     : https://prove2.me/theorems/cb846480-19a5-4c86-800d-5cb1cf3cc079
-- title:
--   LPSGraph
-- statement:
--   Definitions and structural lemmas for LPSGraph, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSGraph.lean

import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_projectiveDetIsSquare_upperUnipotent
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_inv_mem_lpsGenerators401_of_mem
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_not_projectiveDetIsSquare_of_mem_lpsGenerators401

set_option autoImplicit false
open scoped MatrixGroups
namespace QEC.Coding.BalancedProduct.LPSGraph
open Matrix
open LPSArithmetic LPSGenerators
noncomputable instance pglFintype401 (q : ℕ) [Fact q.Prime] :
    Fintype (PGL(2, ZMod q)) := by
  classical
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  letI : Fintype (GL (Fin 2) (ZMod q)) :=
    Fintype.ofInjective Units.val Units.val_injective
  exact Fintype.ofSurjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
noncomputable def lpsCayleyGraph401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    SimpleGraph PGL(2, ZMod q) :=
  SimpleGraph.fromRel fun g w =>
    ∃ s ∈ lpsGenerators401 q hq, s * g = w
theorem one_not_mem_lpsGenerators401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    (1 : PGL(2, ZMod q)) ∉ lpsGenerators401 q hq := by
  intro hone
  have hnonsquare :=
    not_projectiveDetIsSquare_of_mem_lpsGenerators401 q hq hone
  apply hnonsquare
  simpa using
    (projectiveDetIsSquare_upperUnipotent (R := ZMod q) (0 : ZMod q))
theorem lpsCayleyGraph401_adj_iff
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (g w : PGL(2, ZMod q)) :
    (lpsCayleyGraph401 q hq).Adj g w ↔
      ∃ s ∈ lpsGenerators401 q hq, s * g = w := by
  rw [lpsCayleyGraph401, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, ⟨s, hs, hsg⟩ | ⟨s, hs, hsw⟩⟩
    · exact ⟨s, hs, hsg⟩
    · refine ⟨s⁻¹, inv_mem_lpsGenerators401_of_mem q hq hs, ?_⟩
      rw [← hsw]
      simp
  · rintro ⟨s, hs, rfl⟩
    refine ⟨?_, Or.inl ⟨s, hs, rfl⟩⟩
    intro heq
    have hsone : s = 1 := by
      apply mul_right_cancel (b := g)
      simpa using heq
    exact one_not_mem_lpsGenerators401 q hq (hsone ▸ hs)
noncomputable def lpsNeighbors401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (g : PGL(2, ZMod q)) : Finset PGL(2, ZMod q) := by
  classical
  exact (lpsGenerators401 q hq).image fun s => s * g
theorem lpsCayleyGraph401_adj_mul_right_iff
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (g w h : PGL(2, ZMod q)) :
    (lpsCayleyGraph401 q hq).Adj (g * h) (w * h) ↔
      (lpsCayleyGraph401 q hq).Adj g w := by
  simp only [lpsCayleyGraph401_adj_iff]
  constructor
  · rintro ⟨s, hs, hsw⟩
    refine ⟨s, hs, ?_⟩
    apply mul_right_cancel (b := h)
    simpa [mul_assoc] using hsw
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, by simp [mul_assoc]⟩
noncomputable def lpsRightIso401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (h : PGL(2, ZMod q)) :
    lpsCayleyGraph401 q hq ≃g lpsCayleyGraph401 q hq where
  toEquiv := Equiv.mulRight h
  map_rel_iff' := by
    intro g w
    exact lpsCayleyGraph401_adj_mul_right_iff q hq g w h
noncomputable def adjacencyRayleigh401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (f : PGL(2, ZMod q) → ℝ) : ℝ :=
  ∑ v, f v * ∑ w ∈ lpsNeighbors401 q hq v, f w
def LPS401RayleighBound
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : Prop :=
  (lpsCayleyGraph401 q hq).Connected ∧
    ∀ f : PGL(2, ZMod q) → ℝ,
      (∑ v, f v) = 0 →
      10 * adjacencyRayleigh401 q hq f ≤
        401 * ∑ v, (f v) ^ 2
noncomputable def vertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (S : Finset (PGL(2, ZMod q)))
    (v : PGL(2, ZMod q)) : ℝ := by
  classical
  exact if v ∈ S then 1 else 0
noncomputable def centeredVertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (S : Finset (PGL(2, ZMod q)))
    (v : PGL(2, ZMod q)) : ℝ :=
  Fintype.card (PGL(2, ZMod q)) * vertexIndicator401 q S v - S.card
noncomputable def lpsNeighborsIn401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q)))
    (v : PGL(2, ZMod q)) : Finset (PGL(2, ZMod q)) := by
  classical
  exact (lpsNeighbors401 q hq v).filter (· ∈ S)
noncomputable def insideAdjacencyCount401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q))) : ℕ := by
  classical
  exact ∑ v ∈ S, (lpsNeighborsIn401 q hq S v).card
end QEC.Coding.BalancedProduct.LPSGraph


