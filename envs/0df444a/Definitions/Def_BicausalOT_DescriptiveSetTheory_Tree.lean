-- Prove2me | Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
-- name    : BicausalOT_DescriptiveSetTheory_Tree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:01:17.954798+00:00
-- url     : https://prove2.me/theorems/0956ae93-ecfb-4b35-989d-326e9a44ae78
-- title:
--   Tree
-- statement:
--   Definitions and structural lemmas for Tree, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]
def closedFiberG (F : Set (X × (ℕ → ℕ))) (x : X) : Set (ℕ → ℕ) :=
  { y | (x, y) ∈ F }
def fiberRestNG (F : Set (X × (ℕ → ℕ))) (x : X) (f : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) :=
  { y | (x, y) ∈ F ∧ ∀ i < n, y i = f i }
omit [TopologicalSpace X] in
theorem fiberRestNG_zero (F : Set (X × (ℕ → ℕ))) (x : X) (f : ℕ → ℕ) :
    fiberRestNG F x f 0 = closedFiberG F x := by
  ext y; simp [fiberRestNG, closedFiberG]
omit [TopologicalSpace X] in
theorem exists_extNG {F : Set (X × (ℕ → ℕ))} {x : X} {f : ℕ → ℕ} {n : ℕ}
    (hne : (fiberRestNG F x f n).Nonempty) :
    ∃ k, (fiberRestNG F x (Function.update f n k) (n + 1)).Nonempty := by
  obtain ⟨y, hy_mem, hy_ext⟩ := hne
  refine ⟨y n, y, hy_mem, fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · rw [Function.update_of_ne (by omega)]; exact hy_ext i h
  · subst h; simp [Function.update_self]
def leftmostAuxG (F : Set (X × (ℕ → ℕ))) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) :
    (n : ℕ) → { f : ℕ → ℕ // (fiberRestNG F x f n).Nonempty }
  | 0 => ⟨fun _ => 0, fiberRestNG_zero F x _ ▸ h₀⟩
  | n + 1 =>
    let ⟨f, hf⟩ := leftmostAuxG F x h₀ n
    ⟨Function.update f n (Nat.find (exists_extNG hf)),
     Nat.find_spec (exists_extNG hf)⟩
def leftmostBranchG (F : Set (X × (ℕ → ℕ))) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) (n : ℕ) : ℕ :=
  Nat.find (exists_extNG (leftmostAuxG F x h₀ n).2)
def leftmostWitnessG (F : Set (X × (ℕ → ℕ))) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) (n : ℕ) : ℕ → ℕ :=
  (leftmostAuxG F x h₀ n).2.some
def projFiberCylNG (F : Set (X × (ℕ → ℕ))) (f : ℕ → ℕ) (n : ℕ) : Set X :=
  { x | (fiberRestNG F x f n).Nonempty }
def closedUniformizerG (F : Set (X × (ℕ → ℕ))) (_hF : IsClosed F)
    (hne : F.Nonempty) : X → (ℕ → ℕ) :=
  fun x => if h : (closedFiberG F x).Nonempty then leftmostBranchG F x h
            else hne.some.2
end


