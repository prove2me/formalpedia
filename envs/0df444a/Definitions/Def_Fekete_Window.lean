-- Prove2me | Definitions.Def_Fekete_Window
-- name    : Fekete_Window
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:26:17.858728+00:00
-- url     : https://prove2.me/theorems/4977d55d-d669-56a1-923e-b27e5776359d
-- title:
--   Window
-- statement:
--   Definitions and structural lemmas for Window, from Brian Sanders (Egly443/lean-fekete; see pinned Apache-2.0 LICENSE and source headers)'s pinned Nearly subadditive sequences and Fekete's lemma beyond Mathlib development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Window.lean

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Filter Set
open scoped Topology
def NearlySubadditive (f : ℕ → ℝ) (μ : ℝ) (N : ℕ) (u : ℕ → ℝ) : Prop :=
  ∀ ⦃m n : ℕ⦄, N ≤ m → m ≤ n → (n : ℝ) ≤ μ * m → u (m + n) ≤ u m + u n + f (m + n)
namespace NearlySubadditive
variable {f g : ℕ → ℝ} {μ ν : ℝ} {N M : ℕ} {u v : ℕ → ℝ}
end NearlySubadditive
namespace NearlySubadditive
variable {μ : ℝ} {N : ℕ} {u : ℕ → ℝ}
def blockMax (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Finset.Icc n (2 * n)).sup' ⟨n, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩ fun j ↦ u j / j
def windowEnd (μ : ℝ) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | i + 1 => windowEnd μ n i + ⌊μ * windowEnd μ n i⌋₊
@[irreducible]
protected def lim (N : ℕ) (u : ℕ → ℝ) : ℝ :=
  sInf ((fun k : ℕ ↦ u k / k) '' Ici (max N 1))
end NearlySubadditive


