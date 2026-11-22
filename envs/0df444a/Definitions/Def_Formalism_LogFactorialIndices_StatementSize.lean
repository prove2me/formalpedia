-- Prove2me | Definitions.Def_Formalism_LogFactorialIndices_StatementSize
-- name    : Formalism_LogFactorialIndices_StatementSize
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:07.506807+00:00
-- url     : https://prove2.me/theorems/eb8aebea-aedc-4e62-a89b-e80509be3624
-- title:
--   Statement Size
-- statement:
--   Definitions and structural lemmas for Statement Size, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/StatementSize.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeIndexTer
def ph (u : ℝ) : ℝ := u * Real.log u - u
def PhIncr : Prop :=
  ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → (1 ≤ u ∨ 1 ≤ v) → |ph (u + v) - ph u| ≤ v * Real.log (u + v + 2)
def PhIncrFalse : Prop :=
  ¬ ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → |ph (u + v) - ph u| ≤ v * Real.log (u + v + 2)
def PhIncrNat : Prop :=
  ∀ u v : ℕ, |ph ((u : ℝ) + v) - ph u| ≤ (v : ℝ) * Real.log ((u : ℝ) + v + 2)
def Interlaced (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S : ℝ) : Prop :=
  (∀ i, 0 ≤ c i ∧ c i ≤ S) ∧ ∀ i : Fin k, c' i ≤ c i.castSucc ∧ c i.succ ≤ c' i
def Interlace : Prop :=
  ∀ (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S w : ℝ), Interlaced k c c' S → 1 ≤ w →
    |(∑ i, ph (w + c i)) - ∑ i, ph (w + c' i)| ≤ (w + 2 * S) * Real.log (w + S + 2)
def InterlaceFalse : Prop :=
  ¬ ∀ (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S w : ℝ), Interlaced k c c' S → 0 ≤ w →
    |(∑ i, ph (w + c i)) - ∑ i, ph (w + c' i)| ≤ (w + 2 * S) * Real.log (w + S + 2)
def InterlaceNat : Prop :=
  ∀ (k : ℕ) (c : Fin (k + 1) → ℕ) (c' : Fin k → ℕ) (S w : ℕ),
    Interlaced k (fun i => (c i : ℝ)) (fun i => (c' i : ℝ)) S →
    |(∑ i, ph ((w : ℝ) + c i)) - ∑ i, ph ((w : ℝ) + c' i)| ≤
      ((w : ℝ) + 2 * S) * Real.log ((w : ℝ) + S + 2)
def hookProd (μ : YoungDiagram) : ℕ :=
  ∏ x ∈ μ.cells, ((μ.rowLen x.1 - x.2) + (μ.colLen x.2 - x.1) - 1)
def HookFact : Prop :=
  ∀ μ : YoungDiagram, ∏ i ∈ Finset.range (μ.colLen 0), (μ.rowLen i).factorial ≤ hookProd μ
def HookLog : Prop :=
  ∀ μ : YoungDiagram,
    (∑ i ∈ Finset.range (μ.colLen 0), Real.log ((μ.rowLen i).factorial : ℝ)) -
        ((μ.colLen 0 : ℝ) ^ 2) * Real.log ((μ.rowLen 0 : ℝ) + μ.colLen 0) ≤
      Real.log (hookProd μ : ℝ)
end Formalism.LatticeIndexTer


