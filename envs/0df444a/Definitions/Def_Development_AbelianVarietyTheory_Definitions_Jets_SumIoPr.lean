-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
-- name    : Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:59.98491+00:00
-- url     : https://prove2.me/theorems/09f749ab-4057-4d70-915c-af2aa35ccc9b
-- title:
--   Sum Io Pr
-- statement:
--   Definitions and structural lemmas for Sum Io Pr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/SumIoPr.lean

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
namespace BranchingSupport
section alg
variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
def CasKLe (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (c : ℝ) (w : M) : Prop :=
  ∃ S : Submodule ℂ M, FiniteDimensional ℂ S ∧ (∀ a b, ε a = ε b → ∀ x ∈ S, E a b x ∈ S) ∧ w ∈ S ∧
    ∀ x ∈ S, (⟪x, Formalism.REAL.CasK ε E x⟫_ℂ).re ≤ c ^ 2 * ‖x‖ ^ 2
def WtNear (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) : Submodule ℂ M :=
  Submodule.span ℂ {x | ∃ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t ∧ Formalism.REAL.IsWeight E ω x}
def Lev (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (mu : Fin n → ℝ) (j : ℕ) (w : M) : Prop :=
  CasKLe ε E (Real.sqrt (Formalism.REAL.ckv ε (Formalism.QuantumDeterminants.lowK ε mu)) + 4 * (n : ℝ) * (j : ℝ)) w ∧
    w ∈ WtNear E (Formalism.QuantumDeterminants.lowK ε mu) (j : ℝ)
def casG (mu : Fin n → ℝ) : ℝ := (∑ a, mu a ^ 2) - ∑ a, Formalism.QuantumDeterminants.rhoStd n a ^ 2
def IsMod (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (mu : Fin n → ℝ) : Prop :=
  Formalism.REAL.GlRel E ∧ Formalism.REAL.IsUnitary ε E ∧ ∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w
def dualTens (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (x : Fin n → M) : Fin n → M :=
  fun i => E a b (x i) - if i = b then x a else 0
def hhJ (ε : Fin n → Bool) (x y : Fin n → M) : ℂ := ∑ c, (if ε c then 1 else -1) * ⟪y c, x c⟫_ℂ
def splitCas (E : Fin n → Fin n → Module.End ℂ M) (x : Fin n → M) : Fin n → M := fun b => -∑ c, E b c (x c)
structure AlgTens (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type)
    [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)]
    (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M))
    (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) : Prop where
  io_comm : ∀ s a b y, io s (F s a b y) = dualTens E a b (io s y)
  pr_comm : ∀ s a b x, pr s (dualTens E a b x) = F s a b (pr s x)
  sum_io_pr : ∀ x, ∑ s, io s (pr s x) = x
  pr_io : ∀ s y, pr s (io s y) = y
  pr_io_ne : ∀ s t, s ≠ t → ∀ y, pr s (io t y) = 0
  orth : ∀ s t, s ≠ t → ∀ y y', hhJ ε (io s y) (io t y') = 0
  sign : ∀ s, ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∀ y y', hhJ ε (io s y) (io s y') = (e : ℂ) * ⟪y', y⟫_ℂ
end alg
def Shape {n : ℕ} (ε : Fin n → Bool) (kk : ℕ) (mu : Fin n → ℝ) (bv : ℝ) : Prop :=
  1 ≤ kk ∧ kk + 1 ≤ n ∧ (∀ a c : Fin n, a < c → 2 ≤ mu a - mu c) ∧
  (∀ a : Fin n, a.val + 1 < kk → ε a = true ∧ -(bv / 100) ≤ mu a ∧ mu a ≤ bv / 8 + bv / 100) ∧
  (∀ a : Fin n, kk ≤ a.val + 1 → -2 * bv - bv / 100 ≤ mu a ∧ mu a ≤ -bv + bv / 100) ∧
  10 ^ 6 * (n : ℝ) ^ 7 ≤ bv
end BranchingSupport


