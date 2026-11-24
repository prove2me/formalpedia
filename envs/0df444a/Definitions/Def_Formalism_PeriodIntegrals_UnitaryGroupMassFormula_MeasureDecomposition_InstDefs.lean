-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T13:28:33.821486+00:00
-- url     : https://prove2.me/theorems/4be79f4e-aabb-4991-944c-9bbe501b2b4e
-- title:
--   Inst Defs
-- statement:
--   Definitions and structural lemmas for Inst Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstDefs.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Theorems.Thm_Formalism_REAL_uJInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField Matrix
open scoped ENNReal Pointwise
namespace PI.ScMuExists.UnitaryGroupMassFormula
def instFvec {I : Formalism.MainNotions.S.AutInst} {r : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) :
    Fin r ⊕ Fin r ⊕ Unit → Fin I.n → I.E
  | Sum.inl a => e a
  | Sum.inr (Sum.inl a) => f a
  | Sum.inr (Sum.inr _) => z
def instBmat (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {r : ℕ} (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) : Matrix (Fin I.n) (Fin r ⊕ Fin r ⊕ Unit) ℂ :=
  Matrix.of fun i j => rv I v (instFvec e f z j) i
def instMkUJ {n : ℕ} (ε : Fin n → Bool) (m : Matrix (Fin n) (Fin n) ℂ) (hm : Formalism.REAL.inUJ ε m) :
    Formalism.REAL.UJ ε :=
  ⟨⟨m, Formalism.REAL.Jm ε * mᴴ * Formalism.REAL.Jm ε, (Formalism.REAL.uJInv n ε m hm).1, (Formalism.REAL.uJInv n ε m hm).2⟩, hm⟩
def InstExpFix : Prop :=
  ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ), X.IsHermitian → ∀ w : Fin n → ℂ,
    NormedSpace.exp X *ᵥ w = w ↔ X *ᵥ w = 0
def InstAdaptBasis : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix (Fin n) ι ℂ),
    IsUnit (Bᴴ * Formalism.REAL.Jm ε * B) →
    ∃ (A : Matrix (Fin n) (Fin n) ℂ) (ε' : Fin n → Bool) (T : Finset (Fin n)),
      Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε' ∧
      (∀ i ∈ T, ∃ c : ι → ℂ, A *ᵥ Pi.single i 1 = B *ᵥ c) ∧
      (∀ j : ι, ∃ c : Fin n → ℂ, (∀ i ∉ T, c i = 0) ∧ B *ᵥ Pi.single j 1 = A *ᵥ c)
def InstPlaceDecomp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix (Fin n) ι ℂ),
    IsUnit (Bᴴ * Formalism.REAL.Jm ε * B) →
    ∀ g : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inUJ ε g → g * B = B →
    ∃ k p σ : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inUJ ε k ∧ Formalism.REAL.inUJ ε p ∧ Formalism.REAL.inUJ ε σ ∧
      k * B = B ∧ p * B = B ∧ σ * B = B ∧ g = k * p ∧ σ * σ = 1 ∧ σ * p * σ * p = 1 ∧
      ∃ C : Set (Formalism.REAL.UJ ε), IsCompact C ∧ (1 : Formalism.REAL.UJ ε) ∈ interior C ∧
        ∀ x y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.uMat y * k = k * Formalism.MainNotions.S.uMat x → (y ∈ C ↔ x ∈ C)
def InstFrameGram : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E), IsFrame I e f z →
    ∀ v, IsUnit ((instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z)
end PI.ScMuExists.UnitaryGroupMassFormula


