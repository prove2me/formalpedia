-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T14:27:16.434997+00:00
-- url     : https://prove2.me/theorems/1210ec66-5641-456f-b342-96ea91be54cd
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/Development.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace QmCapCommW
def CapCongr : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (a b : Fin (mdim k r i)) (f f' : Mx k r → E), IsOpen D → (∀ g ∈ Glev k r i ∩ D, f g = f' g) →
    ∀ g ∈ Glev k r i ∩ D, EH k r (posL k r i a) (posL k r i b) f g = EH k r (posL k r i a) (posL k r i b) f' g
def QdetCommute : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ u v : ℂ, qdet E u * qdet E v = qdet E v * qdet E u
def CapTransfer : Prop := CapCongr → QdetCommute → EabPres → EabGlLev → CapCommute
example (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) :
    IsOpen (Set.univ : Set (Mx k r)) ∧ SmoothLev k r i Set.univ (fun _ => (0 : E)) ∧
      (1 : Mx k r) ∈ Glev k r i ∩ Set.univ :=
  ⟨isOpen_univ, fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
    ⟨⟨by simp [UH], fun _ _ => ⟨by simp, by simp⟩⟩, trivial⟩⟩
end QmCapCommW


