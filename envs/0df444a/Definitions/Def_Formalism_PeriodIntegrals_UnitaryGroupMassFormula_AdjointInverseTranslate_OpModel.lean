-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T15:10:32.014597+00:00
-- url     : https://prove2.me/theorems/ee706b58-c51e-431b-9c68-6ba80ec29157
-- title:
--   Op Model
-- statement:
--   Definitions and structural lemmas for Op Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OpModel.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
def OpModel : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), HInvol H →
    ∃ (M : Submodule ℂ ({x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E))
      (cls : (Matrix (Fin n) (Fin n) ℂ → E) → M) (Eh : Fin n → Fin n → Module.End ℂ M),
      GlRel Eh ∧
      (∀ (t : ℕ) (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
          (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUH H g),
        SmoothOnH H f → qminorOp (EabH H) a b u f g = ((qminor Eh a b u (cls f) : M) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨g, hg⟩) ∧
      ∀ s : Matrix (Fin n) (Fin n) ℂ, inUH H s → ∃ ρ : Module.End ℂ M,
        (∀ f : Matrix (Fin n) (Fin n) ℂ → E, SmoothOnH H f → cls (fun x => f (x * s)) = ρ (cls f)) ∧
        (∀ (ψ : M) (y : Matrix (Fin n) (Fin n) ℂ) (hy : inUH H y) (y' : Matrix (Fin n) (Fin n) ℂ)
            (hy' : inUH H y'), y' = y * s → ((ρ ψ : M) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨y, hy⟩ = (ψ : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨y', hy'⟩) ∧
        ∀ a b : Fin n, Eh a b * ρ = ρ * ∑ c, ∑ d, (s⁻¹ c a * s b d) • Eh c d
end AAInvW


