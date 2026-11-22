-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:43.538286+00:00
-- url     : https://prove2.me/theorems/d8f1ca9e-f50c-4ba1-9e6e-9df24abbaba6
-- title:
--   Sat Gram Loc
-- statement:
--   Definitions and structural lemmas for Sat Gram Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLoc.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace Formalism.L2.SG.Pf.SatGramLoc
def SplitPrimeLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (p : ℕ), p.Prime →
    {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E →
      (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal →
        Nat.card (𝓞 F ⧸ v.asIdeal) = p ∧
          Valued.v ((p : ℕ) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) ∧
      {v : HeightOneSpectrum (𝓞 F) | ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}.ncard = Module.finrank ℚ F
def RedCore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ x, σ (σ x) = x) → Module.finrank F E = 2 →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : E ⊗[F] v.adicCompletion F),
      e ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring →
      e * e = e → e * Formalism.UG.sigR σ (v.adicCompletion F) e = 0 →
      (∃ c : v.adicCompletion F, Valued.v c < 1 ∧ ∃ t ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E)
          (v.adicCompletionIntegers F).toSubring,
        1 - e - Formalism.UG.sigR σ (v.adicCompletion F) e = ((1 : E) ⊗ₜ[F] c) * t) →
      ∃ r : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F,
        r e = 1 ∧ (∀ a : v.adicCompletion F, r ((1 : E) ⊗ₜ[F] a) = a) ∧
        (∀ x ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring,
          r x ∈ v.adicCompletionIntegers F) ∧
        ∀ x, e * x = x → x = ((1 : E) ⊗ₜ[F] r x) * e
end Formalism.L2.SG.Pf.SatGramLoc


