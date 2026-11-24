-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
-- name    : Formalism_LocalToGlobal_CharacterGerms_NegMem
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T11:28:14.504096+00:00
-- url     : https://prove2.me/theorems/78072b67-59a2-4936-8ad1-26c9c3e29cf5
-- title:
--   Neg Mem
-- statement:
--   Definitions and structural lemmas for Neg Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NegMem.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValNonnegLeadingCoeffOfMemTySet
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
def AddCvSt (V : VF C) : Prop :=
  ∀ γ γ' : κ → PowerSeries C, IsCv V γ → IsCv V γ' →
    ∃ γ'' : κ → PowerSeries C, IsCv V γ'' ∧
      (∀ i, alongCv γ'' (X.lg i) = alongCv γ (X.lg i) + alongCv γ' (X.lg i)) ∧
      ∀ v : κ → C, (∀ i, V.Ge 0 (v i)) →
        PowerSeries.constantCoeff (alongCv γ'' (X.sg v) - alongCv γ (X.sg v) - alongCv γ' (X.sg v)) = 0 ∧
        ∀ n, V.Ge 0 (PowerSeries.coeff n (alongCv γ'' (X.sg v) - alongCv γ (X.sg v) - alongCv γ' (X.sg v)))
end RawChart
end Formalism.L2.FormalSeriesBounds


