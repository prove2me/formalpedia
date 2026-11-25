-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePLogExSt
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePLogExSt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:24.714419+00:00
-- url     : https://prove2.me/theorems/6a0a06c7-d67e-49b1-932e-5920567e75c3
-- title:
--   Row Tie PLog Ex St
-- statement:
--   Definitions and structural lemmas for Row Tie PLog Ex St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePLogExSt.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCuts
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Classical
namespace Formalism.L2.FormalSeriesBounds
namespace LogEx
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
def LinN {C : Type} [CommRing C] {dd : ℕ} (f : Pt C 1 dd) : Prop :=
  ∀ i (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 →
    MvPowerSeries.coeff μ (f i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd)
def LogSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (dd : ℕ) (G : FGLaw C dd), ∃ lg : Pt C 1 dd, LinN lg ∧
    ∀ i, ev (n := 2) ![addOf G.F (pt C dd 0) (pt C dd 1)] (lg i) =
      ev (n := 2) ![pt C dd 0] (lg i) + ev (n := 2) ![pt C dd 1] (lg i)
def RInvSt : Prop :=
  ∀ (C : Type) [Field C] (dd : ℕ) (φ : Pt C 1 dd), LinN φ → ∃ ψ : Pt C 1 dd, LinN ψ ∧ comp1 φ ψ = pt C dd 0
section Gen
variable {C : Type} [CommRing C] {dd : ℕ}
end Gen
end LogEx
end Formalism.L2.FormalSeriesBounds


