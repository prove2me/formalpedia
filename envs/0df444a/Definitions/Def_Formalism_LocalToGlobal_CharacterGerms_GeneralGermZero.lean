-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
-- name    : Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:56:02.875329+00:00
-- url     : https://prove2.me/theorems/fe33d4f1-c178-4b8d-9384-b13ce96232a5
-- title:
--   General Germ Zero
-- statement:
--   Definitions and structural lemmas for General Germ Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeneralGermZero.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
namespace GeneralGermZero
open Formalism.IncomingBounds FormalGermZero
variable {C : Type} [Field C] {κ : Type} [Fintype κ]
def addK {σ : Type} (F : κ → MvPowerSeries (Fin 2 × κ) C) (a b : κ → MvPowerSeries σ C) : κ → MvPowerSeries σ C :=
  fun k => MvPowerSeries.subst (fun q : Fin 2 × κ => ![a, b] q.1 q.2) (F k)
def gsumK {σ ι : Type} (F : κ → MvPowerSeries (Fin 2 × κ) C) (Γ : ι → κ → MvPowerSeries σ C) :
    List ι → κ → MvPowerSeries σ C
  | [] => 0
  | c :: l => addK F (Γ c) (gsumK F Γ l)
def LgAdd (F : κ → MvPowerSeries (Fin 2 × κ) C) (lg : κ → MvPowerSeries κ C) : Prop :=
  ∀ k, MvPowerSeries.subst F (lg k) =
    MvPowerSeries.subst (fun q : κ => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × κ) C)) (lg k) +
      MvPowerSeries.subst (fun q : κ => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × κ) C)) (lg k)
section Sum
variable {F : κ → MvPowerSeries (Fin 2 × κ) C} (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
include hF0
end Sum
section Sys1
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ)
  (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
  (hFI : ∀ k, IntS V (F k)) (hadd : LgAdd F X.lg)
  (hlin : ∀ k (μ : κ →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ (X.lg k) = MvPowerSeries.coeff μ (MvPowerSeries.X k))
  (hexlg : ∀ k, MvPowerSeries.subst X.lg (X.ex k) = (MvPowerSeries.X k : MvPowerSeries κ C))
include hF0 hFI hadd hlin hexlg
end Sys1
end GeneralGermZero
end Formalism.L2.FormalSeriesBounds


