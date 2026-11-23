-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsRowLoc
-- name    : Formalism_LocalToGlobal_GaloisLevelStructure_DefsRowLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:02.879476+00:00
-- url     : https://prove2.me/theorems/f6c4a4a3-bc5d-4593-ab35-06ca9729864f
-- title:
--   Defs Row Loc
-- statement:
--   Definitions and structural lemmas for Defs Row Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GaloisLevelStructure/DefsRowLoc.lean

import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAutLoc
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
namespace Formalism.L2.NG
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
local notation3 "L⁺" => NumberField.maximalRealSubfield L
variable {L n}
variable {W : Type} [AddCommGroup W] [Module ℂ W]
def SatAtS (S : Submodule ℂ (GAf L n → W)) {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)}
    (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ) : Prop :=
  ∃ f ∈ S, f ≠ 0 ∧ ∃ U : Subgroup (GAf L n), (∀ κ ∈ U, rt L n κ f = f) ∧
    (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) ∧
    ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n),
      heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV L⁺ v) h α • f
end Formalism.L2.NG


