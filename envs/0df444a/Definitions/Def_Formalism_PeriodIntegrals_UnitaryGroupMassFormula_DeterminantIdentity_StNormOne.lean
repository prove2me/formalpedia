-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_StNormOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_StNormOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:04.447111+00:00
-- url     : https://prove2.me/theorems/4e752d49-2466-4f89-bdad-d9d047a394f1
-- title:
--   St Norm One
-- statement:
--   Definitions and structural lemmas for St Norm One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/StNormOne.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DetIdPG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace PI.DIP
def detId (E : Type) [Field E] [NumberField E] (N : ℕ) (L₀ L : Submodule (𝓞 E) (Fin N → E)) :
    Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {x : E | ∃ A : Matrix (Fin N) (Fin N) E, (∀ v ∈ L₀, A.mulVec v ∈ L) ∧ x = A.det}
def IsLat (E : Type) [Field E] [NumberField E] (N : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin N → E)) = ⊤
def StAdj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) (L₀ L : Submodule (𝓞 E) (Fin N → E)),
    DetIdPG.IsSDLat E N L₀ → DetIdPG.IsSDLat E N L → ∀ x ∈ detId E N L₀ L, star x ∈ detId E N L L₀
def StProdLe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) (L₀ L : Submodule (𝓞 E) (Fin N → E)),
    IsLat E N L₀ → IsLat E N L → detId E N L₀ L * detId E N L L₀ ≤ 1
def StProdGe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) (L₀ L : Submodule (𝓞 E) (Fin N → E)),
    IsLat E N L₀ → IsLat E N L → 1 ≤ detId E N L₀ L * detId E N L L₀
def StScal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) (L₀ L : Submodule (𝓞 E) (Fin N → E)) (s : ℕ),
    (∀ x ∈ L₀, (s : E) • x ∈ L) → (s : E) ^ N ∈ detId E N L₀ L
def StNormOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ x, c (c x) = x) →
    ∀ 𝔞 𝔟 : Submodule (𝓞 E) E, (∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) → 𝔞 * 𝔟 = 1 →
      ∃ (h : ℕ) (z : E), 0 < h ∧ z * c z = 1 ∧ 𝔞 ^ h = Submodule.span (𝓞 E) {z}
def StIntNorm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (ψ : E →+* ℂ_[p]) (x : 𝓞 E),
    ‖ψ (x : E)‖ ≤ 1
end PI.DIP


