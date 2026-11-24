-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:01:46.971796+00:00
-- url     : https://prove2.me/theorems/a60c7336-5765-4998-81cf-1be6efca420f
-- title:
--   Is Split Place Of Split Pl
-- statement:
--   Definitions and structural lemmas for Is Split Place Of Split Pl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
open Classical in

def ind (S : Set (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun w => if w ∈ S then 1 else 0, Filter.Eventually.of_forall fun w => by
    by_cases h : w ∈ S
    · simp only [if_pos h]; exact one_mem _
    · simp only [if_neg h]; exact zero_mem _⟩
def HasRep (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (N : ℕ) : Prop :=
  ∀ g : GL (Fin n) (RA F E), IsUnA c G g.1 → ∃ (γ : GL (Fin n) E) (h k : GL (Fin n) (RA F E)),
    IsUnE c G γ.1 ∧ IsUnA c G h.1 ∧ IsUnA c G k.1 ∧ g.1 = fm F γ.1 * h.1 * k.1 ∧ SuppSplit c N h.1 ∧
    (∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), k.1 *ᵥ z - z = N • w) ∧
    ∀ z ∈ hat F (L : Set (Fin n → E)), (k⁻¹).1 *ᵥ z ∈ hat F (L : Set (Fin n → E))
def RepStatement (n₀ : ℕ) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ),
    n₀ ≤ n → ∀ G : Matrix (Fin n) (Fin n) E, IsHermForm c G → Module.finrank F E = 2 →
    ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
    ∀ N : ℕ, 0 < N → HasRep c G L N
end GlobalTheory.UnRep.Compare


