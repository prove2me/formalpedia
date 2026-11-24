-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ClassCountWaLat
-- name    : Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ClassCountWaLat
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:00:47.652514+00:00
-- url     : https://prove2.me/theorems/b532e6a9-158a-45de-b429-c8fe8d405320
-- title:
--   Class Count Wa Lat
-- statement:
--   Definitions and structural lemmas for Class Count Wa Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ClassCountWaLat.lean

import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.MainNotions.Gaps.CC.Surj
open Formalism.UG
def WACore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ e, σ (σ e) = e) → (∃ θ, σ θ ≠ θ) → IsHerm (σ : E →+* E) J → IsUnit J.det →
    ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ g ∈ UPts σ J (v.adicCompletion F), ∀ D : 𝓞 F, D ≠ 0 →
    ∃ γ ∈ UJ (σ : E →+* E) J, ∀ i j,
      ∃ s ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring,
        (g : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
            inclE (F := F) (v.adicCompletion F) ((γ : Matrix n n E) i j) =
          inclE (F := F) (v.adicCompletion F) (algebraMap F E (D : F)) * s
def WeakApprox1 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ e, σ (σ e) = e) → (∃ θ, σ θ ≠ θ) → IsHerm (σ : E →+* E) J → IsUnit J.det →
    ∀ (Λ : Submodule (𝓞 E) (n → E)), Module.Finite (𝓞 E) Λ →
    Submodule.span E (Λ : Set (n → E)) = ⊤ → ∀ (v : HeightOneSpectrum (𝓞 F)),
    ∀ g ∈ UPts σ J (v.adicCompletion F), ∃ γ ∈ UJ (σ : E →+* E) J,
      (bc (inclE (F := F) (v.adicCompletion F)) γ)⁻¹ * g ∈
        stabGL (latS (F := F) (v.adicCompletion F)
          (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ)
section Abs
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
def walInt (S : Subring A) (M : Matrix n n A) : Prop := ∀ i j, M i j ∈ S
end Abs
section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]
local notation "Av" => E ⊗[F] v.adicCompletion F
local notation "Sv" => Formalism.UG.P.lvS F E v
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
end Loc
end Formalism.MainNotions.Gaps.CC.Surj


