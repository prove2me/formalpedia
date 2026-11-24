-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGLev
-- name    : Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGLev
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T10:16:48.087531+00:00
-- url     : https://prove2.me/theorems/0a374290-b80e-421f-a8dd-7a20f33b9aeb
-- title:
--   At GLev
-- statement:
--   Definitions and structural lemmas for At GLev, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelCharts/AtGLev.lean

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGGlob
import Theorems.Thm_Formalism_L2_G_mem_placesOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
namespace Formalism.L2.G
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
structure LevAtG (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (gp : Fin 2 → ℕ)
    (splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (Lb : Submodule (𝓞 E) (Fin N → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))) (k m t j : ℕ) where

  frG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → GL (Fin N) (v.adicCompletion F)

  frG_lat : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (x : Fin N → v.adicCompletion F),
    (∃ y ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb,
      ∀ b, (splitG i v h (y b)).1 = x b) ↔
      ∀ b, (((frG i v h)⁻¹ : GL (Fin N) (v.adicCompletion F)) : Matrix (Fin N) (Fin N) (v.adicCompletion F)).mulVec x b ∈
        v.adicCompletionIntegers F

  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
    Uloc v = JXU σE J v (splitG i v h) (frG i v h) k m t j
variable {σE : E →ₐ[F] E} {J : Matrix (Fin N) (Fin N) E} {gp : Fin 2 → ℕ}
    {splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    {Lb : Submodule (𝓞 E) (Fin N → E)}
    {Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))} {k m t j : ℕ}
def LevAtG.lamV {Z : Type} [CommGroup Z] (X : LevAtG σE J gp splitG Lb Uloc k m t j) (i : Fin 2)
    (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (ψ0 : AddChar (resV F v) Z)
    (χ : ℕ → (resV F v)ˣ →* Z) : Uloc v →* Z :=
  (lamXU σE J v (splitG i v h) (X.frG i v h) k m t j ψ0 χ).comp (Subgroup.inclusion (le_of_eq (X.Uloc_g i v h)))
def LevAtG.lamGlob {Z : Type} [CommGroup Z] (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0)
    (ψ0 : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → AddChar (resV F v) Z)
    (χ : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ℕ → (resV F v)ˣ →* Z)
    (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hUp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      Up ≤ (Uloc v).comap (bc (prV (E := E) v))) : Up →* Z :=
  ∏ i : Fin 2, prodChar (placesOver F (gp i)) Uloc
    (fun v hv => X.lamV i v ((mem_placesOver F (gp i) (hg i) v).1 hv) (ψ0 i v ((mem_placesOver F (gp i) (hg i) v).1 hv))
      (χ i v ((mem_placesOver F (gp i) (hg i) v).1 hv)))
    Up (fun v hv => hUp i v ((mem_placesOver F (gp i) (hg i) v).1 hv))
end Formalism.L2.G


