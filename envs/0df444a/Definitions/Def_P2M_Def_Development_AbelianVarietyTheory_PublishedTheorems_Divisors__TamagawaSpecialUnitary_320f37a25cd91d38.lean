-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__TamagawaSpecialUnitary_320f37a25cd91d38
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__TamagawaSpecialUnitary_320f37a25cd91d38
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:57.769872+00:00
-- url     : https://prove2.me/theorems/2b0ec11a-6a26-4b8a-a1c8-6df12b8481ee
-- title:
--   Tamagawa Special Unitary
-- statement:
--   Definitions and structural lemmas for Tamagawa Special Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/TamagawaSpecialUnitary.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EmbGLMemRealSU_dd53fabb718cd1c0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Published
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol
open scoped ENNReal
def TamagawaSpecialUnitary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ))
    [MeasurableSpace (realSU Ψ G)] [BorelSpace (realSU Ψ G)]
    (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E)
    (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)),
    2 ≤ r → Unr E → SelfDualLat G Λ →
    (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) →
    (∀ i, e i ∈ lieLat G Λ) → LinearIndependent (maximalRealSubfield E) e →
    IsSReps G (Λ : Set (Fin r → E)) 1 s →
    Multipliable (locFactor E r) ∧
    (∑' j, covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) (realSU Ψ G)
        (tangentHaar (realSU Ψ G) (formLie Ψ e))) *
      ENNReal.ofReal (|(discr (maximalRealSubfield E) : ℝ)| ^ (-((r : ℝ) ^ 2 - 1) / 2) *
        ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) *
        ∏' v, locFactor E r v) = 1
end GlobalTheory.Published


