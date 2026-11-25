-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoRatioPow
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoRatioPow
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T07:19:35.249127+00:00
-- url     : https://prove2.me/theorems/ea5d8f32-452f-4238-a513-7082a3943e8f
-- title:
--   Tendsto Ratio Pow
-- statement:
--   Definitions and structural lemmas for Tendsto Ratio Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoRatioPow.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemLpBzOfSup
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralInnerGermMoving
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
section propGD
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
structure GermD {ι : Type} (s : ℕ) (β ε : ℂ) (Y : Finset ι) (ut : ι → ℂ → ℂ → H) (bt : ι → ℂ → H) (SS : ℝ) :
    Prop where
  hs : s ≠ 0
  hβ : β ≠ 0
  hε : ‖ε‖ = 1
  memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (ut h x) 2 volume
  sup : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ∫ D, ‖ut h x D‖ ^ 2 ≤ SS
  meas : ∀ h ∈ Y, StronglyMeasurable (bt h)
  loc : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖bz s (bt h) z‖ ^ 2) K
  germ : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
    ∀ᵐ D, D ∈ K → ‖ut h x D - mainD s β ε (bt h) x D‖ ≤ C * ‖x‖⁻¹
def Uc {ι : Type} (s : ℕ) (ut : ι → ℂ → ℂ → H) : ι × ℂ → ℂ → H := fun p => cvec s (ut p.1) p.2
def Ac {ι : Type} (s : ℕ) (β ε : ℂ) (bt : ι → ℂ → H) : ι × ℂ → ℂ → H :=
  fun p => cvec s (fun x D => mainD s β ε (bt p.1) x D) p.2
def Nhat {ι : Type} (s : ℕ) (β : ℂ) (bt : ι → ℂ → H) (σ : ℂ) (h h' : ι) : ℂ :=
  ∫ z, G.psi β (σ * z) • ⟪bz s (bt h) z, bz s (bt h') z⟫_ℂ
variable {ι : Type} {s : ℕ} {β ε : ℂ} {Y : Finset ι} {ut : ι → ℂ → ℂ → H} {bt : ι → ℂ → H} {SS : ℝ}
end propGD
end
end Formalism.FourierDecayAlt.P.PBK


