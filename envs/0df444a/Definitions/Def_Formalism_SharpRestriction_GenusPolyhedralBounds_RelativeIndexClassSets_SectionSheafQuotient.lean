-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_SectionSheafQuotient
-- name    : Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_SectionSheafQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:36.688261+00:00
-- url     : https://prove2.me/theorems/d912565b-e948-465e-9690-ead49e95bd6f
-- title:
--   Section Sheaf Quotient
-- statement:
--   Definitions and structural lemmas for Section Sheaf Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/SectionSheafQuotient.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Module
namespace Formalism.MainNotions.Gaps.HeightData
def lN (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm la.asIdeal : ℝ) / (finrank ℚ K : ℝ)
structure HtData where

  K : Type
  [fK : Field K]
  [nfK : NumberField K]

  D : ℕ
  δ : ℕ
  i : ℕ

  g0 : ℝ
  L : ℝ
  G : ℝ
  PH : ℝ
  Prw : ℝ
  Pet : ℝ

  S : Fin δ → ℝ

  etaPart : Prop

  Op : HeightOneSpectrum (𝓞 K) → Type
  [rOp : ∀ la, CommRing (Op la)]

  SectionSheafQuotient : HeightOneSpectrum (𝓞 K) → Type
  [gA : ∀ la, AddCommGroup (SectionSheafQuotient la)]
  [mA : ∀ la, Module (Op la) (SectionSheafQuotient la)]
  A0 : ∀ la, Submodule (Op la) (SectionSheafQuotient la)
  t : ∀ la, Fin δ → SectionSheafQuotient la

  Pts : HeightOneSpectrum (𝓞 K) → Type
  ep : ∀ la, Pts la → ℕ
  f : ∀ la, Pts la → ℕ
  vEt : ∀ la, Pts la → ℝ
attribute [instance] HtData.fK HtData.nfK HtData.rOp HtData.gA HtData.mA
namespace HtData
variable (H : HtData)
def Ila (la : HeightOneSpectrum (𝓞 H.K)) : ℕ∞ :=
  Module.length (H.Op la) (↥(H.A0 la) ⧸ (Submodule.span (H.Op la) (Set.range (H.t la))).comap (H.A0 la).subtype)
def Net (la : HeightOneSpectrum (𝓞 H.K)) : ℝ :=
  ∑ᶠ ζ, (H.ep la ζ : ℝ) * (H.f la ζ : ℝ) * H.vEt la ζ
end HtData
def HtConcl (H : HtData) : Prop :=
  (∀ la, H.Ila la ≠ ⊤) ∧ Summable (fun la => ((H.Ila la).toNat : ℝ) * lN H.K la) ∧
  2 * (∑' la, ((H.Ila la).toNat : ℝ) * lN H.K la) ≤
    (H.δ : ℝ) * Real.log H.δ + 2 * ∑ k, H.S k +
      8 / 3 * (H.D : ℝ) * ((H.D : ℝ) + 4) * H.δ * H.Prw * H.L +
      2 * ((H.D : ℝ) + 4) * ((H.D : ℝ) + 1) * H.δ * (2 * H.G + 6 * H.PH) * H.L ∧
  (H.etaPart → Summable (fun la => H.Net la * lN H.K la) ∧
    (∑' la, H.Net la * lN H.K la) / (H.i : ℝ) ≤
      H.g0 * (((H.D : ℝ) + 1) * H.δ * (2 * H.G + 6 * H.PH) * H.L + 4 / 3 * (H.D : ℝ) * H.δ * H.Prw * H.L) +
        H.δ * H.Pet)
end Formalism.MainNotions.Gaps.HeightData


