-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:03:07.186969+00:00
-- url     : https://prove2.me/theorems/fbbe40df-194e-40d9-97c7-a7a2f409781f
-- title:
--   Cut GCore GTCLRad TCut
-- statement:
--   Definitions and structural lemmas for Cut GCore GTCLRad TCut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTCut.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLocalCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def ZJ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r N : ℕ) (f : Q.Mx k r → E) (g₀ : Q.Mx k r) : Prop :=
  ∃ (U : Set (Q.Mx k r)) (F : Q.Mx k r → E), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧
    (∀ g ∈ U, g ∈ Q.Glev k r (Fin.last r) → f g = F g) ∧ ∀ j ≤ N, iteratedFDeriv ℝ j F g₀ = 0
def GTCLRJetT : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (a b : Fin 2), ∃ N : ℕ, ∀ (f : Q.Mx k r → E) (g₀ : Q.Mx k r), g₀ ∈ Q.Glev k r (Fin.last r) →
      ZJ k r N f g₀ → Q.tL k r z z' (Fin.last r) Y a b f g₀ = 0
def GTCLRJetRad : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
    ∀ N : ℕ, (∀ j ≤ N, iteratedFDeriv ℝ j
        (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)) q.2 = 0) →
      ZJ P.k P.r N ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1) (NF.muZ P.k P.r Bs.μsec q.2)
def GTCLRTaylor : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (ψ : ℂ → V) (U : Set ℂ) (ζ₀ : ℂ) (N : ℕ),
    IsOpen U → ζ₀ ∈ U → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ U →
    ∀ i ≤ N, iteratedFDeriv ℝ i (fun ζ => ψ ζ - ∑ j ∈ Finset.range (N + 1),
        ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) ζ₀ = 0
def GTCLRadTOfCut : Prop := GTCLRJetT → GTCLRJetRad → GTCLRTaylor → GTCLRadT
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC


