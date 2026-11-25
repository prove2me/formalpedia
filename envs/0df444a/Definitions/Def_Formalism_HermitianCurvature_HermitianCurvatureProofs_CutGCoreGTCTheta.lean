-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCTheta
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCTheta
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:11:20.514624+00:00
-- url     : https://prove2.me/theorems/8f119d32-9bf4-4806-b226-bf1b10ff325b
-- title:
--   Cut GCore GTCTheta
-- statement:
--   Definitions and structural lemmas for Cut GCore GTCTheta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCTheta.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCRefCut
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
def rhoSum (P : M.Par) (ρ : M.Ty P) : ℝ := ∑ i ∈ Finset.Icc 1 (P.k - 1), M.rho P ρ i
def uSum (P : M.Par) : ℝ := ∑ i ∈ Finset.Icc 1 P.k, (P.u i + P.u' i)
def ThetaNF (P : M.Par) {𝒜 : Type} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : Q.NFData P 𝒜) : 𝒜 :=
  d.L.ζ * d.L.nab + d.L.ζb * d.L.nabs + d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ)) +
    algebraMap ℂ 𝒜 d.L.TT * d.L.GGi * d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))
def GTRTopNF : Prop :=
  ∀ (P : M.Par) (𝒜 : Type) [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : Q.NFData P 𝒜),
    P.OK → 2 ≤ P.k → Fr.IsStarLevel d.L → d.Rel → d.L.TT = ((P.TT : ℝ) : ℂ) →
    ∃ c : ℕ → 𝒜, (∀ Y : ℂ, d.QQ Y 0 0 = ∑ j ∈ Finset.range (P.k + 2), Y ^ j • c j) ∧
      ∃ s : ℤ, c P.k = ThetaNF P d + ((s : ℂ)) • (1 : 𝒜)
def GTRTopAct : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ X : Q.ActualOps P.k P.r z z' π π',
    ∃ c : ℕ → Module.End ℂ (Q.RadSp P.k P.r z z' π π'),
      (∀ Y : ℂ, X.t Y 0 0 = ∑ j ∈ Finset.range (P.k + 2), Y ^ j • c j) ∧
      ∃ s : ℤ, ∀ (Φ : Q.RadSp P.k P.r z z' π π'), ∀ x ∈ Q.DomR P.k P.r z z',
        (c P.k Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC


