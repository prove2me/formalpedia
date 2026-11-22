-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:10.410231+00:00
-- url     : https://prove2.me/theorems/a54d626d-8b72-46a1-b49f-30d572ebfd71
-- title:
--   Orbital Integral Converges Abs
-- statement:
--   Definitions and structural lemmas for Orbital Integral Converges Abs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
instance sigmaFinite_mu (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance
instance sigmaFinite_muPi (β : ℂ) (ι : Type) [Fintype ι] : SigmaFinite (muPi β ι) := by
  unfold muPi; infer_instance
noncomputable def sig {m : ℕ} (D t : ℂ) (ρ : Fin (m + 1) → ℂ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (B : Fin (m + 1) → ℂ) : ℂ :=
  (D + ∑ j ∈ Finset.range (m + 1), (ρ ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (m + 1 - 1 - j)) / t ^ (m + 1)
noncomputable def Fint {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Φ : Mat (m + 1 + 1) → V) (t c : ℂ) (p : BlockCoord (m + 1)) : V :=
  psi β ((p.1 0 + ∑ k, xOf (strictUpper p.2.1) p.2.2 k) / t) •
    Φ (Mcoord t (strictUpper p.2.1) p.2.2 p.1 (sig (c * t ^ (m + 1)) t p.1 (strictUpper p.2.1) p.2.2))
def consMap (m : ℕ) (q : RedCoord m) : BlockCoord (m + 1) := (Fin.cons q.1 q.2.1, q.2.2)
noncomputable def cofLin {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (t : ℂ) :
    (Fin (m + 1) → ℂ) →ₗ[ℝ] ℂ where
  toFun B := Cof X B t
  map_add' B B' := by simp [Cof, Matrix.mulVec_add, add_mul, Finset.sum_add_distrib]
  map_smul' r B := by
    simp only [Cof, Matrix.mulVec_smul, Pi.smul_apply, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]
end Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


