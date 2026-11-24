-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:26:44.633295+00:00
-- url     : https://prove2.me/theorems/e43e076a-9e93-4160-8c35-1f798043e088
-- title:
--   Hermitian Levi Vector Base Orthogonal
-- statement:
--   Definitions and structural lemmas for Hermitian Levi Vector Base Orthogonal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianLeviVectorBaseOrthogonal.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
def iF (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩
def iL (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩
def xi (k r' : ℕ) (p : ℂ × HPar k r') : Fin (2 * (1 + r') + k + 1) → ℂ :=
  p.1 • (es0 k r' + liftVec k 1 r' p.2.1 + hb k r' p.2.1 p.2.2 • e0 k r')
def eta (k r' : ℕ) (v : Fin (2 * (1 + r') + k + 1) → ℂ) : ℂ × HPar k r' :=
  (v (iL k r'), (fun j => v (levPos k 1 r' j) / v (iL k r'), (v (iF k r') / v (iL k r')).im))
def tau (k r' : ℕ) (p : ℂ × HPar k r') : Mt k (1 + r') := heis0 k r' p.2 * w0 k r' p.1
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r r' : ℕ}
def adjF (x : Mt k r) : Mt k r := (Matrix.of x : Mat k r).adjugate
def detF (x : Mt k r) : ℂ := (Matrix.of x : Mat k r).det
def heisF (k r' : ℕ) (x : HPar k r') : Mt k (1 + r') := heis0 k r' x
def w0F (k r' : ℕ) (c : ℂ) : Mt k (1 + r') := w0 k r' c
def Psi (k r' : ℕ) (p : ℂ × ((HPar k r' × HPar k r') × Mt k r')) : Mt k (1 + r') :=
  oneStep k r' p.2.1.1 p.1 (Matrix.of p.2.2) p.2.1.2
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
def wt (k r' : ℕ) (c : ℂ) : ℝ≥0∞ := ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1)))
def mC (k r' : ℕ) : Measure ℂ := (volume : Measure ℂ).withDensity (wt k r')
def mCone (k r' : ℕ) : Measure (ℂ × HPar k r') := (mC k r').prod volume
def muP (μG₁ : Measure (Mt k r')) : Measure (Mt k (1 + r')) := ((μHeis k r').prod (μG₁.map (levM k r'))).map mulM
def Ff (μP : Measure (Mt k (1 + r'))) (f : Mt k (1 + r') → ℝ≥0∞) (g : Mt k (1 + r')) : ℝ≥0∞ := ∫⁻ q, f (mulM (g, q)) ∂μP
def II (μG₁ : Measure (Mt k r')) (f : Mt k (1 + r') → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ c : ℂ, wt k r' c * ∫⁻ p : (HPar k r' × HPar k r') × Mt k r', f (Psi k r' (c, p))
          ∂((volume : Measure (HPar k r' × HPar k r')).prod μG₁)
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
def nu (μG₁ : Measure (Mt k r')) : Measure (Mt k (1 + r')) :=
  ((mC k r').prod ((volume : Measure (HPar k r' × HPar k r')).prod μG₁)).map (Psi k r')
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9.S1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
def rho (k r' : ℕ) (g : Mt k (1 + r')) : Mt k (1 + r') :=
  ιLev k 1 r' (fun i j => g (levPos k 1 r' i) (levPos k 1 r' j))
end Formalism.FourierDecayAlt.P.B2x9.S1
namespace Formalism.FourierDecayAlt.P.B2x9.S2
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.B2x9.S2
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P


