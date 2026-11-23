-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:44.996817+00:00
-- url     : https://prove2.me/theorems/fc5f246e-ae17-4cb7-a104-fef8e4ffde64
-- title:
--   Etale Integrality Facts
-- statement:
--   Definitions and structural lemmas for Etale Integrality Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Filter Topology
section Calc
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
def DB (q : ℕ) (f : E → F) (u : E) (S P : ℝ) : Prop :=
  ContDiffAt ℝ q f u ∧ ∀ j ≤ q, ‖iteratedFDeriv ℝ j f u‖ ≤ S * P ^ j
end Calc
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Formalism.FourierDecayAlt.G Matrix
noncomputable section
def Xm (m : ℕ) (p : XY m) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := strictUpper (redOf m p).2.2.1
def Bm (m : ℕ) (p : XY m) : Fin (m + 1) → ℂ := (redOf m p).2.2.2
def rm (m : ℕ) (p : XY m) : Fin m → ℂ := (redOf m p).2.1
def sm (m : ℕ) (p : XY m) : ℂ := (redOf m p).1
def cof1XY (m : ℕ) (t : ℂ) (p : XY m) : ℂ :=
  ∑ j ∈ Finset.range m, ((-Xm m p) ^ j *ᵥ Bm m p) 0 * t ^ (m - 1 - j)
def r1XY (m : ℕ) (t : ℂ) (p : XY m) : ℂ :=
  ∑ j ∈ Finset.range m, (∑ k : Fin m, rm m p k * ((-Xm m p) ^ j *ᵥ Bm m p) k.succ) * t ^ (m - 1 - j)
def cof0XY (m : ℕ) (p : XY m) : ℂ := (-1) ^ m * ∏ k, p.1 k
def gExt (m : ℕ) (D t : ℂ) (p : XY m) : ℂ :=
  ((t ^ m * sm m p - r1XY m t p) * cof0XY m p + D * cof1XY m t p) * (cofXY m t p)⁻¹ * (cof0XY m p)⁻¹
end
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Formalism.FourierDecayAlt.G Matrix Filter Topology
noncomputable section
def ampE {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ) (Φ : Mat (m + 1 + 1) → V)
    (D t : ℂ) (p : XY m) : V :=
  (psi β (gExt m D t p) * (((‖cofXY m t p‖ ^ 2)⁻¹ : ℝ) : ℂ)) • Φ (MXY m D t p)
section Gen
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
end Gen
section Poly
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m q : ℕ} {tt : E → ℂ}
  {xx : E → Fin (m + 1) → ℂ} {yy : E → UT (m + 2) → ℂ} {u : E} {Q : ℝ}
end Poly
end
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology
noncomputable section
end
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far Matrix Filter Topology
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology MeasureTheory
noncomputable section
def CoreProp (a b : ℕ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m q : ℕ) (β D : ℂ) (tt : E → ℂ)
    (xx : E → Fin (m + 1) → ℂ) (yy : E → UT (m + 2) → ℂ) (u : E) (Q W : ℝ),
    2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial ≤ Q → DB q tt u Q 1 → (∀ k, DB q (fun v => xx v k) u Q 1) →
    (∀ e, DB q (fun v => yy v e) u Q 1) → ‖D‖ ≤ Q → ‖β‖ ≤ Q → Q ^ (4 * (m + 2)) ≤ W →
    cofXY m (tt u) (xx u, yy u) ≠ 0 → ‖cofXY m (tt u) (xx u, yy u)‖⁻¹ ≤ W →
    ∏ k, xx u k ≠ 0 → ‖∏ k, xx u k‖⁻¹ ≤ W →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Φ : Mat (m + 1 + 1) → V) (K' : ℝ),
      DB q Φ (MXY m D (tt u) (xx u, yy u)) K' 1 →
      DB q (fun v => ampE β m Φ D (tt v) (xx v, yy v)) u (K' * W ^ a) (W ^ b)
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
end
end
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim


