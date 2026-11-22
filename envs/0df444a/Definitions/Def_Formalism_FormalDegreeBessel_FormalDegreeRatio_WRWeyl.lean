-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:05:27.977934+00:00
-- url     : https://prove2.me/theorems/078d154a-c664-4bb8-a799-ded5e568931f
-- title:
--   WRWeyl
-- statement:
--   Definitions and structural lemmas for WRWeyl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
namespace Formalism.QuantumDeterminants
namespace WirtingerDerivatives
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def Wc (u w : Fin m → ℂ) (s : ℂ) : ((Fin m → ℂ) →L[ℝ] E) →L[ℝ] E :=
  (ContinuousLinearMap.lsmul ℝ ℂ (1 / 2 : ℂ)).comp
    (ContinuousLinearMap.apply ℝ E u +
      (ContinuousLinearMap.lsmul ℝ ℂ s).comp (ContinuousLinearMap.apply ℝ E w))
def Reg (g : (Fin m → ℂ) → E) : Prop := ∀ x ∈ OmX m, ContDiffAt ℝ ∞ g x
def coef (k : Fin m) : Fin 6 → (Fin m → ℂ) → ℂ
  | 0 => fun y => y k
  | 1 => fun y => y k
  | 2 => fun y => (y k)⁻¹
  | 3 => fun y => star (y k)
  | 4 => fun y => star (y k)
  | 5 => fun y => (star (y k))⁻¹
def ck (k : Fin m) : Fin 6 → (Fin m → ℂ) → ℂ
  | 0 => fun _ => 1
  | 1 => fun _ => 1
  | 2 => fun y => -((y k) ^ 2)⁻¹
  | 3 => fun _ => 1
  | 4 => fun _ => 1
  | 5 => fun y => -((star (y k)) ^ 2)⁻¹
def Dop (k : Fin m) : Fin 6 → ((Fin m → ℂ) → E) → (Fin m → ℂ) → E
  | 0 => wirt k
  | 1 => fun g => g
  | 2 => fun g => g
  | 3 => wirtBar k
  | 4 => fun g => g
  | 5 => fun g => g
def dco (l : Fin m) (i : Fin 6) (k : Fin m) (j : Fin 6) (x : Fin m → ℂ) : ℂ :=
  match i with
  | 0 => wirt l (coef k j) x
  | 3 => wirtBar l (coef k j) x
  | _ => 0
end WirtingerDerivatives
open WirtingerDerivatives
end Formalism.QuantumDeterminants


