-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:47:38.66863+00:00
-- url     : https://prove2.me/theorems/37206855-9d77-40da-8deb-5cd00f2d7473
-- title:
--   Base Index Constant Injective
-- statement:
--   Definitions and structural lemmas for Base Index Constant Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BaseIndexConstantInjective.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val


set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2
section ring
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}
def c0 (a : Fin (2 * r + k + 1)) : Fin (Q.mdim k r 0) := Fin.cast (by simp [Q.mdim]) a
def E0 (hD : IsOpen D) (a b : Fin (2 * r + k + 1)) : Module.End ℂ (VS k r 0 D E) := Eh hD (c0 a) (c0 b)
def vK (hD : IsOpen D) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K) : VS k r 0 D E :=
  ⟨cut k r 0 D K, cut_mem hD hK⟩
def La (hD : IsOpen D) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K) (x₁ : Q.Mx k r) :
    Module.End ℂ (VS k r 0 D E) →ₗ[ℂ] E where
  toFun X := ((X (vK hD K hK)) : Q.Mx k r → E) x₁
  map_add' X Y := by simp [LinearMap.add_apply]
  map_smul' c X := by simp [LinearMap.smul_apply]
end ring
end Formalism.FourierDecayAlt.P.PBG


