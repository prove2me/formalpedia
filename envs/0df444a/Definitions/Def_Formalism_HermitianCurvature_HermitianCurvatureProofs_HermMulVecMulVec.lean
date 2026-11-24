-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermMulVecMulVec
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HermMulVecMulVec
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:03:41.787894+00:00
-- url     : https://prove2.me/theorems/681ddf87-d10b-4a74-ab43-39d6019031ea
-- title:
--   Herm Mul Vec Mul Vec
-- statement:
--   Definitions and structural lemmas for Herm Mul Vec Mul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermMulVecMulVec.lean

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Wave
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}
lemma mul_mem (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x)
    (Φ : RadSp k r z z' π π') :
    (fun c g => m (c, g) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) ∈ RadSp k r z z' π π' := by
  have hΦm : (Φ : Fn k r (Wq →L[ℂ] Wp)) ∈ RadSp k r z z' π π' := Φ.2
  obtain ⟨h0, hs, he⟩ := hΦm
  refine (show _ ∧ _ ∧ _ from ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩)
  · show m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = 0
    rw [h0 x hx, smul_zero]
  · obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x₀ hx₀
    refine ⟨U, fun x => m x • F x, hU, hxU, hm.contDiffOn.smul hF, fun x hx hg => ?_⟩
    show m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = m x • F x
    rw [hΦ x hx hg]
  · show m (x.1, h * x.2 * h') • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 (h * x.2 * h') =
      (π h).comp ((m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2).comp (π' h'))
    rw [hinv x hx h hh h' hh', he x hx h hh h' hh']
    ext v
    simp
def mulOp (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x) :
    Module.End ℂ (RadSp k r z z' π π') where
  toFun Φ := ⟨_, mul_mem m hm hinv Φ⟩
  map_add' Φ Ψ := by
    ext c g v
    simp [smul_add]
  map_smul' a Φ := by
    ext c g v
    simp [smul_smul, mul_comm]
def hermLin (H : Mx k r) (v w : Fin (2 * r + k + 1) → ℂ) : Mx k r →ₗ[ℂ] ℂ where
  toFun g := herm H (g *ᵥ v) w
  map_add' g g' := by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
  map_smul' a g := by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul]
end Wave
section Zero
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
end Zero
end Formalism.FourierDecayAlt.P5


