-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T16:50:31.385271+00:00
-- url     : https://prove2.me/theorems/ba97da6a-8bb1-4d0c-b639-fa8fed30ef5e
-- title:
--   Operator Representations
-- statement:
--   Definitions and structural lemmas for Operator Representations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OperatorRepresentations.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace OperatorRepresentations
section Mul
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
def invL (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) : Mx k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => ((Hpk k r * Mᴴ * Hpk k r) *ᵥ v) p
      map_add' := fun M N => by
        simp only [Matrix.conjTranspose_add, mul_add, add_mul, Matrix.add_mulVec, Pi.add_apply]
      map_smul' := fun c M => by
        simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec,
          Pi.smul_apply, RingHom.id_apply] }
def hrmL (k r : ℕ) (w x : Fin (2 * r + k + 1) → ℂ) : Mx k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => herm (Hpk k r) (M *ᵥ w) x
      map_add' := fun M N => by
        simp only [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c M => by
        simp only [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, RingHom.id_apply] }
end Mul
section Op
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
def Rep (X : Module.End ℂ (SV k r i D E)) (T : (Mx k r → E) → Mx k r → E) : Prop :=
  Qx2.Good k r i D T ∧ ∀ (φ : SV k r i D E), ∀ g ∈ Glev k r i ∩ D, (X φ).1 g = T φ.1 g
theorem Rep.mkV (hD : IsOpen D) {X : Module.End ℂ (SV k r i D E)} {T : (Mx k r → E) → Mx k r → E} (hX : Rep X T)
    {f : Mx k r → E} (hf : SmoothLev k r i D f) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    (X (mkV hD f hf)).1 g = T f g := by
  rw [hX.2 _ g hg]
  exact hX.1.loc _ _ (fun x hx => cutF_of_mem hx) g hg
end Op
end OperatorRepresentations
end Formalism.FourierDecayAlt.P


