-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_FrameExists2
-- name    : Formalism_HermitianCurvature_FrameExists2
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:46:03.577811+00:00
-- url     : https://prove2.me/theorems/7ebaed23-d73b-40bd-af9d-9885b2eb798c
-- title:
--   Frame Exists2
-- statement:
--   Definitions and structural lemmas for Frame Exists2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/FrameExists2.lean

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.Qr
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def Trotter : Prop :=
  ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (X Y : 𝔸),
    Tendsto (fun n : ℕ => (NormedSpace.exp (((n : ℝ)⁻¹) • X) * NormedSpace.exp (((n : ℝ)⁻¹) • Y)) ^ n) atTop
      (𝓝 (NormedSpace.exp (X + Y)))
def TrotterMx : Prop :=
  ∀ (N : ℕ) (X Y : Matrix (Fin N) (Fin N) ℂ),
    Tendsto (fun n : ℕ => (NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • X) * NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • Y)) ^ n) atTop
      (𝓝 (NormedSpace.exp (X + Y)))
def InGlW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Z : Mx k r) : Prop :=
  InLieW k r z (hpart1 (Hpk k r) Z) ∧ InLieW k r z (hpart2 (Hpk k r) Z)
def IsRepW {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (π : Mx k r → (W →L[ℂ] W)) : Prop :=
  IsCRepOn (UWset k r z) π ∧ ContinuousOn π (UWset k r z)
def PiExp : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (k r : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (W →L[ℂ] W)), IsRepW k r z π → ∀ X, InLieW k r z X → ∀ t : ℝ,
      π (NormedSpace.exp ((t : ℂ) • X)) = NormedSpace.exp (t • dOp π X)
def DOpLin : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (k r : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (W →L[ℂ] W)), IsRepW k r z π → ∀ X Y, InLieW k r z X → InLieW k r z Y →
      dOp π (X + Y) = dOp π X + dOp π Y ∧ ∀ s : ℝ, dOp π ((s : ℂ) • X) = s • dOp π X
def DOpAd : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (k r : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (W →L[ℂ] W)), IsRepW k r z π → ∀ X, InLieW k r z X → ∀ h ∈ UWset k r z,
      h⁻¹ ∈ UWset k r z ∧ InLieW k r z (h * X * h⁻¹) ∧
        dOp π (h * X * h⁻¹) = (π h).comp ((dOp π X).comp (π h⁻¹))
def DOpBracket : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (k r : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (W →L[ℂ] W)), IsRepW k r z π → ∀ X Y, InLieW k r z X → InLieW k r z Y →
      InLieW k r z (X * Y - Y * X) ∧
        dOp π (X * Y - Y * X) = (dOp π X).comp (dOp π Y) - (dOp π Y).comp (dOp π X)
def EcLie : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (k r : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (W →L[ℂ] W)), IsRepW k r z π → ∀ Z Z', InGlW k r z Z → InGlW k r z Z' →
      (InGlW k r z (Z + Z') ∧ ecOp π (Z + Z') = ecOp π Z + ecOp π Z') ∧
      (∀ c : ℂ, InGlW k r z (c • Z) ∧ ecOp π (c • Z) = c • ecOp π Z) ∧
      (InGlW k r z (Z * Z' - Z' * Z) ∧
        ecOp π (Z * Z' - Z' * Z) = (ecOp π Z).comp (ecOp π Z') - (ecOp π Z').comp (ecOp π Z))
def EB {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {k r m : ℕ} (π : Mx k r → (W →L[ℂ] W))
    (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m) : Module.End ℂ W :=
  (ecOp π (unitB (Hpk k r) Bs a b)).toLinearMap
def FrameGl : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (k r m : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (W →L[ℂ] W)) (Bs : Fin m → Fin (2 * r + k + 1) → ℂ), IsRepW k r z π →
    IsFrameOf k r [z] Bs →
      GlRel (EB π Bs) ∧ ∀ (w : ℂ) (v : W), capRep k r π Bs w v = qdet (EB π Bs) w v
def ExpGen : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → ∀ Pr : Mx k r → Prop, Pr 1 →
    (∀ X g, InLieW k r z X → Pr g → Pr (NormedSpace.exp X * g)) → ∀ h ∈ UWset k r z, Pr h
def LieStab : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (k r : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (W →L[ℂ] W)) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), inWb k r z →
    0 < Tz k r z → IsRepW k r z π → IsFrameOf k r [z] Bs → ∀ S : Submodule ℂ W, Stab (EB π Bs) S →
      ∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S
def StabLie : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (k r m : ℕ)
    (z e : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (W →L[ℂ] W)) (Bs : Fin m → Fin (2 * r + k + 1) → ℂ), IsRepW k r z π →
    IsFrameOf k r [z, e] Bs → ∀ S : Submodule ℂ W, (∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v ∈ S, π h v ∈ S) →
      Stab (EB π Bs) S
def FrameChange : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (n r : ℕ)
    (z e : Fin (2 * r + (n + 1) + 1) → ℂ) (π : Mx (n + 1) r → (W →L[ℂ] W))
    (Bs Bs' : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → inWb (n + 1) r e →
    herm (Hpk (n + 1) r) e z = 0 → herm (Hpk (n + 1) r) e e = 1 → IsRepW (n + 1) r z π →
    IsFrameOf (n + 1) r [z, e] Bs → IsFrameOf (n + 1) r [z, e] Bs' → ∀ w : ℂ, qdet (EB π Bs) w = qdet (EB π Bs') w
def FrameExists2 : Prop :=
  ∀ (n r : ℕ) (z e : Fin (2 * r + (n + 1) + 1) → ℂ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → inWb (n + 1) r e →
    herm (Hpk (n + 1) r) e z = 0 → herm (Hpk (n + 1) r) e e = 1 →
    ∃ Bs : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ, IsFrameOf (n + 1) r [z, e] Bs
def BranchingK : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp] (n r : ℕ)
    (z e : Fin (2 * r + (n + 1) + 1) → ℂ) (π : Mx (n + 1) r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ),
    inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L →
    (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) →
    inWb (n + 1) r e → herm (Hpk (n + 1) r) e z = 0 → herm (Hpk (n + 1) r) e e = 1 →
    ∃ S : {M : Fin n → ℤ // Box L M} → Submodule ℂ Wp, DirectSum.IsInternal S ∧
      (∀ M, S M ≠ ⊥ ∧ ∀ S' : Submodule ℂ Wp, S' ≤ S M →
        (∀ h ∈ UWset (n + 1) r z, h *ᵥ e = e → ∀ v ∈ S', π h v ∈ S') → S' = ⊥ ∨ S' = S M) ∧
      ∀ Bs : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ, IsFrameOf (n + 1) r [z, e] Bs →
        ∀ (M : {M : Fin n → ℤ // Box L M}) (w : ℂ), ∀ v ∈ S M, capRep (n + 1) r π Bs w v = cpol (shf β M.1) w • v
end Formalism.FourierDecayAlt.Qr


