-- Prove2me | Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_BridgeLIFT
-- name    : Formalism_CoboundaryTransfers_GammaStableTransfers_BridgeLIFT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:54.916838+00:00
-- url     : https://prove2.me/theorems/e64ec079-9968-4a27-b303-bca8a9300f5a
-- title:
--   Bridge LIFT
-- statement:
--   Definitions and structural lemmas for Bridge LIFT, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/BridgeLIFT.lean

import Definitions.Def_Formalism_CoboundaryTransfers_StatementBridge
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CoeffSumXPowMulExpand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CoboundaryTransfers
open Formalism
theorem pow_smul_bijective {A D : Type} [CommRing A] [AddCommGroup D] [Module A D] (Q : A)
    (h : Function.Bijective (fun x : D => Q • x)) (M : ℕ) :
    Function.Bijective (fun x : D => Q ^ M • x) := by
  have e : (fun x : D => Q ^ M • x) = (fun x : D => Q • x)^[M] := by
    funext x
    induction M with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ← ih, pow_succ', mul_smul]
  rw [e]
  exact h.iterate M
theorem lift_gamma_invariant_lattice : LIFTGammaQN := by
  intro ℓ _ A _ _ B M D _ _ _ _ W y hy
  obtain ⟨t, hv, hγQ⟩ := B.γQ
  obtain ⟨n, hn, hγn⟩ := W.γ_N _ hy
  obtain ⟨w, hw⟩ := hv.exists_left_inv
  have hX : B.X ∣ w - 1 := ⟨-(w * t), by linear_combination hw⟩
  obtain ⟨r, hr⟩ : B.X ∣ w ^ M - 1 := by
    have h := sub_dvd_pow_sub_pow w 1 M
    rw [one_pow] at h
    exact dvd_trans hX h
  have hw' : w ^ M = B.X * r + 1 := by rw [← hr]; ring
  have h1 : W.γ (B.Q ^ M • y) = B.Q ^ M • ((1 + B.X * t) ^ M • W.γ y) := by
    rw [W.γ_smul, map_pow, hγQ, mul_pow, mul_smul]
  have h2 : w ^ M • W.γ (B.Q ^ M • y) = B.Q ^ M • W.γ y := by
    rw [h1, smul_comm (w ^ M) (B.Q ^ M), ← mul_smul (w ^ M), ← mul_pow, hw, one_pow, one_smul]
  have h3 : W.γ (B.Q ^ M • y) = B.Q ^ M • y + B.X • n := by rw [← hγn]; abel
  have key : B.Q ^ M • (W.γ y - y) = B.X • (r • B.Q ^ M • y + w ^ M • n) := by
    rw [smul_sub, ← h2, h3, hw']
    module
  have hb := pow_smul_bijective B.Q W.Q_bij M
  obtain ⟨y', hy'⟩ := hb.2 (r • B.Q ^ M • y + w ^ M • n)
  simp only at hy'
  refine ⟨y', ?_, ?_⟩
  · rw [hy']
    exact W.N.add_mem (W.N.smul_mem _ hy) (W.N.smul_mem _ hn)
  · apply hb.1
    simp only
    rw [key, smul_comm (B.Q ^ M) B.X y', hy']
def sesOfLIFT {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
    {B : LIFT.Base ℓ A} {M : ℕ} {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    {W₀ : LIFT.WD B M D₀} {W₁ : LIFT.WD B M D₁} {W₂ : LIFT.WD B M D₂}
    (S : LIFT.SES W₀ W₁ W₂) :
    SES (ofLIFT W₀ (lift_gamma_invariant_lattice ℓ A B M D₀ W₀)) (ofLIFT W₁ (lift_gamma_invariant_lattice ℓ A B M D₁ W₁))
      (ofLIFT W₂ (lift_gamma_invariant_lattice ℓ A B M D₂ W₂)) where
  ι := ⟨S.ι.f, S.ι.φ_comm, S.ι.γ_comm, S.ι.N_le⟩
  π := ⟨S.π.f, S.π.φ_comm, S.π.γ_comm, S.π.N_le⟩
  ι_inj := S.ι_inj
  exact := S.exact
  sat := S.sat
end Formalism.CoboundaryTransfers


