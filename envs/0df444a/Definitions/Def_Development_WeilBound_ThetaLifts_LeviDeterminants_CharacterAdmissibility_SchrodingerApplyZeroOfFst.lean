-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
-- name    : Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:22.048976+00:00
-- url     : https://prove2.me/theorems/0e411ea3-691c-463e-8139-7633f0827f91
-- title:
--   Schrodinger Apply Zero Of Fst
-- statement:
--   Definitions and structural lemmas for Schrodinger Apply Zero Of Fst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
  {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]
omit [Invertible (2 : R)] in
theorem IsSp.symm {S : V R κ ≃ₗ[R] V R κ} (h : IsSp S) : IsSp S.symm := fun w w' => by
  have := h (S.symm w) (S.symm w')
  simpa using this.symm
structure IsImp (C : TestClass R) (ψ : AddChar R ℂ) (S : V R κ ≃ₗ[R] V R κ) (T : Module.End ℂ ((κ → R) → ℂ)) : Prop where
  maps : ∀ φ ∈ C.sp κ, T φ ∈ C.sp κ
  adm : ∀ l ∈ C.adm κ, l ∘ₗ T ∈ C.adm κ
  law : ∀ w, ∀ φ ∈ C.sp κ, T (schr ψ w φ) = schr ψ (S w) (T φ)
  inj : ∀ φ ∈ C.sp κ, T φ = 0 → φ = 0
structure Ax (C : TestClass R) (ψ : AddChar R ℂ) : Prop extends AxB C ψ where
  delta : AxDelta C ψ
  imp : AxImp C ψ
def Cyc (C : TestClass R) (ψ : AddChar R ℂ) (l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ ∈ C.sp κ, φ ≠ 0 → ∃ w, l (schr ψ w φ) ≠ 0
theorem Cyc.ne (h : Ax C ψ) {l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : Cyc C ψ l) : ∃ φ ∈ C.sp κ, l φ ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := h.ne κ
  obtain ⟨w, hw⟩ := hl φ hφ h0
  exact ⟨_, h.schr κ w φ hφ, hw⟩
def Law (C : TestClass R) (ψ : AddChar R ℂ) (S : V R κ ≃ₗ[R] V R κ) (j : κ₁ → κ)
    (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) : Prop :=
  ∀ w w₁, Rel S j w w₁ → ∀ φ ∈ C.sp κ, e (schr ψ w φ) = schr ψ w₁ (e φ)
structure IsE (C : TestClass R) (ψ : AddChar R ℂ) (S : V R κ ≃ₗ[R] V R κ) (j : κ₁ → κ)
    (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) : Prop where
  maps : ∀ φ ∈ C.sp κ, e φ ∈ C.sp κ₁
  adm : ∀ l ∈ C.adm κ₁, l ∘ₗ e ∈ C.adm κ
  law : Law C ψ S j e
  ne : ∃ φ ∈ C.sp κ, e φ ≠ 0
variable {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e e' : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
end PositivityTheory.ThKF0.Chr


