-- Prove2me | Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff
-- name    : Formalism_AdmissibleDesigns_InvariantsEqBotIff
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:51:28.446315+00:00
-- url     : https://prove2.me/theorems/ed8fc19d-ec80-4fdf-98e1-3fe5e34e5a56
-- title:
--   Invariants Eq Bot Iff
-- statement:
--   Definitions and structural lemmas for Invariants Eq Bot Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct
namespace Formalism.MainNotions.N.K.Norm
section ConjM
variable {Γ : Type} {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
def IsConjM (M M' : Γ → Matrix n n K) : Prop :=
  ∃ P Q : Matrix n n K, P * Q = 1 ∧ Q * P = 1 ∧ ∀ g, P * M g = M' g * P
theorem IsConjM.refl (M : Γ → Matrix n n K) : IsConjM M M :=
  ⟨1, 1, by simp, by simp, fun g => by simp⟩
theorem IsConjM.symm {M M' : Γ → Matrix n n K} (h : IsConjM M M') : IsConjM M' M := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  refine ⟨Q, P, h2, h1, fun g => ?_⟩
  calc Q * M' g = Q * M' g * (P * Q) := by rw [h1, Matrix.mul_one]
    _ = Q * (M' g * P) * Q := by simp only [Matrix.mul_assoc]
    _ = Q * (P * M g) * Q := by rw [h3]
    _ = M g * Q := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
theorem IsConjM.map {M M' : Γ → Matrix n n K} (h : IsConjM M M') {S : Type} [CommRing S] (f : K →+* S) :
    IsConjM (fun g => (M g).map f) (fun g => (M' g).map f) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  refine ⟨P.map f, Q.map f, ?_, ?_, fun g => ?_⟩
  · rw [← Matrix.map_mul, h1, Matrix.map_one _ f.map_zero f.map_one]
  · rw [← Matrix.map_mul, h2, Matrix.map_one _ f.map_zero f.map_one]
  · rw [← Matrix.map_mul, ← Matrix.map_mul, h3]
end ConjM
section MatRep
variable {Γ : Type} [Group Γ] {K : Type} [CommRing K] {k : ℕ}
def matEquiv (P Q : Matrix (Fin k) (Fin k) K) (h1 : P * Q = 1) (h2 : Q * P = 1) :
    (Fin k → K) ≃ₗ[K] (Fin k → K) where
  toLinearMap := Matrix.toLin' P
  invFun v := Q.mulVec v
  left_inv v := by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2]
  right_inv v := by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h1]
end MatRep
section Inv
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he
end Inv
section Sums
variable {G : Type} [Group G] {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]
  (ρ : Representation LL G V) {ι : Type} {k : ℕ}
end Sums
section SS
variable {Kf : Type} [Field Kf] {Γ : Type} [Group Γ] {V V' : Type} [AddCommGroup V] [Module Kf V]
  [AddCommGroup V'] [Module Kf V'] {ρ : Representation Kf Γ V} {ρ' : Representation Kf Γ V'}
  (e : V ≃ₗ[Kf] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he
end SS
section Abs
variable {Kf : Type} [Field Kf] {Γ : Type} [Group Γ] {V V' : Type} [AddCommGroup V] [Module Kf V]
  [AddCommGroup V'] [Module Kf V'] {ρ : Representation Kf Γ V} {ρ' : Representation Kf Γ V'}
  (e : V ≃ₗ[Kf] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he
end Abs
end Formalism.MainNotions.N.K.Norm


