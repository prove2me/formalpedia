-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:28:57.426553+00:00
-- url     : https://prove2.me/theorems/47aa31d9-51a4-463e-8d11-0ffaeadfef07
-- title:
--   Sum Neg One Pow Finrank Eq Zero
-- statement:
--   Definitions and structural lemmas for Sum Neg One Pow Finrank Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_GlobalTheory_SheafLES_shortExact_map_toSheaf
import Theorems.Thm_P2M_GlobalTheory_SheafLES___naturality_d0a1c18f99f7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
namespace GlobalTheory
namespace ExactSeq
section Ring
variable {R : Type*} [Ring R] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
end Ring
section Field
variable {k : Type*} [DivisionRing k]
variable {A B C : ℕ → Type*} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
  [∀ i, AddCommGroup (C i)] [∀ i, Module k (A i)] [∀ i, Module k (B i)] [∀ i, Module k (C i)]
  (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
end Field
end ExactSeq
variable {X : Scheme.{u}}
theorem shortExact_toAbSheaf {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (toAbSheaf X)).ShortExact :=
  SheafLES.shortExact_map_toSheaf X.ringCatSheaf hS
@[simps] def smulShortComplexHom (S : ShortComplex X.Modules) (r : Γ(X, ⊤)) : S ⟶ S where
  τ₁ := smulHom S.X₁ r
  τ₂ := smulHom S.X₂ r
  τ₃ := smulHom S.X₃ r
  comm₁₂ := smulHom_comp S.f r
  comm₂₃ := smulHom_comp S.g r
namespace cohOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
def δ (U : X.Opens) (n : ℕ) : cohOn S.X₃ U n →ₗ[R] cohOn S.X₁ U (n + 1) :=
  WithAction.linearMap (action S.X₃ U n) (action S.X₁ U (n + 1)) R
    (SheafLES.δ.{u} (shortExact_toAbSheaf hS) n U) fun r x ↦ by
      rw [action_apply, action_apply]
      exact (SheafLES.δ_naturality.{u} (shortExact_toAbSheaf hS) (shortExact_toAbSheaf hS)
        ((toAbSheaf X).mapShortComplex.map (smulShortComplexHom S r)) n U x).symm
variable (U : X.Opens) (n : ℕ)
include hS
section Finite
variable [IsNoetherianRing R]
end Finite
section Field
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]
end Field
end cohOn
section hdim
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
include hS
end hdim
end GlobalTheory


