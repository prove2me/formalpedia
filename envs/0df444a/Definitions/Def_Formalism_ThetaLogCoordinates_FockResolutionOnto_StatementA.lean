-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementA
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:09.343548+00:00
-- url     : https://prove2.me/theorems/42d9b9e3-3940-48ff-972e-f7e512be6623
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/StatementA.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_ShiftLastLetterThresholds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset
def PartnerDet : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Vs : Type) [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]
    (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (k : ℕ) (g : Fin k → Vs) (D : ℝ),
    LinearIndependent ℤ_[p] g →
    (∀ u ∈ Submodule.span ℤ_[p] (Set.range g),
      (∀ (a : ℤ_[p]) (x : Vs), x ∈ Submodule.span ℤ_[p] (Set.range g) → u = a • x → IsUnit a) →
      ∃ u' ∈ Submodule.span ℤ_[p] (Set.range g), (p : ℝ) ^ (-D) ≤ ‖be u u'‖) →
    (p : ℝ) ^ (-(D * k)) ≤ ‖(Matrix.of fun a b => be (g a) (g b)).det‖
def GradedPieceBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e D c : ℕ) (κ : ℝ),
    ProjAt p LLw J M ρ w e D → SatAt p LLw J M ρ w e c → ((D + 2 * c : ℕ) : ℝ) ≤ κ →
    ∀ (k : ℕ) (g : Fin k → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      LinearIndependent ℤ_[p] g → Submodule.span ℤ_[p] (Set.range g) = grLat p LLw J M ρ w (Fin.last K, ρ) e →
      (p : ℝ) ^ (-(κ * k)) ≤
        ‖(Matrix.of fun a b => fock p (g a) (g b) / ∏ i, ((LLw.deg i).factorial : ℚ_[p])).det‖
end Formalism.InvariantFactorPaths.L4


