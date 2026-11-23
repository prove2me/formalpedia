-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:24.198581+00:00
-- url     : https://prove2.me/theorems/a933569c-5621-4ebf-800a-3e1c475ac6ee
-- title:
--   Finsupp Step Induction
-- statement:
--   Definitions and structural lemmas for Finsupp Step Induction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (jetPair)
section Shift
variable {K ι κ : Type} [Field K] [Fintype κ]
def shiftGen (b : κ → ι → K) (x : ι) : MvPolynomial κ (MvPolynomial ι K) :=
  MvPolynomial.C (MvPolynomial.X x) +
    ∑ k, MvPolynomial.C (MvPolynomial.C (b k x)) * MvPolynomial.X k
def dirD (c : ι → K) [Fintype ι] (Q : MvPolynomial ι K) : MvPolynomial ι K :=
  ∑ x, MvPolynomial.C (c x) * MvPolynomial.pderiv x Q
end Shift
section Jet
variable {K ι : Type} [Field K]
end Jet
section Expand
variable {K ι κ : Type} [Field K] [Fintype κ]
def biHom (d : ℕ) (F : MvPolynomial κ (MvPolynomial ι K)) : Prop :=
  ∀ β n, MvPolynomial.coeff n (MvPolynomial.coeff β F) ≠ 0 → n.degree + β.degree = d
end Expand
section Integral
variable (K ι κ : Type) [NormedField K] [IsUltrametricDist K]
def biInt : Subring (MvPolynomial κ (MvPolynomial ι K)) where
  carrier := {F | ∀ β, MvPolynomial.coeff β F ∈ Formalism.DworkPowerSeriesWeights.opInt K ι}
  mul_mem' := by
    intro P Q hP hQ β
    classical
    rw [MvPolynomial.coeff_mul]
    exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hP _) (hQ _)
  one_mem' := by
    intro β
    classical
    rw [MvPolynomial.coeff_one]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  add_mem' := by
    intro P Q hP hQ β
    rw [MvPolynomial.coeff_add]
    exact Subring.add_mem _ (hP _) (hQ _)
  zero_mem' := by
    intro β
    rw [MvPolynomial.coeff_zero]
    exact Subring.zero_mem _
  neg_mem' := by
    intro P hP β
    rw [MvPolynomial.coeff_neg]
    exact Subring.neg_mem _ (hP β)
variable {K ι κ}
end Integral
section DegLE
variable {κ R : Type} [CommRing R]
def degLE (W : Finset κ) (n : ℕ) (F : MvPolynomial κ R) : Prop :=
  ∀ β, MvPolynomial.coeff β F ≠ 0 → ∑ k ∈ W, β k ≤ n
end DegLE
section Minor
variable {K σ κ : Type} [Field K] [DecidableEq σ] [Fintype κ]
variable {r0 r1 l : ℕ} (s : σ) (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) (pos : κ → σ)
  (ξ : κ → Fin r0 → K) (col : κ → Fin r1)
end Minor
end Formalism.InvariantFactorPaths.G7


