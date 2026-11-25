-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T23:56:36.027744+00:00
-- url     : https://prove2.me/theorems/77a71983-3322-49f7-a9ba-2a1cd03a4bb9
-- title:
--   Is Discrete Valuation Ring Integral Closure
-- statement:
--   Definitions and structural lemmas for Is Discrete Valuation Ring Integral Closure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Germ_ev_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X


set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
namespace GlobalTheory.FormalIsogeny
section Nakayama
end Nakayama
section IntegralClosure
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
include K
end IntegralClosure
section PowerSeries
variable {R : Type*} [CommRing R] {σ τ : Type*}
variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Finite σ]
def FiniteReduction {R : Type*} [CommRing R] [IsLocalRing R] {σ τ : Type*}
    (f : τ → MvPowerSeries σ R) : Prop :=
  Module.Finite (ResidueField R) (MvPowerSeries σ (ResidueField R) ⧸
    Ideal.span (Set.range fun j => MvPowerSeries.map (residue R) (f j)))
variable [Finite τ]
end PowerSeries
section Criterion
variable {R : Type*} [CommRing R] {σ τ : Type*} [Finite σ]
variable [IsLocalRing R]
end Criterion
section Free
variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {σ τ : Type*} [Finite σ] [Finite τ]
end Free
section Solve
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
variable {R} [IsAdicComplete (maximalIdeal R) R] {σ τ : Type*} [Finite σ] [Finite τ]
end Solve
section FormalGroup
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
variable {R : Type} [CommRing R] {d : ℕ}
theorem constantCoeff_mulN (G : FGLaw R d) (k : ℕ) (i : Fin d) :
    constantCoeff (mulN G k i) = 0 := by
  induction k generalizing i with
  | zero => simp [mulN]
  | succ k ih =>
    have h : ∀ (j : Fin 2) (l : Fin d),
        constantCoeff ((![mulN G k, pt R d 0] : Fin 2 → Pt R 1 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt, ih]
    exact constantCoeff_subst_eq_zero (hasSubst_ev _ h) (fun p => h p.1 p.2) (G.const i)
theorem constantCoeff_vec_mulN (G : FGLaw R d) (k : ℕ) (j : Fin 1) (i : Fin d) :
    constantCoeff ((![mulN G k] : Fin 1 → Pt R 1 d) j i) = 0 := by
  simp [constantCoeff_mulN]
def mulNHom (G : FGLaw R d) (k : ℕ) : PS R 1 d →ₐ[R] PS R 1 d :=
  substAlgHom (hasSubst_ev ![mulN G k] (constantCoeff_vec_mulN G k))
def mulLaw (R : Type) [CommRing R] (d : ℕ) : FGLaw R d where
  F := fun i => X ((0 : Fin 2), i) + X ((1 : Fin 2), i) + X ((0 : Fin 2), i) * X ((1 : Fin 2), i)
  const := fun i => by simp
  unit := fun i => by
    have h : ∀ (j : Fin 2) (l : Fin d),
        constantCoeff ((![0, pt R d 0] : Fin 2 → Pt R 1 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    simp only [ev_add _ h, ev_mul _ h, ev_X _ h]
    simp [pt]
  comm := fun i => by
    have h : ∀ (j : Fin 2) (l : Fin d),
        constantCoeff ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    simp only [ev_add _ h, ev_mul _ h, ev_X _ h]
    simp [pt, add_comm, mul_comm]
  assoc := fun i => by
    have key : ∀ a b : Pt R 3 d, (∀ l, constantCoeff (a l) = 0) → (∀ l, constantCoeff (b l) = 0) →
        ∀ l, ev ![a, b] (X ((0 : Fin 2), l) + X ((1 : Fin 2), l) +
          X ((0 : Fin 2), l) * X ((1 : Fin 2), l) : PS R 2 d) = a l + b l + a l * b l := by
      intro a b ha hb l
      have h : ∀ (j : Fin 2) (l : Fin d), constantCoeff ((![a, b] : Fin 2 → Pt R 3 d) j l) = 0 := by
        intro j l; fin_cases j <;> simp [ha, hb]
      simp only [ev_add _ h, ev_mul _ h, ev_X _ h]
      simp
    have hp : ∀ (j : Fin 3) (l : Fin d), constantCoeff (pt R d j l) = 0 := by simp [pt]
    rw [funext (key _ _ (hp 0) (hp 1)), funext (key _ _ (hp 1) (hp 2)),
      key _ _ (by simp [hp]) (hp 2), key _ _ (hp 0) (by simp [hp])]
    ring
end FormalGroup
end GlobalTheory.FormalIsogeny


