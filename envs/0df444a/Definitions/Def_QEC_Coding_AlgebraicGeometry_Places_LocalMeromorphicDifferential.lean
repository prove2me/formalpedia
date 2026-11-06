-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
-- name    : QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:04:59.293764+00:00
-- url     : https://prove2.me/theorems/6178ad14-45af-4b4c-8b41-855a6c8de424
-- title:
--   Local Meromorphic Differential
-- statement:
--   Definitions and structural lemmas for Local Meromorphic Differential, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
import Mathlib.RingTheory.Kaehler.Basic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_germOrder_coe

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
local instance _p2m_local_instance_8465ba921d_22 : Algebra ℂ (MeromorphicGermRing a) := (germComplexConstants a).toAlgebra
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]
abbrev localFieldOrder : AddValuation K (WithTop ℤ) :=
  AddValuation.comap (algebraMap K (MeromorphicGermRing a)) (meromorphicOrderValuation a)
abbrev localValuationRing : ValuationSubring K :=
  Valuation.valuationSubring (AddValuation.toValuation (localFieldOrder K a))
def fieldLocalDerivation : Derivation ℂ K (MeromorphicGermRing a) :=
  (germCoefficientDerivation a).compAlgebraMap K
def fieldLocalDifferentialMap : (KaehlerDifferential ℂ K) →ₗ[K] (MeromorphicGermRing a) :=
  (fieldLocalDerivation K a).liftKaehlerDifferential
def localDifferentialLattice : Submodule (localValuationRing K a) (KaehlerDifferential ℂ K) :=
  Submodule.span (localValuationRing K a) (Set.range fun f : (localValuationRing K a) => KaehlerDifferential.D ℂ K (f : K))
def analyticRegularDifferentialSubmodule : Submodule (localValuationRing K a) (KaehlerDifferential ℂ K) where
  carrier := {ω | 0 ≤ meromorphicOrderValuation a (fieldLocalDifferentialMap K a ω)}
  zero_mem' := by simp
  add_mem' := by
    intro ω η hω hη
    change 0 ≤ meromorphicOrderValuation a (fieldLocalDifferentialMap K a (ω + η))
    rw [map_add]
    exact (meromorphicOrderValuation a).map_le_add hω hη
  smul_mem' := by
    intro c ω hω
    change 0 ≤ meromorphicOrderValuation a
      (fieldLocalDifferentialMap K a ((c : K) • ω))
    rw [map_smul, Algebra.smul_def]
    change 0 ≤ meromorphicOrderValuation a
      ((IsScalarTower.toAlgHom ℂ K (MeromorphicGermRing a)) c.val * fieldLocalDifferentialMap K a ω)
    rw [(meromorphicOrderValuation a).map_mul]
    exact add_nonneg c.property hω
variable [IsDiscreteValuationRing (localValuationRing K a)]
def complexConstantsToValuationRing : ℂ →+* (localValuationRing K a) :=
  (algebraMap ℂ K).codRestrict (localValuationRing K a) (fun c => by
    change 0 ≤ meromorphicOrderValuation a ((IsScalarTower.toAlgHom ℂ K (MeromorphicGermRing a)) (algebraMap ℂ K c))
    rw [(IsScalarTower.toAlgHom ℂ K (MeromorphicGermRing a)).commutes]
    change 0 ≤ meromorphicOrderValuation a (germComplexConstants a c)
    change 0 ≤ germOrder a (((fun _ : ℂ => c) : Germ (𝓝[≠] a) ℂ))
    rw [germOrder_coe]
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) a).meromorphicOrderAt_nonneg)
section LocalKaehlerImage
local instance _p2m_local_instance_8465ba921d_158 : Algebra ℂ (localValuationRing K a) := (complexConstantsToValuationRing K a).toAlgebra
local instance _p2m_local_instance_8465ba921d_159 : IsScalarTower ℂ (localValuationRing K a) K := .of_algebraMap_eq fun c => by rfl
end LocalKaehlerImage
end
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential


