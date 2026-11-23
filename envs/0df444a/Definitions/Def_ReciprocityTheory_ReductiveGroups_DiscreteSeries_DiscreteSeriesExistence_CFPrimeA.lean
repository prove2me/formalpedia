-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:59.998794+00:00
-- url     : https://prove2.me/theorems/b333980f-2992-4cd4-9682-e39683f86529
-- title:
--   CFPrime A
-- statement:
--   Definitions and structural lemmas for CFPrime A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def modeWt (ε : Fin n → Bool) (x : Fin n × Fin n) : Fin n → ℝ :=
  if ε x.1 = true ∧ ε x.2 = false then root x.1 x.2 else 0
def fockBasis (n : ℕ) : Module.Basis (Finset (Fin (n * n))) ℂ (Fock n) :=
  ((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv).ExteriorAlgebra
def fockWt (ε : Fin n → Bool) (s : Finset (Fin (n * n))) : Fin n → ℝ :=
  ∑ k ∈ s, modeWt ε (finProdFinEquiv.symm k)
section Comm
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
end Comm
def cfaM (ε : Fin n → Bool) (lam : Fin n → ℝ) (x : Fin n × Fin n) : ℝ :=
  (if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then lam x.1 else 0) -
    (if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then lam x.2 else 0)
end ReciprocityTheory.ChartRestriction.DS


