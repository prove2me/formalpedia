-- Prove2me | Definitions.Def_KernelRankLean_Differential
-- name    : KernelRankLean_Differential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T02:05:57.871146+00:00
-- url     : https://prove2.me/theorems/d76d282c-c047-4691-8a60-378e7c2a4cfd
-- title:
--   Differential
-- statement:
--   Definitions and structural lemmas for Differential, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Differential.lean

import Definitions.Def_KernelRankLean_TranslationSemigroup
set_option autoImplicit true
open Polynomial NNReal
namespace KernelRank
noncomputable def differentialOperator (p : ℂ[X]) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    p.coeff k * iteratedDerivWithin k f (Set.Ici 0) t
noncomputable section Endomorphism
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance _p2m_local_instance_4c459f894a_30 : NormedSpace ℝ E := .restrictScalars ℝ ℂ E
local instance _p2m_local_instance_4c459f894a_31 : NormedAlgebra ℝ (E →L[ℂ] E) := .restrictScalars ℝ ℂ _
local instance _p2m_local_instance_4c459f894a_32 : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _
noncomputable def operatorOrbit (A : E →L[ℂ] E) (v : E)
    (β : E →L[ℂ] ℂ) (t : ℝ) : ℂ :=
  β (NormedSpace.exp ((t : ℂ) • A) v)
end Endomorphism
attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace
end KernelRank


