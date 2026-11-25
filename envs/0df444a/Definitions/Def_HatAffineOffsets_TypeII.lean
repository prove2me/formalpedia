-- Prove2me | Definitions.Def_HatAffineOffsets_TypeII
-- name    : HatAffineOffsets_TypeII
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:09:06.8131+00:00
-- url     : https://prove2.me/theorems/87c8ce7f-84b0-5ad7-b159-c8fde2271f40
-- title:
--   Type II
-- statement:
--   Definitions and structural lemmas for Type II, from insammael (insammael/one-sided-affine-hat-guessing; see pinned Apache-2.0 LICENSE)'s pinned One-sided affine obstructions in complete bipartite hat guessing development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/Lean/HatAffineOffsets/TypeII.lean

import Definitions.Def_HatAffineOffsets_TypeI
set_option autoImplicit true
namespace HatAffineOffsets
universe u
open Finset
noncomputable local instance _p2m_local_instance_68713dd93e_9 (p : Prop) : Decidable p :=
  Classical.propDecidable p
def typeIID
    {K : Type u} {I : Type*} [Field K]
    (alpha b x : I -> K) (i : I) : K :=
  (x i - b i) / alpha i
def TypeIIGood
    {K : Type u} {I : Type*} [Field K]
    (c d : I -> K) : Prop :=
  exists a beta : K, forall i, d i = a - c i * beta
def TypeIICross
    {K : Type u} {I : Type*} [Field K]
    (c d : I -> K) : Prop :=
  exists a beta : K, forall U V : K,
    (forall i, U - c i * V ≠ d i) -> U = a ∨ V = beta
noncomputable def nonzeroFinset (K : Type u) [Zero K] [Fintype K]
    [DecidableEq K] : Finset K :=
  Finset.univ.erase 0
noncomputable def puncturedPairs (K : Type u) [Zero K] [Fintype K]
    [DecidableEq K] : Finset (K × K) :=
  (nonzeroFinset K).product (nonzeroFinset K)
noncomputable def puncturedLine
    {K : Type u} [Field K] [Fintype K]
    (c e : K) : Finset (K × K) :=
  (puncturedPairs K).filter (fun p => p.1 - c * p.2 = e)
noncomputable def allowedLineParameter
    {K : Type u} [Field K] [Fintype K]
    (c e : K) : Finset K :=
  (nonzeroFinset K).filter (fun t => c * t + e ≠ 0)
def typeIIParam
    {K : Type u} {I : Type*} [Field K]
    (c : I -> K) (p : K × K) : I -> K :=
  fun i => p.1 - c i * p.2
end HatAffineOffsets


