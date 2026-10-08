-- Prove2me | Definitions.Def_QuantitativeVanDerWaerden
-- name    : QuantitativeVanDerWaerden
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:13.12747+00:00
-- url     : https://prove2.me/theorems/fcaf7e49-1b1a-46ef-bdcf-625a4aa7a1de
-- statement:
--   For a coloring c of the natural numbers by values in a type α, MonoAP(c,k,a,d) means that the k terms a, a+d, ..., a+(k-1)d (indices a+jd for j<k) all receive the same color as a. HasMonoAP(c,k,N) means there exist a start a and a positive common difference d such that a+(k-1)d < N, so the progression lies within {0,...,N-1}, and it is monochromatic of length k. IsRamsey(α,k,N) means that every coloring c : ℕ → α has such a monochromatic k-term arithmetic progression inside the first N numbers. The quantity W(r,k) is defined as the infimum (sInf) of the set of positive N for which IsRamsey(Fin r,k,N) holds, i.e. the least positive interval length that forces a monochromatic k-term progression under every r-coloring. As the source notes, this is only a definition; if the set is empty, sInf gives 0, and no finiteness proof is built in.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/QuantitativeVanDerWaerden.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/QuantitativeVanDerWaerden.lean; bytes 16..659
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

universe u

namespace QuantitativeVanDerWaerden

def MonoAP {α : Type u} (c : ℕ → α) (k a d : ℕ) : Prop :=
  ∀ j < k, c (a + j * d) = c a

def HasMonoAP {α : Type u} (c : ℕ → α) (k N : ℕ) : Prop :=
  ∃ a d, 0 < d ∧ a + (k - 1) * d < N ∧ MonoAP c k a d

def IsRamsey (α : Type u) (k N : ℕ) : Prop :=
  ∀ c : ℕ → α, HasMonoAP c k N

/-- The least positive Ramsey interval size. Statements about its Ramsey
property require a finiteness proof; no such proof is built into this definition. -/
noncomputable def W (r k : ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ IsRamsey (Fin r) k N}

open Filter



end QuantitativeVanDerWaerden
end OAI


