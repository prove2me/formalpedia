-- Prove2me | Definitions.Def_KadisonRingrose
-- name    : KadisonRingrose
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:16.380004+00:00
-- url     : https://prove2.me/theorems/5add4a2d-f4a5-4255-b76a-bcf7d0daec86
-- statement:
--   For a normed complex vector space M, an n-cochain is a bounded (continuous) n-linear map from M×…×M (n copies) to M, for n a natural number. For a multiplication on M, mergeInputs takes n+1 inputs v₀,…,vₙ and an index j<n and returns n inputs by keeping the entries before position j, replacing positions j and j+1 by their product v_j·v_{j+1}, and shifting the later entries down. When M is a normed ring that is also a complex normed algebra, the differential of an n-cochain f evaluated on (v₀,…,vₙ) is v₀·f(v₁,…,vₙ) + Σ_{j<n} (−1)^{j+1} f(mergeInputs(v,j)) + (−1)^{n+1} f(v₀,…,v_{n−1})·vₙ. This is the standard Hochschild coboundary for bounded cochains with coefficients in M itself. A comment states the intended Kadison–Ringrose-type result, that every bounded higher Hochschild cocycle of a complex von Neumann algebra is the coboundary of a bounded cochain, but the block contains no definition or theorem of that statement, since the KadisonRingrose namespace is empty.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KadisonRingrose.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KadisonRingrose.lean; bytes 16..954
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! Every ordinary bounded higher Hochschild cocycle of a complex von Neumann
algebra is the coboundary of a bounded cochain with values in the same algebra. -/

noncomputable section

namespace BoundedHochschild

abbrev Cochain (M : Type*) [NormedAddCommGroup M] [NormedSpace ℂ M] (n : ℕ) :=
  ContinuousMultilinearMap ℂ (fun _ : Fin n => M) M

def mergeInputs {M : Type*} [Mul M] {n : ℕ}
    (v : Fin (n + 1) → M) (j : Fin n) : Fin n → M :=
  fun i => if i < j then v i.castSucc
    else if i = j then v i.castSucc * v i.succ else v i.succ

noncomputable def differentialValue {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]
    {n : ℕ} (f : Cochain M n) (v : Fin (n + 1) → M) : M :=
  v 0 * f (fun i => v i.succ) +
    ∑ j : Fin n, ((-1 : ℂ) ^ (j.val + 1)) • f (mergeInputs v j) +
    ((-1 : ℂ) ^ (n + 1)) • (f (fun i => v i.castSucc) * v (Fin.last n))

namespace KadisonRingrose

universe u



end KadisonRingrose
end BoundedHochschild
end
end OAI


