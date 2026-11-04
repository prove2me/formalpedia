-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
-- name    : Submission_ThreeSum_LightTernaryPairedPotential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:46:16.487012+00:00
-- url     : https://prove2.me/theorems/71b600e5-512a-4fe4-851c-75abe0ca1eb2
-- title:
--   Light Ternary Paired Potential
-- statement:
--   Definitions and structural lemmas for Light Ternary Paired Potential, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotential.lean

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators
def columns (m Λ i : ℕ) : PairedIndex m → ℕ :=
  fun r => WeightEnumeration.digit Λ (width m) i (Fintype.equivFin (PairedIndex m) r).val
def term (m base Λ : ℕ) (μ : ℕ → ℤ) (i : ℕ) : ℤ :=
  value (fun q => μ (base+tensorIndex Λ (columns m Λ i q.1) (columns m Λ i q.2.1)
    (columns m Λ i q.2.2.1) (columns m Λ i q.2.2.2)))
def prefixSum (m base Λ : ℕ) (μ : ℕ → ℤ) (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range i, term m base Λ μ j
def body (m pPowers pRow pPoly : ℕ) : Stmt :=
  .call pPowers [v 3,k (width m+1),v 1] 4 ;;
  .set 5 (M (v 3 +' k (width m))) ;;
  .set 6 (k 0) ;;
  .for 7 (v 5) (
    .call pRow [k (width m),v 1,v 7,v 3,k 0,k 1,v 2,k (width m)] 8 ;;
    .call pPoly [v 0,v 1,v 2] 9 ;;
    .set 6 (v 6 +' v 9)) ;;
  .set 0 (v 6)
def time (m Λ : ℕ) : ℕ := powTableTime (width m+1)+Λ^(width m)*
  (LightWeightRow.time (width m) (Λ^width m)+LightTernaryPairedPolynomial.time m+300)+300
def word (m Λ : ℕ) (U : ℤ) : ℤ :=
  10*((Λ^(width m+1) : ℕ)+(Λ^width m)+width m+Λ+2)+
    2*((Λ^width m : ℕ)+1)*((polynomial m).bound U+1)
def Inv (m base Λ colsBase powers : ℕ) (μ₁ : ℕ → ℤ) (powRet : ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r₀ r₁ : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [base,Λ,colsBase,powers,powRet,Λ^width m,prefixSum m base Λ μ₁ i,i,r₀,r₁],ν⟩ ∧
      SameOutside μ₁ ν colsBase (width m)
def program (m : ℕ) : Program :=
  [body m 1 2 5, powTableBody, LightWeightRow.body 3,
    LightRadixDigit.body 4, LightSmallDivide.body, LightTernaryPairedPolynomial.body m]
end ThreeSum.LightTernaryPairedPotential


