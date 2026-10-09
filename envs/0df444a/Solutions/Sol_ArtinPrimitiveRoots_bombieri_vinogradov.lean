-- Prove2me | solution 1 for ArtinPrimitiveRoots.bombieri_vinogradov
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T16:44:33.271091+00:00
-- url     : https://prove2.me/submissions/a5d4e8ee-ec45-4da4-b776-0021a44ae312

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_psi_bombieri_vinogradov
import Theorems.Thm_ArtinPrimitiveRoots_bombieri_vinogradov_of_psi

open ArtinPrimitiveRoots Real in
theorem solution (A' η : ℝ) (hA' : 0 < A') (hη : 0 < η) :
    ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y → ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈Y ^ (1 / 2 - η)⌉₊).filter (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < Y ^ (1 / 2 - η)),
          |(primeCountingAP Y q (v q) : ℝ) - logIntegral Y / Nat.totient q| ≤
        C * (Y * log Y ^ (-A')) :=
  ArtinPrimitiveRoots.bombieri_vinogradov_of_psi
    (fun A η hA hη => ArtinPrimitiveRoots.psi_bombieri_vinogradov A η hA hη) A' η hA' hη
