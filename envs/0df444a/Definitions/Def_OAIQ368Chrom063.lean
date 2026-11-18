-- Prove2me | Definitions.Def_OAIQ368Chrom063
-- name    : OAIQ368Chrom063
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:38:35.781841+00:00
-- url     : https://prove2.me/theorems/86918a7b-01f7-45f5-afb8-4fbc108af171
-- title:
--   Definitions bundle OAIQ368Chrom063 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_QuantumTorus_Admissible`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/Admissible.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom058` and `OAIQ368Chrom062` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom069`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom058
import Definitions.Def_OAIQ368Chrom062

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_Admissible
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.CoefficientReflection

@[simp] theorem coeff_reflect {α : Type*} (M : ℕ)
    (P : MvPolynomial α (Polynomial ℕ)) (m : α →₀ ℕ) :
    (reflect M P).coeff m =
      Polynomial.reflect M (P.coeff m) := rfl

theorem reflect_C_X_pow_mul_map {α : Type*} (M k : ℕ) (hk : k ≤ M)
    (P : MvPolynomial α ℕ) :
    reflect M (MvPolynomial.C (Polynomial.X ^ k) *
      MvPolynomial.map Polynomial.C P) =
    MvPolynomial.C (Polynomial.X ^ (M-k)) * MvPolynomial.map Polynomial.C P := by
  ext m
  simp only [coeff_reflect, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  rw [mul_comm, Polynomial.reflect_C_mul, Polynomial.reflect_monomial,
    Polynomial.revAt_le hk, mul_comm]

theorem reflect_C_X_pow_mul_esymmPart {α : Type*} [Fintype α]
    {n : ℕ} (lam : Nat.Partition n) (M k : ℕ) (hk : k ≤ M) :
    reflect M (MvPolynomial.C (Polynomial.X ^ k) *
      MvPolynomial.esymmPart α (Polynomial ℕ) lam) =
    MvPolynomial.C (Polynomial.X ^ (M-k)) *
      MvPolynomial.esymmPart α (Polynomial ℕ) lam := by
  rw [← map_esymmPart lam]
  exact reflect_C_X_pow_mul_map M k hk _

end ElementaryPositivity.CoefficientReflection

end

end OAI
end


