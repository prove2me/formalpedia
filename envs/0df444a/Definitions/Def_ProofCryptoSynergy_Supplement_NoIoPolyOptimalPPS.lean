-- Prove2me | Definitions.Def_ProofCryptoSynergy_Supplement_NoIoPolyOptimalPPS
-- name    : ProofCryptoSynergy_Supplement_NoIoPolyOptimalPPS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:47:16.682204+00:00
-- url     : https://prove2.me/theorems/60010458-273a-4db5-8b9d-952bef2425ec
-- title:
--   No infinitely-often polynomially optimal proof system
-- statement:
--   A propositional proof system $L$ **polynomially infinitely-often simulates** a proof system $L'$ if there is a constant $c\ge1$ such that for infinitely many $n$, every tautology $x$ of length $n$ satisfies
--   $$L\text{-size}(x)\le \big(L'\text{-size}(x)\big)^c .$$
--   There is **no infinitely-often polynomially optimal proof system** if no proof system $L$ polynomially infinitely-often simulates every proof system $L'$.
--
--   This is the proof-complexity hypothesis of Theorem 38, the polynomial counterpart of the published `NoIoSubexpOptimalPPS`.
--
--   **Formalization Note** Proof systems are the published `IsPPS` (sound, not necessarily complete). The size inequality is written as: every $L'$-proof $\pi'$ of $x$ yields an $L$-proof $\pi$ with $|\pi|\le|\pi'|^c$; this is the same condition at the shortest $\pi'$ and requires nothing when $x$ has no $L'$-proof.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definitions 7 and 8, p.18 (PDF 20); Theorem 38, p.33 (PDF 35)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_NoIoSubexpOptimalPPS

open LaconicBarrier

namespace ProofCryptoSynergy.Supplement

/-- `L` **polynomially infinitely-often simulates** `L'` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 7, second paragraph, p.18
(PDF 20)): there is a polynomial `p(n) = n^c`, `c ≥ 1`, such that for infinitely many `n`, for all
`x ∈ TAUT` with `|x| = n`, `L-size(x) ≤ p(L'-size(x))`.

**Formalization Note** As in the published `IoSubexpSimulates`, "`L-size(x) ≤ p(L'-size(x))`" is written
as: every `L'`-proof `π'` of `x` yields an `L`-proof `π` with `|π| ≤ |π'|^c` (the same condition at the
shortest `π'`, since `p` is increasing; no `L'`-proof requires nothing). `c` is real and may depend on
`(L, L')`. -/
def IoPolySimulates (L L' : List Bool → List Bool) : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧
    {n : ℕ | ∀ x ∈ TAUT, x.length = n → ∀ π', L' π' = x →
      ∃ π, L π = x ∧ (π.length : ℝ) ≤ (π'.length : ℝ) ^ c}.Infinite

/-- **There is no infinitely-often polynomially optimal proof system** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 8, second
paragraph, p.18 (PDF 20); Theorem 38, assumption 2, p.33 (PDF 35)): no PPS `L` (published `IsPPS`)
polynomially infinitely-often simulates every PPS `L'`. -/
def NoIoPolyOptimalPPS : Prop :=
  ¬ ∃ L, IsPPS L ∧ ∀ L', IsPPS L' → IoPolySimulates L L'

end ProofCryptoSynergy.Supplement


