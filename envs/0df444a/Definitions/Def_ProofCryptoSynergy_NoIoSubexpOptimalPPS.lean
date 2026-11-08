-- Prove2me | Definitions.Def_ProofCryptoSynergy_NoIoSubexpOptimalPPS
-- name    : ProofCryptoSynergy_NoIoSubexpOptimalPPS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:06:07.517631+00:00
-- url     : https://prove2.me/theorems/5a173ca4-e0ca-4d3c-b86f-37f428cc368f
-- title:
--   Propositional proof systems; no infinitely-often subexponentially optimal proof system
-- statement:
--   A **propositional proof system (PPS)** is a polynomial-time map $L:\{0,1\}^*\to\mathrm{TAUT}$; it is sound and not necessarily complete. $L$ **subexponentially infinitely-often simulates** $L'$ if for every constant $c\ge 1$ there are infinitely many $n$ such that for all $x\in\mathrm{TAUT}$ with $|x|=n$,
--   $$L\text{-size}(x)\le 2^{(L'\text{-size}(x))^{1/c}}.$$
--   A PPS is **subexponentially infinitely-often optimal** if it so simulates every PPS. The assumption is that no such PPS exists, a strengthening of the Krajíček–Pudlák conjecture.
--
--   **Formalization Note** The size inequality is written as: every $L'$-proof $\pi'$ of $x$ yields an $L$-proof $\pi$ with $|\pi|\le 2^{|\pi'|^{1/c}}$. This is the same condition and avoids $\infty$.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definitions 6, 7, 8, p.18 (PDF 20)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_TAUT

open LaconicBarrier

namespace ProofCryptoSynergy

/-- A **propositional proof system** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 6, p.18 (PDF 20)): a polynomial-time algorithm
`L : {0,1}* → TAUT`.

**Formalization Note** Sound, not necessarily complete, exactly as Definition 6 and its footnote 14 say. -/
def IsPPS (L : List Bool → List Bool) : Prop :=
  PolyTimeOn (ι := List Bool) (fun π => [π]) L ∧ ∀ π, L π ∈ TAUT

/-- `L` **subexponentially infinitely-often simulates** `L'` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 7, second paragraph,
p.18 (PDF 20)): for all constants `c ≥ 1`, with `p(n) = 2^{n^{1/c}}`, there are infinitely many `n` such
that for all `x ∈ TAUT` with `|x| = n`, `L-size(x) ≤ p(L'-size(x))`.

**Formalization Note** "`L-size(x) ≤ p(L'-size(x))`" is written as: every `L'`-proof `π'` of `x` yields an
`L`-proof `π` with `|π| ≤ p(|π'|)`. Since `p` is increasing this is the same condition at the shortest `π'`,
and it avoids `∞` (no `L'`-proof: nothing is required). `c` ranges over the positive integers (same
condition, `p` decreases in `c`). -/
def IoSubexpSimulates (L L' : List Bool → List Bool) : Prop :=
  ∀ c : ℕ, 1 ≤ c →
    {n : ℕ | ∀ x ∈ TAUT, x.length = n → ∀ π', L' π' = x →
      ∃ π, L π = x ∧ (π.length : ℝ) ≤ (2 : ℝ) ^ ((π'.length : ℝ) ^ (1 / (c : ℝ)))}.Infinite

/-- **There is no infinitely-often subexponentially optimal proof system** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 8, second
paragraph, p.18 (PDF 20): `L` is optimal if it infinitely-often simulates every PPS `L'`). -/
def NoIoSubexpOptimalPPS : Prop :=
  ¬ ∃ L, IsPPS L ∧ ∀ L', IsPPS L' → IoSubexpSimulates L L'

end ProofCryptoSynergy


