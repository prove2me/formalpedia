-- Prove2me | Definitions.Def_ProofCryptoSynergy_Supplement_CoNPNotIoSubexpNTIME
-- name    : ProofCryptoSynergy_Supplement_CoNPNotIoSubexpNTIME
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:47:44.457164+00:00
-- url     : https://prove2.me/theorems/42ef3a41-e978-417a-b0cc-0fb3b57a0e10
-- title:
--   $\mathsf{coNP}\not\subseteq\bigcap_{c\ge1}\text{io-}\mathsf{NTIME}[2^{n^{1/c}}]$
-- statement:
--   A language $L$ is in **io-NTIME$[T]$** if some language in $\mathsf{NTIME}[T]$ agrees with $L$ on all strings of length $n$, for infinitely many $n$. The hypothesis
--   $$\mathsf{coNP}\not\subseteq\bigcap_{c\ge1}\text{io-}\mathsf{NTIME}\big[2^{n^{1/c}}\big]$$
--   says that some language $L$ whose complement is in NP lies outside io-NTIME$[2^{n^{1/c}}]$ for some $c\ge1$.
--
--   It is the proof-complexity hypothesis of Theorem 56 and of the second item of Theorem 2.
--
--   **Formalization Note** NTIME is the published witness form `InNTIME`; the time bound is $\lfloor 2^{n^{1/c}}\rfloor$ steps, and $c$ ranges over the positive integers (the classes shrink as $c$ grows, so the intersection is the same).
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 56, p.44 (PDF 46); Lemma 29, p.25 (PDF 27)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_InUTIME

namespace ProofCryptoSynergy.Supplement

/-- `L ∈ io-NTIME[T]`: some language in `NTIME[T]` (published `InNTIME`, witness form) agrees with `L` at
infinitely many input lengths, as the published `InIoNP` does for NP (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 29, p.25 (PDF 27);
Theorem 56, p.44 (PDF 46)).

**Formalization Note** The paper uses io-NTIME without defining it; this is the standard definition. -/
def InIoNTIME (T : ℕ → ℕ) (L : Set (List Bool)) : Prop :=
  ∃ A, InNTIME T A ∧ {n : ℕ | ∀ x : List Bool, x.length = n → (x ∈ A ↔ x ∈ L)}.Infinite

/-- **`coNP ⊄ ⋂_{c≥1} io-NTIME[2^{n^{1/c}}]`** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 56, assumption 2, p.44 (PDF 46);
Lemma 29, item 1, p.25 (PDF 27)): some language `L` with `Lᶜ ∈ NP` is, for some `c ≥ 1`, not in
`io-NTIME[2^{n^{1/c}}]`.

**Formalization Note** Negating the intersection gives `∃ c`. `c` ranges over the positive integers: the
classes shrink as `c` grows, so the intersection over real `c ≥ 1` is the same. The time bound is
`⌊2^{n^{1/c}}⌋`, a natural number of steps. -/
def CoNPNotIoSubexpNTIME : Prop :=
  ∃ L : Set (List Bool), InNP Lᶜ ∧ ∃ c : ℕ, 1 ≤ c ∧
    ¬ InIoNTIME (fun n => ⌊(2 : ℝ) ^ ((n : ℝ) ^ (1 / (c : ℝ)))⌋₊) L

end ProofCryptoSynergy.Supplement


