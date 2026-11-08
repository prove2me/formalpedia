-- Prove2me | Definitions.Def_ProofCryptoSynergy_promiseBPP
-- name    : ProofCryptoSynergy_promiseBPP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:04:09.972683+00:00
-- url     : https://prove2.me/theorems/226b1ef5-95b5-4cc0-8ffe-596bde35aa04
-- title:
--   $\text{promise-P}$, $\text{promise-QP}$, $\text{promise-BPP}$
-- statement:
--   On promise problems, pairs of disjoint yes- and no-instances: **promise-P** has a deterministic polynomial-time machine accepting yes-instances and rejecting no-instances, **promise-QP** the same in time $2^{(\log_2(n+2))^k}$, and **promise-BPP** a polynomial-time machine on $(x,r)$ with $r$ uniform of length $|x|^k+k$ that accepts with probability at least $2/3$ on yes-instances and at most $1/3$ on no-instances.
--
--   **Formalization Note** The paper uses these classes without defining them; the definitions are the standard ones.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 35, p.31 (PDF 33); Corollary 45, p.38 (PDF 40)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_OracleTM_Accepts
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_KarpLiptonOM_countStr
import Definitions.Def_KarpLiptonOM_PromiseProblem

open KarpLiptonOM

namespace ProofCryptoSynergy

/-- Promise problems solved in deterministic time `T`: a machine halting within `T(|x|)` steps on every `x`,
accepting the yes-instances and rejecting the no-instances. -/
def promiseDTIME (T : ℕ → ℕ) : Set PromiseProblem :=
  {Q | ∃ M : OracleTM, (∀ x : List Bool, M.HaltsWithin ∅ (T x.length) (tupleEnc [x])) ∧
    (∀ x ∈ Q.yes, M.Accepts ∅ (tupleEnc [x])) ∧ (∀ x ∈ Q.no, ¬ M.Accepts ∅ (tupleEnc [x]))}

/-- **promise-P** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Corollary 45, item 2, p.38 (PDF 40)).

**Formalization Note** The paper does not define promise-P, promise-QP or promise-BPP; these are the standard
definitions, on the published `KarpLiptonOM.PromiseProblem` (a disjoint pair of yes- and no-instances). -/
def promiseP : Set PromiseProblem := {Q | ∃ k : ℕ, Q ∈ promiseDTIME (fun n => n ^ k + k)}

/-- **promise-QP**: deterministic time `2^{(log₂(n+2))^k}` for some `k` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Lemma 35, p.31 (PDF 33)). -/
def promiseQP : Set PromiseProblem :=
  {Q | ∃ k : ℕ, Q ∈ promiseDTIME (fun n => 2 ^ (Nat.log 2 (n + 2)) ^ k)}

/-- **promise-BPP** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Corollary 45, item 2, p.38 (PDF 40)): a polynomial-time machine on `(x, r)`, with
`r` uniform of length `|x|ᵏ + k`, accepting with probability at least `2/3` on yes-instances and at most `1/3` on
no-instances. Probabilities are integer inequalities between `countStr` and `2^q`. -/
def promiseBPP : Set PromiseProblem :=
  {Q | ∃ (M : OracleTM) (k j : ℕ),
    (∀ x r : List Bool, r.length = x.length ^ k + k →
      M.HaltsWithin ∅ (x.length ^ j + j) (tupleEnc [x, r])) ∧
    (∀ x ∈ Q.yes, 2 * 2 ^ (x.length ^ k + k) ≤
      3 * countStr (x.length ^ k + k) (fun r => M.Accepts ∅ (tupleEnc [x, r]))) ∧
    (∀ x ∈ Q.no, 3 * countStr (x.length ^ k + k) (fun r => M.Accepts ∅ (tupleEnc [x, r])) ≤
      2 ^ (x.length ^ k + k))}

end ProofCryptoSynergy


