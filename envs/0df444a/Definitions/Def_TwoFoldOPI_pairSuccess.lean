-- Prove2me | Definitions.Def_TwoFoldOPI_pairSuccess
-- name    : TwoFoldOPI_pairSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:14.205384+00:00
-- url     : https://prove2.me/theorems/98d4db79-a619-45b0-b9d3-155ad1fed0a7
-- title:
--   Success probability of Lemma 7.3's algorithm on random pairs
-- statement:
--   Fix a hidden word $c\in K^m$ and a rule $\mathrm{ord}$ that, given the random partners $c'$, decides for each $i$ whether the pair $\{c_i,c'_i\}$ is presented as $(c_i,c'_i)$ or $(c'_i,c_i)$. Each $c'_i$ is uniform on $K\setminus\{c_i\}$, independently. The success probability of a program run for $N$ steps is
--   $$\sum_{c'\in K^m}\Big(\prod_{i}\frac{[c'_i\neq c_i]}{q-1}\Big)\cdot\Pr\big[\text{the program halts within }N\text{ steps with output } c\big].$$
--   Any coins of the program are averaged inside the second factor.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.2, Lemma 7.3, p. 39

import Mathlib
import Definitions.Def_TwoFoldOPI_pairConfig

namespace TwoFoldOPI

/-- **Success probability of Lemma 7.3's algorithm on random pairs.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.2, Lemma 7.3, p.39: "There is a hidden c ∈ C⊥, fixed but arbitrary. The input to the
algorithm consists of the unordered pairs {c_1, c′_1}, …, {c_m, c′_m}, where each c′_i is sampled
independently and uniformly from F_q∖{c_i}. The algorithm's goal is to output c. The algorithm
succeeds with probability (over the randomness of the input pairs) …".

For a program `prog`, a hidden word `c`, a presentation order `ord` and `N` steps:
`Σ_{c′} (∏ᵢ [c′ᵢ ≠ cᵢ]/(q − 1)) · Pr[prog halts within N steps with output c on the pairs]`,
where pair `i` is presented as `(cᵢ, c′ᵢ)` if `ord c′ i` and as `(c′ᵢ, cᵢ)` otherwise.

**Formalization Note.** The order of each pair may depend on the whole `c′` (and, through the
statement, on `c`): an unordered pair carries no order, so a statement must hold for every
`ord`. The machine's own coins, if any, are averaged by `outputProb`. -/
noncomputable def pairSuccess {m : ℕ} {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (prog : LinSysAmp.Program K) (O : LinSysAmp.Oracle m K) (r : ℕ) (gen : Bool)
    (H : Matrix (Fin r) (Fin m) K) (c : Fin m → K) (ord : (Fin m → K) → Fin m → Bool)
    (N : ℕ) : ℝ :=
  ∑ c' : Fin m → K, (∏ i, if c' i ≠ c i then ((Fintype.card K : ℝ) - 1)⁻¹ else 0) *
    LinSysAmp.outputProb m O prog
      (pairConfig m r gen H (fun i => if ord c' i then c i else c' i)
        (fun i => if ord c' i then c' i else c i)) N c

end TwoFoldOPI


