-- Prove2me | Definitions.Def_MantriCVQ_Supplement_HeightBounds
-- name    : MantriCVQ_Supplement_HeightBounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:02:23.805345+00:00
-- url     : https://prove2.me/theorems/c3b0693d-2e48-4e66-bccf-cb3032a7001c
-- title:
--   The properties of Theorem 1.3 for $(h,O,L)$
-- statement:
--   For a height function $h$, an oracle $O$ and a language $L$, this predicate collects the full conclusion of Theorem 1.3. $L$ is a total unary language ($L\subseteq\{1^n\}$) with $L\in\mathsf{EQP}^O$ and $L\notin\mathsf{PH}^O$, and there is one polynomial $p$ such that on input $1^n$, $n\ge1$:
--
--   1. **(i)** a uniform family of polynomial-size quantum circuits over $\{H,X,\mathrm{Toffoli}\}$ with oracle gates decides $L$ exactly (acceptance probability $1$ on $L$, $0$ off $L$), its circuit for length $n$ has exactly $3^{h(n)}$ oracle gates, and its size and ancilla count are at most $3^{h(n)}p(n)$;
--   2. **(ii)** there are a public-coin verifier in the fixed-schedule form of §3.1 and a uniform quantum honest prover with perfect completeness on $L$ and soundness error at most $1/4$ against every prover strategy off $L$; the schedule on $1^n$ has exactly $2h(n)$ slots (alternating, so $h(n)$ for each party); the prover's slot lengths sum to less than $n\cdot4^{h(n)}/3$ and the verifier's to less than $n\cdot4^{h(n)}$; along every transcript of the schedule the decision machine halts within $4^{h(n)}p(n)$ steps and makes at most $4^{h(n)}$ oracle queries;
--   3. **(iii)** along every transcript of the schedule, the honest prover's circuits at its slots have exactly $4^{h(n)}-3^{h(n)}$ oracle gates in total and total size at most $4^{h(n)}p(n)$.
--
--   Theorem 1.3 asserts that these properties can be achieved for every height function, and Theorem 1.6 asserts that they can be achieved together with a matching message lower bound; both use this one predicate.
--
--   **Formalization Note** The gate set $\{H,X,\mathrm{Toffoli}\}$ is the smallest admissible one, as in the published goal. Query counts are exact numbers of oracle gates; time is circuit size (and ancilla count for the algorithm) and the step count of the verifier's decision machine with the oracle $O$. The prover's slots are those of the verifier's alternating schedule, whatever the first speaker.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 1.3, pp. 3–4 (PDF pp. 5–6); §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_MantriCVQ_EQP
import Definitions.Def_MantriCVQ_PH
import Definitions.Def_MantriCVQ_G0
import Definitions.Def_MantriCVQ_acceptProb
import Definitions.Def_MantriCVQ_QProver
import Definitions.Def_MantriCVQ_queryCount
import Definitions.Def_MantriCVQ_Implements53

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ.Supplement

open MantriCVQ

/-- The conclusion of Theorem 1.3 for the height function `h`, the oracle `O` and the language `L`
(Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 1.3, pp. 3–4 (PDF pp. 5–6)):
`L` is a total unary language with `L ∈ EQP^O` and `L ∉ PH^O`, and on input `1^n`:

(i) a uniform quantum algorithm decides `L` exactly with `3^{h(n)}` queries and in time
`3^{h(n)} poly(n)`;

(ii) `L` has a public-coin interactive proof system relative to `O` with perfect completeness and
soundness error at most `1/4` against every prover, in which the parties exchange `2h(n)` messages,
`h(n)` from each; the prover sends fewer than `n · 4^{h(n)}/3` bits and the verifier fewer than
`n · 4^{h(n)}` random bits; the verifier makes at most `4^{h(n)}` queries and runs in time
`4^{h(n)} poly(n)`;

(iii) the honest prover is a uniform quantum algorithm that makes `4^{h(n)} − 3^{h(n)}` queries and
runs in time `4^{h(n)} poly(n)`.

It is a definition so that Theorem 1.6 ("with the properties of Theorem 1.3") uses the same text.

**Formalization Note** The gate set is `{H, X, Toffoli}` (`G0`), the smallest admissible one, as in
the published goal `MantriCVQ.theorem_1_1`. "With `3^{h(n)}` queries" is exactly `3^{h(n)}` oracle
gates in the circuit for length `n`, and "`4^{h(n)} − 3^{h(n)}` queries" is exactly that many oracle
gates summed over the prover's circuits at its slots, along every transcript of the schedule (as in
`MantriCVQ.theorem_5_5`). Time is circuit size and ancilla count for the algorithm, circuit size for
the prover, and the step count of the decision machine `D` with the oracle `O` for the verifier,
whose queries are counted by `queryCount`. `poly(n)` is one polynomial `p`. The `2h(n)` messages
are the `2h(n)` slots of the schedule; slots alternate, so `h(n)` belong to each party, and the
prover's slots are those of `PCVerifier.proverSlot` (the first speaker is not fixed). The bit counts
are sums of slot lengths and are compared in `ℝ`. The bounds are stated for `n ≥ 1`. -/
def HeightBounds (h : ℕ → ℕ) (O : Oracle) (L : Set Str) : Prop :=
  L ⊆ Set.range unary ∧ L ∈ EQP G0 O ∧ L ∉ PH O ∧
  ∃ p : Polynomial ℕ,
    -- (i) the exact quantum algorithm
    (∃ F : ExactFamily G0, F.Uniform ∧ F.PolyBounded ∧
      (∀ x : Str, (x ∈ L → F.acceptProb O x = 1) ∧ (x ∉ L → F.acceptProb O x = 0)) ∧
      ∀ n : ℕ, 1 ≤ n →
        (F.circ n).queries = 3 ^ h n ∧ (F.circ n).size ≤ 3 ^ h n * p.eval n ∧
          F.anc n ≤ 3 ^ h n * p.eval n) ∧
    -- (ii) and (iii) the proof system and its honest prover
    ∃ (V : PCVerifier) (P : QProver G0), P.Uniform ∧ P.PolyBounded ∧
      (∀ w ∈ L, acceptProb O V (P.toStrategy O) w = 1) ∧
      (∀ w : Str, w ∉ L → ∀ σ : Strategy, acceptProb O V σ w ≤ 1 / 4) ∧
      ∀ n : ℕ, 1 ≤ n →
        V.S (unary n) = 2 * h n ∧
        (((∑ i ∈ (Finset.range (2 * h n)).filter (fun i => V.proverSlot (unary n) i = true),
            V.len (unary n) i : ℕ) : ℝ) < (n : ℝ) * 4 ^ h n / 3) ∧
        (((∑ i ∈ (Finset.range (2 * h n)).filter (fun i => V.proverSlot (unary n) i = false),
            V.len (unary n) i : ℕ) : ℝ) < (n : ℝ) * 4 ^ h n) ∧
        ∀ tr : List Str, Conforms V (unary n) tr →
          (V.D.result O (tup (unary n :: tr)) (4 ^ h n * p.eval n)).isSome ∧
          queryCount V.D O (tup (unary n :: tr)) (4 ^ h n * p.eval n) ≤ 4 ^ h n ∧
          (∑ i ∈ (Finset.range (2 * h n)).filter (fun i => V.proverSlot (unary n) i = true),
              (P.circ (unary n) i (tup (unary n :: tr.take i)).length).queries) =
            4 ^ h n - 3 ^ h n ∧
          (∑ i ∈ (Finset.range (2 * h n)).filter (fun i => V.proverSlot (unary n) i = true),
              (P.circ (unary n) i (tup (unary n :: tr.take i)).length).size) ≤
            4 ^ h n * p.eval n

end MantriCVQ.Supplement


