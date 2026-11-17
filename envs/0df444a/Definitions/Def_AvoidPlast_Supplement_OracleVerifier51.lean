-- Prove2me | Definitions.Def_AvoidPlast_Supplement_OracleVerifier51
-- name    : AvoidPlast_Supplement_OracleVerifier51
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:00:21.736311+00:00
-- url     : https://prove2.me/theorems/d3f876d9-0c94-4a11-9d27-f0699ab0b5c5
-- title:
--   The verifier of Theorem 5.1
-- statement:
--   For a family $C$, an output length $m$, $\delta>0$, an ensemble $D$, a bound $p$, a language $L$ and $e\ge1$: there is a verifier $V$ reading $x$, the oracle $C_x$, one prover message $z$ of $\lceil n^\delta\rceil$ bits and a random string $\rho$ of $K(\lceil n^\delta\rceil+1)$ bits, such that for every $n$:
--
--   1. $V$ runs in time $a(n^a+1)$ and work space $K(n^\delta+1)$;
--   2. the interaction is one-way, the prover sending $z$;
--   3. with probability at least $1-p(n)$ over $x\sim D_n$, if $x\in L$ then some $z$ makes $V$ accept for every $\rho$;
--   4. for every $x\notin L$ and every $z$, $V$ accepts with probability at most $2^{-(\lg n)^e}$ over $\rho$.
--
--   **Formalization Note** The random string fits in the space bound, so two-way access to it gives nothing beyond storing it. $\lg n=\log_2(n+2)$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.1, items 1–4, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_lg
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_workSpace
import Definitions.Def_AvoidPlast_Supplement_Ensemble
import Definitions.Def_AvoidPlast_Supplement_pr
import Definitions.Def_AvoidPlast_Supplement_oracleTable

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The conclusion of Theorem 5.1 for a language `L` and a polylog exponent `e` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728),
Theorem 5.1, items 1–4, p.21): a probabilistic verifier `V` with read-only tapes for the input
`x`, the oracle `C_x` (`oracleTable`), the prover's one message `z` of `⌈n^δ⌉` bits, and its
random string `ρ`, such that for every `n`:

1. `V` runs in time `a(n^a + 1)` and work space `K(n^δ + 1)`;
2. the interaction is one-way, the prover sending `z`;
3. with probability at least `1 - p(n)` over `x ∼ D_n`, if `x ∈ L` then some `z` makes `V`
   accept with probability `1`;
4. every `x ∉ L` is accepted, against every `z`, with probability at most `2^{-(lg n)^e}`.

**Formalization Note** The random string has the fixed length `K(⌈n^δ⌉ + 1)`, within the space
bound, so reading it two-way gives nothing beyond storing it (the proof uses `polylog(n)` random
bits, p.22). -/
def OracleVerifier51 (C : List Bool → List Bool → List Bool) (m : ℕ → ℕ) (δ : ℝ)
    (D : Ensemble) (p : ℕ → ℝ) (L : Set (List Bool)) (e : ℝ) : Prop :=
  ∃ (V : Machine 4) (a K : ℕ),
    (∀ x z ρ : List Bool, z.length = ceilPow δ x.length → ρ.length = K * (ceilPow δ x.length + 1) →
      HaltsWithin V ![x, oracleTable C (ceilPow δ) m x, z, ρ] (a * (x.length ^ a + 1)) ∧
      (workSpace V ![x, oracleTable C (ceilPow δ) m x, z, ρ] : ℝ) ≤ K * ((x.length : ℝ) ^ δ + 1)) ∧
    (∀ n : ℕ, 1 - p n ≤ pr (D.dist n) fun x => x ∈ L →
      ∃ z : List Bool, z.length = ceilPow δ n ∧ ∀ ρ : List Bool, ρ.length = K * (ceilPow δ n + 1) →
        Accepts V ![x, oracleTable C (ceilPow δ) m x, z, ρ]) ∧
    ∀ x : List Bool, x ∉ L → ∀ z : List Bool, z.length = ceilPow δ x.length →
      prob (K * (ceilPow δ x.length + 1)) (fun ρ => Accepts V ![x, oracleTable C (ceilPow δ) m x, z, ρ])
        ≤ (2 : ℝ) ^ (-(lg x.length) ^ e)

end AvoidPlast.Supplement


