-- Prove2me | Definitions.Def_MLManagesComplexity_IsCryptoPRG
-- name    : MLManagesComplexity_IsCryptoPRG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:42:21.501009+00:00
-- url     : https://prove2.me/theorems/c3bf6387-74b0-4d1b-b050-32033e65b2f9
-- title:
--   Cryptographic pseudorandom generators and their output distribution
-- statement:
--   Let $\ell:\mathbb N\to\mathbb N$ be a seed length and $G=(G_n)$ a family of maps $G_n:\{0,1\}^{\ell(n)}\to\{0,1\}^n$. The **output distribution** of $G$ is the family $D_n=G_n(s)$ for a uniformly random seed $s\in\{0,1\}^{\ell(n)}$.
--
--   $G$ is a **cryptographic pseudorandom generator** if
--
--   1. $G$ is computable in polynomial time: a single polynomial-time Turing machine maps $1^n0\,s$ to $G_n(s)$ for every $n$ and every seed $s$;
--   2. it stretches: $\ell(n)<n$ for every $n\ge1$;
--   3. its output is pseudorandom: the output distribution $D$ and the uniform family $U$ are computationally indistinguishable (against polynomial-size probabilistic circuit families).
--
--   This is Yao's definition of a pseudorandom generator (§3.3 of the paper); by Håstad, Impagliazzo, Levin and Luby such generators exist if one-way functions exist.
--
--   **Formalization Note** Polynomial time is the published `QAlgorithms.Complexity.PolyTimeComputable` (Mathlib's `TM2ComputableInPolyTime` on bit strings); the machine is also given $n$ in unary, so that it may run in time polynomial in $n$ even when the seed is much shorter. The stretch is required for $n\ge1$, since at $n=0$ no seed length is smaller than $0$. The proof of Theorem 6.3 uses only clause 3.
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), §3.3, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_MLManagesComplexity_CompIndist

set_option autoImplicit false

namespace MLManagesComplexity

/-- The **output distribution of a generator** `G`: `Gₙ(s)` for a uniformly random seed
`s ∈ {0,1}^{ℓ(n)}`, a distribution on `{0,1}^n`. -/
noncomputable def prgDist (ℓ : ℕ → ℕ) (G : (n : ℕ) → (Fin (ℓ n) → Bool) → (Fin n → Bool)) :
    DistFamily :=
  fun n => (PMF.uniformOfFintype (Fin (ℓ n) → Bool)).map (G n)

/-- `G` is a **cryptographic pseudorandom generator** with seed length `ℓ` (Fortnow,
arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), §3.3, printed p.5, PDF p.6:
"Formally, G is computable in polynomial time and takes seeds of length ℓ to outputs of length
n > ℓ such that for all probabilistic P/poly algorithms A,
|Pr_{s∈{0,1}^ℓ}(A(G(s)) = 1) − Pr_{r∈{0,1}^n}(A(r) = 1)| ≤ negl(n)"):
1. one polynomial-time machine `M` computes `Gₙ(s)` from `1ⁿ0` followed by `s`;
2. the output is longer than the seed: `ℓ(n) < n` for every `n ≥ 1`;
3. the output distribution `Gₙ(U_{ℓ(n)})` is computationally indistinguishable from `Uₙ`.

**Formalization Note** `G` is a family indexed by the output length `n`; polynomial time is the
published `QAlgorithms.Complexity.PolyTimeComputable` (Mathlib `TM2ComputableInPolyTime` on
`List Bool`), and the machine also receives `n` in unary (`QAlgorithms.Complexity.encNat n`), so
that it may run in time polynomial in `n` even when the seed is much shorter. The stretch is
required for `n ≥ 1` only, since no seed length is below `0`. -/
def IsCryptoPRG (ℓ : ℕ → ℕ) (G : (n : ℕ) → (Fin (ℓ n) → Bool) → (Fin n → Bool)) : Prop :=
  (∃ M : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable M ∧
      ∀ (n : ℕ) (s : Fin (ℓ n) → Bool),
        M (QAlgorithms.Complexity.encNat n ++ List.ofFn s) = List.ofFn (G n s)) ∧
    (∀ n : ℕ, 1 ≤ n → ℓ n < n) ∧
    CompIndist (prgDist ℓ G) uniformFamily

end MLManagesComplexity


