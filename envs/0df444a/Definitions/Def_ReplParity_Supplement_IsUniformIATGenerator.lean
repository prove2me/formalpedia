-- Prove2me | Definitions.Def_ReplParity_Supplement_IsUniformIATGenerator
-- name    : ReplParity_Supplement_IsUniformIATGenerator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:57:58.136793+00:00
-- url     : https://prove2.me/theorems/dfd26f76-baa3-4e9f-9b0f-daefda0d6379
-- title:
--   Definition 2.5 — uniform efficient robust IAT generator with surface bound $A(N,\gamma,\zeta)$
-- statement:
--   A **uniform efficient robust IAT generator** with surface bound $A(N,\gamma,\zeta)$ is a pair of finite-bit algorithms, a generator $G$ and its query program $Q$, such that:
--
--   1. $G$ receives $N$ and rationals $0<\gamma,\zeta<1/2$ together with uniform random bits and runs in time polynomial in $N$, $1/\gamma$, $\log(1/\zeta)$ and the encoding lengths of $\gamma,\zeta$; on a query $q$, $Q$ runs in time polynomial in the same quantities and the encoding length of $q$ (so the returned label also has polynomial length); both use polynomially many random bits;
--   2. in every output $(d,\eta^*)$ of $G$ with $\eta^*>0$, $\log(1/\eta^*)$ is bounded by a polynomial in $N$, $1/\gamma$, $\log(1/\zeta)$;
--   3. for every $N\ge1$ and rationals $0<\gamma,\zeta<1/2$, with probability at least $1-\zeta$ over its random bits, $G$ outputs $(d,\eta^*)$ that, run by $Q$, is a robust description (Definition 2.4) of some $(\gamma,A(N,\gamma,\zeta))$-IAT of $\mathbb R^N$.
--
--   One generator serves every $N,\gamma,\zeta$, and its randomness is its own, independent of any learning data. Statement 2 of Theorem 5.3 asks for such a generator with $A\le CN\,\mathrm{polylog}(N,1/\gamma,1/\zeta)$.
--
--   **Formalization Note** Polynomial time is that of Mathlib's Turing machines (`TM2ComputableInPolyTime`) on the fixed encodings of `genEncoding`; $N+\lceil1/\gamma\rceil+\lceil\log_2(1/\zeta)\rceil$ is supplied in unary so that time polynomial in the input length is time polynomial in $N$, $1/\gamma$, $\log(1/\zeta)$. The encoding lengths of $\gamma,\zeta$ enter as §2.2 requires.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Definition 2.5, p.12 (PDF p.14); finite-bit model §2.2, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ReplParity_Supplement_IAT
import Definitions.Def_ReplParity_Supplement_genEncoding
import Definitions.Def_ReplParity_Supplement_IsRobustDescription

set_option autoImplicit false

namespace ReplParity

namespace Supplement

/-- **Definition 2.5 (Uniform efficient generator).** Shen, Zhong, *Replicable Parity Learning:
Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256
40424491…), Definition 2.5, p.12 (PDF p.14): "A uniform efficient robust IAT generator with surface
bound A(N, γ, ζ) is a finite-bit algorithm that receives N and rationals 0 < γ, ζ < 1/2, runs in time
polynomial in N, 1/γ, and log(1/ζ), and with probability at least 1 − ζ outputs a robust description
of a (γ, A(N, γ, ζ))-IAT. In the description, log(1/η∗) is polynomial in N, 1/γ, and log(1/ζ), and
on a query q the running time and the length of the returned label are polynomial in these
quantities and in the encoding length of q. Its randomness is independent of any learning data."

`IsUniformIATGenerator G gbits Q qbits Abd` says that the generator `G` (using `gbits N γ ζ` random
bits) and its query program `Q` (using `qbits N γ ζ (qSize q)` random bits on the query `q`) form a
uniform efficient robust IAT generator with surface bound `Abd`:
1. `G` and `Q` are computed in polynomial time by Mathlib `TM2` machines on the fixed encodings
   `encGenIn`/`encGenOut` and `encQIn`/`encQOut`; the unary header makes this polynomial in
   `N, 1/γ, log(1/ζ)`, the encoding lengths of `γ, ζ` (and of `q`), and the random bits;
2. on the valid parameter range, both numbers of random bits are polynomial in the same quantities;
3. on that range, `log(1/η∗) ≤ c · padSize(N, γ, ζ)^k + c` for every prescribed-length
   random string whose output has `η∗ > 0`;
4. for every `N ≥ 1` and rationals `0 < γ, ζ < 1/2`, with probability at least `1 − ζ` over its
   random bits, `G`'s output `(d, η∗)` is a robust description (via `Q`) of some
   `(γ, Abd N γ ζ)`-IAT of `ℝ^N`.

**Formalization Note.** One generator and one query program serve every `N, γ, ζ`. Mathlib's
`TM2ComputableInPolyTime` measures time in the input length, so `N + ⌈1/γ⌉ + ⌈log₂(1/ζ)⌉` is supplied
in unary (`encHeader`); the encoding lengths of `γ, ζ` enter as §2.2 requires ("polynomial in … the
encoding lengths of its parameters"). The label length is at most the input length plus the running
time of `Q`, so it is polynomial too. The generator's randomness is its own bits, independent of
any learning data. -/
def IsUniformIATGenerator (G : GenInput → GenOutput) (gbits : ℕ → ℚ → ℚ → ℕ)
    (Q : QInput → Option (List ℚ)) (qbits : ℕ → ℚ → ℚ → ℕ → ℕ) (Abd : ℕ → ℚ → ℚ → ℝ) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encGenIn encGenOut G) ∧
  Nonempty (Turing.TM2ComputableInPolyTime encQIn encQOut Q) ∧
  (∃ k c : ℕ, ∀ (N : ℕ), 1 ≤ N → ∀ (γ ζ : ℚ),
    0 < γ → γ < 1 / 2 → 0 < ζ → ζ < 1 / 2 →
    gbits N γ ζ ≤ c * (padSize N γ ζ + ratSize γ + ratSize ζ) ^ k + c) ∧
  (∃ k c : ℕ, ∀ (N : ℕ), 1 ≤ N → ∀ (γ ζ : ℚ),
    0 < γ → γ < 1 / 2 → 0 < ζ → ζ < 1 / 2 → ∀ s : ℕ,
    qbits N γ ζ s ≤ c * (padSize N γ ζ + ratSize γ + ratSize ζ + s) ^ k + c) ∧
  (∃ k c : ℕ, ∀ (N : ℕ), 1 ≤ N → ∀ (γ ζ : ℚ),
    0 < γ → γ < 1 / 2 → 0 < ζ → ζ < 1 / 2 →
    ∀ r : Fin (gbits N γ ζ) → Bool, 0 < (G (N, γ, ζ, List.ofFn r)).2 →
    Real.log (1 / ((G (N, γ, ζ, List.ofFn r)).2 : ℝ)) ≤
      c * (padSize N γ ζ : ℝ) ^ k + c) ∧
  ∀ N : ℕ, 1 ≤ N → ∀ γ ζ : ℚ, 0 < γ → γ < 1 / 2 → 0 < ζ → ζ < 1 / 2 →
    1 - (ζ : ℝ) ≤ bitProb (gbits N γ ζ) (fun r =>
      ∃ (L : Set (EuclideanSpace ℝ (Fin N)))
        (T : EuclideanSpace ℝ (Fin N) → Set (EuclideanSpace ℝ (Fin N))),
        IsIAT N γ (Abd N γ ζ) L T ∧
        IsRobustDescription Q qbits N γ ζ (G (N, γ, ζ, List.ofFn r)).1
          (G (N, γ, ζ, List.ofFn r)).2 L T)

end Supplement

end ReplParity


