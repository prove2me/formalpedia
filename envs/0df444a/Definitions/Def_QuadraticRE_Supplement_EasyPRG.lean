-- Prove2me | Definitions.Def_QuadraticRE_Supplement_EasyPRG
-- name    : QuadraticRE_Supplement_EasyPRG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:51:51.09321+00:00
-- url     : https://prove2.me/theorems/45221a9a-fb0f-48c1-bc89-758da2260866
-- title:
--   The easy PRG assumption
-- statement:
--   The **easy PRG assumption** of Applebaum, Ishai and Kushilevitz asks for a secure pseudorandom generator whose output bits can each be computed from the seed by a mod-2 branching program, with program size and construction time polynomial in the seed length.
--
--   Precisely: there are a stretch $\ell:\mathbb N\to\mathbb N$ with $\ell(k)>k$ for every $k\ge1$ and representations $G_k$ by mod-2 branching programs (one per output bit) of maps $G_k:\{0,1\}^k\to\{0,1\}^{\ell(k)}$ such that
--
--   1. one polynomial-time machine computes the representation $G_k$ from $1^k$, and
--   2. for every nonuniform probabilistic polynomial-time distinguisher $A$,
--   $$\Big|\Pr_{s\leftarrow\{0,1\}^k}\big[A(1^k,G_k(s))=1\big]-\Pr_{u\leftarrow\{0,1\}^{\ell(k)}}\big[A(1^k,u)=1\big]\Big|$$
--   is negligible in $k$.
--
--   This is the hypothesis of Theorem 4.13 (computational quadratic encodings for circuits).
--
--   **Formalization Note** No stretch is named on the page; the textbook notion of a pseudorandom generator only requires $\ell(k)>k$, which is the weakest reading of the hypothesis. Polynomial program size follows from the polynomial construction time. Distinguishers and negligibility are the published `QuadraticRE.Distinguisher` and `QuadraticRE.Negligible`.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), §4.4, p.30; §3.1, p.13

import Mathlib
import Definitions.Def_QuadraticRE_CompPrivate

namespace QuadraticRE.Supplement

open QuadraticRE

/-- The easy PRG assumption of Applebaum, Ishai and Kushilevitz, as stated in Orsini, Patra, *From
Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), §4.4, p.30: "a secure
pseudorandom generator whose output bits can each be computed from the seed by a mod-2 branching
program, with both the program size and its construction time polynomial in the seed length".

There are a stretch `ℓ` with `ℓ k > k` for every seed length `k ≥ 1` and a sequence `G k` of mod-2
branching-program representations (one program per output bit) with `k` input and `ℓ k` output bits,
such that one polynomial-time machine maps `1^k` to the encoding of `G k`, and for every nonuniform
probabilistic polynomial-time distinguisher `A` the advantage between `G_k(s)` on a uniform seed `s`
and a uniform string `u` of length `ℓ k` is negligible in `k`.

**Formalization Note.** "Secure pseudorandom generator" is the textbook notion with minimal stretch
`ℓ k > k` (no stretch is named on the page). Polynomial program size follows from the polynomial
construction time (the encoding lists every vertex), so it is not a separate clause. Distinguishers
and negligibility are the base mission's `Distinguisher` and `Negligible` (Def 3.7 conventions). -/
def EasyPRG : Prop :=
  ∃ (ℓ : ℕ → ℕ) (G : ℕ → Rep),
    (∀ k, 1 ≤ k → k < ℓ k) ∧
    (∀ k, (G k).N = k ∧ (G k).b = ℓ k) ∧
    PolyTimeFn encNat (fun k => encTokens (repTokens (G k))) ∧
    ∀ A : Distinguisher,
      Negligible fun k =>
        |prob (fun ω : (Fin (G k).N → F2) × (Fin (A.coins k) → F2) =>
            A.Accepts k (bits ((G k).eval ω.1)) ω.2)
          - prob (fun ω : (Fin (G k).b → F2) × (Fin (A.coins k) → F2) =>
            A.Accepts k (bits ω.1) ω.2)|

end QuadraticRE.Supplement


