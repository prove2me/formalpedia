-- Prove2me | Definitions.Def_ZipfLaw_Defs
-- name    : ZipfLaw_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:25:53.895255+00:00
-- url     : https://prove2.me/theorems/80b903ce-0a62-46ef-a030-7a4fb82b4c05
-- title:
--   Zipf's law: generalized harmonic numbers, Zipf / Zipf–Mandelbrot / Yule–Simon laws
-- statement:
--   Core definitions for the Zipf's-law mission.
--
--   1. **Generalized harmonic number.** $H_{N,s}=\sum_{k=1}^N k^{-s}$ for $N\in\mathbb N$ and real $s$ ($H_{0,s}=0$).
--   2. **Zipf distribution.** $f(k;N,s)=\dfrac{1}{H_{N,s}}\dfrac{1}{k^s}$ for $1\le k\le N$, and $f(k;N,s)=0$ for every other natural number $k$.
--   3. **Hurwitz zeta (series form).** $\zeta(s,a)=\sum_{n\ge0}(n+a)^{-s}$.
--   4. **Zipf–Mandelbrot law (infinite ranks).** $f(k;q,s)=\dfrac{1}{\zeta(s,q+1)\,(k+q)^s}$ for $k\ge1$, and $0$ for $k=0$.
--   5. **Yule–Simon distribution.** $f(k;\rho)=\rho\,\dfrac{\Gamma(k)\,\Gamma(\rho+1)}{\Gamma(k+\rho+1)}=\rho\,B(k,\rho+1)$.
--   6. **Leading decimal digit** of a natural number $n\ge1$: $\lfloor n/10^{\lfloor\log_{10}n\rfloor}\rfloor$.
--   7. **Random-typing word probability.** With $m$ equiprobable letter keys, each typed with probability $q$, and a space typed with probability $1-mq$, the probability that the word following a space is exactly $w$ is $q^{|w|}(1-mq)$.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note.** Powers are real powers (`Real.rpow`). The Hurwitz series takes the value $0$ when it is not summable (Lean's `tsum` convention); statements using it assume $s>1$. The leading digit of $0$ is $0$.
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, sections "Formal definition", "Related laws", "Statistical explanations" and the infobox.

import Mathlib

/-!
# Zipf's law — core definitions

Shared definitions for the Zipf's-law mission (source: Wikipedia, "Zipf's law").
-/

namespace ZipfLaw

/-- The `N`-th generalized harmonic number `H_{N,s} = ∑_{k=1}^{N} 1 / k^s`
(real exponent `s`; `H_{0,s} = 0`). -/
noncomputable def genHarmonic (N : ℕ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ^ s

/-- The (generalized) Zipf distribution on `N` elements with exponent `s`: the element of
rank `k ∈ {1, …, N}` has probability `(1 / k^s) / H_{N,s}`; every other `k` gets `0`. -/
noncomputable def zipfPMF (N : ℕ) (s : ℝ) (k : ℕ) : ℝ :=
  if 1 ≤ k ∧ k ≤ N then (1 / (k : ℝ) ^ s) / genHarmonic N s else 0

/-- The Hurwitz zeta function, as its defining series `ζ(s, a) = ∑_{n ≥ 0} 1 / (n + a)^s`
(the value is `0` when the series is not summable). -/
noncomputable def hurwitzZetaSeries (s a : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / ((n : ℝ) + a) ^ s

/-- The Zipf–Mandelbrot law on the ranks `k = 1, 2, 3, …` with shift `q` and exponent `s`:
`f(k; q, s) = (1 / C) · 1 / (k + q)^s` with normalizing constant
`C = ∑_{k ≥ 1} 1 / (k + q)^s = ζ(s, q + 1)` (Hurwitz zeta). Rank `0` gets `0`. -/
noncomputable def zipfMandelbrotPMF (q s : ℝ) (k : ℕ) : ℝ :=
  if 1 ≤ k then 1 / (hurwitzZetaSeries s (q + 1) * ((k : ℝ) + q) ^ s) else 0

/-- The Yule–Simon distribution with parameter `ρ`:
`f(k; ρ) = ρ · B(k, ρ + 1) = ρ · Γ(k) Γ(ρ + 1) / Γ(k + ρ + 1)` for `k = 1, 2, …`. -/
noncomputable def yuleSimonPMF (ρ : ℝ) (k : ℕ) : ℝ :=
  ρ * (Real.Gamma k * Real.Gamma (ρ + 1) / Real.Gamma (k + ρ + 1))

/-- The leading decimal digit of a natural number (`leadingDigit 0 = 0`). -/
def leadingDigit (n : ℕ) : ℕ :=
  n / 10 ^ Nat.log 10 n

/-- Random typing with `m` equiprobable letter keys, each hit with probability `q`, and a
space bar hit with probability `1 - m q`: the probability that the word (maximal block of
letters) following a space is exactly `w`, namely `q^{|w|} (1 - m q)`. -/
noncomputable def monkeyWordProb (m : ℕ) (q : ℝ) (w : List (Fin m)) : ℝ :=
  q ^ w.length * (1 - m * q)

end ZipfLaw


