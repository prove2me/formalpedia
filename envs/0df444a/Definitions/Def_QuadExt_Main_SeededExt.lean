-- Prove2me | Definitions.Def_QuadExt_Main_SeededExt
-- name    : QuadExt_Main_SeededExt
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:03:37.955027+00:00
-- url     : https://prove2.me/theorems/c696de91-4974-42fc-9995-47dc8dbaca3f
-- title:
--   Strong linear seeded extractors (Definition 3.1), for all min-entropy-$k$ sources or for a class
-- statement:
--   A function $\mathrm{LExt} : \mathbb F_2^n \times S \to \mathbb F_2^m$, with $S$ a finite non-empty seed set (seeds in $\{0,1\}^d$, or in $[N]$), is an **$(\varepsilon, \delta)$-strong linear seeded extractor for a class $\mathcal X$** of sources if
--
--   1. $x \mapsto \mathrm{LExt}(x, y)$ is linear over $\mathbb F_2$ for every seed $y$, and
--   2. for every source $X \in \mathcal X$, with probability at least $1 - \varepsilon$ over a uniform seed $y$,
--   $$\mathrm{LExt}(X, y) \approx_\delta U_m .$$
--
--   It is a **$(k, \varepsilon, \delta)$-strong linear seeded extractor** when $\mathcal X$ is the class of all sources with $H_\infty(X) \ge k$, and a **$(k, \varepsilon)$-strong linear seeded extractor** when moreover $\delta = \varepsilon$. $\varepsilon$ is the strength error and $\delta$ the closeness error.
--
--   Two classes are used in §8: quadratic sources $f(U_k)$ ($k \ge 1$ generating bits) with $H_\infty(\partial_a f(U_k)) \ge d$ for every non-zero $a$ (`QuadDerivClass n d`), and affine sources with min-entropy at least $d$ (`AffineClass n d`).
--
--   **Formalization Note.** "With probability at least $1 - \varepsilon$ over the seed" is the count $\#\{\text{good seeds}\} \ge (1-\varepsilon)\,|S|$. The seed set is required to be non-empty: a uniform seed must exist (otherwise the count condition would hold vacuously). `QuadDerivClass` requires $k \ge 1$: at $k = 0$ the derivative condition "for all non-zero $a$" is vacuous and a constant source would enter the class; the proof of Lemma 8.3 works with $k \times k$ matrices, $k \ge 1$.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 4 (PDF 5), Definition 3.1; p. 25 (PDF 26), Lemma 8.3 (the two classes)

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_QuadExt_Main_Sources

namespace QuadExt.Main

/-!
# Strong linear seeded extractors, for all min-entropy-`k` sources or for a class of sources

Chandrasekaran, Goodman, Zuckerman, *Quadratic Extractors*, STOC 2027 submission (manuscript
sha256 ddc80a9a…), p. 4 (PDF 5), Definition 3.1.

Seeds range over a finite set `S` and are uniform on it: `S = Fin d → ZMod 2` for seeds in
`{0,1}^d`, `S = Fin N` for seeds in `[N]` (Lemma 8.3, Theorem 8.1). "With probability at least
`1 − ε` over the seed" is the count `#{good seeds} ≥ (1 − ε)·|S|`.
-/

/-- `E` is an **`(ε, δ)`-strong linear seeded extractor for the class `C`** (Definition 3.1, last
paragraph): the seed set is non-empty (a uniform seed exists), `x ↦ E x y` is 𝔽₂-linear for every
seed `y`, and for every source `X` in `C`, with probability at least `1 − ε` over a uniform seed
`y`, `d_TV(E(X, y), U_m) ≤ δ`. -/
def IsSLSEFor {n m : ℕ} {S : Type} [Fintype S] (C : PMF (Fin n → ZMod 2) → Prop) (ε δ : ℝ)
    (E : (Fin n → ZMod 2) → S → (Fin m → ZMod 2)) : Prop :=
  0 < Fintype.card S ∧ (∀ y, IsLinearMap (ZMod 2) (fun x => E x y)) ∧
  ∀ P, C P → (1 - ε) * (Fintype.card S : ℝ) ≤
    ((Finset.univ.filter fun y =>
        SSNonExt.TV (P.map fun x => E x y) (PMF.uniformOfFintype (Fin m → ZMod 2)) ≤ δ).card : ℝ)

/-- A **`(k, ε, δ)`-strong linear seeded extractor** (Definition 3.1): the class is every source
with `H_∞(X) ≥ k`. A `(k, ε)`-strong linear seeded extractor is the case `δ = ε`. -/
def IsSLSE {n m : ℕ} {S : Type} [Fintype S] (k ε δ : ℝ)
    (E : (Fin n → ZMod 2) → S → (Fin m → ZMod 2)) : Prop :=
  IsSLSEFor (fun P => k ≤ SSNonExt.minEntropy P) ε δ E

/-- The class of **quadratic sources with derivative entropy at least `d`** (Lemma 8.3(1),
Theorem 8.1(1)): `X = f(U_k)` for some `k ≥ 1` and a quadratic `f` with `H_∞(∂_a f(U_k)) ≥ d` for
every non-zero `a ∈ 𝔽₂^k`. At `k = 0` the derivative condition is vacuous and a constant source would
enter the class; the matrices `G_i ∈ 𝔽₂^{k×k}` of the proof of Lemma 8.3 have `k ≥ 1`. -/
def QuadDerivClass (n : ℕ) (d : ℝ) (P : PMF (Fin n → ZMod 2)) : Prop :=
  ∃ (k : ℕ) (f : (Fin k → ZMod 2) → (Fin n → ZMod 2)), 0 < k ∧ IsQuadraticMap f ∧
    (∀ a : Fin k → ZMod 2, a ≠ 0 → d ≤ SSNonExt.minEntropy (source (dirDeriv a f))) ∧ P = source f

/-- The class of **affine sources with entropy at least `d`** (Lemma 8.3(2), Theorem 8.1(2)). -/
def AffineClass (n : ℕ) (d : ℝ) (P : PMF (Fin n → ZMod 2)) : Prop :=
  IsAffineSource P ∧ d ≤ SSNonExt.minEntropy P

end QuadExt.Main


