-- Prove2me | Definitions.Def_FuzzyExtractors_ImprovedJS_Basic
-- name    : FuzzyExtractors_ImprovedJS_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:26.745504+00:00
-- url     : https://prove2.me/theorems/6a30fcb9-ff6e-4e5c-a111-22d1d6261524
-- title:
--   The metric $\mathrm{SDif}_s(\mathcal U)$ and the improved Juels–Sudan sketch (Construction 5)
-- statement:
--   This module fixes the objects of Theorem 6.1 of Dodis, Ostrovsky, Reyzin and Smith that are specific to §6.2. Average min-entropy and (average-case) secure sketches are declared in the shared module `FuzzyExtractors.Hamming.Basic`, which this module imports; they are recalled in the next two paragraphs for reference.
--
--   **Random variables and average min-entropy.** A random variable is identified with its law. For a pair $(A,B)$ with joint law $P_{AB}$, the *average min-entropy* of $A$ given $B$ (§2.4, p. 9) is
--
--   $$\tilde H_\infty(A\mid B) \;=\; -\log_2 \mathbb E_{b\leftarrow B}\Big[\max_a \Pr[A=a\mid B=b]\Big] \;=\; -\log_2 \sum_b \max_a \Pr[A=a \wedge B=b].$$
--
--   **Secure sketches (Definitions 3 and 4, p. 11).** Let $\mathcal M$ be a set with an integer-valued distance $\mathrm{dis}$. A pair of randomized procedures $(\mathsf{SS},\mathsf{Rec})$ is *correct for $t$* if for all $w,w'$ with $\mathrm{dis}(w,w')\le t$ and every possible output $v$ of $\mathsf{SS}(w)$, $\mathsf{Rec}(w',v)=w$ with probability one. It is an *average-case $(\mathcal M,m,\tilde m,t)$-secure sketch* if it is correct for $t$ and, for all random variables $W$ over $\mathcal M$ and $I$ (any auxiliary information) with $\tilde H_\infty(W\mid I)\ge m$, one has $\tilde H_\infty(W\mid(\mathsf{SS}(W),I))\ge\tilde m$, where the coins of $\mathsf{SS}$ are independent of $(W,I)$.
--
--   **The metric $\mathrm{SDif}_s(\mathcal U)$ (§2.1, p. 7; §6, p. 18).** For a universe $\mathcal U$, $\mathrm{SDif}_s(\mathcal U)$ is the set of $s$-element subsets of $\mathcal U$ with distance $\mathrm{dis}(w,w')=|w\triangle w'|$.
--
--   **Construction 5 (p. 21).** Let $\mathcal F$ be a finite field, the universe $\mathcal U=\mathcal F$, and $s,t$ natural numbers.
--   1. $\mathsf{SS}(w)$: let $p'(z)=\prod_{x\in w}(z-x)$ and output the coefficients of $p'$ of degree $s-1$ down to $s-t$, a vector $(a_{s-1},\dots,a_{s-t})\in\mathcal F^t$.
--   2. $\mathsf{Rec}(w',(a_{s-1},\dots,a_{s-t}))$: let $p_{\mathrm{high}}(z)=z^s+\sum_{i=s-t}^{s-1}a_iz^i$. If there is a polynomial $p_{\mathrm{low}}$ of degree at most $s-t-1$ with $p_{\mathrm{low}}(x)=p_{\mathrm{high}}(x)$ for at least $s-t/2$ points $x\in w'$, choose one; if the set of roots of $p_{\mathrm{high}}-p_{\mathrm{low}}$ has exactly $s$ elements, output it. Otherwise ("fail") output $w'$.
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note.** Laws are `PMF`s and randomized procedures are kernels `M → PMF S`; both procedures of Construction 5 are deterministic (`PMF.pure`). $\tilde H_\infty$ is written in the joint form above, which equals the paper's average and avoids conditioning on null events; logarithms are base 2. The auxiliary variable $I$ ranges over an arbitrary type `ι : Type` (a superset of the paper's $\{0,1\}^*$). The universe $\mathcal U$ is the field $\mathcal F$ itself, so $n=|\mathcal U|$ is a prime power automatically. "Degree at most $s-t-1$" is `degree < s - t` (so $p_{\mathrm{low}}=0$ when $t=s$), and "at least $s-t/2$ points" is doubled to $2\cdot\#\ge 2s-t$ to stay in $\mathbb N$. Entry $i$ of the sketch vector (`Fin t`) is the coefficient of degree $s-1-i$. The paper's "fail" is an output outside $\mathcal M$; here $\mathsf{Rec}$ returns $w'$ instead, which only matters when $\mathrm{dis}(w,w')>t$, where the paper makes no guarantee. The paper's Step 3 asks for *a* polynomial found by Reed–Solomon decoding; we take an arbitrary one by choice, and running time is not modelled.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, §2.1 (set difference metric) p. 7, §2.4 (average min-entropy) p. 9, Definitions 3–4 p. 11, §6 (SDif_s) p. 18, §6.2 and Construction 5, pp. 20–21

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
open scoped ENNReal
open Polynomial

noncomputable section

namespace FuzzyExtractors.ImprovedJS

/-! ### Shared model (Dodis–Ostrovsky–Reyzin–Smith, §2.4 and §3.1) -/

/-! ### The set difference metric on s-element sets (§2.1, p. 7; §6, p. 18) -/

/-- SDif_s(𝓤): the s-element subsets of the universe `𝓤`. -/
abbrev SDifS (𝓤 : Type) (s : ℕ) : Type := {w : Finset 𝓤 // w.card = s}

/-- The set difference distance dis(w, w′) = |w △ w′|. -/
def sdifDist {𝓤 : Type} [DecidableEq 𝓤] {s : ℕ} (w w' : SDifS 𝓤 s) : ℕ :=
  (symmDiff w.1 w'.1).card

/-! ### Construction 5 (improved Juels–Sudan sketch, p. 21), over the field 𝔽 = GF(n) -/

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]

/-- p′(z) = ∏_{x ∈ w} (z − x), the monic polynomial whose roots are the points of w (Step 1 of SS). -/
def charPoly (w : Finset 𝔽) : 𝔽[X] := ∏ x ∈ w, (X - C x)

/-- The sketch value: the coefficients of p′ of degree s − 1 down to s − t (Step 2 of SS);
entry `i : Fin t` is the coefficient of degree s − 1 − i. -/
def sketchCoeffs (s t : ℕ) (w : Finset 𝔽) : Fin t → 𝔽 :=
  fun i => (charPoly w).coeff (s - 1 - (i : ℕ))

/-- SS(w) for Construction 5 (deterministic). -/
def sketch (s t : ℕ) (w : SDifS 𝔽 s) : PMF (Fin t → 𝔽) :=
  PMF.pure (sketchCoeffs s t w.1)

/-- p_high(z) = z^s + Σ_{i=s−t}^{s−1} a_i z^i, built from the sketch value
(`coeffs i` is the coefficient of degree s − 1 − i) (Step 1 of Rec). -/
def pHigh (s t : ℕ) (coeffs : Fin t → 𝔽) : 𝔽[X] :=
  X ^ s + ∑ i : Fin t, C (coeffs i) * X ^ (s - 1 - (i : ℕ))

/-- The condition of Step 3 of Rec: `pLow` has degree at most s − t − 1 (i.e. `degree < s − t`)
and agrees with p_high on at least s − t/2 points of w′ (doubled to stay in ℕ). -/
def Step3Cond (s t : ℕ) (coeffs : Fin t → 𝔽) (w' : Finset 𝔽) (pLow : 𝔽[X]) : Prop :=
  pLow.degree < ((s - t : ℕ) : WithBot ℕ) ∧
    2 * s - t ≤ 2 * (w'.filter fun x => pLow.eval x = (pHigh s t coeffs).eval x).card

open Classical in
/-- Rec(w′, a) for Construction 5 (deterministic). If some p_low satisfies Step 3, take one and
return the set of roots of p_high − p_low when it has s elements. The paper's "fail" (no p_low,
or a root set that is not an s-element set) is encoded by returning w′ itself. -/
def recover (s t : ℕ) (w' : SDifS 𝔽 s) (coeffs : Fin t → 𝔽) : PMF (SDifS 𝔽 s) :=
  PMF.pure <|
    if h : ∃ pLow, Step3Cond s t coeffs w'.1 pLow then
      if hR : (pHigh s t coeffs - Classical.choose h).roots.toFinset.card = s then
        ⟨(pHigh s t coeffs - Classical.choose h).roots.toFinset, hR⟩
      else w'
    else w'

end FuzzyExtractors.ImprovedJS


