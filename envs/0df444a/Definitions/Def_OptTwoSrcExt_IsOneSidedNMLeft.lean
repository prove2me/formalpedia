-- Prove2me | Definitions.Def_OptTwoSrcExt_IsOneSidedNMLeft
-- name    : OptTwoSrcExt_IsOneSidedNMLeft
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:25:00.662924+00:00
-- url     : https://prove2.me/theorems/1e8fb313-8225-44aa-bc1a-303634edca6e
-- title:
--   One-sided non-malleability against fixed-point-free left (or right) maps
-- statement:
--   Let $G:\mathcal A\times\mathcal B\to\mathcal O$ be a function into a finite set, $k$ a min-entropy threshold and $\gamma\ge0$ an error. $G$ is **one-sided non-malleable against fixed-point-free left maps at threshold $k$ with error $\gamma$** if for every map $f:\mathcal A\to\mathcal A$ with $f(x)\ne x$ for all $x$, and all independent sources $X,Y$ with $H_\infty(X),H_\infty(Y)\ge k$,
--   $$\Delta\big((G(X,Y),\,G(f(X),Y)),\ (U,\,G(f(X),Y))\big)\le\gamma,$$
--   where $U$ is uniform on $\mathcal O$ and independent of the actual tampered output $G(f(X),Y)$. The **right** version tampers only the second source: maps $g$ with $g(y)\ne y$, and the comparison $(G(X,Y),G(X,g(Y)))$ against $(U,G(X,g(Y)))$.
--
--   This is hypothesis (i) of the collision-recycling Lemma 4.1 and the shape of guarantee (3.36) of the sumset seed.
--
--   **Formalization Note** Min-entropy, statistical distance and the law of an independent pair are the published `FuzzyExtractors.Hamming.minEntropy`, `statDist` and `LowErrExt.indepPair`; sources are arbitrary probability mass functions, and no entropy assumption is made on $f(X)$.
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Lemma 4.1 (i), p.80 (PDF p.82); (3.36), p.48; Definition 2.2, p.14

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_indepPair

open FuzzyExtractors.Hamming LowErrExt

namespace OptTwoSrcExt

/-- **One-sided non-malleability against fixed-point-free left maps.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Lemma 4.1 (i), printed p.80 (PDF p.82): "G is one-sided
non-malleable against every fixed-point-free left map at component threshold k − 4 with error γ";
the comparison is that of (3.36), p.48, and Definition 2.2, p.14, with one tampering of the left
source only.

`IsOneSidedNMLeft k γ G`: for every map `f` with `f(x) ≠ x` for all `x`, and all independent
sources `X, Y` with min-entropy at least `k`,
`Δ((G(X, Y), G(f(X), Y)), (U, G(f(X), Y))) ≤ γ`, where `U` is uniform on the output type and
independent of the actual tampered output `G(f(X), Y)`.

**Formalization Note.** Min-entropy and statistical distance are the published
`FuzzyExtractors.Hamming.minEntropy` and `statDist`; the law of an independent pair is
`LowErrExt.indepPair`. Sources are arbitrary probability mass functions. No entropy assumption is
made on `f(X)`. -/
def IsOneSidedNMLeft {A B O : Type*} [Fintype O] [Nonempty O] (k γ : ℝ) (G : A → B → O) : Prop :=
  ∀ f : A → A, (∀ x, f x ≠ x) → ∀ (X : PMF A) (Y : PMF B), k ≤ minEntropy X → k ≤ minEntropy Y →
    statDist ((indepPair X Y).map fun p => (G p.1 p.2, G (f p.1) p.2))
      (indepPair (PMF.uniformOfFintype O) ((indepPair X Y).map fun p => G (f p.1) p.2)) ≤ γ

/-- **One-sided non-malleability against fixed-point-free right maps** (the "right-tampering
version of (i)").
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Lemma 4.1, printed p.81 (PDF p.83): "The symmetric
conclusion with X retained follows by exchanging the sources and using the right-tampering version
of (i)."

`IsOneSidedNMRight k γ G`: for every map `g` with `g(y) ≠ y` for all `y`, and all independent
sources `X, Y` with min-entropy at least `k`,
`Δ((G(X, Y), G(X, g(Y))), (U, G(X, g(Y)))) ≤ γ`. -/
def IsOneSidedNMRight {A B O : Type*} [Fintype O] [Nonempty O] (k γ : ℝ) (G : A → B → O) : Prop :=
  ∀ g : B → B, (∀ y, g y ≠ y) → ∀ (X : PMF A) (Y : PMF B), k ≤ minEntropy X → k ≤ minEntropy Y →
    statDist ((indepPair X Y).map fun p => (G p.1 p.2, G p.1 (g p.2)))
      (indepPair (PMF.uniformOfFintype O) ((indepPair X Y).map fun p => G p.1 (g p.2))) ≤ γ

end OptTwoSrcExt


