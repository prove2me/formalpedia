-- Prove2me | Definitions.Def_LowErrExt_IsTwoSourceExtractor
-- name    : LowErrExt_IsTwoSourceExtractor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:36.464325+00:00
-- url     : https://prove2.me/theorems/75cd3758-114f-45a7-b5ed-34c5226ef60c
-- title:
--   Two-source extractors and strong two-source extractors
-- statement:
--   Let $E:A\times B\to O$ with $O$ finite. $E$ is a **$(k,\varepsilon)$ two-source extractor** if for all independent sources $\mathbf X$ on $A$ and $\mathbf Y$ on $B$ with $H_\infty[\mathbf X]\ge k$ and $H_\infty[\mathbf Y]\ge k$,
--   $$E(\mathbf X,\mathbf Y)\approx_\varepsilon U_O,$$
--   i.e. the statistical distance to the uniform distribution on $O$ is at most $\varepsilon$. It is **strong with respect to both sources** if moreover $(E(\mathbf X,\mathbf Y),\mathbf Y)\approx_\varepsilon(U_O,\mathbf Y)$ and $(E(\mathbf X,\mathbf Y),\mathbf X)\approx_\varepsilon(U_O,\mathbf X)$, with $U_O$ independent of the sources.
--
--   **Formalization Note** Min-entropy and statistical distance are the published `FuzzyExtractors.Hamming.minEntropy` and `statDist`. The sources range over all distributions, not only flat ones.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definition 2.24, p.19; p.4

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_indepPair

open FuzzyExtractors.Hamming

namespace LowErrExt

/-- **Two-source extractor `(k, ε)`.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 2.24, p.19, and p.4: "We say that it works for min-entropy k and error ε if for any
independent sources X, Y ∼ {0, 1}n with min-entropy at least k, the output 2Ext(X, Y) is ε-close to
Um (the uniform distribution on m bits), in statistical distance."

`IsTwoSourceExtractor k ε E`: for all sources `X, Y` with `H∞ ≥ k`, the law of `E(X, Y)` for
independent `X, Y` is within statistical distance `ε` of the uniform law on the output type.

**Formalization Note.** Min-entropy and statistical distance are the published
`FuzzyExtractors.Hamming.minEntropy` and `statDist` (½ ∑ |P(v) − Q(v)|). Sources are arbitrary
probability mass functions, not only flat ones. -/
def IsTwoSourceExtractor {A B O : Type*} [Fintype O] [Nonempty O] (k ε : ℝ) (E : A → B → O) : Prop :=
  ∀ (X : PMF A) (Y : PMF B), k ≤ minEntropy X → k ≤ minEntropy Y →
    statDist ((indepPair X Y).map fun p => E p.1 p.2) (PMF.uniformOfFintype O) ≤ ε

/-- **Strong two-source extractor (with respect to both sources).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 2.24, p.19: "We say that the extractor is strong (say in the second input) if
(Ext(X, Y), Y) ≈ε (Um, Y)", and Corollary 5.6, p.37 ("with respect to both sources").

Both `(E(X, Y), Y) ≈ε (U, Y)` and `(E(X, Y), X) ≈ε (U, X)`, with `U` uniform and independent. -/
def IsStrongTwoSourceExtractor {A B O : Type*} [Fintype O] [Nonempty O] (k ε : ℝ) (E : A → B → O) :
    Prop :=
  ∀ (X : PMF A) (Y : PMF B), k ≤ minEntropy X → k ≤ minEntropy Y →
    statDist ((indepPair X Y).map fun p => (E p.1 p.2, p.2))
        (indepPair (PMF.uniformOfFintype O) Y) ≤ ε ∧
      statDist ((indepPair X Y).map fun p => (E p.1 p.2, p.1))
        (indepPair (PMF.uniformOfFintype O) X) ≤ ε

end LowErrExt


