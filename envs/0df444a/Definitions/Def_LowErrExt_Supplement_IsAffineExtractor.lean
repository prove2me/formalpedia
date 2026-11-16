-- Prove2me | Definitions.Def_LowErrExt_Supplement_IsAffineExtractor
-- name    : LowErrExt_Supplement_IsAffineExtractor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:33:36.71735+00:00
-- url     : https://prove2.me/theorems/16b8aa57-a558-46a0-8744-cefa495d2883
-- title:
--   Affine extractor for min-entropy $k$ with error $\varepsilon$
-- statement:
--   A function $\mathrm{Ext}:\{0,1\}^n\to\{0,1\}^m$ is an **affine extractor for min-entropy $k$ with error $\varepsilon$** if for every affine source $\mathbf X$ on $\mathbb F_2^n$ (a random variable uniform on an affine subspace) with $H_\infty[\mathbf X]\ge k$,
--   $$\mathrm{SD}\big(\mathrm{Ext}(\mathbf X),\,U_m\big)\le\varepsilon,$$
--   where $U_m$ is uniform on $\{0,1\}^m$ and $\mathrm{SD}$ is statistical distance.
--
--   This is the extractor notion of Theorem 4.1 (Theorem 1.2).
--
--   **Formalization Note** Affine sources are the published `IsAffineSource`; $H_\infty$, $\mathrm{SD}$ and $U_m$ are the published `minEntropy`, `statDist`, `uniformBits`; $k$ and $\varepsilon$ are real.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), §1.1, p.5 (affine source); Theorem 4.1, p.29

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_IsAffineSource

namespace LowErrExt.Supplement

open LowErrExt FuzzyExtractors.Hamming

/-- **Affine extractor.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…), §1.1,
p.5 ("An affine source is just a random variable X ∼ F₂ⁿ that is uniform over some affine subspace")
and Theorem 4.1, p.29 ("an explicit affine extractor Ext : {0,1}ⁿ → {0,1}ᵐ for min-entropy k, which
has error ε"): for every affine source `X` on `𝔽₂ⁿ` with `H∞[X] ≥ k`, `Ext(X)` is `ε`-close to the
uniform distribution `U_m`.

**Formalization Note.** Affine sources are the published `IsAffineSource` (uniform on a coset);
`H∞` is the published `minEntropy`; closeness is the published `statDist` against `uniformBits m`;
`k` and `ε` are real. -/
def IsAffineExtractor {n m : ℕ} (k ε : ℝ) (E : (Fin n → ZMod 2) → (Fin m → Bool)) : Prop :=
  ∀ X : PMF (Fin n → ZMod 2), IsAffineSource X → k ≤ minEntropy X →
    statDist (X.map E) (uniformBits m) ≤ ε

end LowErrExt.Supplement


