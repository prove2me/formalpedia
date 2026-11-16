-- Prove2me | Definitions.Def_LowErrExt_Supplement_IsRankExtAffine
-- name    : LowErrExt_Supplement_IsRankExtAffine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:32:37.279773+00:00
-- url     : https://prove2.me/theorems/d9c52ceb-78b9-4ea9-a7fb-f739fe797642
-- title:
--   $k$-rank extractor for affine sources
-- statement:
--   A function $\mathrm{Ext}:\mathbb F_2^n\to\mathbb F_2^m$ is a **$k$-rank extractor for affine sources** if for every affine subspace $A\subseteq\mathbb F_2^n$ with
--   $$H_0[A]=\log_2|A|\ge k,$$
--   the image $\mathrm{Ext}(A)=\{\mathrm{Ext}(a):a\in A\}$ has dimension $m$, i.e. its affine span is all of $\mathbb F_2^m$.
--
--   Rank extractors are the zero-error, "full support" analogue of affine extractors; an affine extractor with error below $1/2$ is one (Observation 3.19).
--
--   **Formalization Note** Affine subspaces of $\mathbb F_2^n$ are the cosets (published `IsCoset`); dimension is the published `dimSet`, the dimension of the affine span; $k$ is real.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definition 3.17, p.25

import Mathlib
import Definitions.Def_LowErrExt_H2
import Definitions.Def_LowErrExt_IsCoset
import Definitions.Def_LowErrExt_dimSet

namespace LowErrExt.Supplement

open LowErrExt

/-- **Rank extractor for affine sources.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 3.17, p.25: "A function Ext : F₂ⁿ → F₂ᵐ is a k-rank extractor for affine sources if, for
any affine space X ⊆ F₂ⁿ with H0[X] ≥ k, it holds that Ext(X) has dimension m."

**Formalization Note.** Affine spaces of `𝔽₂ⁿ` are the cosets (`IsCoset`, published); `H0` is the
published `log₂` of the size; `Ext(X)` is the image set and its dimension is the published
`dimSet` (dimension of the affine span, p.22). `k` is real. -/
def IsRankExtAffine {n m : ℕ} (k : ℝ) (E : (Fin n → ZMod 2) → (Fin m → ZMod 2)) : Prop :=
  ∀ A : Set (Fin n → ZMod 2), IsCoset A → k ≤ H0 A → dimSet (E '' A) = m

end LowErrExt.Supplement


