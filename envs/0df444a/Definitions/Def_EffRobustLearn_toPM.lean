-- Prove2me | Definitions.Def_EffRobustLearn_toPM
-- name    : EffRobustLearn_toPM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:30:58.106528+00:00
-- url     : https://prove2.me/theorems/dbad38b8-df52-4286-9976-b414df3f528a
-- title:
--   The $\pm1$ value of a Boolean concept
-- statement:
--   Concepts and labels take values in $\{\pm1\}$ in the paper. They are stored as Booleans, with $\mathrm{pm}(\mathrm{true})=1$ and $\mathrm{pm}(\mathrm{false})=-1$, and a concept $c:X\to\mathrm{Bool}$ is read as the real function $x\mapsto\mathrm{pm}(c(x))$.
--
--   Every concept enters the errors, the certificate and $\mathrm{conv}(C)$ through this cast.
--
--   **Formalization Note** Boolean values let the published VC-dimension definition apply directly.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), §1, p.1 (PDF p.2), concepts $X\to\{\pm1\}$

import Mathlib

namespace EffRobustLearn

/-- The ±1 value of a Boolean label: `true` is `+1`, `false` is `-1`.

**Formalization Note.** Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), writes concepts and labels with values in `{±1}`. This development stores them as `Bool`, so that the published
`UnderstandingML.vcDim` and `UnderstandingML.PointwiseSeparable` apply, and reads them as reals only through `pm`. -/
noncomputable def pm (b : Bool) : ℝ := if b then 1 else -1

/-- The real ±1-valued function `x ↦ c(x)` of a concept `c : X → Bool` (see `pm`). Every concept enters
the errors, the certificate and `conv(C)` through this cast. -/
noncomputable def toPM {X : Type*} (c : X → Bool) : X → ℝ := fun x => pm (c x)

end EffRobustLearn


