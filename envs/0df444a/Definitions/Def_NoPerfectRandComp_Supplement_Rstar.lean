-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_Rstar
-- name    : NoPerfectRandComp_Supplement_Rstar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:20:50.176507+00:00
-- url     : https://prove2.me/theorems/cff505f4-9c04-4d3d-bc7c-37deb3f343a9
-- title:
--   Composition limit $\mathrm{R}^*(f)$
-- statement:
--   The **composition limit** of a Boolean function $f$ is
--   $$
--   \mathrm{R}^*(f) = \lim_{d\to\infty}\mathrm{R}\bigl(f^{\circ d}\bigr)^{1/d}.
--   $$
--
--   **Formalization Note** The paper writes a limit; this definition is the $\limsup$ of the sequence, which lies in $[0,n]$ for $f$ on $n$ bits. Theorem 10.7 bounds the $\liminf$ from below and this $\limsup$ from above, so the bounds hold for every limit point, and for the limit when it exists.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), p.4

import Mathlib
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_Supplement_iterComp

namespace NoPerfectRandComp

namespace Supplement

/-- The composition limit `R*(f) = lim_d R(f^{∘d})^{1/d}` studied in [3] (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.4).

**Formalization Note** The paper writes a limit. This is its `limsup` over `d → ∞` in `ℝ`; the
sequence lies in `[0, n]` for `f` on `n` bits (`R(f^{∘d}) ≤ n^d`), so the `limsup` is a genuine
one. Theorems about `R*` in this supplement bound the `liminf` from below and the `limsup` from
above, so every limit point obeys them. -/
noncomputable def Rstar {ι : Type} (f : (ι → Bool) → Bool) : ℝ :=
  Filter.limsup (fun d : ℕ => (Rt (iterComp f d) : ℝ) ^ ((1 : ℝ) / d)) Filter.atTop

end Supplement

end NoPerfectRandComp


