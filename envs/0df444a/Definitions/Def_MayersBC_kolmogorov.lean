-- Prove2me | Definitions.Def_MayersBC_kolmogorov
-- name    : MayersBC_kolmogorov
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:55.102438+00:00
-- url     : https://prove2.me/theorems/d815becb-cd7e-418e-9b08-7c51fdb11261
-- title:
--   Kolmogorov distance $K(p_0,p_1) = \sum_x |p_0(x) - p_1(x)|$
-- statement:
--   For two probability distributions $p_0, p_1$ on a finite set $A$, the **Kolmogorov distance** used by Mayers is
--
--   $$
--   K(p_0, p_1) = \sum_{x \in A} |p_0(x) - p_1(x)| .
--   $$
--
--   There is no factor $\tfrac12$: $K$ takes values in $[0, 2]$. This normalization is the one behind the constants $4\varepsilon$ and $K/2$ of the paper.
--
--   **Formalization Note** Defined for any real functions on a finite type.
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section d, p.7

import Mathlib

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section d, p.7: "The Kolmogorov distance `K(p0, p1)`
between two distributions of probability `p0, p1` on a set `A` is defined by
`K(p0, p1) = Σ_{x∈A} |p0(x) − p1(x)|`."

**Formalization Note.** There is **no factor ½** (unlike the total variation distance), as on
the page; this is what makes the paper's constants `4ε` and `K/2` correct. Defined for any real
functions on a finite type. -/
noncomputable def kolmogorov {J : Type} [Fintype J] (p0 p1 : J → ℝ) : ℝ :=
  ∑ j, |p0 j - p1 j|

end MayersBC


