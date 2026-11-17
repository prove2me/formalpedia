-- Prove2me | Definitions.Def_Max3CutHard_Supplement_maxS
-- name    : Max3CutHard_Supplement_maxS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:45:52.975993+00:00
-- url     : https://prove2.me/theorems/df864514-ed2a-492a-b028-6ebeb82f4db2
-- title:
--   $\max_{x,y}S_y(x)$
-- statement:
--   For a family $(I_0,I_1,I_2)$ of gadgets for Max-$k$-Cut, this is the largest pattern value
--
--   $$\max_{x\in[k]^3}\ \max_{y\in[k]^k}\ S_y(x),$$
--
--   taken jointly over the colours $x$ of the primaries and the colours $y$ of the global vertices. It is the soundness numerator of Theorem 4.1.
--
--   The paper writes the maximum over $y\in Y_k$, a set of representatives of the colourings of the globals modulo permutations of the colours; Section 2 (p.5) notes that, since gadget values are invariant under permuting all colours, maxima of sums of gadget values over $x$ and $y\in Y_k$ equal those over all $y\in[k]^k$. The definition takes the maximum over all $y$.
--
--   **Formalization Note** A finite nonempty maximum (`Finset.sup'`) over pairs $(x,y)$; no set $Y_k$ is defined.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Theorem 4.1, p.7 (with Section 2, Gadgets, p.5, on Y_k)

import Mathlib
import Definitions.Def_Max3CutHard_Family
import Definitions.Def_Max3CutHard_Supplement_Sval

namespace Max3CutHard.Supplement

open Max3CutHard

/-- **`max_{x,y} S_y(x)`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Theorem 4.1, p.7:
"`ρ = max_{y∈Y_k} max_{x∈[k]^3} S_y(x) / Σ_{t∈Z3} C_t`", the numerator
written `max_{x,y} S_y(x)` in the theorem's `(c, s)` clause.

**Formalization Note.** The maximum is taken jointly over all `x : Fin 3 → Fin k` and **all**
`y : Fin k → Fin k` (a finite nonempty maximum, `Finset.sup'`). The paper restricts `y` to the
restricted growth strings `Y_k` and states (Section 2, p.5) that maxima of sums of gadget values
jointly over `x` and `y ∈ Y_k` equal those over all `y ∈ [k]^k`, "the normalisation is only a
computational saving"; no `Y_k` is defined. -/
noncomputable def maxS {k : ℕ} [NeZero k] (F : Family k) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    fun p : (Fin 3 → Fin k) × (Fin k → Fin k) => Sval F p.1 p.2

end Max3CutHard.Supplement


