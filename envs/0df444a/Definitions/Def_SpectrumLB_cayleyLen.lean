-- Prove2me | Definitions.Def_SpectrumLB_cayleyLen
-- name    : SpectrumLB_cayleyLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:21.777983+00:00
-- url     : https://prove2.me/theorems/5fe6011f-d7d6-424e-a80e-cf3a1720b73f
-- title:
--   Definition 2.6 — Cayley length $|\pi|=n-\#\mathrm{cyc}(\pi)$
-- statement:
--   The Cayley length of $\pi\in S_n$ is the minimum number of transpositions whose product is $\pi$,
--
--   $$
--   |\pi|=n-\#\mathrm{cyc}(\pi),
--   $$
--
--   where $\#\mathrm{cyc}(\pi)$ counts all cycles including fixed points. Equivalently, $|\pi|$ is the size of the support of $\pi$ minus its number of non-trivial cycles. For a conjugacy class $\mu$, $|\mu|$ denotes the common Cayley length of its elements.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Definition 2.6, p. 12

import Mathlib

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Cayley length `|π| = n − #cyc(π)`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Definition 2.6, p. 12: "The Cayley length of a permutation is defined to be the minimum number of
transpositions (2-cycles) necessary to implement π, and is denoted by |π| := n − #cyc(π)."

**Formalization Note.** Computed as `|supp π| − (number of non-trivial cycles)`, which equals `n − #cyc(π)`
since each fixed point is a 1-cycle. -/
def cayleyLen {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  π.support.card - π.cycleType.card

end SpectrumLB


