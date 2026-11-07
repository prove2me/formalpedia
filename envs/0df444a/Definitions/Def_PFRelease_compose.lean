-- Prove2me | Definitions.Def_PFRelease_compose
-- name    : PFRelease_compose
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:44.631611+00:00
-- url     : https://prove2.me/theorems/aeff989d-82d6-4d9c-bcd0-79b8b539553d
-- title:
--   The composition $M\circ\mathcal F$ of a release mechanism with a filter
-- statement:
--   Given a filter $\mathcal F$ and a release mechanism $M$, the composition $M\circ\mathcal F$ runs the filter on $s$ and then $M$ on the filtered dataset, with independent randomness. If the filter nulls exactly $I$ with probability $\mathcal F_s(I)$, the law of the output is
--   $$
--   (M\circ\mathcal F)(s)=\sum_{I\subseteq[n]}\mathcal F_s(I)\,M(s^{I\to\perp}).
--   $$
--   PFR is such a composition (Definition 4.2), and PFR with element–block filtering is $M\circ\mathcal F_{b,t,\kappa,\sigma,\sigma'}(F_{2\tau}(\varphi))$.
--
--   **Formalization Note** The mixture is a finite sum of measures; it needs no measurability of $M$ in its input.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Definition 4.2, p.11 (PDF p.13), and §4.2, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_PFRelease_Dataset

open MeasureTheory

namespace PFRelease

/-- The composition `M ∘ F` of a release mechanism with a filter (Shenfeld, Tsfadia, Ligett,
arXiv:2610.40654, held version sha256 e1d516b3…, Definition 4.2, p.11, and the PFR composition,
p.13): run the filter on `s`, obtaining `s^{I→⊥}`, then run `M` on it with independent coins.

**Formalization Note** With `Fil s I` the probability that the filter nulls exactly `I` on input
`s`, the law of `M(F(s))` is the finite mixture `∑_I Fil s I • M(s^{I→⊥})`. This needs no
measurability of `M` in its input (no `Measure.bind`). -/
noncomputable def compose {X Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (M : (Fin n → Option X) → Measure Y) (Fil : (Fin n → Option X) → Finset (Fin n) → ENNReal)
    (s : Fin n → Option X) : Measure Y :=
  ∑ I : Finset (Fin n), Fil s I • M (nullOut s I)

end PFRelease


