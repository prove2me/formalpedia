-- Prove2me | Definitions.Def_EuclidDiamStream_StreamAlg
-- name    : EuclidDiamStream_StreamAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:51.959219+00:00
-- url     : https://prove2.me/theorems/71a5cbee-4c91-46b5-a596-796abef2f651
-- title:
--   Randomized streaming algorithms with bounded randomness
-- statement:
--   A **randomized streaming algorithm** draws a public seed once, keeps an internal state that it updates on each stream element, and produces an output that is a function of the final state and the seed only. It has **bounded randomness complexity** when the seed comes from a finite set, whose distribution does not depend on the stream.
--
--   This definition adds the seed distribution to the published one-pass automaton `BoolCSPDel.TurnstileAlg`. That reference also supplies streams, frequency vectors $\mathrm{freq}(\sigma)$, and the **strict turnstile** model, in which every prefix of a stream has a nonnegative frequency vector. No diameter problem appears here, so any streaming lower bound in this model can reuse it.
--
--   **Formalization Note** The state type is arbitrary and not assumed finite. The transitions and the output are arbitrary functions. The seed type is a `Fintype` and its distribution an arbitrary `PMF`.
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.6 (§2) and footnote 6, p.7 footnote 7, p.13

import Mathlib
import Definitions.Def_BoolCSPDel_TurnstileAlg

namespace EuclidDiamStream

/-- A randomized streaming algorithm with **bounded randomness complexity** of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…) (§2, p.6; footnote 7,
p.7; p.13). The automaton part is the published `BoolCSPDel.TurnstileAlg`: a state updated on each update
`(p, b)`, with `b = true` for `Add(p)` and `b = false` for `Remove(p)`, and an output, `false` = 0 and `true` = 1,
that depends only on the final state and the seed. The seed `ρ : R` is drawn once from `μ`, is public, and is
not stored in the state. Streams, `freq(σ)` and the strict turnstile model (footnote 6, p.6) are
`BoolCSPDel.freq` and `BoolCSPDel.IsLegal`.

**Formalization Note.** The seed type `R` is finite, and `μ` is an arbitrary distribution on it. It is
fixed before any stream, so it does not depend on the stream length (pp.3, 13). The state type `W` is
arbitrary, not assumed finite, and the transitions and output are arbitrary functions. -/
structure StreamAlg (U R W : Type) [Fintype R] extends BoolCSPDel.TurnstileAlg U R W Bool where
  /-- The distribution of the public random seed. -/
  μ : PMF R

end EuclidDiamStream


