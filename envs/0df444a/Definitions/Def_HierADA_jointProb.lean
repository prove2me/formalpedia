-- Prove2me | Definitions.Def_HierADA_jointProb
-- name    : HierADA_jointProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:59:44.229196+00:00
-- url     : https://prove2.me/theorems/f7211ad7-3633-4981-b4d2-e34abd1d3920
-- title:
--   Probability over the sample blocks and the noise
-- statement:
--   For a set $E$ of pairs (sample blocks, noise realization), its probability when the blocks are independent i.i.d. samples from $P$ and the noise is drawn from the noise law independently of them is
--
--   $$
--   \Pr[E]=\sum_SP(S)\cdot\nu\{z:(S,z)\in E\}.
--   $$
--
--   All probabilistic statements about the hierarchical mechanism (Proposition 3.2, Theorem 3.7) are stated with this probability.
--
--   **Formalization Note** The block space is finite, so this is the product measure. The noise measure is applied to each section directly (outer measure), so a bound $\Pr[E^{c}]\le\xi$ gives a measurable set of probability at least $1-\xi$ inside $E$.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Proposition 3.2 (p.18) and Theorem 3.7 (p.24)

import Mathlib
import Definitions.Def_HierADA_noiseLaw
import Definitions.Def_HierADA_blocksMass

set_option autoImplicit false

open MeasureTheory

namespace HierADA

/-- **Probability over the samples and the noise** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, *Adaptive
Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version of
2026-11-03, sha256 f220ae51…), Proposition 3.2 (p.18) and Theorem 3.7 (p.24).

The probability of a set `E` of (blocks, noise) pairs when the blocks are independent i.i.d. samples
from `P` and the noise is drawn from `noiseLaw prm k` independently of them:
`∑_S P(S) · ν{z : (S, z) ∈ E}`.

**Formalization Note.** The block space is finite, so this is the product measure; the noise measure
is applied to each section directly (Lean's outer measure). Bounds of the form
`jointProb (Eᶜ) ≤ ξ` therefore give a measurable set of probability at least `1 − ξ` inside `E`. -/
noncomputable def jointProb {X : Type} (prm : Params) (k : ℕ) (P : PMF X) (n : Fin prm.p → ℕ)
    (E : Set (((j : Fin prm.p) → Fin (n j) → X) × Noise)) : ENNReal :=
  ∑' S, blocksMass P n S * noiseLaw prm k {z | (S, z) ∈ E}

end HierADA


