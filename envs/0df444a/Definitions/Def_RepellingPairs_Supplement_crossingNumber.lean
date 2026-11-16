-- Prove2me | Definitions.Def_RepellingPairs_Supplement_crossingNumber
-- name    : RepellingPairs_Supplement_crossingNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:58:18.719806+00:00
-- url     : https://prove2.me/theorems/38e0ad57-d7a4-4bd7-bcd4-eadc0e06f3cf
-- title:
--   Crossing number $\mathrm{cr}(\Phi)$ of a template
-- statement:
--   A **template** is a perfect matching $\Phi$ on boundary points $z_0,\dots,z_{n-1}$ of a disk, drawn as chords. Its **crossing number** $\mathrm{cr}(\Phi)$ is the number of unordered pairs of distinct chords $\{z,\Phi(z)\}$, $\{w,\Phi(w)\}$ that cross, i.e. whose four endpoints alternate around the circle.
--
--   In the paper, $\mathrm{cr}(\Phi)$ is the number of edges of every OS graph whose medial graph has template $\Phi$ (Lemma 33), so minimizing it is minimizing the number of edges.
--
--   **Formalization Note** Templates are the base mission's `PerfectMatching n`. Each chord is counted once through its smaller endpoint, and each pair of chords once through the order of those endpoints; crossing is the base mission's `Config.ChordsCross`.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §5.3.1, p.31 (PDF p.32)

import Mathlib
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching

set_option autoImplicit false

namespace RepellingPairs

namespace Supplement

/-- Decidability of `Config.ChordsCross`, used to count crossing pairs. -/
instance instDecidableChordsCross {n : ℕ} (x y z w : Fin n) : Decidable (Config.ChordsCross x y z w) := by
  unfold Config.ChordsCross; infer_instance

/-- The crossing number `cr(Φ)` of a template `Φ` (a perfect matching on the points `Fin n`, drawn as
chords): "the number of crossing pairs of chords". Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of
October 23, 2026), §5.3.1, p.31.

**Formalization Note.** Each chord `{x, Φ(x)}` is represented once, by its smaller endpoint `x < Φ(x)`, and
each unordered pair of distinct chords once, by `x < y` on those representatives; two chords cross when
`Config.ChordsCross` holds (four distinct endpoints alternating on the circle). -/
def crossingNumber {n : ℕ} (Φ : PerfectMatching n) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter (fun xy =>
    xy.1 < Φ.partner xy.1 ∧ xy.2 < Φ.partner xy.2 ∧ xy.1 < xy.2 ∧
      Config.ChordsCross xy.1 (Φ.partner xy.1) xy.2 (Φ.partner xy.2))).card

end Supplement

end RepellingPairs


