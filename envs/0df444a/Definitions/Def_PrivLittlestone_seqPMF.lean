-- Prove2me | Definitions.Def_PrivLittlestone_seqPMF
-- name    : PrivLittlestone_seqPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:28:40.517735+00:00
-- url     : https://prove2.me/theorems/47c67e33-3830-4e9f-9c14-277bcb261ad8
-- title:
--   Law of a sequential interaction with history-dependent kernels
-- statement:
--   For kernels $\kappa_i(\cdot \mid h)$ on an output space, indexed by the step $i$ and the history $h$ of the $i$ earlier outputs, the **law of the $n$-step interaction** draws $w_1 \sim \kappa_0(\cdot)$, $w_2 \sim \kappa_1(\cdot \mid w_1)$, and so on up to $w_n$. Transcript laws built from candidate-release and threshold kernels at every history are of this form.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), proof of Lemma B.3, p.23

import Mathlib

namespace PrivLittlestone

/-- The **law of an `n`-step sequential interaction** with history-dependent kernels (He–He,
*Private Online Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission
manuscript (sha256 21480556…c562), proof of Lemma B.3, p.23: transcript laws built from
candidate-release and threshold transition kernels at every history): step `i` draws its output
from `κ i h`, where `h` is the sequence of the `i` earlier outputs. -/
noncomputable def seqPMF {α : Type*} (κ : (i : ℕ) → (Fin i → α) → PMF α) : (n : ℕ) → PMF (Fin n → α)
  | 0 => PMF.pure Fin.elim0
  | n + 1 => (seqPMF κ n).bind fun h => (κ n h).map (Fin.snoc (α := fun _ => α) h)

end PrivLittlestone


