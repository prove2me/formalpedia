-- Prove2me | Definitions.Def_PrivLittlestone_prodProb
-- name    : PrivLittlestone_prodProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:03.957268+00:00
-- url     : https://prove2.me/theorems/a2be03c8-ccfb-4d01-a164-8728ee233e75
-- title:
--   Probability of an event under $m$ independent draws
-- statement:
--   For a finitely supported distribution $q$ on a finite set $s$ and $m \in \mathbb N$, the probability that $m$ independent draws $(h_1, \dots, h_m) \sim q^{\otimes m}$ satisfy a property $P$ is
--   $$
--   \sum_{(h_1, \dots, h_m) \in s^m} \Big(\prod_{i=1}^m q(h_i)\Big)\, \mathbf 1\{P(h_1, \dots, h_m)\}.
--   $$
--   It is used for the phase samples of the continual learner, which are drawn independently from $Q_S$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §4.1, p.6; (A2), p.7; Lemma 5.2, p.10

import Mathlib

namespace PrivLittlestone

open Classical in
/-- The probability, under `m` independent draws from a finitely supported distribution `q` on a
finite set `s`, that the sample `(h_1, …, h_m)` satisfies `P` (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
§4.1, p.6: "sample `h_1, …, h_m` independently from `Q_S`"; (A2), p.7; Lemma 5.2, p.10): the sum
over `s^m` of `∏_i q(h_i)` on the samples satisfying `P`. -/
noncomputable def prodProb {V : Type*} (s : Finset V) (q : V → ℝ) (m : ℕ)
    (P : (Fin m → V) → Prop) : ℝ :=
  ∑ h ∈ Fintype.piFinset (fun _ : Fin m => s), (∏ i, q (h i)) * (if P h then 1 else 0)

end PrivLittlestone


