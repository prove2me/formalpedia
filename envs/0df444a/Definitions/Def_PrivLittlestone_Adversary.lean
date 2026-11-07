-- Prove2me | Definitions.Def_PrivLittlestone_Adversary
-- name    : PrivLittlestone_Adversary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:52.029588+00:00
-- url     : https://prove2.me/theorems/f72824f4-f35c-464d-bc0c-e7aee8a561cb
-- title:
--   Adaptive single-challenge adversary strategy
-- statement:
--   An **adaptive single-challenge adversary** supplies at each round $t$ a pair of records $(z^0_t, z^1_t)$, using its current view: the classifiers $g_1, \dots, g_t$ released so far, its own earlier pairs and its randomness.
--
--   **Formalization Note** The strategy is deterministic (the adversary's coins are fixed, as in the paper's proof of Lemma B.3). With the strategy fixed, the pairs in the view are a function of the released classifiers, so the view is determined by the classifier transcript; the inequality for each fixed coin integrates to every randomized adversary.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Definition 2.1, p.4

import Mathlib

namespace PrivLittlestone

/-- An **adaptive single-challenge adversary strategy** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
Definition 2.1, p.4): using its current view, it supplies at each round a pair `(z⁰_t, z¹_t)` of
records.

**Formalization Note** The strategy is deterministic (the adversary's coins are fixed, as in the
proof of Lemma B.3, p.23: "Fix the adversary's coins"; the per-coin inequality integrates to every
randomized adversary). Given the strategy, the record pairs in the view are a function of the
released classifiers, so the view is determined by the classifier transcript. At the 0-based
round `t` it sees `g_0, …, g_t`, including the current classifier. -/
abbrev Adversary (X : Type*) (T : ℕ) : Type _ :=
  (t : Fin T) → (Fin (t.val + 1) → X → Bool) → (X × Bool) × (X × Bool)

end PrivLittlestone


