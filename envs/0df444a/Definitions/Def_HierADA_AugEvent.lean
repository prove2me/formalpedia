-- Prove2me | Definitions.Def_HierADA_AugEvent
-- name    : HierADA_AugEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:29.995644+00:00
-- url     : https://prove2.me/theorems/04f9822a-ce0f-4a0d-87a3-f9a876e833ad
-- title:
--   Entries of the augmented transcript
-- statement:
--   An entry of the **augmented transcript** of the hierarchical mechanism is one of:
--
--   1. the outcome $q\in\{-1,0,+1\}$ of a private comparison on an edge;
--   2. a released answer, recorded by its index $m$ on the grid of spacing $\tau/64$ (the released value is $m\tau/64$);
--   3. a marker that the auxiliary mechanism reached a correction limit and stopped.
--
--   The paper lets the transcript "record all internal comparison outcomes together with the rounded answers"; this transcript is the output whose privacy Theorem 3.7 establishes.
--
--   **Formalization Note** Lists of entries carry the discrete σ-algebra; the type is countable, so every event is measurable.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Section 3.2, p.18

import Mathlib

set_option autoImplicit false

namespace HierADA

/-- **Entries of the augmented transcript** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, *Adaptive
Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version of
2026-11-03, sha256 f220ae51…), Section 3.2, p.18: "let T record all internal comparison outcomes
together with the rounded answers".

An entry is a comparison outcome `q ∈ {−1, 0, +1}` on an edge, a released answer, recorded by its
index `m` on the grid of spacing `τ/64` (the released value is `m·τ/64`), or the marker that the
auxiliary mechanism reached a correction limit and stopped.

**Formalization Note.** Lists of entries carry the discrete σ-algebra (every set is measurable);
the type is countable, so this is the σ-algebra of a finite-valued transcript. -/
inductive AugEvent
  /-- outcome `q` of `Compare` on (0-based) edge `edge` -/
  | compare (edge : ℕ) (q : ℤ)
  /-- a released answer `m · τ/64` -/
  | answer (m : ℤ)
  /-- the auxiliary mechanism reached a correction limit and stopped -/
  | halt
  deriving DecidableEq

instance : MeasurableSpace (List AugEvent) := ⊤

instance : MeasurableSingletonClass (List AugEvent) := ⟨fun _ => trivial⟩

end HierADA


