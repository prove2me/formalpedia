-- Prove2me | Definitions.Def_BlockSSM_Tracker_transMonoid
-- name    : BlockSSM_Tracker_transMonoid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:06.223205+00:00
-- url     : https://prove2.me/theorems/9ee00f07-f06a-4994-ba9c-6a24d2c85b8d
-- title:
--   Transition monoid $M$
-- statement:
--   The **transition monoid** $M$ of a tracker is the set of restrictions $F_s|_V$ of its word maps to $V=\mathrm{aff}(R)$, under composition. Its identity is the restriction of the empty word, and $F_t|_V\circ F_s|_V=F_{st}|_V$, where $st$ reads $s$ first.
--
--   **Formalization Note** $M$ is built from the given tracker, not an arbitrary monoid of affine maps.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 5, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_BlockSSM_Tracker_wordRes

universe u

namespace BlockSSM

variable {G : Type u} {b : ℕ∞}

/-- **The transition monoid `M`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 5, p.3 (PDF p.4): "The restrictions of word maps to V
form a finite monoid M."

**Formalization Note.** The monoid of *this* tracker: the submonoid of `Function.End V` whose carrier
is exactly the set of restrictions `F_s|_V`. The identity is the empty word's restriction and
`F_t|_V * F_s|_V = F_{st}|_V`, with `st` the concatenation that reads `s` first. -/
def Tracker.transMonoid (T : Tracker G b) : Submonoid (Function.End T.hull) where
  carrier := Set.range T.wordRes
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro _ _ ⟨t, rfl⟩ ⟨s, rfl⟩
    refine ⟨s ++ t, ?_⟩
    funext x
    apply Subtype.ext
    exact List.foldl_append ..

/-- The element `F_s|_V` of the transition monoid. -/
def Tracker.wordElt (T : Tracker G b) (s : List G) : T.transMonoid :=
  ⟨T.wordRes s, s, rfl⟩

end BlockSSM


