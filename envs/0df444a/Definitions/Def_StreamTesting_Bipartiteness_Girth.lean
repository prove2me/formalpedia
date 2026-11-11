-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Girth
-- name    : StreamTesting_Bipartiteness_Girth
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:55:33.313104+00:00
-- url     : https://prove2.me/theorems/f18d0f52-3890-4943-b641-fd027454322c
-- title:
--   Strict extended-girth lower bound
-- statement:
--   The predicate expressing $\operatorname{girth}(G)>a$ requires every simple cycle to have more than $a$ edges. A forest satisfies this for every finite real $a$, representing infinite forest girth.
--
--   The weak inequality uses the compatible published GreedyColoringLCA969 cycle-length predicate. Neither definition assigns zero girth to a forest.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §4.1 and Lemma 20, printed p.20 / PDF p.20.

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Strict lower bound on cycle lengths, representing a < extended girth. -/
def GirthGreater {V : Type*} (G : SimpleGraph V) (a : ℝ) : Prop :=
  ∀ v (p : G.Walk v v), p.IsCycle → a < (p.length : ℝ)

end StreamTesting.Bipartiteness


