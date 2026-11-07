-- Prove2me | Definitions.Def_OnlineBinCover_Greedy
-- name    : OnlineBinCover_Greedy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:46:00.103769+00:00
-- url     : https://prove2.me/theorems/ebb67ede-9d0d-4221-b4cd-ab9985b5a115
-- title:
--   Greedy filling of slots in a fixed order
-- statement:
--   Let slots $1,\dots,b$ have demands $d_1,\dots,d_b$, taken in this order. Items arrive one at a time; each is added to the first slot whose load is still below its demand, so the filler advances as soon as a demand is met, and a slot of demand $0$ is met from the start. An item arriving when every demand is met changes no slot. The result is the vector of slot loads.
--
--   This is the greedy filling of Lemma B.5.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Lemma B.5, p.22 (PDF p.23)

import Mathlib

namespace OnlineBinCover

/-!
# Greedy filling of slots in a fixed order (Lemma B.5)

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), Lemma B.5, p.22 ("filling slots one at a time
in increasing demand order … using the items of S ∪ M in any order").

**Formalization Note.** There are `b` slots with demands `d : Fin b → ℝ`, listed in the order in
which they are filled. Each arriving item (given by its size) is added to the first slot whose
demand is not yet met (load strictly below demand); the filler thus advances as soon as a demand is
met, and a slot of demand `0` is met from the start. An item arriving when every demand is met is
placed elsewhere and changes no slot.
-/

open Finset

/-- One greedy step: add `w` to the first slot whose load is below its demand. -/
noncomputable def greedyStep {b : ℕ} (d : Fin b → ℝ) (ld : Fin b → ℝ) (w : ℝ) : Fin b → ℝ :=
  by classical exact
    let unmet := univ.filter (fun j => ld j < d j)
    if h : unmet.Nonempty then Function.update ld (unmet.min' h) (ld (unmet.min' h) + w) else ld

/-- The slot loads after greedily filling with the item sizes `ws` in order. -/
noncomputable def greedyLoads {b : ℕ} (d : Fin b → ℝ) (ws : List ℝ) : Fin b → ℝ :=
  ws.foldl (greedyStep d) (fun _ => 0)

end OnlineBinCover


