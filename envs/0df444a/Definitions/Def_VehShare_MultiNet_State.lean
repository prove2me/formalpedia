-- Prove2me | Definitions.Def_VehShare_MultiNet_State
-- name    : VehShare_MultiNet_State
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:36:40.054536+00:00
-- url     : https://prove2.me/theorems/3ea34023-0142-46c0-83f6-8fb7d988632d
-- title:
--   States of the system with $K$ vehicles
-- statement:
--   A **state** $x$ with $K$ vehicles assigns to every slot (location or transit stage) a number of vehicles, $K$ in total:
--
--   $$
--   S=\Big\{x:\text{slots}\to\mathbb N\ :\ \sum_a x_a=K\Big\}.
--   $$
--
--   The state space is finite.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, footnote 1, p. 4; §2, p. 4

import Mathlib
import Definitions.Def_VehShare_MultiNet_Slot

namespace VehShare.MultiNet

/-- **States of the system with `K` vehicles.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), footnote 1, p. 4, and §2 p. 4 ("a network consisting of `N` locations and `K` vehicles").

A state assigns to each slot (location or transit stage) a number of vehicles, `K` in total. The
state space is finite (instance below). -/
abbrev State (P : Instance) (K : ℕ) : Type := {z : Slot P → ℕ // ∑ a, z a = K}

noncomputable instance (P : Instance) (K : ℕ) : Fintype (State P K) :=
  Fintype.ofInjective
    (fun z a => (⟨z.1 a, Nat.lt_succ_of_le ((Finset.single_le_sum (f := z.1) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ a)).trans_eq z.2)⟩ :
        Fin (K + 1)))
    (by
      intro z w h
      apply Subtype.ext
      funext a
      have := congrFun h a
      simpa [Fin.ext_iff] using this)

end VehShare.MultiNet


