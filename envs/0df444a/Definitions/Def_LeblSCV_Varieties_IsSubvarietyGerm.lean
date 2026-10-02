-- Prove2me | Definitions.Def_LeblSCV_Varieties_IsSubvarietyGerm
-- name    : LeblSCV_Varieties_IsSubvarietyGerm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:12:42.755264+00:00
-- url     : https://prove2.me/theorems/b3e6fc2d-84fb-44d0-9f8b-4b636bcb6bc4
-- title:
--   Germ of a subvariety at $p$
-- statement:
--   Let $p \in \mathbb{C}^n$ and $Y \subset \mathbb{C}^n$. The germ $(Y, p)$ is a **germ of a subvariety** if it has a representative that is a subvariety of a neighborhood of $p$: there is an open set $W \ni p$ such that
--   $$Y \cap W \text{ is a subvariety of } W.$$
--
--   **Formalization Note.** Uses `IsSubvariety` (Definition 6.5.1). The germ is represented by the set $Y$ itself; only $Y \cap W$ matters.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), pp. 183–186 (germs of subvarieties, §6.5), with Definition 6.1.3, p. 168

import Mathlib
import Definitions.Def_LeblSCV_Varieties_IsSubvariety

namespace LeblSCV.Varieties

/-- Lebl, §6.5 (germs of subvarieties, with Definition 6.1.3): the germ `(Y, p)` is a **germ of a
subvariety** if for some open neighborhood `W` of `p` the representative `Y ∩ W` is a subvariety
of `W` (Definition 6.5.1). -/
def IsSubvarietyGerm {n : ℕ} (p : Fin n → ℂ) (Y : Set (Fin n → ℂ)) : Prop :=
  ∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧ IsSubvariety W (Y ∩ W)

end LeblSCV.Varieties


