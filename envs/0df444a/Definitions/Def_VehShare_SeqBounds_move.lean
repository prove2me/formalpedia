-- Prove2me | Definitions.Def_VehShare_SeqBounds_move
-- name    : VehShare_SeqBounds_move
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:35:54.177539+00:00
-- url     : https://prove2.me/theorems/ce3ef482-2712-4b10-b11e-888d90e29e22
-- title:
--   Moving one vehicle between slots
-- statement:
--   For a state $x$ and slots $a,b$, $\mathrm{move}(x,a,b)$ is the state obtained by moving one vehicle from $a$ to $b$, when $a$ holds a vehicle; when $a$ is empty it is $x$ itself. These are the transitions of the closed queueing network.
--
--   **Formalization Note** The convention for an empty slot $a$ is never used with a positive rate.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, §2, pp. 4–5 (unnumbered)

import Mathlib
import Definitions.Def_VehShare_SeqBounds_State

namespace VehShare.SeqBounds

/-- **Moving one vehicle from slot `a` to slot `b`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), §2 pp. 4–5 (unnumbered; the transitions of the closed queueing network).

If slot `a` holds a vehicle, `move z a b` is `z` with one vehicle less at `a` and one more at `b`;
otherwise it is `z` (never used with a positive rate: every rate of a move out of an empty slot is 0). -/
def move {P : Instance} {K : ℕ} (z : State P K) (a b : Slot P) : State P K :=
  if h : 1 ≤ z.1 a then
    ⟨fun x => z.1 x - (if x = a then 1 else 0) + (if x = b then 1 else 0), by
      have h1 : ∀ x, (z.1 x - (if x = a then 1 else 0)) + (if x = a then 1 else 0) = z.1 x := by
        intro x
        by_cases hx : x = a
        · subst hx; simp; omega
        · simp [hx]
      have h2 : ∑ x, (z.1 x - (if x = a then 1 else 0)) + 1 = K := by
        have h3 := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x (_ : x ∈ Finset.univ) => h1 x)
        rw [Finset.sum_add_distrib, z.2] at h3
        simpa using h3
      rw [Finset.sum_add_distrib]
      simpa using h2⟩
  else z

end VehShare.SeqBounds


