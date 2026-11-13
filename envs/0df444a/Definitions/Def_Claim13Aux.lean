-- Prove2me | Definitions.Def_Claim13Aux
-- name    : Claim13Aux
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T10:58:17.603541+00:00
-- url     : https://prove2.me/theorems/ed0a2cc7-58ff-412f-a2fb-bb7ac8a5e24c
-- title:
--   Claim 13 bookkeeping — arc cut counts and the two induction-step configurations Ctx13 and KD
-- statement:
--   Auxiliary definitions for the induction in the proof of Claim 13 of Chen, Pylyavskyy, Tan, *Paths and Intersections: Repelling Pairs*, arXiv:2607.02883 (version of October 23, 2026), p.12. All objects live in the namespace `RepellingPairs.Claim13Aux` and talk about a perfect matching `C` on the `n` boundary points `Fin n`.
--
--   - `cr C S` is the number of points of the set `S` whose partner under `C` lies outside `S`: the number of chords of `C` leaving `S`. For an arc `S` this is the distance `dist_C` of the corresponding cut.
--   - `ar n s m` is the arc of `m` consecutive points of `Fin n` starting at `s`, wrapping around past `n - 1`.
--   - `oa u v` is the set of points strictly inside the clockwise open arc from `u` to `v`.
--   - `Ctx13 C C' x y s m e` collects the standing assumptions of the induction step: `x, y` is a good pair of minimal segment count, the arc `ar n s m` contains `x` and `C'(x)` but not `y` or `C(x)`, the cut counts satisfy `cr C' ≤ cr C` on every arc (this is `C ≻ C'`), and `e` is an endpoint of the arc, different from `x` and `C'(x)`, lying in the gap between `C(x)` and `y`, with `C(e)` inside the arc and `C'(e)` outside it.
--   - `KD C C' e u v k` records the paper's open arc `(u, v)` between `e` and `C(e)` containing `C'(e)`, and the point `k` outside it whose `C`-partner is inside and whose `C'`-partner is outside.
--
--   **Formalization note.** The paper treats these configurations in prose ("the chord count ... gives a point k"); the structures name each fact so that the three cases of the final step can be stated and proved separately.
-- source:
--   Chen, Y., Pylyavskyy, P., Tan, Z., Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), https://arxiv.org/abs/2607.02883, p. 12, proof of Claim 13; auxiliary notions (cut counts of arcs, the induction-step configuration)

import Mathlib
import Definitions.Def_RepellingPairs_CyclicallyOrdered
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair

set_option autoImplicit false

namespace RepellingPairs.Claim13Aux

variable {n : ℕ}

open Classical in
/-- The number of points of `S` whose partner under the perfect matching `C` is outside `S`: the number of
chords of `C` leaving `S`. -/
noncomputable def cr (C : PerfectMatching n) (S : Fin n → Prop) : ℕ :=
  (Finset.univ.filter fun a => S a ∧ ¬ S (C.partner a)).card

/-- The arc of `m` consecutive points of `Fin n` starting at `s` (`s ≤ n`), wrapping around past `n - 1`. -/
def ar (n s m : ℕ) (a : Fin n) : Prop :=
  (s ≤ a.val ∧ a.val < s + m) ∨ (a.val < s ∧ a.val + n < s + m)

/-- `a` lies strictly inside the clockwise open arc from `u` to `v`. -/
def oa (u v a : Fin n) : Prop :=
  (u.val < v.val ∧ u.val < a.val ∧ a.val < v.val) ∨ (v.val < u.val ∧ (u.val < a.val ∨ a.val < v.val))

/-- The setting of the induction in the proof of Claim 13 (p.12): `C ≻ C'` has been normalised so that
`x, y` is a good pair of minimal segment count, `ar n s m` is an arc containing `x` and `C'(x)` but neither
`y` nor `C(x)`, whose chord cut count under `C'` is at most that under `C` for every arc (`hdom`), and `e` is
an endpoint of the arc with `e ≠ x`, `e ≠ C'(x)`, lying in the gap `C(x) .. y`, such that `C(e)` is inside
the arc and `C'(e)` is outside it. -/
structure Ctx13 (C C' : PerfectMatching n) (x y : Fin n) (s m : ℕ) (e : Fin n) : Prop where
  hgood : IsGoodPair C C' x y
  hmin : ∀ x₂ y₂, IsGoodPair C C' x₂ y₂ → segmentCount C x y ≤ segmentCount C x₂ y₂
  hdom : ∀ s m, s ≤ n → m < n → cr C' (ar n s m) ≤ cr C (ar n s m)
  hs : s < n
  hm0 : 0 < m
  hmn : m < n
  hx : ar n s m x
  hc'x : ar n s m (C'.partner x)
  hy : ¬ ar n s m y
  hcx : ¬ ar n s m (C.partner x)
  hend : e.val = s ∨ e.val = s + m - 1 ∨ e.val + n = s + m - 1
  hxe : e ≠ x
  hc'xe : e ≠ C'.partner x
  hgap : CyclicallyOrdered (C.partner x) x e y ∨ CyclicallyOrdered (C.partner x) y e x
  hCe : ar n s m (C.partner e)
  hC'e : ¬ ar n s m (C'.partner e)

/-- The choice of the open arc `(u, v)` bounded by `e` and `C(e)` that excludes `e`, `C(e)` and contains
`C'(e)`, together with a point `k` outside it whose partner under `C` is inside and under `C'` outside. -/
structure KD (C C' : PerfectMatching n) (e u v k : Fin n) : Prop where
  huv : u ≠ v
  huv' : (u = e ∧ v = C.partner e) ∨ (u = C.partner e ∧ v = e)
  hTe : ¬ oa u v e
  hTce : ¬ oa u v (C.partner e)
  hTc'e : oa u v (C'.partner e)
  hk1 : ¬ oa u v k
  hk2 : oa u v (C.partner k)
  hk3 : ¬ oa u v (C'.partner k)

end RepellingPairs.Claim13Aux


