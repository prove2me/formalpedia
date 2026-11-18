-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_CycleCheck
-- name    : RealPinwheel_FiveSixths_CycleCheck
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T03:02:35.908194+00:00
-- url     : https://prove2.me/theorems/1b3910da-2a4e-4208-a65b-7208f124dbd4
-- title:
--   Exact finite-window checker for periodic density boxes
-- statement:
--   For a nonempty cycle of $L$ task labels, form its infinite repetition and store the prefix execution counts through two copies. For each task, a positive rational density endpoint $p/q$ and a flag specify whether that endpoint is excluded.
--
--   The checker requires the mean inequality $pL\le qC$, where $C$ counts executions in one copy. For every starting position and residual window length $0\le m,r<L$, it also checks
--
--   $$pr<q(C(m,r)+1)$$
--
--   for an included endpoint, or the weak inequality for an excluded endpoint. Here $C(m,r)$ counts executions in the window. Every check uses natural-number arithmetic. This supports independent verification of the periodic words and their open or closed box faces.
--
--   **Formalization Note** This is an alternative finite-window implementation of the source's cyclic-gap checks. Soundness is a separate theorem; the validity predicate remains the independently published all-window predicate.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf, Section 3, proof of equation (2), printed p. 8 (PDF p. 9), and Section 4 certificate verification, printed pp. 9–11 (PDF pp. 10–12).

import Definitions.Def_RealPinwheel_FiveSixths_Instance

namespace RealPinwheel.FiveSixths

/-- Infinite repetition of a nonempty array of task labels. -/
def cycleSchedule {n : ℕ} (w : Array (Fin n)) (h : 0 < w.size) (t : ℕ) : Fin n :=
  w[t % w.size]'(Nat.mod_lt _ h)

/-- Prefix counts through two copies of the cycle. -/
def cyclePrefixes {n : ℕ} (w : Array (Fin n)) (h : 0 < w.size) (i : Fin n) : Array ℕ :=
  Array.ofFn fun t : Fin (2 * w.size + 1) =>
    Nat.count (fun s => cycleSchedule w h s = i) t.val

/-- Exact integer checks for a rational box of admissible periods. The flag
`strict i` excludes the reciprocal endpoint den(i)/num(i). -/
def cycleCheck {n : ℕ} (w : Array (Fin n))
    (num den : Fin n → ℕ) (strict : Fin n → Bool) : Bool :=
  if h : 0 < w.size then
    (List.finRange n).all fun i =>
      let p := cyclePrefixes w h i
      decide (0 < num i ∧ 0 < den i) &&
      decide (num i * w.size ≤ den i * p[w.size]'(by simp only [p, cyclePrefixes, Array.size_ofFn]; omega)) &&
      (List.finRange w.size).all fun m => (List.finRange w.size).all fun r =>
        if strict i then
          decide (num i * r.val ≤ den i *
            (p[m.val + r.val]'(by simp [p, cyclePrefixes]; omega) -
              p[m.val]'(by simp only [p, cyclePrefixes, Array.size_ofFn]; omega) + 1))
        else
          decide (num i * r.val < den i *
            (p[m.val + r.val]'(by simp [p, cyclePrefixes]; omega) -
              p[m.val]'(by simp only [p, cyclePrefixes, Array.size_ofFn]; omega) + 1))
  else false

end RealPinwheel.FiveSixths


