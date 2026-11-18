-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_FastCheck
-- name    : RealPinwheel_FiveSixths_FastCheck
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T03:18:48.490661+00:00
-- url     : https://prove2.me/theorems/38a21a43-159f-4217-812d-caeecfcf99fe
-- title:
--   Cycle checker with incremental prefix counts
-- statement:
--   This implementation of the exact finite-window checker computes the prefix execution counts in one left-to-right scan through two copies of a word. It applies the same integer mean and residual-window inequalities and preserves all strict endpoint flags.
--
--   $$C(t+1)=C(t)+\mathbf1_{\{S(t)=i\}},\qquad C(0)=0.$$
--
--   A separate equality theorem identifies this implementation with the original checker. Incremental counting makes checking the longer certificate words practical without changing their scheduling semantics.
-- source:
--   Fujiwara et al., STOC 2027 submission #885, Section 3, proof of equation (2), printed p. 8 (PDF p. 9), and Section 4 exact certificate checks, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Formalization implementation of finite prefix counts.

import Definitions.Def_RealPinwheel_FiveSixths_CycleCode
namespace RealPinwheel.FiveSixths

/-- Prefix counts computed in a single left-to-right pass. -/
def fastCyclePrefixes {n : ℕ} (w : Array (Fin n)) (h : 0 < w.size) (i : Fin n) : Array ℕ :=
  ((List.range (2 * w.size)).scanl
    (fun c t => c + if cycleSchedule w h t = i then 1 else 0) 0).toArray

def fastCycleCheck {n : ℕ} (w : Array (Fin n))
    (num den : Fin n → ℕ) (strict : Fin n → Bool) : Bool :=
  if h : 0 < w.size then
    (List.finRange n).all fun i =>
      let p := fastCyclePrefixes w h i
      decide (0 < num i ∧ 0 < den i) &&
      decide (num i * w.size ≤ den i * p[w.size]'(by simp [p, fastCyclePrefixes]; omega)) &&
      (List.finRange w.size).all fun m => (List.finRange w.size).all fun r =>
        if strict i then
          decide (num i * r.val ≤ den i *
            (p[m.val + r.val]'(by simp [p, fastCyclePrefixes]; omega) -
              p[m.val]'(by simp [p, fastCyclePrefixes]; omega) + 1))
        else
          decide (num i * r.val < den i *
            (p[m.val + r.val]'(by simp [p, fastCyclePrefixes]; omega) -
              p[m.val]'(by simp [p, fastCyclePrefixes]; omega) + 1))
  else false


def fastCodeCheck (n : ℕ) (hn : 0 < n) (c : CycleCode) : Bool :=
  fastCycleCheck (codeWord n hn c) (codeNum c) (codeDen c) (codeStrict c)

end RealPinwheel.FiveSixths


