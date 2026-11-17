-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_LinState
-- name    : IntroDelayAMDP_Supplement_LinState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:50:16.563131+00:00
-- url     : https://prove2.me/theorems/e572ed73-f14c-4427-8326-fc3bedadf24d
-- title:
--   State of Algorithms 3 and 5
-- statement:
--   The state of Algorithms 3 and 5 between processing steps: the running estimates $\hat Q_k(s,a)$ ($0$ before initialization), the policies $\pi_k$ played so far, the list of processed episodes in processing order, the regions of each processed episode and layer, and for each MGRR estimate started by episode $k$ at layer $h$: whether it is unfinished, its number of attempts $n$, the product $Z_n$ of Eq. (25), its truncation level $M_j$, the value $Y_{k,h}$ of Eq. (21) and the index $j$ of its region.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 3, p.19; Algorithm 5, p.59

import Mathlib
import Definitions.Def_IntroDelayAMDP_Supplement_Region

namespace IntroDelayAMDP.Supplement

/-- **The state of Algorithms 3 and 5 between processing steps** (Algorithm 3, printed p.19, PDF p.21;
Algorithm 5, printed p.59, PDF p.61, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)).
* `qhat k s a`: the running estimate `Q̂_k(s, a)` of the 0-based episode `k` (`0` before its line-7
  initialization);
* `pol k`: the policy `π_k` played in episode `k`;
* `processed`: the episodes processed so far, in processing order;
* `regs k h`: the regions `(C_j, p̂_j, Σ̂_j)_j` of layer `h` built when `k` was processed;
* for the MGRR estimate started by episode `k` at layer `h`: `active` (unfinished), `nAtt` (attempts made),
  `Z` (the product `Z_n` of Eq. (25)), `Mcap` (`M_j = ⌈m₀/p̂_j⌉`), `Y` (`Y_{k,h}` of Eq. (21)) and `reg` (the
  0-based index `j` of its region `C_j` in `regs k h`). -/
structure LinState (X A : Type) (d : ℕ) where
  qhat : ℕ → X → A → ℝ
  pol : ℕ → X → A → ℝ
  processed : List ℕ
  regs : ℕ → ℕ → List (Region d)
  active : ℕ → ℕ → Prop
  nAtt : ℕ → ℕ → ℕ
  Z : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ
  Mcap : ℕ → ℕ → ℕ
  Y : ℕ → ℕ → ℝ
  reg : ℕ → ℕ → ℕ

end IntroDelayAMDP.Supplement


