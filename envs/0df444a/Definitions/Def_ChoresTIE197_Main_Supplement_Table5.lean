-- Prove2me | Definitions.Def_ChoresTIE197_Main_Supplement_Table5
-- name    : ChoresTIE197_Main_Supplement_Table5
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:59:07.845181+00:00
-- url     : https://prove2.me/theorems/542ddc34-fa9a-46b4-b8f6-fd31dc80fde2
-- title:
--   Table 5 — ordinary and exaggerated reports and a single deviation
-- statement:
--   For $n\ge4$ agents take $m=n+7$ chores. The first eleven indices are $s_1,s_2,t_1,t_2,t_3,t_4,u_1,u_2,\ell_1,\ell_2,e$, and the remaining $n-4$ indices are huge chores. For a nonnegative real parameter $\varepsilon$, the core singleton costs are
--   $$
--   c_0=(2,2,3,3,3,3,4+\varepsilon,4,6,6,8),\qquad
--   c_1=(2,2,3,3,3,3,5,5,7,7,8).
--   $$
--   Every huge chore costs $11$ under both reports. Bundle costs use the published finite additive sum. At the single-deviation profile, any specified agent $i$ reports $c_1$ and all others report $c_0$.
--
--   These data define the concrete instance for Lemma 5.4. No MMS values, approximation property, packing or ordinary-cost bound is supplied by the definition. The lemma imposes $\varepsilon>0$ and the source's smallness inequality. Indices start at zero; at $n=4$ there are no huge chores. The functions are total for $n<4$, but that range is never used.
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Table 5 and §5.3, printed p.28, PDF p.28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib
import Definitions.Def_ChoresTIE197_Main_Setting

open scoped NNReal ENNReal

noncomputable section

namespace ChoresTIE197.Main.Supplement

/-- Table 5, printed/PDF p.28. Indices 0,...,10 are
s1,s2,t1,t2,t3,t4,u1,u2,ℓ1,ℓ2,e; later indices are huge chores.
For n ≥ 4 there are exactly eleven core chores and n - 4 huge chores. -/
def ordinary (n : ℕ) (ε : ℝ≥0) : Fin (n + 7) → ℝ≥0 := fun e =>
  match e.val with
  | 0 | 1 => 2
  | 2 | 3 | 4 | 5 => 3
  | 6 => 4 + ε
  | 7 => 4
  | 8 | 9 => 6
  | 10 => 8
  | _ => 11

/-- Table 5's exaggerated row. No MMS value or packing property is assumed. -/
def exaggerated (n : ℕ) : Fin (n + 7) → ℝ≥0 := fun e =>
  match e.val with
  | 0 | 1 => 2
  | 2 | 3 | 4 | 5 => 3
  | 6 | 7 => 5
  | 8 | 9 => 7
  | 10 => 8
  | _ => 11

/-- Any named agent reports c1, with every other agent reporting c0. -/
def singleReport (n : ℕ) (ε : ℝ≥0) (i : Fin n) : Profile n (n + 7) :=
  Function.update (fun _ => ordinary n ε) i (exaggerated n)

end ChoresTIE197.Main.Supplement


