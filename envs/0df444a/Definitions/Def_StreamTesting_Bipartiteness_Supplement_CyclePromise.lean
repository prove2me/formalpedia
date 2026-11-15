-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_CyclePromise
-- name    : StreamTesting_Bipartiteness_Supplement_CyclePromise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:56:23.191636+00:00
-- url     : https://prove2.me/theorems/7820a432-1d42-41dd-a745-2720795f8d0f
-- title:
--   All labeled inputs in the cycle distinguishing promise
-- statement:
--   The long-cycle case consists of every graph isomorphic to $C_n$. The short-cycle case consists of every graph isomorphic to the union of exactly $n/6$ copies of $C_6$.
--
--   $$\mathcal P_n=\{G:G\cong C_n\}\cup\{G:G\cong\bigsqcup_{a=1}^{n/6}C_6\}.$$
--
--   Theorem 11 uses sufficiently large $n$ divisible by six, so these are the full intended families on the same $n$ labels. No hidden labeling or special order is supplied to the tester.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Theorem 11 and preceding paragraph, printed/PDF p.15.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_CycleUnion

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

def IsLongCycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  Nonempty ((SimpleGraph.cycleGraph n) ≃g G)

def IsSixCycleUnion {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  Nonempty ((sixCycleUnion (n / 6)) ≃g G)

def CyclePromise {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  IsLongCycle G ∨ IsSixCycleUnion G

end StreamTesting.Bipartiteness.Supplement


