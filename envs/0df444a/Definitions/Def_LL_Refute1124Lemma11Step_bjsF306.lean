-- Prove2me | Definitions.Def_LL_Refute1124Lemma11Step_bjsF306
-- name    : LL_Refute1124Lemma11Step_bjsF306
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-27T05:47:05.47683+00:00
-- url     : https://prove2.me/theorems/161b0ab3-211d-5a5d-8168-081542f7fde6
-- title:
--   The linear sieve functions $f_n$ of Bordignon, Johnston and Starichkova
-- statement:
--   bjsF306 n s is $f_n(s)$: $f_0=0$; $f_1(s)=(3-s)/s$ for $s\le3$ and $0$ for $s>3$; for $n\ge2$, $f_n(s)=\frac1s\int_{t>3}f_{n-1}(t-1)\,dt$ when $n$ is odd and $s\le3$, and $f_n(s)=\frac1s\int_{t>s}f_{n-1}(t-1)\,dt$ otherwise. The integrals are Lebesgue integrals over open half lines.

import Mathlib

namespace LL_Refute1124Lemma11Step

noncomputable section

open Finset Real

def bjsF306 : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun s => if s ≤ 3 then (3 - s) / s else 0
  | (n + 2) => fun s =>
      if Odd (n + 2) ∧ s ≤ 3 then (∫ t in Set.Ioi (3 : ℝ), bjsF306 (n + 1) (t - 1)) / s
      else (∫ t in Set.Ioi s, bjsF306 (n + 1) (t - 1)) / s

end

end LL_Refute1124Lemma11Step


