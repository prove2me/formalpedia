-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_Pattern132
-- name    : StreamTesting_Bipartiteness_Supplement_Pattern132
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:00:44.38055+00:00
-- url     : https://prove2.me/theorems/fbb6dd6f-c550-454a-b1eb-b3802a3ed33a
-- title:
--   Strict 132 patterns and freeness
-- statement:
--   A strict 132 copy in a real sequence $f$ consists of positions
--
--   $$i<j<k,\qquad f(i)<f(k)<f(j).$$
--
--   A sequence is 132-free when it contains no such triple. Repeated values are allowed throughout the input; equalities do not form a strict pattern. This is the property of Theorem 24 and Remark 25.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §1.2, printed/PDF p.5; §6 and Remark 25, printed/PDF p.29.

import Mathlib

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

def Copy132 {n : ℕ} (f : Fin n → ℝ) (i j k : Fin n) : Prop :=
  i < j ∧ j < k ∧ f i < f k ∧ f k < f j

def Free132 {n : ℕ} (f : Fin n → ℝ) : Prop :=
  ∀ i j k : Fin n, ¬ Copy132 f i j k

end StreamTesting.Bipartiteness.Supplement


