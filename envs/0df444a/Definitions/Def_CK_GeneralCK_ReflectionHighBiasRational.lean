-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionHighBiasRational
-- name    : CK_GeneralCK_ReflectionHighBiasRational
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:59:38.309328+00:00
-- url     : https://prove2.me/theorems/5d9f379a-387a-4e32-a9b4-21c6720ebfdf
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionHighBiasRational` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionHighBiasRational` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionHighBiasRational` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionHighBiasRational (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionHighBiasRational.lean)

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

-- ===== source module GeneralCK.ReflectionHighBiasRational =====
section

namespace GeneralCK.Reflection.HighBiasRational

theorem case1_bound {a b c B q u : ℝ}
    (ha : (999/1000:ℝ)≤a) (hb : (1/2:ℝ)≤b) (hc : (1/2:ℝ)≤c)
    (hB : (69/100:ℝ)≤B) (hq0 : 0≤q) (hq1 : q≤1/2)
    (_hu0 : 0≤u) (hu1 : u≤4/125) :
    2*q^2/(a^3*b*(a+b)*(1+c)^2)+u/(a^3*b*(1+a)*(1+c)*B)<1/2 := by
  have h : 2*q^2/(a^3*b*(a+b)*(1+c)^2)+u/(a^3*b*(1+a)*(1+c)*B) ≤
      2*(1/2:ℝ)^2/((999/1000)^3*(1/2)*(999/1000+1/2)*(1+1/2)^2)+
      (4/125)/((999/1000)^3*(1/2)*(1+999/1000)*(1+1/2)*(69/100)) := by
    gcongr
  exact h.trans_lt (by norm_num)

theorem case2_bound {a b c B q u : ℝ}
    (ha : (999/1000:ℝ)≤a) (hb : (109/125:ℝ)≤b) (hc : (121/125:ℝ)≤c)
    (hB : (69/40:ℝ)≤B) (hq0 : 0≤q) (hq1 : q≤1)
    (_hu0 : 0≤u) (hu1 : u≤1) :
    2*q^2/(a^3*b*(a+b)*(1+c)^2)+u/(a^3*b*(1+a)*(1+c)*B)<1/2 := by
  have h : 2*q^2/(a^3*b*(a+b)*(1+c)^2)+u/(a^3*b*(1+a)*(1+c)*B) ≤
      2*(1:ℝ)^2/((999/1000)^3*(109/125)*(999/1000+109/125)*(1+121/125)^2)+
      1/((999/1000)^3*(109/125)*(1+999/1000)*(1+121/125)*(69/40)) := by
    gcongr
  exact h.trans_lt (by norm_num)

end GeneralCK.Reflection.HighBiasRational

end


