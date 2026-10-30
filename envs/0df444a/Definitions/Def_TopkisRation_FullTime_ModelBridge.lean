-- Prove2me | Definitions.Def_TopkisRation_FullTime_ModelBridge
-- name    : TopkisRation_FullTime_ModelBridge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:39:13.206652+00:00
-- url     : https://prove2.me/theorems/24cdf3b6-795b-4039-9f0f-0f86861b644c
-- title:
--   Fieldwise bridge between the canonical single-procurement models
-- statement:
--   The two published representations of the single-procurement inventory model use identical data: a finite horizon $k$, backlog factors $a_s$, ordered penalty vectors $p_s$, holding costs $h_s$, salvage costs $v_1,v_2$, an ordering cost $c$, and interval demand laws $\mu_s$. This adapter sends a TimeMono model $M$ to a Levels model by copying every field:
--
--   $$
--   (k,a,p,h,v_1,v_2,c,\mu)\longmapsto(k,a,p,h,v_1,v_2,c,\mu).
--   $$
--
--   It also transports the standing assumptions (A)–(C), nonnegative backlog factors, and nonnegative probability demand laws with finite coordinate means, field by field. It supplies no value function, derivative comparison, optimality assertion, or threshold order. Each model's value functions continue to be computed by its published recursion (1).
--
--   This constructor interface permits reuse of the Levels regularity and policy results alongside the TimeMono marginal comparisons without redeclaring either model. Identities between their recursively computed values remain ordinary proof obligations.
--
--   **Formalization Note.** The only accompanying theorem is the immediate structural transport of the Standing fields; there is no substantive inventory theorem in this definition file.
-- source:
--   Topkis, Management Science 15(3) (1968), DOI 10.1287/mnsc.15.3.160, §1 model and (A)–(C), pp. 162–163 (PDF 4–5); representation adapter for the two canonical published model definitions

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model
import Definitions.Def_TopkisRation_TimeMono_Model

set_option autoImplicit false

namespace TopkisRation.FullTime

/-- Identity on the data of the two published copies of the model in §1, pp. 162–163.
No value functions, optimality properties, or derivative inequalities are supplied. -/
def toLevels {n : ℕ} (M : TopkisRation.TimeMono.Model n) : TopkisRation.Levels.Model n where
  k := M.k
  a := M.a
  p := M.p
  h := M.h
  v₁ := M.v₁
  v₂ := M.v₂
  c := M.c
  μ := M.μ

/-- The standing assumptions are copied fieldwise, without strengthening them. -/
theorem toLevelsStanding {n : ℕ} (M : TopkisRation.TimeMono.Model n) (hM : M.Standing) :
    (toLevels M).Standing := {
  a_nonneg := hM.a_nonneg
  h_convex := hM.h_convex
  h_cont := hM.h_cont
  v₁_convex := hM.v₁_convex
  v₁_cont := hM.v₁_cont
  v₂_convex := hM.v₂_convex
  v₂_cont := hM.v₂_cont
  v₂_slope := hM.v₂_slope
  p_nonneg := hM.p_nonneg
  p_mono := hM.p_mono
  μ_prob := hM.μ_prob
  μ_nonneg := hM.μ_nonneg
  μ_mean := hM.μ_mean
}

end TopkisRation.FullTime


