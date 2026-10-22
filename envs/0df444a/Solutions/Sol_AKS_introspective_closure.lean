-- Prove2me | solution 1 for AKS.introspective_closure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:07:57.650898+00:00
-- url     : https://prove2.me/submissions/bfeda8b9-ecaf-4fef-a9bf-26da8f67edc4

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg
open AKS

open Polynomial in
theorem solution (p r : ℕ)
    (f g : Polynomial (ZMod p)) (m m' : ℕ)
    (hm : introspective p r f m) (hm' : introspective p r f m')
    (hgm : introspective p r g m) :
    introspective p r f (m * m') ∧ introspective p r (f * g) m := by
  unfold introspective at *
  constructor
  · have h1 : (X ^ r - 1 : Polynomial (ZMod p)) ∣ (f ^ m) ^ m' - (f.comp (X ^ m)) ^ m' :=
      dvd_trans hm (sub_dvd_pow_sub_pow _ _ _)
    have h2 : (X ^ r - 1 : Polynomial (ZMod p)) ∣ (f.comp (X ^ m)) ^ m' - f.comp (X ^ (m * m')) := by
      obtain ⟨c, hc⟩ := hm'
      have h3 : (f ^ m' - f.comp (X ^ m')).comp (X ^ m)
          = ((X ^ r - 1 : Polynomial (ZMod p)).comp (X ^ m)) * c.comp (X ^ m) := by
        rw [hc, mul_comp]
      have h4 : (X ^ r - 1 : Polynomial (ZMod p)) ∣ (X ^ r - 1 : Polynomial (ZMod p)).comp (X ^ m) := by
        have := sub_dvd_pow_sub_pow (X ^ r : Polynomial (ZMod p)) 1 m
        simpa [sub_comp, pow_comp, ← pow_mul, mul_comm] using this
      have h5 : (f ^ m' - f.comp (X ^ m')).comp (X ^ m)
          = (f.comp (X ^ m)) ^ m' - f.comp (X ^ (m * m')) := by
        rw [sub_comp, pow_comp, comp_assoc, X_pow_comp, ← pow_mul]
      rw [← h5, h3]
      exact dvd_mul_of_dvd_left h4 _
    have := dvd_add h1 h2
    rw [pow_mul]
    convert this using 1
    ring
  · have := dvd_add (dvd_mul_of_dvd_left hm (g ^ m)) (dvd_mul_of_dvd_right hgm (f.comp (X ^ m)))
    rw [mul_pow, mul_comp]
    convert this using 1
    ring
