-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.aa_hyps_force
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:24:44.146208+00:00
-- url     : https://prove2.me/submissions/1a4adac6-dca1-4306-a05e-6202c6fce7ff

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_eq_zero_of_degree_zero
import Theorems.Thm_AaronsonAmbainis_Level_variance_eq_zero_of_isEmpty


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f : Cube ι → ℝ} {d : ℕ} (hdeg : HasDegreeLE f d) (hv : 0 < variance f) :
    1 ≤ d ∧ Nonempty ι := by
  constructor
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [variance_eq_zero_of_degree_zero hdeg] at hv
      exact absurd hv (lt_irrefl 0)
    · exact hd
  · by_contra hne
    have : IsEmpty ι := not_nonempty_iff.mp hne
    rw [Level.variance_eq_zero_of_isEmpty f] at hv
    exact lt_irrefl 0 hv
end AaronsonAmbainis.Bridge
