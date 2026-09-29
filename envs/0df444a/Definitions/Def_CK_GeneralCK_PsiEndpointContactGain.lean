-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointContactGain
-- name    : CK_GeneralCK_PsiEndpointContactGain
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T02:35:47.997694+00:00
-- url     : https://prove2.me/theorems/06be059f-2544-48a3-9fa5-f5ea90e99907
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointContactGain` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointContactGain` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointContactGain` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointContactGain (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointContactGain.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointContact
import Definitions.Def_CK_GeneralCK_PsiEndpointLogCurvature
import Definitions.Def_CK_GeneralCK_PsiRetainedChildBridge_v2

-- ===== source module GeneralCK.PsiEndpointContactGain =====
section

/-!
# The endpoint contact value has a logarithmic entropy-imbalance gain

This module compares actual, uniquely constructed contacts. It proves a
lower bound for the contact value itself; transferring that value to the
cost of an arbitrary finite law still requires the global supporting plane.
-/

namespace GeneralCK.PsiEndpointContact.Contact
open Set PsiEndpointLogGain PsiSignedSplit

noncomputable def value {d e f : ℝ} (c : Contact d e f) : ℝ :=
  c.mass * interiorCost c.left (1 - c.right)

theorem difference_pos {d e f : ℝ} (c : Contact d e f) : 0 < d := by
  have hp : 0 < c.mass * (1 - c.left - c.right) :=
    mul_pos c.mass_pos (by linarith [c.left_lt_half, c.right_lt_half])
  linarith [c.difference_eq]

/-- Exact entropy-coordinate expression for the contact value. -/
theorem value_eq_Q {d e f : ℝ} (c : Contact d e f) :
    c.value = d / 2 * (Q (e / c.mass) + Q (f / c.mass)) := by
  have h : c.value = c.mass * (1 - c.left - c.right) * (J c.left + J c.right) / 2 := by
    unfold value interiorCost
    rw [J_complement]
    ring
  rw [← c.difference_eq] at h
  simpa only [Q, ← c.left_eq_inverse, ← c.right_eq_inverse, div_mul_eq_mul_div] using h

theorem equal_coordinate_eq {d E : ℝ} (c : Contact d E E) : c.left = c.right := by
  rw [c.left_eq_inverse, c.right_eq_inverse]

/-- The equal-entropy endpoint contact is the ordinary radial contact. -/
theorem equal_radialContact {d E : ℝ} (c : Contact d E E) :
    radialContact d E = c.left := by
  apply radialContact_eq_of_equation c.difference_pos c.entropy_left_pos
    c.left_pos c.left_lt_half
  calc
    d * H c.left = (c.mass * (1 - c.left - c.right)) * H c.left :=
      congrArg (fun x => x * H c.left) c.difference_eq
    _ = (c.mass * H c.left) * (1 - 2 * c.left) := by
      rw [← c.equal_coordinate_eq]
      ring
    _ = E * (1 - 2 * c.left) :=
      congrArg (fun x => x * (1 - 2 * c.left)) c.entropy_left_eq.symm

theorem F_eq_equal_Q {d E : ℝ} (c : Contact d E E) :
    F d E = d * Q (E / c.mass) := by
  rw [F, if_neg c.difference_pos.ne', c.equal_radialContact]
  rw [Q, ← c.left_eq_inverse]

theorem exists_equal_contact {d e f : ℝ} (c : Contact d e f) :
    Nonempty (Contact d ((e + f) / 2) ((e + f) / 2)) := by
  have he := c.entropy_left_pos
  have hf := c.entropy_right_pos
  have he1 : e ≤ 1 := ((le_max_left e f).trans c.mass_gt_max.le).trans c.mass_le_one
  have hf1 : f ≤ 1 := ((le_max_right e f).trans c.mass_gt_max.le).trans c.mass_le_one
  have hm := (massFunction_strictMonoOn he hf).monotoneOn
    c.mass_gt_max.le (show max e f ≤ (1 : ℝ) from max_le he1 hf1) c.mass_le_one
  rw [c.mass_root, massFunction_one] at hm
  exact exists_equal_entropy_contact he hf he1 hf1 c.difference_pos hm

/-- Comparing the masses turns the endpoint value into a bound involving
the two unequal entropy arguments at the equal-entropy mass. -/
theorem value_ge_equal_mass_Q {d e f : ℝ} (c : Contact d e f)
    (cbar : Contact d ((e + f) / 2) ((e + f) / 2))
    (hd : e + f ≤ d) :
    d / 2 * (Q (e / cbar.mass) + Q (f / cbar.mass)) ≤ c.value := by
  have he := c.entropy_left_pos
  have hf := c.entropy_right_pos
  have hm := c.equal_entropy_mass_le cbar hd
  have hdomain : max e f ≤ cbar.mass := by
    have hmax : max e f ≤ e + f := max_le (by linarith) (by linarith)
    exact hmax.trans (hd.trans cbar.difference_le_mass)
  obtain ⟨hebar, hfbar⟩ := entropy_ratios_mem he hf hdomain
  have heQ := Q_antitone (div_pos he c.mass_pos)
    (div_le_div_of_nonneg_left he.le cbar.mass_pos hm) hebar.2
  have hfQ := Q_antitone (div_pos hf c.mass_pos)
    (div_le_div_of_nonneg_left hf.le cbar.mass_pos hm) hfbar.2
  rw [c.value_eq_Q]
  exact mul_le_mul_of_nonneg_left (add_le_add heQ hfQ) (by linarith [c.difference_pos])

/-- The ratio-eight endpoint value inequality, for every strictly positive
entropy split and with no common child-entropy-cap assumption. -/
theorem value_logarithmic_gain {d e f : ℝ} (c : Contact d e f)
    (hd : 8 * ((e + f) / 2) ≤ d) :
    F d ((e + f) / 2) + d / (2 * Real.log 2) * barrier ((e - f) / (e + f)) ≤ c.value := by
  let E := (e + f) / 2
  let t := (e - f) / (e + f)
  have he := c.entropy_left_pos
  have hf := c.entropy_right_pos
  have hE : 0 < E := by dsimp [E]; linarith
  obtain ⟨cbar⟩ := c.exists_equal_contact
  have hbar : 0 < E / cbar.mass := div_pos hE cbar.mass_pos
  have hbarcap : E / cbar.mass ≤ 1 / 8 := by
    apply (div_le_iff₀ cbar.mass_pos).2
    have hm := cbar.difference_le_mass
    dsimp [E]
    linarith
  obtain ⟨ht, het, hft⟩ := PsiRetainedChildBridge.positive_entropy_split he hf
  have hplus : (E / cbar.mass) * (1 + t) = e / cbar.mass := by
    calc
      _ = (E * (1 + t)) / cbar.mass := by ring
      _ = e / cbar.mass := congrArg (fun x => x / cbar.mass) het
  have hminus : (E / cbar.mass) * (1 - t) = f / cbar.mass := by
    calc
      _ = (E * (1 - t)) / cbar.mass := by ring
      _ = f / cbar.mass := congrArg (fun x => x / cbar.mass) hft
  have hgain := Q_split_gain hbar hbarcap ht
  change Q (E / cbar.mass) + barrier t / (2 * Real.log 2) ≤
    (Q ((E / cbar.mass) * (1 + t)) + Q ((E / cbar.mass) * (1 - t))) / 2 at hgain
  rw [hplus, hminus] at hgain
  have hmul := mul_le_mul_of_nonneg_left hgain c.difference_pos.le
  have hlast := c.value_ge_equal_mass_Q cbar (by linarith)
  have hbound : F d E + d / (2 * Real.log 2) * barrier t ≤
      d / 2 * (Q (e / cbar.mass) + Q (f / cbar.mass)) := by
    rw [cbar.F_eq_equal_Q]
    convert! hmul using 1 <;> ring
  exact hbound.trans hlast

#print axioms value_eq_Q
#print axioms equal_radialContact
#print axioms F_eq_equal_Q
#print axioms exists_equal_contact
#print axioms value_ge_equal_mass_Q
#print axioms value_logarithmic_gain

end GeneralCK.PsiEndpointContact.Contact

end


