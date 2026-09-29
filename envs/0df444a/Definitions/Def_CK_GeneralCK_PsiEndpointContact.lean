-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointContact
-- name    : CK_GeneralCK_PsiEndpointContact
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:50:48.577997+00:00
-- url     : https://prove2.me/theorems/87aaca49-e5d2-4730-8669-10e23471cad0
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointContact` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointContact` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointContact` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointContact (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointContact.lean)

import Definitions.Def_CK_GeneralCK_CorrectionBasics

-- ===== source module GeneralCK.PsiEndpointContact =====
section

/-!
# Existence and uniqueness of the strict cross-half endpoint contact

The contact mass function is strictly increasing on its entire closed domain.
This follows directly from monotonicity of the lower entropy inverse: a
larger mass decreases both inverse coordinates and increases the remaining
radius. No derivative at the half-entropy endpoint is needed.

These results construct the contact; they do not assert that its value is a
lower bound for the cost. The global supporting plane is a separate theorem.
-/

namespace GeneralCK.PsiEndpointContact
open Set

noncomputable def massFunction (e f p : ℝ) : ℝ :=
  p * (1 - entropyInverse (e / p) - entropyInverse (f / p))

theorem mass_pos {e f p : ℝ} (he : 0 < e) (hp : max e f ≤ p) : 0 < p :=
  he.trans_le ((le_max_left e f).trans hp)

theorem entropy_ratios_mem {e f p : ℝ} (he : 0 < e) (hf : 0 < f)
    (hp : max e f ≤ p) : e / p ∈ Ioc (0 : ℝ) 1 ∧ f / p ∈ Ioc (0 : ℝ) 1 := by
  have hp0 := mass_pos he hp
  exact ⟨⟨div_pos he hp0, (div_le_one hp0).2 ((le_max_left e f).trans hp)⟩,
    ⟨div_pos hf hp0, (div_le_one hp0).2 ((le_max_right e f).trans hp)⟩⟩

theorem entropy_ratios_strict {e f p : ℝ} (he : 0 < e) (hf : 0 < f)
    (hp : max e f < p) : e / p ∈ Ioo (0 : ℝ) 1 ∧ f / p ∈ Ioo (0 : ℝ) 1 := by
  have hp0 := mass_pos he hp.le
  exact ⟨⟨div_pos he hp0, (div_lt_one hp0).2 ((le_max_left e f).trans_lt hp)⟩,
    ⟨div_pos hf hp0, (div_lt_one hp0).2 ((le_max_right e f).trans_lt hp)⟩⟩

/-- Strict increase includes the closed lower endpoint, where either or both
inverse entropy coordinates may equal one half. -/
theorem massFunction_strictMonoOn {e f : ℝ} (he : 0 < e) (hf : 0 < f) :
    StrictMonoOn (massFunction e f) (Ici (max e f)) := by
  intro p hp r hr hpr
  have hp0 := mass_pos he hp
  have hr0 := mass_pos he hr
  obtain ⟨hep, hfp⟩ := entropy_ratios_mem he hf hp
  obtain ⟨her, hfr⟩ := entropy_ratios_strict he hf (hp.trans_lt hpr)
  have hepr : e / r ≤ e / p := div_le_div_of_nonneg_left he.le hp0 hpr.le
  have hfpr : f / r ≤ f / p := div_le_div_of_nonneg_left hf.le hp0 hpr.le
  have hu := entropyInverse_mono her.1.le hep.2 hepr
  have hv := entropyInverse_mono hfr.1.le hfp.2 hfpr
  have hur := entropyInverse_lt_half her.1.le her.2
  have hvr := entropyInverse_lt_half hfr.1.le hfr.2
  have hrad : 0 < 1 - entropyInverse (e / r) - entropyInverse (f / r) := by linarith
  unfold massFunction
  calc
    _ ≤ p * (1 - entropyInverse (e / r) - entropyInverse (f / r)) :=
      mul_le_mul_of_nonneg_left (by linarith) hp0.le
    _ < r * (1 - entropyInverse (e / r) - entropyInverse (f / r)) :=
      mul_lt_mul_of_pos_right hpr hrad

theorem massFunction_continuousOn {e f : ℝ} (he : 0 < e) (hf : 0 < f) :
    ContinuousOn (massFunction e f) (Ici (max e f)) := by
  have hediv : ContinuousOn (fun p : ℝ => e / p) (Ici (max e f)) :=
    continuousOn_const.div continuousOn_id (fun p hp => (mass_pos he hp).ne')
  have hfdiv : ContinuousOn (fun p : ℝ => f / p) (Ici (max e f)) :=
    continuousOn_const.div continuousOn_id (fun p hp => (mass_pos he hp).ne')
  have heu := entropyInverse_continuousOn.comp hediv (by
    intro p hp
    exact ⟨(entropy_ratios_mem he hf hp).1.1.le, (entropy_ratios_mem he hf hp).1.2⟩)
  have hfu := entropyInverse_continuousOn.comp hfdiv (by
    intro p hp
    exact ⟨(entropy_ratios_mem he hf hp).2.1.le, (entropy_ratios_mem he hf hp).2.2⟩)
  exact continuousOn_id.mul ((continuousOn_const.sub heu).sub hfu)

@[simp] theorem massFunction_one (e f : ℝ) :
    massFunction e f 1 = 1 - entropyInverse e - entropyInverse f := by
  simp [massFunction]

/-- The strict lower test and weak upper test give one and only one mass.
In particular the upper boundary `p=1` is allowed. -/
theorem existsUnique_mass {d e f : ℝ} (he : 0 < e) (hf : 0 < f)
    (he1 : e ≤ 1) (hf1 : f ≤ 1)
    (hlow : massFunction e f (max e f) < d)
    (hupp : d ≤ massFunction e f 1) :
    ∃! p : ℝ, p ∈ Ioc (max e f) 1 ∧ massFunction e f p = d := by
  have hp1 : max e f ≤ 1 := max_le he1 hf1
  have hc : ContinuousOn (massFunction e f) (Icc (max e f) 1) :=
    (massFunction_continuousOn he hf).mono (fun _ hp => hp.1)
  obtain ⟨p, hp, heq⟩ := intermediate_value_Icc hp1 hc ⟨hlow.le, hupp⟩
  have hpstrict : max e f < p := by
    apply lt_of_le_of_ne hp.1
    intro h
    rw [← h] at heq
    linarith
  refine ⟨p, ⟨⟨hpstrict, hp.2⟩, heq⟩, ?_⟩
  intro r hr
  exact (massFunction_strictMonoOn he hf).injOn hr.1.1.le hp.1 (hr.2.trans heq.symm)

/-- One inverse coordinate at the lower endpoint is exactly one half; the
other is nonnegative. This supplies a uniform endpoint threshold. -/
theorem lower_massFunction_le_half_max {e f : ℝ} (he : 0 < e) (hf : 0 < f) :
    massFunction e f (max e f) ≤ max e f / 2 := by
  have hp0 : 0 < max e f := he.trans_le (le_max_left e f)
  have hi : entropyInverse (1 : ℝ) = 1 / 2 := by
    simpa only [H_half] using entropyInverse_H_lower (v := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨hea, hfa⟩ := entropy_ratios_mem he hf (le_refl (max e f))
  have hue := (entropyInverse_spec hea.1.le hea.2).1
  have huf := (entropyInverse_spec hfa.1.le hfa.2).1
  rcases le_total e f with hef | hfe
  · rw [max_eq_right hef] at *
    unfold massFunction
    rw [div_self hf.ne', hi]
    nlinarith
  · rw [max_eq_left hfe] at *
    unfold massFunction
    rw [div_self he.ne', hi]
    nlinarith

theorem lower_massFunction_le_mean {e f : ℝ} (he : 0 < e) (hf : 0 < f) :
    massFunction e f (max e f) ≤ (e + f) / 2 := by
  have h := lower_massFunction_le_half_max he hf
  have hm : max e f ≤ e + f := max_le (by linarith) (by linarith)
  linarith

/-- Positive entropy caps bound inverse coordinates by either side of their
mean, without requiring the mean to lie on the lower entropy branch. -/
theorem inverse_le_mean_and_complement {a e : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (he : 0 ≤ e) (hecap : e ≤ H a) :
    entropyInverse e ≤ a ∧ entropyInverse e ≤ 1 - a := by
  have hm := entropyInverse_mono he (H_le_one a) hecap
  rw [entropyInverse_H ha.1 ha.2] at hm
  exact ⟨hm.trans (min_le_left _ _), hm.trans (min_le_right _ _)⟩

/-- Every feasible mean pair satisfies the upper endpoint contact test. -/
theorem feasible_upper_test {a b e f : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hecap : e ≤ H a) (hfcap : f ≤ H b) :
    b - a ≤ massFunction e f 1 := by
  have hu := (inverse_le_mean_and_complement ha he hecap).1
  have hv := (inverse_le_mean_and_complement hb hf hfcap).2
  rw [massFunction_one]
  linarith

/-- The analytic branch needs only `d>E` for existence; the stronger
`d>=5E` used by the logarithmic gain implies this immediately. -/
theorem existsUnique_mass_of_feasible {a b e f : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (he : 0 < e) (hf : 0 < f) (hecap : e ≤ H a) (hfcap : f ≤ H b)
    (hd : (e + f) / 2 < b - a) :
    ∃! p : ℝ, p ∈ Ioc (max e f) 1 ∧ massFunction e f p = b - a := by
  exact existsUnique_mass he hf (hecap.trans (H_le_one _)) (hfcap.trans (H_le_one _))
    ((lower_massFunction_le_mean he hf).trans_lt hd)
    (feasible_upper_test ha hb he.le hf.le hecap hfcap)

/-- A strict cross-half contact with all equations in bit units. This record
contains no claim about cost minimization or supporting planes. -/
structure Contact (d e f : ℝ) where
  mass : ℝ
  left : ℝ
  right : ℝ
  mass_pos : 0 < mass
  mass_le_one : mass ≤ 1
  left_pos : 0 < left
  left_lt_half : left < 1 / 2
  right_pos : 0 < right
  right_lt_half : right < 1 / 2
  difference_eq : d = mass * (1 - left - right)
  entropy_left_eq : e = mass * H left
  entropy_right_eq : f = mass * H right

/-- Turn the unique mass root into the actual strict contact coordinates. -/
theorem contact_of_mass {d e f p : ℝ} (he : 0 < e) (hf : 0 < f)
    (hp : p ∈ Ioc (max e f) 1) (heq : massFunction e f p = d) :
    Nonempty (Contact d e f) := by
  obtain ⟨her, hfr⟩ := entropy_ratios_strict he hf hp.1
  have hp0 := mass_pos he hp.1.le
  refine ⟨{
    mass := p
    left := entropyInverse (e / p)
    right := entropyInverse (f / p)
    mass_pos := hp0
    mass_le_one := hp.2
    left_pos := entropyInverse_pos her.1 her.2.le
    left_lt_half := entropyInverse_lt_half her.1.le her.2
    right_pos := entropyInverse_pos hfr.1 hfr.2.le
    right_lt_half := entropyInverse_lt_half hfr.1.le hfr.2
    difference_eq := heq.symm
    entropy_left_eq := ?_
    entropy_right_eq := ?_ }⟩
  · rw [(entropyInverse_spec her.1.le her.2.le).2.2]
    field_simp
  · rw [(entropyInverse_spec hfr.1.le hfr.2.le).2.2]
    field_simp

theorem exists_contact_of_feasible {a b e f : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (he : 0 < e) (hf : 0 < f) (hecap : e ≤ H a) (hfcap : f ≤ H b)
    (hd : (e + f) / 2 < b - a) : Nonempty (Contact (b - a) e f) := by
  obtain ⟨p, hp, _⟩ := existsUnique_mass_of_feasible ha hb he hf hecap hfcap hd
  exact contact_of_mass he hf hp.1 hp.2

theorem exists_contact_of_five_ratio {a b e f : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (he : 0 < e) (hf : 0 < f) (hecap : e ≤ H a) (hfcap : f ≤ H b)
    (hd : 5 * ((e + f) / 2) ≤ b - a) : Nonempty (Contact (b - a) e f) := by
  exact exists_contact_of_feasible ha hb he hf hecap hfcap (by linarith)

/-- Midpoint convexity of the lower entropy inverse, including both caps,
is an immediate consequence of entropy concavity and inverse monotonicity. -/
theorem inverse_midpoint_le {e f : ℝ} (he : e ∈ Icc (0 : ℝ) 1)
    (hf : f ∈ Icc (0 : ℝ) 1) :
    entropyInverse ((e + f) / 2) ≤ (entropyInverse e + entropyInverse f) / 2 := by
  obtain ⟨hu0, hu1, hue⟩ := entropyInverse_spec he.1 he.2
  obtain ⟨hv0, hv1, hvf⟩ := entropyInverse_spec hf.1 hf.2
  have hj := Real.strictConcave_binEntropy.concaveOn.2
    (show entropyInverse e ∈ Icc (0 : ℝ) 1 from ⟨hu0, by linarith⟩)
    (show entropyInverse f ∈ Icc (0 : ℝ) 1 from ⟨hv0, by linarith⟩)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hj
  have h := div_le_div_of_nonneg_right hj log_two_pos.le
  have hmiddle : (e + f) / 2 ≤ H ((entropyInverse e + entropyInverse f) / 2) := by
    have heq : (1 / 2 : ℝ) * entropyInverse e + (1 / 2) * entropyInverse f =
        (entropyInverse e + entropyInverse f) / 2 := by ring
    rw [heq] at h
    have hmiddle' : (H (entropyInverse e) + H (entropyInverse f)) / 2 ≤
        H ((entropyInverse e + entropyInverse f) / 2) := by
      unfold H
      convert! h using 1
      ring
    simpa only [hue, hvf] using hmiddle'
  have hm := entropyInverse_mono (show 0 ≤ (e + f) / 2 by linarith [he.1, hf.1])
    (H_le_one _) hmiddle
  rw [entropyInverse_H_lower (by linarith : 0 ≤ (entropyInverse e + entropyInverse f) / 2)
    (by linarith : (entropyInverse e + entropyInverse f) / 2 ≤ 1 / 2)] at hm
  exact hm

theorem exists_equal_entropy_contact {d e f : ℝ} (he : 0 < e) (hf : 0 < f)
    (he1 : e ≤ 1) (hf1 : f ≤ 1) (hd : 0 < d)
    (hupp : d ≤ 1 - entropyInverse e - entropyInverse f) :
    Nonempty (Contact d ((e + f) / 2) ((e + f) / 2)) := by
  let E := (e + f) / 2
  have hE : 0 < E := by dsimp [E]; linarith
  have hE1 : E ≤ 1 := by dsimp [E]; linarith
  have hi : entropyInverse (1 : ℝ) = 1 / 2 := by
    simpa only [H_half] using entropyInverse_H_lower (v := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hlo : massFunction E E (max E E) = 0 := by
    simp only [max_self, massFunction, div_self hE.ne', hi]
    ring
  have hm := inverse_midpoint_le ⟨he.le, he1⟩ ⟨hf.le, hf1⟩
  have hupper : d ≤ massFunction E E 1 := by
    rw [massFunction_one]
    dsimp [E]
    linarith
  obtain ⟨p, hp, _⟩ := existsUnique_mass hE hE hE1 hE1 (by rwa [hlo]) hupper
  exact contact_of_mass hE hE hp.1 hp.2

namespace Contact

theorem entropy_left_pos {d e f : ℝ} (c : Contact d e f) : 0 < e := by
  rw [c.entropy_left_eq]
  exact mul_pos c.mass_pos (H_pos c.left_pos (by linarith [c.left_lt_half]))

theorem entropy_right_pos {d e f : ℝ} (c : Contact d e f) : 0 < f := by
  rw [c.entropy_right_eq]
  exact mul_pos c.mass_pos (H_pos c.right_pos (by linarith [c.right_lt_half]))

theorem mass_gt_max {d e f : ℝ} (c : Contact d e f) : max e f < c.mass := by
  have hl : H c.left < 1 := by
    have h := H_strictMonoOn ⟨c.left_pos.le, c.left_lt_half.le⟩
      (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) by norm_num) c.left_lt_half
    simpa only [H_half] using h
  have hr : H c.right < 1 := by
    have h := H_strictMonoOn ⟨c.right_pos.le, c.right_lt_half.le⟩
      (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) by norm_num) c.right_lt_half
    simpa only [H_half] using h
  apply max_lt
  · have h := mul_lt_mul_of_pos_left hl c.mass_pos
    linarith [c.entropy_left_eq]
  · have h := mul_lt_mul_of_pos_left hr c.mass_pos
    linarith [c.entropy_right_eq]

theorem difference_le_mass {d e f : ℝ} (c : Contact d e f) : d ≤ c.mass := by
  have h := mul_le_mul_of_nonneg_left
    (show 1 - c.left - c.right ≤ 1 by linarith [c.left_pos, c.right_pos]) c.mass_pos.le
  linarith [c.difference_eq]

theorem left_eq_inverse {d e f : ℝ} (c : Contact d e f) :
    c.left = entropyInverse (e / c.mass) := by
  have hratio : e / c.mass = H c.left := by
    calc
      _ = (c.mass * H c.left) / c.mass := congrArg (fun x => x / c.mass) c.entropy_left_eq
      _ = H c.left := mul_div_cancel_left₀ _ c.mass_pos.ne'
  rw [hratio, entropyInverse_H_lower c.left_pos.le c.left_lt_half.le]

theorem right_eq_inverse {d e f : ℝ} (c : Contact d e f) :
    c.right = entropyInverse (f / c.mass) := by
  have hratio : f / c.mass = H c.right := by
    calc
      _ = (c.mass * H c.right) / c.mass := congrArg (fun x => x / c.mass) c.entropy_right_eq
      _ = H c.right := mul_div_cancel_left₀ _ c.mass_pos.ne'
  rw [hratio, entropyInverse_H_lower c.right_pos.le c.right_lt_half.le]

theorem mass_root {d e f : ℝ} (c : Contact d e f) :
    massFunction e f c.mass = d := by
  unfold massFunction
  rw [← c.left_eq_inverse, ← c.right_eq_inverse]
  exact c.difference_eq.symm

/-- All strict contact triples agree, including their mass and both inverse
coordinates. This does not use or claim uniqueness of a representing law. -/
theorem unique_values {d e f : ℝ} (c₁ c₂ : Contact d e f) :
    c₁.mass = c₂.mass ∧ c₁.left = c₂.left ∧ c₁.right = c₂.right := by
  have hm : c₁.mass = c₂.mass :=
    (massFunction_strictMonoOn c₁.entropy_left_pos c₁.entropy_right_pos).injOn
      c₁.mass_gt_max.le c₂.mass_gt_max.le (c₁.mass_root.trans c₂.mass_root.symm)
  refine ⟨hm, ?_, ?_⟩
  · rw [c₁.left_eq_inverse, c₂.left_eq_inverse, hm]
  · rw [c₁.right_eq_inverse, c₂.right_eq_inverse, hm]

/-- Unequal child entropies increase the endpoint contact mass. The displayed
ratio assumption ensures that the equal-entropy mass lies in the physical
domain of the unequal-entropy mass function. -/
theorem equal_entropy_mass_le {d e f : ℝ} (c : Contact d e f)
    (cbar : Contact d ((e + f) / 2) ((e + f) / 2))
    (hd : e + f ≤ d) : cbar.mass ≤ c.mass := by
  have he := c.entropy_left_pos
  have hf := c.entropy_right_pos
  have hdomain : max e f ≤ cbar.mass := by
    have hm : max e f ≤ e + f := max_le (by linarith) (by linarith)
    exact hm.trans (hd.trans cbar.difference_le_mass)
  obtain ⟨her, hfr⟩ := entropy_ratios_mem he hf hdomain
  have hi := inverse_midpoint_le ⟨her.1.le, her.2⟩ ⟨hfr.1.le, hfr.2⟩
  have hmean : (e / cbar.mass + f / cbar.mass) / 2 = ((e + f) / 2) / cbar.mass := by ring
  rw [hmean] at hi
  have hupper : massFunction e f cbar.mass ≤ d := by
    have hp := mul_le_mul_of_nonneg_left
      (show 1 - entropyInverse (e / cbar.mass) - entropyInverse (f / cbar.mass) ≤
        1 - entropyInverse (((e + f) / 2) / cbar.mass) -
          entropyInverse (((e + f) / 2) / cbar.mass) by linarith) cbar.mass_pos.le
    change massFunction e f cbar.mass ≤ massFunction ((e + f) / 2) ((e + f) / 2) cbar.mass at hp
    rwa [cbar.mass_root] at hp
  by_contra hn
  have hm := massFunction_strictMonoOn he hf c.mass_gt_max.le hdomain (lt_of_not_ge hn)
  rw [c.mass_root] at hm
  linarith

end Contact

#print axioms massFunction_strictMonoOn
#print axioms massFunction_continuousOn
#print axioms existsUnique_mass
#print axioms lower_massFunction_le_mean
#print axioms feasible_upper_test
#print axioms existsUnique_mass_of_feasible
#print axioms contact_of_mass
#print axioms exists_contact_of_feasible
#print axioms exists_contact_of_five_ratio
#print axioms Contact.mass_gt_max
#print axioms Contact.difference_le_mass
#print axioms Contact.unique_values
#print axioms inverse_midpoint_le
#print axioms exists_equal_entropy_contact
#print axioms Contact.equal_entropy_mass_le

end GeneralCK.PsiEndpointContact

end


