-- Prove2me | Definitions.Def_CK_CKLaneD_Cover
-- name    : CK_CKLaneD_Cover
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T06:31:34.801535+00:00
-- url     : https://prove2.me/theorems/b529e70e-ffcd-427e-8d93-7eda858cc47a
-- title:
--   Courtade–Kumar proof module `CKLaneD.Cover` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneD.Cover` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneD.Cover` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneD.Cover (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneD/Cover.lean)

import Definitions.Def_CK_CKLaneD_ArchTree
import Mathlib.Analysis.SpecialFunctions.Log.Base

-- ===== source module CKLaneD.Cover =====
section

/-!
# Coverage of the outer-opposite domain by the archived partition tree

`archTree_cover`: every interior law whose means/entropy lie in the archived outer-opposite domain
(`2^-28 ≤ a ≤ 1/10`, `1/2 ≤ b`, `2^-28 ≤ 1 - b`, `a + b ≤ 1`, `EMIN ≤ E`) lies in the physical image
`InUVT (uvtBox q)` of some leaf `q` of the archived tree (any owner label).
-/

namespace CKLaneD

open GeneralCK

/-- A real point of `(u, v, t)` space lies in a leaf box. -/
def PtIn (U : UVT) (u v t : ℝ) : Prop :=
  (U.u0 : ℝ) ≤ u ∧ u ≤ (U.u1 : ℝ) ∧ (U.v0 : ℝ) ≤ v ∧ v ≤ (U.v1 : ℝ) ∧
    (U.t0 : ℝ) ≤ t ∧ t ≤ (U.t1 : ℝ)

theorem uvtBox_append (p : List ℕ) (d : ℕ) : uvtBox (p ++ [d]) = uvtStep (uvtBox p) d := by
  unfold uvtBox
  rw [List.foldl_append]
  rfl

theorem ptIn_step {B : UVT} {u v t : ℝ} (h : PtIn B u v t) (ax : ℕ) :
    PtIn (uvtStep B (2 * ax)) u v t ∨ PtIn (uvtStep B (2 * ax + 1)) u v t := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rcases ax with _ | _ | _ | ax
  · rcases le_total u (((B.u0 + B.u1) / 2 : ℚ) : ℝ) with hm | hm
    · left; exact ⟨h1, hm, h3, h4, h5, h6⟩
    · right; exact ⟨hm, h2, h3, h4, h5, h6⟩
  · rcases le_total v (((B.v0 + B.v1) / 2 : ℚ) : ℝ) with hm | hm
    · left; exact ⟨h1, h2, h3, hm, h5, h6⟩
    · right; exact ⟨h1, h2, hm, h4, h5, h6⟩
  · rcases le_total t (((B.t0 + B.t1) / 2 : ℚ) : ℝ) with hm | hm
    · left; exact ⟨h1, h2, h3, h4, h5, hm⟩
    · right; exact ⟨h1, h2, h3, h4, hm, h6⟩
  · left
    have e : 2 * (ax + 3) = 2 * ax + 6 := by ring
    simp only [uvtStep, e]
    exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Every point of a node box lies in the box of one of the node's leaves
(`rpre` is the reversed path prefix of the node). -/
theorem PTree.coverR : ∀ (T : PTree) (rpre : List ℕ) {u v t : ℝ},
    PtIn (uvtBox rpre.reverse) u v t → ∃ q ∈ T.leavesR rpre, PtIn (uvtBox q.1) u v t
  | .leaf l, rpre, u, v, t, h => ⟨(rpre.reverse, l), by simp [PTree.leavesR], h⟩
  | .node ax l r, rpre, u, v, t, h => by
      rcases ptIn_step h ax with h' | h'
      · rw [← uvtBox_append, ← List.reverse_cons] at h'
        obtain ⟨q, hq, hq'⟩ := PTree.coverR l (2 * ax :: rpre) h'
        exact ⟨q, by simp only [PTree.leavesR, List.mem_append]; exact Or.inl hq, hq'⟩
      · rw [← uvtBox_append, ← List.reverse_cons] at h'
        obtain ⟨q, hq, hq'⟩ := PTree.coverR r ((2 * ax + 1) :: rpre) h'
        exact ⟨q, by simp only [PTree.leavesR, List.mem_append]; exact Or.inr hq, hq'⟩

theorem PTree.cover (T : PTree) {u v t : ℝ} (h : PtIn (uvtBox []) u v t) :
    ∃ q ∈ T.leaves, PtIn (uvtBox q.1) u v t :=
  PTree.coverR T [] (by simpa using h)

/-- A physical point `a = 2^-u`, `b = 1 - 2^-v`, `E = EMIN + t (C0 - EMIN)` in a leaf box lies in the
leaf's physical image. -/
theorem inUVT_of_ptIn {U : UVT} {a b E u v t : ℝ} (h : PtIn U u v t)
    (ha : a = (2 : ℝ) ^ (-u)) (hb : 1 - b = (2 : ℝ) ^ (-v))
    (hE : E = (EMIN : ℝ) + t * ((H a + H b) / 2 - (EMIN : ℝ)))
    (hC : (EMIN : ℝ) ≤ (H a + H b) / 2) (ha10 : a ≤ 1 / 10) (hab : a + b ≤ 1) :
    InUVT U a b E := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hmono : ∀ x y : ℝ, x ≤ y → (2 : ℝ) ^ (-y) ≤ (2 : ℝ) ^ (-x) := by
    intro x y hxy
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hC' : 0 ≤ (H a + H b) / 2 - (EMIN : ℝ) := by linarith
  refine ⟨?_, ?_, ?_, ?_, ha10, hab, ?_, ?_⟩
  · rw [ha]; exact hmono _ _ h2
  · rw [ha]; exact hmono _ _ h1
  · have := hmono _ _ h3; linarith
  · have := hmono _ _ h4; linarith
  · rw [hE]; nlinarith [mul_le_mul_of_nonneg_right h5 hC']
  · rw [hE]; nlinarith [mul_le_mul_of_nonneg_right h6 hC']

/-- Coverage of the archived outer-opposite domain by the leaves of `archTree`. -/
theorem archTree_cover {k : ℕ} (μ : InteriorLaw (Fin k))
    (ha0 : (2 : ℝ) ^ (-(28 : ℝ)) ≤ μ.a) (ha1 : μ.a ≤ 1 / 10)
    (hb0 : 1 / 2 ≤ μ.b) (hb1 : (2 : ℝ) ^ (-(28 : ℝ)) ≤ 1 - μ.b) (hab : μ.a + μ.b ≤ 1)
    (hE : (EMIN : ℝ) ≤ μ.meanEntropy) :
    ∃ q ∈ ArchTree.archTree.leaves, InUVT (uvtBox q.1) μ.a μ.b μ.meanEntropy := by
  have hapos : 0 < μ.a := μ.a_interior.1
  have hbpos : 0 < 1 - μ.b := by linarith [μ.b_interior.2]
  set u : ℝ := -Real.logb 2 μ.a with hu
  set v : ℝ := -Real.logb 2 (1 - μ.b) with hv
  have hau : μ.a = (2 : ℝ) ^ (-u) := by
    rw [hu, neg_neg, Real.rpow_logb (by norm_num) (by norm_num) hapos]
  have hbv : 1 - μ.b = (2 : ℝ) ^ (-v) := by
    rw [hv, neg_neg, Real.rpow_logb (by norm_num) (by norm_num) hbpos]
  -- entropy coordinate
  have hEle : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_le_cap, μ.f_le_cap]
  set C := (H μ.a + H μ.b) / 2 with hCdef
  set t : ℝ := if (EMIN : ℝ) < C then (μ.meanEntropy - EMIN) / (C - EMIN) else 0 with ht
  have htE : μ.meanEntropy = (EMIN : ℝ) + t * (C - EMIN) := by
    rw [ht]
    split_ifs with hc
    · have hne : C - (EMIN : ℝ) ≠ 0 := (sub_pos.mpr hc).ne'
      rw [div_mul_cancel₀ _ hne]
      ring
    · have : C = (EMIN : ℝ) := by linarith
      rw [this]; ring_nf; linarith
  have ht01 : 0 ≤ t ∧ t ≤ 1 := by
    rw [ht]
    split_ifs with hc
    · constructor
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]; linarith
    · norm_num
  -- u, v ranges from the mean ranges
  have hlog_le : ∀ x : ℝ, 0 < x → ∀ y : ℝ, (2 : ℝ) ^ (-y) ≤ x → -Real.logb 2 x ≤ y := by
    intro x hx y hxy
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _) hxy
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at this
    linarith
  have hlog_ge : ∀ x : ℝ, 0 < x → ∀ y : ℝ, x ≤ (2 : ℝ) ^ (-y) → y ≤ -Real.logb 2 x := by
    intro x hx y hxy
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hx hxy
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at this
    linarith
  have hu28 : u ≤ 28 := hlog_le _ hapos _ ha0
  have hu3 : 3 ≤ u := by
    apply hlog_ge _ hapos
    have : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [this]; linarith
  have hv28 : v ≤ 28 := hlog_le _ hbpos _ hb1
  have hv1 : 1 ≤ v := by
    apply hlog_ge _ hbpos
    have : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [this]; linarith
  have hroot : PtIn (uvtBox []) u v t := by
    simp only [uvtBox, List.foldl_nil, uvtRoot, PtIn]
    push_cast
    exact ⟨hu3, hu28, hv1, hv28, ht01.1, ht01.2⟩
  obtain ⟨q, hq, hq'⟩ := PTree.cover ArchTree.archTree hroot
  refine ⟨q, hq, inUVT_of_ptIn hq' hau hbv ?_ ?_ ha1 hab⟩
  · rw [← hCdef]; exact htE
  · rw [← hCdef]
    by_contra hc
    have hc' : C < (EMIN : ℝ) := lt_of_not_ge hc
    have : μ.meanEntropy < EMIN := lt_of_le_of_lt hEle hc'
    linarith

end CKLaneD

end


