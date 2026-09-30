-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRationalTreeBridgeKernel
-- name    : CK_GeneralCK_Certificates_E8TAxisRationalTreeBridgeKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:48:58.338217+00:00
-- url     : https://prove2.me/theorems/b44d9bce-d100-4e9a-bc11-f5b9e2b35185
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisRationalTreeBridgeKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisRationalTreeBridgeKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisRationalTreeBridgeKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisRationalTreeBridgeKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisRationalTreeBridgeKernel.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneratedGeometry

-- ===== source module GeneralCK.Certificates.E8TAxisRationalTreeBridgeKernel =====
section

/-! Exact rational split validation, independent of the analytic leaf proofs. -/

namespace GeneralCK.Certificates.E8TAxisRationalTreeBridgeKernel

open E8TAxisPartitionKernel E8TAxisGeneratedGeometry

def qLeftS (r : RatRect) (x : ℚ) : RatRect := { r with s1 := x }
def qRightS (r : RatRect) (x : ℚ) : RatRect := { r with s0 := x }
def qLowerT (r : RatRect) (x : ℚ) : RatRect := { r with t1 := x }
def qUpperT (r : RatRect) (x : ℚ) : RatRect := { r with t0 := x }

def qLeaves : Tree → RatRect → List RatRect
  | .leaf, r => [r]
  | .splitS x left right, r =>
      qLeaves left (qLeftS r x) ++ qLeaves right (qRightS r x)
  | .splitT x lower upper, r =>
      qLeaves lower (qLowerT r x) ++ qLeaves upper (qUpperT r x)

def qValid : Tree → RatRect → Prop
  | .leaf, _ => True
  | .splitS x left right, r =>
      r.s0 ≤ x ∧ x ≤ r.s1 ∧ qValid left (qLeftS r x) ∧ qValid right (qRightS r x)
  | .splitT x lower upper, r =>
      r.t0 ≤ x ∧ x ≤ r.t1 ∧ qValid lower (qLowerT r x) ∧ qValid upper (qUpperT r x)

def qValidB : Tree → RatRect → Bool
  | .leaf, _ => true
  | .splitS x left right, r =>
      decide (r.s0 ≤ x) && (decide (x ≤ r.s1) &&
        (qValidB left (qLeftS r x) && qValidB right (qRightS r x)))
  | .splitT x lower upper, r =>
      decide (r.t0 ≤ x) && (decide (x ≤ r.t1) &&
        (qValidB lower (qLowerT r x) && qValidB upper (qUpperT r x)))

theorem qValid_of_bool {tree : Tree} {r : RatRect}
    (h : qValidB tree r = true) : qValid tree r := by
  induction tree generalizing r with
  | leaf => trivial
  | splitS x left right ihl ihr =>
      simp only [qValidB, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨hx0, hx1, hl, hr⟩
      exact ⟨hx0, hx1, ihl hl, ihr hr⟩
  | splitT x lower upper ihl ihu =>
      simp only [qValidB, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨hx0, hx1, hl, hr⟩
      exact ⟨hx0, hx1, ihl hl, ihu hr⟩

theorem allLeaves_of_qValid {tree : Tree} {r : RatRect}
    (hv : qValid tree r)
    (hp : ∀ q ∈ qLeaves tree r, CellPositive q.real) :
    AllLeaves CellPositive tree r.real := by
  induction tree generalizing r with
  | leaf =>
      change CellPositive r.real
      exact hp r (by simp [qLeaves])
  | splitS x left right ihl ihr =>
      rcases hv with ⟨hx0, hx1, hvl, hvr⟩
      change (r.s0 : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ (r.s1 : ℝ) ∧
        AllLeaves CellPositive left (qLeftS r x).real ∧
        AllLeaves CellPositive right (qRightS r x).real
      refine ⟨by exact_mod_cast hx0, by exact_mod_cast hx1, ?_, ?_⟩
      · apply ihl hvl
        intro q hq
        exact hp q (by simp only [qLeaves, List.mem_append]; exact Or.inl hq)
      · apply ihr hvr
        intro q hq
        exact hp q (by simp only [qLeaves, List.mem_append]; exact Or.inr hq)
  | splitT x lower upper ihl ihu =>
      rcases hv with ⟨hx0, hx1, hvl, hvr⟩
      change (r.t0 : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ (r.t1 : ℝ) ∧
        AllLeaves CellPositive lower (qLowerT r x).real ∧
        AllLeaves CellPositive upper (qUpperT r x).real
      refine ⟨by exact_mod_cast hx0, by exact_mod_cast hx1, ?_, ?_⟩
      · apply ihl hvl
        intro q hq
        exact hp q (by simp only [qLeaves, List.mem_append]; exact Or.inl hq)
      · apply ihu hvr
        intro q hq
        exact hp q (by simp only [qLeaves, List.mem_append]; exact Or.inr hq)

def qDomain : RatRect := ⟨3 / 50, 63 / 20, 0, 1 / 50⟩

theorem qDomain_real : qDomain.real = domain := by
  norm_num [qDomain, RatRect.real, domain]

#print axioms allLeaves_of_qValid
#print axioms qValid_of_bool
#print axioms qDomain_real

end GeneralCK.Certificates.E8TAxisRationalTreeBridgeKernel

end


