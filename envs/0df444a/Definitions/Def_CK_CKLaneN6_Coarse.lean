-- Prove2me | Definitions.Def_CK_CKLaneN6_Coarse
-- name    : CK_CKLaneN6_Coarse
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:30:00.849823+00:00
-- url     : https://prove2.me/theorems/964badd9-0a95-45f8-8197-8dd0e01693bc
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Coarse` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Coarse` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Coarse` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Coarse (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Coarse.lean)

import Definitions.Def_CK_CKLaneN6_Check

-- ===== source module CKLaneN6.Coarse =====
section

/-!
# Lane N6: coarse certificates (one kernel check certifies a whole archived subtree)

`leafOK_extend`: the Thm 3 obligation on the box of an archived tree node gives it on the box of every
descendant path (exact halving shrinks the box; the row's `10^-6 ≤ E ≤ C0` makes the entropy-fraction
bounds monotone in `t`).  `shard_sound2`: a shard entry `(p, T, S)` — node path `p`, certificate tree
`T` below `feBox p`, archived leaf suffixes `S` — gives `LeafOK (feBox (p ++ s))` for every `s ∈ S`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN6

open GeneralCK
open CKLaneM05.FE8 (feRoot feStep feBox feBox_append CT)

/-- Box sanity: every coordinate interval is ordered. -/
def Sane (B : CKLaneD.Box) : Prop := B.alo ≤ B.ahi ∧ B.blo ≤ B.bhi ∧ B.t0 ≤ B.t1

theorem sane_step {B : CKLaneD.Box} (hB : Sane B) (d : ℕ) : Sane (feStep B d) := by
  unfold Sane at hB ⊢
  obtain ⟨h1, h2, h3⟩ := hB
  rcases d with _ | _ | _ | _ | _ | _ | d
  · exact ⟨by simp only [feStep]; linarith, h2, h3⟩
  · exact ⟨by simp only [feStep]; linarith, h2, h3⟩
  · exact ⟨h1, by simp only [feStep]; linarith, h3⟩
  · exact ⟨h1, by simp only [feStep]; linarith, h3⟩
  · exact ⟨h1, h2, by simp only [feStep]; linarith⟩
  · exact ⟨h1, h2, by simp only [feStep]; linarith⟩
  · simp only [feStep]
    exact ⟨h1, h2, h3⟩

theorem sane_foldl : ∀ (s : List ℕ) (B : CKLaneD.Box), Sane B → Sane (s.foldl feStep B)
  | [], _, h => h
  | d :: s, B, h => sane_foldl s (feStep B d) (sane_step h d)

theorem feBox_sane (p : List ℕ) : Sane (feBox p) :=
  sane_foldl p feRoot ⟨by norm_num [feRoot], by norm_num [feRoot], by norm_num [feRoot]⟩

/-- Exact halving keeps the image inside the parent image (for laws with `EMIN ≤ C0`). -/
theorem inBox_of_step {B : CKLaneD.Box} (hB : Sane B) (d : ℕ) {a b E : ℝ}
    (hC : ((CKLaneD.EMIN : ℚ) : ℝ) ≤ (H a + H b) / 2)
    (h : CKLaneD.InBox (feStep B d) a b E) : CKLaneD.InBox B a b E := by
  obtain ⟨q1, q2, q3⟩ := hB
  have r1 : (B.alo : ℝ) ≤ B.ahi := by exact_mod_cast q1
  have r2 : (B.blo : ℝ) ≤ B.bhi := by exact_mod_cast q2
  have r3 : (B.t0 : ℝ) ≤ B.t1 := by exact_mod_cast q3
  have hC0 : 0 ≤ (H a + H b) / 2 - ((CKLaneD.EMIN : ℚ) : ℝ) := by linarith
  rcases d with _ | _ | _ | _ | _ | _ | d
  · simp only [feStep] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    push_cast at h2
    exact ⟨h1, by linarith, h3, h4, h5, h6⟩
  · simp only [feStep] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    push_cast at h1
    exact ⟨by linarith, h2, h3, h4, h5, h6⟩
  · simp only [feStep] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    push_cast at h4
    exact ⟨h1, h2, h3, by linarith, h5, h6⟩
  · simp only [feStep] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    push_cast at h3
    exact ⟨h1, h2, by linarith, h4, h5, h6⟩
  · simp only [feStep] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    push_cast at h6
    refine ⟨h1, h2, h3, h4, h5, ?_⟩
    have k : ((B.t0 : ℝ) + B.t1) / 2 * ((H a + H b) / 2 - ((CKLaneD.EMIN : ℚ) : ℝ)) ≤
        (B.t1 : ℝ) * ((H a + H b) / 2 - ((CKLaneD.EMIN : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hC0
    linarith
  · simp only [feStep] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    push_cast at h5
    refine ⟨h1, h2, h3, h4, ?_, h6⟩
    have k : (B.t0 : ℝ) * ((H a + H b) / 2 - ((CKLaneD.EMIN : ℚ) : ℝ)) ≤
        ((B.t0 : ℝ) + B.t1) / 2 * ((H a + H b) / 2 - ((CKLaneD.EMIN : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hC0
    linarith
  · simpa only [feStep] using h

theorem leafOK_of_step {B : CKLaneD.Box} (hB : Sane B) (d : ℕ) (h : LeafOK B) :
    LeafOK (feStep B d) := by
  intro k μ hab hsum ha hb hd hd20 hE hor hs hin hact
  have hEC : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
    unfold InteriorLaw.meanEntropy; linarith [μ.e_le_cap, μ.f_le_cap]
  have hEM : ((CKLaneD.EMIN : ℚ) : ℝ) = 1 / 1000000 := by
    simp only [CKLaneD.EMIN]; push_cast; ring
  have hC : ((CKLaneD.EMIN : ℚ) : ℝ) ≤ (H μ.a + H μ.b) / 2 := by rw [hEM]; linarith
  exact h k μ hab hsum ha hb hd hd20 hE hor hs (inBox_of_step hB d hC hin) hact

theorem leafOK_foldl : ∀ (s : List ℕ) (B : CKLaneD.Box), Sane B → LeafOK B →
    LeafOK (s.foldl feStep B)
  | [], _, _, h => h
  | d :: s, B, hs, h => leafOK_foldl s (feStep B d) (sane_step hs d) (leafOK_of_step hs d h)

/-- The obligation on a node box gives it on every descendant box. -/
theorem leafOK_extend {p : List ℕ} (h : LeafOK (feBox p)) (s : List ℕ) : LeafOK (feBox (p ++ s)) := by
  unfold feBox
  rw [List.foldl_append]
  exact leafOK_foldl s _ (feBox_sane p) h

/-- Coarse shard: entries `(node path, certificate tree, archived leaf suffixes)`. -/
theorem shard_sound2 (L : List (List ℕ × CT W × List (List ℕ)))
    (h : L.all (fun x => x.2.1.check W.check (feBox x.1)) = true) :
    ∀ q ∈ L.flatMap (fun x => x.2.2.map (fun s => x.1 ++ s)), LeafOK (feBox q) := by
  intro q hq
  obtain ⟨x, hx, hq'⟩ := List.mem_flatMap.mp hq
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hq'
  rw [List.all_eq_true] at h
  exact leafOK_extend (CT.soundN6 W.check W.check_sound x.2.1 _ (h x hx)) s

end CKLaneN6

end


