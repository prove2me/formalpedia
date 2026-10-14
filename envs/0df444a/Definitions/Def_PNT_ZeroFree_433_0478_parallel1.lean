-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0478_parallel1
-- name    : PNT_ZeroFree_433_0478_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:26:08.36682+00:00
-- url     : https://prove2.me/theorems/79b8fb45-55d1-486c-82ce-fec122bbcce2
-- title:
--   Zero-free region foundations: Descent.Basic [0478_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Descent.Basic
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/Basic.lean#L10-L166

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_PNT_ZeroFree_433_0150
import Definitions.Def_PNT_ZeroFree_433_0292_parallel1
import Definitions.Def_PNT_ZeroFree_433_0293_parallel1
import Definitions.Def_PNT_ZeroFree_433_0294_parallel1
import Definitions.Def_PNT_ZeroFree_433_0306_parallel1
import Definitions.Def_PNT_ZeroFree_433_0326_parallel1
import Definitions.Def_PNT_ZeroFree_433_0339_parallel1
import Definitions.Def_PNT_ZeroFree_433_0366_parallel1
import Definitions.Def_PNT_ZeroFree_433_0369_parallel1
import Definitions.Def_PNT_ZeroFree_433_0391_parallel1
import Definitions.Def_PNT_ZeroFree_433_0439_parallel1
import Definitions.Def_PNT_ZeroFree_433_0464_parallel1
import Definitions.Def_PNT_ZeroFree_433_0480_parallel1
import Definitions.Def_PNT_ZeroFree_433_0600_parallel1
import Definitions.Def_PNT_ZeroFree_433_0616_parallel1
import Definitions.Def_PNT_ZeroFree_433_0623_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/Basic.lean#L10-L166
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Descent.Basic
section
namespace OAI

namespace SevenEighths.InverseMoment

def MarkedMargins (m r z c : ℝ) : Prop :=
  r + 2 * z ≤ m - c ∧ 2 * r + 8 * z ≤ 3 * m - c

def CanonicalMargins (F M Q z c : ℝ) : Prop :=
  c ≤ F - M - Q - z ∧ c ≤ 4 * F - 3 * M - 6 * z

theorem markedMargins_of_strict {m r z : ℝ}
    (h₁ : r + 2 * z < m) (h₂ : 2 * r + 8 * z < 3 * m) :
    ∃ c > 0, MarkedMargins m r z c := by
  refine ⟨min (m - r - 2 * z) (3 * m - 2 * r - 8 * z), ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · constructor
    · have := min_le_left (m - r - 2 * z) (3 * m - 2 * r - 8 * z)
      linarith
    · have := min_le_right (m - r - 2 * z) (3 * m - 2 * r - 8 * z)
      linarith

theorem markedMargins_subcollection {m r z z' c : ℝ}
    (h : MarkedMargins m r z c) (hz : z' ≤ z) :
    MarkedMargins m r z' c := by
  obtain ⟨h₁, h₂⟩ := h
  constructor <;> linarith

theorem canonicalMargins_subcollection {F M Q z z' c : ℝ}
    (h : CanonicalMargins F M Q z c) (hz : z' ≤ z) :
    CanonicalMargins F M Q z' c := by
  obtain ⟨h₁, h₂⟩ := h
  constructor <;> linarith

theorem canonicalMargins_weaken {F M Q z c c' : ℝ}
    (h : CanonicalMargins F M Q z c) (hc : c' ≤ c) :
    CanonicalMargins F M Q z c' := by
  exact ⟨hc.trans h.1, hc.trans h.2⟩

def decrease (ell A t g theta V : ℝ) : ℝ := ell + A + t + g - theta + V

def childF (F ell A t g theta V j delta : ℝ) : ℝ :=
  F - decrease ell A t g theta V - 2 * ell + j + delta

def childM (M ell A t g theta V j eta : ℝ) : ℝ :=
  M - 2 * decrease ell A t g theta V - 2 * ell + j + eta

theorem canonical_transition (F M ell A t g theta V j : ℝ) :
    childF F ell A t g theta V j 0 - childM M ell A t g theta V j 0 =
      F - M + decrease ell A t g theta V ∧
    4 * childF F ell A t g theta V j 0 -
      3 * childM M ell A t g theta V j 0 =
      4 * F - 3 * M + 2 * (A + t + g - theta + V) + j := by
  constructor <;> unfold childF childM decrease <;> ring

theorem child_margins_sharp {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    c + delta - 5 * eta ≤
      childF F ell A t g theta V j delta -
      childM M ell A t g theta V j eta - Q' - z ∧
    c + 4 * delta - 7 * eta ≤
      4 * childF F ell A t g theta V j delta -
      3 * childM M ell A t g theta V j eta - 6 * z := by
  obtain ⟨h₁, h₂⟩ := h
  unfold childF childM decrease at *
  constructor <;> linarith

theorem child_margins {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta) Q' z (c - 7 * eta) := by
  obtain ⟨h₁, h₂⟩ := child_margins_sharp (delta := delta) h hA ht hV hj hgt hQ
  constructor <;> linarith

theorem child_row_decrease {M ell A t g theta V j eta d : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hgt : -2 * eta ≤ g - theta)
    (hj : j ≤ 2 * ell + 3 * eta) (hterminal : d ≤ ell + V)
    (heta : eta ≤ d / 16) :
    3 * d / 2 ≤ M - childM M ell A t g theta V j eta := by
  unfold childM decrease
  linarith

theorem childF_upper {F ell A t g theta V j delta eta : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hell : 0 ≤ ell) (hV : 0 ≤ V)
    (hgt : -2 * eta ≤ g - theta) (hj : j ≤ 2 * ell + 3 * eta)
    (hdelta : delta ≤ 6 * eta) :
    childF F ell A t g theta V j delta ≤ F + 11 * eta := by
  unfold childF decrease
  linarith

theorem clipping_bounds {N eta : ℝ} (heta : 0 ≤ eta) (hN : -6 * eta ≤ N) :
    0 ≤ max 0 N - N ∧ max 0 N - N ≤ 6 * eta := by
  constructor
  · exact sub_nonneg.mpr (le_max_right 0 N)
  · rcases le_total 0 N with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith

theorem step_energy_exponent {F Fc kappa lambda count delta eta tau pi eps : ℝ}
    (hid : kappa + lambda + count + 2 * Fc = F)
    (hdelta : delta ≤ 6 * eta) :
    kappa + lambda + count + 2 * (Fc + delta) +
      (9 / 2 + 18 + 11 / 2) * eta + tau + pi + eps ≤
      F + 40 * eta + tau + pi + eps := by
  linarith

def initialF (r z G P delta : ℝ) : ℝ := r + z - 2 * G - P + delta

def initialM (m r z G P eta tau : ℝ) : ℝ :=
  2 * (r + z - 2 * G) - m - 2 * P + 6 * eta + tau

theorem initial_margins_sharp {m r z G P delta eta tau Q c₁ c₂ : ℝ}
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta) :
    c₁ + delta - 9 * eta - tau ≤
      initialF r z G P delta - initialM m r z G P eta tau - Q - (z - G) ∧
    c₂ + 4 * delta - 22 * eta - 3 * tau ≤
      4 * initialF r z G P delta - 3 * initialM m r z G P eta tau -
        6 * (z - G) := by
  unfold initialF initialM
  constructor <;> linarith

theorem initial_margins {m r z G P delta eta tau Q c₁ c₂ : ℝ}
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta)
    (hc : 0 ≤ min c₁ c₂) (hdelta : 0 ≤ delta) (heta : eta ≤ min c₁ c₂ / 100)
    (htau : tau ≤ min c₁ c₂ / 100) :
    CanonicalMargins (initialF r z G P delta)
      (initialM m r z G P eta tau) Q (z - G) (3 * min c₁ c₂ / 4) := by
  obtain ⟨ha, hb⟩ := initial_margins_sharp (delta := delta) (tau := tau) h₁ h₂ hG hP hQ
  have hc₁ := min_le_left c₁ c₂
  have hc₂ := min_le_right c₁ c₂
  constructor <;> linarith

theorem initial_prefactor_identity (m r z G P : ℝ) :
    (m - 2 * (r + z - 2 * G) + P) + P +
      2 * initialF r z G P 0 = m := by
  unfold initialF
  ring

theorem initial_energy_exponent {m delta eta pi eps : ℝ}
    (hdelta : delta ≤ 3 * eta) :
    m + 3 * eta + 2 * eta + 2 * delta + pi + eps ≤
      m + 11 * eta + pi + eps := by
  linarith

theorem total_step_loss {D eta tau pi eps : ℝ}
    (h₁ : D * eta ≤ eps / 160) (h₂ : D * tau ≤ eps / 4)
    (h₃ : D * pi ≤ eps / 4) :
    D * (40 * eta + tau + pi) ≤ 3 * eps / 4 := by
  nlinarith

theorem depth_margin {c D h eta : ℝ} (heta : 0 ≤ eta) (hh : h ≤ D)
    (hbudget : D * eta ≤ c / 14) : c / 2 ≤ c - 7 * h * eta := by
  have := mul_le_mul_of_nonneg_right hh heta
  nlinarith

end SevenEighths.InverseMoment

end OAI

end


