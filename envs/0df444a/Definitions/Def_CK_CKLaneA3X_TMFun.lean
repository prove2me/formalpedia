-- Prove2me | Definitions.Def_CK_CKLaneA3X_TMFun
-- name    : CK_CKLaneA3X_TMFun
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:21:04.078556+00:00
-- url     : https://prove2.me/theorems/e2cc92fe-3546-4c11-95ea-2c72672f86e3
-- title:
--   Courtade–Kumar proof module `CKLaneA3X.TMFun` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3X.TMFun` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3X.TMFun` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3X.TMFun (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/TMFun.lean)

import Definitions.Def_CK_CKLaneA3X_TM

/-!
# CKLaneA3X.TMFun — functional Taylor-model operations (kernel-evaluable) with soundness

A `TMd` is `(P, r, n)`.  `Good f d` := `Encl f d.P d.r d.n ∧ 0 ≤ d.r`.
All remainders are rounded up to multiples of `2^-40` (`rup`) to keep rationals small.
-/

namespace CKLaneA3X

structure TMd where
  P : TPoly
  r : ℚ
  n : ℕ

def Good (f : ℝ → ℝ → ℝ) (d : TMd) : Prop := Encl f d.P d.r d.n ∧ 0 ≤ d.r

noncomputable def rup (x : ℚ) : ℚ := ((⌈x * 1099511627776⌉ : ℤ) : ℚ) / 1099511627776

theorem le_rup (x : ℚ) : x ≤ rup x := by
  unfold rup
  rw [le_div_iff₀ (by norm_num)]
  exact Int.le_ceil _

noncomputable def entryBounds (P : TPoly) : List ℚ :=
  @List.rec SPoly (fun _ => List ℚ) [] (fun s _ ih => rup (SPoly.absB s) :: ih) P

theorem entryBounds_spec (P : TPoly) : EntryBnd P (entryBounds P) := by
  induction P with
  | nil => exact List.Forall₂.nil
  | cons s P ih =>
    refine List.Forall₂.cons ?_ ih
    intro σ hσ
    exact (SPoly.absB_spec hσ log2_lo log2_hi s).trans (by exact_mod_cast le_rup _)

theorem zeroPrefix_zero (P : TPoly) : zeroPrefix P 0 = true := by cases P <;> rfl

theorem HB_nonneg (β γ : List ℚ) (hβ : Nonneg β) (hγ : Nonneg γ) (n : ℕ) : 0 ≤ HB β γ n := by
  induction β generalizing n with
  | nil => show (0 : ℚ) ≤ 0; exact le_refl _
  | cons b β ih =>
    have hb : 0 ≤ b := hβ b List.mem_cons_self
    have hβ' : Nonneg β := fun x hx => hβ x (List.mem_cons_of_mem _ hx)
    cases n with
    | zero =>
      show 0 ≤ bsum (b :: β) * bsum γ
      exact mul_nonneg (bsum_nonneg _ hβ) (bsum_nonneg _ hγ)
    | succ n =>
      show 0 ≤ b * bsum (ldrop γ (n + 1)) + HB β γ n
      exact add_nonneg (mul_nonneg hb (bsum_nonneg _ (ldrop_nonneg _ hγ _))) (ih hβ' n)

noncomputable def mulRem (β γ : List ℚ) (r1 r2 : ℚ) (n1 n2 v1 v2 n : ℕ) : ℚ :=
  HB β γ n + (bsum (ldrop β v1) + r1 * Tq ^ (n1 - v1)) * r2 * Tq ^ (v1 + n2 - n)
    + bsum (ldrop γ v2) * r1 * Tq ^ (v2 + n1 - n)

noncomputable def TMd.mul (a b : TMd) (va vb n : ℕ) : TMd :=
  ⟨TPoly.mulT a.P b.P n, rup (mulRem (entryBounds a.P) (entryBounds b.P) a.r b.r a.n b.n va vb n), n⟩

theorem Tq_nonneg : (0 : ℚ) ≤ Tq := by norm_num [Tq]

theorem TMd.mul_good {f g : ℝ → ℝ → ℝ} {a b : TMd} (ha : Good f a) (hb : Good g b) (va vb n : ℕ)
    (hza : zeroPrefix a.P va = true) (hzb : zeroPrefix b.P vb = true)
    (hva : va ≤ a.n) (hn1 : n ≤ va + b.n) (hn2 : n ≤ vb + a.n) :
    Good (fun t ρ => f t ρ * g t ρ) (TMd.mul a b va vb n) := by
  have hβ := entryBounds_spec a.P
  have hγ := entryBounds_spec b.P
  refine ⟨?_, ?_⟩
  · exact Encl.mul ha.1 hβ hb.1 hγ hza hzb hva hn1 hn2 ha.2 hb.2 rfl (le_rup _)
  · refine le_trans ?_ (le_rup _)
    unfold mulRem
    have h1 := HB_nonneg _ _ hβ.nonneg hγ.nonneg n
    have h2 := bsum_nonneg _ (ldrop_nonneg _ hβ.nonneg va)
    have h3 := bsum_nonneg _ (ldrop_nonneg _ hγ.nonneg vb)
    have ha2 := ha.2
    have hb2 := hb.2
    have hT := Tq_nonneg
    positivity

noncomputable def TMd.add (a b : TMd) : TMd :=
  ⟨TPoly.add a.P b.P, rup (a.r * Tq ^ (a.n - min a.n b.n) + b.r * Tq ^ (b.n - min a.n b.n)), min a.n b.n⟩

theorem TMd.add_good {f g : ℝ → ℝ → ℝ} {a b : TMd} (ha : Good f a) (hb : Good g b) :
    Good (fun t ρ => f t ρ + g t ρ) (TMd.add a b) := by
  have hT := Tq_nonneg
  have h1 : Encl f a.P (a.r * Tq ^ (a.n - min a.n b.n)) (min a.n b.n) :=
    Encl.lower ha.1 (min_le_left _ _) ha.2 (le_refl _)
  have h2 : Encl g b.P (b.r * Tq ^ (b.n - min a.n b.n)) (min a.n b.n) :=
    Encl.lower hb.1 (min_le_right _ _) hb.2 (le_refl _)
  refine ⟨Encl.add h1 h2 rfl (le_rup _), ?_⟩
  refine le_trans ?_ (le_rup _)
  have := ha.2; have := hb.2
  positivity

noncomputable def TMd.scale (c : ℚ) (a : TMd) : TMd := ⟨TPoly.scale c a.P, rup (|c| * a.r), a.n⟩

theorem TMd.scale_good {f : ℝ → ℝ → ℝ} {a : TMd} (ha : Good f a) (c : ℚ) :
    Good (fun t ρ => (c : ℝ) * f t ρ) (TMd.scale c a) := by
  refine ⟨Encl.scale c ha.1 rfl (le_rup _), ?_⟩
  refine le_trans ?_ (le_rup _)
  have := ha.2
  positivity

/-- exact constant `c` as a TM of order `n` -/
def TMd.const (c : ℚ) (n : ℕ) : TMd := ⟨[[(0, [(0, c)])]], 0, n⟩

theorem TMd.const_good (c : ℚ) (n : ℕ) : Good (fun _ _ => (c : ℝ)) (TMd.const c n) := by
  refine ⟨Encl.exact n ?_, le_refl _⟩
  intro t ρ _
  simp [ev, TMd.const, TPoly.eval_cons, TPoly.eval_nil, SPoly.eval_cons, SPoly.eval_nil,
    LPoly.eval_cons, LPoly.eval_nil]

def TMd.zero (n : ℕ) : TMd := ⟨[], 0, n⟩

theorem TMd.zero_good (n : ℕ) : Good (fun _ _ => (0 : ℝ)) (TMd.zero n) := by
  refine ⟨Encl.exact n ?_, le_refl _⟩
  intro t ρ _
  simp [ev, TMd.zero, TPoly.eval_nil]

/-! ## Horner evaluation of a rational polynomial at a TM -/

noncomputable def hornerR (cs : List ℚ) (z : ℝ) : ℝ :=
  @List.rec ℚ (fun _ => ℝ) 0 (fun c _ ih => (c : ℝ) + z * ih) cs

theorem hornerR_nil (z : ℝ) : hornerR [] z = 0 := rfl
theorem hornerR_cons (c : ℚ) (cs : List ℚ) (z : ℝ) : hornerR (c :: cs) z = (c : ℝ) + z * hornerR cs z := rfl

theorem hornerR_eq_sum (cs : List ℚ) (z : ℝ) :
    hornerR cs z = ∑ k ∈ Finset.range cs.length, (cs.getD k 0 : ℝ) * z ^ k := by
  induction cs with
  | nil => simp [hornerR_nil]
  | cons c cs ih =>
    rw [hornerR_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [Finset.mul_sum]
    ring_nf

noncomputable def tmHorner (X : TMd) (vx n : ℕ) (cs : List ℚ) : TMd :=
  @List.rec ℚ (fun _ => TMd) (TMd.zero n)
    (fun c _ acc => TMd.add (TMd.const c n) (TMd.mul X acc vx 0 n)) cs

theorem tmHorner_good {x : ℝ → ℝ → ℝ} {X : TMd} (hx : Good x X) (vx n : ℕ)
    (hz : zeroPrefix X.P vx = true) (hvx : vx ≤ X.n) (hn : n ≤ X.n) (cs : List ℚ) :
    Good (fun t ρ => hornerR cs (x t ρ)) (tmHorner X vx n cs) ∧ (tmHorner X vx n cs).n = n := by
  induction cs with
  | nil => exact ⟨TMd.zero_good n, rfl⟩
  | cons c cs ih =>
    obtain ⟨hacc, han⟩ := ih
    have hm := TMd.mul_good hx hacc vx 0 n hz (zeroPrefix_zero _) hvx (by omega) (by omega)
    have hadd := TMd.add_good (TMd.const_good c n) hm
    refine ⟨?_, ?_⟩
    · exact hadd
    · show min n n = n
      exact min_self n

/-! ## magnitude of a TM-enclosed function -/

theorem Good.abs_le {x : ℝ → ℝ → ℝ} {X : TMd} (hx : Good x X) {v : ℕ}
    (hz : zeroPrefix X.P v = true) (hv : v ≤ X.n) {t ρ : ℝ} (hd : Dom t ρ) :
    |x t ρ| ≤ t ^ v * ((bsum (ldrop (entryBounds X.P) v) : ℝ) + X.r * (Tq : ℝ) ^ (X.n - v)) := by
  have ht0 := hd.1.le
  have h1 := hx.1 t ρ hd
  have hp := (entryBounds_spec X.P).eval_le_val hz ht0 hd.2.1 hd.sigma
  have h4 : t ^ X.n ≤ (Tq : ℝ) ^ (X.n - v) * t ^ v := pow_le_T_pow ht0 hd.2.1 hv
  have hr : (0 : ℝ) ≤ X.r := by exact_mod_cast hx.2
  unfold ev at h1
  have h3 : |x t ρ| ≤ |TPoly.eval t (ρ - 1 / 2) (Real.log 2) X.P| + X.r * t ^ X.n := by
    have := abs_sub_abs_le_abs_sub (x t ρ) (TPoly.eval t (ρ - 1 / 2) (Real.log 2) X.P)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h4 hr, pow_nonneg ht0 v]

end CKLaneA3X


