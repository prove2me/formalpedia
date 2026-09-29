-- Prove2me | Definitions.Def_CK_CKLaneA_PsiEnc
-- name    : CK_CKLaneA_PsiEnc
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:34:53.542006+00:00
-- url     : https://prove2.me/theorems/c797fe5e-9567-4a28-8682-408418eed984
-- title:
--   Courtade–Kumar proof module `CKLaneA.PsiEnc` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA.PsiEnc` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA.PsiEnc` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA.PsiEnc (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA/PsiEnc.lean)

import Definitions.Def_CK_CKLaneA_Psi
import Definitions.Def_CK_GeneralCK_Certificates_DyadicBivariateJetBounds

/-!
# Lane A: dyadic enclosures of `ψ, ψ', ψ''` over intervals
-/

namespace CKLaneA
open GeneralCK GeneralCK.Certificates Finset

namespace DI
variable {p : ℕ}

def pt (z : ℤ) : DyadicInterval p := ⟨z, z⟩
def zero : DyadicInterval p := ⟨0, 0⟩
def one : DyadicInterval p := DyadicInterval.ofInt p 1
def mulNat (a : DyadicInterval p) (m : ℕ) : DyadicInterval p := ⟨a.lo * m, a.hi * m⟩
def divNat (a : DyadicInterval p) (m : ℕ) : DyadicInterval p :=
  ⟨DyadicInterval.floorDiv a.lo m, DyadicInterval.ceilDiv a.hi m⟩
def widen (a : DyadicInterval p) (T : ℤ) : DyadicInterval p := ⟨a.lo - T, a.hi + T⟩
/-- an integer upper bound for `2^p * |x|` -/
def mag (a : DyadicInterval p) : ℤ := max (-a.lo) a.hi

theorem scale_pos' (p : ℕ) : (0 : ℝ) < (DyadicInterval.scale p : ℝ) := by
  unfold DyadicInterval.scale; push_cast; positivity

theorem pt_contains (z : ℤ) : (pt z : DyadicInterval p).Contains ((z : ℝ) / DyadicInterval.scale p) := by
  have hs := scale_pos' p
  constructor <;> simp only [pt] <;> rw [mul_div_cancel₀ _ hs.ne']

theorem zero_contains : (zero : DyadicInterval p).Contains 0 := by
  constructor <;> simp [zero]

theorem one_contains : (one : DyadicInterval p).Contains 1 := by
  simpa [one] using DyadicInterval.ofInt_sound p 1

theorem mulNat_sound {a : DyadicInterval p} {x : ℝ} (h : a.Contains x) (m : ℕ) :
    (mulNat a m).Contains (x * m) := by
  obtain ⟨h1, h2⟩ := h
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  constructor <;> simp only [mulNat] <;> push_cast
  · have := mul_le_mul_of_nonneg_right h1 hm; linarith
  · have := mul_le_mul_of_nonneg_right h2 hm; linarith

theorem divNat_sound {a : DyadicInterval p} {x : ℝ} (h : a.Contains x) {m : ℕ} (hm : 0 < m) :
    (divNat a m).Contains (x / m) := by
  obtain ⟨h1, h2⟩ := h
  have hmz : (0:ℤ) < (m:ℤ) := by exact_mod_cast hm
  have hmr : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hf := DyadicInterval.floorDiv_mul_le a.lo hmz
  have hc := DyadicInterval.le_ceilDiv_mul a.hi hmz
  have hf' : ((DyadicInterval.floorDiv a.lo m : ℤ) : ℝ) * (m:ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast hf
  have hc' : (a.hi : ℝ) ≤ ((DyadicInterval.ceilDiv a.hi m : ℤ) : ℝ) * (m:ℝ) := by exact_mod_cast hc
  constructor <;> simp only [divNat]
  · rw [mul_div_assoc', le_div_iff₀ hmr]; linarith
  · rw [mul_div_assoc', div_le_iff₀ hmr]; linarith

theorem widen_sound {a : DyadicInterval p} {x e : ℝ} (h : a.Contains x) {T : ℤ}
    (he : |e| ≤ (T : ℝ) / DyadicInterval.scale p) : (widen a T).Contains (x + e) := by
  obtain ⟨h1, h2⟩ := h
  have hs := scale_pos' p
  have he' : |(DyadicInterval.scale p : ℝ) * e| ≤ T := by
    rw [abs_mul, abs_of_pos hs]; rw [le_div_iff₀ hs] at he; linarith
  have := abs_le.mp he'
  constructor <;> simp only [widen] <;> push_cast <;> nlinarith [this.1, this.2]

theorem mag_bound {a : DyadicInterval p} {x : ℝ} (h : a.Contains x) :
    |x| ≤ (mag a : ℝ) / DyadicInterval.scale p := by
  obtain ⟨h1, h2⟩ := h
  have hs := scale_pos' p
  have hm1 : (-(a.lo:ℝ)) ≤ (mag a : ℝ) := by
    have : -a.lo ≤ mag a := le_max_left _ _
    exact_mod_cast this
  have hm2 : ((a.hi:ℝ)) ≤ (mag a : ℝ) := by
    have : a.hi ≤ mag a := le_max_right _ _
    exact_mod_cast this
  have hab : |(DyadicInterval.scale p : ℝ) * x| ≤ (mag a : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_mul, abs_of_pos hs] at hab
  rw [le_div_iff₀ hs]; linarith

def powDI (a : DyadicInterval p) : ℕ → DyadicInterval p
  | 0 => one
  | n + 1 => (powDI a n).mul a

theorem powDI_sound {a : DyadicInterval p} {x : ℝ} (h : a.Contains x) :
    ∀ n, (powDI a n).Contains (x ^ n)
  | 0 => by simpa [powDI] using one_contains
  | n + 1 => by rw [pow_succ]; exact DyadicInterval.mul_sound (powDI_sound h n) h

end DI

/-! ## Partial sums -/

section Sums
variable {p : ℕ}
open DI

/-- `(Σ_{k<n} Y^(2k)/(2k+1), Y^(2n))` -/
def sum0 (YY : DyadicInterval p) : ℕ → DyadicInterval p × DyadicInterval p
  | 0 => (zero, one)
  | n + 1 => ((sum0 YY n).1.add (DI.divNat (sum0 YY n).2 (2 * n + 1)), (sum0 YY n).2.mul YY)

/-- `(Σ_{k<n+1} psiT1 k, Y^(2n+1))` -/
def sum1 (Y YY : DyadicInterval p) : ℕ → DyadicInterval p × DyadicInterval p
  | 0 => (zero, Y)
  | n + 1 => ((sum1 Y YY n).1.add (DI.divNat (DI.mulNat (sum1 Y YY n).2 (2 * n + 2)) (2 * n + 3)),
      (sum1 Y YY n).2.mul YY)

/-- `(Σ_{k<n+1} psiT2 k, Y^(2n))` -/
def sum2 (YY : DyadicInterval p) : ℕ → DyadicInterval p × DyadicInterval p
  | 0 => (zero, one)
  | n + 1 => ((sum2 YY n).1.add
        (DI.divNat (DI.mulNat (DI.mulNat (sum2 YY n).2 (2 * n + 2)) (2 * n + 1)) (2 * n + 3)),
      (sum2 YY n).2.mul YY)

theorem sum0_sound {Y : DyadicInterval p} {y : ℝ} (hy : Y.Contains y) :
    ∀ n, (sum0 (Y.mul Y) n).1.Contains (∑ k ∈ range n, psiT k y) ∧
      (sum0 (Y.mul Y) n).2.Contains (y ^ (2 * n))
  | 0 => by simpa [sum0] using ⟨zero_contains, one_contains⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := sum0_sound hy n
    refine ⟨?_, ?_⟩
    · rw [sum_range_succ]
      have ht : psiT n y = y ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ) := by
        unfold psiT; push_cast; ring
      rw [ht]
      exact DyadicInterval.add_sound h1 (divNat_sound h2 (by omega))
    · have : y ^ (2 * (n + 1)) = y ^ (2 * n) * (y * y) := by ring
      rw [this]
      exact DyadicInterval.mul_sound h2 (DyadicInterval.mul_sound hy hy)

theorem sum1_sound {Y : DyadicInterval p} {y : ℝ} (hy : Y.Contains y) :
    ∀ n, (sum1 Y (Y.mul Y) n).1.Contains (∑ k ∈ range (n + 1), psiT1 k y) ∧
      (sum1 Y (Y.mul Y) n).2.Contains (y ^ (2 * n + 1))
  | 0 => by
    refine ⟨?_, by simpa [sum1] using hy⟩
    simpa [sum1, psiT1] using zero_contains
  | n + 1 => by
    obtain ⟨h1, h2⟩ := sum1_sound hy n
    refine ⟨?_, ?_⟩
    · rw [sum_range_succ]
      have ht : psiT1 (n + 1) y = y ^ (2 * n + 1) * ((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ) := by
        unfold psiT1
        have e1 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
        rw [e1]; push_cast; ring
      rw [ht]
      exact DyadicInterval.add_sound h1 (divNat_sound (mulNat_sound h2 _) (by omega))
    · have : y ^ (2 * (n + 1) + 1) = y ^ (2 * n + 1) * (y * y) := by ring
      rw [this]
      exact DyadicInterval.mul_sound h2 (DyadicInterval.mul_sound hy hy)

theorem sum2_sound {Y : DyadicInterval p} {y : ℝ} (hy : Y.Contains y) :
    ∀ n, (sum2 (Y.mul Y) n).1.Contains (∑ k ∈ range (n + 1), psiT2 k y) ∧
      (sum2 (Y.mul Y) n).2.Contains (y ^ (2 * n))
  | 0 => by
    refine ⟨?_, by simpa [sum2] using one_contains⟩
    simpa [sum2, psiT2] using zero_contains
  | n + 1 => by
    obtain ⟨h1, h2⟩ := sum2_sound hy n
    refine ⟨?_, ?_⟩
    · rw [sum_range_succ]
      have ht : psiT2 (n + 1) y =
          y ^ (2 * n) * ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ) := by
        unfold psiT2
        have e1 : 2 * (n + 1) - 1 - 1 = 2 * n := by omega
        have e2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
        rw [e1, e2]; push_cast; ring
      rw [ht]
      exact DyadicInterval.add_sound h1 (divNat_sound (mulNat_sound (mulNat_sound h2 _) _) (by omega))
    · have : y ^ (2 * (n + 1)) = y ^ (2 * n) * (y * y) := by ring
      rw [this]
      exact DyadicInterval.mul_sound h2 (DyadicInterval.mul_sound hy hy)

end Sums

/-! ## Tail bounds as dyadic integers -/

section Tails
variable {p : ℕ}
open DI

/-- `ρ = R / 2^p`, tails with `q = ρ^2` resp. `2ρ^2` -/
def tail0 (R : ℤ) (N : ℕ) : ℤ :=
  ((powDI (pt R : DyadicInterval p) (2 * N)).mul ((one.add (((pt R).mul (pt R)).neg)).recip)).hi
def tail1 (R : ℤ) (N : ℕ) : ℤ :=
  ((powDI (pt R : DyadicInterval p) (2 * N - 1)).mul ((one.add (((pt R).mul (pt R)).neg)).recip)).hi
def tail2 (R : ℤ) (N : ℕ) : ℤ :=
  (((DyadicInterval.ofInt p (2 * N)).mul (powDI (pt R : DyadicInterval p) (2 * N - 2))).mul
    ((one.add ((DyadicInterval.ofInt p 2).mul ((pt R).mul (pt R))).neg).recip)).hi

/-- the checkable side condition: `1 ≤ R`, `(1 - ρ²)` and `(1 - 2ρ²)` enclosures positive -/
def tailOK (R : ℤ) (N : ℕ) : Bool :=
  decide (1 ≤ R) && decide (1 ≤ N) &&
  decide (0 < (one.add (((pt R : DyadicInterval p).mul (pt R)).neg)).lo) &&
  decide (0 < (one.add ((DyadicInterval.ofInt p 2).mul ((pt R : DyadicInterval p).mul (pt R))).neg).lo)

theorem hi_bound {a : DyadicInterval p} {x : ℝ} (h : a.Contains x) :
    x ≤ (a.hi : ℝ) / DyadicInterval.scale p := by
  rw [le_div_iff₀ (scale_pos' p)]; linarith [h.2]

theorem lo_bound {a : DyadicInterval p} {x : ℝ} (h : a.Contains x) :
    (a.lo : ℝ) / DyadicInterval.scale p ≤ x := by
  rw [div_le_iff₀ (scale_pos' p)]; linarith [h.1]

theorem pos_of_lo_pos {a : DyadicInterval p} {x : ℝ} (h : a.Contains x) (hl : 0 < a.lo) : 0 < x :=
  DyadicInterval.positiveCheck_sound (by simpa [DyadicInterval.positiveCheck] using hl) h

theorem tailOK_facts {R : ℤ} {N : ℕ} (h : tailOK (p := p) R N = true) :
    let r : ℝ := (R : ℝ) / DyadicInterval.scale p
    0 < r ∧ r < 1 ∧ 2 * r ^ 2 < 1 ∧ 1 ≤ N ∧
    r ^ (2 * N) / (1 - r ^ 2) ≤ (tail0 (p := p) R N : ℝ) / DyadicInterval.scale p ∧
    r ^ (2 * N - 1) / (1 - r ^ 2) ≤ (tail1 (p := p) R N : ℝ) / DyadicInterval.scale p ∧
    (2 * N * r ^ (2 * N - 2)) / (1 - 2 * r ^ 2) ≤ (tail2 (p := p) R N : ℝ) / DyadicInterval.scale p := by
  intro r
  simp only [tailOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hR, hN⟩, hq1⟩, hq2⟩ := h
  have hs := scale_pos' p
  have hr : (pt R : DyadicInterval p).Contains r := pt_contains R
  have hr0 : 0 < r := by
    apply div_pos _ hs
    exact_mod_cast (show (0:ℤ) < R by omega)
  have hrr := DyadicInterval.mul_sound hr hr
  have h1r := DyadicInterval.add_sound one_contains (DyadicInterval.neg_sound hrr)
  have h1rpos : 0 < 1 + -(r * r) := pos_of_lo_pos h1r hq1
  have htwo : (DyadicInterval.ofInt p 2).Contains (2:ℝ) := by
    simpa using DyadicInterval.ofInt_sound p 2
  have h2r := DyadicInterval.add_sound one_contains
    (DyadicInterval.neg_sound (DyadicInterval.mul_sound htwo hrr))
  have h2rpos : 0 < 1 + -(2 * (r * r)) := pos_of_lo_pos h2r hq2
  have hr1 : r < 1 := by nlinarith
  refine ⟨hr0, hr1, by nlinarith, hN, ?_, ?_, ?_⟩
  · have hrec := DyadicInterval.recip_sound hq1 h1r
    have := hi_bound (DyadicInterval.mul_sound (powDI_sound hr (2 * N)) hrec)
    unfold tail0
    convert this using 1
    rw [div_eq_mul_inv]; congr 1; ring
  · have hrec := DyadicInterval.recip_sound hq1 h1r
    have := hi_bound (DyadicInterval.mul_sound (powDI_sound hr (2 * N - 1)) hrec)
    unfold tail1
    convert this using 1
    rw [div_eq_mul_inv]; congr 1; ring
  · have hrec := DyadicInterval.recip_sound hq2 h2r
    have hN2 : (DyadicInterval.ofInt p (2 * (N : ℤ))).Contains (2 * (N : ℝ)) := by
      have := DyadicInterval.ofInt_sound p (2 * (N : ℤ))
      push_cast at this; exact this
    have := hi_bound (DyadicInterval.mul_sound (DyadicInterval.mul_sound hN2 (powDI_sound hr (2 * N - 2))) hrec)
    unfold tail2
    convert this using 1
    rw [div_eq_mul_inv]; congr 1; ring

end Tails

/-! ## The ψ jet and its enclosure -/

noncomputable def psiJet : Jet2 := ⟨psi, psi1, psi2⟩

theorem psiJet_soundAt {y : ℝ} (hy : |y| < 1) : psiJet.SoundAt y :=
  ⟨hasDerivAt_psi hy, hasDerivAt_psi1 hy⟩

section PsiEnc
variable {p : ℕ}
open DI

def psiR (Y : DyadicInterval p) : ℤ := max (mag Y) 1

def psiOK (Y : DyadicInterval p) (N : ℕ) : Bool := tailOK (p := p) (psiR Y) N

def psiVal (Y : DyadicInterval p) (N : ℕ) : DyadicInterval p :=
  widen (sum0 (Y.mul Y) N).1 (tail0 (p := p) (psiR Y) N)

def psiEnc (Y : DyadicInterval p) (N : ℕ) : DyadicJetEnclosure p :=
  ⟨psiVal Y N,
   widen (sum1 Y (Y.mul Y) (N - 1)).1 (tail1 (p := p) (psiR Y) N),
   widen (sum2 (Y.mul Y) (N - 1)).1 (tail2 (p := p) (psiR Y) N)⟩

theorem psi_abs_lt {Y : DyadicInterval p} {N : ℕ} (hok : psiOK Y N = true) {y : ℝ}
    (hy : Y.Contains y) : |y| < 1 ∧ |y| ≤ (psiR Y : ℝ) / DyadicInterval.scale p := by
  obtain ⟨hr0, hr1, -, -⟩ := tailOK_facts hok
  have hm := mag_bound hy
  have hle : (mag Y : ℝ) ≤ (psiR Y : ℝ) := by exact_mod_cast le_max_left (mag Y) 1
  have h2 : |y| ≤ (psiR Y : ℝ) / DyadicInterval.scale p :=
    hm.trans (div_le_div_of_nonneg_right hle (scale_pos' p).le)
  exact ⟨lt_of_le_of_lt h2 hr1, h2⟩

theorem psiVal_sound {Y : DyadicInterval p} {N : ℕ} (hok : psiOK Y N = true) {y : ℝ}
    (hy : Y.Contains y) : (psiVal Y N).Contains (psi y) := by
  obtain ⟨hr0, hr1, hq, hN, t0, -, -⟩ := tailOK_facts hok
  obtain ⟨hy1, hyr⟩ := psi_abs_lt hok hy
  set r : ℝ := (psiR Y : ℝ) / DyadicInterval.scale p
  rw [psi_split hy1 N]
  apply widen_sound (sum0_sound hy N).1
  refine le_trans ?_ t0
  exact tail_bound (f := fun m => psiT m y) (C := r ^ (2 * N)) (q := r ^ 2) (by positivity)
    (by nlinarith) N (fun k => psiT_tail_term hyr N k)

theorem psiEnc_sound {Y : DyadicInterval p} {N : ℕ} (hok : psiOK Y N = true) {y : ℝ}
    (hy : Y.Contains y) : (psiEnc Y N).Contains psiJet y ∧ |y| < 1 := by
  obtain ⟨hr0, hr1, hq, hN, t0, t1, t2⟩ := tailOK_facts hok
  obtain ⟨hy1, hyr⟩ := psi_abs_lt hok hy
  set r : ℝ := (psiR Y : ℝ) / DyadicInterval.scale p
  refine ⟨⟨psiVal_sound hok hy, ?_, ?_⟩, hy1⟩
  · show (widen (sum1 Y (Y.mul Y) (N - 1)).1 (tail1 (p := p) (psiR Y) N)).Contains (psi1 y)
    have hN' : N - 1 + 1 = N := by omega
    have hs := (sum1_sound hy (N - 1)).1
    rw [hN'] at hs
    rw [psi1_split hy1 N]
    apply widen_sound hs
    refine le_trans ?_ t1
    exact tail_bound (f := fun m => psiT1 m y) (C := r ^ (2 * N - 1)) (q := r ^ 2) (by positivity)
      (by nlinarith) N (fun k => psiT1_tail_term hr0 hr1 hyr N k hN)
  · show (widen (sum2 (Y.mul Y) (N - 1)).1 (tail2 (p := p) (psiR Y) N)).Contains (psi2 y)
    have hN' : N - 1 + 1 = N := by omega
    have hs := (sum2_sound hy (N - 1)).1
    rw [hN'] at hs
    rw [psi2_split hy1 N]
    apply widen_sound hs
    refine le_trans ?_ t2
    exact tail_bound (f := fun m => psiT2 m y) (C := 2 * N * r ^ (2 * N - 2)) (q := 2 * r ^ 2)
      (by positivity) hq N (fun k => psiT2_tail_term hr0 hr1 hyr N k hN)

end PsiEnc

end CKLaneA

namespace CKLaneA
open GeneralCK GeneralCK.Certificates
section Adaptive
variable {p : ℕ}

/-- adaptive number of series terms from the magnitude bound -/
def psiN (Y : DyadicInterval p) : ℕ :=
  let R := psiR Y
  if 5 * R ≤ DyadicInterval.scale p then 22
  else if 3 * R ≤ DyadicInterval.scale p then 34
  else if 2 * R ≤ DyadicInterval.scale p then 52
  else 70

def psiOKA (Y : DyadicInterval p) : Bool := psiOK Y (psiN Y)
def psiValA (Y : DyadicInterval p) : DyadicInterval p := psiVal Y (psiN Y)
def psiEncA (Y : DyadicInterval p) : DyadicJetEnclosure p := psiEnc Y (psiN Y)

theorem psiValA_sound {Y : DyadicInterval p} (hok : psiOKA Y = true) {y : ℝ}
    (hy : Y.Contains y) : (psiValA Y).Contains (psi y) := psiVal_sound hok hy

theorem psiEncA_sound {Y : DyadicInterval p} (hok : psiOKA Y = true) {y : ℝ}
    (hy : Y.Contains y) : (psiEncA Y).Contains psiJet y ∧ |y| < 1 := psiEnc_sound hok hy

end Adaptive
end CKLaneA


