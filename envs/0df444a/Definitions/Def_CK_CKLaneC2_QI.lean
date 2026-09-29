-- Prove2me | Definitions.Def_CK_CKLaneC2_QI
-- name    : CK_CKLaneC2_QI
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:03:29.997414+00:00
-- url     : https://prove2.me/theorems/22832ee0-b499-4d18-8a12-16c17c02c3cc
-- title:
--   Courtade–Kumar proof module `CKLaneC2.QI` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2.QI` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2.QI` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2.QI (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2/QI.lean)

import Mathlib

-- ===== source module CKLaneC2.QI =====
section
/-
Lane C2 — exact rational interval arithmetic, proved sound once.

`QI` is a closed rational interval.  Every operation is computable (plain `ℚ` arithmetic,
evaluated by the kernel with GMP-accelerated `Nat` primitives under `decide +kernel`), and
every operation has a soundness lemma of the form

    x ∈ I → y ∈ J → (x ⋆ y) ∈ (I ⋆ J)

for real `x y`.  `Ex` is a tiny expression language (variables, rational constants, `+ - *`,
natural powers) with a real semantics `evalR` and an interval semantics `evalI`, related by
`Ex.evalI_sound`, proved by structural induction.  Nothing numerical is assumed here.
-/

set_option autoImplicit false

namespace CKLaneC2

/-- A closed rational interval `[lo, hi]` (no well-formedness is required for soundness). -/
structure QI where
  lo : ℚ
  hi : ℚ
deriving Repr

namespace QI

/-- Real membership. -/
def Mem (x : ℝ) (I : QI) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def ofQ (q : ℚ) : QI := ⟨q, q⟩
def add (I J : QI) : QI := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : QI) : QI := ⟨-I.hi, -I.lo⟩
def sub (I J : QI) : QI := ⟨I.lo - J.hi, I.hi - J.lo⟩
def mul (I J : QI) : QI :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩
def pow (I : QI) : ℕ → QI
  | 0 => ofQ 1
  | n + 1 => mul (pow I n) I

theorem mem_ofQ (q : ℚ) : Mem (q : ℝ) (ofQ q) := ⟨le_rfl, le_rfl⟩

theorem mem_add {x y : ℝ} {I J : QI} (hx : Mem x I) (hy : Mem y J) :
    Mem (x + y) (add I J) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  constructor <;> simp only [add, Rat.cast_add] <;> linarith

theorem mem_neg {x : ℝ} {I : QI} (hx : Mem x I) : Mem (-x) (neg I) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> simp only [neg, Rat.cast_neg] <;> linarith

theorem mem_sub {x y : ℝ} {I J : QI} (hx : Mem x I) (hy : Mem y J) :
    Mem (x - y) (sub I J) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  constructor <;> simp only [sub, Rat.cast_sub] <;> linarith

/-- `x*y` lies between `a*y` and `b*y` when `x ∈ [a,b]`. -/
theorem between_mul_right {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right h1 hy),
      (mul_le_mul_of_nonneg_right h2 hy).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right h2 hy),
      (mul_le_mul_of_nonpos_right h1 hy).trans (le_max_left _ _)⟩

theorem between_mul_left {a b x y : ℝ} (h1 : a ≤ y) (h2 : y ≤ b) :
    min (x * a) (x * b) ≤ x * y ∧ x * y ≤ max (x * a) (x * b) := by
  have h := between_mul_right (y := x) h1 h2
  simp only [mul_comm] at h ⊢
  exact h

theorem mem_mul {x y : ℝ} {I J : QI} (hx : Mem x I) (hy : Mem y J) :
    Mem (x * y) (mul I J) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  have hA := between_mul_right (y := y) h1 h2
  have hB := between_mul_left (x := (I.lo : ℝ)) h3 h4
  have hC := between_mul_left (x := (I.hi : ℝ)) h3 h4
  simp only [Mem, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  constructor
  · refine le_trans ?_ hA.1
    rcases min_choice ((I.lo : ℝ) * y) ((I.hi : ℝ) * y) with h | h <;> rw [h]
    · exact le_trans (min_le_left _ _) hB.1
    · exact le_trans (min_le_right _ _) hC.1
  · refine le_trans hA.2 ?_
    rcases max_choice ((I.lo : ℝ) * y) ((I.hi : ℝ) * y) with h | h <;> rw [h]
    · exact le_trans hB.2 (le_max_left _ _)
    · exact le_trans hC.2 (le_max_right _ _)

theorem mem_pow {x : ℝ} {I : QI} (hx : Mem x I) : ∀ n : ℕ, Mem (x ^ n) (pow I n)
  | 0 => by simpa [pow] using mem_ofQ 1
  | n + 1 => by
      rw [pow_succ]
      exact mem_mul (mem_pow hx n) hx

end QI

/-- Expression language for the certificate polynomials. -/
inductive Ex where
  | var (i : ℕ)
  | cst (q : ℚ)
  | add (a b : Ex)
  | sub (a b : Ex)
  | mul (a b : Ex)
  | pow (a : Ex) (n : ℕ)
deriving Repr

namespace Ex

/-- Real semantics; variables are read from a list (default `0`). -/
noncomputable def evalR (ρ : List ℝ) : Ex → ℝ
  | var i => ρ.getD i 0
  | cst q => (q : ℝ)
  | add a b => evalR ρ a + evalR ρ b
  | sub a b => evalR ρ a - evalR ρ b
  | mul a b => evalR ρ a * evalR ρ b
  | pow a n => (evalR ρ a) ^ n

/-- Interval semantics; variables are read from a list (default `[0,0]`). -/
def evalI (σ : List QI) : Ex → QI
  | var i => σ.getD i (QI.ofQ 0)
  | cst q => QI.ofQ q
  | add a b => QI.add (evalI σ a) (evalI σ b)
  | sub a b => QI.sub (evalI σ a) (evalI σ b)
  | mul a b => QI.mul (evalI σ a) (evalI σ b)
  | pow a n => QI.pow (evalI σ a) n

/-- Pointwise membership of an environment. -/
def EnvMem : List ℝ → List QI → Prop
  | [], [] => True
  | x :: xs, I :: Is => QI.Mem x I ∧ EnvMem xs Is
  | _, _ => False

theorem envMem_getD : ∀ (ρ : List ℝ) (σ : List QI), EnvMem ρ σ →
    ∀ i : ℕ, QI.Mem (ρ.getD i 0) (σ.getD i (QI.ofQ 0))
  | [], [], _, i => by simpa using QI.mem_ofQ 0
  | x :: xs, I :: Is, h, 0 => by simpa using h.1
  | x :: xs, I :: Is, h, i + 1 => by simpa using envMem_getD xs Is h.2 i
  | [], _ :: _, h, _ => absurd h (by simp [EnvMem])
  | _ :: _, [], h, _ => absurd h (by simp [EnvMem])

theorem evalI_sound {ρ : List ℝ} {σ : List QI} (h : EnvMem ρ σ) :
    ∀ e : Ex, QI.Mem (evalR ρ e) (evalI σ e)
  | var i => envMem_getD ρ σ h i
  | cst q => QI.mem_ofQ q
  | add a b => QI.mem_add (evalI_sound h a) (evalI_sound h b)
  | sub a b => QI.mem_sub (evalI_sound h a) (evalI_sound h b)
  | mul a b => QI.mem_mul (evalI_sound h a) (evalI_sound h b)
  | pow a n => QI.mem_pow (evalI_sound h a) n

end Ex

end CKLaneC2

end


