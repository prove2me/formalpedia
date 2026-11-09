-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Basic
-- name    : LinearSetReconciliation327_Main_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:53.536309+00:00
-- url     : https://prove2.me/theorems/2ae9e665-c9ce-46cb-b2cc-799638c416c9
-- title:
--   §2.1 — logarithms, volume, h_N, G_a, entropy, uniform laws, cyclic rows
-- statement:
--   Logarithms are to base two. $L(N,t)=\log\sum_{a=0}^t\binom Na$. $h_N(z)=z\log(eN/z)$ with $h_N(0)=0$. $G_a(z)=\min\{1,2^{z-a}\}$. Shannon entropy of a countable family is an extended nonnegative sum, and a finite family also has a real-valued version. `prU` and `expU` are the uniform probability and expectation on a nonempty finite type. Rows: position $p$ of a permutation of $[N]$ goes to row $p\bmod m$ at local index $\lfloor p/m\rfloor$, so row lengths differ by at most one. `rowImage` is the row-local image of a set, and `assemble` maps row estimates back to original coordinates, discarding padding positions.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), §2.1 and §2.2, PDF p.9 (printed p.8)

import Mathlib

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

/-! Notation of §2.1 (PDF p.9, printed p.8) of Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with
O(d) Additive Redundancy*, STOC 2027 submission #327. Coordinates are 0-based (`[N]` is `Fin N` or
`range N`); supports are finite sets of naturals and addition of vectors is symmetric difference. -/

/-- All unmarked logarithms of the paper are to base two. -/
def lg (x : ℝ) : ℝ := Real.logb 2 x

/-- `L(N,t) = log ∑_{a=0}^t binom(N,a)`, equation (1). -/
def L (N t : ℕ) : ℝ := lg ((∑ a ∈ range (t + 1), N.choose a : ℕ) : ℝ)

/-- `h_N(z) = z log(eN/z)` with `h_N(0) = 0` (PDF p.10). -/
def hN (N : ℕ) (z : ℝ) : ℝ := if z = 0 then 0 else z * lg (Real.exp 1 * N / z)

/-- `G_a(z) = min{1, 2^{z-a}}` (Lemma 4.6). -/
def G (a : ℕ) (z : ℝ) : ℝ := min 1 ((2 : ℝ) ^ (z - a))

/-- Shannon entropy in bits of a countable family of probabilities, as an extended nonnegative sum,
so a divergent sum is `⊤` and not a junk value. A zero term is zero (`0 * lg (1/0) = 0`). -/
def entropy {ι : Type} (p : ι → ℝ) : ℝ≥0∞ := ∑' i, ENNReal.ofReal (p i * lg (1 / p i))

/-- Shannon entropy in bits of a finite family, as a real number. -/
def entropyFin {ι : Type} [Fintype ι] (p : ι → ℝ) : ℝ := ∑ i, p i * lg (1 / p i)

open Classical in
/-- Probability of an event under the uniform law of a nonempty finite type. -/
def prU {α : Type} [Fintype α] (P : α → Prop) : ℝ :=
  ((univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

/-- Expectation under the uniform law of a nonempty finite type. -/
def expU {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / (Fintype.card α : ℝ)

/-- Length of row `j` when the positions `0, …, N-1` are dealt to `m` rows cyclically: position `p`
goes to row `p % m` at local index `p / m`. Row lengths differ by at most one. -/
def rowLen (N m j : ℕ) : ℕ := ((range N).filter (fun p => p % m = j)).card

open Classical in
/-- Row-local image of the set `S` of coordinates in row `j`, after the permutation `π` of `[N]`.
Elements of `S` outside `[N]` are ignored. Padding is never a coordinate. -/
def rowImage (N m : ℕ) (π : Equiv.Perm (Fin N)) (j : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (univ.filter (fun i : Fin N => i.val ∈ S ∧ (π i).val % m = j)).image (fun i => (π i).val / m)

open Classical in
/-- The original coordinates whose row-local image lies in the row estimate; the row positions that
correspond to padding are discarded. -/
def assemble (N m : ℕ) (π : Equiv.Perm (Fin N)) (est : ℕ → Finset ℕ) : Finset ℕ :=
  (univ.filter (fun i : Fin N => (π i).val / m ∈ est ((π i).val % m))).image (fun i => i.val)

/-- In characteristic two a sum over a symmetric difference is the sum of the two sums. -/
theorem sum_symmDiff_char_two {A : Type} [AddCommGroup A] (h2 : ∀ a : A, a + a = 0)
    (C C' : Finset ℕ) (f : ℕ → A) :
    ∑ v ∈ symmDiff C C', f v = ∑ v ∈ C, f v + ∑ v ∈ C', f v := by
  classical
  have hd : Disjoint (C \ C') (C' \ C) := by
    rw [Finset.disjoint_left]; intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have e1 : ∑ v ∈ symmDiff C C', f v = ∑ v ∈ C \ C', f v + ∑ v ∈ C' \ C, f v := by
    rw [symmDiff_def, Finset.sup_eq_union, Finset.sum_union hd]
  have e2 : ∑ v ∈ C, f v = ∑ v ∈ C \ C', f v + ∑ v ∈ C ∩ C', f v := by
    rw [← Finset.sum_sdiff (Finset.inter_subset_left : C ∩ C' ⊆ C), Finset.sdiff_inter_self_left]
  have e3 : ∑ v ∈ C', f v = ∑ v ∈ C' \ C, f v + ∑ v ∈ C ∩ C', f v := by
    rw [← Finset.sum_sdiff (Finset.inter_subset_right : C ∩ C' ⊆ C'), Finset.sdiff_inter_self_right]
  rw [e1, e2, e3]
  have := h2 (∑ v ∈ C ∩ C', f v)
  abel_nf
  have h4 : (2:ℤ) • (∑ v ∈ C ∩ C', f v) = 0 := by rw [two_zsmul]; exact this
  rw [h4]; simp

end LinearSetReconciliation327.Main


