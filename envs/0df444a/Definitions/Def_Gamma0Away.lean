-- Prove2me | Definitions.Def_Gamma0Away
-- name    : Gamma0Away
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/f9eba2a0-2749-5e3f-8260-8ed7b49c395b
-- title:
--   Γ₀-type subgroup of SL₂(ℤ[1/q]) and conjugation by diag(1,q)
-- statement:
--   The module works over [`Ihara.ZAway q`](../def/Gamma0Away.html#L11), the abbreviation for `Localization.Away (q : ℤ)`, i.e. the localisation $\mathbb{Z}[1/q]$ of $\mathbb{Z}$ at the element $q$. For natural numbers $N$ and $q$, [`Ihara.Gamma0Away N q`](../def/Gamma0Away.html#L15) is the subgroup of $\mathrm{SL}_2(\mathbb{Z}[1/q])$ whose underlying set consists of those $g$ with $(N : \mathbb{Z}[1/q])$ dividing the entry $g_{1,0}$, i.e. the lower left entry in the $0$-indexed $2\times 2$ convention; closure under multiplication and inversion comes from the explicit formulas for the product and for the inverse of a $2\times 2$ matrix of determinant one. No primality, coprimality or non-vanishing hypotheses are imposed on $N$ and $q$: for $N = 0$ the condition is that the lower left entry vanishes, and for $q = 0$ the coefficient ring is the zero ring. Membership is recorded both in the `Nat.cast` form ([`Ihara.mem_Gamma0Away`](../def/Gamma0Away.html#L35)) and in the form with divisibility by `algebraMap ℤ (ZAway q) (N : ℤ)` ([`Ihara.mem_Gamma0Away_iff_algebraMap`](../def/Gamma0Away.html#L39)).
--
--   The second half of the module makes the element $w = \mathrm{diag}(1,q)$ invertible over $\mathbb{Z}[1/q]$ and packages conjugation by it. [`Ihara.wMat q`](../def/Gamma0Away.html#L44) is the matrix $\mathrm{diag}(1, q)$ and [`Ihara.wMatInv q`](../def/Gamma0Away.html#L46) is $\mathrm{diag}(1, 1/q)$, built from Mathlib's `IsLocalization.Away.invSelf`; the two are mutually inverse, as recorded by [`Ihara.wMat_mul_wMatInv`](../def/Gamma0Away.html#L57) and [`Ihara.wMatInv_mul_wMat`](../def/Gamma0Away.html#L61) (with the scalar identities [`Ihara.q_mul_invSelf`](../def/Gamma0Away.html#L49), [`Ihara.invSelf_mul_q`](../def/Gamma0Away.html#L53)). The maps $\gamma \mapsto w^{-1}\gamma w$ and $\gamma \mapsto w\gamma w^{-1}$ preserve determinant one, giving [`Ihara.wConjFun`](../def/Gamma0Away.html#L65) and [`Ihara.wConjInvFun`](../def/Gamma0Away.html#L69), assembled into the multiplicative automorphism [`Ihara.wConj q`](../def/Gamma0Away.html#L81), of type $\mathrm{SL}_2(\mathbb{Z}[1/q]) \simeq^* \mathrm{SL}_2(\mathbb{Z}[1/q])$, $\gamma \mapsto w^{-1}\gamma w$, with its inverse as stated; on entries it sends $\begin{pmatrix}a&b\\ c&d\end{pmatrix}$ to $\begin{pmatrix}a& qb\\ c/q& d\end{pmatrix}$. Finally [`Ihara.wMatSwap q`](../def/Gamma0Away.html#L115) is $\mathrm{diag}(q,1)$, with inverse [`Ihara.wMatSwapInv q`](../def/Gamma0Away.html#L117), and [`Ihara.wConj_swap`](../def/Gamma0Away.html#L128) identifies conjugation by this matrix, $\gamma \mapsto \mathrm{diag}(q,1)^{-1}\gamma\,\mathrm{diag}(q,1)$, with the inverse automorphism $(\mathrm{wConj}\ q)^{-1}$, the two diagonal matrices differing by the central scalar $q$.
--
--   **Relation to Mathlib.** Mathlib's congruence subgroups $\Gamma_0(N)$ live inside $\mathrm{SL}_2(\mathbb{Z})$; the subgroup defined here is the project's own analogue inside $\mathrm{SL}_2(\mathbb{Z}[1/q])$. The coefficient ring and the inverse of $q$ in it are Mathlib's `Localization.Away` and `IsLocalization.Away.invSelf`, and the group is Mathlib's `SpecialLinearGroup`.
--
--   **Where it is used.** These definitions provide the group-theoretic setting for Ihara's lemma: for a prime $q$ not dividing $N$, the group `Gamma0Away N q` is an amalgam of two copies of $\Gamma_0(N)$ along $\Gamma_0(Nq)$, the second copy being embedded via the automorphism `wConj`, which fixes the convention $\gamma \mapsto w^{-1}\gamma w$ used throughout the project's treatment.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Gamma0Away.lean

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Localization.Away.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace Ihara

open Matrix

open scoped MatrixGroups

abbrev ZAway (q : ℕ) : Type := Localization.Away (q : ℤ)

variable (N q : ℕ)

def Gamma0Away : Subgroup (SL(2, ZAway q)) where
  carrier := { g | (N : ZAway q) ∣ g 1 0 }
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    change (N : ZAway q) ∣ (1 : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0
    rw [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    exact dvd_zero _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    change (N : ZAway q) ∣ (a.1 * b.1) 1 0
    rw [(Matrix.two_mul_expl a.1 b.1).2.2.1]
    exact dvd_add (ha.mul_right _) (hb.mul_left _)
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [SpecialLinearGroup.SL2_inv_expl a]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    exact dvd_neg.mpr ha

theorem mem_Gamma0Away {N q : ℕ} {g : SL(2, ZAway q)} :
    g ∈ Gamma0Away N q ↔ (N : ZAway q) ∣ g 1 0 :=
  Iff.rfl

theorem mem_Gamma0Away_iff_algebraMap {N q : ℕ} {g : SL(2, ZAway q)} :
    g ∈ Gamma0Away N q ↔ algebraMap ℤ (ZAway q) (N : ℤ) ∣ g 1 0 := by
  have h : algebraMap ℤ (ZAway q) (N : ℤ) = (N : ZAway q) := by simp
  rw [mem_Gamma0Away, h]

def wMat : Matrix (Fin 2) (Fin 2) (ZAway q) := !![1, 0; 0, (q : ZAway q)]

noncomputable def wMatInv : Matrix (Fin 2) (Fin 2) (ZAway q) :=
  !![1, 0; 0, IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ)]

theorem q_mul_invSelf :
    (q : ZAway q) * IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) = 1 := by
  simpa using IsLocalization.Away.mul_invSelf (S := ZAway q) ((q : ℕ) : ℤ)

theorem invSelf_mul_q :
    IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) * (q : ZAway q) = 1 := by
  rw [mul_comm]; exact q_mul_invSelf q

theorem wMat_mul_wMatInv : wMat q * wMatInv q = 1 := by
  rw [wMat, wMatInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [q_mul_invSelf q]

theorem wMatInv_mul_wMat : wMatInv q * wMat q = 1 := by
  rw [wMat, wMatInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [invSelf_mul_q q]

noncomputable def wConjFun (γ : SL(2, ZAway q)) : SL(2, ZAway q) :=
  ⟨wMatInv q * γ.1 * wMat q, by
    rw [det_mul, det_mul, γ.2, mul_one, ← det_mul, wMatInv_mul_wMat, det_one]⟩

noncomputable def wConjInvFun (γ : SL(2, ZAway q)) : SL(2, ZAway q) :=
  ⟨wMat q * γ.1 * wMatInv q, by
    rw [det_mul, det_mul, γ.2, mul_one, ← det_mul, wMat_mul_wMatInv, det_one]⟩

theorem wConjFun_coe (γ : SL(2, ZAway q)) :
    (wConjFun q γ).1 = wMatInv q * γ.1 * wMat q :=
  rfl

theorem wConjInvFun_coe (γ : SL(2, ZAway q)) :
    (wConjInvFun q γ).1 = wMat q * γ.1 * wMatInv q :=
  rfl

noncomputable def wConj : SL(2, ZAway q) ≃* SL(2, ZAway q) where
  toFun := wConjFun q
  invFun := wConjInvFun q
  left_inv γ := Subtype.ext <| by
    rw [wConjInvFun_coe, wConjFun_coe,
      show wMat q * (wMatInv q * γ.1 * wMat q) * wMatInv q
          = (wMat q * wMatInv q) * γ.1 * (wMat q * wMatInv q) by
        simp only [mul_assoc],
      wMat_mul_wMatInv, one_mul, mul_one]
  right_inv γ := Subtype.ext <| by
    rw [wConjFun_coe, wConjInvFun_coe,
      show wMatInv q * (wMat q * γ.1 * wMatInv q) * wMat q
          = (wMatInv q * wMat q) * γ.1 * (wMatInv q * wMat q) by
        simp only [mul_assoc],
      wMatInv_mul_wMat, one_mul, mul_one]
  map_mul' a b := Subtype.ext <| by
    change wMatInv q * (a.1 * b.1) * wMat q
        = wMatInv q * a.1 * wMat q * (wMatInv q * b.1 * wMat q)
    rw [show wMatInv q * a.1 * wMat q * (wMatInv q * b.1 * wMat q)
          = wMatInv q * a.1 * (wMat q * wMatInv q) * (b.1 * wMat q) by
        simp only [mul_assoc],
      wMat_mul_wMatInv, mul_one]
    simp only [mul_assoc]

@[simp]
theorem wConj_coe (γ : SL(2, ZAway q)) :
    (wConj q γ).1 = wMatInv q * γ.1 * wMat q :=
  rfl

@[simp]
theorem wConj_symm_coe (γ : SL(2, ZAway q)) :
    ((wConj q).symm γ).1 = wMat q * γ.1 * wMatInv q :=
  rfl

def wMatSwap : Matrix (Fin 2) (Fin 2) (ZAway q) := !![(q : ZAway q), 0; 0, 1]

noncomputable def wMatSwapInv : Matrix (Fin 2) (Fin 2) (ZAway q) :=
  !![IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ), 0; 0, 1]

theorem wMatSwap_mul_wMatSwapInv : wMatSwap q * wMatSwapInv q = 1 := by
  rw [wMatSwap, wMatSwapInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [q_mul_invSelf q]

theorem wMatSwapInv_mul_wMatSwap : wMatSwapInv q * wMatSwap q = 1 := by
  rw [wMatSwap, wMatSwapInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [invSelf_mul_q q]

theorem wConj_swap (γ : SL(2, ZAway q)) :
    wMatSwapInv q * γ.1 * wMatSwap q = ((wConj q).symm γ).1 := by
  have hu := invSelf_mul_q q
  rw [wConj_symm_coe]
  induction γ using Matrix.SpecialLinearGroup.fin_two_induction with
  | h a b c d hdet =>
    show wMatSwapInv q * !![a, b; c, d] * wMatSwap q
        = wMat q * !![a, b; c, d] * wMatInv q
    rw [wMat, wMatInv, wMatSwap, wMatSwapInv, Matrix.mul_fin_two, Matrix.mul_fin_two,
      Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp only [mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one]
    rw [mul_right_comm (IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ)) a (q : ZAway q), hu]
    simp only [one_mul]
    rw [mul_comm (IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ)) b,
      mul_comm c (q : ZAway q),
      mul_right_comm (q : ZAway q) d (IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ)),
      q_mul_invSelf q]
    simp only [one_mul]

end Ihara


