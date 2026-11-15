-- Prove2me | Definitions.Def_RPLib_S3_EllW2K2b
-- name    : RPLib_S3_EllW2K2b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:49:48.396699+00:00
-- url     : https://prove2.me/theorems/f4a1ffc1-3960-4987-9d9c-c17302487b4b
-- title:
--   The Eichler-Selberg trace formula in weight two: the Fourier transform of `WcF` as a double sum
-- statement:
--   The Fourier transform of `WcF` as a double sum.
--
--   * `mkT_add_mul`: `mkT n (c,t) (a + x c) = T^x · mkT n (c,t) a · T^{-x}`, so `levelCount_mkT_add_mul`:
--     `λ(a, t) := levelCount (mkT n (c,t) a)` is `c`-periodic in `a`.
--   * `WcG M n δ' c t a = [c ∣ a(t-a) - n] λ(a, t)` (`a : ℕ`); `WcG_add`: period `|c|`.
--   * `two_mul_WcF_eq_range`: `2 WcF c t = Σ_{a < |c|} WcG a`; `two_mul_M_WcF_eq`: `2 M WcF c t = Σ_{a < |c| M} WcG a`.
--   * **`dft_WcF_eq`**: for `q = |c| M`,
--     `2 M · dft (x ↦ WcF c x.val) j = Σ_{x,y : ZMod q} [c ∣ x(y-x) - n] λ(x, y) e(-yj/q)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; A. Weil, On some exponential sums, Proc. Nat. Acad. Sci. USA 34 (1948), 204-207; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2EX
import Definitions.Def_RPLib_S3_EllW2K1
import Definitions.Def_RPLib_S3_EllW2K2a

/-!
# S3-ES-Wt2 (O6, file K2b): the Fourier transform of `WcF` as a double sum

* `mkT_add_mul`: `mkT n (c,t) (a + x c) = T^x · mkT n (c,t) a · T^{-x}`, so `levelCount_mkT_add_mul`:
  `λ(a, t) := levelCount (mkT n (c,t) a)` is `c`-periodic in `a`.
* `WcG M n δ' c t a = [c ∣ a(t-a) - n] λ(a, t)` (`a : ℕ`); `WcG_add`: period `|c|`.
* `two_mul_WcF_eq_range`: `2 WcF c t = Σ_{a < |c|} WcG a`; `two_mul_M_WcF_eq`: `2 M WcF c t = Σ_{a < |c| M} WcG a`.
* **`dft_WcF_eq`**: for `q = |c| M`,
  `2 M · dft (x ↦ WcF c x.val) j = Σ_{x,y : ZMod q} [c ∣ x(y-x) - n] λ(x, y) e(-yj/q)`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

lemma mkT_add_mul (n : ℤ) {c : ℤ} (hc : c ≠ 0) (t a x : ℤ) :
    mkT n (c, t) (a + x * c) = S3.Conj.conj (ModularGroup.T ^ x) (mkT n (c, t) a) := by
  have hb : ((a + x * c) * (t - (a + x * c)) - n) / c =
      (a * (t - a) - n) / c + (x * (t - a) - x * a - x * x * c) := by
    rw [show (a + x * c) * (t - (a + x * c)) - n =
      a * (t - a) - n + c * (x * (t - a) - x * a - x * x * c) by ring]
    exact Int.add_mul_ediv_left _ _ hc
  rw [S3.Conj.conj_T_zpow]
  simp only [mkT]
  rw [hb]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

lemma levelCount_mkT_add_mul (δ' : ZMod M) (n : ℤ) {c : ℤ} (hc : c ≠ 0) (t a x : ℤ) :
    S3.levelCount M δ' (mkT n (c, t) (a + x * c)) = S3.levelCount M δ' (mkT n (c, t) a) := by
  rw [mkT_add_mul n hc, HypPar.levelCount_conj]

/-- The summand `a ↦ [c ∣ a(t-a) - n] λ(a, t)` (with `a` a natural number). -/
def WcG (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (c t : ℤ) (a : ℕ) : ℂ :=
  if c ∣ (a : ℤ) * (t - a) - n then (S3.levelCount M δ' (mkT n (c, t) a) : ℂ) else 0

lemma WcG_add (n : ℤ) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) (t : ℤ) (a : ℕ) :
    WcG M n δ' c t (a + c.natAbs) = WcG M n δ' c t a := by
  obtain ⟨x, hx⟩ : ∃ x : ℤ, ((c.natAbs : ℕ) : ℤ) = x * c := by
    rcases Int.natAbs_eq c with h | h
    · exact ⟨1, by linarith⟩
    · exact ⟨-1, by linarith⟩
  have e : ((a + c.natAbs : ℕ) : ℤ) = (a : ℤ) + x * c := by rw [Nat.cast_add, hx]
  have hd : c ∣ ((a : ℤ) + x * c) * (t - ((a : ℤ) + x * c)) - n ↔ c ∣ (a : ℤ) * (t - a) - n := by
    rw [show ((a : ℤ) + x * c) * (t - ((a : ℤ) + x * c)) - n =
      (a : ℤ) * (t - a) - n + c * (x * (t - a) - x * a - x * x * c) by ring]
    exact dvd_add_left (dvd_mul_right c _)
  unfold WcG
  rw [e, levelCount_mkT_add_mul δ' n hc]
  by_cases h : c ∣ (a : ℤ) * (t - a) - n
  · rw [if_pos (hd.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hd.1 h')), if_neg h]

lemma two_mul_WcF_eq_range (n : ℤ) (δ' : ZMod M) (c t : ℤ) :
    2 * WcF M n δ' c t = ∑ a ∈ range c.natAbs, WcG M n δ' c t a := by
  unfold WcF fib WcG
  rw [Finset.mul_sum, Finset.sum_filter]
  symm
  refine Finset.sum_bij' (fun a _ => (a : ℤ)) (fun a _ => a.toNat) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Ico, ← Int.natCast_natAbs]
    exact ⟨Int.natCast_nonneg a, by exact_mod_cast ha⟩
  · intro a ha
    rw [Finset.mem_Ico, ← Int.natCast_natAbs] at ha
    rw [Finset.mem_range]
    omega
  · intro a _
    simp
  · intro a ha
    rw [Finset.mem_Ico] at ha
    exact Int.toNat_of_nonneg ha.1
  · intro a _
    split_ifs <;> ring

lemma two_mul_M_WcF_eq (n : ℤ) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) (t : ℤ) :
    2 * (M : ℂ) * WcF M n δ' c t = ∑ a ∈ range (c.natAbs * M), WcG M n δ' c t a := by
  rw [sum_range_mul_of_periodic (WcG_add n δ' hc t) M, ← two_mul_WcF_eq_range n δ' c t]
  ring

/-- **The Fourier transform of `WcF c ·` as a double sum over `ZMod q`**, `q = |c| M`. -/
theorem dft_WcF_eq (n : ℤ) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q]
    (hq : q = c.natAbs * M) (j : ZMod q) :
    2 * (M : ℂ) * ZMod.dft (fun x : ZMod q => WcF M n δ' c (x.val : ℤ)) j =
      ∑ x : ZMod q, ∑ y : ZMod q,
        (if c ∣ (x.val : ℤ) * ((y.val : ℤ) - x.val) - n then
          (S3.levelCount M δ' (mkT n (c, (y.val : ℤ)) (x.val : ℤ)) : ℂ) *
            (ZMod.stdAddChar (-(y * j)) : ℂ)
         else 0) := by
  have hr : range q = range (c.natAbs * M) := by rw [hq]
  have e1 : ∀ u : ℕ, 2 * (M : ℂ) * ((ZMod.stdAddChar (-((u : ZMod q) * j)) : ℂ) * WcF M n δ' c u) =
      (ZMod.stdAddChar (-((u : ZMod q) * j)) : ℂ) * ∑ x : ZMod q, WcG M n δ' c u x.val := by
    intro u
    rw [sum_zmod_val (q := q) (WcG M n δ' c u), hr, ← two_mul_M_WcF_eq n δ' hc]
    ring
  calc 2 * (M : ℂ) * ZMod.dft (fun x : ZMod q => WcF M n δ' c (x.val : ℤ)) j
      = ∑ u ∈ range q, (ZMod.stdAddChar (-((u : ZMod q) * j)) : ℂ) *
          ∑ x : ZMod q, WcG M n δ' c u x.val := by
        rw [dft_val_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => e1 u
    _ = ∑ y : ZMod q, (ZMod.stdAddChar (-(y * j)) : ℂ) *
          ∑ x : ZMod q, WcG M n δ' c (y.val : ℤ) x.val := by
        rw [← sum_zmod_val]
        simp only [ZMod.natCast_zmod_val]
    _ = ∑ x : ZMod q, ∑ y : ZMod q,
          (ZMod.stdAddChar (-(y * j)) : ℂ) * WcG M n δ' c (y.val : ℤ) x.val := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        unfold WcG
        split_ifs <;> ring

end RamanujanPetersson.EllW2


