-- Prove2me | Definitions.Def_RPLib_S3_EllW2MV3a
-- name    : RPLib_S3_EllW2MV3a
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:57:39.667723+00:00
-- url     : https://prove2.me/theorems/c70f1557-a5c5-4f6b-81b5-c6ff104600f0
-- title:
--   The Eichler-Selberg trace formula in weight two: `#Xc = M² N(|c|)`
-- statement:
--   `#Xc = M² N(|c|)`.
--
--   * `Nk n k = Σ_{h ∣ k, h ∣ n} h φ(k/h)` (the number of solutions of `a b ≡ n (mod k)`), `gf n g = [g ∣ n] g`.
--   * `card_dvd_mul_sub`: `#{b mod K : K ∣ a b̃ - n} = gf n (gcd(K, a))`.
--   * `card_fib_x`: `#{d mod q : c ∣ x̃ d̃ - n} = M · gf n (gcd(|c|, x̃))`.
--   * `sum_range_gcd`: `Σ_{a < k} f(gcd(k, a)) = Σ_{h ∣ k} φ(k/h) f(h)`; `sum_gf_eq_Nk`.
--   * **`card_Xc_eq_Nk`**: `#{z ∈ (ZMod q)² : Xc z} = M · M · Nk n |c|`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2MV2b
import Definitions.Def_RPLib_S3_EllW2K2d
import Definitions.Def_RPLib_S3_HypParG

/-!
# S3-ES-Wt2 (O6, file MV3a): `#Xc = M² N(|c|)`

* `Nk n k = Σ_{h ∣ k, h ∣ n} h φ(k/h)` (the number of solutions of `a b ≡ n (mod k)`), `gf n g = [g ∣ n] g`.
* `card_dvd_mul_sub`: `#{b mod K : K ∣ a b̃ - n} = gf n (gcd(K, a))`.
* `card_fib_x`: `#{d mod q : c ∣ x̃ d̃ - n} = M · gf n (gcd(|c|, x̃))`.
* `sum_range_gcd`: `Σ_{a < k} f(gcd(k, a)) = Σ_{h ∣ k} φ(k/h) f(h)`; `sum_gf_eq_Nk`.
* **`card_Xc_eq_Nk`**: `#{z ∈ (ZMod q)² : Xc z} = M · M · Nk n |c|`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

variable {M : ℕ} [NeZero M]

/-- `N(k) = Σ_{h ∣ k, h ∣ n} h φ(k/h)`. -/
def Nk (n : ℤ) (k : ℕ) : ℕ :=
  ∑ h ∈ k.divisors.filter (fun h : ℕ => (h : ℤ) ∣ n), h * Nat.totient (k / h)

/-- `gf n g = [g ∣ n] g`. -/
def gf (n : ℤ) (g : ℕ) : ℕ := if (g : ℤ) ∣ n then g else 0

lemma coprime_one_val {K : ℕ} (g : ℕ) (hg : g ∣ K) : Nat.Coprime (1 : ZMod K).val g := by
  rw [ZMod.val_one_eq_one_mod]
  have h : Nat.Coprime (1 % K) K := by
    rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_one_right]
  exact h.coprime_dvd_right hg

lemma card_dvd_mul_sub (n : ℤ) {K : ℕ} [NeZero K] (a : ℕ) :
    (univ.filter fun b : ZMod K => (K : ℤ) ∣ (a : ℤ) * b.val - n).card = gf n (Nat.gcd K a) := by
  have e : ∀ b : ZMod K, ((K : ℤ) ∣ (a : ℤ) * b.val - n) ↔ b * (a : ZMod K) = (n : ZMod K) * 1 := by
    intro b
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, mul_one, Int.cast_sub, Int.cast_mul, sub_eq_zero,
      Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm]
  rw [Finset.filter_congr (fun b _ => e b),
    HypPar.card_mul_eq (a : ZMod K) 1 n (coprime_one_val _ (Nat.gcd_dvd_left _ _)),
    ZMod.val_natCast, Nat.gcd_comm K (a % K), ← Nat.gcd_rec]
  rfl

omit [NeZero M] in
lemma card_fib_x (n : ℤ) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q] (hq : q = c.natAbs * M)
    (x : ZMod q) :
    (univ.filter fun d : ZMod q => Xc n c (x, d)).card = M * gf n (Nat.gcd c.natAbs x.val) := by
  have : NeZero c.natAbs := ⟨Int.natAbs_ne_zero.mpr hc⟩
  have e : ∀ d : ZMod q, Xc n c (x, d) ↔ ((c.natAbs : ℤ) ∣ (x.val : ℤ) * d.val - n) := by
    intro d; exact Int.natAbs_dvd.symm
  have hr : range q = range (M * c.natAbs) := by rw [hq, mul_comm]
  have hP : ∀ m : ℕ, ((c.natAbs : ℤ) ∣ (x.val : ℤ) * ((m + c.natAbs : ℕ) : ℤ) - n) ↔
      ((c.natAbs : ℤ) ∣ (x.val : ℤ) * (m : ℤ) - n) := by
    intro m
    have e2 : (x.val : ℤ) * ((m + c.natAbs : ℕ) : ℤ) - n =
        ((x.val : ℤ) * m - n) + c.natAbs * x.val := by push_cast; ring
    rw [e2]
    exact dvd_add_left (dvd_mul_right _ _)
  rw [Finset.filter_congr (fun d _ => e d),
    HypPar.card_filter_val (M := q) (fun m : ℕ => ((c.natAbs : ℤ) ∣ (x.val : ℤ) * m - n)), hr,
    HypPar.card_filter_range_periodic _ c.natAbs hP M,
    ← HypPar.card_filter_val (M := c.natAbs) (fun m : ℕ => ((c.natAbs : ℤ) ∣ (x.val : ℤ) * m - n))]
  rw [card_dvd_mul_sub n x.val]

lemma card_Xc_sum (n : ℤ) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q] (hq : q = c.natAbs * M) :
    (univ.filter fun z : ZMod q × ZMod q => Xc n c z).card =
      ∑ x : ZMod q, M * gf n (Nat.gcd c.natAbs x.val) := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← card_fib_x n hc hq x, Finset.card_filter]

omit [NeZero M] in
lemma sum_range_gcd (k : ℕ) (hk : 0 < k) (f : ℕ → ℕ) :
    ∑ a ∈ range k, f (Nat.gcd k a) = ∑ h ∈ k.divisors, Nat.totient (k / h) * f h := by
  rw [← Finset.sum_fiberwise_of_maps_to' (s := range k) (t := k.divisors)
    (g := fun a => Nat.gcd k a) (fun a _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left k a, hk.ne'⟩) f]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.sum_const, smul_eq_mul, Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hh)]

omit [NeZero M] in
lemma sum_gf_eq_Nk (n : ℤ) (k : ℕ) (hk : 0 < k) :
    ∑ a ∈ range k, gf n (Nat.gcd k a) = Nk n k := by
  rw [sum_range_gcd k hk, Nk, Finset.sum_filter]
  refine Finset.sum_congr rfl fun h _ => ?_
  unfold gf
  split_ifs <;> ring

theorem card_Xc_eq_Nk (n : ℤ) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q] (hq : q = c.natAbs * M) :
    (univ.filter fun z : ZMod q × ZMod q => Xc n c z).card = M * M * Nk n c.natAbs := by
  have hc0 : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  have h1 : ∑ x : ZMod q, M * gf n (Nat.gcd c.natAbs x.val) =
      ∑ u ∈ range q, M * gf n (Nat.gcd c.natAbs u) :=
    sum_zmod_val' (fun a => M * gf n (Nat.gcd c.natAbs a))
  have h2 : ∑ u ∈ range (c.natAbs * M), M * gf n (Nat.gcd c.natAbs u) =
      M * ∑ u ∈ range c.natAbs, M * gf n (Nat.gcd c.natAbs u) :=
    sum_range_mul_of_periodic' (G := fun u => M * gf n (Nat.gcd c.natAbs u))
      (fun a => by simp only [Nat.gcd_add_self_right]) M
  rw [card_Xc_sum n hc hq, h1, hq, h2, ← Finset.mul_sum, sum_gf_eq_Nk n _ hc0]
  ring

end RamanujanPetersson.EllW2


