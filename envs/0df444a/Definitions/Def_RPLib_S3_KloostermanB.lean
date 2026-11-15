-- Prove2me | Definitions.Def_RPLib_S3_KloostermanB
-- name    : RPLib_S3_KloostermanB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:26:12.120196+00:00
-- url     : https://prove2.me/theorems/f3ce1308-7333-4c02-b404-3d8a3c9484b6
-- title:
--   The Eichler-Selberg trace formula in weight two: CRT for (restricted) Kloosterman sums and the multiplicative bound
-- statement:
--   CRT for (restricted) Kloosterman sums and the multiplicative bound.
--
--   * `klR M c u m r = Σ_{x ∈ (ℤ/c)ˣ, x ≡ u (M)} e((m x + r x⁻¹)/c)`; `klR_one`; `norm_klR_le` (`≤ c`).
--   * `stdAddChar_crt`, `crt_injective`, `units_crt_bijective`, `sum_units_crt`, `klR_crt` (for `M ∣ c1`, `c1 ⊥ c2`,
--     `α c2 + β c1 = 1`: `klR M (c1 c2) u m r = klR M c1 u (α m) (α r) * kl c2 (β m) (β r)`), `kl_crt`.
--   * `bp`, `Bnd n m r = Π_{p ∣ n} bp p (v_p n) m r` (`p^(7/8)` or `p` at `v_p = 1`, `p^e` at `v_p = e ≥ 2`), `Bnd_mul`,
--     `norm_kl_le_Bnd` (all prime factors of `n` at least 11, `v` a unit: `‖kl n (v m) (v r)‖ ≤ Bnd n m r`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; A. Weil, On some exponential sums, Proc. Nat. Acad. Sci. USA 34 (1948), 204-207; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_KloostermanA

/-!
# S3-ES-Wt2 (O4, KL_B): CRT for (restricted) Kloosterman sums and the multiplicative bound

* `klR M c u m r = Σ_{x ∈ (ℤ/c)ˣ, x ≡ u (M)} e((m x + r x⁻¹)/c)`; `klR_one`; `norm_klR_le` (`≤ c`).
* `stdAddChar_crt`, `crt_injective`, `units_crt_bijective`, `sum_units_crt`, `klR_crt` (for `M ∣ c1`, `c1 ⊥ c2`,
  `α c2 + β c1 = 1`: `klR M (c1 c2) u m r = klR M c1 u (α m) (α r) * kl c2 (β m) (β r)`), `kl_crt`.
* `bp`, `Bnd n m r = Π_{p ∣ n} bp p (v_p n) m r` (`p^(7/8)` or `p` at `v_p = 1`, `p^e` at `v_p = e ≥ 2`), `Bnd_mul`,
  `norm_kl_le_Bnd` (all prime factors of `n` at least 11, `v` a unit: `‖kl n (v m) (v r)‖ ≤ Bnd n m r`).

-/

open Finset
open scoped ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KL

instance neZero_mul' {a b : ℕ} [NeZero a] [NeZero b] : NeZero (a * b) :=
  ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩

/-- Restricted Kloosterman sum `Σ_{x ∈ (ℤ/c)ˣ, x ≡ u (M)} e((m x + r x⁻¹)/c)`. -/
def klR (M c : ℕ) [NeZero c] (u : ZMod M) (m r : ZMod c) : ℂ :=
  ∑ x : (ZMod c)ˣ, if (ZMod.cast (x : ZMod c) : ZMod M) = u then
    (ZMod.stdAddChar (m * (x : ZMod c) + r * (x : ZMod c)⁻¹) : ℂ) else 0

lemma klR_one (c : ℕ) [NeZero c] (u : ZMod 1) (m r : ZMod c) : klR 1 c u m r = kl c m r := by
  unfold klR kl
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [if_pos (Subsingleton.elim _ _)]

lemma norm_klR_le (M c : ℕ) [NeZero c] (u : ZMod M) (m r : ZMod c) : ‖klR M c u m r‖ ≤ c := by
  unfold klR
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x : (ZMod c)ˣ, ‖(if (ZMod.cast (x : ZMod c) : ZMod M) = u then
        (ZMod.stdAddChar (m * (x : ZMod c) + r * (x : ZMod c)⁻¹) : ℂ) else 0)‖
      ≤ ∑ _x : (ZMod c)ˣ, (1 : ℝ) := Finset.sum_le_sum (fun x _ => by
        split_ifs <;> simp)
    _ = Fintype.card (ZMod c)ˣ := by simp
    _ ≤ c := by
        rw [ZMod.card_units_eq_totient]; exact_mod_cast Nat.totient_le c

section CRT

variable {n1 n2 : ℕ}

lemma stdAddChar_crt [NeZero n1] [NeZero n2] {α β : ℤ} (hab : α * n2 + β * n1 = 1)
    (t : ZMod (n1 * n2)) :
    (ZMod.stdAddChar t : ℂ) =
      ZMod.stdAddChar ((α : ZMod n1) * ZMod.castHom (Dvd.intro n2 rfl) (ZMod n1) t) *
      ZMod.stdAddChar ((β : ZMod n2) * ZMod.castHom (Dvd.intro_left n1 rfl) (ZMod n2) t) := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective t
  have e1 : ZMod.castHom (Dvd.intro n2 rfl) (ZMod n1) (k : ZMod (n1 * n2)) = (k : ZMod n1) :=
    map_intCast _ k
  have e2 : ZMod.castHom (Dvd.intro_left n1 rfl) (ZMod n2) (k : ZMod (n1 * n2)) = (k : ZMod n2) :=
    map_intCast _ k
  rw [e1, e2, ← Int.cast_mul, ← Int.cast_mul, ZMod.stdAddChar_coe,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have h1 : (n1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n1)
  have h2 : (n2 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n2)
  have hab' : (α : ℂ) * n2 + β * n1 = 1 := by exact_mod_cast hab
  rw [Nat.cast_mul, div_add_div _ _ h1 h2, div_left_inj' (mul_ne_zero h1 h2)]
  push_cast
  linear_combination (-(2 * (Real.pi : ℂ) * Complex.I * k)) * hab'

lemma crt_injective [NeZero n1] [NeZero n2] (h : n1.Coprime n2) {x y : ZMod (n1 * n2)}
    (h1 : ZMod.castHom (Dvd.intro n2 rfl) (ZMod n1) x = ZMod.castHom (Dvd.intro n2 rfl) (ZMod n1) y)
    (h2 : ZMod.castHom (Dvd.intro_left n1 rfl) (ZMod n2) x =
      ZMod.castHom (Dvd.intro_left n1 rfl) (ZMod n2) y) : x = y := by
  have hx : ∀ z : ZMod (n1 * n2), ∀ d (hd : d ∣ n1 * n2),
      ZMod.castHom hd (ZMod d) z = ((z.val : ℕ) : ZMod d) := by
    intro z d hd; rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [hx, hx, ZMod.natCast_eq_natCast_iff] at h1 h2
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, ZMod.natCast_eq_natCast_iff]
  exact (Nat.modEq_and_modEq_iff_modEq_mul h).1 ⟨h1, h2⟩

lemma units_crt_bijective [NeZero n1] [NeZero n2] (h : n1.Coprime n2) :
    Function.Bijective (fun x : (ZMod (n1 * n2))ˣ =>
      (ZMod.unitsMap (Dvd.intro n2 rfl) x, ZMod.unitsMap (Dvd.intro_left n1 rfl) x)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun x y hxy => Units.ext ?_, ?_⟩
  · simp only [Prod.mk.injEq] at hxy
    exact crt_injective h (congrArg Units.val hxy.1) (congrArg Units.val hxy.2)
  · rw [Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient,
      ZMod.card_units_eq_totient, Nat.totient_mul h]

lemma sum_units_crt [NeZero n1] [NeZero n2] (h : n1.Coprime n2)
    (F : (ZMod n1)ˣ → (ZMod n2)ˣ → ℂ) :
    ∑ x : (ZMod (n1 * n2))ˣ,
        F (ZMod.unitsMap (Dvd.intro n2 rfl) x) (ZMod.unitsMap (Dvd.intro_left n1 rfl) x) =
      ∑ x1 : (ZMod n1)ˣ, ∑ x2 : (ZMod n2)ˣ, F x1 x2 := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_bijective _ (units_crt_bijective h) _ _ (fun x => rfl)

lemma castHom_inv_unit {n d : ℕ} (hd : d ∣ n) (x : (ZMod n)ˣ) :
    ZMod.castHom hd (ZMod d) ((x : ZMod n)⁻¹) = ((ZMod.unitsMap hd x : (ZMod d)ˣ) : ZMod d)⁻¹ := by
  rw [ZMod.inv_coe_unit, ZMod.inv_coe_unit, ← map_inv]
  rfl

lemma cast_castHom {M c1 c : ℕ} (hM : M ∣ c1) (h1 : c1 ∣ c) (x : ZMod c) :
    (ZMod.cast (ZMod.castHom h1 (ZMod c1) x) : ZMod M) = ZMod.cast x := by
  have := RingHom.congr_fun (ZMod.castHom_comp hM h1) x
  simp only [RingHom.comp_apply, ZMod.castHom_apply] at this
  simpa only [ZMod.castHom_apply] using this

end CRT

theorem klR_crt {M c1 c2 : ℕ} [NeZero c1] [NeZero c2] (hM : M ∣ c1) (hc : c1.Coprime c2)
    {α β : ℤ} (hab : α * c2 + β * c1 = 1) (u : ZMod M) (m r : ZMod (c1 * c2)) :
    klR M (c1 * c2) u m r =
      klR M c1 u ((α : ZMod c1) * ZMod.castHom (Dvd.intro c2 rfl) (ZMod c1) m)
        ((α : ZMod c1) * ZMod.castHom (Dvd.intro c2 rfl) (ZMod c1) r) *
      kl c2 ((β : ZMod c2) * ZMod.castHom (Dvd.intro_left c1 rfl) (ZMod c2) m)
        ((β : ZMod c2) * ZMod.castHom (Dvd.intro_left c1 rfl) (ZMod c2) r) := by
  unfold klR kl
  rw [Finset.sum_mul_sum]
  refine Eq.trans ?_ (sum_units_crt hc (fun x1 x2 =>
    (if (ZMod.cast (x1 : ZMod c1) : ZMod M) = u then
      (ZMod.stdAddChar ((α : ZMod c1) * ZMod.castHom (Dvd.intro c2 rfl) (ZMod c1) m * (x1 : ZMod c1) +
        (α : ZMod c1) * ZMod.castHom (Dvd.intro c2 rfl) (ZMod c1) r * (x1 : ZMod c1)⁻¹) : ℂ) else 0) *
      ZMod.stdAddChar ((β : ZMod c2) * ZMod.castHom (Dvd.intro_left c1 rfl) (ZMod c2) m * (x2 : ZMod c2) +
        (β : ZMod c2) * ZMod.castHom (Dvd.intro_left c1 rfl) (ZMod c2) r * (x2 : ZMod c2)⁻¹)))
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hx1 : ZMod.castHom (Dvd.intro c2 rfl) (ZMod c1) (x : ZMod (c1 * c2)) =
      ((ZMod.unitsMap (Dvd.intro c2 rfl) x : (ZMod c1)ˣ) : ZMod c1) := rfl
  have hx2 : ZMod.castHom (Dvd.intro_left c1 rfl) (ZMod c2) (x : ZMod (c1 * c2)) =
      ((ZMod.unitsMap (Dvd.intro_left c1 rfl) x : (ZMod c2)ˣ) : ZMod c2) := rfl
  have hcond : (ZMod.cast ((ZMod.unitsMap (Dvd.intro c2 rfl) x : (ZMod c1)ˣ) : ZMod c1) : ZMod M) =
      ZMod.cast (x : ZMod (c1 * c2)) := by
    rw [← hx1]; exact cast_castHom hM (Dvd.intro c2 rfl) (x : ZMod (c1 * c2))
  rw [hcond]
  split_ifs with hu
  · rw [stdAddChar_crt hab]
    congr 2
    · rw [map_add, map_mul, map_mul, castHom_inv_unit, hx1]; ring
    · rw [map_add, map_mul, map_mul, castHom_inv_unit, hx2]; ring
  · rw [zero_mul]

theorem kl_crt {c1 c2 : ℕ} [NeZero c1] [NeZero c2] (hc : c1.Coprime c2)
    {α β : ℤ} (hab : α * c2 + β * c1 = 1) (m r : ZMod (c1 * c2)) :
    kl (c1 * c2) m r =
      kl c1 ((α : ZMod c1) * ZMod.castHom (Dvd.intro c2 rfl) (ZMod c1) m)
        ((α : ZMod c1) * ZMod.castHom (Dvd.intro c2 rfl) (ZMod c1) r) *
      kl c2 ((β : ZMod c2) * ZMod.castHom (Dvd.intro_left c1 rfl) (ZMod c2) m)
        ((β : ZMod c2) * ZMod.castHom (Dvd.intro_left c1 rfl) (ZMod c2) r) := by
  rw [← klR_one (c1 * c2) 0, klR_crt (one_dvd c1) hc hab, klR_one]

/-! ### The multiplicative bound -/

/-- Local factor: `p` or `p^(7/8)` at exponent 1 (according as `p ∣ (m, r)`), `p^e` otherwise. -/
def bp (p e : ℕ) (m r : ℤ) : ℝ :=
  if e = 1 then (if (p : ℤ) ∣ m ∧ (p : ℤ) ∣ r then (p : ℝ) else (p : ℝ) ^ ((7 : ℝ) / 8))
  else (p : ℝ) ^ e

def Bnd (n : ℕ) (m r : ℤ) : ℝ := ∏ p ∈ n.primeFactors, bp p (n.factorization p) m r

lemma bp_nonneg (p e : ℕ) (m r : ℤ) : 0 ≤ bp p e m r := by
  unfold bp; split_ifs <;> positivity

lemma Bnd_nonneg (n : ℕ) (m r : ℤ) : 0 ≤ Bnd n m r :=
  Finset.prod_nonneg (fun _ _ => bp_nonneg _ _ _ _)

lemma Bnd_one (m r : ℤ) : Bnd 1 m r = 1 := by simp [Bnd]

lemma Bnd_prime_pow {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) (m r : ℤ) : Bnd (p ^ e) m r = bp p e m r := by
  rw [Bnd, Nat.primeFactors_prime_pow he hp, Finset.prod_singleton, Nat.factorization_pow,
    Finsupp.smul_apply, hp.factorization_self, smul_eq_mul, mul_one]

lemma Bnd_mul {a b : ℕ} (h : a.Coprime b) (m r : ℤ) : Bnd (a * b) m r = Bnd a m r * Bnd b m r := by
  unfold Bnd
  rw [Nat.Coprime.primeFactors_mul h, Finset.prod_union h.disjoint_primeFactors]
  congr 1
  · refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpb : p ∉ b.primeFactors := Finset.disjoint_left.1 h.disjoint_primeFactors hp
    have : b.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
    rw [Nat.factorization_mul_of_coprime h, Finsupp.add_apply, this, add_zero]
  · refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpa : p ∉ a.primeFactors := Finset.disjoint_right.1 h.disjoint_primeFactors hp
    have : a.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
    rw [Nat.factorization_mul_of_coprime h, Finsupp.add_apply, this, zero_add]

lemma norm_kl_le_card (n : ℕ) [NeZero n] (m r : ZMod n) : ‖kl n m r‖ ≤ n := by
  refine (norm_kl_le n m r).trans ?_
  rw [ZMod.card_units_eq_totient]; exact_mod_cast Nat.totient_le n

lemma norm_kl_prime_le {q : ℕ} [Fact q.Prime] (hq : 11 ≤ q) (m r : ℤ) (v : ZMod q) (hv : IsUnit v) :
    ‖kl q (v * m) (v * r)‖ ≤ bp q 1 m r := by
  unfold bp
  rw [if_pos rfl]
  split_ifs with hd
  · exact (norm_kl_le_pred _ _).trans (by linarith)
  · refine norm_kl_le_rpow (by omega) ?_
    by_contra hc
    push_neg at hc
    apply hd
    rw [hv.mul_right_eq_zero, hv.mul_right_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd,
      ZMod.intCast_zmod_eq_zero_iff_dvd] at hc
    exact hc

theorem norm_kl_le_Bnd (m r : ℤ) : ∀ (n : ℕ) (hn0 : n ≠ 0), (∀ p ∈ n.primeFactors, 11 ≤ p) →
    ∀ (v : ZMod n), IsUnit v →
      ‖@kl n ⟨hn0⟩ (v * m) (v * r)‖ ≤ Bnd n m r := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd rfl h
  | one =>
      intro hn0 _ v _
      have : NeZero (1 : ℕ) := ⟨hn0⟩
      rw [Bnd_one]
      refine (norm_kl_le 1 _ _).trans ?_
      simp
  | prime_pow p e hp he =>
      intro hn0 hpf v hv
      have : NeZero (p ^ e) := ⟨hn0⟩
      rw [Bnd_prime_pow hp (by omega)]
      have hp11 : 11 ≤ p := hpf p (by
        rw [Nat.primeFactors_prime_pow (by omega) hp]; exact Finset.mem_singleton_self p)
      by_cases he1 : e = 1
      · subst he1
        have : Fact (p ^ 1).Prime := ⟨by rw [pow_one]; exact hp⟩
        have h := norm_kl_prime_le (q := p ^ 1) (by rw [pow_one]; exact hp11) m r v hv
        simpa only [bp, pow_one] using h
      · unfold bp
        rw [if_neg he1]
        refine (norm_kl_le_card _ _ _).trans ?_
        push_cast; exact le_rfl
  | coprime a b ha hb hab iha ihb =>
      intro hn0 hpf v hv
      have : NeZero a := ⟨by omega⟩
      have : NeZero b := ⟨by omega⟩
      obtain ⟨α, β, hαβ⟩ : IsCoprime (b : ℤ) (a : ℤ) := Nat.isCoprime_iff_coprime.2 hab.symm
      have hαβ' : α * b + β * a = 1 := hαβ
      rw [kl_crt hab hαβ', norm_mul, Bnd_mul hab]
      have hpf' : ∀ p ∈ (a * b).primeFactors, 11 ≤ p := hpf
      rw [Nat.Coprime.primeFactors_mul hab] at hpf'
      have hua : IsUnit ((α : ZMod a)) := by
        refine IsUnit.of_mul_eq_one (b : ZMod a) ?_
        have := congrArg (fun z : ℤ => (z : ZMod a)) hαβ'
        push_cast at this
        simpa using this
      have hub : IsUnit ((β : ZMod b)) := by
        refine IsUnit.of_mul_eq_one (a : ZMod b) ?_
        have := congrArg (fun z : ℤ => (z : ZMod b)) hαβ'
        push_cast at this
        simpa using this
      refine mul_le_mul ?_ ?_ (norm_nonneg _) (Bnd_nonneg _ _ _)
      · have h := iha (by omega) (fun p hp => hpf' p (Finset.mem_union_left _ hp))
          ((α : ZMod a) * ZMod.castHom (Dvd.intro b rfl) (ZMod a) v)
          (hua.mul (hv.map _))
        have e : ∀ t : ℤ, (α : ZMod a) * ZMod.castHom (Dvd.intro b rfl) (ZMod a) (v * (t : ZMod (a * b))) =
            ((α : ZMod a) * ZMod.castHom (Dvd.intro b rfl) (ZMod a) v) * (t : ZMod a) := by
          intro t; rw [map_mul, map_intCast, mul_assoc]
        rw [e, e]; exact h
      · have h := ihb (by omega) (fun p hp => hpf' p (Finset.mem_union_right _ hp))
          ((β : ZMod b) * ZMod.castHom (Dvd.intro_left a rfl) (ZMod b) v)
          (hub.mul (hv.map _))
        have e : ∀ t : ℤ, (β : ZMod b) * ZMod.castHom (Dvd.intro_left a rfl) (ZMod b) (v * (t : ZMod (a * b))) =
            ((β : ZMod b) * ZMod.castHom (Dvd.intro_left a rfl) (ZMod b) v) * (t : ZMod b) := by
          intro t; rw [map_mul, map_intCast, mul_assoc]
        rw [e, e]; exact h

end RamanujanPetersson.KL


