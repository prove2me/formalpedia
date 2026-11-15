-- Prove2me | Definitions.Def_RPLib_S3_EllW2K2c
-- name    : RPLib_S3_EllW2K2c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:53:46.496957+00:00
-- url     : https://prove2.me/theorems/118b1aee-abd7-4c31-aec5-23f70c2d9e25
-- title:
--   The Eichler-Selberg trace formula in weight two: the Fourier coefficients of `WcF` through a Kloosterman sum
-- statement:
--   The Fourier coefficients of `WcF` through a Kloosterman sum.
--
--   Split `|c| = A0 · B` with `A0 ⊥ B`, `B ⊥ M`, `n` a unit mod `B`, all primes of `B` at least `11`, and put
--   `q = A0 M B`. By CRT (`ZMod q ≅ ZMod (A0 M) × ZMod B`):
--   * `levelCount_mkT_congr`: `λ(a, t) = levelCount (mkT n (c,t) a)` only depends on `(a, t) mod A0 M`;
--   * `dvd_iff_crt`: `c ∣ a(t-a) - n` iff `A0 ∣ (a mod A0M)(t mod A0M - a mod A0M) - n` and `a(t-a) ≡ n (mod B)`;
--   * `stdAddChar_neg_mul_crt`: `e(-yj/q)` splits into a character mod `A0 M` and one mod `B`;
--   * `norm_hyperbola_le`: the `B`-part is a Kloosterman sum, bounded by `Bnd B j (j n)`;
--   * **`norm_dft_WcF_le`**: `2M ‖dft (WcF c ·) j‖ ≤ #(Fin 2 → ZMod M) · #PA · Bnd B j (j n)`,
--     `PA = {(x, y) ∈ ZMod (A0 M)² : A0 ∣ x(y-x) - n}`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; A. Weil, On some exponential sums, Proc. Nat. Acad. Sci. USA 34 (1948), 204-207; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2K2b

/-!
# S3-ES-Wt2 (O6, file K2c): the Fourier coefficients of `WcF` through a Kloosterman sum

Split `|c| = A0 · B` with `A0 ⊥ B`, `B ⊥ M`, `n` a unit mod `B`, all primes of `B` at least `11`, and put
`q = A0 M B`. By CRT (`ZMod q ≅ ZMod (A0 M) × ZMod B`):
* `levelCount_mkT_congr`: `λ(a, t) = levelCount (mkT n (c,t) a)` only depends on `(a, t) mod A0 M`;
* `dvd_iff_crt`: `c ∣ a(t-a) - n` iff `A0 ∣ (a mod A0M)(t mod A0M - a mod A0M) - n` and `a(t-a) ≡ n (mod B)`;
* `stdAddChar_neg_mul_crt`: `e(-yj/q)` splits into a character mod `A0 M` and one mod `B`;
* `norm_hyperbola_le`: the `B`-part is a Kloosterman sum, bounded by `Bnd B j (j n)`;
* **`norm_dft_WcF_le`**: `2M ‖dft (WcF c ·) j‖ ≤ #(Fin 2 → ZMod M) · #PA · Bnd B j (j n)`,
  `PA = {(x, y) ∈ ZMod (A0 M)² : A0 ∣ x(y-x) - n}`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-- `levelCount (mkT n (c,t) a)` only depends on `(a, t) mod A0 M` when `|c| = A0 B` and `B ⊥ M`. -/
lemma levelCount_mkT_congr (δ' : ZMod M) (n : ℤ) {c : ℤ} (hc : c ≠ 0) {A0 B : ℕ}
    (hAB : c.natAbs = A0 * B) (hA0 : A0 ≠ 0) (hBM : B.Coprime M) {a t a' t' : ℤ}
    (h1 : c ∣ a * (t - a) - n) (h2 : c ∣ a' * (t' - a') - n)
    (ha : ((A0 * M : ℕ) : ℤ) ∣ a' - a) (ht : ((A0 * M : ℕ) : ℤ) ∣ t' - t) :
    S3.levelCount M δ' (mkT n (c, t) a) = S3.levelCount M δ' (mkT n (c, t') a') := by
  obtain ⟨b, hb⟩ := h1
  obtain ⟨b', hb'⟩ := h2
  have hMA : (M : ℤ) ∣ ((A0 * M : ℕ) : ℤ) := by push_cast; exact dvd_mul_left _ _
  have hD : ((A0 * M : ℕ) : ℤ) ∣ c * (b' - b) := by
    rw [mul_sub, ← hb, ← hb']
    rw [show a' * (t' - a') - n - (a * (t - a) - n) =
      (a' - a) * (t' - a') + a * ((t' - t) - (a' - a)) by ring]
    exact dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right (dvd_sub ht ha) _)
  have hD' : (A0 : ℤ) * M ∣ (A0 : ℤ) * (B * (b' - b)) := by
    have e : c * (b' - b) = (A0 : ℤ) * (B * (b' - b)) ∨
        c * (b' - b) = -((A0 : ℤ) * (B * (b' - b))) := by
      rcases Int.natAbs_eq c with h | h
      · left; rw [h, hAB]; push_cast; ring
      · right; rw [h, hAB]; push_cast; ring
    push_cast at hD
    rcases e with e | e
    · rwa [e] at hD
    · rwa [e, dvd_neg] at hD
  have hA0' : (A0 : ℤ) ≠ 0 := by exact_mod_cast hA0
  have hMB : (M : ℤ) ∣ B * (b' - b) := (mul_dvd_mul_iff_left hA0').1 hD'
  have hMb : (M : ℤ) ∣ b' - b :=
    IsCoprime.dvd_of_dvd_mul_left (Nat.isCoprime_iff_coprime.2 hBM.symm) hMB
  have ea : (a : ZMod M) = a' := (ZMod.intCast_eq_intCast_iff_dvd_sub a a' M).2 (hMA.trans ha)
  have et : (t : ZMod M) = t' := (ZMod.intCast_eq_intCast_iff_dvd_sub t t' M).2 (hMA.trans ht)
  have eb : (b : ZMod M) = b' := (ZMod.intCast_eq_intCast_iff_dvd_sub b b' M).2 hMb
  have m1 : mkT n (c, t) a = !![a, b; c, t - a] := by
    simp only [mkT]; rw [hb, Int.mul_ediv_cancel_left b hc]
  have m2 : mkT n (c, t') a' = !![a', b'; c, t' - a'] := by
    simp only [mkT]; rw [hb', Int.mul_ediv_cancel_left b' hc]
  have hmap : (mkT n (c, t) a).map (Int.castRingHom (ZMod M)) =
      (mkT n (c, t') a').map (Int.castRingHom (ZMod M)) := by
    rw [m1, m2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ea, et, eb]
  unfold S3.levelCount
  rw [hmap]

/-! ## The CRT projections -/

/-- `ZMod (A B) → ZMod A`. -/
def crtA (A B : ℕ) : ZMod (A * B) →+* ZMod A := ZMod.castHom (Dvd.intro B rfl) (ZMod A)

/-- `ZMod (A B) → ZMod B`. -/
def crtB (A B : ℕ) : ZMod (A * B) →+* ZMod B := ZMod.castHom (Dvd.intro_left A rfl) (ZMod B)

omit [NeZero M] in
lemma val_crtA {A B : ℕ} [NeZero A] [NeZero B] (x : ZMod (A * B)) : (crtA A B x).val = x.val % A := by
  rw [crtA, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

omit [NeZero M] in
lemma crtB_apply {A B : ℕ} [NeZero A] [NeZero B] (x : ZMod (A * B)) : crtB A B x = (x.val : ZMod B) := by
  rw [crtB, ZMod.castHom_apply, ZMod.cast_eq_val]

omit [NeZero M] in
lemma crt_bijective {A B : ℕ} [NeZero A] [NeZero B] (h : A.Coprime B) :
    Function.Bijective fun x : ZMod (A * B) => (crtA A B x, crtB A B x) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun x y hxy => ?_, ?_⟩
  · simp only [Prod.mk.injEq] at hxy
    exact KL.crt_injective h hxy.1 hxy.2
  · rw [Fintype.card_prod, ZMod.card, ZMod.card, ZMod.card]

omit [NeZero M] in
lemma stdAddChar_neg_mul_crt {A B : ℕ} [NeZero A] [NeZero B] {α β : ℤ} (hab : α * B + β * A = 1)
    (j y : ZMod (A * B)) :
    (ZMod.stdAddChar (-(y * j)) : ℂ) =
      (ZMod.stdAddChar ((-((α : ZMod A) * crtA A B j)) * crtA A B y) : ℂ) *
        (ZMod.stdAddChar ((-((β : ZMod B) * crtB A B j)) * crtB A B y) : ℂ) := by
  rw [KL.stdAddChar_crt hab]
  simp only [crtA, crtB, map_neg, map_mul]
  congr 2 <;> ring

lemma dvd_iff_crt (n : ℤ) {c : ℤ} {A0 B : ℕ} [NeZero A0] [NeZero B] (hAB : c.natAbs = A0 * B)
    (hcop : A0.Coprime B) (x y : ZMod (A0 * M * B)) :
    c ∣ (x.val : ℤ) * ((y.val : ℤ) - x.val) - n ↔
      (A0 : ℤ) ∣ ((crtA (A0 * M) B x).val : ℤ) * (((crtA (A0 * M) B y).val : ℤ) -
          (crtA (A0 * M) B x).val) - n ∧
        crtB (A0 * M) B x * (crtB (A0 * M) B y - crtB (A0 * M) B x) = (n : ZMod B) := by
  have hmod : ∀ z : ZMod (A0 * M * B), ((crtA (A0 * M) B z).val : ZMod A0) = (z.val : ZMod A0) := by
    intro z
    rw [val_crtA, ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd _ (dvd_mul_right A0 M)]
  rw [← Int.natAbs_dvd, hAB, Nat.cast_mul]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 : (A0 : ℤ) ∣ (x.val : ℤ) * ((y.val : ℤ) - x.val) - n := (dvd_mul_right _ _).trans h
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 ⊢
      push_cast at h1 ⊢
      rw [hmod, hmod]; exact h1
    · have h2 : (B : ℤ) ∣ (x.val : ℤ) * ((y.val : ℤ) - x.val) - n := (dvd_mul_left _ _).trans h
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
      push_cast at h2
      rw [crtB_apply, crtB_apply]; exact sub_eq_zero.1 h2
  · rintro ⟨h1, h2⟩
    refine IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.2 hcop) ?_ ?_
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 ⊢
      push_cast at h1 ⊢
      rw [hmod, hmod] at h1; exact h1
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [crtB_apply, crtB_apply] at h2; exact sub_eq_zero.2 h2

omit [NeZero M] in
/-- The `B`-part: a Kloosterman sum. -/
lemma norm_hyperbola_le {B : ℕ} [NeZero B] (hB : ∀ p ∈ B.primeFactors, 11 ≤ p) {n : ℤ}
    (hn : IsUnit (n : ZMod B)) {β : ZMod B} (hβ : IsUnit β) {w : ZMod B} (k : ℕ) (hw : w = (k : ZMod B)) :
    ‖∑ x2 : ZMod B, ∑ y2 : ZMod B,
        (if x2 * (y2 - x2) = (n : ZMod B) then (ZMod.stdAddChar ((-(β * w)) * y2) : ℂ) else 0)‖ ≤
      KL.Bnd B k (k * n) := by
  subst hw
  rw [sum_hyperbola_eq_kl hn]
  have e1 : -(β * (k : ZMod B)) = (-β) * (((k : ℤ)) : ZMod B) := by push_cast; ring
  have e2 : -(β * (k : ZMod B)) * (n : ZMod B) = (-β) * (((k : ℤ) * n : ℤ) : ZMod B) := by
    push_cast; ring
  rw [e2, e1]
  exact KL.norm_kl_le_Bnd _ _ B (NeZero.ne B) hB _ hβ.neg

/-- **The Fourier coefficients of `WcF c ·`** (period `q = A0 M B = |c| M`). -/
theorem norm_dft_WcF_le (n : ℤ) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) {A0 B : ℕ} [NeZero A0] [NeZero B]
    (hAB : c.natAbs = A0 * B) (hcop : A0.Coprime B) (hBM : B.Coprime M) (hnB : IsUnit (n : ZMod B))
    (h11 : ∀ p ∈ B.primeFactors, 11 ≤ p) (j : ZMod (A0 * M * B)) :
    2 * (M : ℝ) * ‖ZMod.dft (fun x : ZMod (A0 * M * B) => WcF M n δ' c (x.val : ℤ)) j‖ ≤
      (Fintype.card (Fin 2 → ZMod M) : ℝ) *
        ((univ.filter fun p : ZMod (A0 * M) × ZMod (A0 * M) =>
          (A0 : ℤ) ∣ (p.1.val : ℤ) * ((p.2.val : ℤ) - p.1.val) - n).card : ℝ) *
        KL.Bnd B (j.val : ℤ) ((j.val : ℤ) * n) := by
  have hq : A0 * M * B = c.natAbs * M := by rw [hAB]; ring
  have hcop' : (A0 * M).Coprime B := Nat.Coprime.mul_left hcop hBM.symm
  obtain ⟨α, β, hαβ⟩ : IsCoprime (B : ℤ) ((A0 * M : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 hcop'.symm
  have hab : α * B + β * ((A0 * M : ℕ) : ℤ) = 1 := hαβ
  have hβ : IsUnit (β : ZMod B) := by
    refine IsUnit.of_mul_eq_one ((A0 * M : ℕ) : ZMod B) ?_
    have := congrArg (fun z : ℤ => (z : ZMod B)) hab
    push_cast at this
    simpa using this
  have hlam : ∀ x y x' y' : ZMod (A0 * M * B),
      c ∣ (x.val : ℤ) * ((y.val : ℤ) - x.val) - n →
      c ∣ (x'.val : ℤ) * ((y'.val : ℤ) - x'.val) - n →
      crtA (A0 * M) B x = crtA (A0 * M) B x' → crtA (A0 * M) B y = crtA (A0 * M) B y' →
      (S3.levelCount M δ' (mkT n (c, (y.val : ℤ)) (x.val : ℤ)) : ℂ) =
        (S3.levelCount M δ' (mkT n (c, (y'.val : ℤ)) (x'.val : ℤ)) : ℂ) := by
    intro x y x' y' h1 h2 hx hy
    have hd : ∀ z z' : ZMod (A0 * M * B), crtA (A0 * M) B z = crtA (A0 * M) B z' →
        ((A0 * M : ℕ) : ℤ) ∣ (z'.val : ℤ) - z.val := by
      intro z z' h
      have h' := congrArg ZMod.val h
      rw [val_crtA, val_crtA] at h'
      exact Nat.modEq_iff_dvd.1 h'
    rw [levelCount_mkT_congr δ' n hc hAB (NeZero.ne A0) hBM h1 h2 (hd x x' hx) (hd y y' hy)]
  have hL : ∀ x y : ZMod (A0 * M * B),
      ‖(S3.levelCount M δ' (mkT n (c, (y.val : ℤ)) (x.val : ℤ)) : ℂ)‖ ≤
        (Fintype.card (Fin 2 → ZMod M) : ℝ) := by
    intro x y
    rw [Complex.norm_natCast]
    exact levelCount_le δ' _
  have key := norm_sum_factor_le (crtA (A0 * M) B) (crtB (A0 * M) B) (crt_bijective hcop')
    (fun x y : ZMod (A0 * M * B) => c ∣ (x.val : ℤ) * ((y.val : ℤ) - x.val) - n)
    (fun x1 y1 : ZMod (A0 * M) => (A0 : ℤ) ∣ (x1.val : ℤ) * ((y1.val : ℤ) - x1.val) - n)
    (fun x2 y2 : ZMod B => x2 * (y2 - x2) = (n : ZMod B)) (dvd_iff_crt n hAB hcop)
    (fun x y : ZMod (A0 * M * B) => (S3.levelCount M δ' (mkT n (c, (y.val : ℤ)) (x.val : ℤ)) : ℂ))
    hlam (fun y : ZMod (A0 * M * B) => (ZMod.stdAddChar (-(y * j)) : ℂ))
    (fun y1 => (ZMod.stdAddChar ((-((α : ZMod (A0 * M)) * crtA (A0 * M) B j)) * y1) : ℂ))
    (fun y2 => (ZMod.stdAddChar ((-((β : ZMod B) * crtB (A0 * M) B j)) * y2) : ℂ))
    (fun y => stdAddChar_neg_mul_crt hab j y) (by positivity) hL (fun y => KL.norm_stdAddChar _ _)
  have h2M : ‖(2 * (M : ℂ))‖ = 2 * (M : ℝ) := by
    rw [show (2 * (M : ℂ)) = ((2 * M : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  rw [← h2M, ← norm_mul, dft_WcF_eq n δ' hc hq j]
  refine key.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact norm_hyperbola_le h11 hnB hβ j.val (crtB_apply j)

end RamanujanPetersson.EllW2


