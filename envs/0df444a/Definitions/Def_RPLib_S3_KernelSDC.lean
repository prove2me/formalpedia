-- Prove2me | Definitions.Def_RPLib_S3_KernelSDC
-- name    : RPLib_S3_KernelSDC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:32:29.026565+00:00
-- url     : https://prove2.me/theorems/e2eaacd1-ffb8-4900-8e49-6e7a835567d0
-- title:
--   The Eichler-Selberg trace formula in weight two: the MAIN sum regrouped into `Γ(M)`-classes (finite-sum form)
-- statement:
--   The MAIN sum regrouped into `Γ(M)`-classes (finite-sum form).
--
--   * `Tp M`: `c > 0`, `M ∣ c`, `M c ∣ a d - 1`; `chi M a = 1[a ≡ 1] + 1[a ≡ -1]` (mod `M`).
--   * `tsum_Tset_fold`: `Σ_{Tset} f = Σ_σ chi · f (Psi σ)` for `f(-p) = f(p)`, where
--     `Psi : (Σ c', (ZMod L)ˣ × ℤ × ℤ) → ℤ³`, `(c', x, i, j) ↦ (C, val x + L i, val x⁻¹ + L j)`,
--     `C = M (c'+1)`, `L = M C`, is injective with range `Tp M`.
--   * `Mterm_eq`: `Mterm (c,a,d) = Wt · fz((z + d/c)/M) · fz((w + a/c)/M)`.
--   * `tsum_Mterm_eq_MF`: `Σ_{Tset} Mterm = Σ_{c'} MF c'`,
--     `MF c' = WtR · Σ_x chiU x · Gs s (zeta z (val x⁻¹)) · Gs s (zeta w (val x))`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSDB

/-!
# S3-ES-Wt2, part KS_D (C): the MAIN sum regrouped into `Γ(M)`-classes (finite-sum form)

* `Tp M`: `c > 0`, `M ∣ c`, `M c ∣ a d - 1`; `chi M a = 1[a ≡ 1] + 1[a ≡ -1]` (mod `M`).
* `tsum_Tset_fold`: `Σ_{Tset} f = Σ_σ chi · f (Psi σ)` for `f(-p) = f(p)`, where
  `Psi : (Σ c', (ZMod L)ˣ × ℤ × ℤ) → ℤ³`, `(c', x, i, j) ↦ (C, val x + L i, val x⁻¹ + L j)`,
  `C = M (c'+1)`, `L = M C`, is injective with range `Tp M`.
* `Mterm_eq`: `Mterm (c,a,d) = Wt · fz((z + d/c)/M) · fz((w + a/c)/M)`.
* `tsum_Mterm_eq_MF`: `Σ_{Tset} Mterm = Σ_{c'} MF c'`,
  `MF c' = WtR · Σ_x chiU x · Gs s (zeta z (val x⁻¹)) · Gs s (zeta w (val x))`.
-/

open Complex Filter Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelSD

open RamanujanPetersson.Kernel RamanujanPetersson.KernelS RamanujanPetersson.GSA

/-! ### Folding `c < 0` onto `c > 0` -/

def Tp (M : ℕ) : Set (ℤ × ℤ × ℤ) :=
  {p | 0 < p.1 ∧ (M : ℤ) ∣ p.1 ∧ (M : ℤ) * p.1 ∣ p.2.1 * p.2.2 - 1}

def chi (M : ℕ) (a : ℤ) : ℂ :=
  (if (a : ZMod M) = 1 then 1 else 0) + (if (a : ZMod M) = -1 then 1 else 0)

def Ppos : Set (ℤ × ℤ × ℤ) := {q | 0 < q.1}

lemma Mterm_neg (s : ℝ) (z w : ℂ) (c a d : ℤ) : Mterm s z w (-c, -a, -d) = Mterm s z w (c, a, d) := by
  have h1 : AC z w (-c, -a, -d) = AC z w (c, a, d) := by simp only [AC]; push_cast; ring
  have h2 : etaC z w (-c) = etaC z w c := by simp only [etaC]; push_cast; ring
  simp only [Mterm]; rw [h1, h2]; push_cast; ring

lemma zmod_eq_one_iff (M : ℕ) (a : ℤ) : (a : ZMod M) = 1 ↔ (M : ℤ) ∣ a - 1 := by
  rw [← CharP.intCast_eq_zero_iff (ZMod M) M, Int.cast_sub, Int.cast_one, sub_eq_zero]

lemma zmod_eq_neg_one_iff (M : ℕ) (a : ℤ) : (a : ZMod M) = -1 ↔ (M : ℤ) ∣ -a - 1 := by
  rw [← CharP.intCast_eq_zero_iff (ZMod M) M, Int.cast_sub, Int.cast_neg, Int.cast_one, sub_eq_zero,
    neg_eq_iff_eq_neg]

lemma mem_Tset_pos {M : ℕ} {c a d : ℤ} (hc : 0 < c) :
    (c, a, d) ∈ Tset M ↔ (c, a, d) ∈ Tp M ∧ (a : ZMod M) = 1 := by
  simp only [Tset, Tp, Set.mem_setOf_eq, zmod_eq_one_iff]
  constructor
  · rintro ⟨_, h1, h2, h3⟩; exact ⟨⟨hc, h1, h3⟩, h2⟩
  · rintro ⟨⟨_, h1, h3⟩, h2⟩; exact ⟨hc.ne', h1, h2, h3⟩

lemma mem_Tset_neg {M : ℕ} {c a d : ℤ} (hc : 0 < c) :
    (-c, -a, -d) ∈ Tset M ↔ (c, a, d) ∈ Tp M ∧ (a : ZMod M) = -1 := by
  simp only [Tset, Tp, Set.mem_setOf_eq, neg_ne_zero, dvd_neg, mul_neg, neg_dvd, neg_mul_neg, neg_mul,
    neg_neg, zmod_eq_neg_one_iff]
  constructor
  · rintro ⟨_, h1, h2, h3⟩; exact ⟨⟨hc, h1, h3⟩, h2⟩
  · rintro ⟨⟨_, h1, h3⟩, h2⟩; exact ⟨hc.ne', h1, h2, h3⟩

lemma fold_pt (M : ℕ) (f : ℤ × ℤ × ℤ → ℂ) (hf : ∀ c a d : ℤ, f (-c, -a, -d) = f (c, a, d))
    (p : ℤ × ℤ × ℤ) :
    Ppos.indicator ((Tset M).indicator f) p + Pposᶜ.indicator ((Tset M).indicator f) (-p) =
      (Tp M).indicator (fun q => chi M q.2.1 * f q) p := by
  obtain ⟨c, a, d⟩ := p
  simp only [Prod.neg_mk]
  rcases lt_trichotomy 0 c with hc | rfl | hc
  · have hP : (c, a, d) ∈ Ppos := hc
    have hP' : (-c, -a, -d) ∈ Pposᶜ := fun h => by have h' : 0 < -c := h; linarith
    rw [Set.indicator_of_mem hP, Set.indicator_of_mem hP']
    by_cases hp : (c, a, d) ∈ Tp M
    · rw [Set.indicator_of_mem hp]
      have e1 : (Tset M).indicator f (c, a, d) = if (a : ZMod M) = 1 then f (c, a, d) else 0 := by
        by_cases h1 : (a : ZMod M) = 1
        · rw [if_pos h1]; exact Set.indicator_of_mem ((mem_Tset_pos hc).2 ⟨hp, h1⟩) f
        · rw [if_neg h1]; exact Set.indicator_of_notMem (fun h => h1 ((mem_Tset_pos hc).1 h).2) f
      have e2 : (Tset M).indicator f (-c, -a, -d) = if (a : ZMod M) = -1 then f (c, a, d) else 0 := by
        by_cases h2 : (a : ZMod M) = -1
        · rw [if_pos h2, ← hf]; exact Set.indicator_of_mem ((mem_Tset_neg hc).2 ⟨hp, h2⟩) f
        · rw [if_neg h2]; exact Set.indicator_of_notMem (fun h => h2 ((mem_Tset_neg hc).1 h).2) f
      rw [e1, e2]
      simp only [chi]
      split_ifs <;> ring
    · rw [Set.indicator_of_notMem hp]
      simp [Set.indicator_apply, mem_Tset_pos hc, mem_Tset_neg hc, hp]
  · simp [Set.indicator_apply, Ppos, Tset, Tp]
  · have hn : (c, a, d) ∉ Ppos := fun h => by have h' : 0 < c := h; linarith
    have hn' : (-c, -a, -d) ∉ Pposᶜ := fun h => h (show 0 < -c by linarith)
    have hp : (c, a, d) ∉ Tp M := fun h => by have h' : 0 < c := h.1; linarith
    rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn', Set.indicator_of_notMem hp, add_zero]

/-! ### The parametrisation `Psi` of `Tp M` -/

/-- `L = M · M (c' + 1)`. -/
def Lm (M c' : ℕ) : ℕ := M * (M * (c' + 1))

instance instNeZeroLm (M c' : ℕ) [NeZero M] : NeZero (Lm M c') :=
  ⟨Nat.mul_ne_zero (NeZero.ne M) (Nat.mul_ne_zero (NeZero.ne M) (Nat.succ_ne_zero c'))⟩

def Psi (M : ℕ) (σ : Σ c' : ℕ, (ZMod (Lm M c'))ˣ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  ((M : ℤ) * ((σ.1 : ℤ) + 1),
    (((σ.2.1 : (ZMod (Lm M σ.1))ˣ) : ZMod (Lm M σ.1)).val : ℤ) + (Lm M σ.1 : ℤ) * σ.2.2.1,
    (((σ.2.1⁻¹ : (ZMod (Lm M σ.1))ˣ) : ZMod (Lm M σ.1)).val : ℤ) + (Lm M σ.1 : ℤ) * σ.2.2.2)

lemma Lm_cast (M c' : ℕ) : ((Lm M c' : ℕ) : ℤ) = (M : ℤ) * ((M : ℤ) * ((c' : ℤ) + 1)) := by
  push_cast [Lm]; ring

lemma Psi_mem {M : ℕ} [NeZero M] (σ : Σ c' : ℕ, (ZMod (Lm M c'))ˣ × ℤ × ℤ) : Psi M σ ∈ Tp M := by
  obtain ⟨c', x, i, j⟩ := σ
  have hM : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  refine ⟨by simp only [Psi]; positivity, dvd_mul_right _ _, ?_⟩
  simp only [Psi]
  rw [← Lm_cast, ← CharP.intCast_eq_zero_iff (ZMod (Lm M c')) (Lm M c')]
  simp

lemma divmod_unique {L r r' i i' : ℤ} (hL : 0 < L) (hr : 0 ≤ r) (hrL : r < L) (hr' : 0 ≤ r')
    (hr'L : r' < L) (h : r + L * i = r' + L * i') : r = r' ∧ i = i' := by
  have e1 : (r + L * i) % L = r := by rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr hrL]
  have e2 : (r' + L * i') % L = r' := by rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr' hr'L]
  have hrr : r = r' := by rw [← e1, ← e2, h]
  refine ⟨hrr, ?_⟩
  subst hrr
  exact mul_left_cancel₀ hL.ne' (by linarith)

lemma Psi_injective {M : ℕ} [NeZero M] : Function.Injective (Psi M) := by
  rintro ⟨c', x, i, j⟩ ⟨c'', x', i', j'⟩ h
  simp only [Psi, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hc : c' = c'' := by
    have := mul_left_cancel₀ hM h1
    omega
  subst hc
  have hL : (0 : ℤ) < (Lm M c' : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  have hv := ZMod.val_lt (x : ZMod (Lm M c'))
  have hv' := ZMod.val_lt (x' : ZMod (Lm M c'))
  obtain ⟨hxx, hii⟩ := divmod_unique hL (by positivity) (by exact_mod_cast hv) (by positivity)
    (by exact_mod_cast hv') h2
  have hx : x = x' := Units.ext (ZMod.val_injective _ (by exact_mod_cast hxx))
  subst hx; subst hii
  have hjj : j = j' := mul_left_cancel₀ hL.ne' (by linarith)
  subst hjj
  rfl

lemma Psi_range {M : ℕ} [NeZero M] : Set.range (Psi M) = Tp M := by
  ext p
  refine ⟨fun ⟨σ, hσ⟩ => hσ ▸ Psi_mem σ, fun hp => ?_⟩
  obtain ⟨c, a, d⟩ := p
  obtain ⟨hc, ⟨k, hk⟩, hL⟩ := hp
  have hM : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hk0 : 0 < k := pos_of_mul_pos_right (hk ▸ hc) hM.le
  obtain ⟨c', hc'⟩ : ∃ c' : ℕ, k = (c' : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  subst hc'; subst hk
  have hL' : ((Lm M c' : ℕ) : ℤ) ∣ a * d - 1 := by rw [Lm_cast]; exact hL
  have had : (a : ZMod (Lm M c')) * (d : ZMod (Lm M c')) = 1 := by
    have h0 := (CharP.intCast_eq_zero_iff (ZMod (Lm M c')) (Lm M c') _).2 hL'
    push_cast at h0
    exact sub_eq_zero.1 h0
  let x : (ZMod (Lm M c'))ˣ := Units.mkOfMulEqOne _ _ had
  have hx : (x : ZMod (Lm M c')) = a := Units.val_mkOfMulEqOne had
  have hxi : ((x⁻¹ : (ZMod (Lm M c'))ˣ) : ZMod (Lm M c')) = d :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hx]; exact had)
  refine ⟨⟨c', x, a / (Lm M c' : ℤ), d / (Lm M c' : ℤ)⟩, ?_⟩
  simp only [Psi, Prod.mk.injEq, true_and]
  refine ⟨?_, ?_⟩
  · rw [hx, ZMod.val_intCast]; exact Int.emod_add_mul_ediv a _
  · rw [hxi, ZMod.val_intCast]; exact Int.emod_add_mul_ediv d _

/-- **Folding and parametrisation.** -/
theorem tsum_Tset_fold (M : ℕ) [NeZero M] (f : ℤ × ℤ × ℤ → ℂ)
    (hf : ∀ c a d : ℤ, f (-c, -a, -d) = f (c, a, d)) (hs : Summable (fun p : Tset M => f p.1)) :
    Summable (fun σ => chi M (Psi M σ).2.1 * f (Psi M σ)) ∧
      ∑' p : Tset M, f p.1 = ∑' σ, chi M (Psi M σ).2.1 * f (Psi M σ) := by
  have hF : Summable ((Tset M).indicator f) := summable_subtype_iff_indicator.1 hs
  have h1 : Summable (Ppos.indicator ((Tset M).indicator f)) := hF.indicator Ppos
  have h2 : Summable (Pposᶜ.indicator ((Tset M).indicator f)) := hF.indicator Pposᶜ
  have h2' : Summable (fun p => Pposᶜ.indicator ((Tset M).indicator f) (-p)) :=
    h2.comp_injective neg_injective
  have hH : Summable ((Tp M).indicator (fun q => chi M q.2.1 * f q)) :=
    (h1.add h2').congr (fun p => fold_pt M f hf p)
  have hHσ : Summable (fun σ => chi M (Psi M σ).2.1 * f (Psi M σ)) :=
    (hH.comp_injective Psi_injective).congr (fun σ => by
      simp only [Function.comp_apply, Set.indicator_of_mem (Psi_mem σ)])
  refine ⟨hHσ, ?_⟩
  calc ∑' p : Tset M, f p.1 = ∑' p, (Tset M).indicator f p := tsum_subtype (Tset M) f
    _ = ∑' p, (Ppos.indicator ((Tset M).indicator f) p + Pposᶜ.indicator ((Tset M).indicator f) p) :=
        tsum_congr fun p => (Set.indicator_self_add_compl_apply Ppos _ p).symm
    _ = ∑' p, Ppos.indicator ((Tset M).indicator f) p + ∑' p, Pposᶜ.indicator ((Tset M).indicator f) p :=
        h1.tsum_add h2
    _ = ∑' p, Ppos.indicator ((Tset M).indicator f) p +
          ∑' p, Pposᶜ.indicator ((Tset M).indicator f) (-p) := by
        congr 1; exact ((Equiv.neg (ℤ × ℤ × ℤ)).tsum_eq _).symm
    _ = ∑' p, (Ppos.indicator ((Tset M).indicator f) p +
          Pposᶜ.indicator ((Tset M).indicator f) (-p)) := (h1.tsum_add h2').symm
    _ = ∑' p, (Tp M).indicator (fun q => chi M q.2.1 * f q) p := tsum_congr (fold_pt M f hf)
    _ = ∑' q : Tp M, chi M q.1.2.1 * f q.1 := (tsum_subtype (Tp M) _).symm
    _ = ∑' q : Set.range (Psi M), chi M q.1.2.1 * f q.1 := by rw [Psi_range]
    _ = ∑' σ, chi M (Psi M σ).2.1 * f (Psi M σ) :=
        tsum_range (fun q => chi M q.2.1 * f q) Psi_injective

/-! ### Factorisation of `Mterm` -/

def fz (s : ℝ) (ζ : ℂ) : ℂ := ((ζ ^ 2)⁻¹) * ((normSq ζ ^ (-s) : ℝ) : ℂ)

lemma normSq_pos_of_im {ζ : ℂ} (h : 0 < ζ.im) : 0 < normSq ζ :=
  normSq_pos.2 (fun h0 => by rw [h0, Complex.zero_im] at h; exact lt_irrefl 0 h)

theorem Mterm_eq {M : ℕ} (hM : M ≠ 0) (s : ℝ) {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) {c : ℤ}
    (hc : c ≠ 0) (a d : ℤ) :
    Mterm s z w (c, a, d) = (((z.im * w.im / ((c : ℝ) ^ 2 * (M : ℝ) ^ 4)) ^ s /
      ((c : ℝ) ^ 2 * (M : ℝ) ^ 4) : ℝ) : ℂ) * fz s ((z + d / c) / M) * fz s ((w + a / c) / M) := by
  have hc' : (c : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)
  have hcr : (0 : ℝ) < (c : ℝ) ^ 2 := by positivity
  have imζ : ((z + d / c) / (M : ℂ)).im = z.im / M := by
    rw [Complex.div_natCast_im, Complex.add_im]
    norm_num [Complex.div_im]
  have imξ : ((w + a / c) / (M : ℂ)).im = w.im / M := by
    rw [Complex.div_natCast_im, Complex.add_im]
    norm_num [Complex.div_im]
  have hζ0 := normSq_pos_of_im (show 0 < ((z + d / c) / (M : ℂ)).im by rw [imζ]; positivity)
  have hξ0 := normSq_pos_of_im (show 0 < ((w + a / c) / (M : ℂ)).im by rw [imξ]; positivity)
  have hζne : (z + d / c) / (M : ℂ) ≠ 0 := fun h => by rw [h, map_zero] at hζ0; exact lt_irrefl 0 hζ0
  have hξne : (w + a / c) / (M : ℂ) ≠ 0 := fun h => by rw [h, map_zero] at hξ0; exact lt_irrefl 0 hξ0
  have hA : AC z w (c, a, d) = ((c : ℂ) * M) ^ 2 * (((z + d / c) / M) * ((w + a / c) / M)) := by
    show ((c : ℂ) * z + d) * ((c : ℂ) * w + a) = _
    field_simp
  have hN : ‖AC z w (c, a, d)‖ ^ 2 = ((c : ℝ) ^ 2 * (M : ℝ) ^ 2) ^ 2 *
      (normSq ((z + d / c) / M) * normSq ((w + a / c) / M)) := by
    rw [Complex.sq_norm, hA]
    simp only [map_mul, map_pow, Complex.normSq_intCast, Complex.normSq_natCast]
    ring
  have hR : etaC z w c / ‖AC z w (c, a, d)‖ ^ 2 = (z.im * w.im / ((c : ℝ) ^ 2 * (M : ℝ) ^ 4)) *
      ((normSq ((z + d / c) / M))⁻¹ * (normSq ((w + a / c) / M))⁻¹) := by
    rw [hN]; unfold etaC; field_simp
  have hX0 : 0 ≤ z.im * w.im / ((c : ℝ) ^ 2 * (M : ℝ) ^ 4) := by positivity
  have hRs : (etaC z w c / ‖AC z w (c, a, d)‖ ^ 2) ^ s =
      (z.im * w.im / ((c : ℝ) ^ 2 * (M : ℝ) ^ 4)) ^ s *
      (normSq ((z + d / c) / M) ^ (-s) * normSq ((w + a / c) / M) ^ (-s)) := by
    rw [hR, Real.mul_rpow hX0 (by positivity), Real.mul_rpow (inv_nonneg.2 hζ0.le) (inv_nonneg.2 hξ0.le),
      Real.inv_rpow hζ0.le, Real.inv_rpow hξ0.le, ← Real.rpow_neg hζ0.le, ← Real.rpow_neg hξ0.le]
  have hcplx : (c : ℂ) ^ 2 * ((AC z w (c, a, d)) ^ 2)⁻¹ =
      ((((c : ℝ) ^ 2 * (M : ℝ) ^ 4 : ℝ) : ℂ))⁻¹ *
        ((((z + d / c) / M) ^ 2)⁻¹ * (((w + a / c) / M) ^ 2)⁻¹) := by
    rw [hA]; push_cast; field_simp
  have e1 : Mterm s z w (c, a, d) = ((c : ℂ) ^ 2 * ((AC z w (c, a, d)) ^ 2)⁻¹) *
      (((etaC z w c / ‖AC z w (c, a, d)‖ ^ 2) ^ s : ℝ) : ℂ) := by
    simp only [Mterm]; ring
  rw [e1, hcplx, hRs, fz, fz]
  push_cast
  ring

/-! ### The class sums -/

/-- `ζ = (z + n / C) / M`, `C = M (c' + 1)`. -/
def zeta (M c' : ℕ) (z : ℂ) (n : ℕ) : ℂ := (z + (((n : ℝ) / ((M : ℝ) * (c' + 1)) : ℝ) : ℂ)) / (M : ℂ)

lemma im_zeta (M c' : ℕ) (z : ℂ) (n : ℕ) : (zeta M c' z n).im = z.im / M := by
  rw [zeta, Complex.div_natCast_im, Complex.add_im, Complex.ofReal_im, add_zero]

lemma re_zeta (M c' : ℕ) (z : ℂ) (n : ℕ) :
    (zeta M c' z n).re = (z.re + (n : ℝ) / ((M : ℝ) * (c' + 1))) / M := by
  rw [zeta, Complex.div_natCast_re, Complex.add_re, Complex.ofReal_re]

/-- The weight `(t / (C² M⁴))^s / (C² M⁴)`. -/
def WtR (M : ℕ) (s t : ℝ) (c' : ℕ) : ℝ :=
  (t / (((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4)) ^ s / (((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4)

/-- The class indicator on units: `1[x ≡ 1] + 1[x ≡ -1]` mod `M`. -/
def chiU (M c' : ℕ) (x : (ZMod (Lm M c'))ˣ) : ℂ :=
  (if (ZMod.cast (x : ZMod (Lm M c')) : ZMod M) = 1 then 1 else 0) +
    (if (ZMod.cast (x : ZMod (Lm M c')) : ZMod M) = -1 then 1 else 0)

/-- The `c' `-block of the MAIN sum (finite-sum form). -/
def MF (M : ℕ) [NeZero M] (s : ℝ) (z w : ℂ) (c' : ℕ) : ℂ :=
  ((WtR M s (z.im * w.im) c' : ℝ) : ℂ) * ∑ x : (ZMod (Lm M c'))ˣ, chiU M c' x *
    (Gs s (zeta M c' z ((x⁻¹ : (ZMod (Lm M c'))ˣ) : ZMod (Lm M c')).val) *
      Gs s (zeta M c' w ((x : ZMod (Lm M c')).val)))

lemma chi_Psi {M : ℕ} [NeZero M] (c' : ℕ) (x : (ZMod (Lm M c'))ˣ) (i j : ℤ) :
    chi M (Psi M ⟨c', (x, i, j)⟩).2.1 = chiU M c' x := by
  have hdvd : ((Lm M c' : ℕ) : ZMod M) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod M) M _).2 (Dvd.intro _ rfl)
  have e : ((((x : ZMod (Lm M c')).val : ℤ) + (Lm M c' : ℤ) * i : ℤ) : ZMod M) =
      (ZMod.cast (x : ZMod (Lm M c')) : ZMod M) := by
    rw [ZMod.cast_eq_val]; push_cast; rw [hdvd, zero_mul, add_zero]
  simp only [Psi, chi, chiU, e]

lemma summable_norm_fS_shift {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {ζ : ℂ} (hζ : 0 < ζ.im) :
    Summable (fun n : ℤ => ‖fS s ζ.im (ζ.re + n)‖) := by
  obtain ⟨hS, -⟩ := sum1D ζ.re ζ.im hζ
  refine (hS.mul_left (rho ζ.im * (ζ.im ^ 2) ^ (-(1 / 4 : ℝ)))).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => ?_)
  refine (norm_fS_le hs0 hs1 hζ _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith [one_le_rho ζ.im])
  have hT : 0 < tq ζ.im (ζ.re + n) := tq_pos hζ _
  have hle : ζ.im ^ 2 ≤ tq ζ.im (ζ.re + n) := by unfold tq; nlinarith [sq_nonneg (ζ.re + n)]
  have e : (tq ζ.im (ζ.re + n))⁻¹ =
      (tq ζ.im (ζ.re + n)) ^ (-(1 / 4 : ℝ)) * (tq ζ.im (ζ.re + n)) ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_add hT, show (-(1 / 4 : ℝ)) + (-(3 / 4)) = -1 by norm_num, Real.rpow_neg_one]
  rw [e]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num))
    (Real.rpow_nonneg hT.le _)

lemma hasSum_Gs_mul {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {ζ ξ : ℂ} (hζ : 0 < ζ.im) (hξ : 0 < ξ.im) :
    HasSum (fun ij : ℤ × ℤ => fS s ξ.im (ξ.re + ij.1) * fS s ζ.im (ζ.re + ij.2)) (Gs s ξ * Gs s ζ) := by
  have hξn := summable_norm_fS_shift hs0 hs1 hξ
  have hζn := summable_norm_fS_shift hs0 hs1 hζ
  have h := (summable_mul_of_summable_norm hξn hζn).hasSum
  rwa [← tsum_mul_tsum_of_summable_norm hξn hζn] at h

lemma zeta_shift (M c' : ℕ) [NeZero M] (z : ℂ) (n : ℕ) (j : ℤ) :
    (z + ((((n : ℤ) + (Lm M c' : ℤ) * j : ℤ) : ℂ)) / (((M : ℤ) * ((c' : ℤ) + 1) : ℤ) : ℂ)) / (M : ℂ) =
      zeta M c' z n + j := by
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hc1 : ((c' : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero c'
  rw [zeta, Lm]; push_cast; field_simp; ring

/-- The `(c', x)` block of the MAIN sum. -/
theorem hasSum_block {M : ℕ} [NeZero M] {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) (c' : ℕ) (x : (ZMod (Lm M c'))ˣ) :
    HasSum (fun ij : ℤ × ℤ => chi M (Psi M ⟨c', (x, ij)⟩).2.1 * Mterm s z w (Psi M ⟨c', (x, ij)⟩))
      (((WtR M s (z.im * w.im) c' : ℝ) : ℂ) * (chiU M c' x *
        (Gs s (zeta M c' z ((x⁻¹ : (ZMod (Lm M c'))ˣ) : ZMod (Lm M c')).val) *
          Gs s (zeta M c' w ((x : ZMod (Lm M c')).val))))) := by
  have hM0 : M ≠ 0 := NeZero.ne M
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM0)
  have hc0 : (M : ℤ) * ((c' : ℤ) + 1) ≠ 0 := by positivity
  set ζ := zeta M c' z ((x⁻¹ : (ZMod (Lm M c'))ˣ) : ZMod (Lm M c')).val with hζdef
  set ξ := zeta M c' w ((x : ZMod (Lm M c')).val) with hξdef
  have hζ : 0 < ζ.im := by rw [hζdef, im_zeta]; positivity
  have hξ : 0 < ξ.im := by rw [hξdef, im_zeta]; positivity
  have hpt : ∀ ij : ℤ × ℤ, chi M (Psi M ⟨c', (x, ij)⟩).2.1 * Mterm s z w (Psi M ⟨c', (x, ij)⟩) =
      (((WtR M s (z.im * w.im) c' : ℝ) : ℂ) * chiU M c' x) *
        (fS s ξ.im (ξ.re + ij.1) * fS s ζ.im (ζ.re + ij.2)) := by
    rintro ⟨i, j⟩
    rw [chi_Psi]
    have hP : Psi M ⟨c', (x, i, j)⟩ = ((M : ℤ) * ((c' : ℤ) + 1),
        (((x : ZMod (Lm M c')).val : ℕ) : ℤ) + (Lm M c' : ℤ) * i,
        ((((x⁻¹ : (ZMod (Lm M c'))ˣ) : ZMod (Lm M c')).val : ℕ) : ℤ) + (Lm M c' : ℤ) * j) := rfl
    rw [hP, Mterm_eq hM0 s hy hv hc0, zeta_shift, zeta_shift, ← hζdef, ← hξdef, fS_shift, fS_shift]
    simp only [fz, WtR]
    push_cast
    ring
  have h := (hasSum_Gs_mul hs0 hs1 hζ hξ).mul_left (((WtR M s (z.im * w.im) c' : ℝ) : ℂ) * chiU M c' x)
  rw [show (fun ij : ℤ × ℤ => chi M (Psi M ⟨c', (x, ij)⟩).2.1 * Mterm s z w (Psi M ⟨c', (x, ij)⟩)) =
      fun ij : ℤ × ℤ => (((WtR M s (z.im * w.im) c' : ℝ) : ℂ) * chiU M c' x) *
        (fS s ξ.im (ξ.re + ij.1) * fS s ζ.im (ζ.re + ij.2)) from funext hpt]
  rw [show ((WtR M s (z.im * w.im) c' : ℝ) : ℂ) * (chiU M c' x * (Gs s ζ * Gs s ξ)) =
      (((WtR M s (z.im * w.im) c' : ℝ) : ℂ) * chiU M c' x) * (Gs s ξ * Gs s ζ) by ring]
  exact h

/-- **MAIN in finite-sum form**: `Σ_{Tset} Mterm = Σ_{c'} MF c'` (`0 < s ≤ 1`, `M ≥ 3`). -/
theorem tsum_Mterm_eq_MF {M : ℕ} [NeZero M] (hM : 3 ≤ M) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {z w : ℂ}
    (hy : 0 < z.im) (hv : 0 < w.im) :
    Summable (MF M s z w) ∧ ∑' p : Tset M, Mterm s z w p.1 = ∑' c', MF M s z w c' := by
  obtain ⟨hMs, -⟩ := KG_split hM hs hs1 hy hv
  obtain ⟨hσ, heq⟩ := tsum_Tset_fold M (Mterm s z w) (Mterm_neg s z w) hMs
  have hblock : ∀ c', ∑' t : (ZMod (Lm M c'))ˣ × ℤ × ℤ,
      chi M (Psi M ⟨c', t⟩).2.1 * Mterm s z w (Psi M ⟨c', t⟩) = MF M s z w c' := by
    intro c'
    rw [(hσ.sigma_factor c').tsum_prod, tsum_fintype, MF, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => (hasSum_block hs.le hs1 hy hv c' x).tsum_eq
  refine ⟨(hσ.sigma).congr hblock, ?_⟩
  rw [heq, hσ.tsum_sigma]
  exact tsum_congr hblock

end RamanujanPetersson.KernelSD


