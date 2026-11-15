-- Prove2me | Definitions.Def_RPLib_S3_DWSOR
-- name    : RPLib_S3_DWSOR
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:44:02.931211+00:00
-- url     : https://prove2.me/theorems/8a3d38df-a2b1-44ef-be4f-8f47fc53b995
-- title:
--   Weight-two Ramanujan-Petersson library: `ellCount` split by content (O5, form half)
-- statement:
--   `ellCount` split by content (O5, form half).
--
--   * `Lval M t f D'`: the common value `L_f` of `levelCount M 1` on multiplication by `π = (t - f b₀)/2 + f ω` in the
--     canonical model `ℤ[ω]` (`ω² = a₀ + b₀ ω`, `b₀ = D' % 2`) of discriminant `D'`; **`Lval_eq`**: every model
--     `QuadraticAlgebra ℤ a b` with `2x + f b = t` gives `Lval M t f (b² + 4a)`.
--   * `exists_isUnit_eval`: a primitive form takes a value prime to `M`.
--   * `fset D = {f ∈ [1, |D|] : f² ∣ D}`, `content_mem_fset`, `content_scaleQ`, `sum_content_eq`.
--   * **`ellCount_eq_sum`**: `ellCount M 1 t n = Σ_{f ∈ fset D} #redPrim(D/f²) · L_f / sD(D/f²)`, `D = t² - 4n`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOQ
import Definitions.Def_RPLib_S3_ConjClassesD
import Definitions.Def_RPLib_S3_DWSTateQ5

/-!
# S3-DWS-Ordinary, part R: `ellCount` split by content (O5, form half)

* `Lval M t f D'`: the common value `L_f` of `levelCount M 1` on multiplication by `π = (t - f b₀)/2 + f ω` in the
  canonical model `ℤ[ω]` (`ω² = a₀ + b₀ ω`, `b₀ = D' % 2`) of discriminant `D'`; **`Lval_eq`**: every model
  `QuadraticAlgebra ℤ a b` with `2x + f b = t` gives `Lval M t f (b² + 4a)`.
* `exists_isUnit_eval`: a primitive form takes a value prime to `M`.
* `fset D = {f ∈ [1, |D|] : f² ∣ D}`, `content_mem_fset`, `content_scaleQ`, `sum_content_eq`.
* **`ellCount_eq_sum`**: `ellCount M 1 t n = Σ_{f ∈ fset D} #redPrim(D/f²) · L_f / sD(D/f²)`, `D = t² - 4n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.S3.DWSO

open RamanujanPetersson.Hurwitz RamanujanPetersson.S3.Conj

/-- `L_f(t, D')` in the canonical model `b₀ = D' % 2`, `a₀ = (D' - b₀)/4`. -/
def Lval (M : ℕ) [NeZero M] (t f D' : ℤ) : ℕ :=
  levelCount M 1 (mulMat (⟨(t - f * (D' % 2)) / 2, f⟩ : QuadraticAlgebra ℤ ((D' - D' % 2) / 4) (D' % 2)))

theorem Lval_eq (M : ℕ) [NeZero M] {a b x f t : ℤ} (ht : 2 * x + f * b = t) :
    levelCount M 1 (mulMat (⟨x, f⟩ : QuadraticAlgebra ℤ a b)) = Lval M t f (b ^ 2 + 4 * a) := by
  subst ht
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r : ℤ, (r = 0 ∨ r = 1) ∧ b = 2 * k + r := ⟨b / 2, b % 2, by omega, by omega⟩
  have hr2 : r ^ 2 = r := by rcases hr with rfl | rfl <;> norm_num
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = k ^ 2 + k * r + a := ⟨_, rfl⟩
  have hD : (2 * k + r) ^ 2 + 4 * a = 4 * m + r := by rw [hm]; linear_combination hr2
  have e1 : ((2 * k + r) ^ 2 + 4 * a) % 2 = r := by rw [hD]; omega
  have e2 : ((2 * k + r) ^ 2 + 4 * a - r) / 4 = m := by rw [hD]; omega
  have e3 : 2 * x + f * (2 * k + r) - f * r = 2 * (x + f * k) := by ring
  unfold Lval
  rw [e1, e2, e3, Int.mul_ediv_cancel_left _ two_ne_zero]
  apply levelCount_mulMat_eq
  · linear_combination hD - hr2
  · ring

/-- **R1.** A primitive form takes a value prime to `M` (`x`, `y` explicit products of primes dividing `M`). -/
theorem exists_isUnit_eval (M : ℕ) [NeZero M] {a' b' c' : ℤ}
    (hp : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ a' → (ℓ : ℤ) ∣ b' → (ℓ : ℤ) ∣ c' → False) :
    ∃ x y : ℤ, IsUnit ((a' * x ^ 2 + b' * x * y + c' * y ^ 2 : ℤ) : ZMod M) := by
  classical
  have hfac : ∀ ℓ : ℕ, ℓ.Prime → ∀ (P : ℕ → Prop) [DecidablePred P],
      (ℓ : ℤ) ∣ ∏ ℓ' ∈ M.primeFactors.filter P, (ℓ' : ℤ) → P ℓ := by
    intro ℓ hℓ P _ h
    obtain ⟨ℓ', hℓ', hd⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.1 hℓ) _).1 h
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hℓ'
    rw [(Nat.prime_dvd_prime_iff_eq hℓ hℓ'.1.1).1 (Int.natCast_dvd_natCast.1 hd)]
    exact hℓ'.2
  have hmem : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ∀ (P : ℕ → Prop) [DecidablePred P], P ℓ →
      (ℓ : ℤ) ∣ ∏ ℓ' ∈ M.primeFactors.filter P, (ℓ' : ℤ) := fun ℓ hℓ hM P _ h =>
    Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hℓ, hM, NeZero.ne M⟩, h⟩)
  obtain ⟨x, hx⟩ : ∃ x : ℤ,
      x = ∏ ℓ ∈ M.primeFactors.filter (fun ℓ : ℕ => (ℓ : ℤ) ∣ a' ∧ ¬ (ℓ : ℤ) ∣ c'), ((ℓ : ℕ) : ℤ) :=
    ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y = ∏ ℓ ∈ M.primeFactors.filter (fun ℓ : ℕ => ¬ (ℓ : ℤ) ∣ a'), ((ℓ : ℕ) : ℤ) :=
    ⟨_, rfl⟩
  refine ⟨x, y, ?_⟩
  have key : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ¬ (ℓ : ℤ) ∣ a' * x ^ 2 + b' * x * y + c' * y ^ 2 := by
    intro ℓ hℓ hM hdv
    have := Fact.mk hℓ
    have z : ∀ u : ℤ, (ℓ : ℤ) ∣ u ↔ (u : ZMod ℓ) = 0 := fun u => (ZMod.intCast_zmod_eq_zero_iff_dvd u ℓ).symm
    rw [z] at hdv
    push_cast at hdv
    by_cases ha : (ℓ : ℤ) ∣ a'
    · by_cases hc : (ℓ : ℤ) ∣ c'
      · have hb : ¬ (ℓ : ℤ) ∣ b' := fun hb => hp ℓ hℓ ha hb hc
        have hxl : ¬ (ℓ : ℤ) ∣ x := fun h => by
          rw [hx] at h; exact (hfac ℓ hℓ (fun ℓ => (ℓ : ℤ) ∣ a' ∧ ¬ (ℓ : ℤ) ∣ c') h).2 hc
        have hyl : ¬ (ℓ : ℤ) ∣ y := fun h => by
          rw [hy] at h; exact hfac ℓ hℓ (fun ℓ => ¬ (ℓ : ℤ) ∣ a') h ha
        rw [z] at ha hb hc hxl hyl
        exact mul_ne_zero (mul_ne_zero hb hxl) hyl
          (by linear_combination hdv - (x : ZMod ℓ) ^ 2 * ha - (y : ZMod ℓ) ^ 2 * hc)
      · have hxl : (ℓ : ℤ) ∣ x := by
          rw [hx]; exact hmem ℓ hℓ hM (fun ℓ => (ℓ : ℤ) ∣ a' ∧ ¬ (ℓ : ℤ) ∣ c') ⟨ha, hc⟩
        have hyl : ¬ (ℓ : ℤ) ∣ y := fun h => by
          rw [hy] at h; exact hfac ℓ hℓ (fun ℓ => ¬ (ℓ : ℤ) ∣ a') h ha
        rw [z] at ha hc hxl hyl
        exact mul_ne_zero hc (pow_ne_zero 2 hyl)
          (by linear_combination hdv - ((a' : ZMod ℓ) * x + b' * y) * hxl)
    · have hyl : (ℓ : ℤ) ∣ y := by rw [hy]; exact hmem ℓ hℓ hM (fun ℓ => ¬ (ℓ : ℤ) ∣ a') ha
      have hxl : ¬ (ℓ : ℤ) ∣ x := fun h => by
        rw [hx] at h; exact ha (hfac ℓ hℓ (fun ℓ => (ℓ : ℤ) ∣ a' ∧ ¬ (ℓ : ℤ) ∣ c') h).1
      rw [z] at ha hxl hyl
      exact mul_ne_zero ha (pow_ne_zero 2 hxl) (by linear_combination hdv - ((b' : ZMod ℓ) * x + c' * y) * hyl)
  have hcop : Nat.Coprime M (a' * x ^ 2 + b' * x * y + c' * y ^ 2).natAbs :=
    Nat.coprime_of_dvd fun ℓ hℓ hM hv => key ℓ hℓ hM (Int.ofNat_dvd_left.2 hv)
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one]
  exact hcop

/-- Admissible contents for discriminant `D`. -/
noncomputable def fset (D : ℤ) : Finset ℤ := (Finset.Icc 1 |D|).filter fun f => f ^ 2 ∣ D

theorem content_mem_fset {D : ℤ} {Q : ℤ × ℤ × ℤ} (hQ : Q ∈ redForms D) : ((toBQF Q).content : ℤ) ∈ fset D := by
  obtain ⟨hD, hR⟩ := mem_redForms.1 hQ
  have hpos : 0 < (toBQF Q).content := Int.gcd_pos_of_ne_zero_left _ hR.a_pos.ne'
  obtain ⟨a1, ha⟩ := BQF.content_dvd_a (toBQF Q)
  obtain ⟨b1, hb⟩ := BQF.content_dvd_b (toBQF Q)
  obtain ⟨c1, hc⟩ := BQF.content_dvd_c (toBQF Q)
  have hdvd : ((toBQF Q).content : ℤ) ^ 2 ∣ D :=
    ⟨b1 ^ 2 - 4 * a1 * c1, by rw [← hD, BQF.disc, ha, hb, hc]; ring⟩
  have hD0 : D < 0 := hD ▸ hR.disc_neg
  have hle := Int.le_of_dvd (abs_pos.2 hD0.ne) ((dvd_abs _ _).2 hdvd)
  have hg1 : (1 : ℤ) ≤ (toBQF Q).content := by exact_mod_cast hpos
  rw [fset, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hg1, by nlinarith⟩, hdvd⟩

theorem content_scaleQ {f : ℤ} (hf : 0 < f) (Q : ℤ × ℤ × ℤ) :
    ((toBQF (scaleQ f Q)).content : ℤ) = f * (toBQF Q).content := by
  have h1 : ((f.natAbs : ℕ) : ℤ) = f := Int.natAbs_of_nonneg hf.le
  simp only [BQF.content, toBQF, scaleQ]
  rw [Int.gcd_mul_left, Nat.cast_mul, h1, Int.gcd_mul_left, Nat.cast_mul, h1]

theorem dvd_of_content {f : ℤ} {Q : ℤ × ℤ × ℤ} (h : ((toBQF Q).content : ℤ) = f) :
    f ∣ Q.1 ∧ f ∣ Q.2.1 ∧ f ∣ Q.2.2 := by
  subst h
  exact ⟨BQF.content_dvd_a (toBQF Q), BQF.content_dvd_b (toBQF Q), BQF.content_dvd_c (toBQF Q)⟩

/-- **R2-R4.** The reduced forms of content `f` contribute `#redPrim(D/f²) · L_f / sD(D/f²)`. -/
theorem sum_content_eq (M : ℕ) [NeZero M] (t : ℤ) (n : ℕ) {f : ℤ} (hf : f ∈ fset (t ^ 2 - 4 * n)) :
    ∑ Q ∈ (redForms (t ^ 2 - 4 * n)).filter (fun Q => ((toBQF Q).content : ℤ) = f),
        (levelCount M 1 (gammaQ Q t) : ℚ) / stabOrd Q =
      ((redPrim ((t ^ 2 - 4 * n) / f ^ 2)).card : ℚ) * Lval M t f ((t ^ 2 - 4 * n) / f ^ 2) /
        RPLib.DWS.QA.sD ((t ^ 2 - 4 * n) / f ^ 2) := by
  rw [fset, Finset.mem_filter, Finset.mem_Icc] at hf
  obtain ⟨⟨hf1, -⟩, hfD⟩ := hf
  have hf0 : (0 : ℤ) < f := by omega
  have hDD : f ^ 2 * ((t ^ 2 - 4 * n) / f ^ 2) = t ^ 2 - 4 * n := Int.mul_ediv_cancel' hfD
  generalize (t ^ 2 - 4 * (n : ℤ)) / f ^ 2 = D' at hDD ⊢
  rw [mul_div_assoc, ← nsmul_eq_mul, ← Finset.sum_const]
  symm
  refine Finset.sum_nbij' (fun g => scaleQ f (g.a, g.b, g.c)) (fun Q => toBQF (unscaleQ f Q)) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    obtain ⟨hgD, hgR, hgP⟩ := mem_redPrim.1 hg
    rw [Finset.mem_filter, mem_redForms, disc_scaleQ, isReduced_scaleQ_iff hf0, content_scaleQ hf0]
    refine ⟨⟨?_, hgR⟩, ?_⟩
    · show f ^ 2 * g.disc = _
      rw [hgD, hDD]
    · rw [show (toBQF (g.a, g.b, g.c)).content = 1 from hgP, Nat.cast_one, mul_one]
  · intro Q hQ
    rw [Finset.mem_filter] at hQ
    obtain ⟨hQR, hQc⟩ := hQ
    obtain ⟨h1, h2, h3⟩ := dvd_of_content hQc
    have hs := scaleQ_unscaleQ h1 h2 h3
    have hQ' := mem_redForms.1 hQR
    rw [← hs, disc_scaleQ, isReduced_scaleQ_iff hf0, ← hDD] at hQ'
    rw [mem_redPrim]
    refine ⟨mul_left_cancel₀ (pow_ne_zero 2 hf0.ne') hQ'.1, hQ'.2, ?_⟩
    have hc := content_scaleQ hf0 (unscaleQ f Q)
    rw [hs, hQc] at hc
    have h1' : ((toBQF (unscaleQ f Q)).content : ℤ) = 1 :=
      mul_left_cancel₀ hf0.ne' (hc.symm.trans (mul_one f).symm)
    show (toBQF (unscaleQ f Q)).content = 1
    exact_mod_cast h1'
  · intro g _
    exact congrArg toBQF (unscaleQ_scaleQ hf0.ne' (g.a, g.b, g.c))
  · intro Q hQ
    rw [Finset.mem_filter] at hQ
    obtain ⟨h1, h2, h3⟩ := dvd_of_content hQ.2
    exact scaleQ_unscaleQ h1 h2 h3
  · intro g hg
    obtain ⟨hgD, hgR, hgP⟩ := mem_redPrim.1 hg
    have hst : stabOrd (scaleQ f (g.a, g.b, g.c)) = RPLib.DWS.QA.sD D' := by
      rw [stabOrd_scaleQ hf0.ne', stabOrd_eq_card (Q := (g.a, g.b, g.c)) hgR, ← hgD]
      exact RPLib.DWS.QA.card_stab_eq_sD (mem_primForms.2 ⟨rfl, hgR.posDef, hgP⟩)
    have hprim : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ g.a → (ℓ : ℤ) ∣ g.b → (ℓ : ℤ) ∣ g.c → False :=
      fun ℓ hℓ ha hb hc => by
        have h := BQF.dvd_content g ha hb hc
        rw [show g.content = 1 from hgP, Nat.dvd_one] at h
        exact hℓ.one_lt.ne' h
    obtain ⟨x, y, hxy⟩ := exists_isUnit_eval M hprim
    have hD2 : t ^ 2 - 4 * n = f ^ 2 * (g.b ^ 2 - 4 * g.a * g.c) := by rw [← hDD, ← hgD, BQF.disc]
    have ht : 2 ∣ t - f * g.b := by
      have h2 : (2 : ℤ) ∣ (t - f * g.b) * (t + f * g.b) :=
        ⟨2 * (n - f ^ 2 * g.a * g.c), by linear_combination hD2⟩
      rcases Int.prime_two.dvd_or_dvd h2 with h | h
      · exact h
      · have e : t - f * g.b = (t + f * g.b) - 2 * (f * g.b) := by ring
        rw [e]; exact dvd_sub h (dvd_mul_right 2 _)
    have hx2 : 2 * ((t - f * g.b) / 2) + f * g.b = t := by rw [Int.mul_ediv_cancel' ht]; ring
    have hlev : levelCount M 1 (gammaQ (scaleQ f (g.a, g.b, g.c)) t) = Lval M t f D' := by
      show levelCount M 1 (gammaQ (f * g.a, f * g.b, f * g.c) t) = _
      rw [levelCount_gammaQ M 1 g.a g.b g.c f t x y ht hxy, Lval_eq M (a := -(g.a * g.c)) hx2]
      congr 1
      rw [← hgD, BQF.disc]; ring
    rw [hlev, hst]

/-- **O5 (forms side).** `ellCount M 1 t n = Σ_{f ∈ fset D} #redPrim(D/f²) · L_f / sD(D/f²)`, `D = t² - 4n`. -/
theorem ellCount_eq_sum (M : ℕ) [NeZero M] (t : ℤ) (n : ℕ) :
    ellCount M 1 t n = ∑ f ∈ fset (t ^ 2 - 4 * n),
      ((redPrim ((t ^ 2 - 4 * n) / f ^ 2)).card : ℚ) * Lval M t f ((t ^ 2 - 4 * n) / f ^ 2) /
        RPLib.DWS.QA.sD ((t ^ 2 - 4 * n) / f ^ 2) := by
  rw [ellCount, ← Finset.sum_fiberwise_of_maps_to (g := fun Q => ((toBQF Q).content : ℤ))
    (fun Q hQ => content_mem_fset hQ)]
  exact Finset.sum_congr rfl fun f hf => sum_content_eq M t n hf

end RamanujanPetersson.S3.DWSO


