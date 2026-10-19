-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_norm_tsum_tsum_mul_conj_tsum_weight_mul_residueSymbol_pow_three_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T11:09:35.777456+00:00
-- url     : https://prove2.me/submissions/fa138947-e11a-46a8-9bf9-a9b02540d1ac

import Definitions.Def_ArtinGLWeight
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Theorems.Thm_ArtinPrimitiveRoots_tsum_indicator_W_mul_eq_TTt_add_DPt_add_DQt_sub_RPt
import Theorems.Thm_ArtinPrimitiveRoots_norm_PSnp_RPt_le_and_norm_PSnp_DPt_le_and_norm_PSnp_DQt_le_and_norm_PSnp_TTt_le
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_cls_exists_differentiable_eq_tsum_residueSymbol_pow_three_and_functionalEquation
import Mathlib

section
section
/-! # L92M_Basic: Mellin transforms of smooth functions supported in `[a, b] ⊂ (0, ∞)`

For `g : ℝ → ℝ` continuous with `tsupport g ⊆ Icc a b`, `0 < a`, the Mellin transform of
`(g · : ℂ)` is entire and bounded on vertical strips; for smooth `g`, integration by parts
(`D g t = t g'(t)`, `mellin (D g) s = -s mellin g s`) gives decay faster than any power of `|Im s|`.
-/

namespace ArtinPrimitiveRoots.L92M

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Interval ContDiff

section General

variable {g : ℝ → ℝ} {a b : ℝ}

end General

section IBP

variable {g : ℝ → ℝ} {a b : ℝ}

end IBP

section Main

variable (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ) (ha : 0 < a)
  (hab : tsupport f ⊆ Set.Icc a b)

include hf ha hab

end Main

end ArtinPrimitiveRoots.L92M

end
end

section
section
/-!
# L3Q_W: the weight `W` of GL Prop 5.2 and its Mellin transform

`W` is a smooth bump with `W = 1` on `[1, 2]`, `0 ≤ W ≤ 1`, support in `[1/2, 5/2]`. Its Mellin
transform `Wm` is entire, decays faster than any power on vertical strips, and inverts back to `W`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open MeasureTheory Complex
open scoped Real

theorem W_nonneg (t : ℝ) : 0 ≤ W t := WB.nonneg

theorem W_le_one (t : ℝ) : W t ≤ 1 := WB.le_one

theorem tsupport_W : tsupport W ⊆ Set.Icc (1 / 2) (5 / 2) := by
  have : tsupport W = Metric.closedBall (3 / 2 : ℝ) 1 := WB.tsupport_eq
  rw [this, Real.closedBall_eq_Icc]
  norm_num

theorem W_eq_zero {t : ℝ} (ht : t < 1 / 2 ∨ 5 / 2 < t) : W t = 0 := by
  by_contra h
  have := tsupport_W (subset_tsupport _ h)
  rw [Set.mem_Icc] at this
  rcases ht with ht | ht <;> linarith [this.1, this.2]

theorem W_eq_one {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 2) : W t = 1 :=
  WB.one_of_mem_closedBall (by
    rw [show WB.rIn = 1 / 2 from rfl, Real.closedBall_eq_Icc]; constructor <;> linarith)

theorem W_props : (∀ t, 0 ≤ W t ∧ W t ≤ 1) ∧ (∀ t, 1 < t → t ≤ 2 → W t = 1) ∧
    (∀ t, 3 ≤ t → W t = 0) :=
  ⟨fun t => ⟨W_nonneg t, W_le_one t⟩, fun t h1 h2 => W_eq_one h1.le h2,
    fun t h => W_eq_zero (Or.inr (by linarith))⟩

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # C3P_Shift: one-variable contour shifts of vertical line integrals

* `C3P_shift`: no pole, with a decaying integrable majorant `g (Im s)` on the strip;
* `C3P_shift_pole`: one simple pole `p` inside the strip, `f = A / (s - p)`; the majorant is only
  required on the two lines and for `|Im s| ≥ 1`.

The pole computation follows `OAI.SevenEighths.PrincipalMellinResidues.verticalIntegral_simple_pole`
(copied and adapted). -/

set_option maxHeartbeats 1000000

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace C3P

/-! ### A simple pole -/

end C3P

end ArtinPrimitiveRoots

end
end

section
section
/-!
# L3Q_Mel: Mellin inversion of `W` against Dirichlet series, and contour shifts

* `tsum_W_eq`: `∑ b_i W(x_i) = (2π)⁻¹ ∫ Wm(σ+it) ∑ b_i x_i^{-(σ+it)} dt` (absolute convergence).
* `shift_hol`, `shift_pole`: shifting `∫ Wm(σ+it) h(σ+it) dt` across a strip where `h` is
  holomorphic (resp. `A/(w − p)` with `A` holomorphic) and polynomially bounded.
* `norm_integral_Wm_le`: `‖∫ Wm(σ+it) Φ(t) dt‖ ≤ B · IW σ A` when `‖Φ t‖ ≤ B (1+|t|)^A`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open MeasureTheory Complex Filter Topology
open scoped Real

/-! ### The polynomial majorant -/

/-! ### Mellin inversion against a Dirichlet series -/

/-! ### Bounding a line integral -/

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Sq: `a = s r²` with `s` squarefree, and coprimality bookkeeping

* `sqdec_exists`, `sqdec_unique`: every nonzero ideal is uniquely `s r²` with `s` squarefree.
* `tsum_sqdec`: `∑'_a f a = ∑'_{(s, r)} f (s r²)` when `f ⊥ = 0`.
* `sfree_gt_iff`: `(∀ 𝔟, 𝔟² ∣ s r² → L N𝔟² < N(s r²)) ↔ L < N s` (GL's `s(a) > L`).
* `cop`: coprimality to a finite set of primes; `sup_eq_top_iff_cop`; transfer to `s r²`.
-/

open NumberField UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots.L3Q

open GLW

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma absNorm_pos {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (0 : ℝ) < Ideal.absNorm I := by
  have : Ideal.absNorm I ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  exact_mod_cast Nat.pos_of_ne_zero this

/-! ### Coprimality -/

lemma sup_mul_eq_top_iff {I J K : Ideal (𝓞 F)} : I * J ⊔ K = ⊤ ↔ I ⊔ K = ⊤ ∧ J ⊔ K = ⊤ := by
  simp only [← Ideal.isCoprime_iff_sup_eq]
  exact IsCoprime.mul_left_iff

lemma mem_sqfRows {𝔪 : Ideal (𝓞 F)} {Y : ℝ} {a : Ideal (𝓞 F)} :
    a ∈ sqfRows 𝔪 Y ↔ IsExterior 𝔪 a ∧ Squarefree a ∧ (Ideal.absNorm a : ℝ) ≤ Y := by
  unfold sqfRows; rw [Set.Finite.mem_toFinset]; rfl

lemma mem_primesOf {𝔤 P : Ideal (𝓞 F)} : P ∈ primesOf 𝔤 ↔ P ∈ normalizedFactors 𝔤 := by
  unfold primesOf; rw [Multiset.mem_toFinset]

lemma primesOf_prime {𝔤 P : Ideal (𝓞 F)} (h : P ∈ primesOf 𝔤) : P.IsPrime ∧ P ≠ ⊥ := by
  have hp := prime_of_normalized_factor P (mem_primesOf.1 h)
  exact ⟨Ideal.isPrime_of_prime hp, by rw [← Ideal.zero_eq_bot]; exact hp.ne_zero⟩

lemma le_of_mem_primesOf {𝔤 P : Ideal (𝓞 F)} (h : P ∈ primesOf 𝔤) : 𝔤 ≤ P :=
  Ideal.le_of_dvd (dvd_of_mem_normalizedFactors (mem_primesOf.1 h))

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Zeta: `(s − 1) ζ_F(s)` and the coprime partial zeta functions

From the seam `exists_differentiable_eq_sub_one_mul_dedekindZeta_and_norm_le_and_tsum_indicator_eq`.
* `R0 F`: entire, `= (s − 1) ζ_F(s)` on `Re s > 1`, polynomially bounded on `−1/2 ≤ Re s ≤ X`.
* `zeta_tsum`, `zeta_cop`: `ζ_F(s) = ∑' N I^{-s}`; `∑'_{I ⊔ q = ⊤} N I^{-s} = ζ_F(s) ∏_{P ∣ q}(1 − N P^{-s})`.
* `summable_norm_cpow`, `summable_absNorm_rpow`, `sieve`: the Dirichlet series and its Euler factors.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex

variable (F : Type*) [Field F] [NumberField F]

instance fiber_finite_L3Q (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

variable {F}

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-- The generator of the unit ideal is a unit of `R`. -/
lemma isUnit_gen_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) :
    IsUnit (g.gen ⊤) := by
  have h := g.span_gen ⊤ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.map_top] at h
  exact Ideal.span_singleton_eq_top.mp h

lemma normalizedFactors_top : normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
  rw [← Ideal.one_eq_top, normalizedFactors_one]

lemma residueSymbol_top (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 ⊤ x = 1 := by
  simp [residueSymbol, normalizedFactors_top]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Unit: `U_S⁶`-invariance of `poissonFactor`, and `u = 1` for the principal class

* `exists_sub_mem_map`: `𝓞/P → R/PR` is onto for `P ∉ S`; hence Fermat in `R/PR`.
* `sexticResidueSymbol_unit_pow_six`: `χ_P(μ⁶ x) = χ_P(x)` when `6 ∣ N P − 1`.
* `poissonFactor_unit_pow_six`: `F(𝔰, 𝔄, μ⁶ h) = F(𝔰, 𝔄, h)` for exterior `𝔰, 𝔄` whose prime
  factors all have `6 ∣ N P − 1`.
* `freqElt_principalFreq`: the principal frequency element is `μ⁶` for an `S`-unit `μ`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

section residue

variable {𝔪 : Ideal (𝓞 F)}

lemma coe_algebraMap_SInt (x : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) x : SInt 𝔪) : F) = (x : F) := rfl

lemma card_quot (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥) [Fintype (𝓞 F ⧸ P)] :
    Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end residue

section gen

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end gen

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Good: exterior primes satisfy `6 ∣ N P − 1` once `S` contains the primes above `2, 3` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-- A prime of norm divisible by the rational prime `p` has norm at most `p^[F:ℚ]`. -/
theorem absNorm_le_of_prime_dvd (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥)
    [P.IsMaximal] (hpd : p ∣ Ideal.absNorm P) :
    Ideal.absNorm P ≤ p ^ Module.finrank ℤ (𝓞 F) := by
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard := card_quot P hP0
  obtain ⟨f, hq, hpf⟩ := FiniteField.card (𝓞 F ⧸ P) (ringChar (𝓞 F ⧸ P))
  rw [hcard] at hpf
  rw [hpf] at hpd
  have hpq : p = ringChar (𝓞 F ⧸ P) :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpd)
  have hp0 : ((p : ℕ) : 𝓞 F ⧸ P) = 0 := by rw [hpq]; exact ringChar.Nat.cast_ringChar
  have hmem : (p : 𝓞 F) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hp0
  have hle : Ideal.span {(p : 𝓞 F)} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hn : Algebra.norm ℤ (p : 𝓞 F) = (p : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
    rw [show (p : 𝓞 F) = algebraMap ℤ (𝓞 F) p by simp, Algebra.norm_algebraMap]
  rw [hn, Int.natAbs_pow, Int.natAbs_natCast] at hdvd
  exact Nat.le_of_dvd (pow_pos hp.pos _) hdvd

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Res: the residue rings `R / P^j R` at a prime `P ∉ S`

For a height-one prime `v` of `𝓞 F` outside `S = placesOf 𝔪`:
* `mem_map_pow_iff`: `r ∈ v^j R ↔ v(r) ≤ exp(-j)` for `r ∈ R`;
* `quotEquiv`: `𝓞/v^j ≃+* R/v^j R`; `natCard_quot`: `#(R/v^j R) = N(v)^j`;
* `isMaximal_map`: `v R` is maximal;
* `finsum_quot_fibre`: summing a function that only depends on the class mod `v^i R`
  over `R/v^j R` (`i ≤ j`) gives `N(v)^(j-i)` times the sum over `R/v^i R`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section val

variable {v : HeightOneSpectrum (𝓞 F)}

lemma coe_alg (a : 𝓞 F) : ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a :=
  rfl

lemma val_le_one (hv : v ∉ placesOf 𝔪) (r : SInt 𝔪) : v.valuation F (r : F) ≤ 1 := r.2 v hv

lemma val_alg (a : 𝓞 F) : v.valuation F (algebraMap (𝓞 F) F a) = v.intValuation a :=
  v.valuation_of_algebraMap a

/-- Elements of `v^j R` have valuation at most `exp(-j)`. -/
lemma val_le_of_mem (hv : v ∉ placesOf 𝔪) (j : ℕ) {r : SInt 𝔪}
    (hr : r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (r : F) ≤ exp (-(j : ℤ)) := by
  rw [Ideal.map] at hr
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coe_alg, val_alg]
    exact (v.intValuation_le_pow_iff_mem a j).2 ha
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add]
    exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    rw [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (a : F) * v.valuation F (x : F) ≤ 1 * exp (-(j : ℤ)) :=
          mul_le_mul' (val_le_one hv a) hx
      _ = _ := one_mul _

/-- An element of `𝓞` not in `v` has an inverse modulo `v^j`. -/
lemma exists_mul_sub_one_mem (j : ℕ) {d : 𝓞 F} (hd : d ∉ v.asIdeal) :
    ∃ c : 𝓞 F, c * d - 1 ∈ v.asIdeal ^ j := by
  have h1 : IsCoprime v.asIdeal (Ideal.span {d}) := by
    obtain ⟨y, i, hi, hyi⟩ := v.isMaximal.exists_inv hd
    exact Ideal.isCoprime_iff_exists.mpr ⟨i, hi, y * d, Ideal.mul_mem_left _ _
      (Ideal.mem_span_singleton_self d), by rw [add_comm]; exact hyi⟩
  obtain ⟨i, hi, x, hx, hix⟩ := (h1.pow_left (m := j)).exists
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  refine ⟨c, ?_⟩
  have : c * d - 1 = -i := by linear_combination hix
  rw [this]
  exact neg_mem hi

/-- Every `x ∈ F` with `v(x) ≤ 1` is congruent modulo `v^j` (in valuation) to an element of `𝓞`. -/
lemma exists_val_sub_le (j : ℕ) (x : F) (hx : v.valuation F x ≤ 1) :
    ∃ a : 𝓞 F, v.valuation F (x - algebraMap (𝓞 F) F a) ≤ exp (-(j : ℤ)) := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) x hx
  obtain ⟨c, hc⟩ := exists_mul_sub_one_mem (v := v) j hd
  refine ⟨c * n, ?_⟩
  have hvd : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
  have heq : x - algebraMap (𝓞 F) F (c * n) =
      -(x * algebraMap (𝓞 F) F (c * d - 1)) := by
    have hnd' : x * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n := hnd
    rw [map_mul, ← hnd', map_sub, map_mul, map_one]; ring
  rw [heq, Valuation.map_neg, map_mul, val_alg]
  calc v.valuation F x * v.intValuation (c * d - 1) ≤ 1 * exp (-(j : ℤ)) :=
        mul_le_mul' hx ((v.intValuation_le_pow_iff_mem _ j).2 hc)
    _ = _ := one_mul _

/-- Elements of `R` of valuation at most `exp(-j)` lie in `v^j R`. -/
lemma mem_of_val_le (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪)
    (h : v.valuation F (r : F) ≤ exp (-(j : ℤ))) :
    r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) (r : F) (r.2 v hv)
  have hnd' : (r : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n := hnd
  have hvd : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
  have hn : n ∈ v.asIdeal ^ j := by
    rw [← v.intValuation_le_pow_iff_mem, ← val_alg (v := v), ← hnd', map_mul, hvd, mul_one]
    exact h
  obtain ⟨c, hc⟩ := exists_mul_sub_one_mem (v := v) j hd
  have heq : r = algebraMap (𝓞 F) (SInt 𝔪) (c * n) -
      r * algebraMap (𝓞 F) (SInt 𝔪) (c * d - 1) := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, Subalgebra.coe_mul, coe_alg, coe_alg, map_mul, map_sub, map_mul,
      map_one, ← hnd']
    ring
  rw [heq]
  exact sub_mem (Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hn))
    (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hc))

lemma mem_map_pow_iff (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪) :
    r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      v.valuation F (r : F) ≤ exp (-(j : ℤ)) :=
  ⟨val_le_of_mem hv j, mem_of_val_le hv j r⟩

lemma alg_mem_map_pow_iff (hv : v ∉ placesOf 𝔪) (j : ℕ) (a : 𝓞 F) :
    algebraMap (𝓞 F) (SInt 𝔪) a ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      a ∈ v.asIdeal ^ j := by
  rw [mem_map_pow_iff hv, coe_alg, val_alg, v.intValuation_le_pow_iff_mem]

lemma exists_sub_mem_map_pow (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪) :
    ∃ a : 𝓞 F, r - algebraMap (𝓞 F) (SInt 𝔪) a ∈
      (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨a, ha⟩ := exists_val_sub_le (v := v) j (r : F) (r.2 v hv)
  exact ⟨a, mem_of_val_le hv j _ (by rw [Subalgebra.coe_sub, coe_alg]; exact ha)⟩

end val

section quot

variable {v : HeightOneSpectrum (𝓞 F)}

/-- `𝓞/v^j → R/v^j R`. -/
noncomputable def quotHom (𝔪 : Ideal (𝓞 F)) (I : Ideal (𝓞 F)) :
    𝓞 F ⧸ I →+* SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.quotientMap _ (algebraMap (𝓞 F) (SInt 𝔪)) Ideal.le_comap_map

lemma quotHom_mk (I : Ideal (𝓞 F)) (a : 𝓞 F) :
    quotHom 𝔪 I (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) a) :=
  rfl

lemma quotHom_bijective (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Function.Bijective (quotHom 𝔪 (v.asIdeal ^ j)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotHom_mk, Ideal.Quotient.eq_zero_iff_mem, alg_mem_map_pow_iff hv] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_sub_mem_map_pow hv j r
    exact ⟨Ideal.Quotient.mk _ a, by rw [quotHom_mk]; exact (Ideal.Quotient.eq.mpr ha).symm⟩

/-- `𝓞/v^j ≃+* R/v^j R`. -/
noncomputable def quotEquiv (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    𝓞 F ⧸ v.asIdeal ^ j ≃+* SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  RingEquiv.ofBijective _ (quotHom_bijective hv j)

lemma finite_quot (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Finite (SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ v.asIdeal ^ j) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ v.ne_bot)
  exact Finite.of_equiv _ (quotEquiv hv j).toEquiv

lemma natCard_quot (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Nat.card (SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) =
      Ideal.absNorm v.asIdeal ^ j := by
  rw [← Nat.card_congr (quotEquiv hv j).toEquiv, ← map_pow, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

/-- `v R` is a maximal ideal of `R`. -/
lemma isMaximal_map (hv : v ∉ placesOf 𝔪) :
    (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal := by
  have e := quotEquiv (𝔪 := 𝔪) hv 1
  rw [pow_one] at e
  apply Ideal.Quotient.maximal_of_isField
  have : (v.asIdeal).IsMaximal := v.isMaximal
  have hf : IsField (𝓞 F ⧸ v.asIdeal) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp this
  exact MulEquiv.isField hf e.symm.toMulEquiv

end quot

section fibre

variable {v : HeightOneSpectrum (𝓞 F)}

end fibre

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3H_Core: finite bilinear-form bounds and the row-multiplication step (GL Lemma 4.4)

`SBf χ R Cs v`: for every coefficient vector `z`, `∑_{a ∈ R} |∑_{c ∈ Cs} z c χ a c|² ≤ v ∑ |z c|²`.

* `SBf.mono_rows`, `SBf.union`, `SBf.biUnion`: row-set bookkeeping.
* `SBf.of_inj`: rows that map injectively into `R'` with `χ a c = w c χ (f a) c`, `‖w c‖ ≤ 1`.
* `SBf.lift`: Heath-Brown's Lemma 9 (GL Lemma 4.4) in abstract form: if rows can be multiplied by
  any of a family `P` of "primes", each row or column being divisible by at most `ω` of them and
  `8 ω ≤ #P`, then a bound `W` for the multiplied rows gives the bound `8 W`.
-/

namespace L3H

open Finset

variable {I : Type*}

/-- The finite sieve-form bound. -/
def SBf (χ : I → I → ℂ) (R Cs : Finset I) (v : ℝ) : Prop :=
  ∀ z : I → ℂ, ∑ a ∈ R, ‖∑ c ∈ Cs, z c * χ a c‖ ^ 2 ≤ v * ∑ c ∈ Cs, ‖z c‖ ^ 2

variable {χ : I → I → ℂ}

theorem SBf.mono_v {R Cs : Finset I} {v v' : ℝ} (h : SBf χ R Cs v) (hv : v ≤ v') :
    SBf χ R Cs v' := fun z =>
  (h z).trans (mul_le_mul_of_nonneg_right hv (sum_nonneg fun _ _ => by positivity))

theorem SBf.mono_rows {R R' Cs : Finset I} {v : ℝ} (h : SBf χ R' Cs v) (hR : R ⊆ R') :
    SBf χ R Cs v := fun z =>
  le_trans (sum_le_sum_of_subset_of_nonneg hR fun _ _ _ => by positivity) (h z)

theorem SBf.mono_cols {R Cs Cs' : Finset I} {v : ℝ} (h : SBf χ R Cs v) (hC : Cs' ⊆ Cs) :
    SBf χ R Cs' v := by
  classical
  intro z
  have := h (fun c => if c ∈ Cs' then z c else 0)
  have e1 : ∀ a, ∑ c ∈ Cs, (if c ∈ Cs' then z c else 0) * χ a c = ∑ c ∈ Cs', z c * χ a c := by
    intro a
    rw [← sum_subset hC (f := fun c => (if c ∈ Cs' then z c else 0) * χ a c)]
    · exact sum_congr rfl fun c hc => by rw [if_pos hc]
    · intro c _ hc; rw [if_neg hc, zero_mul]
  have e2 : ∑ c ∈ Cs, ‖(if c ∈ Cs' then z c else 0)‖ ^ 2 = ∑ c ∈ Cs', ‖z c‖ ^ 2 := by
    rw [← sum_subset hC (f := fun c => ‖(if c ∈ Cs' then z c else 0)‖ ^ 2)]
    · exact sum_congr rfl fun c hc => by rw [if_pos hc]
    · intro c _ hc; simp [hc]
  simp only [e1, e2] at this
  exact this

end L3H

end
end

section
section
/-! # L3H_NT: the quadratic family `χ_𝔠(𝔡) = residueSymbol 𝔡 (gen 𝔠)³` as a finite kernel

* `rowsF 𝔪 lo hi`: exterior squarefree ideals with `lo < N 𝔡 ≤ hi`, as a `Finset`.
* `chiK ι 𝔪 g 𝔡 𝔠 = residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) ^ 3`.
* `chiK_mul_row`: `χ(a) = w · χ(a p)` with `‖w‖ = 1` for an exterior good prime `p ∤ 𝔠`.
* `sb_iff_dyadic`, `sb_of_SBf`: the `tsum`-over-subtypes statements against `SBf`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

/-! ### Residue symbols -/

lemma rs_mul {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

/-! ### Multiplicativity of the symbol (without `C3I.chi`) -/

/-! ### The kernel -/

/-- `χ_𝔠(𝔡)`, the quadratic symbol of the family. -/
noncomputable def chiK (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪)
    (𝔡 𝔠 : Ideal (𝓞 F)) : ℂ :=
  residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) ^ 3

/-! ### Ideal facts -/

/-! ### Row and column sets -/

lemma fin_set (𝔪 : Ideal (𝓞 F)) (lo hi : ℝ) :
    {𝔡 : Ideal (𝓞 F) | IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ lo < (Ideal.absNorm 𝔡 : ℝ) ∧
      (Ideal.absNorm 𝔡 : ℝ) ≤ hi}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊hi⌋₊).subset
    (fun 𝔡 h => Nat.le_floor h.2.2.2)

/-- Exterior squarefree ideals with `lo < N 𝔡 ≤ hi`. -/
noncomputable def rowsF (𝔪 : Ideal (𝓞 F)) (lo hi : ℝ) : Finset (Ideal (𝓞 F)) :=
  (fin_set 𝔪 lo hi).toFinset

lemma mem_rowsF {𝔪 : Ideal (𝓞 F)} {lo hi : ℝ} {𝔡 : Ideal (𝓞 F)} :
    𝔡 ∈ rowsF 𝔪 lo hi ↔ IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ lo < (Ideal.absNorm 𝔡 : ℝ) ∧
      (Ideal.absNorm 𝔡 : ℝ) ≤ hi := by
  unfold rowsF; rw [Set.Finite.mem_toFinset]; rfl

lemma one_le_absNorm {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (1 : ℝ) ≤ Ideal.absNorm I := by
  have : Ideal.absNorm I ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

lemma mem_rowsF_zero {𝔪 : Ideal (𝓞 F)} {hi : ℝ} {𝔡 : Ideal (𝓞 F)} :
    𝔡 ∈ rowsF 𝔪 0 hi ↔ IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ hi := by
  rw [mem_rowsF]
  constructor
  · rintro ⟨h1, h2, -, h4⟩; exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h4⟩
    exact ⟨h1, h2, lt_of_lt_of_le zero_lt_one (one_le_absNorm h1.1), h4⟩

/-! ### `tsum` over subtypes -/

lemma tsum_subtype_eq {β E : Type*} [AddCommMonoid E] [TopologicalSpace E] (p : β → Prop)
    (S : Finset β) (hS : ∀ x, x ∈ S ↔ p x) (f : β → E) :
    ∑' x : {x // p x}, f x.1 = ∑ x ∈ S, f x := by
  rw [← Finset.tsum_subtype S f]
  exact (Equiv.subtypeEquivRight (fun x => (hS x).symm)).tsum_eq (fun x => f x.1)

variable (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪)

end L3H

end
end

section
section
/-!
# L3Q_Orig: the part `s(a) ≤ L` of the original sum (GL's `T′` plus the error `RP`)

For a pair character `ψ` (`PsiHyp`) and `q = 𝔤 𝔪 c`:
`∑_{a ⊔ 𝔤 = ⊤, s(a) ≤ L} W(Na/M) ψ(a) = ∑_{s ∈ Srow} ψ(s) [κ (Ns/M)^{-1/2} Wm(1/2) ∏_{P∣q}(1 − 1/NP)
  + (2π)⁻¹ ∫ Wm(ε+it) (Ns/M)^{-(ε+it)} ∏_{P∣q}(1 − NP^{-2(ε+it)}) R0(2(ε+it))/(2(ε+it) − 1) dt]`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Filter Topology
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

instance countable_ideal_L3Q : Countable (Ideal (𝓞 F)) :=
  (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)).symm.injective.countable

lemma sqfRows_eq (𝔪 : Ideal (𝓞 F)) (Y : ℝ) : sqfRows 𝔪 Y = L3H.rowsF 𝔪 0 Y := by
  ext a; rw [mem_sqfRows, L3H.mem_rowsF_zero]

lemma Srow_def (𝔪 𝔤 : Ideal (𝓞 F)) (L : ℝ) :
    Srow 𝔪 𝔤 L = haveI := Classical.decEq (Ideal (𝓞 F));
      (L3H.rowsF 𝔪 0 L).filter (fun s => s ⊔ 𝔤 = ⊤) := by
  unfold Srow; rw [sqfRows_eq]

lemma tsum_subtype_of_zero' {β E : Type*} [AddCommMonoid E] [TopologicalSpace E] (p : β → Prop)
    (S : Finset β) (hS : ∀ x ∈ S, p x) (f : β → E) (hf : ∀ x, p x → x ∉ S → f x = 0) :
    ∑' x : {x // p x}, f x.1 = ∑ x ∈ S, f x := by
  classical
  change ∑' x : ({x | p x} : Set β), f x = _
  rw [tsum_subtype, tsum_eq_sum (s := S)]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [Set.indicator_of_mem (show x ∈ {x | p x} from hS x hx)]
  · intro x hx
    by_cases h : p x
    · rw [Set.indicator_of_mem (show x ∈ {x | p x} from h)]; exact hf x h hx
    · rw [Set.indicator_of_notMem (show x ∉ {x | p x} from h)]

lemma W_div_eq_zero {M x : ℝ} (hM : 0 < M) (hx : 3 * M ≤ x) : W (x / M) = 0 :=
  W_eq_zero (Or.inr (by rw [lt_div_iff₀ hM]; linarith))

lemma one_le_absNorm_of_mem_primesOf {q P : Ideal (𝓞 F)} (hP : P ∈ primesOf q) :
    1 ≤ Ideal.absNorm P := by
  have := (primesOf_prime hP).2
  exact Nat.one_le_iff_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact this)

lemma W_zero : W 0 = 0 := W_eq_zero (Or.inl (by norm_num))

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # L3K_Gamma: the Gamma-factor ratio on the left edge of the convexity strip

* `norm_Gamma_mono`: `σ ↦ ‖Γ(σ + it)‖ / Γ(σ)` is nondecreasing on `σ > 0` (Gauss's product).
* `norm_Gamma_one_add_sq`: `‖Γ(1 + it)‖² = π |t| / |sinh(π t)|`.
* `exists_norm_Gammaℂ_ratio_le`: for `0 < δ < 1`,
  `‖Γ_ℂ(1 + δ − it) / Γ_ℂ(−δ + it)‖ ≤ C (1 + |t|)^3`. -/

open Complex Filter Topology

set_option autoImplicit false

namespace ArtinPrimitiveRoots

namespace L3K

end L3K

end ArtinPrimitiveRoots

end
end

section
section
/-!
# L3Q_Gam: the gamma ratio `G₀(w) = Γ_ℂ(1−w)/Γ_ℂ(w)`

`G₀ w = (2π)^{2w−1} Γ(1−w)² sin(πw) / π`: holomorphic on `Re w < 1`, equal to `Γ_ℂ(1−w)/Γ_ℂ(w)` off
the poles, `G₀(1/2) = 1`, and polynomially bounded on closed vertical strips inside `Re w < 1`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open Complex
open scoped Real

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_DualA: Dirichlet-series identities for the dual side

`LamHyp`: the entire continuation `Λ = ζ_𝔪 · L_ext(ψ)` with the functional equation and growth
(the content of the cut). Here:
* `tsum_cop_eq`: `∑'_{a ⊔ 𝔤 = ⊤} ψ(a) N a^{-w} = Λ(w) E(w)` on `Re w > 1`;
* `fe_line`: `Λ(w) = D^{1/2−w} G₀(w)^{r₂} Λ(1−w)` off the poles;
* `Lam_eq_split`: `Λ(u) = Zm(u) ζ(2u) ∏_{P ∣ 𝔪c}(1 − NP^{-2u}) (P_{L′}(u) + Q_{L′}(u))` on `Re u > 1`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Filter Topology
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma two_le_absNorm_of_mem_primesOf {q P : Ideal (𝓞 F)} (hP : P ∈ primesOf q) :
    2 ≤ Ideal.absNorm P := by
  have h1 := one_le_absNorm_of_mem_primesOf hP
  have hne : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact (primesOf_prime hP).1.ne_top
  omega

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_DualB: kernels and bounds for the dual side

`Kd(w) = M^w E(w) D^{1/2−w} G₀(w)^{r₂} ζ_𝔪(1−w) ∏_{P ∣ 𝔪c}(1 − NP^{-2(1−w)})`, the finite
Dirichlet polynomial `Pf` and the tail `Qf`; holomorphy and polynomial bounds on strips.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Filter Topology
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

/-! ### Polynomial bounds -/

/-! ### The dual kernels -/

/-! ### Bounds and holomorphy of the kernels -/

/-! ### Holomorphy -/

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_DualC: the full sum via the functional equation (GL's `T` plus `DP` and `DQ`)

`∑_{a ⊔ 𝔤 = ⊤} W(Na/M) ψ(a) = T + (2π)⁻¹ ∫_{(1−ε′)} Wm Kd R0(2(1−w))/(1−2w) P_{L′}(1−w)
  + (2π)⁻¹ ∫_{(−σ₁)} Wm Kd ζ(2(1−w)) Q_{L′}(1−w)`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Filter Topology
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # L3H_Mob: Möbius function and divisor counts for squarefree ideals of `𝓞 F`

* `pf n`: the set of prime factors; for squarefree `n ≠ ⊥`, `∏_{p ∈ pf n} p = n`.
* `mobI`: `μ(d) = (-1)^ω(d)` on squarefree `d`, `0` otherwise.
* `sum_mobI`: `∑_{d ∈ S, d ∣ n} μ(d) = [n = ⊤]` for squarefree `n ≠ ⊥`, if `S` holds every divisor.
* `card_dvd_le`: `#{d ∈ S, d ∣ n} ≤ 2^ω(n)` for squarefree `n ≠ ⊥`.
* `two_pow_card_pf_le`: `2^ω(n) ≤ C_ε (N n)^ε` for squarefree `n ≠ ⊥`.
-/

open NumberField UniqueFactorizationMonoid

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

open Classical in
/-- The prime factors. -/
noncomputable def pf (n : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) := (normalizedFactors n).toFinset

lemma nodup_of_sq {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) :
    (normalizedFactors n).Nodup :=
  (squarefree_iff_nodup_normalizedFactors hn0).1 hn

open Classical in
lemma pf_val {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) :
    (pf n).val = normalizedFactors n := by
  unfold pf; rw [Multiset.toFinset_val, Multiset.dedup_eq_self.2 (nodup_of_sq hn0 hn)]

lemma prod_pf {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) : ∏ p ∈ pf n, p = n := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id', pf_val hn0 hn]
  exact Ideal.prod_normalizedFactors_eq_self hn0

lemma prime_of_mem_pf {n p : Ideal (𝓞 F)} (hp : p ∈ pf n) : Prime p := by
  unfold pf at hp; rw [Multiset.mem_toFinset] at hp
  exact prime_of_normalized_factor p hp

lemma absNorm_eq_prod_pf {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) :
    (Ideal.absNorm n : ℝ) = ∏ p ∈ pf n, (Ideal.absNorm p : ℝ) := by
  conv_lhs => rw [← prod_pf hn0 hn]
  rw [map_prod, Nat.cast_prod]

/-- The divisor bound `2^ω(n) ≤ C_ε (N n)^ε` on squarefree ideals. -/
theorem two_pow_card_pf_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : Ideal (𝓞 F), n ≠ ⊥ → Squarefree n →
      (2 : ℝ) ^ (pf n).card ≤ C * (Ideal.absNorm n : ℝ) ^ ε := by
  classical
  set B : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  set small : Finset (Ideal (𝓞 F)) :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) B).toFinset
  refine ⟨2 ^ small.card, by positivity, fun n hn0 hn => ?_⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := pf n) (fun p => p ∈ small)
  have hs : ((pf n).filter (fun p => p ∈ small)).card ≤ small.card :=
    Finset.card_le_card fun p hp => (Finset.mem_filter.1 hp).2
  have hlarge : (2 : ℝ) ^ ((pf n).filter (fun p => p ∉ small)).card ≤
      (Ideal.absNorm n : ℝ) ^ ε := by
    rw [absNorm_eq_prod_pf hn0 hn, ← Real.finset_prod_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
    rw [← Finset.prod_const]
    calc ∏ _p ∈ (pf n).filter (fun p => p ∉ small), (2 : ℝ)
        ≤ ∏ p ∈ (pf n).filter (fun p => p ∉ small), (Ideal.absNorm p : ℝ) ^ ε := by
          refine Finset.prod_le_prod (fun _ _ => by norm_num) fun p hp => ?_
          have hp' := (Finset.mem_filter.1 hp).2
          have hB : (B : ℝ) < Ideal.absNorm p := by
            by_contra h
            push Not at h
            apply hp'
            rw [Set.Finite.mem_toFinset]
            exact_mod_cast h
          have h2 : (2 : ℝ) ^ (1 / ε) ≤ B := Nat.le_ceil _
          have h3 : (2 : ℝ) ^ (1 / ε) ≤ Ideal.absNorm p := le_trans h2 hB.le
          calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
                rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
            _ ≤ (Ideal.absNorm p : ℝ) ^ ε :=
                Real.rpow_le_rpow (by positivity) h3 hε.le
      _ ≤ ∏ p ∈ pf n, (Ideal.absNorm p : ℝ) ^ ε := by
          rw [← Finset.prod_filter_mul_prod_filter_not (pf n) (fun p => p ∉ small)]
          have h1 : (1 : ℝ) ≤ ∏ p ∈ (pf n).filter (fun p => ¬ p ∉ small),
              (Ideal.absNorm p : ℝ) ^ ε := by
            rw [← Finset.prod_const_one (s := (pf n).filter (fun p => ¬ p ∉ small))]
            refine Finset.prod_le_prod (fun _ _ => zero_le_one) ?_
            intro p hp
            have hp0 : p ≠ ⊥ := (prime_of_mem_pf (Finset.mem_filter.1 hp).1).ne_zero
            have : Ideal.absNorm p ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hp0
            have : (1 : ℝ) ≤ Ideal.absNorm p := by exact_mod_cast Nat.one_le_iff_ne_zero.2 this
            exact Real.one_le_rpow this hε.le
          have h0 : 0 ≤ ∏ p ∈ (pf n).filter (fun p => p ∉ small), (Ideal.absNorm p : ℝ) ^ ε :=
            Finset.prod_nonneg fun _ _ => by positivity
          nlinarith
  calc (2 : ℝ) ^ (pf n).card
      = 2 ^ ((pf n).filter (fun p => p ∈ small)).card *
          2 ^ ((pf n).filter (fun p => p ∉ small)).card := by rw [← pow_add, hsplit]
    _ ≤ 2 ^ small.card * (Ideal.absNorm n : ℝ) ^ ε := by
        gcongr
        · norm_num

end L3H

end
end

section
section
/-!
# L3Q_TT: the two main terms `T` and `T′`

`T − T′ = κ √M Wm(1/2) ∏_{P ∣ 𝔪c}(1 − 1/NP) ∑_{e, f ⊆ primes(𝔤)} (−1)^{|e|} (NeNf)^{-1/2} ψ(e)ψ(f)
  ∑_{s coprime 𝔤} (1[Ns ≤ L′/Nf] − 1[Ns ≤ L]) ψ(s) Ns^{-1/2}`: only rows between `L′/Nf` and `L`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Filter Topology UniqueFactorizationMonoid
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma primesOf_mul {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    primesOf (I * J) = primesOf I ∪ primesOf J := by
  classical
  ext P
  rw [Finset.mem_union, mem_primesOf, mem_primesOf, mem_primesOf,
    normalizedFactors_mul (by rwa [Ne, ← Ideal.zero_eq_bot] at hI)
      (by rwa [Ne, ← Ideal.zero_eq_bot] at hJ), Multiset.mem_add]

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # C3B_Main: (7.16)–(7.17) at `u = 1` from four arithmetic cuts

With `b(𝔠, 𝔫, 𝔰, 𝔯) = γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, gen(𝔯)⁶)` (the coefficient at `u = 1`, without the
`S`-unit `u`), the target `exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul` follows from

* `CutMul`: cross-prime multiplicativity `b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀},P^l,P^k,P^m) b(𝔠,𝔫,𝔰,𝔯)`
  ((7.14), (7.16): Chinese remainders + reciprocity (3.3));
* `CutF`: the local Poisson factor `F(P^k, P^{e₀}(P^l)³, gen(P^m)⁶)` ((7.15), (7.17));
* `CutHD`: `γ₁(P) γ₂(P) Λ̄(P) Ḡ(P) = −1` (Davenport–Hasse, (3.9)–(3.11));
* `CutG6`: `Ḡ(P)⁶ = 1`.

Proved here: `a(1,1,1,1) = 1` (`C3B_Norm`), the `U_S⁶`-invariance replacing `u` by `1`
(`C3B_Unit`, `C3B_Good`), `ϑ` on prime powers, `Λ⁶ = jacobiPhaseSix`, and the table algebra. -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Elementary lemmas -/

lemma normalizedFactors_prime_pow {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (t : ℕ) :
    normalizedFactors (P ^ t) = Multiset.replicate t P := by
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [normalizedFactors_pow, normalizedFactors_irreducible hirr, normalize_eq,
    Multiset.nsmul_singleton]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Add: the additive character `e`

* `HasWit 𝔪 x`: `x` has a witness `y` in the definition of `sAddChar` (`x - y ∈ R`, `y` integral
  at `S`). `hasWit_of_mul_mem`: true when `x I ⊆ R` for an ideal `I` coprime to `𝔪`; in particular
  `hasWit_div_gen`: `a / gen 𝔞` for `a ∈ R`, `𝔞` exterior.
* `sAddChar_eq_of_wit`: `e(x) = exp(-2πi Tr y)` for every witness; `sAddChar_add`: `e` is additive
  on elements with witnesses.
* `exists_trace_not_int`: for `P ∤ 𝔇`, some `z ∈ P⁻¹` has `Tr z ∉ ℤ`; `sAddChar_ne_one_of_dual`.
* `exists_sAddChar_ne_one`: primitivity at every level: for `x ∈ R ∖ P^j R` some `r ∈ R` has
  `e(x r / gen(P^j)) ≠ 1`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {ι : F →+* ℂ}

/-! ### The inverse different -/

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

end prim

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Base: hypotheses from section A, finite quotients `R/𝔞R`, residue-symbol algebra

* `HypAdd 𝔪`: `e` is additive on `F` (needs the existence of `sAddChar` witnesses).
* `HypChi ι 𝔪`: at every exterior prime `P`, `χ_P` is multiplicative on `R` and `χ_P(x)⁶ = 1`
  for `x ∉ PR`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- Hypothesis (section A): at an exterior prime, the sextic symbol is multiplicative on `R`, with
sixth power `1` off `PR`. -/
def HypChi (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P →
    (∀ x y : SInt 𝔪, sexticResidueSymbol ι 𝔪 P (x * y) =
      sexticResidueSymbol ι 𝔪 P x * sexticResidueSymbol ι 𝔪 P y) ∧
    (∀ x : SInt 𝔪, x ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) → sexticResidueSymbol ι 𝔪 P x ^ 6 = 1)

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Ideals -/

lemma exterior_of_mem_factors {𝔞 Q : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (hQ : Q ∈ normalizedFactors 𝔞) : Q.IsPrime ∧ IsExterior 𝔪 Q := by
  have hpr : Prime Q := prime_of_normalized_factor Q hQ
  refine ⟨Ideal.isPrime_of_prime hpr, hpr.ne_zero, ?_⟩
  have hle : 𝔞 ≤ Q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ)
  exact eq_top_iff.mpr (h𝔞.2 ▸ sup_le_sup_right hle 𝔪)

lemma isExterior_of_mul_left {I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) : IsExterior 𝔪 I := by
  refine ⟨fun h0 => h.1 (by rw [h0, Ideal.bot_mul]), ?_⟩
  exact eq_top_iff.mpr (h.2 ▸ sup_le_sup_right (Ideal.mul_le_inf.trans inf_le_left) 𝔪)

lemma isExterior_of_mul_right {I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) :
    IsExterior 𝔪 J := by
  rw [mul_comm] at h; exact isExterior_of_mul_left h

/-- An exterior prime does not become the unit ideal in `R`. -/
lemma map_ne_top {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQe : IsExterior 𝔪 Q) :
    Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≠ ⊤ := by
  intro htop
  let v : HeightOneSpectrum (𝓞 F) := ⟨Q, hQ, hQe.1⟩
  have hvS : v ∉ placesOf 𝔪 := by
    intro hv
    have : (⊤ : Ideal (𝓞 F)) ≤ Q := hQe.2 ▸ sup_le le_rfl hv
    exact hQ.ne_top (eq_top_iff.mpr this)
  let J : Ideal (SInt 𝔪) :=
    { carrier := {x | v.valuation F (x : F) < 1}
      add_mem' := fun {a b} ha hb => by
        show v.valuation F ((a + b : SInt 𝔪) : F) < 1
        rw [Subalgebra.coe_add]
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
      zero_mem' := by
        show v.valuation F ((0 : SInt 𝔪) : F) < 1
        simp
      smul_mem' := fun c x hx => by
        show v.valuation F ((c * x : SInt 𝔪) : F) < 1
        rw [Subalgebra.coe_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (c.2 v hvS)) hx }
  have hle : Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show v.valuation F ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) < 1
    rw [C3B.coe_algebraMap_SInt]
    exact (v.valuation_lt_one_iff_mem a).mpr ha
  have h1 : (1 : SInt 𝔪) ∈ J := hle (htop ▸ Submodule.mem_top)
  have : v.valuation F ((1 : SInt 𝔪) : F) < 1 := h1
  simp at this

lemma isCoprime_map {I J : Ideal (𝓞 F)} (h : IsCoprime I J) :
    IsCoprime (I.map (algebraMap (𝓞 F) (SInt 𝔪))) (J.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  rw [← Ideal.map_sup, h, Ideal.map_top]

/-! ### Residue symbols -/

variable {ι : F →+* ℂ}

lemma residueSymbol_mul_ideal (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

lemma residueSymbol_prime {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P x := by
  have h := C3B.normalizedFactors_prime_pow hP hP0 1
  rw [pow_one, Multiset.replicate_one] at h
  simp [residueSymbol, h]

lemma residueSymbol_mul (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (x y : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 (x * y) = residueSymbol ι 𝔪 𝔞 x * residueSymbol ι 𝔪 𝔞 y := by
  unfold residueSymbol
  rw [← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun Q hQ => ?_
  obtain ⟨hQp, hQe⟩ := exterior_of_mem_factors h𝔞 hQ
  exact (hχ Q hQp hQe).1 x y

lemma not_mem_of_isCoprime {I : Ideal (SInt 𝔪)} (hI : I ≠ ⊤) {x : SInt 𝔪}
    (h : IsCoprime (Ideal.span {x}) I) : x ∉ I := by
  intro hx
  apply hI
  rw [Ideal.isCoprime_iff_sup_eq] at h
  rw [eq_top_iff, ← h]
  exact sup_le ((Ideal.span_singleton_le_iff_mem I).mpr hx) le_rfl

lemma residueSymbol_pow_six (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    {x : SInt 𝔪} (hx : IsCoprime (Ideal.span {x}) (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)))) :
    residueSymbol ι 𝔪 𝔞 x ^ 6 = 1 := by
  unfold residueSymbol
  rw [← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hz
  obtain ⟨hQp, hQe⟩ := exterior_of_mem_factors h𝔞 hQ
  apply (hχ Q hQp hQe).2
  apply not_mem_of_isCoprime (map_ne_top hQp hQe)
  have hle : 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ Q.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.map_mono (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ))
  rw [Ideal.isCoprime_iff_sup_eq] at hx ⊢
  exact eq_top_iff.mpr (hx ▸ sup_le_sup_left hle _)

lemma residueSymbol_ne_zero (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    {x : SInt 𝔪} (hx : IsCoprime (Ideal.span {x}) (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)))) :
    residueSymbol ι 𝔪 𝔞 x ≠ 0 := by
  intro h0
  have := residueSymbol_pow_six hχ h𝔞 hx
  rw [h0] at this; norm_num at this

lemma isCoprime_one (I : Ideal (SInt 𝔪)) : IsCoprime (Ideal.span {(1 : SInt 𝔪)}) I := by
  rw [Ideal.span_singleton_one]; exact Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)

lemma residueSymbol_one (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    residueSymbol ι 𝔪 𝔞 1 = 1 := by
  have h := residueSymbol_mul hχ h𝔞 (1 : SInt 𝔪) 1
  rw [one_mul] at h
  have h0 := residueSymbol_ne_zero hχ h𝔞 (isCoprime_one _)
  have : residueSymbol ι 𝔪 𝔞 1 * (residueSymbol ι 𝔪 𝔞 1 - 1) = 0 := by
    rw [mul_sub, ← h]; ring
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 h0
  · exact sub_eq_zero.mp h1

lemma isCoprime_unit (u : (SInt 𝔪)ˣ) (I : Ideal (SInt 𝔪)) :
    IsCoprime (Ideal.span {(u : SInt 𝔪)}) I := by
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit]; exact Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)

lemma residueSymbol_unit_pow_six (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (u : (SInt 𝔪)ˣ) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 ((u : SInt 𝔪) ^ 6 * x) = residueSymbol ι 𝔪 𝔞 x := by
  have hp : ∀ n : ℕ, residueSymbol ι 𝔪 𝔞 ((u : SInt 𝔪) ^ n) = residueSymbol ι 𝔪 𝔞 u ^ n := by
    intro n
    induction n with
    | zero => simp [residueSymbol_one hχ h𝔞]
    | succ n ih => rw [pow_succ, residueSymbol_mul hχ h𝔞, ih, pow_succ]
  rw [residueSymbol_mul hχ h𝔞, hp, residueSymbol_pow_six hχ h𝔞 (isCoprime_unit u _), one_mul]

/-! ### Generators -/

/-- `gen(I J) = ε⁶ gen(I) gen(J)` with `ε` a unit of `R`. -/
lemma gen_mul' (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (hJ : IsExterior 𝔪 J) :
    ∃ ε : (SInt 𝔪)ˣ, g.gen (I * J) = (ε : SInt 𝔪) ^ 6 * g.gen I * g.gen J := by
  obtain ⟨ε, hε⟩ := g.gen_mul I J hI hJ
  refine ⟨Set.unitEquivUnitsInteger (placesOf 𝔪) F ε, ?_⟩
  apply Subtype.ext
  rw [hε]
  simp

lemma gen_top (g : AllowedGen ι 𝔪) : ∃ ε : (SInt 𝔪)ˣ, g.gen ⊤ = (ε : SInt 𝔪) ^ 6 := by
  obtain ⟨ε, hε⟩ := gen_mul' g ⟨top_ne_bot, top_sup_eq _⟩ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.top_mul] at hε
  obtain ⟨u, hu⟩ := C3B.isUnit_gen_top g
  refine ⟨ε⁻¹, ?_⟩
  have h1 : (u : SInt 𝔪) * 1 = (u : SInt 𝔪) * ((ε : SInt 𝔪) ^ 6 * (u : SInt 𝔪)) := by
    rw [← hu] at hε
    rw [mul_one]
    calc (u : SInt 𝔪) = (ε : SInt 𝔪) ^ 6 * u * u := hε
      _ = _ := by ring
  have h2 := u.isUnit.mul_left_cancel h1
  rw [← hu]
  have h3 : ((ε : SInt 𝔪) ^ 6) * ((↑(ε⁻¹) : SInt 𝔪) ^ 6) = 1 := by
    rw [← mul_pow, Units.mul_inv, one_pow]
  calc (u : SInt 𝔪) = (u : SInt 𝔪) * ((ε : SInt 𝔪) ^ 6 * (↑(ε⁻¹) : SInt 𝔪) ^ 6) := by
        rw [h3, mul_one]
    _ = ((ε : SInt 𝔪) ^ 6 * (u : SInt 𝔪)) * (↑(ε⁻¹) : SInt 𝔪) ^ 6 := by ring
    _ = (↑(ε⁻¹) : SInt 𝔪) ^ 6 := by rw [← h2, one_mul]

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Sum: the Poisson sum and the Gauss sum with free generators; CRT and twists

* `PS 𝔰 𝔄 s A Af c h = ∑_{d mod 𝔰} ∑_{v mod 𝔄} [h ≡ Af d (𝔰)] χ_𝔰(d) χ_𝔄(v) e((h − Af d) v c/(sA))`;
  `poissonFactor g 𝔰 𝔄 h = PS 𝔰 𝔄 (gen 𝔰) (gen 𝔄) (gen 𝔄) 1 h`.
* `GS 𝔠 c c' j = ∑_{x mod 𝔠} χ_𝔠(x)^j e(x c'/c)`; `gaussPhase g j 𝔠 = q^{-1/2} GS 𝔠 (gen 𝔠) 1 j`.
* `PS_crt`, `GS_crt`: Chinese remainders with idempotents `β s₂A₂`, `α s₁A₁`.
* `PS_twist`, `GS_twist`: unit substitutions.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

section defs

variable (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))

end defs

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Generic lemmas -/

/-! ### Coercions -/

/-! ### The Poisson summand -/

section U

variable {𝔰 𝔄 : Ideal (𝓞 F)} {s A Af c h : SInt 𝔪}

end U

/-! ### Field identities -/

/-! ### CRT and twists for `PS` -/

section crt

variable {𝔰₁ 𝔰₂ 𝔄₁ 𝔄₂ : Ideal (𝓞 F)} {s₁ s₂ A₁ A₂ Af c h α β : SInt 𝔪}

end crt

/-! ### Gauss sums -/

section gs

variable {𝔠 : Ideal (𝓞 F)} {c c' : SInt 𝔪} {j : ℕ}

end gs

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Mul: twisted multiplicativity of `γ_j`, of `F(𝔰, 𝔄, gen(𝔯)⁶)`, of `ϑ`, and reciprocity

* `gaussPhase_mul` (3.10): `γ_j(𝔠₁𝔠₂) = χ_{𝔠₁}(c₂)^j χ_{𝔠₂}(c₁)^j γ_j(𝔠₁) γ_j(𝔠₂)`.
* `poissonFactor_mul`: for `𝔰₁𝔄₁` coprime to `𝔰₂𝔄₂`, `𝔯ᵢ` coprime to the other side,
  `χ_{𝔰₁}(A₂) χ_{𝔰₂}(A₁) F(𝔰₁𝔰₂, 𝔄₁𝔄₂, gen(𝔯₁𝔯₂)⁶)
     = χ_{𝔄₁}(s₂A₂) χ_{𝔄₂}(s₁A₁) F(𝔰₁, 𝔄₁, gen(𝔯₁)⁶) F(𝔰₂, 𝔄₂, gen(𝔯₂)⁶)`.
* `residueSymbol_gen_prime`: `χ_𝔟(gen P) = χ_P(gen 𝔟)` (from (3.3)).
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Coprimality in `R` -/

/-! ### Change of generators -/

/-! ### Generators and residue symbols -/

lemma residueSymbol_gen_mul (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔞 I J : Ideal (𝓞 F)}
    (h𝔞 : IsExterior 𝔪 𝔞) (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    residueSymbol ι 𝔪 𝔞 (g.gen (I * J)) =
      residueSymbol ι 𝔪 𝔞 (g.gen I) * residueSymbol ι 𝔪 𝔞 (g.gen J) := by
  obtain ⟨ε, hε⟩ := gen_mul' g hI hJ
  rw [hε, mul_assoc, residueSymbol_unit_pow_six hχ h𝔞, residueSymbol_mul hχ h𝔞]

lemma residueSymbol_gen_top (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔞 : Ideal (𝓞 F)}
    (h𝔞 : IsExterior 𝔪 𝔞) : residueSymbol ι 𝔪 𝔞 (g.gen ⊤) = 1 := by
  obtain ⟨ε, hε⟩ := gen_top g
  rw [hε, ← mul_one ((ε : SInt 𝔪) ^ 6), residueSymbol_unit_pow_six hχ h𝔞,
    residueSymbol_one hχ h𝔞]

/-- Extended reciprocity: `χ_𝔟(gen P) = χ_P(gen 𝔟)` for an exterior `𝔟` prime to `P`. -/
lemma residueSymbol_gen_prime (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)}
    (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) (𝔟 : Ideal (𝓞 F)) :
    IsExterior 𝔪 𝔟 → ¬ 𝔟 ≤ P →
      residueSymbol ι 𝔪 𝔟 (g.gen P) = residueSymbol ι 𝔪 P (g.gen 𝔟) := by
  induction 𝔟 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h.1
  | h₂ u hu =>
    intro hue _
    have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
    subst hu'
    rw [C3B.residueSymbol_top, residueSymbol_gen_top hχ g hPe]
  | h₃ 𝔞 Q _ hQ ih =>
    intro hQa hle
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
    have hQe : IsExterior 𝔪 Q := isExterior_of_mul_left hQa
    have hae : IsExterior 𝔪 𝔞 := isExterior_of_mul_right hQa
    have hQP : ¬ Q ≤ P := fun h => hle (le_trans Ideal.mul_le_left h)
    have haP : ¬ 𝔞 ≤ P := fun h => hle (le_trans Ideal.mul_le_right h)
    have hne : P ≠ Q := fun h => hQP (h ▸ le_rfl)
    rw [residueSymbol_mul_ideal _ _ hQe.1 hae.1, ih hae haP,
      residueSymbol_gen_mul hχ g hPe hQe hae, residueSymbol_prime hQp hQe.1,
      residueSymbol_prime hP hPe.1, residueSymbol_prime hP hPe.1,
      ← g.reciprocity P Q hP hQp hPe hQe hne]

/-! ### `ϑ` and norms -/

/-! ### (3.10) -/

/-! ### Cross-prime multiplicativity of the Poisson factor -/

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Main: CutMul from `HypAdd` and `HypChi`

`b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀}, P^l, P^k, P^m) b(𝔠, 𝔫, 𝔰, 𝔯)`: `ϑ` is completely
multiplicative; `γ₂` and `F` split by (3.10) and `poissonFactor_mul`; with `a = χ_P(gen 𝔠)`,
`w = χ_P(gen 𝔠𝔫³) = a b³`, `σ = χ_P(gen 𝔰)`, `t = e₀ + 3l` the cross factors are
`a^{4e₀}` and `w^{2t}`, whose product is `1`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- `HypChi` for all moduli divisible by the small primes. -/
def HypChiAll (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → HypChi ι 𝔪

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Char: `χ_P` as a multiplicative character and `x ↦ e(x/π)` as a primitive additive
character of the residue field `L = R / P R`

Standing hypotheses `Good 𝔪 v`: `v` coprime to `𝔪`, `12 ∣ N v − 1`, `v ∤ 𝔇`; and a primitive
sixth root of unity `ω ∈ 𝓞`.

* `chi`: `MulChar L ℂ` with `chi (mk x) = sexticResidueSymbol ι 𝔪 v x`; `chi_neg_one`,
  `chi_pow_six`, `chi_pow_ne_one` (`6 ∤ j`), `chi_cube_eq` (`χ³` is the quadratic character).
* `psi`: `AddChar L ℂ` with `psi (mk x) = e(x / gen P)`; `psi_isPrimitive`.
* `cubicResidueChar_eq`: `ρ_P(x) = χ(x)²` through `𝓞/P ≃ L`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- The standing hypotheses at the prime `v`. -/
structure Good (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) : Prop where
  cop : v.asIdeal ⊔ 𝔪 = ⊤
  twelve : 12 ∣ Ideal.absNorm v.asIdeal - 1
  diff : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal

variable {v : HeightOneSpectrum (𝓞 F)}

lemma Good.notS (h : Good 𝔪 v) : v ∉ placesOf 𝔪 := fun hv =>
  v.isPrime.ne_top (eq_top_iff.2 (h.cop ▸ sup_le le_rfl hv))

lemma absNorm_ne_one (v : HeightOneSpectrum (𝓞 F)) : Ideal.absNorm v.asIdeal ≠ 1 := by
  rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top

lemma absNorm_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Ideal.absNorm v.asIdeal := by
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

lemma Good.coprime_six (h : Good 𝔪 v) : (Ideal.absNorm v.asIdeal).Coprime 6 := by
  have h1 := absNorm_pos v
  obtain ⟨k, hk⟩ := h.twelve
  have : Ideal.absNorm v.asIdeal = 12 * k + 1 := by omega
  rw [this, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, show (12 * k + 1) % 6 = 1 by omega,
    Nat.gcd_one_left]

lemma isMaximal_v (h : Good 𝔪 v) : (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal :=
  isMaximal_map h.notS

lemma finite_L (h : Good 𝔪 v) : Finite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have := finite_quot (𝔪 := 𝔪) h.notS 1
  rwa [pow_one] at this

lemma natCard_L (h : Good 𝔪 v) :
    Nat.card (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = Ideal.absNorm v.asIdeal := by
  have := natCard_quot (𝔪 := 𝔪) h.notS 1
  rwa [pow_one, pow_one] at this

lemma quotHom_bijective_one (h : v ∉ placesOf 𝔪) :
    Function.Bijective (quotHom 𝔪 v.asIdeal) := by
  have := quotHom_bijective (𝔪 := 𝔪) h 1
  rwa [pow_one] at this

/-! ### The sixth roots of unity -/

section roots

variable (ι : F →+* ℂ)

/-- Choice-free value of a root of unity: if `f ζ = f ω ^ i` then `ι ζ = ι ω ^ i`. -/
lemma iota_eq_pow_of_map {K : Type*} [CommRing K] [IsDomain K] (f : 𝓞 F →+* K) {m : ℕ}
    (hm : 0 < m) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω m) (hωf : IsPrimitiveRoot (f ω) m)
    {ζ : 𝓞 F} (hζ : ζ ^ m = 1) {i : ℕ} (h : f ζ = f ω ^ i) : ι (ζ : F) = ι (ω : F) ^ i := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨j, hj, rfl⟩ := hω.eq_pow_of_pow_eq_one hζ
  have hpow : ∀ (z : K) (hz : z ^ m = 1) (n : ℕ), z ^ n = z ^ (n % m) := by
    intro z hz n
    conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hz, one_pow, one_mul]
  have hpowC : ∀ (z : ℂ) (hz : z ^ m = 1) (n : ℕ), z ^ n = z ^ (n % m) := by
    intro z hz n
    conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hz, one_pow, one_mul]
  have h1 : f ω ^ j = f ω ^ (i % m) := by
    rw [← map_pow, h, hpow _ hωf.pow_eq_one]
  have hji : j = i % m := hωf.pow_inj hj (Nat.mod_lt _ hm) h1
  have hιω : ι (ω : F) ^ m = 1 := by
    rw [← map_pow, ← map_pow (algebraMap (𝓞 F) F), hω.pow_eq_one, map_one, map_one]
  rw [show ((ω ^ j : 𝓞 F) : F) = (ω : F) ^ j from map_pow (algebraMap (𝓞 F) F) ω j, map_pow, hji,
    ← hpowC _ hιω]

end roots

section chi

/-- The function underlying `sexticResidueSymbol` on `L = R / P R`. -/
noncomputable def sexFun (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℂ := by
  classical
  exact if y = 0 then 0 else
    if h : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
        Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
          (algebraMap (𝓞 F) (SInt 𝔪) ζ) = y ^ ((Ideal.absNorm v.asIdeal - 1) / 6)
    then ι (h.choose : F) else 0

lemma sexticResidueSymbol_eq (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F))
    (x : SInt 𝔪) :
    sexticResidueSymbol ι 𝔪 v.asIdeal x =
      sexFun ι 𝔪 v (Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) x) := by
  unfold sexticResidueSymbol sexFun
  congr 1

variable {ι : F →+* ℂ}

/-- The image of `ω` in `L`. -/
noncomputable abbrev omegaL (ω : 𝓞 F) : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) ω)

lemma omegaL_prim (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    IsPrimitiveRoot (omegaL (𝔪 := 𝔪) (v := v) ω) 6 := by
  have h1 : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal ω) 6 :=
    hω.idealQuotient_mk (absNorm_ne_one v) h.coprime_six
  have h2 := h1.map_of_injective (quotHom_bijective_one (𝔪 := 𝔪) h.notS).1
  exact h2

lemma pow_card_sub_one_L (h : Good 𝔪 v)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    y ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  haveI := finite_L h
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  rw [← natCard_L h, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one y hy

lemma six_mul_e (h : Good 𝔪 v) :
    6 * ((Ideal.absNorm v.asIdeal - 1) / 6) = Ideal.absNorm v.asIdeal - 1 :=
  Nat.mul_div_cancel' ((Nat.dvd_trans (by norm_num) h.twelve))

/-- Every nonzero `y ∈ L` has `y^e` a power of `ω`. -/
lemma exists_pow_e (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    ∃ i : ℕ, i < 6 ∧ y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have h6 : (y ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, six_mul_e h, pow_card_sub_one_L h hy]
  obtain ⟨i, hi, hi'⟩ := (omegaL_prim h hω).eq_pow_of_pow_eq_one h6
  exact ⟨i, hi, hi'.symm⟩

lemma sexFun_eq_pow (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) {i : ℕ}
    (hi : y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i) :
    sexFun ι 𝔪 v y = ι (ω : F) ^ i := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hex : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
      Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
        (algebraMap (𝓞 F) (SInt 𝔪) ζ) = y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) :=
    ⟨ω ^ i, by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], by
      rw [map_pow, map_pow, hi]⟩
  classical
  unfold sexFun
  rw [if_neg hy, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set f : 𝓞 F →+* SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    (Ideal.Quotient.mk _).comp (algebraMap (𝓞 F) (SInt 𝔪))
  exact iota_eq_pow_of_map ι f (by norm_num) hω (omegaL_prim h hω) h1 (by
    change Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) hex.choose) = omegaL ω ^ i
    rw [h2, hi])

lemma sexFun_zero : sexFun ι 𝔪 v (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = 0 := by
  classical
  unfold sexFun; rw [if_pos rfl]

lemma iota_omega_prim {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) : IsPrimitiveRoot (ι (ω : F)) 6 :=
  (hω.map_of_injective RingOfIntegers.coe_injective).map_of_injective ι.injective

/-- `χ_P` as a multiplicative character of `L`. -/
noncomputable def chi (ι : F →+* ℂ) (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    MulChar (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ℂ where
  toFun := sexFun ι 𝔪 v
  map_one' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    rw [sexFun_eq_pow h hω one_ne_zero (i := 0) (by rw [one_pow, pow_zero])]
    simp
  map_mul' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    intro x y
    by_cases hx : x = 0
    · simp [hx, sexFun_zero]
    by_cases hy : y = 0
    · simp [hy, sexFun_zero]
    obtain ⟨i, -, hi⟩ := exists_pow_e h hω hx
    obtain ⟨j, -, hj⟩ := exists_pow_e h hω hy
    rw [sexFun_eq_pow h hω hx hi, sexFun_eq_pow h hω hy hj,
      sexFun_eq_pow h hω (mul_ne_zero hx hy) (i := i + j) (by rw [mul_pow, hi, hj, pow_add]),
      pow_add]
  map_nonunit' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    intro a ha
    have : a = 0 := by
      by_contra h'
      exact ha (Ne.isUnit h')
    rw [this]; exact sexFun_zero

lemma chi_mk (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (x : SInt 𝔪) :
    chi ι h hω (Ideal.Quotient.mk _ x) = sexticResidueSymbol ι 𝔪 v.asIdeal x :=
  (sexticResidueSymbol_eq ι 𝔪 v x).symm

lemma chi_eq_pow (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) {i : ℕ}
    (hi : y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i) :
    chi ι h hω y = ι (ω : F) ^ i :=
  sexFun_eq_pow h hω hy hi

lemma chi_pow_six_apply (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    chi ι h hω y ^ 6 = 1 := by
  obtain ⟨i, -, hi⟩ := exists_pow_e h hω hy
  rw [chi_eq_pow h hω hy hi, ← pow_mul, mul_comm, pow_mul, (iota_omega_prim hω).pow_eq_one,
    one_pow]

end chi

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Chk: `HypChi` from section A's `χ_P` (`C3I_Char`), and CutMul

Exterior primes are `C3I.Good` once `N₀ ≥ max(3^[F:ℚ], N 𝔇)`: `12 ∣ N P − 1` because `μ₁₂ ⊂ F`
and `P ∤ 6`, and `P ∤ 𝔇` because `N P > N 𝔇`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- In `ℚ(μ_n)` with `12 ∣ n`, a prime of norm `> 3^[F:ℚ]` has `12 ∣ N P − 1`. -/
theorem twelve_dvd_absNorm_sub_one (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    [IsCyclotomicExtension {n} ℚ F]
    (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) : 12 ∣ Ideal.absNorm P - 1 := by
  have : P.IsMaximal := hP.isMaximal hP0
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  set Q := Ideal.absNorm P
  have hd : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h23 : 2 ^ Module.finrank ℤ (𝓞 F) ≤ 3 ^ Module.finrank ℤ (𝓞 F) :=
    Nat.pow_le_pow_left (by norm_num) _
  have h3le : 3 ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hd
  have h2 : ¬ 2 ∣ Q := fun h => by
    have := C3B.absNorm_le_of_prime_dvd 2 Nat.prime_two P hP0 h; omega
  have h3 : ¬ 3 ∣ Q := fun h => by
    have := C3B.absNorm_le_of_prime_dvd 3 Nat.prime_three P hP0 h; omega
  have hcop : Q.Coprime 12 := by
    have c2 : Q.Coprime 2 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
    have c3 : Q.Coprime 3 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
    have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [this]; exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 c2) c3
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ12 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 12)) 12 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn).symm
  have hω : IsPrimitiveRoot hζ12.toInteger 12 := hζ12.toInteger_isPrimitiveRoot
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P hζ12.toInteger) 12 :=
    hω.idealQuotient_mk (by omega) hcop
  have h1 : Ideal.Quotient.mk P hζ12.toInteger ^ (Q - 1) = 1 := by
    rw [show Q = Fintype.card (𝓞 F ⧸ P) from (C3B.card_quot P hP0).symm]
    exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
  exact (hωb.pow_eq_one_iff_dvd _).mp h1

/-- `HypChi` holds for every modulus divisible by the primes of norm `≤ max(3^[F:ℚ], N 𝔇)`. -/
theorem hypChiAll (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : HypChiAll F ι := by
  refine ⟨max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F))),
    fun 𝔪 _ hS P hP hPe => ?_⟩
  have h𝔪 : ¬ 𝔪 ≤ P := by
    intro h
    apply hP.ne_top
    rw [eq_top_iff, ← hPe.2]
    exact sup_le le_rfl h
  have hgt : max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F))) <
      Ideal.absNorm P := by
    by_contra hc
    exact h𝔪 (hS P hP hPe.1 (not_lt.mp hc))
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hPe.1⟩
  have hdiff : ¬ differentIdeal ℤ (𝓞 F) ≤ P := by
    intro hle
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    have hD0 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact differentIdeal_ne_bot
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) hdvd
    have := le_max_right (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F)))
    omega
  have hgood : C3I.Good 𝔪 v :=
    ⟨hPe.2, twelve_dvd_absNorm_sub_one n hn0 hn P hP hPe.1 (lt_of_le_of_lt (le_max_left _ _) hgt),
      hdiff⟩
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel (Nat.dvd_trans (by norm_num) hn)).symm
  have hω : IsPrimitiveRoot hζ6.toInteger 6 := hζ6.toInteger_isPrimitiveRoot
  have e : ∀ z : SInt 𝔪, C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) z) =
      sexticResidueSymbol ι 𝔪 P z := fun z => C3I.chi_mk hgood hω z
  refine ⟨fun x y => ?_, fun x hx => ?_⟩
  · have h : C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x *
        Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) =
        C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x) *
          C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) :=
      map_mul _ _ _
    rw [← map_mul, e, e, e] at h
    exact h
  · have hne : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have h := C3I.chi_pow_six_apply (ι := ι) hgood hω hne
    rwa [e] at h

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3E_Arith: the off-diagonal coefficient `χ_𝔡(g𝔠₁)³ conj χ_𝔡(g𝔠₂)³`

For exterior squarefree `𝔠₁ ≠ 𝔠₂`, with `𝔞 = 𝔠₁ ⊔ 𝔠₂`, `𝔠ᵢ = 𝔞 𝔟ᵢ`, `𝔲 = (𝔟₁𝔟₂)³` and
`T` the primes of `𝔞`: the frequency class `r = (𝔲, 1)` is not principal, `N 𝔲 ≤ (N𝔠₁ N𝔠₂)³`,
`2^{|T|} ≤ N𝔠₁`, and for every exterior `𝔡`
`χ_𝔡(g𝔠₁)³ conj χ_𝔡(g𝔠₂)³ = 1[𝔡 ⊄ P ∀ P ∈ T] χ_𝔡(freqElt g r)`. -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

namespace L3E

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma conj_eq_of {z : ℂ} (h : z = 0 ∨ z ^ 2 = 1) : starRingEnd ℂ z = z := by
  rcases h with h | h
  · rw [h, map_zero]
  · have : (z - 1) * (z + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · rw [show z = 1 by linear_combination h1, map_one]
    · rw [show z = -1 by linear_combination h1, map_neg, map_one]

lemma sextic_eq_zero_of_mem {P : Ideal (𝓞 F)} {x : SInt 𝔪}
    (hx : x ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪))) : sexticResidueSymbol ι 𝔪 P x = 0 := by
  unfold sexticResidueSymbol
  rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.2 hx)]

lemma conj_rs_cube (hχ : C3M.HypChi ι 𝔪) {𝔡 : Ideal (𝓞 F)} (h𝔡 : IsExterior 𝔪 𝔡) (x : SInt 𝔪) :
    starRingEnd ℂ (residueSymbol ι 𝔪 𝔡 x ^ 3) = residueSymbol ι 𝔪 𝔡 x ^ 3 := by
  unfold residueSymbol
  rw [← Multiset.prod_map_pow, map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun Q hQ => ?_
  obtain ⟨hQp, hQe⟩ := C3M.exterior_of_mem_factors h𝔡 hQ
  refine conj_eq_of ?_
  by_cases hx : x ∈ Q.map (algebraMap (𝓞 F) (SInt 𝔪))
  · left; simp [sextic_eq_zero_of_mem (ι := ι) hx]
  · right
    have := (hχ Q hQp hQe).2 x hx
    rw [← pow_mul]; simpa using this

lemma mem_normalizedFactors_of_le {I P : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hle : I ≤ P) : P ∈ normalizedFactors I := by
  have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
  obtain ⟨q, hq, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hI hpr.irreducible
    (Ideal.dvd_iff_le.2 hle)
  rwa [associated_iff_eq.1 hassoc]

lemma rs_eq_zero_of_le {𝔡 P : Ideal (𝓞 F)} (h𝔡 : 𝔡 ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hle : 𝔡 ≤ P) {x : SInt 𝔪} (hx : x ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    residueSymbol ι 𝔪 𝔡 x = 0 := by
  unfold residueSymbol
  refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨P, ?_, sextic_eq_zero_of_mem hx⟩)
  exact mem_normalizedFactors_of_le h𝔡 hP hP0 hle

end L3E

end ArtinPrimitiveRoots

end
end

section
section
/-!
# C0-P: the `S`-integers form a PID once `S` contains the small primes

Every ideal class contains a nonzero ideal of bounded norm; once `𝔪` is divisible by every prime of
norm at most that bound, every ideal of `R = 𝓞_S` is principal.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace C0R

variable {F : Type*} [Field F] [NumberField F]

/-- `𝔪 R = R` for `𝔪 ≠ 0`: a power `𝔪^h = (a)` is principal, and `a⁻¹ ∈ R`. -/
theorem map_self_eq_top (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) :
    𝔪.map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ := by
  classical
  have h𝔪' : 𝔪 ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔪
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hpow : 𝔪 ^ h ∈ (Ideal (𝓞 F))⁰ := pow_mem h𝔪' h
  have hprin : (𝔪 ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hpow]
    have : (⟨𝔪 ^ h, hpow⟩ : (Ideal (𝓞 F))⁰) = (⟨𝔪, h𝔪'⟩ : (Ideal (𝓞 F))⁰) ^ h := rfl
    rw [this, map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := hprin.principal
  rw [Ideal.submodule_span_eq] at ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at ha
    exact (pow_ne_zero h h𝔪) ha
  have hamem : a ∈ 𝔪 := by
    have : a ∈ 𝔪 ^ h := by rw [ha]; exact Ideal.mem_span_singleton_self a
    exact Ideal.pow_le_self hpos.ne' this
  -- `a⁻¹` is an `S`-integer
  have hinv : ((a : F))⁻¹ ∈ (placesOf 𝔪).integer F := by
    intro v hv
    have hav : a ∉ v.asIdeal := by
      intro hav
      apply hv
      change 𝔪 ≤ v.asIdeal
      have : 𝔪 ^ h ≤ v.asIdeal := by
        rw [ha, Ideal.span_le, Set.singleton_subset_iff]; exact hav
      exact v.isPrime.le_of_pow_le this
    rw [map_inv₀]
    have : v.valuation F (a : F) = 1 := by
      rw [show (a : F) = algebraMap (𝓞 F) F a from rfl, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_eq_one_iff]
      exact hav
    rw [this, inv_one]
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : SInt 𝔪) = algebraMap (𝓞 F) (SInt 𝔪) a * ⟨_, hinv⟩ := by
    apply Subtype.ext
    change (1 : F) = (a : F) * (a : F)⁻¹
    rw [mul_inv_cancel₀]
    exact_mod_cast ha0
  rw [h1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hamem)

/-- An ideal all of whose prime divisors contain `𝔪` becomes the unit ideal in `R`. -/
theorem map_eq_top_of_primes (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (J : Ideal (𝓞 F))
    (hprimes : ∀ Q : Ideal (𝓞 F), Q.IsPrime → J ≤ Q → 𝔪 ≤ Q) :
    J.map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ hne
  have hQ : (M.comap (algebraMap (𝓞 F) (SInt 𝔪))).IsPrime := Ideal.comap_isPrime _ M
  have hJQ : J ≤ M.comap (algebraMap (𝓞 F) (SInt 𝔪)) := Ideal.map_le_iff_le_comap.1 hJM
  have h𝔪Q := hprimes _ hQ hJQ
  have : 𝔪.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ M :=
    Ideal.map_le_iff_le_comap.2 h𝔪Q
  rw [map_self_eq_top 𝔪 h𝔪, top_le_iff] at this
  exact hM.ne_top this

end C0R

end ArtinPrimitiveRoots

end
end

section
section
/-!
# L3Q_Chi: the quadratic family `χ_c(a) = residueSymbol a (gen c)³`

* `rs_nonext`: the symbol vanishes at non-exterior ideals;
* `chiK_sq`: `χ_c(r)² = [r ⊔ c = ⊤]` for exterior `r, c`;
* `chiK_symm`: exact reciprocity `χ_b(a) = χ_a(b)` for exterior `a, b`;
* `psiHyp_pair`: `a ↦ χ_{c₁}(a) χ_{c₂}(a)` satisfies `PsiHyp 𝔪 (c₁ c₂)`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

set_option linter.unusedSectionVars false

lemma map_eq_top_of_le (h𝔪 : 𝔪 ≠ ⊥) {P : Ideal (𝓞 F)} (hle : 𝔪 ≤ P) :
    P.map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ :=
  C0R.map_eq_top_of_primes 𝔪 h𝔪 P fun _ _ hPQ => le_trans hle hPQ

lemma rs_nonext (h𝔪 : 𝔪 ≠ ⊥) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hI𝔪 : I ⊔ 𝔪 ≠ ⊤) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 I x = 0 := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hI𝔪
  have hM0 : M ≠ ⊥ := by
    intro h; rw [h] at hle; exact h𝔪 (le_bot_iff.1 (le_trans le_sup_right hle))
  refine L3E.rs_eq_zero_of_le hI hM.isPrime hM0 (le_trans le_sup_left hle) ?_
  rw [map_eq_top_of_le h𝔪 (le_trans le_sup_right hle)]; trivial

lemma norm_sext_le (P : Ideal (𝓞 F)) (x : SInt 𝔪) : ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h1 h2
  · simp
  · have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
      rw [← map_pow, ← map_pow, h2.choose_spec.1]; simp
    rw [Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)]
  · simp

lemma norm_rs_le (I : Ideal (𝓞 F)) (x : SInt 𝔪) : ‖residueSymbol ι 𝔪 I x‖ ≤ 1 := by
  unfold residueSymbol
  induction normalizedFactors I using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (norm_sext_le P x) (norm_nonneg _) ih

lemma gen_mem_map {g : AllowedGen ι 𝔪} {c P : Ideal (𝓞 F)} (hc : IsExterior 𝔪 c) (hcP : c ≤ P) :
    g.gen c ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  have h : g.gen c ∈ Ideal.span {g.gen c} := Ideal.subset_span rfl
  rw [g.span_gen c hc] at h
  exact Ideal.map_mono hcP h

lemma rs_gen_pow_six (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {r c : Ideal (𝓞 F)}
    (hr : IsExterior 𝔪 r) (hc : IsExterior 𝔪 c) :
    residueSymbol ι 𝔪 r (g.gen c) ^ 6 = if r ⊔ c = ⊤ then 1 else 0 := by
  by_cases hrc : r ⊔ c = ⊤
  · rw [if_pos hrc]
    refine C3M.residueSymbol_pow_six hχ hr ?_
    rw [g.span_gen c hc]
    exact C3M.isCoprime_map (Ideal.isCoprime_iff_sup_eq.2 (by rwa [sup_comm]))
  · rw [if_neg hrc]
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hrc
    have hM0 : M ≠ ⊥ := by
      intro h; rw [h] at hle; exact hr.1 (le_bot_iff.1 (le_trans le_sup_left hle))
    rw [L3E.rs_eq_zero_of_le hr.1 hM.isPrime hM0 (le_trans le_sup_left hle)
      (gen_mem_map hc (le_trans le_sup_right hle))]
    norm_num

lemma chiK_sq (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {r c : Ideal (𝓞 F)}
    (hr : IsExterior 𝔪 r) (hc : IsExterior 𝔪 c) :
    L3H.chiK ι 𝔪 g r c ^ 2 = if r ⊔ c = ⊤ then 1 else 0 := by
  unfold L3H.chiK
  rw [← pow_mul]
  exact rs_gen_pow_six hχ g hr hc

lemma chiK_conj (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {r : Ideal (𝓞 F)}
    (hr : IsExterior 𝔪 r) (c : Ideal (𝓞 F)) :
    starRingEnd ℂ (L3H.chiK ι 𝔪 g r c) = L3H.chiK ι 𝔪 g r c :=
  L3E.conj_rs_cube hχ hr _

lemma chiK_mul_bot (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (c : Ideal (𝓞 F)) :
    L3H.chiK ι 𝔪 g (I * J) c = L3H.chiK ι 𝔪 g I c * L3H.chiK ι 𝔪 g J c := by
  unfold L3H.chiK
  rw [L3H.rs_mul I J hI hJ, mul_pow]

lemma rs_top (x : SInt 𝔪) : residueSymbol ι 𝔪 ⊤ x = 1 := by
  simp [residueSymbol, ← Ideal.one_eq_top]

/-- Exact reciprocity for coprime exterior ideals. -/
lemma rs_gen_symm_cop (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {b : Ideal (𝓞 F)}
    (hb : IsExterior 𝔪 b) (a : Ideal (𝓞 F)) :
    IsExterior 𝔪 a → a ⊔ b = ⊤ →
      residueSymbol ι 𝔪 a (g.gen b) = residueSymbol ι 𝔪 b (g.gen a) := by
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h.1
  | h₂ u hu =>
    intro _ _
    have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
    subst hu'
    rw [rs_top, C3M.residueSymbol_gen_top hχ g hb]
  | h₃ a Q _ hQ ih =>
    intro hQa hcop
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
    have hQe : IsExterior 𝔪 Q := C3M.isExterior_of_mul_left hQa
    have hae : IsExterior 𝔪 a := C3M.isExterior_of_mul_right hQa
    have hcop' : Q ⊔ b = ⊤ ∧ a ⊔ b = ⊤ := sup_mul_eq_top_iff.1 hcop
    have hbQ : ¬ b ≤ Q := fun h => hQp.ne_top (top_le_iff.1 (hcop'.1 ▸ sup_le le_rfl h))
    rw [C3M.residueSymbol_mul_ideal _ _ hQe.1 hae.1, ih hae hcop'.2,
      C3M.residueSymbol_gen_mul hχ g hb hQe hae,
      C3M.residueSymbol_gen_prime hχ g hQp hQe b hb hbQ]

/-- Exact reciprocity `χ_b(a) = χ_a(b)` for exterior `a, b`. -/
lemma chiK_symm (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {a b : Ideal (𝓞 F)}
    (ha : IsExterior 𝔪 a) (hb : IsExterior 𝔪 b) :
    L3H.chiK ι 𝔪 g a b = L3H.chiK ι 𝔪 g b a := by
  unfold L3H.chiK
  by_cases hab : a ⊔ b = ⊤
  · rw [rs_gen_symm_cop hχ g hb a ha hab]
  · obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hab
    have hM0 : M ≠ ⊥ := by
      intro h; rw [h] at hle; exact ha.1 (le_bot_iff.1 (le_trans le_sup_left hle))
    rw [L3E.rs_eq_zero_of_le ha.1 hM.isPrime hM0 (le_trans le_sup_left hle)
        (gen_mem_map hb (le_trans le_sup_right hle)),
      L3E.rs_eq_zero_of_le hb.1 hM.isPrime hM0 (le_trans le_sup_right hle)
        (gen_mem_map ha (le_trans le_sup_left hle))]

/-- The pair character `ψ = χ_{c₁} χ_{c₂}` satisfies `PsiHyp`. -/
theorem psiHyp_pair (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪) (h𝔪 : 𝔪 ≠ ⊥)
    {c₁ c₂ : Ideal (𝓞 F)} (hc₁ : IsExterior 𝔪 c₁) (hc₂ : IsExterior 𝔪 c₂) :
    PsiHyp 𝔪 (c₁ * c₂) (fun a => L3H.chiK ι 𝔪 g a c₁ * L3H.chiK ι 𝔪 g a c₂) where
  mul I J hI hJ := by
    show L3H.chiK ι 𝔪 g (I * J) c₁ * L3H.chiK ι 𝔪 g (I * J) c₂ = _
    rw [chiK_mul_bot g hI hJ, chiK_mul_bot g hI hJ]; ring
  norm_le I := by
    simp only [L3H.chiK, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_rs_le _ _)) (by positivity)
      (pow_le_one₀ (norm_nonneg _) (norm_rs_le _ _))
  nonext I hI hI𝔪 := by
    simp only [L3H.chiK, rs_nonext h𝔪 hI hI𝔪]; ring
  sq r hr hr𝔪 := by
    show (L3H.chiK ι 𝔪 g r c₁ * L3H.chiK ι 𝔪 g r c₂) ^ 2 = _
    have hre : IsExterior 𝔪 r := ⟨hr, hr𝔪⟩
    rw [mul_pow, chiK_sq hχ g hre hc₁, chiK_sq hχ g hre hc₂]
    have e : r ⊔ c₁ * c₂ = ⊤ ↔ r ⊔ c₁ = ⊤ ∧ r ⊔ c₂ = ⊤ := by
      rw [sup_comm, sup_mul_eq_top_iff, sup_comm c₁, sup_comm c₂]
    by_cases h1 : r ⊔ c₁ = ⊤ <;> by_cases h2 : r ⊔ c₂ = ⊤ <;> simp [h1, h2, e]
  top := by simp [L3H.chiK, rs_top]

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Pair: the explicit formula for one pair `(c₁, c₂)`

`O = ∑'_{a ⊔ 𝔤 = ⊤, s(a) > L} W(Na/M) ψ(a) = (T − T′) + DP + DQ − RP`, from `Aall_eq`, `Ale_eq`, `TT_eq`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory UniqueFactorizationMonoid
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Bil: the bilinear bound for coprime pairs

For a kernel `χ` (rows × columns), rows `R`, columns `C`, a Möbius system for coprimality on `C`,
and an `SBf` bound `β` for `χ` on `R × C`:
`‖∑_{c₁,c₂ ∈ C, cop} u(c₁) v(c₂) ∑_{s ∈ R} a(s) χ(s,c₁) χ(s,c₂)‖ ≤ A β √U √V`,
`U = ∑_h ∑_{c, h | c} ‖u c‖²`, `A ≥ ‖a‖`.
-/

namespace ArtinPrimitiveRoots.L3Q


open Finset

variable {I : Type*} [DecidableEq I]

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # L3H_S3: the weighted forms `Q` (GL's `Σ₂`, `B₂`) and `S3` (GL's `Σ₃`)

Rows `a ∈ Rw` with weights `w a ≥ 0`, kernel `χ a c`, columns a `Finset`.
* `Qf Cs μ = ∑_a w a ‖∑_{c ∈ Cs} μ c χ a c‖²`; `B2f Cs v`: `Qf Cs μ ≤ v ∑ ‖μ c‖²` for all `μ`.
* `S3 Cs 𝔤 λ = ∑_{b₁, b₂ ∈ Cs, b₁ ⊔ b₂ = 𝔤} λ b₁ conj(λ b₂) ∑_a w a χ a b₁ conj(χ a b₂)`.
* `Qf_eq_sum_S3`: `Qf = ∑_𝔤 S3` (sorting the pairs by their gcd).
* `Qf_le_classes`: Cauchy–Schwarz over `k` classes.
* `norm_S3_le_tail`: GL Lemma 5.1's Möbius step: for `𝔤 ≠ ⊥`, `‖S3 Cs 𝔤 λ‖` is at most
  `v' ∑_{d} ∑_{c, d ∣ c} ‖λ(𝔤 c)‖²` from the bound `v'` on columns `c` with `𝔤 c ∈ Cs`.
-/

open NumberField

namespace L3H

section abstract

variable {I : Type*} (χ : I → I → ℂ) (Rw : Finset I) (w : I → ℝ)

/-- GL's `Σ₃`. -/
noncomputable def S3 [DecidableEq I] (gcd : I → I → I) (Cs : Finset I) (𝔤 : I) (μ : I → ℂ) : ℂ :=
  ∑ b₁ ∈ Cs, ∑ b₂ ∈ Cs, if gcd b₁ b₂ = 𝔤 then
    μ b₁ * starRingEnd ℂ (μ b₂) * ∑ a ∈ Rw, (w a : ℂ) * χ a b₁ * starRingEnd ℂ (χ a b₂) else 0

variable {χ Rw w}

end abstract

end L3H

end
end

section
section
/-! # L3H_Tail: the Möbius step of GL Lemma 5.1

For `𝔤 ≠ ⊥`: pairs `b₁, b₂` with `b₁ ⊔ b₂ = 𝔤` are `b_i = 𝔤 c_i` with `c₁ ⊔ c₂ = ⊤`; detecting
`c₁ ⊔ c₂ = ⊤` by `∑_{d ∣ c₁, d ∣ c₂} μ(d)` turns `S3` into `∑_d μ(d) Q(c ≡ 0 mod d)`. -/

open NumberField UniqueFactorizationMonoid

namespace L3H

variable {F : Type*} [Field F] [NumberField F]


open Classical in
lemma reindex {M : Type*} [AddCommMonoid M] {𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) (Cs C'' : Finset (Ideal (𝓞 F)))
    (hC'' : ∀ b ∈ Cs, ∀ c, b = 𝔤 * c → c ∈ C'') (f : Ideal (𝓞 F) → M)
    (hf : ∀ b ∈ Cs, ¬ 𝔤 ∣ b → f b = 0) :
    ∑ b ∈ Cs, f b = ∑ c ∈ C'', if 𝔤 * c ∈ Cs then f (𝔤 * c) else 0 := by
  have h𝔤0 : 𝔤 ≠ 0 := h𝔤
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun c => 𝔤 * c) (C''.filter (fun c => 𝔤 * c ∈ Cs) : Set (Ideal (𝓞 F))) :=
    fun x _ y _ hxy => mul_left_cancel₀ h𝔤0 hxy
  rw [← Finset.sum_image (f := f) hinj]
  have himg : (C''.filter (fun c => 𝔤 * c ∈ Cs)).image (fun c => 𝔤 * c) =
      Cs.filter (fun b => 𝔤 ∣ b) := by
    ext b
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨c, ⟨_, hc⟩, rfl⟩; exact ⟨hc, dvd_mul_right _ _⟩
    · rintro ⟨hb, c, rfl⟩; exact ⟨c, ⟨hC'' _ hb c rfl, hb⟩, rfl⟩
  rw [himg, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b hb => ?_
  split_ifs with h
  · rfl
  · exact hf b hb h

lemma mul_sup_eq_iff {𝔤 c₁ c₂ : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) : 𝔤 * c₁ ⊔ 𝔤 * c₂ = 𝔤 ↔ c₁ ⊔ c₂ = ⊤ := by
  rw [← Ideal.mul_sup]
  constructor
  · intro h
    have h' : 𝔤 * (c₁ ⊔ c₂) = 𝔤 * ⊤ := by rw [h, Ideal.mul_top]
    exact mul_left_cancel₀ (show 𝔤 ≠ 0 from h𝔤) h'
  · intro h; rw [h, Ideal.mul_top]

variable {χ : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ} {Rw : Finset (Ideal (𝓞 F))} {w : Ideal (𝓞 F) → ℝ}

end L3H

end
end

section
section
/-!
# L3Q_Mob: the Möbius system on squarefree exterior columns, and the bilinear bound for pairs

`bil_np`: for columns `C ⊆ rows(≤ Cmax)` and an `SBf` bound `β`,
`‖∑_{c₁ ⊔ c₂ = ⊤, (c₁,c₂) ≠ (1,1)} u(c₁) v(c₂) ∑_s a(s) χ(s,c₁)χ(s,c₂)‖ ≤ 2 A β √(∑ 2^ω |u|²) √(∑ 2^ω |v|²)`.
-/

namespace ArtinPrimitiveRoots.L3Q


open NumberField Finset

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Piece: finite sums of line integrals against `Wm`
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open MeasureTheory Complex Filter
open scoped Real

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_PRP: the error term `RP` summed over pairs

`‖∑_{pairs} z(c₁) conj z(c₂) RP(c₁c₂)‖ ≤ (2π)⁻¹ IW · M^ε 2^{ω(𝔤𝔪)} C_R 2^{A_R}/(1 − 2ε) · 2β · Zτ`,
with `β` an `SBf` bound on rows `≤ L` and `Zτ = ∑ 8^{ω(c)} |z(c)|²`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Finset
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma primesOf_eq_pf (c : Ideal (𝓞 F)) : primesOf c = L3H.pf c := by
  ext P; simp [primesOf, L3H.pf]

lemma Ztau_def (C : Finset (Ideal (𝓞 F))) (z : Ideal (𝓞 F) → ℂ) :
    Ztau C z = ∑ c ∈ C, (8 : ℝ) ^ (L3H.pf c).card * ‖z c‖ ^ 2 := by
  unfold Ztau; simp only [primesOf_eq_pf]

lemma psiP_apply {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (c₁ c₂ a : Ideal (𝓞 F)) :
    psiP g c₁ c₂ a = L3H.chiK ι 𝔪 g a c₁ * L3H.chiK ι 𝔪 g a c₂ := rfl

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # L3H_Aux: shared helpers (dyadic covers, `log₂` bounds, trivial bounds, `rpow` facts) -/

open NumberField ArtinPrimitiveRoots Real

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

end L3H

end
end

section
section
/-! # L3H_L51: GL Lemma 5.1 for the family `chiK`

Columns `N < N b ≤ 2N` (`rowsF 𝔪 N (2N)`), `k` classes. From GL Prop 5.2 at the gcds `𝔤` with
`N 𝔤 ≤ G₀` (bound `A N𝔤⁴`) and the bound `v'` for every column scale `N' ≤ N / G₀`:
`B₂ ≤ k (A G₀⁴ #{N 𝔤 ≤ G₀} + v' T²)`, with `T` a bound for the number of divisors. -/

open NumberField ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

end L3H

end
end

section
section
/-! # L3H_Iter: the iteration (5.3)–(5.4) in the proof of GL Theorem 4.3

`V 0 = v₀`, `V (i+1) = k (A G₀⁴ Cnt + V i T²) + v₀`; column scales `N' < G₀^i` are bounded by
`V i`, by GL Lemma 5.1 (`lemma51`) at each step, and `V i ≤ (k T² + 1)^i (i+1) (k A G₀⁴ Cnt + v₀)`. -/

open NumberField ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

end L3H

end
end

section
section
/-! # L3H_Rows: the rows of `Σ₂, Σ₃`, ideal counting, and the passage `B₁ ≤ B₂`

* `RwF 𝔪 L M`: exterior `𝔞` with squarefree part of norm `> L` and `N 𝔞 < 3M`.
* `card_le_mul`: `#{N I ≤ X} ≤ c X` (Mathlib's ideal-count asymptotic).
* `SBf_of_B2f`: rows `M < N 𝔡 ≤ 2M` (squarefree) inside `RwF` with weight `1`, for `L ≤ M`.
* `SBf_cols_blocks`: columns `N 𝔠 ≤ C` from the dyadic column blocks (Cauchy–Schwarz).
-/

open NumberField ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

lemma fin_rows (𝔪 : Ideal (𝓞 F)) (L M : ℝ) :
    {𝔞 : Ideal (𝓞 F) | IsExterior 𝔪 𝔞 ∧ (∀ 𝔟 : Ideal (𝓞 F), 𝔟 ^ 2 ∣ 𝔞 →
      L * (Ideal.absNorm 𝔟 : ℝ) ^ 2 < Ideal.absNorm 𝔞) ∧ (Ideal.absNorm 𝔞 : ℝ) < 3 * M}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊3 * M⌋₊).subset
    (fun 𝔞 h => Nat.le_floor h.2.2.le)

/-- The rows of `Σ₂`, `Σ₃` meeting the weight. -/
noncomputable def RwF (𝔪 : Ideal (𝓞 F)) (L M : ℝ) : Finset (Ideal (𝓞 F)) :=
  (fin_rows 𝔪 L M).toFinset

lemma mem_RwF {𝔪 : Ideal (𝓞 F)} {L M : ℝ} {𝔞 : Ideal (𝓞 F)} :
    𝔞 ∈ RwF 𝔪 L M ↔ IsExterior 𝔪 𝔞 ∧ (∀ 𝔟 : Ideal (𝓞 F), 𝔟 ^ 2 ∣ 𝔞 →
      L * (Ideal.absNorm 𝔟 : ℝ) ^ 2 < Ideal.absNorm 𝔞) ∧ (Ideal.absNorm 𝔞 : ℝ) < 3 * M := by
  unfold RwF; rw [Set.Finite.mem_toFinset]; rfl

/-- Linear ideal counting. -/
theorem card_le_mul (F : Type*) [Field F] [NumberField F] :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset (Ideal (𝓞 F)),
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X) → (S.card : ℝ) ≤ c * X := by
  have ht := NumberField.Ideal.tendsto_norm_le_div_atTop F
  set l := (2 ^ NumberField.InfinitePlace.nrRealPlaces F * (2 * Real.pi) ^
    NumberField.InfinitePlace.nrComplexPlaces F * NumberField.Units.regulator F *
    (NumberField.classNumber F : ℝ)) /
    (NumberField.Units.torsionOrder F * Real.sqrt |(NumberField.discr F : ℝ)|) with hl
  have hev := ht.eventually (Iic_mem_nhds (lt_add_one l))
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.1 hev
  set s₁ := max s₀ 1
  have hfin : ∀ X : ℝ, {I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ X}.Finite := fun X =>
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊X⌋₊).subset
      (fun I h => Nat.le_floor h)
  have hcardS : ∀ X : ℝ, ∀ S : Finset (Ideal (𝓞 F)), (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X) →
      (S.card : ℝ) ≤ Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} := by
    intro X S hS
    change (S.card : ℝ) ≤
      (Nat.card ({I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ X} : Set (Ideal (𝓞 F))) : ℝ)
    rw [← Set.ncard_coe_finset, Nat.card_coe_set_eq]
    exact_mod_cast Set.ncard_le_ncard (fun I hI => hS I hI) (hfin X)
  set c₀ : ℝ := ((Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ s₁} : ℕ) : ℝ)
  have hl0 : 0 ≤ l + 1 := by
    have : 0 ≤ l := by
      rw [hl]
      have := NumberField.Units.regulator_pos F
      positivity
    linarith
  refine ⟨max (l + 1) c₀, le_trans hl0 (le_max_left _ _), fun X hX S hS => ?_⟩
  refine (hcardS X S hS).trans ?_
  by_cases hXs : s₁ ≤ X
  · have h1 := hs₀ X (le_trans (le_max_left _ _) hXs)
    have hX0 : 0 < X := by linarith
    rw [div_le_iff₀ hX0] at h1
    calc (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} : ℝ) ≤ (l + 1) * X := h1
      _ ≤ max (l + 1) c₀ * X := by gcongr; exact le_max_left _ _
  · push Not at hXs
    have hmono : (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} : ℝ) ≤ c₀ := by
      change (Nat.card ({I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ X} : Set (Ideal (𝓞 F))) : ℝ) ≤
        (Nat.card ({I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ s₁} : Set (Ideal (𝓞 F))) : ℝ)
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact_mod_cast Set.ncard_le_ncard (fun I (hI : (Ideal.absNorm I : ℝ) ≤ X) =>
        (show (Ideal.absNorm I : ℝ) ≤ s₁ by linarith)) (hfin s₁)
    have hc0 : 0 ≤ c₀ := Nat.cast_nonneg _
    calc (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} : ℝ) ≤ c₀ := hmono
      _ ≤ max (l + 1) c₀ := le_max_right _ _
      _ = max (l + 1) c₀ * 1 := (mul_one _).symm
      _ ≤ max (l + 1) c₀ * X := by gcongr

/-- The `tsum` hypothesis `(E_α)` as an `SBf` bound. -/
lemma SBf_of_sb (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) {C D v : ℝ}
    (h : ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
        (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
      ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
          (Ideal.absNorm 𝔡 : ℝ) ≤ D},
          ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
        v * ∑' 𝔠, ‖z 𝔠‖ ^ 2) :
    SBf (chiK ι 𝔪 g) (rowsF 𝔪 0 D) (rowsF 𝔪 0 C) v := by
  intro z'
  have h1 := h (fun c => z' c.1)
  rw [tsum_subtype_eq _ _ (fun x => mem_rowsF_zero) (fun c => ‖z' c‖ ^ 2)] at h1
  have hin : ∀ 𝔡 : Ideal (𝓞 F), ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
      (Ideal.absNorm 𝔠 : ℝ) ≤ C}, z' 𝔠.1 * residueSymbol ι 𝔪 𝔡 (g.gen 𝔠.1) ^ 3 =
      ∑ c ∈ rowsF 𝔪 0 C, z' c * chiK ι 𝔪 g 𝔡 c := fun 𝔡 =>
    tsum_subtype_eq _ _ (fun x => mem_rowsF_zero) (fun c => z' c * chiK ι 𝔪 g 𝔡 c)
  simp_rw [hin] at h1
  rw [tsum_subtype_eq _ _ (fun x => mem_rowsF_zero)
    (fun 𝔡 => ‖∑ c ∈ rowsF 𝔪 0 C, z' c * chiK ι 𝔪 g 𝔡 c‖ ^ 2)] at h1
  exact h1

end L3H

end
end

section
section
/-!
# L3Q_Red: from the statement's `tsum` form to the pieces

* `tsum_LHS_eq`: the statement's double `tsum` is `L3H.S3` over the finite column set.
* `S3_reindex`: `b = 𝔤 c`; `b₁ ⊔ b₂ = 𝔤 ⟺ c₁ ⊔ c₂ = ⊤`.
* `row_eq_pair`: the row sum of a pair is the pair sum of `pair_eq`.
* `split_principal`, `principal_le`, `PSnp_decomp`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma sup_eq_top_of_isRelPrime {I J : Ideal (𝓞 F)} (h : IsRelPrime I J) : I ⊔ J = ⊤ := by
  by_contra hc
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hc
  have h1 : P ∣ I := Ideal.dvd_iff_le.2 (le_trans le_sup_left hle)
  have h2 : P ∣ J := Ideal.dvd_iff_le.2 (le_trans le_sup_right hle)
  exact hP.ne_top (Ideal.isUnit_iff.1 (h h1 h2))

lemma sup_eq_top_of_sqf {I J : Ideal (𝓞 F)} (h : Squarefree (I * J)) : I ⊔ J = ⊤ :=
  sup_eq_top_of_isRelPrime (squarefree_mul_iff.1 h).1

lemma sqf_mul_of_sup {I J : Ideal (𝓞 F)} (hI : Squarefree I) (hJ : Squarefree J)
    (h : I ⊔ J = ⊤) : Squarefree (I * J) :=
  squarefree_mul_iff.2 ⟨(Ideal.isCoprime_iff_sup_eq.2 h).isRelPrime, hI, hJ⟩

lemma ext_right {𝔪 I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) : IsExterior 𝔪 J := by
  refine ⟨fun hJ => h.1 (by rw [hJ, Ideal.mul_bot]), (sup_mul_eq_top_iff.1 h.2).2⟩

lemma ext_left {𝔪 I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) : IsExterior 𝔪 I := by
  refine ⟨fun hI => h.1 (by rw [hI, Ideal.bot_mul]), (sup_mul_eq_top_iff.1 h.2).1⟩

lemma ext_mul {𝔪 I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨?_, sup_mul_eq_top_iff.2 ⟨hI.2, hJ.2⟩⟩
  rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
  exact ⟨by rw [Ideal.zero_eq_bot]; exact hI.1, by rw [Ideal.zero_eq_bot]; exact hJ.1⟩

lemma mul_ne_top_of {I J : Ideal (𝓞 F)} (h : ¬ (I = ⊤ ∧ J = ⊤)) : I * J ≠ ⊤ := by
  intro hIJ
  apply h
  exact ⟨eq_top_iff.2 (hIJ ▸ Ideal.mul_le_left), eq_top_iff.2 (hIJ ▸ Ideal.mul_le_right)⟩

/-! ### The statement's `tsum` form -/

open Classical in
theorem tsum_LHS_eq (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) (W : ℝ → ℝ)
    (hW3 : ∀ t, 3 ≤ t → W t = 0) {k : ℕ} (cls : Ideal (𝓞 F) → Fin k) (M N L : ℝ) (hM0 : 0 < M)
    (𝔤 : Ideal (𝓞 F)) (j : Fin k)
    (z : {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟 ∧ Squarefree 𝔟 ∧
      N < (Ideal.absNorm 𝔟 : ℝ) ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ 2 * N ∧ cls 𝔟 = j} → ℂ) :
    (∑' 𝔟₁, ∑' 𝔟₂, if 𝔟₁.1 ⊔ 𝔟₂.1 = 𝔤 then
        z 𝔟₁ * starRingEnd ℂ (z 𝔟₂) *
          ∑' 𝔞 : {𝔞 : Ideal (𝓞 F) // IsExterior 𝔪 𝔞 ∧
              ∀ 𝔟 : Ideal (𝓞 F), 𝔟 ^ 2 ∣ 𝔞 →
                L * (Ideal.absNorm 𝔟 : ℝ) ^ 2 < Ideal.absNorm 𝔞},
            (W ((Ideal.absNorm 𝔞.1 : ℝ) / M) : ℂ) *
              residueSymbol ι 𝔪 𝔞.1 (g.gen 𝔟₁.1) ^ 3 *
              starRingEnd ℂ (residueSymbol ι 𝔪 𝔞.1 (g.gen 𝔟₂.1) ^ 3)
      else 0) =
      L3H.S3 (L3H.chiK ι 𝔪 g) (L3H.RwF 𝔪 L M) (fun 𝔞 => W ((Ideal.absNorm 𝔞 : ℝ) / M))
        (· ⊔ ·) ((L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)) 𝔤
        (fun b => if h : IsExterior 𝔪 b ∧ Squarefree b ∧ N < (Ideal.absNorm b : ℝ) ∧
          (Ideal.absNorm b : ℝ) ≤ 2 * N ∧ cls b = j then z ⟨b, h⟩ else 0) ∧
    ∑' 𝔟, ‖z 𝔟‖ ^ 2 = ∑ b ∈ (L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j),
      ‖(if h : IsExterior 𝔪 b ∧ Squarefree b ∧ N < (Ideal.absNorm b : ℝ) ∧
          (Ideal.absNorm b : ℝ) ≤ 2 * N ∧ cls b = j then z ⟨b, h⟩ else 0)‖ ^ 2 := by
  set lam : Ideal (𝓞 F) → ℂ := fun b => if h : IsExterior 𝔪 b ∧ Squarefree b ∧
    N < (Ideal.absNorm b : ℝ) ∧ (Ideal.absNorm b : ℝ) ≤ 2 * N ∧ cls b = j then z ⟨b, h⟩ else 0
    with hlam
  have hz : ∀ b : {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟 ∧ Squarefree 𝔟 ∧
      N < (Ideal.absNorm 𝔟 : ℝ) ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ 2 * N ∧ cls 𝔟 = j}, z b = lam b.1 :=
    fun b => by simp [hlam, b.2]
  have hcol : ∀ x, x ∈ (L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j) ↔
      (IsExterior 𝔪 x ∧ Squarefree x ∧ N < (Ideal.absNorm x : ℝ) ∧
        (Ideal.absNorm x : ℝ) ≤ 2 * N ∧ cls x = j) := by
    intro x
    rw [Finset.mem_filter, L3H.mem_rowsF]
    tauto
  have hrow : ∀ b₁ b₂ : Ideal (𝓞 F),
      ∑' 𝔞 : {𝔞 : Ideal (𝓞 F) // IsExterior 𝔪 𝔞 ∧ ∀ 𝔟 : Ideal (𝓞 F), 𝔟 ^ 2 ∣ 𝔞 →
          L * (Ideal.absNorm 𝔟 : ℝ) ^ 2 < Ideal.absNorm 𝔞},
        (W ((Ideal.absNorm 𝔞.1 : ℝ) / M) : ℂ) * residueSymbol ι 𝔪 𝔞.1 (g.gen b₁) ^ 3 *
          starRingEnd ℂ (residueSymbol ι 𝔪 𝔞.1 (g.gen b₂) ^ 3) =
      ∑ a ∈ L3H.RwF 𝔪 L M, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) * L3H.chiK ι 𝔪 g a b₁ *
        starRingEnd ℂ (L3H.chiK ι 𝔪 g a b₂) := by
    intro b₁ b₂
    refine tsum_subtype_of_zero' _ (L3H.RwF 𝔪 L M) (fun x hx => ⟨(L3H.mem_RwF.1 hx).1,
      (L3H.mem_RwF.1 hx).2.1⟩) (fun a => (W ((Ideal.absNorm a : ℝ) / M) : ℂ) *
        residueSymbol ι 𝔪 a (g.gen b₁) ^ 3 *
        starRingEnd ℂ (residueSymbol ι 𝔪 a (g.gen b₂) ^ 3)) ?_
    intro a ha hna
    have h3 : 3 * M ≤ (Ideal.absNorm a : ℝ) := by
      by_contra hc; push Not at hc
      exact hna (L3H.mem_RwF.2 ⟨ha.1, ha.2, hc⟩)
    have hW : W ((Ideal.absNorm a : ℝ) / M) = 0 := hW3 _ (by rw [le_div_iff₀ hM0]; linarith)
    simp only [hW, Complex.ofReal_zero, zero_mul]
  refine ⟨?_, ?_⟩
  · simp_rw [hz, hrow]
    have hin : ∀ b₁ : Ideal (𝓞 F), ∑' 𝔟₂ : {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟 ∧ Squarefree 𝔟 ∧
        N < (Ideal.absNorm 𝔟 : ℝ) ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ 2 * N ∧ cls 𝔟 = j},
        (if b₁ ⊔ 𝔟₂.1 = 𝔤 then lam b₁ * starRingEnd ℂ (lam 𝔟₂.1) *
          ∑ a ∈ L3H.RwF 𝔪 L M, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) *
            L3H.chiK ι 𝔪 g a b₁ * starRingEnd ℂ (L3H.chiK ι 𝔪 g a 𝔟₂.1) else 0) =
        ∑ b₂ ∈ (L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j),
          (if b₁ ⊔ b₂ = 𝔤 then lam b₁ * starRingEnd ℂ (lam b₂) *
            ∑ a ∈ L3H.RwF 𝔪 L M, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) *
              L3H.chiK ι 𝔪 g a b₁ * starRingEnd ℂ (L3H.chiK ι 𝔪 g a b₂) else 0) := fun b₁ =>
      L3H.tsum_subtype_eq _ _ hcol (fun b₂ => if b₁ ⊔ b₂ = 𝔤 then lam b₁ * starRingEnd ℂ (lam b₂) *
            ∑ a ∈ L3H.RwF 𝔪 L M, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) *
              L3H.chiK ι 𝔪 g a b₁ * starRingEnd ℂ (L3H.chiK ι 𝔪 g a b₂) else 0)
    simp_rw [hin]
    rw [L3H.tsum_subtype_eq _ _ hcol (fun b₁ => ∑ b₂ ∈ (L3H.rowsF 𝔪 N (2 * N)).filter
      (fun b => cls b = j), (if b₁ ⊔ b₂ = 𝔤 then lam b₁ * starRingEnd ℂ (lam b₂) *
            ∑ a ∈ L3H.RwF 𝔪 L M, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) *
              L3H.chiK ι 𝔪 g a b₁ * starRingEnd ℂ (L3H.chiK ι 𝔪 g a b₂) else 0))]
    rfl
  · calc ∑' 𝔟, ‖z 𝔟‖ ^ 2 = ∑' 𝔟 : {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟 ∧ Squarefree 𝔟 ∧
          N < (Ideal.absNorm 𝔟 : ℝ) ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ 2 * N ∧ cls 𝔟 = j}, ‖lam 𝔟.1‖ ^ 2 :=
          tsum_congr fun b => by rw [hz b]
      _ = _ := L3H.tsum_subtype_eq _ _ hcol (fun b => ‖lam b‖ ^ 2)

/-! ### Reindexing by `b = 𝔤 c` -/

open Classical in
theorem S3_reindex (χ : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ) (Rw : Finset (Ideal (𝓞 F)))
    (w : Ideal (𝓞 F) → ℝ) {𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) (Cs C'' : Finset (Ideal (𝓞 F)))
    (hC'' : ∀ b ∈ Cs, ∀ c, b = 𝔤 * c → c ∈ C'') (lam : Ideal (𝓞 F) → ℂ) :
    L3H.S3 χ Rw w (· ⊔ ·) Cs 𝔤 lam =
      ∑ c₁ ∈ C''.filter (fun c => 𝔤 * c ∈ Cs), ∑ c₂ ∈ C''.filter (fun c => 𝔤 * c ∈ Cs),
        if c₁ ⊔ c₂ = ⊤ then lam (𝔤 * c₁) * starRingEnd ℂ (lam (𝔤 * c₂)) *
          ∑ a ∈ Rw, (w a : ℂ) * χ a (𝔤 * c₁) * starRingEnd ℂ (χ a (𝔤 * c₂)) else 0 := by
  unfold L3H.S3
  rw [L3H.reindex h𝔤 Cs C'' hC'' _ ?_]
  · rw [← Finset.sum_filter]
    refine Finset.sum_congr rfl fun c₁ hc₁ => ?_
    rw [L3H.reindex h𝔤 Cs C'' hC'' _ ?_]
    · rw [← Finset.sum_filter]
      refine Finset.sum_congr rfl fun c₂ _ => ?_
      by_cases h : c₁ ⊔ c₂ = ⊤
      · rw [if_pos h, if_pos ((L3H.mul_sup_eq_iff h𝔤).2 h)]
      · rw [if_neg h, if_neg (fun h' => h ((L3H.mul_sup_eq_iff h𝔤).1 h'))]
    · intro b _ hb
      rw [if_neg]
      intro h; apply hb; rw [Ideal.dvd_iff_le, ← h]; exact le_sup_right
  · intro b _ hb
    refine Finset.sum_eq_zero fun b₂ _ => ?_
    rw [if_neg]
    intro h; apply hb; rw [Ideal.dvd_iff_le, ← h]; exact le_sup_left

/-! ### The row sum of one pair -/

open Classical in
theorem row_eq_pair {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪)
    (h𝔪 : 𝔪 ≠ ⊥) {𝔤 c₁ c₂ : Ideal (𝓞 F)} (h𝔤 : IsExterior 𝔪 𝔤) (hc₁ : IsExterior 𝔪 c₁)
    (hc₂ : IsExterior 𝔪 c₂) {M : ℝ} (hM : 0 < M) (L : ℝ) :
    ∑ a ∈ L3H.RwF 𝔪 L M, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) *
        L3H.chiK ι 𝔪 g a (𝔤 * c₁) * starRingEnd ℂ (L3H.chiK ι 𝔪 g a (𝔤 * c₂)) =
      ∑' a : Ideal (𝓞 F), (if a ⊔ 𝔤 = ⊤ ∧ sgt L a then
        (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * psiP g c₁ c₂ a else 0) := by
  have hmul : ∀ a, IsExterior 𝔪 a → ∀ c, IsExterior 𝔪 c →
      L3H.chiK ι 𝔪 g a (𝔤 * c) = L3H.chiK ι 𝔪 g a 𝔤 * L3H.chiK ι 𝔪 g a c := by
    intro a ha c hc
    unfold L3H.chiK
    rw [C3M.residueSymbol_gen_mul hχ g ha h𝔤 hc, mul_pow]
  rw [tsum_eq_sum (s := L3H.RwF 𝔪 L M)]
  · refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨hae, hsgt, -⟩ := L3H.mem_RwF.1 ha
    rw [chiK_conj hχ g hae, hmul a hae c₁ hc₁, hmul a hae c₂ hc₂]
    have hsq := chiK_sq hχ g hae h𝔤
    have e : L3H.chiK ι 𝔪 g a 𝔤 * L3H.chiK ι 𝔪 g a c₁ * (L3H.chiK ι 𝔪 g a 𝔤 *
        L3H.chiK ι 𝔪 g a c₂) = L3H.chiK ι 𝔪 g a 𝔤 ^ 2 * psiP g c₁ c₂ a := by
      simp only [psiP_apply]; ring
    rw [mul_assoc, e, hsq]
    by_cases h : a ⊔ 𝔤 = ⊤
    · rw [if_pos h, if_pos ⟨h, hsgt⟩]; ring
    · rw [if_neg h, if_neg (fun h' => h h'.1)]; ring
  · intro a ha
    by_cases h : a ⊔ 𝔤 = ⊤ ∧ sgt L a
    · rw [if_pos h]
      by_cases ha0 : a = ⊥
      · rw [ha0]; simp [W_zero]
      by_cases hae : a ⊔ 𝔪 = ⊤
      · have h3 : 3 * M ≤ (Ideal.absNorm a : ℝ) := by
          by_contra hc; push Not at hc
          exact ha (L3H.mem_RwF.2 ⟨⟨ha0, hae⟩, h.2, hc⟩)
        rw [W_div_eq_zero hM h3]; simp
      · simp only [psiP_apply, L3H.chiK, rs_nonext h𝔪 ha0 hae]; ring
    · rw [if_neg h]

/-! ### Principal pair and linearity -/

open Classical in
theorem split_principal (C : Finset (Ideal (𝓞 F))) (z : Ideal (𝓞 F) → ℂ)
    (G : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ) :
    ∑ c₁ ∈ C, ∑ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ then z c₁ * starRingEnd ℂ (z c₂) * G c₁ c₂ else 0) =
      PSnp C z G + ∑ c₁ ∈ C, ∑ c₂ ∈ C,
        (if c₁ = ⊤ ∧ c₂ = ⊤ then z c₁ * starRingEnd ℂ (z c₂) * G c₁ c₂ else 0) := by
  unfold PSnp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c₁ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c₂ _ => ?_
  by_cases h1 : c₁ = ⊤ ∧ c₂ = ⊤
  · obtain ⟨rfl, rfl⟩ := h1
    simp
  · rw [if_neg h1, add_zero]
    by_cases h2 : c₁ ⊔ c₂ = ⊤
    · rw [if_pos h2, if_pos ⟨h2, h1⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.1)]

open Classical in
theorem principal_le (C : Finset (Ideal (𝓞 F))) (z : Ideal (𝓞 F) → ℂ)
    (G : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ‖G ⊤ ⊤‖ ≤ B) :
    ‖∑ c₁ ∈ C, ∑ c₂ ∈ C,
        (if c₁ = ⊤ ∧ c₂ = ⊤ then z c₁ * starRingEnd ℂ (z c₂) * G c₁ c₂ else 0)‖ ≤
      B * ∑ c ∈ C, ‖z c‖ ^ 2 := by
  by_cases hT : (⊤ : Ideal (𝓞 F)) ∈ C
  · rw [Finset.sum_eq_single_of_mem ⊤ hT (fun c₁ _ hne =>
      Finset.sum_eq_zero (fun c₂ _ => if_neg (fun h => hne h.1)))]
    rw [Finset.sum_eq_single_of_mem ⊤ hT (fun c₂ _ hne => if_neg (fun h => hne h.2))]
    rw [if_pos ⟨rfl, rfl⟩, norm_mul, norm_mul, Complex.norm_conj]
    have h1 : ‖z ⊤‖ ^ 2 ≤ ∑ c ∈ C, ‖z c‖ ^ 2 :=
      Finset.single_le_sum (f := fun c => ‖z c‖ ^ 2) (fun c _ => by positivity) hT
    calc ‖z ⊤‖ * ‖z ⊤‖ * ‖G ⊤ ⊤‖ ≤ ‖z ⊤‖ ^ 2 * B := by
          rw [← pow_two]; exact mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ (∑ c ∈ C, ‖z c‖ ^ 2) * B := mul_le_mul_of_nonneg_right h1 hB0
      _ = _ := mul_comm _ _
  · rw [Finset.sum_eq_zero (fun c₁ hc₁ => Finset.sum_eq_zero (fun c₂ _ =>
      if_neg (fun (h : c₁ = ⊤ ∧ c₂ = ⊤) => hT (h.1 ▸ hc₁))))]
    simp only [norm_zero]
    exact mul_nonneg hB0 (Finset.sum_nonneg fun _ _ => by positivity)

open Classical in
theorem PSnp_decomp (C : Finset (Ideal (𝓞 F))) (z : Ideal (𝓞 F) → ℂ)
    (G A B D E : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (h : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ⊔ c₂ = ⊤ → ¬ (c₁ = ⊤ ∧ c₂ = ⊤) →
      G c₁ c₂ = A c₁ c₂ + B c₁ c₂ + D c₁ c₂ - E c₁ c₂) :
    PSnp C z G = PSnp C z A + PSnp C z B + PSnp C z D - PSnp C z E := by
  unfold PSnp
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c₁ hc₁ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c₂ hc₂ => ?_
  by_cases hp : c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤)
  · obtain ⟨hp1, hp2⟩ := hp
    have e := h c₁ hc₁ c₂ hc₂ hp1 hp2
    simp only [hp1, hp2, not_false_eq_true, and_self, if_true, e]; ring
  · simp only [if_neg hp]; ring

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_PDP: the error term `DP` summed over pairs

On `Re w = 1 − ε′`: `HP = Kc(w) ∑_{e ⊆ primes(𝔤)} (−1)^{|e|} N(e)^{-w} u_e(c₁) u_e(c₂) ∑_s N s^{w−1} χ χ`,
`u_e(c) = χ_c(e) N c^{1/2 − w} ∏_{P ∣ c}(1 − NP^{-2(1−w)})`; then the bilinear bound.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Finset
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Dy: dyadic decomposition of rows with weight `N s^{-1/2}`

`bil_dyadic`: for row weights supported on `Y₀ < N s ≤ Y₁` with `|a(s)| ≤ N s^{-1/2}`, the pair sum is
at most `nblk · 2 Bm √U √V`, where `Bm` bounds `(2^k Y₀)^{-1/2} β(2^{k+1} Y₀)` on the blocks and
`nblk = clog₂ ⌈Y₁/Y₀⌉ ≤ (2(Y₁/Y₀ + 1))^δ / (δ log 2)`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Finset

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma nblk_le {δ : ℝ} (hδ : 0 < δ) {Y₀ Y₁ : ℝ} (hY₀ : 0 < Y₀) (hY : Y₀ ≤ Y₁) :
    (nblk Y₀ Y₁ : ℝ) ≤ (2 * (Y₁ / Y₀ + 1)) ^ δ / (δ * Real.log 2) := by
  set K := nblk Y₀ Y₁
  set n := ⌈Y₁ / Y₀⌉₊
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (n : ℝ) ≤ Y₁ / Y₀ + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (by linarith) hY₀.le)).le
  -- `2^K ≤ 2 n`
  have h2K : (2 : ℝ) ^ K ≤ 2 * n := by
    rcases Nat.lt_or_ge 1 n with hn | hn
    · have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hn
      have hK0 : 0 < K := Nat.clog_pos (by norm_num) hn
      have : (2 : ℝ) ^ (K - 1) < n := by exact_mod_cast this
      have e : (2 : ℝ) ^ K = 2 * 2 ^ (K - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e]; linarith
    · have hK : K = 0 := by
        show Nat.clog 2 n = 0
        exact Nat.clog_of_right_le_one hn 2
      rw [hK, pow_zero]
      have : (1 : ℝ) ≤ n := by
        have : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by
          rw [Ne, Nat.ceil_eq_zero, not_le]; exact div_pos (by linarith) hY₀)
        exact_mod_cast this
      linarith
  -- `K δ log 2 ≤ 2^{K δ}`
  have hexp : (K : ℝ) * δ * Real.log 2 ≤ ((2 : ℝ) ^ K) ^ δ := by
    have h := Real.add_one_le_exp ((K : ℝ) * δ * Real.log 2)
    have e : Real.exp ((K : ℝ) * δ * Real.log 2) = ((2 : ℝ) ^ K) ^ δ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
      ring_nf
    linarith [e]
  rw [le_div_iff₀ (by positivity)]
  calc (K : ℝ) * (δ * Real.log 2) = (K : ℝ) * δ * Real.log 2 := by ring
    _ ≤ ((2 : ℝ) ^ K) ^ δ := hexp
    _ ≤ (2 * (Y₁ / Y₀ + 1)) ^ δ := by
        apply Real.rpow_le_rpow (by positivity) _ hδ.le
        linarith

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_PTT: the main-term difference `T − T′` summed over pairs

The rows run between `L′/N f` and `L` with weight `N s^{-1/2}`; dyadic blocks (`bil_dyadic`).
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex Finset
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma norm_chiK_le {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (a c : Ideal (𝓞 F)) :
    ‖L3H.chiK ι 𝔪 g a c‖ ≤ 1 := by
  simp only [L3H.chiK, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_rs_le _ _)

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_PDQ: the dual tail `DQ` (crude bound)

On `Re w = −σ₁`: `‖HQ‖ ≤ M^{−σ₁} N𝔤^{σ₁} 2^{ω(𝔤)} (N c₁ N c₂)^{1/2+σ₁} 2^{ω(c₁)+ω(c₂)} L′^{−(σ₁−1/2)} · K (1+|t|)^A`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex MeasureTheory Finset
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma absNorm_pideal_primesOf_le {𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) :
    (∏ P ∈ primesOf 𝔤, (Ideal.absNorm P : ℝ)) ≤ Ideal.absNorm 𝔤 := by
  have hd : pideal (primesOf 𝔤) ∣ 𝔤 := by
    refine Finset.prod_primes_dvd 𝔤 (fun P hP => Ideal.prime_of_isPrime (primesOf_prime hP).2
      (primesOf_prime hP).1) fun P hP => ?_
    exact Ideal.dvd_iff_le.2 (le_of_mem_primesOf hP)
  have h1 : Ideal.absNorm (pideal (primesOf 𝔤)) ≤ Ideal.absNorm 𝔤 :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔤))
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hd))
  have h2 : (Ideal.absNorm (pideal (primesOf 𝔤)) : ℝ) = ∏ P ∈ primesOf 𝔤, (Ideal.absNorm P : ℝ) := by
    unfold pideal; rw [map_prod]; push_cast; rfl
  rw [← h2]; exact_mod_cast h1

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_SBf: operations on finite bilinear-form bounds

* `SBf.transpose`: the duality principle `‖A‖ = ‖Aᵀ‖`;
* `SBf.congr_kernel`, `SBf.mono_cols`, `SBf.min`.
-/

namespace ArtinPrimitiveRoots.L3Q


open Finset

variable {I : Type*} [DecidableEq I]

theorem SBf_transpose {χ : I → I → ℂ} {R C : Finset I} {β : ℝ} (hβ : 0 ≤ β)
    (h : L3H.SBf χ R C β) : L3H.SBf (fun c a => χ a c) C R β := by
  intro w
  set y : I → ℂ := fun c => ∑ a ∈ R, w a * χ a c
  set Y : ℝ := ∑ c ∈ C, ‖y c‖ ^ 2
  set Wn : ℝ := ∑ a ∈ R, ‖w a‖ ^ 2
  set X : I → ℂ := fun a => ∑ c ∈ C, starRingEnd ℂ (y c) * χ a c
  have hY0 : 0 ≤ Y := sum_nonneg fun _ _ => by positivity
  have hW0 : 0 ≤ Wn := sum_nonneg fun _ _ => by positivity
  have hX : ∑ a ∈ R, ‖X a‖ ^ 2 ≤ β * Y := by
    have := h (fun c => starRingEnd ℂ (y c))
    simpa [X, Y, Complex.norm_conj] using this
  have hYeq : (Y : ℂ) = ∑ a ∈ R, w a * X a := by
    simp only [Y, X, y]
    push_cast
    have : ∀ c ∈ C, ((‖∑ a ∈ R, w a * χ a c‖ : ℝ) : ℂ) ^ 2 =
        starRingEnd ℂ (∑ a ∈ R, w a * χ a c) * ∑ a ∈ R, w a * χ a c :=
      fun c _ => (Complex.conj_mul' _).symm
    rw [sum_congr rfl this]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun c _ => by ring
  have hle : Y ≤ Real.sqrt Wn * Real.sqrt (β * Y) := by
    have h1 : Y ≤ ∑ a ∈ R, ‖w a‖ * ‖X a‖ := by
      have := congrArg Complex.re hYeq
      rw [Complex.ofReal_re] at this
      rw [this]
      refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (le_of_eq ?_))
      exact sum_congr rfl fun a _ => norm_mul _ _
    refine h1.trans ((Real.sum_mul_le_sqrt_mul_sqrt R _ _).trans ?_)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX) (Real.sqrt_nonneg _)
  show Y ≤ β * Wn
  rcases hY0.lt_or_eq with hYpos | hYz
  · have h2 : Y ^ 2 ≤ Wn * (β * Y) := by
      have := pow_le_pow_left₀ hY0 hle 2
      rwa [mul_pow, Real.sq_sqrt hW0, Real.sq_sqrt (by positivity)] at this
    nlinarith
  · rw [← hYz]; positivity

theorem SBf_congr_kernel {χ χ' : I → I → ℂ} {R C : Finset I} {β : ℝ}
    (h : L3H.SBf χ R C β) (heq : ∀ a ∈ R, ∀ c ∈ C, χ a c = χ' a c) : L3H.SBf χ' R C β := by
  intro z
  refine le_trans (le_of_eq ?_) (h z)
  refine sum_congr rfl fun a ha => ?_
  congr 2
  exact sum_congr rfl fun c hc => by rw [heq a ha c hc]

theorem SBf_min {χ : I → I → ℂ} {R C : Finset I} {β₁ β₂ : ℝ}
    (h₁ : L3H.SBf χ R C β₁) (h₂ : L3H.SBf χ R C β₂) : L3H.SBf χ R C (min β₁ β₂) := by
  intro z
  rcases le_total β₁ β₂ with h | h
  · rw [min_eq_left h]; exact h₁ z
  · rw [min_eq_right h]; exact h₂ z

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_E: the two-sided sieve bound from `(E_α)` and reciprocity

From `(E_α)` (rows `≤ D`, columns `≤ C`) and exact reciprocity, for every `δ > 0` there is `K ≥ 0`
with `SBf χ (rows ≤ Y) (cols ≤ C) (K min(Y' + C^α, C + Y'^α) (C Y')^δ)`, `Y' = max Y 1`, `C ≥ 1`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

set_option linter.unusedSectionVars false

/-- The two-sided bound. -/
noncomputable def betaE (K α δ Y C : ℝ) : ℝ :=
  K * min (max Y 1 + C ^ α) (C + max Y 1 ^ α) * (C * max Y 1) ^ δ

lemma betaE_nonneg {K α δ Y C : ℝ} (hK : 0 ≤ K) (hC : 1 ≤ C) : 0 ≤ betaE K α δ Y C := by
  unfold betaE
  have h1 : 0 < max Y 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have : 0 ≤ min (max Y 1 + C ^ α) (C + max Y 1 ^ α) :=
    le_min (by positivity) (by positivity)
  positivity

theorem sbf_of_E (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {α : ℝ}
    (hE : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
      ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
          (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
        ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
            (Ideal.absNorm 𝔡 : ℝ) ≤ D},
            ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
          K * (D + C ^ α) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y C : ℝ, 1 ≤ C →
      L3H.SBf (L3H.chiK ι 𝔪 g) (L3H.rowsF 𝔪 0 Y) (L3H.rowsF 𝔪 0 C) (betaE K α δ Y C) := by
  classical
  obtain ⟨K₀, hK₀⟩ := hE δ hδ
  set K := max K₀ 0
  refine ⟨K, le_max_right _ _, fun Y C hC => ?_⟩
  set Y' := max Y 1 with hY'
  have hY1 : 1 ≤ Y' := le_max_right _ _
  have hsub : L3H.rowsF 𝔪 0 Y ⊆ L3H.rowsF 𝔪 0 Y' := fun s hs => by
    rw [L3H.mem_rowsF_zero] at hs ⊢
    exact ⟨hs.1, hs.2.1, hs.2.2.trans (le_max_left _ _)⟩
  refine L3H.SBf.mono_rows ?_ hsub
  -- the direct bound
  have h1 : L3H.SBf (L3H.chiK ι 𝔪 g) (L3H.rowsF 𝔪 0 Y') (L3H.rowsF 𝔪 0 C)
      (K * (Y' + C ^ α) * (C * Y') ^ δ) := by
    refine (L3H.SBf_of_sb ι 𝔪 g (hK₀ C Y' hC hY1)).mono_v ?_
    have : 0 ≤ (Y' + C ^ α) * (C * Y') ^ δ := by positivity
    have := mul_le_mul_of_nonneg_right (le_max_left K₀ 0) this
    linarith [show K₀ * (Y' + C ^ α) * (C * Y') ^ δ = K₀ * ((Y' + C ^ α) * (C * Y') ^ δ) by ring,
      show K * (Y' + C ^ α) * (C * Y') ^ δ = K * ((Y' + C ^ α) * (C * Y') ^ δ) by ring]
  -- the reciprocal bound
  have h2 : L3H.SBf (L3H.chiK ι 𝔪 g) (L3H.rowsF 𝔪 0 Y') (L3H.rowsF 𝔪 0 C)
      (K * (C + Y' ^ α) * (C * Y') ^ δ) := by
    have h0 := (L3H.SBf_of_sb ι 𝔪 g (hK₀ Y' C hY1 hC)).mono_v
      (v' := K * (C + Y' ^ α) * (Y' * C) ^ δ) (by
        have : 0 ≤ (C + Y' ^ α) * (Y' * C) ^ δ := by positivity
        have := mul_le_mul_of_nonneg_right (le_max_left K₀ 0) this
        linarith [show K₀ * (C + Y' ^ α) * (Y' * C) ^ δ = K₀ * ((C + Y' ^ α) * (Y' * C) ^ δ) by ring,
          show K * (C + Y' ^ α) * (Y' * C) ^ δ = K * ((C + Y' ^ α) * (Y' * C) ^ δ) by ring])
    have ht := SBf_transpose (by
      have : 0 ≤ C + Y' ^ α := by positivity
      positivity) h0
    rw [mul_comm Y' C] at ht
    refine SBf_congr_kernel ht fun a ha c hc => ?_
    exact chiK_symm hχ g (L3H.mem_rowsF_zero.1 hc).1 (L3H.mem_rowsF_zero.1 ha).1
  have h3 := SBf_min h1 h2
  refine h3.mono_v (le_of_eq ?_)
  unfold betaE
  rw [← hY']
  have hP : 0 ≤ (C * Y') ^ δ := by positivity
  rw [mul_assoc K, mul_assoc K, ← mul_min_of_nonneg _ _ (le_max_right K₀ 0),
    ← min_mul_of_nonneg _ _ hP]
  ring

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Ex: the exponent bookkeeping (pure real inequalities)

`Tg M N L α = M + N + √M L^{α−1/2} + √(M/L) N`, the target's shape, in the range
`N²/M (MN)^ε ≤ L ≤ M/(MN)^ε`.
-/

namespace ArtinPrimitiveRoots.L3Q

open Real

/-- The target's shape. -/
noncomputable def Tg (M N L α : ℝ) : ℝ :=
  M + N + Real.sqrt M * L ^ (α - 1 / 2) + Real.sqrt (M / L) * N

/-- The range of `(M, N, L)`. -/
structure Rng (M N L ε : ℝ) : Prop where
  hM : 1 ≤ M
  hN : 1 ≤ N
  hε : 0 < ε
  hL1 : N ^ 2 / M * (M * N) ^ ε ≤ L
  hL2 : L ≤ M / (M * N) ^ ε

namespace Rng

variable {M N L ε : ℝ} (h : Rng M N L ε)
include h

lemma X1 : 1 ≤ M * N := by nlinarith [h.hM, h.hN]

lemma Xε : 1 ≤ (M * N) ^ ε := Real.one_le_rpow h.X1 h.hε.le

lemma Lpos : 0 < L := by
  have h1 : 0 < N ^ 2 / M * (M * N) ^ ε := by
    have := h.hM; have := h.hN; positivity
  linarith [h.hL1]

lemma L_le_M : L ≤ M := by
  have hM0 : 0 < M := by linarith [h.hM]
  refine h.hL2.trans ?_
  rw [div_le_iff₀ (by linarith [h.Xε])]
  nlinarith [h.Xε]

lemma L_ge : N ^ 2 / M ≤ L := by
  have hM0 : 0 < M := by linarith [h.hM]
  refine le_trans ?_ h.hL1
  have : 0 ≤ N ^ 2 / M := by positivity
  nlinarith [h.Xε]

end Rng

lemma Tg_ge_M {M N L α : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hL : 0 < L) : M ≤ Tg M N L α := by
  unfold Tg
  have h1 : 0 ≤ Real.sqrt M * L ^ (α - 1 / 2) := by positivity
  have h2 : 0 ≤ Real.sqrt (M / L) * N := by positivity
  linarith

lemma Tg_ge_N {M N L α : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hL : 0 < L) : N ≤ Tg M N L α := by
  unfold Tg
  have h1 : 0 ≤ Real.sqrt M * L ^ (α - 1 / 2) := by positivity
  have h2 : 0 ≤ Real.sqrt (M / L) * N := by positivity
  linarith

lemma Tg_ge_mid {M N L α : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hL : 0 < L) :
    Real.sqrt M * L ^ (α - 1 / 2) ≤ Tg M N L α := by
  unfold Tg
  have h2 : 0 ≤ Real.sqrt (M / L) * N := by positivity
  linarith

lemma Tg_ge_last {M N L α : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hL : 0 < L) :
    Real.sqrt (M / L) * N ≤ Tg M N L α := by
  unfold Tg
  have h1 : 0 ≤ Real.sqrt M * L ^ (α - 1 / 2) := by positivity
  linarith

lemma Tg_nonneg {M N L α : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hL : 0 < L) : 0 ≤ Tg M N L α :=
  hM.trans (Tg_ge_M hM hN hL)

/-- `M^{1−α} N^{2α−1} ≤ √M L^{α−1/2}` for `L ≥ N²/M`. -/
lemma key1 {M N L α : ℝ} (hM : 0 < M) (hN : 0 < N) (hα : 1 / 2 ≤ α) (hL : N ^ 2 / M ≤ L) :
    M ^ (1 - α) * N ^ (2 * α - 1) ≤ Real.sqrt M * L ^ (α - 1 / 2) := by
  have h1 : (N ^ 2 / M) ^ (α - 1 / 2) ≤ L ^ (α - 1 / 2) :=
    Real.rpow_le_rpow (by positivity) hL (by linarith)
  have e1 : (N ^ 2 / M) ^ (α - 1 / 2) = N ^ (2 * α - 1) * M ^ (-(α - 1 / 2)) := by
    rw [Real.div_rpow (by positivity) hM.le, Real.rpow_neg hM.le, div_eq_mul_inv]
    congr 1
    rw [show (N ^ 2 : ℝ) = N ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hN.le]
    congr 1; ring
  have h2 : Real.sqrt M * (N ^ 2 / M) ^ (α - 1 / 2) = M ^ (1 - α) * N ^ (2 * α - 1) := by
    rw [e1, Real.sqrt_eq_rpow]
    calc M ^ (1 / 2 : ℝ) * (N ^ (2 * α - 1) * M ^ (-(α - 1 / 2)))
        = (M ^ (1 / 2 : ℝ) * M ^ (-(α - 1 / 2))) * N ^ (2 * α - 1) := by ring
      _ = M ^ (1 - α) * N ^ (2 * α - 1) := by
        rw [← Real.rpow_add hM]; congr 2; ring
  rw [← h2]
  exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)

/-- `max L 1 ^ α ≤ Tg` (for `L ≤ M`). -/
lemma maxpow_le {M N L α : ℝ} (hM : 1 ≤ M) (hN : 0 ≤ N) (hL : 0 < L) (hLM : L ≤ M)
    (hα : 1 ≤ α) : max L 1 ^ α ≤ Tg M N L α := by
  rcases le_or_gt 1 L with h1 | h1
  · rw [max_eq_left h1]
    have e : L ^ α = Real.sqrt L * L ^ (α - 1 / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith)]; ring_nf
    rw [e]
    refine le_trans ?_ (Tg_ge_mid (by linarith) hN hL)
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hLM) (by positivity)
  · rw [max_eq_right h1.le, Real.one_rpow]
    exact hM.trans (Tg_ge_M (by linarith) hN hL)

/-- `√(M max L 1) ≤ Tg`. -/
lemma sqrtML_le {M N L α : ℝ} (hM : 1 ≤ M) (hN : 0 ≤ N) (hL : 0 < L) (hLM : L ≤ M)
    (hα : 1 ≤ α) : Real.sqrt (M * max L 1) ≤ Tg M N L α := by
  rcases le_or_gt 1 L with h1 | h1
  · rw [max_eq_left h1, Real.sqrt_mul (by linarith)]
    refine le_trans ?_ (Tg_ge_mid (by linarith) hN hL)
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  · rw [max_eq_right h1.le, mul_one]
    refine le_trans ?_ (Tg_ge_M (by linarith) hN hL)
    calc Real.sqrt M ≤ Real.sqrt M * Real.sqrt M := by
          have := Real.one_le_sqrt.2 hM; nlinarith [Real.sqrt_nonneg M]
      _ = M := Real.mul_self_sqrt (by linarith)

/-- The polynomial shape `B(Y, C) = max Y 1 + C + min(max Y 1, C)^α`. -/
noncomputable def Bf (α Y C : ℝ) : ℝ := max Y 1 + C + min (max Y 1) C ^ α

lemma min_le_Bf {α Y C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) :
    min (max Y 1 + C ^ α) (C + max Y 1 ^ α) ≤ Bf α Y C := by
  unfold Bf
  have hY : 1 ≤ max Y 1 := le_max_right _ _
  rcases le_total (max Y 1) C with h | h
  · rw [min_eq_left h]
    have := min_le_right (max Y 1 + C ^ α) (C + max Y 1 ^ α)
    linarith
  · rw [min_eq_right h]
    have := min_le_left (max Y 1 + C ^ α) (C + max Y 1 ^ α)
    linarith

lemma Bf_nonneg {α Y C : ℝ} (hC : 0 ≤ C) : 0 ≤ Bf α Y C := by
  unfold Bf
  have hY : 1 ≤ max Y 1 := le_max_right _ _
  have : 0 ≤ min (max Y 1) C := le_min (by linarith) hC
  positivity

lemma rpow_le_of_exp {X a b : ℝ} (hX : 1 ≤ X) (hab : a ≤ b) : X ^ a ≤ X ^ b :=
  Real.rpow_le_rpow_of_exponent_le hX hab

/-- RP: `B(L, C) ≤ 4 Tg`. -/
lemma Ex_RP {M N L ε α C : ℝ} (h : Rng M N L ε) (hα : 1 ≤ α) (hC0 : 0 ≤ C) (hC : C ≤ 2 * N) :
    Bf α L C ≤ 4 * Tg M N L α := by
  have hL := h.Lpos
  have hM0 : (0 : ℝ) ≤ M := by linarith [h.hM]
  have hN0 : (0 : ℝ) ≤ N := by linarith [h.hN]
  unfold Bf
  have h1 : max L 1 ≤ Tg M N L α :=
    (max_le h.L_le_M h.hM).trans (Tg_ge_M hM0 hN0 hL)
  have h2 : C ≤ 2 * Tg M N L α := hC.trans (by linarith [Tg_ge_N hM0 hN0 hL (α := α)])
  have h3 : min (max L 1) C ^ α ≤ Tg M N L α := by
    refine le_trans ?_ (maxpow_le h.hM hN0 hL h.L_le_M hα)
    exact Real.rpow_le_rpow (le_min (by positivity) hC0) (min_le_left _ _) (by linarith)
  linarith

lemma Lp_pow {M N η α : ℝ} (hM : 0 < M) (hN : 0 < N) :
    (4 * N ^ 2 / M * (M * N) ^ η) ^ α =
      4 ^ α * N ^ (2 * α) * M ^ (-α) * (M * N) ^ (α * η) := by
  have hX : 0 < M * N := mul_pos hM hN
  rw [Real.mul_rpow (by positivity) (by positivity), Real.div_rpow (by positivity) hM.le,
    Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hX.le, Real.rpow_neg hM.le]
  rw [show (N ^ 2 : ℝ) = N ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hN.le]
  rw [mul_comm η α]
  field_simp

lemma Ex_Nfac {N Ng ε' : ℝ} (hN : 0 < N) (hNg : 1 ≤ Ng) (h0 : 0 ≤ 1 - 2 * ε')
    (h1 : 1 - 2 * ε' ≤ 1) : (N / Ng) ^ (-(1 - 2 * ε')) ≤ Ng * N ^ (2 * ε') / N := by
  have e : (N / Ng) ^ (-(1 - 2 * ε')) = Ng ^ (1 - 2 * ε') * (N ^ (2 * ε') / N) := by
    rw [Real.rpow_neg (by positivity), Real.div_rpow hN.le (by linarith), inv_div,
      Real.rpow_sub hN, Real.rpow_one]
    have : 0 < N ^ (2 * ε') := by positivity
    field_simp
  rw [e]
  have hng : Ng ^ (1 - 2 * ε') ≤ Ng := by
    calc Ng ^ (1 - 2 * ε') ≤ Ng ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNg h1
      _ = Ng := Real.rpow_one Ng
  calc Ng ^ (1 - 2 * ε') * (N ^ (2 * ε') / N) ≤ Ng * (N ^ (2 * ε') / N) :=
        mul_le_mul_of_nonneg_right hng (by positivity)
    _ = _ := by ring

lemma Ex_ML' {M N η : ℝ} (hM : 0 < M) (hN : 0 < N) :
    M / N * (4 * N ^ 2 / M * (M * N) ^ η) = 4 * N * (M * N) ^ η := by
  field_simp

lemma Ex_ML'α {M N η α : ℝ} (hM : 0 < M) (hN : 0 < N) :
    M / N * (4 * N ^ 2 / M * (M * N) ^ η) ^ α =
      4 ^ α * (M ^ (1 - α) * N ^ (2 * α - 1)) * (M * N) ^ (α * η) := by
  rw [Lp_pow hM hN]
  have hm : M * M ^ (-α) = M ^ (1 - α) := by
    rw [show M * M ^ (-α) = M ^ (1 : ℝ) * M ^ (-α) by rw [Real.rpow_one], ← Real.rpow_add hM]
    ring_nf
  have hn : N ^ (2 * α) / N = N ^ (2 * α - 1) := by
    rw [Real.rpow_sub hN, Real.rpow_one]
  calc M / N * (4 ^ α * N ^ (2 * α) * M ^ (-α) * (M * N) ^ (α * η))
      = 4 ^ α * ((M * M ^ (-α)) * (N ^ (2 * α) / N)) * (M * N) ^ (α * η) := by ring
    _ = _ := by rw [hm, hn]

/-- `(M/N) B(L′, C) ≤ (8 + 4^α) (MN)^{η + αη} Tg`. -/
lemma Ex_MB {M N L ε α η C : ℝ} (h : Rng M N L ε) (hα : 1 ≤ α) (hη : 0 < η) (hC0 : 0 ≤ C)
    (hC : C ≤ 2 * N) :
    M / N * Bf α (4 * N ^ 2 / M * (M * N) ^ η) C ≤
      (8 + 4 ^ α) * (M * N) ^ (η + α * η) * Tg M N L α := by
  have hM0 : 0 < M := by linarith [h.hM]
  have hN0 : 0 < N := by linarith [h.hN]
  have hL := h.Lpos
  have hX1 := h.X1
  set X := M * N with hX
  set T := Tg M N L α
  set L' := 4 * N ^ 2 / M * X ^ η with hL'
  have hL'0 : 0 ≤ L' := by positivity
  have hT0 : 0 ≤ T := Tg_nonneg hM0.le hN0.le hL
  have hTM : M ≤ T := Tg_ge_M hM0.le hN0.le hL
  have hTN : N ≤ T := Tg_ge_N hM0.le hN0.le hL
  have hmid : Real.sqrt M * L ^ (α - 1 / 2) ≤ T := Tg_ge_mid hM0.le hN0.le hL
  have hXa : 1 ≤ X ^ (η + α * η) := Real.one_le_rpow hX1 (by positivity)
  have hXη : X ^ η ≤ X ^ (η + α * η) := rpow_le_of_exp hX1 (by nlinarith)
  have hXαη : X ^ (α * η) ≤ X ^ (η + α * η) := rpow_le_of_exp hX1 (by nlinarith)
  have hMN : M / N ≤ M := div_le_self hM0.le h.hN
  have hMN0 : 0 ≤ M / N := by positivity
  -- the three pieces
  have p1 : M / N * max L' 1 ≤ 4 * N * X ^ η + M := by
    have : max L' 1 ≤ L' + 1 := max_le (by linarith) (by linarith)
    calc M / N * max L' 1 ≤ M / N * (L' + 1) := mul_le_mul_of_nonneg_left this hMN0
      _ = 4 * N * X ^ η + M / N := by rw [mul_add, mul_one, hL', Ex_ML' hM0 hN0]
      _ ≤ 4 * N * X ^ η + M := by linarith
  have p2 : M / N * C ≤ 2 * M := by
    calc M / N * C ≤ M / N * (2 * N) := mul_le_mul_of_nonneg_left hC hMN0
      _ = 2 * M := by field_simp
  have p3 : M / N * min (max L' 1) C ^ α ≤ 4 ^ α * T * X ^ (α * η) + M := by
    have hmin : min (max L' 1) C ^ α ≤ L' ^ α + 1 := by
      have h1 : min (max L' 1) C ^ α ≤ max L' 1 ^ α :=
        Real.rpow_le_rpow (le_min (by positivity) hC0) (min_le_left _ _) (by linarith)
      refine h1.trans ?_
      rcases le_total L' 1 with h2 | h2
      · rw [max_eq_right h2, Real.one_rpow]; have : 0 ≤ L' ^ α := by positivity
        linarith
      · rw [max_eq_left h2]; linarith
    have e := Ex_ML'α (η := η) (α := α) hM0 hN0
    rw [← hX] at e
    have hk := key1 hM0 hN0 (by linarith) h.L_ge (α := α)
    calc M / N * min (max L' 1) C ^ α ≤ M / N * (L' ^ α + 1) := mul_le_mul_of_nonneg_left hmin hMN0
      _ = 4 ^ α * (M ^ (1 - α) * N ^ (2 * α - 1)) * X ^ (α * η) + M / N := by
          rw [mul_add, mul_one, hL', e]
      _ ≤ 4 ^ α * T * X ^ (α * η) + M := by
          have h4 : 0 ≤ (4 : ℝ) ^ α := by positivity
          have hXp : 0 ≤ X ^ (α * η) := by positivity
          have : 4 ^ α * (M ^ (1 - α) * N ^ (2 * α - 1)) * X ^ (α * η) ≤ 4 ^ α * T * X ^ (α * η) := by
            gcongr
            exact hk.trans hmid
          linarith
  unfold Bf
  rw [mul_add, mul_add]
  have h4 : 0 ≤ (4 : ℝ) ^ α := by positivity
  have hXp : 0 ≤ X ^ (α * η) := by positivity
  have e1 : 4 * N * X ^ η ≤ 4 * T * X ^ (η + α * η) := by
    have : 0 ≤ X ^ η := by positivity
    nlinarith
  have e2 : 4 ^ α * T * X ^ (α * η) ≤ 4 ^ α * T * X ^ (η + α * η) := by
    have : 0 ≤ 4 ^ α * T := by positivity
    exact mul_le_mul_of_nonneg_left hXαη this
  have e3 : M ≤ T * X ^ (η + α * η) := by nlinarith
  nlinarith

/-- DP. -/
lemma Ex_DP {M N L ε α η ε' Ng C : ℝ} (h : Rng M N L ε) (hα : 1 ≤ α) (hη : 0 < η)
    (hε' : 0 < ε') (hε'4 : ε' ≤ 1 / 4) (hNg : 1 ≤ Ng) (hC0 : 0 ≤ C) (hC : C ≤ 2 * N) :
    M ^ (1 - ε') * (N / Ng) ^ (-(1 - 2 * ε')) * Bf α (4 * N ^ 2 / M * (M * N) ^ η) C ≤
      (8 + 4 ^ α) * Ng * (M * N) ^ (2 * ε' + (η + α * η)) * Tg M N L α := by
  have hM0 : 0 < M := by linarith [h.hM]
  have hN0 : 0 < N := by linarith [h.hN]
  have hX1 := h.X1
  have hB0 : 0 ≤ Bf α (4 * N ^ 2 / M * (M * N) ^ η) C := Bf_nonneg hC0
  have h1 : M ^ (1 - ε') ≤ M := by
    calc M ^ (1 - ε') ≤ M ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.hM (by linarith)
      _ = M := Real.rpow_one M
  have h2 := Ex_Nfac hN0 hNg (ε' := ε') (by linarith) (by linarith)
  have h3 := Ex_MB h hα hη hC0 hC (L := L)
  have hNe : N ^ (2 * ε') ≤ (M * N) ^ (2 * ε') :=
    Real.rpow_le_rpow hN0.le (by nlinarith [h.hM]) (by linarith)
  have hT0 : 0 ≤ Tg M N L α := Tg_nonneg hM0.le hN0.le h.Lpos
  calc M ^ (1 - ε') * (N / Ng) ^ (-(1 - 2 * ε')) * Bf α (4 * N ^ 2 / M * (M * N) ^ η) C
      ≤ M * (Ng * N ^ (2 * ε') / N) * Bf α (4 * N ^ 2 / M * (M * N) ^ η) C := by
        gcongr
    _ = Ng * N ^ (2 * ε') * (M / N * Bf α (4 * N ^ 2 / M * (M * N) ^ η) C) := by ring
    _ ≤ Ng * (M * N) ^ (2 * ε') * ((8 + 4 ^ α) * (M * N) ^ (η + α * η) * Tg M N L α) := by
        gcongr
    _ = (8 + 4 ^ α) * Ng * ((M * N) ^ (2 * ε') * (M * N) ^ (η + α * η)) * Tg M N L α := by ring
    _ = _ := by rw [← Real.rpow_add (by linarith)]

lemma sqrt_Lp {M N η : ℝ} (hM : 0 < M) (hN : 0 < N) :
    Real.sqrt (M * (4 * N ^ 2 / M * (M * N) ^ η)) = 2 * N * Real.sqrt ((M * N) ^ η) := by
  have e : M * (4 * N ^ 2 / M * (M * N) ^ η) = (2 * N) ^ 2 * (M * N) ^ η := by
    field_simp; ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

lemma sqrt_rpow_le {X η : ℝ} (hX : 1 ≤ X) (hη : 0 ≤ η) : Real.sqrt (X ^ η) ≤ X ^ η := by
  have h1 : 1 ≤ X ^ η := Real.one_le_rpow hX hη
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

/-- `√(M Y₁) ≤ (1 + 2 X^η) Tg`. -/
lemma Ex_T1 {M N L ε α η Y₁ Nf : ℝ} (h : Rng M N L ε) (hα : 1 ≤ α) (hη : 0 < η) (hNf : 1 ≤ Nf)
    (hY₁ : Y₁ = max (4 * N ^ 2 / M * (M * N) ^ η / Nf) L) :
    Real.sqrt (M * Y₁) ≤ (1 + 2 * (M * N) ^ η) * Tg M N L α := by
  have hM0 : 0 < M := by linarith [h.hM]
  have hN0 : 0 < N := by linarith [h.hN]
  have hL := h.Lpos
  have hT0 : 0 ≤ Tg M N L α := Tg_nonneg hM0.le hN0.le hL
  have hTN : N ≤ Tg M N L α := Tg_ge_N hM0.le hN0.le hL
  have hX1 := h.X1
  have hXη : 0 ≤ (M * N) ^ η := by positivity
  rw [hY₁]
  rcases le_total (4 * N ^ 2 / M * (M * N) ^ η / Nf) L with h1 | h1
  · rw [max_eq_right h1]
    have := (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (le_max_left L 1) hM0.le)).trans
      (sqrtML_le h.hM hN0.le hL h.L_le_M hα)
    nlinarith
  · rw [max_eq_left h1]
    have hle : 4 * N ^ 2 / M * (M * N) ^ η / Nf ≤ 4 * N ^ 2 / M * (M * N) ^ η :=
      div_le_self (by positivity) hNf
    calc Real.sqrt (M * (4 * N ^ 2 / M * (M * N) ^ η / Nf))
        ≤ Real.sqrt (M * (4 * N ^ 2 / M * (M * N) ^ η)) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle hM0.le)
      _ = 2 * N * Real.sqrt ((M * N) ^ η) := sqrt_Lp hM0 hN0
      _ ≤ 2 * N * (M * N) ^ η := by
          gcongr; exact sqrt_rpow_le hX1 hη.le
      _ ≤ (1 + 2 * (M * N) ^ η) * Tg M N L α := by nlinarith

/-- `√(M/Y₀) N ≤ (1 + √Nf) Tg`. -/
lemma Ex_T2 {M N L ε α η Y₀ Nf : ℝ} (h : Rng M N L ε) (hη : 0 < η) (hNf : 1 ≤ Nf)
    (hY₀ : Y₀ = min (4 * N ^ 2 / M * (M * N) ^ η / Nf) L) :
    Real.sqrt (M / Y₀) * N ≤ (1 + Real.sqrt Nf) * Tg M N L α := by
  have hM0 : 0 < M := by linarith [h.hM]
  have hN0 : 0 < N := by linarith [h.hN]
  have hL := h.Lpos
  have hT0 : 0 ≤ Tg M N L α := Tg_nonneg hM0.le hN0.le hL
  have hTM : M ≤ Tg M N L α := Tg_ge_M hM0.le hN0.le hL
  have hlast := Tg_ge_last hM0.le hN0.le hL (α := α)
  have hX1 := h.X1
  rw [hY₀]
  rcases le_total (4 * N ^ 2 / M * (M * N) ^ η / Nf) L with h1 | h1
  · rw [min_eq_left h1]
    have hXη : 1 ≤ (M * N) ^ η := Real.one_le_rpow hX1 hη.le
    have e : M / (4 * N ^ 2 / M * (M * N) ^ η / Nf) = (M / (2 * N)) ^ 2 * (Nf / (M * N) ^ η) := by
      field_simp; ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have hs : Real.sqrt (Nf / (M * N) ^ η) ≤ Real.sqrt Nf :=
      Real.sqrt_le_sqrt (div_le_self (by linarith) hXη)
    calc M / (2 * N) * Real.sqrt (Nf / (M * N) ^ η) * N = M / 2 * Real.sqrt (Nf / (M * N) ^ η) := by
          field_simp
      _ ≤ M / 2 * Real.sqrt Nf := by gcongr
      _ ≤ (1 + Real.sqrt Nf) * Tg M N L α := by
          have : 0 ≤ Real.sqrt Nf := Real.sqrt_nonneg _
          nlinarith
  · rw [min_eq_right h1]
    have : 0 ≤ Real.sqrt Nf := Real.sqrt_nonneg _
    nlinarith

/-- `√M Y₁^{α−1/2} ≤ (1 + 4^α X^{αη}) Tg`. -/
lemma Ex_T3 {M N L ε α η Y₁ Nf : ℝ} (h : Rng M N L ε) (hα : 1 ≤ α) (hη : 0 < η) (hNf : 1 ≤ Nf)
    (hY₁ : Y₁ = max (4 * N ^ 2 / M * (M * N) ^ η / Nf) L) :
    Real.sqrt M * Y₁ ^ (α - 1 / 2) ≤ (1 + 4 ^ α * (M * N) ^ (α * η)) * Tg M N L α := by
  have hM0 : 0 < M := by linarith [h.hM]
  have hN0 : 0 < N := by linarith [h.hN]
  have hL := h.Lpos
  have hT0 : 0 ≤ Tg M N L α := Tg_nonneg hM0.le hN0.le hL
  have hmid := Tg_ge_mid hM0.le hN0.le hL (α := α)
  have hX1 := h.X1
  have h4 : (0 : ℝ) ≤ 4 ^ α * (M * N) ^ (α * η) := by positivity
  rw [hY₁]
  rcases le_total (4 * N ^ 2 / M * (M * N) ^ η / Nf) L with h1 | h1
  · rw [max_eq_right h1]; nlinarith
  · rw [max_eq_left h1]
    have hle : 4 * N ^ 2 / M * (M * N) ^ η / Nf ≤ 4 * N ^ 2 / M * (M * N) ^ η :=
      div_le_self (by positivity) hNf
    have hp : (4 * N ^ 2 / M * (M * N) ^ η / Nf) ^ (α - 1 / 2) ≤
        (4 * N ^ 2 / M * (M * N) ^ η) ^ (α - 1 / 2) :=
      Real.rpow_le_rpow (by positivity) hle (by linarith)
    -- `√M L′^{α−1/2} = 4^{α−1/2} M^{1−α} N^{2α−1} X^{(α−1/2)η}`
    have e : Real.sqrt M * (4 * N ^ 2 / M * (M * N) ^ η) ^ (α - 1 / 2) =
        4 ^ (α - 1 / 2) * (M ^ (1 - α) * N ^ (2 * α - 1)) * (M * N) ^ ((α - 1 / 2) * η) := by
      rw [Lp_pow hM0 hN0, Real.sqrt_eq_rpow]
      have hm : M ^ (1 / 2 : ℝ) * M ^ (-(α - 1 / 2)) = M ^ (1 - α) := by
        rw [← Real.rpow_add hM0]; ring_nf
      have hn : N ^ (2 * (α - 1 / 2)) = N ^ (2 * α - 1) := by ring_nf
      calc M ^ (1 / 2 : ℝ) * (4 ^ (α - 1 / 2) * N ^ (2 * (α - 1 / 2)) * M ^ (-(α - 1 / 2)) *
            (M * N) ^ ((α - 1 / 2) * η))
          = 4 ^ (α - 1 / 2) * ((M ^ (1 / 2 : ℝ) * M ^ (-(α - 1 / 2))) * N ^ (2 * (α - 1 / 2))) *
            (M * N) ^ ((α - 1 / 2) * η) := by ring
        _ = _ := by rw [hm, hn]
    have hk := key1 hM0 hN0 (by linarith) h.L_ge (α := α)
    have h4a : (4 : ℝ) ^ (α - 1 / 2) ≤ 4 ^ α := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hXa : (M * N) ^ ((α - 1 / 2) * η) ≤ (M * N) ^ (α * η) := rpow_le_of_exp hX1 (by nlinarith)
    have hMN : 0 ≤ M ^ (1 - α) * N ^ (2 * α - 1) := by positivity
    have h4p : (0 : ℝ) ≤ 4 ^ (α - 1 / 2) := by positivity
    have hXp : (0 : ℝ) ≤ (M * N) ^ ((α - 1 / 2) * η) := by positivity
    have hstep : 4 ^ (α - 1 / 2) * (M ^ (1 - α) * N ^ (2 * α - 1)) * (M * N) ^ ((α - 1 / 2) * η)
        ≤ 4 ^ α * Tg M N L α * (M * N) ^ (α * η) :=
      mul_le_mul (mul_le_mul h4a (hk.trans hmid) hMN (by positivity)) hXa hXp (by positivity)
    have hfin : 4 ^ α * Tg M N L α * (M * N) ^ (α * η) ≤
        (1 + 4 ^ α * (M * N) ^ (α * η)) * Tg M N L α := by nlinarith
    calc Real.sqrt M * (4 * N ^ 2 / M * (M * N) ^ η / Nf) ^ (α - 1 / 2)
        ≤ Real.sqrt M * (4 * N ^ 2 / M * (M * N) ^ η) ^ (α - 1 / 2) :=
          mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)
      _ = 4 ^ (α - 1 / 2) * (M ^ (1 - α) * N ^ (2 * α - 1)) * (M * N) ^ ((α - 1 / 2) * η) := e
      _ ≤ 4 ^ α * Tg M N L α * (M * N) ^ (α * η) := hstep
      _ ≤ (1 + 4 ^ α * (M * N) ^ (α * η)) * Tg M N L α := hfin

lemma rpow_neg_half_eq {Y : ℝ} (hY : 0 < Y) : Y ^ (-(1 / 2 : ℝ)) = (Real.sqrt Y)⁻¹ := by
  rw [Real.rpow_neg hY.le, Real.sqrt_eq_rpow]

lemma aux_one_le {q s a b : ℝ} (hq : 1 ≤ q) (hs : 1 ≤ s) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ q * s * (a * b) := by
  have h1 : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le ha hb
  have h2 : 1 ≤ q * s := one_le_mul_of_one_le_of_one_le hq hs
  exact one_le_mul_of_one_le_of_one_le h2 h1

lemma aux_TT {a b s u p q T : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hs : 1 ≤ s) (hus : u ≤ s)
    (hp : 1 ≤ p) (hpq : p * p = q) (hT : 0 ≤ T) :
    3 * ((1 + 2 * a) * T) + 2 * ((1 + u) * T) + p * ((1 + p * b) * T) ≤
      32 * q * s * (a * b) * T := by
  have hq : 1 ≤ q := by rw [← hpq]; exact one_le_mul_of_one_le_of_one_le hp hp
  set Q := q * s * (a * b) with hQ
  have hQ1 : 1 ≤ Q := aux_one_le hq hs ha hb
  have haQ : a ≤ Q := by
    have : 1 ≤ q * s * b := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hq hs) hb
    calc a = a * 1 := (mul_one a).symm
      _ ≤ a * (q * s * b) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = Q := by rw [hQ]; ring
  have hsQ : s ≤ Q := by
    have : 1 ≤ q * (a * b) := one_le_mul_of_one_le_of_one_le hq (one_le_mul_of_one_le_of_one_le ha hb)
    calc s = s * 1 := (mul_one s).symm
      _ ≤ s * (q * (a * b)) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = Q := by rw [hQ]; ring
  have hpQ : p ≤ Q := by
    have hpq' : p ≤ q := by rw [← hpq]; nlinarith
    have : q ≤ Q := by
      have : 1 ≤ s * (a * b) := one_le_mul_of_one_le_of_one_le hs (one_le_mul_of_one_le_of_one_le ha hb)
      calc q = q * 1 := (mul_one q).symm
        _ ≤ q * (s * (a * b)) := mul_le_mul_of_nonneg_left this (by linarith)
        _ = Q := by rw [hQ]; ring
    linarith
  have hqbQ : q * b ≤ Q := by
    have : 1 ≤ s * a := one_le_mul_of_one_le_of_one_le hs ha
    calc q * b = q * b * 1 := (mul_one _).symm
      _ ≤ q * b * (s * a) := mul_le_mul_of_nonneg_left this (by nlinarith)
      _ = Q := by rw [hQ]; ring
  have e : p * ((1 + p * b) * T) = (p + q * b) * T := by rw [← hpq]; ring
  rw [e]
  have h1 : 3 * (1 + 2 * a) ≤ 9 * Q := by linarith
  have h2 : 2 * (1 + u) ≤ 4 * Q := by linarith
  have h3 : p + q * b ≤ 2 * Q := by linarith
  have : 3 * (1 + 2 * a) + 2 * (1 + u) + (p + q * b) ≤ 32 * Q := by linarith
  calc 3 * ((1 + 2 * a) * T) + 2 * ((1 + u) * T) + (p + q * b) * T
      = (3 * (1 + 2 * a) + 2 * (1 + u) + (p + q * b)) * T := by ring
    _ ≤ (32 * Q) * T := mul_le_mul_of_nonneg_right this hT
    _ = 32 * q * s * (a * b) * T := by rw [hQ]; ring

lemma aux_TT2 {a b s u q T : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hs : 1 ≤ s) (hus : u ≤ s)
    (hq : 1 ≤ q) (hT : 0 ≤ T) : 4 * ((1 + u) * T) ≤ 32 * q * s * (a * b) * T := by
  have hQ1 := aux_one_le hq hs ha hb
  have hsQ : s ≤ q * s * (a * b) := by
    have : 1 ≤ q * (a * b) := one_le_mul_of_one_le_of_one_le hq (one_le_mul_of_one_le_of_one_le ha hb)
    calc s = s * 1 := (mul_one s).symm
      _ ≤ s * (q * (a * b)) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = q * s * (a * b) := by ring
  have : 4 * (1 + u) ≤ 32 * (q * s * (a * b)) := by linarith
  calc 4 * ((1 + u) * T) = (4 * (1 + u)) * T := by ring
    _ ≤ (32 * (q * s * (a * b))) * T := mul_le_mul_of_nonneg_right this hT
    _ = _ := by ring

/-- TT: `√M Y^{-1/2} B(2Y, C) ≤ 32·16^α √Ng X^{αη+η} Tg` for `Y₀ ≤ Y ≤ 2Y₁`. -/
lemma Ex_TT {M N L ε α η Ng Nf C Y : ℝ} (h : Rng M N L ε) (hα : 1 ≤ α) (hη : 0 < η)
    (hNf : 1 ≤ Nf) (hNfg : Nf ≤ Ng) (hC0 : 0 ≤ C) (hC : C ≤ 2 * N)
    (hY0 : min (4 * N ^ 2 / M * (M * N) ^ η / Nf) L ≤ Y)
    (hY1 : Y ≤ 2 * max (4 * N ^ 2 / M * (M * N) ^ η / Nf) L) :
    Real.sqrt M * Y ^ (-(1 / 2 : ℝ)) * Bf α (2 * Y) C ≤
      32 * 16 ^ α * Real.sqrt Ng * (M * N) ^ (α * η + η) * Tg M N L α := by
  have hM0 : 0 < M := by linarith [h.hM]
  have hN0 : 0 < N := by linarith [h.hN]
  have hL := h.Lpos
  have hX1 := h.X1
  set X := M * N with hXdef
  set T := Tg M N L α with hTdef
  set Y₀ := min (4 * N ^ 2 / M * X ^ η / Nf) L with hY₀
  set Y₁ := max (4 * N ^ 2 / M * X ^ η / Nf) L with hY₁
  have hT0 : 0 ≤ T := Tg_nonneg hM0.le hN0.le hL
  have hTN : N ≤ T := Tg_ge_N hM0.le hN0.le hL
  have hY₀p : 0 < Y₀ := lt_min (by positivity) hL
  have hYp : 0 < Y := lt_of_lt_of_le hY₀p hY0
  have hY₀₁ : Y₀ ≤ Y₁ := min_le_max
  have hY₁p : 0 < Y₁ := lt_of_lt_of_le hY₀p hY₀₁
  have t1 := Ex_T1 h hα hη hNf (Y₁ := Y₁) rfl
  have t2 := Ex_T2 h hη hNf (Y₀ := Y₀) (α := α) rfl
  have t3 := Ex_T3 h hα hη hNf (Y₁ := Y₁) rfl
  have hsNf : Real.sqrt Nf ≤ Real.sqrt Ng := Real.sqrt_le_sqrt hNfg
  have hsNg : 1 ≤ Real.sqrt Ng := Real.one_le_sqrt.2 (hNf.trans hNfg)
  have hXη : 1 ≤ X ^ η := Real.one_le_rpow hX1 hη.le
  have hXαη : 1 ≤ X ^ (α * η) := Real.one_le_rpow hX1 (by positivity)
  have hXE : X ^ η * X ^ (α * η) = X ^ (α * η + η) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have h16 : (1 : ℝ) ≤ 16 ^ α := Real.one_le_rpow (by norm_num) (by linarith)
  have h4 : (1 : ℝ) ≤ 4 ^ α := Real.one_le_rpow (by norm_num) (by linarith)
  have h416 : (4 : ℝ) ^ α * 4 ^ α = 16 ^ α := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  -- `√M Y^{-1/2} = √(M/Y) ≤ √(M/Y₀)`
  have hsq : Real.sqrt M * Y ^ (-(1 / 2 : ℝ)) = Real.sqrt (M / Y) := by
    rw [rpow_neg_half_eq hYp, Real.sqrt_div' M hYp.le, div_eq_mul_inv]
  have hsqY₀ : Real.sqrt (M / Y) ≤ Real.sqrt (M / Y₀) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hM0.le hY₀p hY0)
  have hS0 : 0 ≤ Real.sqrt (M / Y) := Real.sqrt_nonneg _
  have hC2 : 2 * √(M / Y₀) * N ≤ 2 * ((1 + Real.sqrt Nf) * T) := by linarith
  rw [hsq]
  unfold Bf
  rcases le_or_gt 1 (2 * Y) with h2Y | h2Y
  · rw [max_eq_left h2Y]
    -- piece (i): `√(M/Y) (2Y) = 2 √(MY) ≤ 2√2 √(M Y₁)`
    have pi : Real.sqrt (M / Y) * (2 * Y) ≤ 3 * ((1 + 2 * X ^ η) * T) := by
      have e : Real.sqrt (M / Y) * (2 * Y) = 2 * Real.sqrt (M * Y) := by
        have hY' : Real.sqrt (M * Y) = Real.sqrt (M / Y) * Y := by
          rw [show M * Y = (M / Y) * Y ^ 2 by field_simp, Real.sqrt_mul (by positivity),
            Real.sqrt_sq hYp.le]
        rw [hY']; ring
      rw [e]
      have h2 : Real.sqrt (M * Y) ≤ Real.sqrt 2 * Real.sqrt (M * Y₁) := by
        rw [← Real.sqrt_mul (by norm_num)]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have : 0 ≤ Real.sqrt (M * Y₁) := Real.sqrt_nonneg _
      nlinarith
    -- piece (ii)
    have pii : Real.sqrt (M / Y) * C ≤ 2 * ((1 + Real.sqrt Nf) * T) := by
      calc Real.sqrt (M / Y) * C ≤ Real.sqrt (M / Y₀) * (2 * N) :=
            mul_le_mul hsqY₀ hC hC0 (Real.sqrt_nonneg _)
        _ = 2 * (Real.sqrt (M / Y₀) * N) := by ring
        _ ≤ 2 * ((1 + Real.sqrt Nf) * T) := by linarith
    -- piece (iii)
    have piii : Real.sqrt (M / Y) * min (2 * Y) C ^ α ≤ 4 ^ α * ((1 + 4 ^ α * X ^ (α * η)) * T) := by
      have hm : min (2 * Y) C ^ α ≤ (2 * Y) ^ α :=
        Real.rpow_le_rpow (le_min (by linarith) hC0) (min_le_left _ _) (by linarith)
      have e : Real.sqrt (M / Y) * (2 * Y) ^ α = 2 ^ α * (Real.sqrt M * Y ^ (α - 1 / 2)) := by
        rw [← hsq, Real.mul_rpow (by norm_num) hYp.le]
        have : Y ^ (-(1 / 2 : ℝ)) * Y ^ α = Y ^ (α - 1 / 2) := by
          rw [← Real.rpow_add hYp]; ring_nf
        rw [← this]; ring
      have hY2 : Y ^ (α - 1 / 2) ≤ (2 * Y₁) ^ (α - 1 / 2) :=
        Real.rpow_le_rpow hYp.le hY1 (by linarith)
      have h2Y₁ : (2 * Y₁) ^ (α - 1 / 2) ≤ 2 ^ α * Y₁ ^ (α - 1 / 2) := by
        rw [Real.mul_rpow (by norm_num) hY₁p.le]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by linarith)) (by positivity)
      have h22 : (2 : ℝ) ^ α * 2 ^ α = 4 ^ α := by
        rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
      calc Real.sqrt (M / Y) * min (2 * Y) C ^ α ≤ Real.sqrt (M / Y) * (2 * Y) ^ α :=
            mul_le_mul_of_nonneg_left hm hS0
        _ = 2 ^ α * (Real.sqrt M * Y ^ (α - 1 / 2)) := e
        _ ≤ 2 ^ α * (Real.sqrt M * (2 ^ α * Y₁ ^ (α - 1 / 2))) := by
            gcongr; exact hY2.trans h2Y₁
        _ = 4 ^ α * (Real.sqrt M * Y₁ ^ (α - 1 / 2)) := by rw [← h22]; ring
        _ ≤ 4 ^ α * ((1 + 4 ^ α * X ^ (α * η)) * T) := by gcongr
    rw [mul_add, mul_add]
    have hsum : 3 * ((1 + 2 * X ^ η) * T) + 2 * ((1 + Real.sqrt Nf) * T) +
        4 ^ α * ((1 + 4 ^ α * X ^ (α * η)) * T) ≤
        32 * 16 ^ α * Real.sqrt Ng * X ^ (α * η + η) * T := by
      rw [← hXE]
      exact aux_TT hXη hXαη hsNg hsNf h4 h416 hT0
    linarith
  · rw [max_eq_right h2Y.le]
    have hm : min 1 C ^ α ≤ 1 := Real.rpow_le_one (le_min zero_le_one hC0) (min_le_left _ _)
      (by linarith)
    have hB4 : 1 + C + min 1 C ^ α ≤ 4 * N := by linarith [h.hN]
    calc Real.sqrt (M / Y) * (1 + C + min 1 C ^ α) ≤ Real.sqrt (M / Y₀) * (4 * N) :=
          mul_le_mul hsqY₀ hB4 (by positivity) (Real.sqrt_nonneg _)
      _ = 4 * (Real.sqrt (M / Y₀) * N) := by ring
      _ ≤ 4 * ((1 + Real.sqrt Nf) * T) := by linarith
      _ ≤ 32 * 16 ^ α * Real.sqrt Ng * X ^ (α * η + η) * T := by
          rw [← hXE]
          exact aux_TT2 hXη hXαη hsNg hsNf h16 hT0

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Ex2: more exponent bookkeeping (block count, the crude `DQ` factor)
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open Real

/-- The dyadic ratio: `max(a, L) ≤ 4 X² min(a, L)` for `a = L′/Nf`, `1 ≤ Nf ≤ 2N`. -/
lemma Ex_ratio {M N L ε η Nf : ℝ} (h : Rng M N L ε) (hη0 : 0 < η) (hη : η ≤ 1) (hNf : 1 ≤ Nf)
    (hNf2 : Nf ≤ 2 * N) :
    max (4 * N ^ 2 / M * (M * N) ^ η / Nf) L ≤
      4 * (M * N) ^ 2 * min (4 * N ^ 2 / M * (M * N) ^ η / Nf) L := by
  have hM0 : 0 < M := by linarith [h.hM]
  have hN0 : 0 < N := by linarith [h.hN]
  have hL := h.Lpos
  have hX1 := h.X1
  have hXη1 : 1 ≤ (M * N) ^ η := Real.one_le_rpow hX1 hη0.le
  have hXηX : (M * N) ^ η ≤ M * N := by
    calc (M * N) ^ η ≤ (M * N) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 hη
      _ = M * N := Real.rpow_one _
  have hX2 : M * N ≤ (M * N) ^ 2 := by nlinarith
  set a := 4 * N ^ 2 / M * (M * N) ^ η / Nf with ha
  rcases le_total a L with h1 | h1
  · rw [max_eq_right h1, min_eq_left h1]
    -- a ≥ 2N/M
    have ha2 : 2 * N / M ≤ a := by
      rw [ha, le_div_iff₀ (by linarith), div_mul_eq_mul_div, div_le_iff₀ hM0]
      have : 4 * N ^ 2 / M * (M * N) ^ η * M = 4 * N ^ 2 * (M * N) ^ η := by
        field_simp
      rw [this]
      nlinarith
    have hLM := h.L_le_M
    have : M ≤ 4 * (M * N) ^ 2 * (2 * N / M) := by
      have e : 4 * (M * N) ^ 2 * (2 * N / M) = 8 * M * N ^ 3 := by field_simp; ring
      rw [e]
      have : 1 ≤ N ^ 3 := one_le_pow₀ h.hN
      nlinarith
    calc L ≤ M := hLM
      _ ≤ 4 * (M * N) ^ 2 * (2 * N / M) := this
      _ ≤ 4 * (M * N) ^ 2 * a := by gcongr
  · rw [max_eq_left h1, min_eq_right h1]
    have hLg := h.L_ge
    calc a ≤ 4 * N ^ 2 / M * (M * N) ^ η := div_le_self (by positivity) hNf
      _ = 4 * (M * N) ^ η * (N ^ 2 / M) := by ring
      _ ≤ 4 * (M * N) ^ 2 * L := by
          gcongr
          linarith

/-- The block count. -/
lemma Ex_NB {M N L ε η Nf δ : ℝ} (h : Rng M N L ε) (hη0 : 0 < η) (hη : η ≤ 1) (hNf : 1 ≤ Nf)
    (hNf2 : Nf ≤ 2 * N) (hδ : 0 < δ) :
    (nblk (min (4 * N ^ 2 / M * (M * N) ^ η / Nf) L)
        (max (4 * N ^ 2 / M * (M * N) ^ η / Nf) L) : ℝ) ≤
      (10 * (M * N) ^ 2) ^ δ / (δ * Real.log 2) := by
  have hM0 : 0 < M := by linarith [h.hM]
  have hN0 : 0 < N := by linarith [h.hN]
  have hL := h.Lpos
  have hX1 := h.X1
  set a := 4 * N ^ 2 / M * (M * N) ^ η / Nf with ha
  have ha0 : 0 < a := by rw [ha]; have : 0 < Nf := by linarith
                         positivity
  have hY0 : 0 < min a L := lt_min ha0 hL
  refine (nblk_le hδ hY0 (min_le_max)).trans ?_
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine Real.rpow_le_rpow (by positivity) ?_ hδ.le
  have hr := Ex_ratio h hη0 hη hNf hNf2
  rw [← ha] at hr
  have : max a L / min a L ≤ 4 * (M * N) ^ 2 := by
    rw [div_le_iff₀ hY0]; exact hr
  have hX2 : 1 ≤ (M * N) ^ 2 := one_le_pow₀ hX1
  linarith

/-- The crude `DQ` factor. -/
lemma Ex_DQ {M N L ε η Ng σ : ℝ} (h : Rng M N L ε) (hη0 : 0 < η) (hσ : 1 ≤ σ) (hNg : 1 ≤ Ng)
    (hNg2 : Ng ≤ 2 * N) :
    M ^ (-σ) * Ng ^ σ * (max (2 * N / Ng) 1) ^ (1 + 2 * σ) *
        (4 * N ^ 2 / M * (M * N) ^ η) ^ (-(σ - 1 / 2)) * (2 * N) ≤
      8 * (M * N) ^ (3 - η * (σ - 1 / 2)) := by
  have hM0 : 0 < M := by linarith [h.hM]
  have hN0 : 0 < N := by linarith [h.hN]
  have hNg0 : 0 < Ng := by linarith
  have hX1 := h.X1
  have hX0 : 0 < M * N := by linarith
  have hu1 : 1 ≤ 2 * N / Ng := by rw [le_div_iff₀ hNg0]; linarith
  rw [max_eq_left hu1]
  set u := 2 * N with hu
  have hu0 : 0 < u := by rw [hu]; linarith
  set p := σ - 1 / 2 with hp
  -- Ng^σ (u/Ng)^{1+2σ} ≤ u^{1+2σ}
  have h1 : Ng ^ σ * (u / Ng) ^ (1 + 2 * σ) ≤ u ^ (1 + 2 * σ) := by
    rw [Real.div_rpow hu0.le hNg0.le, mul_div_assoc', div_le_iff₀ (by positivity), mul_comm]
    gcongr <;> first | exact hNg | linarith
  -- L′ = u² X^η / M
  have hL' : 4 * N ^ 2 / M * (M * N) ^ η = u ^ (2 : ℝ) * (M * N) ^ η / M := by
    rw [hu, Real.rpow_two]; ring
  have hL'p : (4 * N ^ 2 / M * (M * N) ^ η) ^ (-p) =
      u ^ (-(2 * p)) * (M * N) ^ (-(η * p)) * M ^ p := by
    rw [hL', Real.div_rpow (by positivity) hM0.le, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hu0.le, ← Real.rpow_mul hX0.le, Real.rpow_neg hM0.le, div_inv_eq_mul]
    congr 2 <;> ring_nf
  have hpos : 0 ≤ (4 * N ^ 2 / M * (M * N) ^ η) ^ (-p) := by positivity
  calc M ^ (-σ) * Ng ^ σ * (u / Ng) ^ (1 + 2 * σ) * (4 * N ^ 2 / M * (M * N) ^ η) ^ (-p) * u
      = M ^ (-σ) * (Ng ^ σ * (u / Ng) ^ (1 + 2 * σ)) *
          (4 * N ^ 2 / M * (M * N) ^ η) ^ (-p) * u := by ring
    _ ≤ M ^ (-σ) * u ^ (1 + 2 * σ) * (4 * N ^ 2 / M * (M * N) ^ η) ^ (-p) * u := by
        gcongr
    _ = (M ^ (-σ) * M ^ p) * (u ^ (1 + 2 * σ) * u ^ (-(2 * p)) * u) * (M * N) ^ (-(η * p)) := by
        rw [hL'p]; ring
    _ = M ^ (-(1 / 2 : ℝ)) * u ^ (3 : ℝ) * (M * N) ^ (-(η * p)) := by
        rw [← Real.rpow_add hM0, ← Real.rpow_add hu0,
          show 1 + 2 * σ + -(2 * p) = (2 : ℝ) by rw [hp]; ring,
          show -σ + p = -(1 / 2 : ℝ) by rw [hp]; ring,
          show (3 : ℝ) = 2 + 1 by norm_num, Real.rpow_add hu0, Real.rpow_one]
    _ ≤ 1 * (8 * (M * N) ^ (3 : ℝ)) * (M * N) ^ (-(η * p)) := by
        gcongr
        · exact Real.rpow_le_one_of_one_le_of_nonpos h.hM (by norm_num)
        · rw [hu, Real.mul_rpow (by norm_num) hN0.le]
          rw [show (2 : ℝ) ^ (3 : ℝ) = 8 by norm_num]
          gcongr
          nlinarith [h.hM]
    _ = 8 * (M * N) ^ (3 - η * p) := by
        rw [one_mul, mul_assoc, ← Real.rpow_add hX0]; ring_nf

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Cut: the cut's output as `LamHyp`, and small counting facts for the assembly
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

/-- The cut's `Λ` for the pair `(c₁, c₂)` satisfies `LamHyp`. -/
theorem lamHyp_of_cut {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪)
    {c₁ c₂ : Ideal (𝓞 F)} {Λ : ℂ → ℂ} (hd : Differentiable ℂ Λ)
    (hdir : ∀ w : ℂ, 1 < w.re →
      Λ w = (∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors 𝔪).toFinset,
          (1 - (Ideal.absNorm P : ℂ) ^ (-w)))⁻¹ *
        ∑' 𝔞 : {𝔞 : Ideal (𝓞 F) // IsExterior 𝔪 𝔞},
          residueSymbol ι 𝔪 𝔞.1 (g.gen c₁) ^ 3 * residueSymbol ι 𝔪 𝔞.1 (g.gen c₂) ^ 3 *
            (Ideal.absNorm 𝔞.1 : ℂ) ^ (-w))
    (hfe : ∀ w : ℂ, (∀ m : ℕ, w ≠ -(m : ℂ)) → (∀ m : ℕ, 1 - w ≠ -(m : ℂ)) →
      (((|discr F| : ℤ) : ℂ) * (Ideal.absNorm (c₁ * c₂) : ℂ)) ^ (w / 2) *
          Complex.Gammaℂ w ^ InfinitePlace.nrComplexPlaces F * Λ w =
        (((|discr F| : ℤ) : ℂ) * (Ideal.absNorm (c₁ * c₂) : ℂ)) ^ ((1 - w) / 2) *
          Complex.Gammaℂ (1 - w) ^ InfinitePlace.nrComplexPlaces F * Λ (1 - w))
    (hgr : ∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ →
      ‖Λ w‖ ≤ C * (1 + |w.im|) ^ A) :
    LamHyp 𝔪 (c₁ * c₂) (psiP g c₁ c₂) Λ where
  diff := hd
  dir w hw := by
    rw [hdir w hw]
    have hP : (UniqueFactorizationMonoid.normalizedFactors 𝔪).toFinset = primesOf 𝔪 := by
      ext P; rw [Multiset.mem_toFinset, mem_primesOf]
    rw [hP]
    congr 1
    have hw0 : -w ≠ 0 := by
      intro h; have : w = 0 := by linear_combination -h
      rw [this] at hw; simp at hw; linarith
    have hs : Function.support (fun a : Ideal (𝓞 F) => psiP g c₁ c₂ a *
        (Ideal.absNorm a : ℂ) ^ (-w)) ⊆ {a | IsExterior 𝔪 a} := by
      intro a ha
      by_contra hne
      apply ha
      simp only [Set.mem_setOf_eq, IsExterior, not_and_or] at hne
      rcases hne with h0 | h1
      · push Not at h0
        simp [h0, Complex.zero_cpow hw0]
      · by_cases ha0 : a = ⊥
        · simp [ha0, Complex.zero_cpow hw0]
        · simp only [psiP_apply, L3H.chiK, rs_nonext h𝔪 ha0 h1]; ring
    exact tsum_subtype_eq_of_support_subset hs
  fe w h1 h2 := hfe w h1 h2
  growth := hgr

/-- `σ₁ = m + 3/2` is never an integer. -/
lemma sigma_nonint (m : ℕ) : ∀ k : ℕ, (m : ℝ) + 3 / 2 ≠ k := by
  intro k hk
  have h : (2 * k : ℝ) = (2 * m + 3 : ℕ) := by push_cast; linarith
  have h' : 2 * k = 2 * m + 3 := by exact_mod_cast h
  omega

lemma two_pow_card_le_absNorm {𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) :
    (2 : ℝ) ^ (primesOf 𝔤).card ≤ Ideal.absNorm 𝔤 := by
  calc (2 : ℝ) ^ (primesOf 𝔤).card = ∏ _P ∈ primesOf 𝔤, (2 : ℝ) := by
        rw [Finset.prod_const]
    _ ≤ ∏ P ∈ primesOf 𝔤, (Ideal.absNorm P : ℝ) :=
        Finset.prod_le_prod (fun _ _ => by norm_num)
          (fun P hP => by exact_mod_cast two_le_absNorm_of_mem_primesOf hP)
    _ ≤ Ideal.absNorm 𝔤 := absNorm_pideal_primesOf_le h𝔤

lemma four_pow_card_le_absNorm {𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) :
    (4 : ℝ) ^ (primesOf 𝔤).card ≤ (Ideal.absNorm 𝔤 : ℝ) ^ 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
  exact pow_le_pow_left₀ (by positivity) (two_pow_card_le_absNorm h𝔤) 2

lemma two_pow_card_mul_le {𝔤 𝔪 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) (h𝔪 : 𝔪 ≠ ⊥) :
    (2 : ℝ) ^ (primesOf (𝔤 * 𝔪)).card ≤ 2 ^ (primesOf 𝔪).card * Ideal.absNorm 𝔤 := by
  classical
  rw [primesOf_mul h𝔤 h𝔪]
  calc (2 : ℝ) ^ (primesOf 𝔤 ∪ primesOf 𝔪).card
      ≤ 2 ^ ((primesOf 𝔤).card + (primesOf 𝔪).card) :=
        pow_le_pow_right₀ (by norm_num) (Finset.card_union_le _ _)
    _ = 2 ^ (primesOf 𝔪).card * 2 ^ (primesOf 𝔤).card := by rw [pow_add, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (two_pow_card_le_absNorm h𝔤) (by positivity)

lemma absNorm_pideal_le {𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) {f : Finset (Ideal (𝓞 F))}
    (hf : f ⊆ primesOf 𝔤) :
    1 ≤ (Ideal.absNorm (pideal f) : ℝ) ∧ (Ideal.absNorm (pideal f) : ℝ) ≤ Ideal.absNorm 𝔤 := by
  have he : (Ideal.absNorm (pideal f) : ℝ) = ∏ P ∈ f, (Ideal.absNorm P : ℝ) := by
    rw [pideal, map_prod, Nat.cast_prod]
  have h1 : ∀ P ∈ primesOf 𝔤, (1 : ℝ) ≤ Ideal.absNorm P := fun P hP => by
    exact_mod_cast one_le_absNorm_of_mem_primesOf hP
  have one_le : ∀ s ⊆ primesOf 𝔤, (1 : ℝ) ≤ ∏ P ∈ s, (Ideal.absNorm P : ℝ) := by
    intro s hs
    calc (1 : ℝ) = ∏ _P ∈ s, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun P hP => h1 P (hs hP))
  rw [he]
  refine ⟨one_le f hf, ?_⟩
  classical
  calc ∏ P ∈ f, (Ideal.absNorm P : ℝ)
      ≤ (∏ P ∈ primesOf 𝔤 \ f, (Ideal.absNorm P : ℝ)) * ∏ P ∈ f, (Ideal.absNorm P : ℝ) :=
        le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) (one_le _ Finset.sdiff_subset)
    _ = ∏ P ∈ primesOf 𝔤, (Ideal.absNorm P : ℝ) := Finset.prod_sdiff hf
    _ ≤ _ := absNorm_pideal_primesOf_le h𝔤

/-- `Zτ ≤ Kτ³ Y^δ ∑ |z|²` from `2^ω ≤ Kτ N^{δ/3}`. -/
lemma Ztau_le {𝔪 : Ideal (𝓞 F)} {C : Finset (Ideal (𝓞 F))} {Y Kτ δ : ℝ} (hδ : 0 ≤ δ)
    (hKτ : 0 < Kτ) (hC : ∀ c ∈ C, c ∈ L3H.rowsF 𝔪 0 Y)
    (hK : ∀ n : Ideal (𝓞 F), n ≠ ⊥ → Squarefree n →
      (2 : ℝ) ^ (L3H.pf n).card ≤ Kτ * (Ideal.absNorm n : ℝ) ^ (δ / 3))
    (z : Ideal (𝓞 F) → ℂ) :
    Ztau C z ≤ Kτ ^ 3 * Y ^ δ * ∑ c ∈ C, ‖z c‖ ^ 2 := by
  rw [Ztau_def]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c hc => ?_
  obtain ⟨hce, hcs, hcY⟩ := L3H.mem_rowsF_zero.1 (hC c hc)
  have h2 := hK c hce.1 hcs
  have h8 : (8 : ℝ) ^ (L3H.pf c).card = ((2 : ℝ) ^ (L3H.pf c).card) ^ 3 := by
    rw [← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, mul_comm]
  have hN0 : (0 : ℝ) ≤ Ideal.absNorm c := by positivity
  have h3 : (Kτ * (Ideal.absNorm c : ℝ) ^ (δ / 3)) ^ 3 = Kτ ^ 3 * (Ideal.absNorm c : ℝ) ^ δ := by
    rw [mul_pow, ← Real.rpow_natCast ((Ideal.absNorm c : ℝ) ^ (δ / 3)), ← Real.rpow_mul hN0]
    norm_num
  rw [h8]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc ((2 : ℝ) ^ (L3H.pf c).card) ^ 3 ≤ (Kτ * (Ideal.absNorm c : ℝ) ^ (δ / 3)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) h2 3
    _ = Kτ ^ 3 * (Ideal.absNorm c : ℝ) ^ δ := h3
    _ ≤ Kτ ^ 3 * Y ^ δ := by gcongr

lemma sum_image_le {𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) (C Cs : Finset (Ideal (𝓞 F)))
    (hC : ∀ c ∈ C, 𝔤 * c ∈ Cs) (lam : Ideal (𝓞 F) → ℂ) :
    ∑ c ∈ C, ‖lam (𝔤 * c)‖ ^ 2 ≤ ∑ b ∈ Cs, ‖lam b‖ ^ 2 := by
  classical
  have hinj : Set.InjOn (fun c => 𝔤 * c) (C : Set (Ideal (𝓞 F))) :=
    fun x _ y _ hxy => mul_left_cancel₀ (show 𝔤 ≠ 0 from h𝔤) hxy
  rw [← Finset.sum_image (f := fun b => ‖lam b‖ ^ 2) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro b hb
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hb
  exact hC c hc

lemma norm_row_le {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (Rw : Finset (Ideal (𝓞 F))) (M : ℝ) (b₁ b₂ : Ideal (𝓞 F)) :
    ‖∑ a ∈ Rw, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) * L3H.chiK ι 𝔪 g a b₁ *
        starRingEnd ℂ (L3H.chiK ι 𝔪 g a b₂)‖ ≤ Rw.card := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a ∈ Rw, ‖((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) * L3H.chiK ι 𝔪 g a b₁ *
        starRingEnd ℂ (L3H.chiK ι 𝔪 g a b₂)‖ ≤ ∑ _a ∈ Rw, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (W_nonneg _)]
        have h1 := W_le_one ((Ideal.absNorm a : ℝ) / M)
        have h2 := norm_chiK_le g a b₁
        have h3 := norm_chiK_le g a b₂
        calc W ((Ideal.absNorm a : ℝ) / M) * ‖L3H.chiK ι 𝔪 g a b₁‖ * ‖L3H.chiK ι 𝔪 g a b₂‖
            ≤ 1 * 1 * 1 := by gcongr
          _ = 1 := by norm_num
    _ = Rw.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Dec: `S3 = PSnp(T − T′) + PSnp(DP) + PSnp(DQ) − PSnp(RP) + (principal pair)`
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

open Classical in
theorem S3_decomp {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪)
    (h𝔪 : 𝔪 ≠ ⊥) (h𝔪t : 𝔪 ≠ ⊤) {k : ℕ} (cls : Ideal (𝓞 F) → Fin k)
    (hcut : ∀ 𝔤 c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 (𝔤 * c₁ * c₂) → Squarefree (𝔤 * c₁ * c₂) →
      c₁ * c₂ ≠ ⊤ → cls (𝔤 * c₁) = cls (𝔤 * c₂) →
        ∃ Λ : ℂ → ℂ, LamHyp 𝔪 (c₁ * c₂) (psiP g c₁ c₂) Λ)
    {𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) (h𝔤e : IsExterior 𝔪 𝔤) (N : ℝ) (j : Fin k)
    {M : ℝ} (hM : 0 < M) (L L' : ℝ) {ε ε' σ₁ : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hε' : 0 < ε') (hε'2 : ε' < 1 / 2) (hσ₁ : 0 < σ₁) (hσint : ∀ m : ℕ, σ₁ ≠ m)
    (lam : Ideal (𝓞 F) → ℂ) :
    L3H.S3 (L3H.chiK ι 𝔪 g) (L3H.RwF 𝔪 L M) (fun 𝔞 => W ((Ideal.absNorm 𝔞 : ℝ) / M))
        (· ⊔ ·) ((L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)) 𝔤 lam =
      PSnp ((L3H.rowsF 𝔪 0 (2 * N / Ideal.absNorm 𝔤)).filter
          (fun c => 𝔤 * c ∈ (L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)))
          (fun c => lam (𝔤 * c)) (fun c₁ c₂ => TTt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L L') +
        PSnp ((L3H.rowsF 𝔪 0 (2 * N / Ideal.absNorm 𝔤)).filter
          (fun c => 𝔤 * c ∈ (L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)))
          (fun c => lam (𝔤 * c)) (fun c₁ c₂ => DPt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L' ε') +
        PSnp ((L3H.rowsF 𝔪 0 (2 * N / Ideal.absNorm 𝔤)).filter
          (fun c => 𝔤 * c ∈ (L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)))
          (fun c => lam (𝔤 * c)) (fun c₁ c₂ => DQt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L' σ₁) -
        PSnp ((L3H.rowsF 𝔪 0 (2 * N / Ideal.absNorm 𝔤)).filter
          (fun c => 𝔤 * c ∈ (L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)))
          (fun c => lam (𝔤 * c)) (fun c₁ c₂ => RPt 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) M L ε) +
        ∑ c₁ ∈ (L3H.rowsF 𝔪 0 (2 * N / Ideal.absNorm 𝔤)).filter
          (fun c => 𝔤 * c ∈ (L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)),
        ∑ c₂ ∈ (L3H.rowsF 𝔪 0 (2 * N / Ideal.absNorm 𝔤)).filter
          (fun c => 𝔤 * c ∈ (L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)),
          (if c₁ = ⊤ ∧ c₂ = ⊤ then lam (𝔤 * c₁) * starRingEnd ℂ (lam (𝔤 * c₂)) *
            ∑ a ∈ L3H.RwF 𝔪 L M, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) *
              L3H.chiK ι 𝔪 g a (𝔤 * c₁) * starRingEnd ℂ (L3H.chiK ι 𝔪 g a (𝔤 * c₂))
          else 0) := by
  set Cs := (L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j) with hCs
  set C'' := L3H.rowsF 𝔪 0 (2 * N / Ideal.absNorm 𝔤) with hC''
  have hNg : (0 : ℝ) < Ideal.absNorm 𝔤 := absNorm_pos h𝔤
  have hmemCs : ∀ b ∈ Cs, IsExterior 𝔪 b ∧ Squarefree b ∧ N < (Ideal.absNorm b : ℝ) ∧
      (Ideal.absNorm b : ℝ) ≤ 2 * N ∧ cls b = j := by
    intro b hb
    rw [hCs, Finset.mem_filter, L3H.mem_rowsF] at hb
    exact ⟨hb.1.1, hb.1.2.1, hb.1.2.2.1, hb.1.2.2.2, hb.2⟩
  have hsub : ∀ b ∈ Cs, ∀ c, b = 𝔤 * c → c ∈ C'' := by
    intro b hb c hbc
    obtain ⟨hbe, hbs, -, hb2, -⟩ := hmemCs b hb
    rw [hbc] at hbe hbs hb2
    rw [hC'', L3H.mem_rowsF_zero]
    refine ⟨ext_right hbe, hbs.of_mul_right, ?_⟩
    rw [map_mul, Nat.cast_mul] at hb2
    rw [le_div_iff₀ hNg]; linarith
  rw [S3_reindex _ _ _ h𝔤 Cs C'' hsub lam, split_principal]
  congr 1
  refine PSnp_decomp _ _ _ _ _ _ _ fun c₁ hc₁ c₂ hc₂ hcop hnp => ?_
  have h1 := hmemCs _ (Finset.mem_filter.1 hc₁).2
  have h2 := hmemCs _ (Finset.mem_filter.1 hc₂).2
  have hc₁e : IsExterior 𝔪 c₁ := ext_right h1.1
  have hc₂e : IsExterior 𝔪 c₂ := ext_right h2.1
  have hg1 : 𝔤 ⊔ c₁ = ⊤ := sup_eq_top_of_sqf h1.2.1
  have hg2 : 𝔤 ⊔ c₂ = ⊤ := sup_eq_top_of_sqf h2.2.1
  have hgc : 𝔤 ⊔ c₁ * c₂ = ⊤ := by
    rw [sup_comm, sup_mul_eq_top_iff, sup_comm, sup_comm c₂]; exact ⟨hg1, hg2⟩
  have hext : IsExterior 𝔪 (𝔤 * c₁ * c₂) := ext_mul h1.1 hc₂e
  have hsq : Squarefree (𝔤 * c₁ * c₂) := by
    refine sqf_mul_of_sup h1.2.1 h2.2.1.of_mul_right ?_
    rw [sup_mul_eq_top_iff]; exact ⟨hg2, hcop⟩
  obtain ⟨Λ, hΛ⟩ := hcut 𝔤 c₁ c₂ hext hsq (mul_ne_top_of hnp) (by rw [h1.2.2.2.2, h2.2.2.2.2])
  show ∑ a ∈ L3H.RwF 𝔪 L M, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) *
      L3H.chiK ι 𝔪 g a (𝔤 * c₁) * starRingEnd ℂ (L3H.chiK ι 𝔪 g a (𝔤 * c₂)) = _
  rw [row_eq_pair hχ g h𝔪 h𝔤e hc₁e hc₂e hM L]
  rw [← tsum_indicator_W_mul_eq_TTt_add_DPt_add_DQt_sub_RPt F 𝔪 𝔤 (c₁ * c₂) (psiP g c₁ c₂) Λ
    (psiHyp_pair hχ g h𝔪 hc₁e hc₂e) hΛ h𝔤 h𝔪 h𝔪t (ext_mul hc₁e hc₂e).1 h𝔤e.2 hgc M hM L L' ε ε'
    σ₁ hε hε2 hε' hε'2 hσ₁ hσint]
  refine tsum_congr fun a => ?_
  by_cases hh : a ⊔ 𝔤 = ⊤ ∧ sgt L a
  · rw [Set.indicator_of_mem (show a ∈ {a | a ⊔ 𝔤 = ⊤ ∧ sgt L a} from hh), if_pos hh]
  · rw [Set.indicator_of_notMem (show a ∉ {a | a ⊔ 𝔤 = ⊤ ∧ sgt L a} from hh), if_neg hh]

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Fin: each piece is `≤ K N𝔤⁴ X^{9δ} Tg Z` (pure real arithmetic)

`X = MN`, `δ = εr = ε′`, `η ≤ δ`, `αη ≤ δ`, `C′ = max (2N/N𝔤) 1`.
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open Real

/-- `y^δ ≤ c X^{kδ}` from `y ≤ c X^k`, `1 ≤ c`, `0 ≤ δ ≤ 1`. -/
lemma rpow_le_cX {y c X δ : ℝ} (k : ℕ) (hy : 0 ≤ y) (hyc : y ≤ c * X ^ k) (hc : 1 ≤ c)
    (hX : 0 ≤ X) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : y ^ δ ≤ c * X ^ ((k : ℝ) * δ) := by
  calc y ^ δ ≤ (c * X ^ k) ^ δ := Real.rpow_le_rpow hy hyc hδ0
    _ = c ^ δ * X ^ ((k : ℝ) * δ) := by
        rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hX]
    _ ≤ c * X ^ ((k : ℝ) * δ) := by
        gcongr
        calc c ^ δ ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc hδ1
          _ = c := Real.rpow_one c

lemma Xpow_mono {X a b : ℝ} (hX : 1 ≤ X) (hab : a ≤ b) : X ^ a ≤ X ^ b :=
  Real.rpow_le_rpow_of_exponent_le hX hab

/-- Common facts in the range. -/
structure Ctx (M N L ε α δ Ng : ℝ) : Prop where
  h : Rng M N L ε
  hα : 1 ≤ α
  hδ0 : 0 < δ
  hδ1 : δ ≤ 1 / 4
  hNg : 1 ≤ Ng
  hNg2 : Ng ≤ 2 * N

namespace Ctx

variable {M N L ε α δ Ng : ℝ} (c : Ctx M N L ε α δ Ng)
include c

lemma X1 : 1 ≤ M * N := c.h.X1
lemma M1 : 1 ≤ M := c.h.hM
lemma N1 : 1 ≤ N := c.h.hN
lemma NX : N ≤ M * N := by nlinarith [c.M1, c.N1]
lemma MX : M ≤ M * N := by nlinarith [c.M1, c.N1]
lemma T0 : 0 ≤ Tg M N L α := Tg_nonneg (by linarith [c.M1]) (by linarith [c.N1]) c.h.Lpos
lemma T1 : 1 ≤ Tg M N L α := le_trans c.M1 (Tg_ge_M (by linarith [c.M1]) (by linarith [c.N1]) c.h.Lpos)
lemma Cm1 : 1 ≤ max (2 * N / Ng) 1 := le_max_right _ _
lemma Cm2 : max (2 * N / Ng) 1 ≤ 2 * N := by
  have hNg0 : 0 < Ng := by linarith [c.hNg]
  refine max_le ?_ (by linarith [c.N1])
  rw [div_le_iff₀ hNg0]; nlinarith [c.hNg, c.N1]
lemma Cm2X : max (2 * N / Ng) 1 ≤ 2 * (M * N) := le_trans c.Cm2 (by linarith [c.NX])

lemma twoN_pow : (2 * N) ^ δ ≤ 2 * (M * N) ^ δ := by
  have := rpow_le_cX 1 (by linarith [c.N1]) (show 2 * N ≤ 2 * (M * N) ^ 1 by
    rw [pow_one]; linarith [c.NX]) (by norm_num) (by linarith [c.X1]) c.hδ0.le
    (by linarith [c.hδ1])
  simpa using this

lemma Lp_le {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    4 * N ^ 2 / M * (M * N) ^ η ≤ 4 * (M * N) ^ 3 := by
  have hM0 : 0 < M := by linarith [c.M1]
  have hXη : (M * N) ^ η ≤ M * N := by
    calc (M * N) ^ η ≤ (M * N) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le c.X1 hη1
      _ = M * N := Real.rpow_one _
  have hN0 : 0 < N := by linarith [c.N1]
  have hX0 : 0 < M * N := by positivity
  have hN2 : N ^ 2 / M ≤ (M * N) ^ 2 := by
    rw [div_le_iff₀ hM0]
    have h3 : N ^ 2 ≤ M ^ 3 * N ^ 2 := le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ c.M1)
    calc N ^ 2 ≤ M ^ 3 * N ^ 2 := h3
      _ = (M * N) ^ 2 * M := by ring
  have h0 : 0 ≤ N ^ 2 / M := by positivity
  have hXη0 : 0 ≤ (M * N) ^ η := by positivity
  calc 4 * N ^ 2 / M * (M * N) ^ η = 4 * (N ^ 2 / M) * (M * N) ^ η := by ring
    _ ≤ 4 * (M * N) ^ 2 * (M * N) := by gcongr
    _ = 4 * (M * N) ^ 3 := by ring

end Ctx

/-- RP. -/
lemma fin_RP {M N L ε α δ Ng Z Zτ P w wm KR KE Kt : ℝ} (c : Ctx M N L ε α δ Ng)
    (hKR : 0 ≤ KR) (hKE : 0 ≤ KE) (hKt : 0 ≤ Kt) (hZ : 0 ≤ Z) (hwm : 0 ≤ wm) (hw0 : 0 ≤ w)
    (hw : w ≤ wm * Ng) (hZτ0 : 0 ≤ Zτ) (hZτ : Zτ ≤ Kt * (2 * N) ^ δ * Z)
    (hP : P ≤ KR * M ^ δ * w * betaE KE α δ L (max (2 * N / Ng) 1) * Zτ) :
    P ≤ (16 * KR * KE * Kt * wm) * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) := by
  have hM0 : 0 < M := by linarith [c.M1]
  have hN0 : 0 < N := by linarith [c.N1]
  have hX0 : 0 < M * N := by linarith [c.X1]
  have hT := c.T0
  have hNg0 : 0 < Ng := by linarith [c.hNg]
  set C' := max (2 * N / Ng) 1 with hC'
  have hβ : betaE KE α δ L C' ≤ KE * (4 * Tg M N L α) * (2 * (M * N) ^ (2 * δ)) := by
    unfold betaE
    have h1 : min (max L 1 + C' ^ α) (C' + max L 1 ^ α) ≤ 4 * Tg M N L α :=
      (min_le_Bf (by linarith [c.hα]) (by linarith [c.Cm1])).trans
        (Ex_RP c.h c.hα (by linarith [c.Cm1]) c.Cm2)
    have h2 : (C' * max L 1) ^ δ ≤ 2 * (M * N) ^ (2 * δ) := by
      have hm : max L 1 ≤ M * N := max_le (le_trans c.h.L_le_M c.MX) c.X1
      have := rpow_le_cX 2 (by have := c.Cm1; positivity)
        (show C' * max L 1 ≤ 2 * (M * N) ^ 2 by
          calc C' * max L 1 ≤ (2 * (M * N)) * (M * N) :=
                mul_le_mul c.Cm2X hm (by positivity) (by positivity)
            _ = 2 * (M * N) ^ 2 := by ring) (by norm_num) hX0.le c.hδ0.le
        (by linarith [c.hδ1])
      simpa using this
    have h0 : 0 ≤ min (max L 1 + C' ^ α) (C' + max L 1 ^ α) := by
      have := c.Cm1
      exact le_min (by positivity) (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hKE) h2 (by positivity) (by positivity)
  have hMδ : M ^ δ ≤ (M * N) ^ δ := Real.rpow_le_rpow hM0.le c.MX c.hδ0.le
  have hZτ' : Zτ ≤ Kt * (2 * (M * N) ^ δ) * Z := hZτ.trans (by gcongr; exact c.twoN_pow)
  have hβ0 : 0 ≤ betaE KE α δ L C' := betaE_nonneg hKE c.Cm1
  calc P ≤ KR * M ^ δ * w * betaE KE α δ L C' * Zτ := hP
    _ ≤ KR * (M * N) ^ δ * (wm * Ng) * (KE * (4 * Tg M N L α) * (2 * (M * N) ^ (2 * δ))) *
          (Kt * (2 * (M * N) ^ δ) * Z) := by gcongr
    _ = (16 * KR * KE * Kt * wm) * (Ng * ((M * N) ^ δ * (M * N) ^ (2 * δ) * (M * N) ^ δ) *
          Tg M N L α * Z) := by ring
    _ ≤ (16 * KR * KE * Kt * wm) * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) := by
        rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
        gcongr
        · calc Ng = Ng ^ 1 := (pow_one _).symm
            _ ≤ Ng ^ 4 := pow_le_pow_right₀ c.hNg (by norm_num)
        · exact c.X1
        · linarith [c.hδ0]

/-- DP. -/
lemma fin_DP {M N L ε α δ η Ng Z Zτ P w KD KE Kt : ℝ} (c : Ctx M N L ε α δ Ng)
    (hη0 : 0 < η) (hηδ : η ≤ δ) (hαη : α * η ≤ δ)
    (hKD : 0 ≤ KD) (hKE : 0 ≤ KE) (hKt : 0 ≤ Kt) (hZ : 0 ≤ Z) (hw0 : 0 ≤ w)
    (hw : w ≤ Ng) (hZτ0 : 0 ≤ Zτ) (hZτ : Zτ ≤ Kt * (2 * N) ^ δ * Z)
    (hP : P ≤ KD * M ^ (1 - δ) * w *
      betaE KE α δ (4 * N ^ 2 / M * (M * N) ^ η) (max (2 * N / Ng) 1) *
        (N / Ng) ^ (-(1 - 2 * δ)) * Zτ) :
    P ≤ (16 * KD * KE * Kt * (8 + 4 ^ α)) * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) := by
  have hM0 : 0 < M := by linarith [c.M1]
  have hN0 : 0 < N := by linarith [c.N1]
  have hNg0 : 0 < Ng := by linarith [c.hNg]
  have hX0 : 0 < M * N := by linarith [c.X1]
  have hT := c.T0
  have hη1 : η ≤ 1 := by linarith [c.hδ1]
  set C' := max (2 * N / Ng) 1 with hC'
  set L' := 4 * N ^ 2 / M * (M * N) ^ η with hL'
  have hL'0 : 0 ≤ L' := by positivity
  have hB := Ex_DP c.h c.hα hη0 c.hδ0 c.hδ1 c.hNg (by linarith [c.Cm1]) c.Cm2
  rw [← hL'] at hB
  have hmin : min (max L' 1 + C' ^ α) (C' + max L' 1 ^ α) ≤ Bf α L' C' :=
    min_le_Bf (by linarith [c.hα]) (by linarith [c.Cm1])
  have h0 : 0 ≤ min (max L' 1 + C' ^ α) (C' + max L' 1 ^ α) := by
    have := c.Cm1
    exact le_min (by positivity) (by positivity)
  have h2 : (C' * max L' 1) ^ δ ≤ 8 * (M * N) ^ (4 * δ) := by
    have hm : max L' 1 ≤ 4 * (M * N) ^ 3 :=
      max_le (c.Lp_le hη0 hη1) (by nlinarith [one_le_pow₀ (n := 3) c.X1])
    have := rpow_le_cX 4 (by have := c.Cm1; positivity)
      (show C' * max L' 1 ≤ 8 * (M * N) ^ 4 by
        calc C' * max L' 1 ≤ (2 * (M * N)) * (4 * (M * N) ^ 3) :=
              mul_le_mul c.Cm2X hm (by positivity) (by positivity)
          _ = 8 * (M * N) ^ 4 := by ring) (by norm_num) hX0.le c.hδ0.le
      (by linarith [c.hδ1])
    simpa using this
  have hZτ' : Zτ ≤ Kt * (2 * (M * N) ^ δ) * Z := hZτ.trans (by gcongr; exact c.twoN_pow)
  have hβ0 : 0 ≤ betaE KE α δ L' C' := betaE_nonneg hKE c.Cm1
  have hT := c.T0
  have hMp : 0 ≤ M ^ (1 - δ) := by positivity
  have hNp : 0 ≤ (N / Ng) ^ (-(1 - 2 * δ)) := by positivity
  have hBf0 : 0 ≤ Bf α L' C' := Bf_nonneg (by linarith [c.Cm1])
  have hexp : (M * N) ^ (2 * δ + (η + α * η)) ≤ (M * N) ^ (4 * δ) :=
    Xpow_mono c.X1 (by linarith)
  calc P ≤ KD * M ^ (1 - δ) * w * betaE KE α δ L' C' * (N / Ng) ^ (-(1 - 2 * δ)) * Zτ := hP
    _ = KD * w * (M ^ (1 - δ) * (N / Ng) ^ (-(1 - 2 * δ)) *
          (KE * min (max L' 1 + C' ^ α) (C' + max L' 1 ^ α))) * (C' * max L' 1) ^ δ * Zτ := by
        unfold betaE; ring
    _ ≤ KD * w * (M ^ (1 - δ) * (N / Ng) ^ (-(1 - 2 * δ)) * (KE * Bf α L' C')) *
          (C' * max L' 1) ^ δ * Zτ := by gcongr
    _ = KD * w * KE * (M ^ (1 - δ) * (N / Ng) ^ (-(1 - 2 * δ)) * Bf α L' C') *
          (C' * max L' 1) ^ δ * Zτ := by ring
    _ ≤ KD * Ng * KE * ((8 + 4 ^ α) * Ng * (M * N) ^ (4 * δ) * Tg M N L α) *
          (8 * (M * N) ^ (4 * δ)) * (Kt * (2 * (M * N) ^ δ) * Z) := by
        have hA : M ^ (1 - δ) * (N / Ng) ^ (-(1 - 2 * δ)) * Bf α L' C' ≤
            (8 + 4 ^ α) * Ng * (M * N) ^ (4 * δ) * Tg M N L α :=
          hB.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp (by have := c.hNg; positivity)) hT)
        gcongr KD * ?_ * KE * ?_ * ?_ * ?_
    _ = (16 * KD * KE * Kt * (8 + 4 ^ α)) * (Ng ^ 2 *
          ((M * N) ^ (4 * δ) * (M * N) ^ (4 * δ) * (M * N) ^ δ) * Tg M N L α * Z) := by ring
    _ ≤ (16 * KD * KE * Kt * (8 + 4 ^ α)) * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) := by
        rw [← Real.rpow_add hX0, ← Real.rpow_add hX0,
          show 4 * δ + 4 * δ + δ = 9 * δ by ring]
        gcongr
        · exact c.hNg
        · norm_num

/-- TT. -/
lemma fin_TT {M N L ε α δ Ng Z Zτ P c0 wm w4 NB Bm KE Kt : ℝ} (c : Ctx M N L ε α δ Ng)
    (hc0 : 0 ≤ c0) (hKE : 0 ≤ KE) (hKt : 0 ≤ Kt) (hZ : 0 ≤ Z) (hwm : 0 ≤ wm) (hw40 : 0 ≤ w4)
    (hw4 : w4 ≤ Ng ^ 2) (hZτ0 : 0 ≤ Zτ) (hZτ : Zτ ≤ Kt * (2 * N) ^ δ * Z)
    (hNB0 : 0 ≤ NB) (hNB : NB ≤ (10 * (M * N) ^ 2) ^ δ / (δ * Real.log 2))
    (hBm : Bm = KE * (32 * 16 ^ α * Ng * (M * N) ^ (2 * δ) * Tg M N L α / Real.sqrt M) *
      (32 * (M * N) ^ (4 * δ)))
    (hP : P ≤ c0 * Real.sqrt M * wm * w4 * (NB * (2 * Bm * Zτ))) :
    P ≤ (c0 * wm * (10 / (δ * Real.log 2)) * 2 * KE * 32 * 16 ^ α * 32 * Kt * 2) *
      (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) := by
  have hM0 : 0 < M := by linarith [c.M1]
  have hX0 : 0 < M * N := by linarith [c.X1]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN0 : 0 < N := by linarith [c.N1]
  have hδ0 := c.hδ0
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM0
  have hT := c.T0
  have hNB' : NB ≤ 10 * (M * N) ^ (2 * δ) / (δ * Real.log 2) := by
    refine hNB.trans (div_le_div_of_nonneg_right ?_ (by have := c.hδ0; positivity))
    have := rpow_le_cX 2 (by positivity) (le_refl (10 * (M * N) ^ 2)) (by norm_num) hX0.le
      c.hδ0.le (by linarith [c.hδ1])
    simpa using this
  have hZτ' : Zτ ≤ Kt * (2 * (M * N) ^ δ) * Z := hZτ.trans (by gcongr; exact c.twoN_pow)
  have hsB : Real.sqrt M * Bm = KE * (32 * 16 ^ α * Ng * (M * N) ^ (2 * δ) * Tg M N L α) *
      (32 * (M * N) ^ (4 * δ)) := by
    rw [hBm]; field_simp
  have hNg0 : 0 ≤ Ng := by linarith [c.hNg]
  calc P ≤ c0 * Real.sqrt M * wm * w4 * (NB * (2 * Bm * Zτ)) := hP
    _ = c0 * wm * w4 * NB * 2 * (Real.sqrt M * Bm) * Zτ := by ring
    _ = c0 * wm * w4 * NB * 2 * (KE * (32 * 16 ^ α * Ng * (M * N) ^ (2 * δ) * Tg M N L α) *
          (32 * (M * N) ^ (4 * δ))) * Zτ := by rw [hsB]
    _ ≤ c0 * wm * Ng ^ 2 * (10 * (M * N) ^ (2 * δ) / (δ * Real.log 2)) * 2 *
          (KE * (32 * 16 ^ α * Ng * (M * N) ^ (2 * δ) * Tg M N L α) *
          (32 * (M * N) ^ (4 * δ))) * (Kt * (2 * (M * N) ^ δ) * Z) := by gcongr
    _ = (c0 * wm * (10 / (δ * Real.log 2)) * 2 * KE * 32 * 16 ^ α * 32 * Kt * 2) *
          (Ng ^ 3 * ((M * N) ^ (2 * δ) * (M * N) ^ (2 * δ) * (M * N) ^ (4 * δ) * (M * N) ^ δ) *
            Tg M N L α * Z) := by ring
    _ ≤ (c0 * wm * (10 / (δ * Real.log 2)) * 2 * KE * 32 * 16 ^ α * 32 * Kt * 2) *
          (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) := by
        rw [← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0,
          show 2 * δ + 2 * δ + 4 * δ + δ = 9 * δ by ring]
        have : 0 ≤ c0 * wm * (10 / (δ * Real.log 2)) * 2 * KE * 32 * 16 ^ α * 32 * Kt * 2 := by
          have := c.hδ0; positivity
        gcongr
        · exact c.hNg
        · norm_num

/-- DQ. -/
lemma fin_DQ {M N L ε α δ η σ Ng Z Zτ P w card KQ Kt cc : ℝ} (c : Ctx M N L ε α δ Ng)
    (hη0 : 0 < η) (hσ : 1 ≤ σ) (hησ : 3 ≤ η * (σ - 1 / 2))
    (hKQ : 0 ≤ KQ) (hKt : 0 ≤ Kt) (hcc : 0 ≤ cc) (hZ : 0 ≤ Z) (hw0 : 0 ≤ w) (hw : w ≤ Ng)
    (hcard0 : 0 ≤ card) (hcard : card ≤ cc * (2 * N))
    (hZτ0 : 0 ≤ Zτ) (hZτ : Zτ ≤ Kt * (2 * N) ^ δ * Z)
    (hP : P ≤ KQ * M ^ (-σ) * Ng ^ σ * w * (max (2 * N / Ng) 1) ^ (1 + 2 * σ) *
      (4 * N ^ 2 / M * (M * N) ^ η) ^ (-(σ - 1 / 2)) * card * Zτ) :
    P ≤ (16 * KQ * cc * Kt) * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) := by
  have hM0 : 0 < M := by linarith [c.M1]
  have hX0 : 0 < M * N := by linarith [c.X1]
  have hT := c.T0
  have hT1 := c.T1
  have hD := Ex_DQ c.h hη0 hσ c.hNg c.hNg2
  have hX3 : (M * N) ^ (3 - η * (σ - 1 / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos c.X1 (by linarith)
  have hZτ' : Zτ ≤ Kt * (2 * (M * N) ^ δ) * Z := hZτ.trans (by gcongr; exact c.twoN_pow)
  set Q := M ^ (-σ) * Ng ^ σ * (max (2 * N / Ng) 1) ^ (1 + 2 * σ) *
      (4 * N ^ 2 / M * (M * N) ^ η) ^ (-(σ - 1 / 2)) with hQ
  have hQ0 : 0 ≤ Q := by
    rw [hQ]; have := c.Cm1; have := c.hNg; positivity
  have hQ8 : Q * (2 * N) ≤ 8 := by
    rw [hQ]; exact hD.trans (by linarith)
  have hNg0 : 0 ≤ Ng := by linarith [c.hNg]
  have hN0 : 0 < N := by linarith [c.N1]
  calc P ≤ KQ * M ^ (-σ) * Ng ^ σ * w * (max (2 * N / Ng) 1) ^ (1 + 2 * σ) *
        (4 * N ^ 2 / M * (M * N) ^ η) ^ (-(σ - 1 / 2)) * card * Zτ := hP
    _ = KQ * w * Q * card * Zτ := by rw [hQ]; ring
    _ ≤ KQ * Ng * Q * (cc * (2 * N)) * (Kt * (2 * (M * N) ^ δ) * Z) := by gcongr
    _ = KQ * Ng * cc * (Q * (2 * N)) * (Kt * (2 * (M * N) ^ δ) * Z) := by ring
    _ ≤ KQ * Ng * cc * 8 * (Kt * (2 * (M * N) ^ δ) * Z) := by gcongr
    _ = (16 * KQ * cc * Kt) * (Ng * (M * N) ^ δ * 1 * Z) := by ring
    _ ≤ (16 * KQ * cc * Kt) * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) := by
        gcongr
        · calc Ng = Ng ^ 1 := (pow_one _).symm
            _ ≤ Ng ^ 4 := pow_le_pow_right₀ c.hNg (by norm_num)
        · exact c.X1
        · linarith [c.hδ0]

/-- The principal pair. -/
lemma fin_PR {M N L ε α δ Ng Z Zc P cc : ℝ} (c : Ctx M N L ε α δ Ng) (hcc : 0 ≤ cc)
    (hZc : Zc ≤ Z) (hZc0 : 0 ≤ Zc) (hP : P ≤ cc * (3 * M) * Zc) :
    P ≤ (3 * cc) * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) := by
  have hM0 : 0 < M := by linarith [c.M1]
  have hTM : M ≤ Tg M N L α := Tg_ge_M hM0.le (by linarith [c.N1]) c.h.Lpos
  have h1 : 1 ≤ Ng ^ 4 := one_le_pow₀ c.hNg
  have h2 : 1 ≤ (M * N) ^ (9 * δ) := Real.one_le_rpow c.X1 (by linarith [c.hδ0])
  have hZ : 0 ≤ Z := hZc0.trans hZc
  have hT := c.T0
  calc P ≤ cc * (3 * M) * Zc := hP
    _ ≤ cc * (3 * Tg M N L α) * Z := by gcongr
    _ = (3 * cc) * (1 * 1 * Tg M N L α * Z) := by ring
    _ ≤ (3 * cc) * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) := by gcongr

/-- The dyadic-row factor `Bm` of the `T − T′` piece. -/
lemma fin_Bm {M N L ε α δ η Ng Nf KE Y : ℝ} (c : Ctx M N L ε α δ Ng) (hη0 : 0 < η)
    (hηδ : η ≤ δ) (hαη : α * η ≤ δ) (hKE : 0 ≤ KE) (hNf : 1 ≤ Nf) (hNfg : Nf ≤ Ng)
    (hY0 : min (4 * N ^ 2 / M * (M * N) ^ η / Nf) L ≤ Y)
    (hY1 : Y ≤ 2 * max (4 * N ^ 2 / M * (M * N) ^ η / Nf) L) :
    Y ^ (-(1 / 2 : ℝ)) * betaE KE α δ (2 * Y) (max (2 * N / Ng) 1) ≤
      KE * (32 * 16 ^ α * Ng * (M * N) ^ (2 * δ) * Tg M N L α / Real.sqrt M) *
        (32 * (M * N) ^ (4 * δ)) := by
  have hM0 : 0 < M := by linarith [c.M1]
  have hN0 : 0 < N := by linarith [c.N1]
  have hX0 : 0 < M * N := by linarith [c.X1]
  have hNg0 : 0 < Ng := by linarith [c.hNg]
  have hNf0 : 0 < Nf := by linarith
  have hT := c.T0
  have hη1 : η ≤ 1 := by linarith [c.hδ1]
  set C' := max (2 * N / Ng) 1 with hC'
  set L' := 4 * N ^ 2 / M * (M * N) ^ η with hL'
  have hL'0 : 0 < L' := by positivity
  have hYpos : 0 < Y := lt_of_lt_of_le (lt_min (by positivity) c.h.Lpos) hY0
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM0
  have hTT := Ex_TT c.h c.hα hη0 hNf hNfg (by linarith [c.Cm1]) c.Cm2 hY0 hY1
  rw [← hC'] at hTT
  have hsNg : Real.sqrt Ng ≤ Ng := by
    calc Real.sqrt Ng ≤ Real.sqrt (Ng ^ 2) := Real.sqrt_le_sqrt (by nlinarith [c.hNg])
      _ = Ng := Real.sqrt_sq hNg0.le
  have hXe : (M * N) ^ (α * η + η) ≤ (M * N) ^ (2 * δ) := Xpow_mono c.X1 (by linarith)
  have hTT' : Real.sqrt M * Y ^ (-(1 / 2 : ℝ)) * Bf α (2 * Y) C' ≤
      32 * 16 ^ α * Ng * (M * N) ^ (2 * δ) * Tg M N L α := by
    refine hTT.trans ?_
    have : (0 : ℝ) ≤ 32 * 16 ^ α := by positivity
    gcongr
  have hmax : max (2 * Y) 1 ≤ 16 * (M * N) ^ 3 := by
    have hX3 : M * N ≤ (M * N) ^ 3 := by
      have := one_le_pow₀ (n := 2) c.X1
      nlinarith
    have hLp := c.Lp_le hη0 hη1
    rw [← hL'] at hLp
    have h1 : L' / Nf ≤ L' := div_le_self hL'0.le hNf
    have h2 : max (L' / Nf) L ≤ 4 * (M * N) ^ 3 :=
      max_le (by linarith) (by linarith [c.h.L_le_M, c.MX])
    refine max_le (by linarith) ?_
    nlinarith [one_le_pow₀ (n := 3) c.X1]
  have hpow : (C' * max (2 * Y) 1) ^ δ ≤ 32 * (M * N) ^ (4 * δ) := by
    have := rpow_le_cX 4 (by have := c.Cm1; positivity)
      (show C' * max (2 * Y) 1 ≤ 32 * (M * N) ^ 4 by
        calc C' * max (2 * Y) 1 ≤ (2 * (M * N)) * (16 * (M * N) ^ 3) :=
              mul_le_mul c.Cm2X hmax (by positivity) (by positivity)
          _ = 32 * (M * N) ^ 4 := by ring) (by norm_num) hX0.le c.hδ0.le
      (by linarith [c.hδ1])
    simpa using this
  have hmin : min (max (2 * Y) 1 + C' ^ α) (C' + max (2 * Y) 1 ^ α) ≤ Bf α (2 * Y) C' :=
    min_le_Bf (by linarith [c.hα]) (by linarith [c.Cm1])
  have h0 : 0 ≤ min (max (2 * Y) 1 + C' ^ α) (C' + max (2 * Y) 1 ^ α) := by
    have := c.Cm1
    exact le_min (by positivity) (by positivity)
  have hYp : 0 ≤ Y ^ (-(1 / 2 : ℝ)) := by positivity
  have hBf0 : 0 ≤ Bf α (2 * Y) C' := Bf_nonneg (by linarith [c.Cm1])
  have hdiv : Y ^ (-(1 / 2 : ℝ)) * Bf α (2 * Y) C' ≤
      32 * 16 ^ α * Ng * (M * N) ^ (2 * δ) * Tg M N L α / Real.sqrt M := by
    rw [le_div_iff₀ hsM]; linarith [hTT']
  unfold betaE
  calc Y ^ (-(1 / 2 : ℝ)) * (KE * min (max (2 * Y) 1 + C' ^ α) (C' + max (2 * Y) 1 ^ α) *
        (C' * max (2 * Y) 1) ^ δ)
      ≤ Y ^ (-(1 / 2 : ℝ)) * (KE * Bf α (2 * Y) C' * (32 * (M * N) ^ (4 * δ))) := by
        gcongr
    _ = KE * (Y ^ (-(1 / 2 : ℝ)) * Bf α (2 * Y) C') * (32 * (M * N) ^ (4 * δ)) := by ring
    _ ≤ _ := by gcongr

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-!
# L3Q_Main: GL Prop 5.2 for one modulus, on finite column sets (`L3H.S3` form)
-/

namespace ArtinPrimitiveRoots.L3Q

open GLW

open NumberField Complex

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

lemma Ztau_nonneg (C : Finset (Ideal (𝓞 F))) (z : Ideal (𝓞 F) → ℂ) : 0 ≤ Ztau C z := by
  unfold Ztau; exact Finset.sum_nonneg fun c _ => by positivity

lemma norm_TT_const (M : ℝ) (hM : 0 < M) :
    ‖R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * Wm (1 / 2)‖ =
      ‖R0 F 1 / 2‖ * ‖Wm (1 / 2)‖ * Real.sqrt M := by
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hM, Real.sqrt_eq_rpow]
  norm_num
  ring

/-- The parameter choices. -/
structure Params (ε₀ α δ η σ : ℝ) : Prop where
  hδ0 : 0 < δ
  hδ1 : δ ≤ 1 / 40
  hη0 : 0 < η
  hηδ : η ≤ δ
  hαη : α * η ≤ δ
  h9 : 9 * δ ≤ ε₀
  hσ1 : 1 ≤ σ
  hσint : ∀ m : ℕ, σ ≠ m
  hησ : 3 ≤ η * (σ - 1 / 2)

lemma params_exist {ε₀ α : ℝ} (hε₀ : 0 < ε₀) (hα : 1 ≤ α) :
    ∃ δ η σ : ℝ, Params ε₀ α δ η σ := by
  set ε₁ := min ε₀ 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε₀ one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁ε : ε₁ ≤ ε₀ := min_le_left _ _
  set δ := ε₁ / 40
  set η := ε₁ / (40 * α)
  have hα0 : 0 < α := by linarith
  have hη0 : 0 < η := by positivity
  set m := ⌈4 / η⌉₊
  refine ⟨δ, η, (m : ℝ) + 3 / 2, ⟨by positivity, by
    show ε₁ / 40 ≤ 1 / 40; linarith, hη0, ?_, ?_, by show 9 * (ε₁ / 40) ≤ ε₀; linarith,
    by have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
       linarith, sigma_nonint m, ?_⟩⟩
  · show ε₁ / (40 * α) ≤ ε₁ / 40
    exact div_le_div_of_nonneg_left hε₁0.le (by norm_num) (by linarith)
  · show α * (ε₁ / (40 * α)) ≤ ε₁ / 40
    rw [le_iff_eq_or_lt]; left; field_simp
  · have hm : 4 / η ≤ m := Nat.le_ceil _
    have : (m : ℝ) + 3 / 2 - 1 / 2 = m + 1 := by ring
    rw [this]
    have h4 : η * (4 / η) = 4 := by field_simp
    nlinarith

set_option maxHeartbeats 4000000 in
open Classical in
theorem main_fin {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪)
    (h𝔪 : 𝔪 ≠ ⊥) (h𝔪t : 𝔪 ≠ ⊤) {α : ℝ} (hα : 1 ≤ α)
    (hE : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
      ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
          (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
        ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
            (Ideal.absNorm 𝔡 : ℝ) ≤ D},
            ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
          K * (D + C ^ α) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2)
    {k : ℕ} (cls : Ideal (𝓞 F) → Fin k)
    (hcut : ∀ 𝔤 c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 (𝔤 * c₁ * c₂) → Squarefree (𝔤 * c₁ * c₂) →
      c₁ * c₂ ≠ ⊤ → cls (𝔤 * c₁) = cls (𝔤 * c₂) →
        ∃ Λ : ℂ → ℂ, LamHyp 𝔪 (c₁ * c₂) (psiP g c₁ c₂) Λ)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ K : ℝ, ∀ M N L : ℝ, Rng M N L ε₀ → ∀ (𝔤 : Ideal (𝓞 F)) (j : Fin k)
      (lam : Ideal (𝓞 F) → ℂ),
      ‖L3H.S3 (L3H.chiK ι 𝔪 g) (L3H.RwF 𝔪 L M) (fun 𝔞 => W ((Ideal.absNorm 𝔞 : ℝ) / M))
          (· ⊔ ·) ((L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)) 𝔤 lam‖ ≤
        K * (Ideal.absNorm 𝔤 : ℝ) ^ 4 * (M * N) ^ ε₀ * Tg M N L α *
          ∑ b ∈ (L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j), ‖lam b‖ ^ 2 := by
  have hψ0 : ∀ c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 c₁ → IsExterior 𝔪 c₂ →
      PsiHyp 𝔪 (c₁ * c₂) (psiP g c₁ c₂) := fun c₁ c₂ h1 h2 => psiHyp_pair hχ g h𝔪 h1 h2
  obtain ⟨δ, η, σ₁, hp⟩ := params_exist hε₀ hα
  have hδ2 : δ < 1 / 2 := by linarith [hp.hδ1]
  have hQ := norm_PSnp_RPt_le_and_norm_PSnp_DPt_le_and_norm_PSnp_DQt_le_and_norm_PSnp_TTt_le F ι 𝔪
    h𝔪 g hψ0
  obtain ⟨KR, hKR0, hRP⟩ := hQ.1 δ hp.hδ0 hδ2
  obtain ⟨KD, hKD0, hDP⟩ := hQ.2.1 δ hp.hδ0 hδ2
  obtain ⟨KQ, hKQ0, hDQ⟩ := hQ.2.2.1 σ₁ hp.hσ1
  obtain ⟨KE, hKE0, hSB⟩ := sbf_of_E hχ g hE hp.hδ0
  obtain ⟨Kτ, hKτ0, hτ⟩ := L3H.two_pow_card_pf_le (F := F) (ε := δ / 3) (by linarith [hp.hδ0])
  obtain ⟨cc, hcc0, hcard⟩ := L3H.card_le_mul F
  set c0 := ‖R0 F 1 / 2‖ * ‖Wm (1 / 2)‖ with hc0
  set wm : ℝ := (2 : ℝ) ^ (primesOf 𝔪).card with hwm
  set Kt := Kτ ^ 3 with hKt
  have hKt0 : 0 ≤ Kt := by positivity
  have hwm0 : 0 ≤ wm := by positivity
  have hc00 : 0 ≤ c0 := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K1 := 16 * KR * KE * Kt * wm
  set K2 := 16 * KD * KE * Kt * (8 + 4 ^ α)
  set K3 := c0 * wm * (10 / (δ * Real.log 2)) * 2 * KE * 32 * 16 ^ α * 32 * Kt * 2
  set K4 := 16 * KQ * cc * Kt
  set K5 := 3 * cc
  have hK3 : 0 ≤ K3 := by have := hp.hδ0; positivity
  refine ⟨K3 + K2 + K4 + K1 + K5, ?_⟩
  intro M N L h 𝔤 j lam
  have hM0 : 0 < M := by linarith [h.hM]
  have hN0 : 0 < N := by linarith [h.hN]
  have hX1 := h.X1
  have hT0 : 0 ≤ Tg M N L α := Tg_nonneg hM0.le hN0.le h.Lpos
  set Cs := (L3H.rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j) with hCs
  set Z := ∑ b ∈ Cs, ‖lam b‖ ^ 2 with hZ
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => by positivity
  have hKall : 0 ≤ K3 + K2 + K4 + K1 + K5 := by
    have : 0 ≤ K1 := by positivity
    have : 0 ≤ K2 := by positivity
    have : 0 ≤ K4 := by positivity
    have : 0 ≤ K5 := by positivity
    linarith
  have hmemCs : ∀ b ∈ Cs, IsExterior 𝔪 b ∧ Squarefree b ∧ N < (Ideal.absNorm b : ℝ) ∧
      (Ideal.absNorm b : ℝ) ≤ 2 * N ∧ cls b = j := by
    intro b hb
    rw [hCs, Finset.mem_filter, L3H.mem_rowsF] at hb
    exact ⟨hb.1.1, hb.1.2.1, hb.1.2.2.1, hb.1.2.2.2, hb.2⟩
  by_cases hex : ∃ b ∈ Cs, 𝔤 ∣ b
  swap
  · push Not at hex
    have h0 : L3H.S3 (L3H.chiK ι 𝔪 g) (L3H.RwF 𝔪 L M) (fun 𝔞 => W ((Ideal.absNorm 𝔞 : ℝ) / M))
        (· ⊔ ·) Cs 𝔤 lam = 0 := by
      unfold L3H.S3
      refine Finset.sum_eq_zero fun b₁ hb₁ => Finset.sum_eq_zero fun b₂ _ => ?_
      rw [if_neg]
      intro hb
      exact hex b₁ hb₁ (Ideal.dvd_iff_le.2 (hb ▸ le_sup_left))
    rw [h0, norm_zero]
    positivity
  obtain ⟨b, hb, c, rfl⟩ := hex
  obtain ⟨hbe, hbs, hbN, hb2N, -⟩ := hmemCs _ hb
  have h𝔤 : 𝔤 ≠ ⊥ := fun h0 => hbe.1 (by rw [h0, Ideal.bot_mul])
  have h𝔤e : IsExterior 𝔪 𝔤 := ext_left hbe
  set Ng : ℝ := (Ideal.absNorm 𝔤 : ℝ) with hNgdef
  have hNg1 : 1 ≤ Ng := by
    rw [hNgdef]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔤)
  have hc0' : c ≠ ⊥ := (ext_right hbe).1
  have hNc1 : (1 : ℝ) ≤ Ideal.absNorm c := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hc0')
  have hNg2 : Ng ≤ 2 * N := by
    rw [map_mul, Nat.cast_mul] at hb2N
    nlinarith
  have cx : Ctx M N L ε₀ α δ Ng := ⟨h, hα, hp.hδ0, by linarith [hp.hδ1], hNg1, hNg2⟩
  have hNg0 : 0 < Ng := by linarith
  -- the decomposition
  set L' := 4 * N ^ 2 / M * (M * N) ^ η with hL'
  have hL'0 : 0 < L' := by have := hp.hη0; positivity
  rw [S3_decomp hχ g h𝔪 h𝔪t cls hcut h𝔤 h𝔤e N j hM0 L L' hp.hδ0 hδ2 hp.hδ0 hδ2
    (by linarith [hp.hσ1]) hp.hσint lam]
  rw [← hCs]
  set C := (L3H.rowsF 𝔪 0 (2 * N / Ideal.absNorm 𝔤)).filter (fun c => 𝔤 * c ∈ Cs) with hC
  set z' : Ideal (𝓞 F) → ℂ := fun c => lam (𝔤 * c) with hz'
  set C' := max (2 * N / Ng) 1 with hC'
  -- facts about the columns
  have hCr : ∀ c ∈ C, c ∈ L3H.rowsF 𝔪 0 (2 * N / Ideal.absNorm 𝔤) :=
    fun c hc => (Finset.mem_filter.1 hc).1
  have hCr' : ∀ c ∈ C, c ∈ L3H.rowsF 𝔪 0 C' := by
    intro c hc
    obtain ⟨h1, h2, h3⟩ := L3H.mem_rowsF_zero.1 (hCr c hc)
    exact L3H.mem_rowsF_zero.2 ⟨h1, h2, h3.trans (le_max_left _ _)⟩
  have hCsub : C ⊆ L3H.rowsF 𝔪 0 C' := fun c hc => hCr' c hc
  have hCCs : ∀ c ∈ C, 𝔤 * c ∈ Cs := fun c hc => (Finset.mem_filter.1 hc).2
  have hCmin : ∀ c ∈ C, N / Ng ≤ (Ideal.absNorm c : ℝ) := by
    intro c hc
    obtain ⟨-, -, h3, -, -⟩ := hmemCs _ (hCCs c hc)
    rw [map_mul, Nat.cast_mul] at h3
    rw [div_le_iff₀ hNg0]; nlinarith
  have hcop : ∀ c ∈ C, c ⊔ 𝔤 * 𝔪 = ⊤ := by
    intro c hc
    obtain ⟨h1, h2, -⟩ := hmemCs _ (hCCs c hc)
    rw [sup_comm, sup_mul_eq_top_iff, sup_comm 𝔪]
    exact ⟨sup_eq_top_of_sqf h2, (ext_right h1).2⟩
  have hZc : ∑ c ∈ C, ‖z' c‖ ^ 2 ≤ Z := sum_image_le h𝔤 C Cs hCCs lam
  have hZc0 : 0 ≤ ∑ c ∈ C, ‖z' c‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hZτ0 := Ztau_nonneg C z'
  have hZτ : Ztau C z' ≤ Kt * (2 * N) ^ δ * Z := by
    refine (Ztau_le hp.hδ0.le hKτ0 hCr hτ z').trans ?_
    have h2N : (2 * N / Ideal.absNorm 𝔤) ^ δ ≤ (2 * N) ^ δ :=
      Real.rpow_le_rpow (by positivity) (div_le_self (by positivity) hNg1) hp.hδ0.le
    exact mul_le_mul (mul_le_mul_of_nonneg_left h2N hKt0) hZc hZc0 (by positivity)
  have hSall : ∀ Y : ℝ, L3H.SBf (L3H.chiK ι 𝔪 g) (L3H.rowsF 𝔪 0 Y) C (betaE KE α δ Y C') :=
    fun Y => (hSB Y C' (le_max_right _ _)).mono_cols hCsub
  have hβ0 : ∀ Y, 0 ≤ betaE KE α δ Y C' := fun Y => betaE_nonneg hKE0 (le_max_right _ _)
  have hw𝔤 : (2 : ℝ) ^ (primesOf 𝔤).card ≤ Ng := two_pow_card_le_absNorm h𝔤
  -- RP
  have h𝔤𝔪 : 𝔤 * 𝔪 ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
    exact ⟨by rw [Ideal.zero_eq_bot]; exact h𝔤, by rw [Ideal.zero_eq_bot]; exact h𝔪⟩
  have hδ0 := hp.hδ0
  -- RP
  have hSrp : L3H.SBf (L3H.chiK ι 𝔪 g) (Srow 𝔪 𝔤 L) C (betaE KE α δ L C') :=
    (hSall L).mono_rows (by rw [Srow_def]; exact Finset.filter_subset _ _)
  have hCq : ∀ c ∈ C, c ∈ sqfRows 𝔪 C' := fun c hc => by rw [sqfRows_eq]; exact hCr' c hc
  have hRP' := hRP 𝔤 h𝔤 h𝔤𝔪 C C' hCq hcop z' M L _ hM0 (hβ0 L) hSrp
  have bRP := fin_RP cx hKR0 hKE0 hKt0 hZ0 hwm0 (by positivity) (two_pow_card_mul_le h𝔤 h𝔪)
    hZτ0 hZτ hRP'
  -- DP
  have hCmin0 : 0 < N / Ng := by positivity
  have hDP' := hDP 𝔤 C C' hCq z' M L' _ _ hM0 (hβ0 L') hCmin0 hCmin
    (by rw [sqfRows_eq]; exact hSall L')
  have bDP := fin_DP cx hp.hη0 hp.hηδ hp.hαη hKD0 hKE0 hKt0 hZ0 (by positivity) hw𝔤 hZτ0 hZτ
    hDP'
  -- DQ
  have hDQ' := hDQ 𝔤 h𝔤 C (2 * N / Ideal.absNorm 𝔤)
    (fun c hc => by rw [sqfRows_eq]; exact hCr c hc) z' M L' hM0 hL'0
  have hcardC : (C.card : ℝ) ≤ cc * (2 * N) :=
    (hcard C' (le_max_right _ _) C
      (fun c hc => (L3H.mem_rowsF_zero.1 (hCr' c hc)).2.2)).trans
      (mul_le_mul_of_nonneg_left cx.Cm2 hcc0)
  have bDQ := fin_DQ cx hp.hη0 hp.hσ1 hp.hησ hKQ0 hKt0 hcc0 hZ0 (by positivity) hw𝔤
    (by positivity) hcardC hZτ0 hZτ hDQ'
  -- T − T′
  set βf : ℝ → ℝ := fun Y => betaE KE α δ Y C' with hβf
  set NB := (10 * (M * N) ^ 2) ^ δ / (δ * Real.log 2) with hNBdef
  set Bm := KE * (32 * 16 ^ α * Ng * (M * N) ^ (2 * δ) * Tg M N L α / Real.sqrt M) *
    (32 * (M * N) ^ (4 * δ)) with hBmdef
  have hNB0 : 0 ≤ NB := by positivity
  have hBm0 : 0 ≤ Bm := by positivity
  have hNB : ∀ f ∈ (primesOf 𝔤).powerset,
      (nblk (min (L' / Ideal.absNorm (pideal f)) L) (max (L' / Ideal.absNorm (pideal f)) L) : ℝ)
        ≤ NB := by
    intro f hf
    obtain ⟨h1, h2⟩ := absNorm_pideal_le h𝔤 (Finset.mem_powerset.1 hf)
    exact Ex_NB h hp.hη0 (by linarith [hp.hηδ, hp.hδ1]) h1 (h2.trans hNg2) hp.hδ0
  have hBm : ∀ f ∈ (primesOf 𝔤).powerset, ∀ k : ℕ,
      2 ^ k * min (L' / Ideal.absNorm (pideal f)) L ≤ 2 * max (L' / Ideal.absNorm (pideal f)) L →
      (2 ^ k * min (L' / Ideal.absNorm (pideal f)) L) ^ (-(1 / 2 : ℝ)) *
        βf (2 ^ (k + 1) * min (L' / Ideal.absNorm (pideal f)) L) ≤ Bm := by
    intro f hf k hk
    obtain ⟨h1, h2⟩ := absNorm_pideal_le h𝔤 (Finset.mem_powerset.1 hf)
    have hm0 : 0 ≤ min (L' / Ideal.absNorm (pideal f)) L :=
      le_min (by positivity) h.Lpos.le
    have hY0 : min (L' / Ideal.absNorm (pideal f)) L ≤
        2 ^ k * min (L' / Ideal.absNorm (pideal f)) L :=
      le_mul_of_one_le_left hm0 (one_le_pow₀ one_le_two)
    have e : (2 : ℝ) ^ (k + 1) * min (L' / Ideal.absNorm (pideal f)) L =
        2 * (2 ^ k * min (L' / Ideal.absNorm (pideal f)) L) := by ring
    rw [hβf, e]
    exact fin_Bm cx hp.hη0 hp.hηδ hp.hαη hKE0 h1 h2 hY0 hk
  have hTT' := hQ.2.2.2 𝔤 C C' hCq z' M L L' h.Lpos hL'0 βf hβ0
    (fun Y => by rw [sqfRows_eq]; exact hSall Y) NB Bm hNB0 hBm0 hNB hBm
  rw [norm_TT_const M hM0] at hTT'
  have bTT := fin_TT cx hc00 hKE0 hKt0 hZ0 hwm0 (by positivity) (four_pow_card_le_absNorm h𝔤)
    hZτ0 hZτ hNB0 le_rfl rfl hTT'
  -- the principal pair
  have hRw : ((L3H.RwF 𝔪 L M).card : ℝ) ≤ cc * (3 * M) :=
    hcard (3 * M) (by linarith [h.hM]) _ (fun a ha => (L3H.mem_RwF.1 ha).2.2.le)
  have hPR := principal_le C z' (fun c₁ c₂ => ∑ a ∈ L3H.RwF 𝔪 L M,
      ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) * L3H.chiK ι 𝔪 g a (𝔤 * c₁) *
        starRingEnd ℂ (L3H.chiK ι 𝔪 g a (𝔤 * c₂))) (B := cc * (3 * M)) (by positivity)
    ((norm_row_le g _ M _ _).trans hRw)
  have bPR := fin_PR cx hcc0 hZc hZc0 hPR
  -- assembly
  refine (norm_add_le _ _).trans ?_
  refine le_trans (add_le_add (norm_sub_le _ _) le_rfl) ?_
  refine le_trans (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) ?_
  refine le_trans (add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl)
    le_rfl) ?_
  refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add bTT bDP) bDQ) bRP) bPR) ?_
  have h9 := hp.h9
  have hX9 : (M * N) ^ (9 * δ) ≤ (M * N) ^ ε₀ := Xpow_mono hX1 h9
  have hNg4 : 0 ≤ Ng ^ 4 := by positivity
  calc K3 * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) +
        K2 * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) +
        K4 * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) +
        K1 * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) +
        K5 * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z)
      = (K3 + K2 + K4 + K1 + K5) * (Ng ^ 4 * (M * N) ^ (9 * δ) * Tg M N L α * Z) := by ring
    _ ≤ (K3 + K2 + K4 + K1 + K5) * (Ng ^ 4 * (M * N) ^ ε₀ * Tg M N L α * Z) := by gcongr
    _ = (K3 + K2 + K4 + K1 + K5) * Ng ^ 4 * (M * N) ^ ε₀ * Tg M N L α * Z := by ring

end ArtinPrimitiveRoots.L3Q

end
end

section
section
/-! # L3Q_Dev: GL Proposition 5.2 (85b89dd7), statement verbatim

From the cut `exists_cutoff_exists_cls_exists_differentiable_eq_tsum_residueSymbol_pow_three_and_functionalEquation`
(the functional equation of `ζ_𝔪 · L(χ_{c₁}χ_{c₂})`). Does not import the target's stub. -/

open NumberField

namespace ArtinPrimitiveRoots

theorem exists_cutoff_norm_tsum_tsum_mul_conj_tsum_weight_mul_residueSymbol_pow_three_le
    (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (α : ℝ), 1 ≤ α →
        (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
          ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
              (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
            ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
                (Ideal.absNorm 𝔡 : ℝ) ≤ D},
                ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
              K * (D + C ^ α) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2) →
        ∃ W : ℝ → ℝ, (∀ t, 0 ≤ W t ∧ W t ≤ 1) ∧ (∀ t, 1 < t → t ≤ 2 → W t = 1) ∧
          (∀ t, 3 ≤ t → W t = 0) ∧
          ∃ (k : ℕ) (cls : Ideal (𝓞 F) → Fin k),
            ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ M N L : ℝ, 1 ≤ M → 1 ≤ N →
              N ^ 2 / M * (M * N) ^ ε ≤ L → L ≤ M / (M * N) ^ ε →
              ∀ (𝔤 : Ideal (𝓞 F)) (j : Fin k)
                (z : {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟 ∧ Squarefree 𝔟 ∧
                  N < (Ideal.absNorm 𝔟 : ℝ) ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ 2 * N ∧ cls 𝔟 = j} → ℂ),
                ‖∑' 𝔟₁, ∑' 𝔟₂, if 𝔟₁.1 ⊔ 𝔟₂.1 = 𝔤 then
                    z 𝔟₁ * starRingEnd ℂ (z 𝔟₂) *
                      ∑' 𝔞 : {𝔞 : Ideal (𝓞 F) // IsExterior 𝔪 𝔞 ∧
                          ∀ 𝔟 : Ideal (𝓞 F), 𝔟 ^ 2 ∣ 𝔞 →
                            L * (Ideal.absNorm 𝔟 : ℝ) ^ 2 < Ideal.absNorm 𝔞},
                        (W ((Ideal.absNorm 𝔞.1 : ℝ) / M) : ℂ) *
                          residueSymbol ι 𝔪 𝔞.1 (g.gen 𝔟₁.1) ^ 3 *
                          starRingEnd ℂ (residueSymbol ι 𝔪 𝔞.1 (g.gen 𝔟₂.1) ^ 3)
                  else 0‖ ≤
                  K * (Ideal.absNorm 𝔤 : ℝ) ^ 4 * (M * N) ^ ε *
                    (M + N + Real.sqrt M * L ^ (α - 1 / 2) + Real.sqrt (M / L) * N) *
                    ∑' 𝔟, ‖z 𝔟‖ ^ 2 := by
  obtain ⟨N₁, h₁⟩ :=
    exists_cutoff_exists_cls_exists_differentiable_eq_tsum_residueSymbol_pow_three_and_functionalEquation
      n hn0 hn F ι
  obtain ⟨N₂, h₂⟩ := C3M.hypChiAll (F := F) n hn0 hn ι
  obtain ⟨P₀, hP₀b, hP₀⟩ := Ring.not_isField_iff_exists_prime.1 (NumberField.RingOfIntegers.not_isField F)
  refine ⟨max (max N₁ N₂) (Ideal.absNorm P₀), fun 𝔪 h𝔪 hs g α hα hE => ?_⟩
  have hs₁ : SmallPrimesDvd N₁ 𝔪 := fun P hP hb hle =>
    hs P hP hb (le_trans hle (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hs₂ : SmallPrimesDvd N₂ 𝔪 := fun P hP hb hle =>
    hs P hP hb (le_trans hle (le_trans (le_max_right _ _) (le_max_left _ _)))
  have h𝔪t : 𝔪 ≠ ⊤ := by
    intro ht
    have := hs P₀ hP₀ hP₀b (le_max_right _ _)
    rw [ht, top_le_iff] at this
    exact hP₀.ne_top this
  have hχ := h₂ 𝔪 h𝔪 hs₂
  obtain ⟨k, cls, hcls⟩ := h₁ 𝔪 h𝔪 hs₁ g
  have hcut : ∀ 𝔤 c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 (𝔤 * c₁ * c₂) →
      Squarefree (𝔤 * c₁ * c₂) → c₁ * c₂ ≠ ⊤ → cls (𝔤 * c₁) = cls (𝔤 * c₂) →
        ∃ Λ : ℂ → ℂ, GLW.LamHyp 𝔪 (c₁ * c₂) (GLW.psiP g c₁ c₂) Λ := by
    intro 𝔤 c₁ c₂ he hsq hne hc
    obtain ⟨Λ, hd, hdir, hfe, hgr⟩ := hcls 𝔤 c₁ c₂ he hsq hne hc
    exact ⟨Λ, L3Q.lamHyp_of_cut h𝔪 g hd hdir hfe hgr⟩
  refine ⟨GLW.W, L3Q.W_props.1, L3Q.W_props.2.1, L3Q.W_props.2.2, k, cls, fun ε hε => ?_⟩
  obtain ⟨K, hK⟩ := L3Q.main_fin hχ g h𝔪 h𝔪t hα hE cls hcut hε
  refine ⟨K, fun M N L hM hN hL1 hL2 𝔤 j z => ?_⟩
  obtain ⟨e1, e2⟩ := L3Q.tsum_LHS_eq ι 𝔪 g GLW.W L3Q.W_props.2.2 cls M N L (by linarith) 𝔤 j z
  rw [e1, e2]
  exact hK M N L ⟨hM, hN, hε, hL1, hL2⟩ 𝔤 j _

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField

theorem solution
    (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (α : ℝ), 1 ≤ α →
        (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
          ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
              (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
            ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
                (Ideal.absNorm 𝔡 : ℝ) ≤ D},
                ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
              K * (D + C ^ α) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2) →
        ∃ W : ℝ → ℝ, (∀ t, 0 ≤ W t ∧ W t ≤ 1) ∧ (∀ t, 1 < t → t ≤ 2 → W t = 1) ∧
          (∀ t, 3 ≤ t → W t = 0) ∧
          ∃ (k : ℕ) (cls : Ideal (𝓞 F) → Fin k),
            ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ M N L : ℝ, 1 ≤ M → 1 ≤ N →
              N ^ 2 / M * (M * N) ^ ε ≤ L → L ≤ M / (M * N) ^ ε →
              ∀ (𝔤 : Ideal (𝓞 F)) (j : Fin k)
                (z : {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟 ∧ Squarefree 𝔟 ∧
                  N < (Ideal.absNorm 𝔟 : ℝ) ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ 2 * N ∧ cls 𝔟 = j} → ℂ),
                ‖∑' 𝔟₁, ∑' 𝔟₂, if 𝔟₁.1 ⊔ 𝔟₂.1 = 𝔤 then
                    z 𝔟₁ * starRingEnd ℂ (z 𝔟₂) *
                      ∑' 𝔞 : {𝔞 : Ideal (𝓞 F) // IsExterior 𝔪 𝔞 ∧
                          ∀ 𝔟 : Ideal (𝓞 F), 𝔟 ^ 2 ∣ 𝔞 →
                            L * (Ideal.absNorm 𝔟 : ℝ) ^ 2 < Ideal.absNorm 𝔞},
                        (W ((Ideal.absNorm 𝔞.1 : ℝ) / M) : ℂ) *
                          residueSymbol ι 𝔪 𝔞.1 (g.gen 𝔟₁.1) ^ 3 *
                          starRingEnd ℂ (residueSymbol ι 𝔪 𝔞.1 (g.gen 𝔟₂.1) ^ 3)
                  else 0‖ ≤
                  K * (Ideal.absNorm 𝔤 : ℝ) ^ 4 * (M * N) ^ ε *
                    (M + N + Real.sqrt M * L ^ (α - 1 / 2) + Real.sqrt (M / L) * N) *
                    ∑' 𝔟, ‖z 𝔟‖ ^ 2 := by
  exact ArtinPrimitiveRoots.exists_cutoff_norm_tsum_tsum_mul_conj_tsum_weight_mul_residueSymbol_pow_three_le n hn0 hn F ι

end
