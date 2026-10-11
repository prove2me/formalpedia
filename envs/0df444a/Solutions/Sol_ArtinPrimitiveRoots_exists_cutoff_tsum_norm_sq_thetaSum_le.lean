-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_thetaSum_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T22:46:32.224666+00:00
-- url     : https://prove2.me/submissions/62e637b4-0a61-457a-b350-4186492ccdb0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_thetaSum_dyadic_le

section
namespace ArtinPrimitiveRoots

/-! L2D: abstract dyadic decomposition, used for (4.6) ⇐ (4.5). -/

/-- Each `x ≥ 1` lies in a dyadic interval `[2^i, 2^(i+1))` with `2^i ≤ x`. -/
lemma L2D_dyad_exists (x : ℝ) (hx : 1 ≤ x) :
    (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ ≤ x ∧ x < 2 * (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ := by
  have h1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.2 hx
  have hne : ⌊x⌋₊ ≠ 0 := by omega
  have a := Nat.pow_log_le_self 2 hne
  have b := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊x⌋₊
  constructor
  · calc (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ = ((2 ^ Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast a
      _ ≤ x := Nat.floor_le (by linarith)
  · have : ⌊x⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊x⌋₊).succ := b
    have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have h3 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 ⌊x⌋₊).succ : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h3
    rw [pow_succ] at h3
    linarith

lemma L2D_dyad_unique (x : ℝ) (i i' : ℕ) (h1 : (2 : ℝ) ^ i ≤ x) (h2 : x < 2 * (2 : ℝ) ^ i)
    (h1' : (2 : ℝ) ^ i' ≤ x) (h2' : x < 2 * (2 : ℝ) ^ i') : i = i' := by
  have key : ∀ a b : ℕ, (2 : ℝ) ^ a ≤ x → x < 2 * (2 : ℝ) ^ b → a ≤ b := by
    intro a b ha hb
    have : (2 : ℝ) ^ a < (2 : ℝ) ^ (b + 1) := by rw [pow_succ]; linarith
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this
    omega
  exact le_antisymm (key _ _ h1 h2') (key _ _ h1' h2)

/-- The dyadic decomposition: if every dyadic block `{P ≤ x < 2P, D ≤ y < 2D}` of the set `A`
has a mass `σ ≤ M` whenever it is nonempty-compatible (`P D ≤ B`), and on `A` one has `x, y ≥ 1`
and `x y ≤ B`, then the mass of `A` is at most `(K + 1)^2 M`, `K = log₂ ⌊B⌋`. -/
lemma L2D_dyadic_sum {β : Type*} (w : β → ℝ) (A : β → Prop)
    (x y : β → ℝ) (B M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ r, A r → 1 ≤ x r ∧ 1 ≤ y r ∧ x r * y r ≤ B)
    (Q : ℝ → ℝ → β → Prop)
    (hQ : ∀ P D r, Q P D r ↔ (A r ∧ P ≤ x r ∧ x r < 2 * P ∧ D ≤ y r ∧ y r < 2 * D))
    (hdy : ∀ P D : ℝ, 1 ≤ P → 1 ≤ D → P * D ≤ B →
      ∃ σ : ℝ, HasSum (fun r : {r // Q P D r} => w r) σ ∧ σ ≤ M) :
    ∃ σ : ℝ, HasSum (fun r : {r // A r} => w r) σ ∧
      σ ≤ ((Nat.log 2 ⌊B⌋₊ + 1 : ℕ) : ℝ) ^ 2 * M := by
  classical
  set K := Nat.log 2 ⌊B⌋₊
  set s : Finset (ℕ × ℕ) := Finset.range (K + 1) ×ˢ Finset.range (K + 1)
  -- the dyadic block sets
  let T : ℕ × ℕ → Set β := fun p => {r | Q ((2 : ℝ) ^ p.1) ((2 : ℝ) ^ p.2) r}
  -- each block has a mass σ_p ≤ M (zero if empty)
  have hblock : ∀ p : ℕ × ℕ, ∃ σ : ℝ, HasSum ((T p).indicator w) σ ∧ σ ≤ M := by
    intro p
    by_cases hne : ∃ r, r ∈ T p
    · obtain ⟨r, hr⟩ := hne
      have hr' := (hQ _ _ r).1 hr
      obtain ⟨hx1, hy1, hxy⟩ := hA r hr'.1
      have hP : (1 : ℝ) ≤ 2 ^ p.1 := one_le_pow₀ (by norm_num)
      have hD : (1 : ℝ) ≤ 2 ^ p.2 := one_le_pow₀ (by norm_num)
      have hPD : (2 : ℝ) ^ p.1 * 2 ^ p.2 ≤ B := by
        calc (2 : ℝ) ^ p.1 * 2 ^ p.2 ≤ x r * y r := by
              apply mul_le_mul hr'.2.1 hr'.2.2.2.1 (by positivity) (by linarith)
          _ ≤ B := hxy
      obtain ⟨σ, hσ, hσM⟩ := hdy _ _ hP hD hPD
      exact ⟨σ, (hasSum_subtype_iff_indicator (s := T p)).1 hσ, hσM⟩
    · push Not at hne
      refine ⟨0, ?_, hM⟩
      have : (T p).indicator w = 0 := by
        funext r; simp [Set.indicator_of_notMem (hne r)]
      rw [this]; exact hasSum_zero
  choose σ hσ hσM using hblock
  -- the pointwise decomposition of `A.indicator w`
  have hdecomp : ({r | A r} : Set β).indicator w = fun r => ∑ p ∈ s, (T p).indicator w r := by
    funext r
    by_cases hr : A r
    · obtain ⟨hx1, hy1, hxy⟩ := hA r hr
      obtain ⟨a1, a2⟩ := L2D_dyad_exists (x r) hx1
      obtain ⟨b1, b2⟩ := L2D_dyad_exists (y r) hy1
      set p0 : ℕ × ℕ := (Nat.log 2 ⌊x r⌋₊, Nat.log 2 ⌊y r⌋₊)
      have hp0T : r ∈ T p0 := (hQ _ _ r).2 ⟨hr, a1, a2, b1, b2⟩
      have hxB : x r ≤ B := by nlinarith
      have hyB : y r ≤ B := by nlinarith
      have hfx : ⌊x r⌋₊ ≤ ⌊B⌋₊ := Nat.floor_le_floor hxB
      have hfy : ⌊y r⌋₊ ≤ ⌊B⌋₊ := Nat.floor_le_floor hyB
      have hp0s : p0 ∈ s := by
        simp only [s, p0, Finset.mem_product, Finset.mem_range]
        exact ⟨Nat.lt_succ_of_le (Nat.log_mono_right hfx),
          Nat.lt_succ_of_le (Nat.log_mono_right hfy)⟩
      rw [Finset.sum_eq_single p0]
      · simp [Set.indicator_of_mem hp0T, Set.indicator_of_mem (show r ∈ {r | A r} from hr)]
      · intro p _ hp
        rw [Set.indicator_of_notMem]
        intro hpT
        have h := (hQ _ _ r).1 hpT
        apply hp
        have e1 := L2D_dyad_unique (x r) _ _ h.2.1 h.2.2.1 a1 a2
        have e2 := L2D_dyad_unique (y r) _ _ h.2.2.2.1 h.2.2.2.2 b1 b2
        exact Prod.ext e1 e2
      · intro h; exact absurd hp0s h
    · rw [Set.indicator_of_notMem (show r ∉ {r | A r} from hr)]
      symm
      apply Finset.sum_eq_zero
      intro p _
      rw [Set.indicator_of_notMem]
      intro hpT
      exact hr ((hQ _ _ r).1 hpT).1
  refine ⟨∑ p ∈ s, σ p, ?_, ?_⟩
  · have h := hasSum_sum (s := s) fun p _ => hσ p
    rw [← hdecomp] at h
    exact (hasSum_subtype_iff_indicator (s := {r | A r})).2 h
  · calc ∑ p ∈ s, σ p ≤ ∑ _p ∈ s, M := Finset.sum_le_sum fun p _ => hσM p
      _ = (s.card : ℝ) * M := by simp
      _ = ((K + 1 : ℕ) : ℝ) ^ 2 * M := by
        rw [Finset.card_product, Finset.card_range]; push_cast; ring

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField Filter Topology

/-! L2D: ideal counting in a number field. -/

variable {F : Type*} [Field F] [NumberField F]

lemma L2D_finite_le (t : ℝ) : {I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ t}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le ⌊t⌋₊).subset fun I hI => Nat.le_floor hI

/-- The finite set of ideals of norm `≤ t` (including `⊥`). -/
noncomputable def L2D_le (F : Type*) [Field F] [NumberField F] (t : ℝ) : Finset (Ideal (𝓞 F)) :=
  (L2D_finite_le (F := F) t).toFinset

@[simp] lemma L2D_mem_le {t : ℝ} {I : Ideal (𝓞 F)} :
    I ∈ L2D_le F t ↔ (Ideal.absNorm I : ℝ) ≤ t := by
  simp [L2D_le]

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: candidate cuts beneath C1b (Proposition 4.1 (4.5)).

* `L2D_Cut64`: Lemma 6.4 (p. 38), the quadratic large sieve for `χ_𝔡(c)^3`
  (Goldmakher–Louvel, Thm 1.1).
* `L2D_Cut63`: Lemma 6.3 (p. 34) with (6.22) (p. 33), the reflected expansion of `B_m(Z)`, with
  the coefficients, row/column functions and profiles existentially quantified and only their
  stated bounds retained. -/

end ArtinPrimitiveRoots
end

section
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

instance fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-! ### Basic facts on Hecke characters -/

/-! ### The Dirichlet series as a sum over ideals -/

/-! ### The finite sieve -/

end T12B

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: factorization combinatorics for the proof of (4.5). -/

variable {F : Type*} [Field F] [NumberField F]

/-! ### `β_p` and the sum of `β_𝔣` -/

open Classical in
lemma L2D_simplePart_dvd (𝔟 : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) : simplePart 𝔟 ∣ 𝔟 := by
  unfold simplePart
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id]
  have hle : ((normalizedFactors 𝔟).toFinset.filter
      fun P => (normalizedFactors 𝔟).count P = 1).val ≤ normalizedFactors 𝔟 := by
    rw [Finset.filter_val, Multiset.toFinset_val]
    exact (Multiset.filter_le _ _).trans (Multiset.dedup_le _)
  have h1 := Multiset.prod_dvd_prod_of_le hle
  have h2 := prod_normalizedFactors h𝔟
  rw [associated_iff_eq] at h2
  rw [h2] at h1
  exact h1


end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: C1b ⇐ its dyadic conjunct (4.5). This is the last paragraph of the proof of
Proposition 4.1 (p. 41): (4.6) follows from (4.5) by summing over the `O((log Z)^2)` dyads. -/

/-- The candidate cut: Proposition 4.1 (4.5) alone, in class form (the first conjunct of C1b). -/
def L2D_Cut45 (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (c₁ c₂ ε : ℝ), 0 < c₁ → 0 < ε →
      ∃ C : ℝ, ∀ Z : ℝ, 2 ≤ Z →
        (∀ P D : ℝ, 1 ≤ P → 1 ≤ D →
          ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 //
              c₁ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
              (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000) ∧
              P ≤ (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) ∧
              (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) < 2 * P ∧
              D ≤ (Ideal.absNorm (simplePart r.1.1) : ℝ) ∧
              (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D} =>
                ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
            σ ≤ C * Z ^ ε * P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z))

variable {F : Type*} [Field F] [NumberField F]

/-- On an exterior `𝔟`: `N𝔟/N𝔡 ≥ 1`, `N𝔡 ≥ 1`, and their product is `N𝔟`. -/
lemma L2D_norm_facts (𝔟 : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) :
    1 ≤ (Ideal.absNorm 𝔟 : ℝ) / Ideal.absNorm (simplePart 𝔟) ∧
      1 ≤ (Ideal.absNorm (simplePart 𝔟) : ℝ) ∧
      (Ideal.absNorm 𝔟 : ℝ) / Ideal.absNorm (simplePart 𝔟) *
        Ideal.absNorm (simplePart 𝔟) = Ideal.absNorm 𝔟 := by
  have hd := L2D_simplePart_dvd 𝔟 h𝔟
  have hdne : simplePart 𝔟 ≠ ⊥ := by
    rintro h; rw [h] at hd
    exact h𝔟 (by simpa using zero_dvd_iff.1 (show (0 : Ideal (𝓞 F)) ∣ 𝔟 from hd))
  have hN : Ideal.absNorm 𝔟 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hNd : Ideal.absNorm (simplePart 𝔟) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hdvd : Ideal.absNorm (simplePart 𝔟) ∣ Ideal.absNorm 𝔟 :=
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hd)
  have hle : Ideal.absNorm (simplePart 𝔟) ≤ Ideal.absNorm 𝔟 :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdvd
  have hpos : (0 : ℝ) < Ideal.absNorm (simplePart 𝔟) := by exact_mod_cast Nat.pos_of_ne_zero hNd
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hpos, one_mul]; exact_mod_cast hle
  · exact_mod_cast Nat.one_le_iff_ne_zero.2 hNd
  · field_simp

/-- The count of dyads: `(log₂ ⌊c Z^E⌋ + 1)^2 ≤ A^2 Z^{4δ/2}`, i.e. `≤ A^2 Z^{2δ}`. -/
lemma L2D_log_count (c E δ : ℝ) (hE : 0 ≤ E) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ Z : ℝ, 2 ≤ Z →
      ((Nat.log 2 ⌊c * Z ^ E⌋₊ + 1 : ℕ) : ℝ) ^ 2 ≤ A ^ 2 * Z ^ (2 * δ) := by
  set A : ℝ := 1 + (Real.log (|c| + 1) + E / δ) / Real.log 2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc1 : 0 ≤ Real.log (|c| + 1) := Real.log_nonneg (by linarith [abs_nonneg c])
  have hA0 : 0 ≤ A := by
    have : 0 ≤ (Real.log (|c| + 1) + E / δ) / Real.log 2 := by positivity
    linarith
  refine ⟨A, hA0, fun Z hZ => ?_⟩
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hZδ : 1 ≤ Z ^ δ := Real.one_le_rpow hZ1 hδ.le
  have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  set K := Nat.log 2 ⌊c * Z ^ E⌋₊
  -- K log 2 ≤ log(|c|+1) + E log Z
  have hK : (K : ℝ) * Real.log 2 ≤ Real.log (|c| + 1) + E * Real.log Z := by
    by_cases h0 : ⌊c * Z ^ E⌋₊ = 0
    · have : K = 0 := by simp [K, h0]
      rw [this]; simp; positivity
    · have h1 : (2 : ℝ) ^ K ≤ c * Z ^ E := by
        calc (2 : ℝ) ^ K = ((2 ^ K : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (⌊c * Z ^ E⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 h0
          _ ≤ c * Z ^ E := Nat.floor_le (by
              by_contra hneg; push Not at hneg
              exact h0 (Nat.floor_eq_zero.2 (by linarith)))
      have hZE : 0 < Z ^ E := Real.rpow_pos_of_pos hZ0 E
      have h2 : c * Z ^ E ≤ (|c| + 1) * Z ^ E := by
        apply mul_le_mul_of_nonneg_right _ hZE.le; linarith [le_abs_self c]
      have h3 := Real.log_le_log (by positivity) (h1.trans h2)
      rw [Real.log_pow, Real.log_mul (by positivity) hZE.ne', Real.log_rpow hZ0] at h3
      exact h3
  have hlog := Real.log_le_rpow_div hZ0.le hδ
  have hK1 : ((K + 1 : ℕ) : ℝ) ≤ A * Z ^ δ := by
    push_cast
    have : (K : ℝ) ≤ (Real.log (|c| + 1) + E / δ * Z ^ δ) / Real.log 2 := by
      rw [le_div_iff₀ hl2]
      calc (K : ℝ) * Real.log 2 ≤ Real.log (|c| + 1) + E * Real.log Z := hK
        _ ≤ Real.log (|c| + 1) + E * (Z ^ δ / δ) := by gcongr
        _ = Real.log (|c| + 1) + E / δ * Z ^ δ := by ring
    have h4 : (Real.log (|c| + 1) + E / δ * Z ^ δ) / Real.log 2 ≤
        (Real.log (|c| + 1) + E / δ) / Real.log 2 * Z ^ δ := by
      have : 0 ≤ E / δ := by positivity
      have hnum : Real.log (|c| + 1) + E / δ * Z ^ δ ≤ (Real.log (|c| + 1) + E / δ) * Z ^ δ := by
        nlinarith
      rw [show (Real.log (|c| + 1) + E / δ) / Real.log 2 * Z ^ δ =
        (Real.log (|c| + 1) + E / δ) * Z ^ δ / Real.log 2 by ring]
      exact div_le_div_of_nonneg_right hnum hl2.le
    calc (K : ℝ) + 1 ≤ (Real.log (|c| + 1) + E / δ) / Real.log 2 * Z ^ δ + Z ^ δ := by linarith
      _ = A * Z ^ δ := by simp only [A]; ring
  have hpos : (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by positivity
  calc ((K + 1 : ℕ) : ℝ) ^ 2 ≤ (A * Z ^ δ) ^ 2 := by gcongr
    _ = A ^ 2 * Z ^ (2 * δ) := by
      rw [mul_pow, ← Real.rpow_natCast (Z ^ δ), ← Real.rpow_mul hZ0.le]; norm_num [mul_comm]

/-- The dyad bound: on a dyad with `P D ≤ c Z^E`, `P^{1/2}(D + D^2 P/Z) ≤ (|c| + c^2) Z^{2E-1}`. -/
lemma L2D_dyad_bound (c E Z P D : ℝ) (hE : 1 ≤ E) (hZ : 1 ≤ Z) (hP : 1 ≤ P) (hD : 1 ≤ D)
    (hPD : P * D ≤ c * Z ^ E) :
    P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z) ≤ (|c| + c ^ 2) * Z ^ (2 * E - 1) := by
  have hZ0 : 0 < Z := by linarith
  have hsq : P ^ ((1 : ℝ) / 2) ≤ P := by
    calc P ^ ((1 : ℝ) / 2) ≤ P ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
      _ = P := Real.rpow_one P
  have hsq0 : 0 ≤ P ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have hB0 : 1 ≤ c * Z ^ E := by nlinarith
  have hZE : Z ^ E ≤ Z ^ (2 * E - 1) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hZ2 : Z ^ (2 * E - 1) = (Z ^ E) ^ 2 / Z := by
    rw [Real.rpow_sub hZ0, Real.rpow_one, ← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
    norm_num
    ring_nf
  have h1 : P ^ ((1 : ℝ) / 2) * D ≤ |c| * Z ^ (2 * E - 1) := by
    calc P ^ ((1 : ℝ) / 2) * D ≤ P * D := by gcongr
      _ ≤ c * Z ^ E := hPD
      _ ≤ |c| * Z ^ E := by gcongr; exact le_abs_self c
      _ ≤ |c| * Z ^ (2 * E - 1) := by gcongr
  have h2 : P ^ ((1 : ℝ) / 2) * (D ^ 2 * P / Z) ≤ c ^ 2 * Z ^ (2 * E - 1) := by
    rw [hZ2]
    have hPD0 : 0 ≤ P * D := by positivity
    calc P ^ ((1 : ℝ) / 2) * (D ^ 2 * P / Z) ≤ P * (D ^ 2 * P / Z) := by
          gcongr
      _ = (P * D) ^ 2 / Z := by ring
      _ ≤ (c * Z ^ E) ^ 2 / Z := by gcongr
      _ = c ^ 2 * ((Z ^ E) ^ 2 / Z) := by ring
  nlinarith

theorem L2D_chk_of_cut45 (n : ℕ) (_hn0 : 0 < n) (_hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (h45 : L2D_Cut45 n F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (c₁ c₂ ε : ℝ), 0 < c₁ → 0 < ε →
        ∃ C : ℝ, ∀ Z : ℝ, 2 ≤ Z →
          (∀ P D : ℝ, 1 ≤ P → 1 ≤ D →
            ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 //
                c₁ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
                (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000) ∧
                P ≤ (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) ∧
                (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) < 2 * P ∧
                D ≤ (Ideal.absNorm (simplePart r.1.1) : ℝ) ∧
                (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D} =>
                  ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
              σ ≤ C * Z ^ ε * P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z)) ∧
          ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 //
              c₁ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
              (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000)} =>
                ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
            σ ≤ C * Z ^ (2 * ((1033 : ℝ) / 1000) - 1 + ε) := by
  obtain ⟨N₀, hN₀⟩ := h45
  refine ⟨N₀, fun 𝔪 h𝔪 hsp χ g c₁ c₂ ε hc₁ hε => ?_⟩
  obtain ⟨C, hC⟩ := hN₀ 𝔪 h𝔪 hsp χ g c₁ c₂ (ε / 2) hc₁ (by positivity)
  set E : ℝ := (1033 : ℝ) / 1000 with hEdef
  obtain ⟨A, hA0, hA⟩ := L2D_log_count c₂ E (ε / 4) (by norm_num [E]) (by positivity)
  refine ⟨|C| + A ^ 2 * |C| * (|c₂| + c₂ ^ 2), fun Z hZ => ⟨?_, ?_⟩⟩
  · intro P D hP hD
    obtain ⟨σ, hσ, hσle⟩ := hC Z hZ P D hP hD
    refine ⟨σ, hσ, ?_⟩
    have hZ1 : 1 ≤ Z := by linarith
    have hX : 0 ≤ P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z) := by
      have : 0 ≤ P := by linarith
      positivity
    have hZε : Z ^ (ε / 2) ≤ Z ^ ε := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
    have hZε0 : 0 ≤ Z ^ (ε / 2) := Real.rpow_nonneg (by linarith) _
    have hextra : 0 ≤ A ^ 2 * |C| * (|c₂| + c₂ ^ 2) := by positivity
    calc σ ≤ C * Z ^ (ε / 2) * P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z) := hσle
      _ = C * (Z ^ (ε / 2) * (P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z))) := by ring
      _ ≤ |C| * (Z ^ (ε / 2) * (P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z))) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (Z ^ ε * (P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z))) := by gcongr
      _ ≤ (|C| + A ^ 2 * |C| * (|c₂| + c₂ ^ 2)) *
            (Z ^ ε * (P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z))) := by
          gcongr; linarith
      _ = (|C| + A ^ 2 * |C| * (|c₂| + c₂ ^ 2)) * Z ^ ε * P ^ ((1 : ℝ) / 2) *
            (D + D ^ 2 * P / Z) := by ring
  · have hZ1 : 1 ≤ Z := by linarith
    have hZ0 : 0 < Z := by linarith
    set M : ℝ := |C| * Z ^ (ε / 2) * ((|c₂| + c₂ ^ 2) * Z ^ (2 * E - 1)) with hMdef
    have hM : 0 ≤ M := by
      have := Real.rpow_nonneg hZ0.le (ε / 2)
      have := Real.rpow_nonneg hZ0.le (2 * E - 1)
      positivity
    obtain ⟨σ, hσ, hσle⟩ := L2D_dyadic_sum
      (fun r : RowClass 𝔪 => ‖χ.thetaSum g (rowElt g r) Z‖ ^ 2)
      (fun r => c₁ * Z ^ E ≤ Ideal.absNorm r.1.1 ∧
        (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ E)
      (fun r => (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1))
      (fun r => (Ideal.absNorm (simplePart r.1.1) : ℝ)) (c₂ * Z ^ E) M hM
      (fun r hr => by
        obtain ⟨a, b, c⟩ := L2D_norm_facts r.1.1 r.1.2.1
        refine ⟨a, b, ?_⟩
        rw [c]; exact hr.2)
      (fun P D r => c₁ * Z ^ E ≤ Ideal.absNorm r.1.1 ∧
              (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ E ∧
              P ≤ (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) ∧
              (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) < 2 * P ∧
              D ≤ (Ideal.absNorm (simplePart r.1.1) : ℝ) ∧
              (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D)
      (fun P D r => by simp only [and_assoc])
      (fun P D hP hD hPD => by
        obtain ⟨σ, hσ, hσle⟩ := hC Z hZ P D hP hD
        refine ⟨σ, hσ, ?_⟩
        have hb := L2D_dyad_bound c₂ E Z P D (by norm_num [E]) hZ1 hP hD hPD
        have hZε0 : 0 ≤ Z ^ (ε / 2) := Real.rpow_nonneg hZ0.le _
        calc σ ≤ C * Z ^ (ε / 2) * P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z) := hσle
          _ = C * (Z ^ (ε / 2) * (P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z))) := by ring
          _ ≤ |C| * (Z ^ (ε / 2) * (P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z))) := by
              apply mul_le_mul_of_nonneg_right (le_abs_self C)
              have : 0 ≤ P := by linarith
              positivity
          _ ≤ |C| * (Z ^ (ε / 2) * ((|c₂| + c₂ ^ 2) * Z ^ (2 * E - 1))) := by gcongr
          _ = M := by rw [hMdef]; ring)
    refine ⟨σ, hσ, ?_⟩
    have hcount := hA Z hZ
    have hZsplit : Z ^ (2 * E - 1 + ε) = Z ^ (2 * (ε / 4)) * Z ^ (ε / 2) * Z ^ (2 * E - 1) := by
      rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]; ring_nf
    have hM0 : 0 ≤ |C| * (|c₂| + c₂ ^ 2) * Z ^ (ε / 2) * Z ^ (2 * E - 1) := by
      have := Real.rpow_nonneg hZ0.le (ε / 2)
      have := Real.rpow_nonneg hZ0.le (2 * E - 1)
      positivity
    have hZ2 : 0 ≤ Z ^ (2 * E - 1 + ε) := Real.rpow_nonneg hZ0.le _
    calc σ ≤ ((Nat.log 2 ⌊c₂ * Z ^ E⌋₊ + 1 : ℕ) : ℝ) ^ 2 * M := hσle
      _ ≤ (A ^ 2 * Z ^ (2 * (ε / 4))) * M := by gcongr
      _ = A ^ 2 * |C| * (|c₂| + c₂ ^ 2) * Z ^ (2 * E - 1 + ε) := by
          rw [hZsplit, hMdef]; ring
      _ ≤ (|C| + A ^ 2 * |C| * (|c₂| + c₂ ^ 2)) * Z ^ (2 * E - 1 + ε) := by
          gcongr; linarith [abs_nonneg C]

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

/-! L2D: C1b (Prop 4.1) from its dyadic conjunct (4.5). -/

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open NumberField
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (c₁ c₂ ε : ℝ), 0 < c₁ → 0 < ε →
        ∃ C : ℝ, ∀ Z : ℝ, 2 ≤ Z →
          (∀ P D : ℝ, 1 ≤ P → 1 ≤ D →
            ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 //
                c₁ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
                (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000) ∧
                P ≤ (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) ∧
                (Ideal.absNorm r.1.1 : ℝ) / Ideal.absNorm (simplePart r.1.1) < 2 * P ∧
                D ≤ (Ideal.absNorm (simplePart r.1.1) : ℝ) ∧
                (Ideal.absNorm (simplePart r.1.1) : ℝ) < 2 * D} =>
                  ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
              σ ≤ C * Z ^ ε * P ^ ((1 : ℝ) / 2) * (D + D ^ 2 * P / Z)) ∧
          ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 //
              c₁ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
              (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000)} =>
                ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
            σ ≤ C * Z ^ (2 * ((1033 : ℝ) / 1000) - 1 + ε) :=
  L2D_chk_of_cut45 n hn0 hn F ι (exists_cutoff_tsum_norm_sq_thetaSum_dyadic_le n hn0 hn F ι)
end
