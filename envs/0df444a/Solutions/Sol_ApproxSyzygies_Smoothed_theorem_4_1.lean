-- Prove2me | solution 1 for ApproxSyzygies.Smoothed.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-21T00:57:22.011446+00:00
-- url     : https://prove2.me/submissions/c7e97b4a-ed92-4585-ac70-f963be4f4150

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Bombieri
import Definitions.Def_ApproxSyzygies_Smoothed_Anticoncentration
import Theorems.Thm_ApproxSyzygies_Smoothed_theorem_4_6
import Theorems.Thm_ApproxSyzygies_Smoothed_lemma_4_2
import Theorems.Thm_ApproxSyzygies_Smoothed_lemma_4_3
import Theorems.Thm_ApproxSyzygies_Smoothed_lemma_4_7
import Theorems.Thm_ApproxSyzygies_Smoothed_lemma_a_2
import Theorems.Thm_ApproxSyzygies_Smoothed_lemma_4_4
section
/-! # Blueprint for Theorem 4.1 (paper §4.6): definitions

Everything here is a concrete definition (no `sorry`). The variable type `σ` is arbitrary; the
split used in the induction step is `σ = Y ⊕ (Fin L × Fin q)`, `Y = Fin k`, with block `ℓ` of the
`z`-variables being `{ℓ} × Fin q`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.G41

open ApproxSyzygies.Smoothed

section General

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- `gaussCoeffs` over an arbitrary finite variable type (`gaussOn (Fin n) = gaussCoeffs n`
definitionally). -/
noncomputable def gaussOn (σ : Type) [Fintype σ] [DecidableEq σ] (m : ℕ) (d : Fin m → ℤ) :
    Measure ((i : Fin m) → monos σ (d i) → ℝ) :=
  Measure.pi fun i => Measure.pi fun _ : monos σ (d i) => gaussianReal 0 1

/-- `perturb` over an arbitrary finite variable type (`perturbOn = perturb` on `Fin n`). -/
noncomputable def perturbOn {d : ℤ} (abar : Hom σ d) (ρ : ℝ) (ζ : monos σ d → ℝ) : Hom σ d :=
  abar + ρ • WithLp.toLp 2 ζ

/-- The generators `b_i = a_i^{D_i}`, `a_i = perturbOn (abar i) ρ (ω i)`. -/
noncomputable def bfam {m : ℕ} (d D : Fin m → ℕ) (abar : ∀ i, Hom σ (d i : ℤ)) (ρ : ℝ)
    (ω : ∀ i, monos σ (d i : ℤ) → ℝ) : ∀ i, Hom σ ((d i : ℤ) * (D i : ℕ)) :=
  fun i => powHom (perturbOn (abar i) ρ (ω i)) (D i)

/-- The degree-`t` bad event of Theorem 4.1 with constant `K` (in the theorem `K = n^C ρ^{-C}`):
some `h` has `K ‖M_b^{(t)} h‖ < dist(h, K_b^{(t)})`. -/
def BadT {m : ℕ} (d D : Fin m → ℕ) (abar : ∀ i, Hom σ (d i : ℤ)) (ρ K : ℝ) (t : ℕ) :
    Set (∀ i, monos σ (d i : ℤ) → ℝ) :=
  {ω | ∃ h : Tup σ (fun i => (t : ℤ) - ((d i : ℤ) * (D i : ℕ))),
      K * ‖mulMap (bfam d D abar ρ ω) (t : ℤ) h‖ <
        Metric.infDist h (koszul (bfam d D abar ρ ω) (t : ℤ))}

/-- The Gaussian norm event: `‖ω_i‖ ≤ 2 √N_i`, `N_i = |monos σ d_i|`, for every `i`. -/
def Ngood {m : ℕ} (d : Fin m → ℕ) (ω : ∀ i, monos σ (d i : ℤ) → ℝ) : Prop :=
  ∀ i, ‖(WithLp.toLp 2 (ω i) : Hom σ (d i : ℤ))‖ ≤
    2 * Real.sqrt ((monos σ (d i : ℤ)).card : ℝ)

/-- Rename the variables of a homogeneous polynomial along `e : σ ≃ σ'`. -/
noncomputable def renameHom {σ' : Type} [Fintype σ'] [DecidableEq σ'] (e : σ ≃ σ') {d : ℤ}
    (p : Hom σ d) : Hom σ' d :=
  ofPoly d (rename e (toPoly p))

end General

/-! ### The per-degree statement and the induction -/

/-- The body of `Q(t)` for fixed `ε, d_max, D_max` and constants `C, c, N₀`. -/
def DegBound (t : ℕ) (ε : ℝ) (dmax Dmax : ℕ) (C c : ℝ) (N₀ : ℕ) : Prop :=
  ∀ n : ℕ, N₀ ≤ n → ∀ (m : ℕ) [NeZero m] (d D : Fin m → ℕ),
    (∀ i, 1 ≤ d i ∧ d i ≤ dmax) → (∀ i, 1 ≤ D i ∧ D i ≤ Dmax) →
    ∑ i, (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) ≤ (n : ℝ) ^ (-ε) →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
    ∀ abar : ∀ i, Hom (Fin n) (d i : ℤ), (∀ i, ‖abar i‖ ≤ 1) →
      gaussCoeffs n m (fun i => (d i : ℤ)) (BadT d D abar ρ ((n : ℝ) ^ C * ρ ^ (-C)) t)
        ≤ ENNReal.ofReal
            (Real.exp (-(c * (n : ℝ) ^ (Finset.univ.inf' Finset.univ_nonempty d))))

/-- `Q(t)`: Theorem 4.1 for the single output degree `t`, for every slack `ε` (the induction is
on `t`; the step uses `Q(s)`, `s < t`, with the smaller slack `min(ε/2, 1/2)`). -/
def PerDegree (t : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ dmax Dmax : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
    DegBound t ε dmax Dmax C c N₀

/-- The inductive hypothesis on the pure-`y` coefficients `ωy`, for all degrees `s < t`, for the
family `b[0]` (exponents `D`) and every family `b̃^{(i)}[0]` (exponents `D` with `D_i` replaced
by `1`), all with constant `K`. -/
def IHgood {Y : Type} [Fintype Y] [DecidableEq Y] {m : ℕ} (d D : Fin m → ℕ)
    (abary : ∀ i, Hom Y (d i : ℤ)) (ρ K : ℝ) (t : ℕ) (ωy : ∀ i, monos Y (d i : ℤ) → ℝ) : Prop :=
  ∀ s : ℕ, s < t → ωy ∉ BadT d D abary ρ K s ∧ ∀ i, ωy ∉ BadT d (Function.update D i 1) abary ρ K s

/-- The constant of the reduction step (Lemmas 4.2 + 4.3): `dist(h, K_b) ≤ redConst (‖f‖ + ‖g‖)`
when `τ ≤ τ₀` and `‖b‖ ≤ N`. -/
noncomputable def redConst (t : ℕ) (τ N : ℝ) : ℝ :=
  ((t : ℝ) + 1) * (1 + 2 ^ (t * t) * (1 + τ) ^ t * (1 + N) ^ t) * (2 + τ + τ * N)

/-! ### The coordinate split -/

/-- Number of `z`-blocks: `L = ⌊t/ε⌋ + 1`, so `(L + 1) ε > t`. -/
noncomputable def Lsplit (ε : ℝ) (t : ℕ) : ℕ := ⌊(t : ℝ) / ε⌋₊ + 1

/-- Block size `q = ⌊n / (2L)⌋`. -/
def Qsplit (n L : ℕ) : ℕ := n / (2 * L)

/-- Size of the `y`-variables: `k = n − L q ≥ n/2`. -/
def Ksplit (n L : ℕ) : ℕ := n - L * Qsplit n L

/-- The split variable type `Y ⊕ (Fin L × Fin q)` for `n` variables. -/
abbrev SplitVar (n L : ℕ) : Type := Fin (Ksplit n L) ⊕ (Fin L × Fin (Qsplit n L))

section Split

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

open Classical in
/-- The pure-`y` coordinates of `ω` (Gaussian coefficients of the monomials `y^β`). -/
noncomputable def restrictY {m : ℕ} {d : Fin m → ℤ} (ω : ∀ i, monos (Y ⊕ Z) (d i) → ℝ) :
    ∀ i, monos Y (d i) → ℝ :=
  fun i β => if h : Finsupp.mapDomain Sum.inl (β : Y →₀ ℕ) ∈ monos (Y ⊕ Z) (d i)
    then ω i ⟨_, h⟩ else 0

variable {L q : ℕ}

/-- Restriction to block `ℓ`: `z_{(ℓ', j)} ↦ 0` for `ℓ' ≠ ℓ`, `z_{(ℓ, j)} ↦ z_j`. -/
noncomputable def restr (ℓ : Fin L) {d : ℤ} (p : Hom (Y ⊕ (Fin L × Fin q)) d) :
    Hom (Y ⊕ Fin q) d :=
  ofPoly d (aeval (Sum.elim (fun y => (X (Sum.inl y) : MvPolynomial (Y ⊕ Fin q) ℝ))
    (fun z : Fin L × Fin q => if z.1 = ℓ then X (Sum.inr z.2) else 0)) (toPoly p))

/-- `restr` on tuples. -/
noncomputable def restrTup (ℓ : Fin L) {m : ℕ} {e : Fin m → ℤ}
    (h : Tup (Y ⊕ (Fin L × Fin q)) e) : Tup (Y ⊕ Fin q) e :=
  WithLp.toLp 2 fun i => restr ℓ (h i)

open Classical in
/-- Replace the block coordinates of `ω₀` by `u` (all blocks at once); every other coordinate is
taken from `ω₀`. -/
noncomputable def replaceV {m : ℕ} {d : Fin m → ℤ}
    (ω₀ : ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i) → ℝ)
    (u : Fin L → ∀ i, monos (Fin q) (d i) → ℝ) :
    ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i) → ℝ :=
  fun i β =>
    if h : ∃ p : Fin L × (Fin q →₀ ℕ),
        Finsupp.mapDomain (fun j => (Sum.inr (p.1, j) : Y ⊕ (Fin L × Fin q))) p.2 = β.1 then
      if h2 : h.choose.2 ∈ monos (Fin q) (d i) then u h.choose.1 i ⟨_, h2⟩ else ω₀ i β
    else ω₀ i β

/-- The law of the block coordinates: independent standard Gaussians. -/
noncomputable def gaussV (L q : ℕ) {m : ℕ} (d : Fin m → ℤ) :
    Measure (Fin L → ∀ i, monos (Fin q) (d i) → ℝ) :=
  Measure.pi fun _ : Fin L => Measure.pi fun i => Measure.pi fun _ : monos (Fin q) (d i) =>
    gaussianReal 0 1

/-- The tensor identification of the `z`-degree-`R` part of `ℝ[y, z]_{=t}`:
`(toTens R t p)_{(α, β)} = √(binom(t, R)) p_{z^α y^β}` (`|α| = R`, `|β| = t − R`). It maps
`ofPoly t (rename inr (toPoly ζ) * rename inl (toPoly g))` to `tens ζ g` exactly, and
`‖toTens R t p‖ ≤ √(binom(t, R)) ‖p‖`. -/
noncomputable def toTens (R t : ℤ) :
    Hom (Y ⊕ Z) t →ₗ[ℝ] EuclideanSpace ℝ (monos Z R × monos Y (t - R)) where
  toFun p := WithLp.toLp 2 fun ab =>
    Real.sqrt ((t.toNat.choose R.toNat : ℕ) : ℝ) *
      (if h : Finsupp.sumElim (ab.2 : Y →₀ ℕ) (ab.1 : Z →₀ ℕ) ∈ monos (Y ⊕ Z) t
        then p ⟨_, h⟩ else 0)
  map_add' p p' := by
    ext ab
    simp only [PiLp.add_apply]
    split_ifs <;> ring
  map_smul' c p := by
    ext ab
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

end Split

end ApproxSyzygies.Smoothed.Dev.G41
end

section
open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.A1

open ApproxSyzygies.Smoothed

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma mem_monos_nat (d : ℕ) (α : σ →₀ ℕ) : α ∈ monos σ (d : ℤ) ↔ ∑ i, α i = d := by
  simp [monos, Finset.mem_finsuppAntidiag]

lemma monos_neg (d : ℤ) (h : d < 0) : monos σ d = ∅ := by
  simp [monos, not_le.2 h]

lemma mfact_pos (α : σ →₀ ℕ) : 0 < mfact α := by
  unfold mfact
  exact Finset.prod_pos fun i _ => by positivity

lemma coeff_toPoly (d : ℕ) (p : Hom σ (d : ℤ)) (α : σ →₀ ℕ) :
    coeff α (toPoly p) =
      if h : α ∈ monos σ (d : ℤ) then p ⟨α, h⟩ * Real.sqrt ((d.factorial : ℝ) / mfact α) else 0 := by
  unfold toPoly
  rw [coeff_sum]
  simp only [coeff_smul, bmono, coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨α, h⟩]
    · have : Finsupp.degree α = d := by
        rw [Finsupp.degree_eq_sum]; exact (mem_monos_nat d α).1 h
      simp [this]
    · intro b _ hb
      have : (b : σ →₀ ℕ) ≠ α := fun e => hb (Subtype.ext e)
      simp [this]
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    have : (b : σ →₀ ℕ) ≠ α := fun e => h (e ▸ b.2)
    simp [this]

lemma normsq_ofPoly (e : ℤ) (f : MvPolynomial σ ℝ) :
    ‖ofPoly e f‖ ^ 2 = ∑ α ∈ monos σ e, (coeff α f) ^ 2 * mfact α / (e.toNat.factorial : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [← Finset.sum_coe_sort (monos σ e)]
  apply Finset.sum_congr rfl
  intro α _
  simp only [ofPoly, Real.norm_eq_abs, sq_abs, mul_pow]
  rw [Real.sq_sqrt (div_nonneg (mfact_pos _).le (by positivity))]
  ring

lemma normsq_hom (d : ℕ) (p : Hom σ (d : ℤ)) :
    ‖p‖ ^ 2 = ∑ α ∈ monos σ (d : ℤ), (coeff α (toPoly p)) ^ 2 * mfact α / (d.factorial : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_coe_sort (monos σ (d : ℤ))]
  apply Finset.sum_congr rfl
  intro α _
  rw [coeff_toPoly, dif_pos α.2]
  simp only [Real.norm_eq_abs, sq_abs, mul_pow]
  rw [Real.sq_sqrt (div_nonneg (by positivity) (mfact_pos _).le)]
  have := mfact_pos (α : σ →₀ ℕ)
  have h2 : (0:ℝ) < d.factorial := by positivity
  field_simp


lemma vand_nat (γ : σ →₀ ℕ) (d1 : ℕ) :
    ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset σ) d1, ∏ i, (γ i).choose (l i) =
      (∑ i, γ i).choose d1 := by
  have h1 : (((∏ i : σ, ((1 + Polynomial.X : Polynomial ℕ) ^ (γ i)) : Polynomial ℕ)) :
      PowerSeries ℕ) = ∏ i : σ, ((((1 + Polynomial.X : Polynomial ℕ) ^ (γ i) : Polynomial ℕ)) :
      PowerSeries ℕ) := map_prod (Polynomial.coeToPowerSeries.ringHom) _ _
  have h2 : (∏ i : σ, ((1 + Polynomial.X : Polynomial ℕ) ^ (γ i))) =
      (1 + Polynomial.X : Polynomial ℕ) ^ (∑ i, γ i) := Finset.prod_pow_eq_pow_sum _ _ _
  have h3 := PowerSeries.coeff_prod (fun i => ((((1 + Polynomial.X : Polynomial ℕ) ^ (γ i) :
      Polynomial ℕ)) : PowerSeries ℕ)) d1 Finset.univ
  rw [← h1, h2, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow] at h3
  rw [Nat.cast_id] at h3
  rw [h3]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, Nat.cast_id]

lemma vand (γ : σ →₀ ℕ) (d1 : ℕ) :
    ∑ α ∈ monos σ (d1 : ℤ), ∏ i, ((γ i).choose (α i) : ℝ) = ((∑ i, γ i).choose d1 : ℝ) := by
  have := vand_nat γ d1
  have h : monos σ (d1 : ℤ) = Finset.finsuppAntidiag (Finset.univ : Finset σ) d1 := by
    simp [monos]
  rw [h]
  exact_mod_cast this


lemma sum_add_apply (x y : σ →₀ ℕ) : ∑ i, (x + y) i = ∑ i, x i + ∑ i, y i := by
  simp [Finsupp.add_apply, Finset.sum_add_distrib]

lemma mfact_split (α γ : σ →₀ ℕ) (h : α ≤ γ) :
    mfact γ = (∏ i, ((γ i).choose (α i) : ℝ)) * mfact α * mfact (γ - α) := by
  unfold mfact
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hi : α i ≤ γ i := h i
  have := Nat.choose_mul_factorial_mul_factorial hi
  simp only [Finsupp.tsub_apply]
  exact_mod_cast this.symm

lemma coeff_mul_eq (d1 : ℕ) (f g : MvPolynomial σ ℝ)
    (hf : ∀ α, α ∉ monos σ (d1 : ℤ) → coeff α f = 0) (γ : σ →₀ ℕ) :
    coeff γ (f * g) = ∑ α ∈ (monos σ (d1 : ℤ)).filter (· ≤ γ), coeff α f * coeff (γ - α) g := by
  rw [coeff_mul]
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.1) ?_ ?_ ?_ ?_
  · intro x hx hne
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · by_contra hn
      apply hne
      rw [hf _ hn, zero_mul]
    · rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [← hx]; exact le_self_add
  · intro x hx _ y hy _ h
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
    have h1 : x.1 = y.1 := h
    ext1
    · exact h1
    · have : x.2 = y.2 := by
        have := hx.trans hy.symm
        rw [h1] at this
        exact add_left_cancel this
      exact this
  · intro α hα hne
    rw [Finset.mem_filter] at hα
    refine ⟨(α, γ - α), ?_, hne, rfl⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    exact add_tsub_cancel_of_le hα.2
  · intro x hx _
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have : γ - x.1 = x.2 := by rw [← hx]; exact add_tsub_cancel_left _ _
    simp [this]

lemma sum_double (d1 d2 : ℕ) (K : (σ →₀ ℕ) → (σ →₀ ℕ) → ℝ) :
    ∑ γ ∈ monos σ ((d1 + d2 : ℕ) : ℤ), ∑ α ∈ (monos σ (d1 : ℤ)).filter (· ≤ γ), K α (γ - α) =
      ∑ α ∈ monos σ (d1 : ℤ), ∑ β ∈ monos σ (d2 : ℤ), K α β := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α hα
  rw [← Finset.sum_filter]
  rw [mem_monos_nat] at hα
  symm
  refine Finset.sum_nbij' (fun β => α + β) (fun γ => γ - α) ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    rw [mem_monos_nat] at hβ
    rw [Finset.mem_filter, mem_monos_nat, sum_add_apply, hα, hβ]
    exact ⟨rfl, le_self_add⟩
  · intro γ hγ
    rw [Finset.mem_filter, mem_monos_nat] at hγ
    rw [mem_monos_nat]
    have h := sum_add_apply (γ - α) α
    rw [tsub_add_cancel_of_le hγ.2, hγ.1, hα] at h
    omega
  · intro β _; exact add_tsub_cancel_left _ _
  · intro γ hγ
    rw [Finset.mem_filter] at hγ
    exact add_tsub_cancel_of_le hγ.2
  · intro β _
    rw [add_tsub_cancel_left]


lemma part3 (d1 d2 : ℕ) (p : Hom σ (d1 : ℤ)) (q : Hom σ (d2 : ℤ)) :
    ‖ofPoly ((d1 : ℤ) + d2) (toPoly p * toPoly q)‖ ≤ ‖p‖ * ‖q‖ := by
  have e : ((d1 : ℤ) + d2) = ((d1 + d2 : ℕ) : ℤ) := by push_cast; ring
  set a : (σ →₀ ℕ) → ℝ := fun α => coeff α (toPoly p) with ha
  set b : (σ →₀ ℕ) → ℝ := fun α => coeff α (toPoly q) with hb
  have hfa : ∀ α, α ∉ monos σ (d1 : ℤ) → coeff α (toPoly p) = 0 := by
    intro α h; rw [coeff_toPoly, dif_neg h]
  set K : (σ →₀ ℕ) → (σ →₀ ℕ) → ℝ := fun α β =>
    a α ^ 2 * mfact α / (d1.factorial : ℝ) * (b β ^ 2 * mfact β / (d2.factorial : ℝ)) with hK
  have hR : (‖p‖ * ‖q‖) ^ 2 = ∑ α ∈ monos σ (d1 : ℤ), ∑ β ∈ monos σ (d2 : ℤ), K α β := by
    rw [mul_pow, normsq_hom d1 p, normsq_hom d2 q, Finset.sum_mul_sum]
  have hL : ‖ofPoly ((d1 : ℤ) + d2) (toPoly p * toPoly q)‖ ^ 2 ≤
      ∑ α ∈ monos σ (d1 : ℤ), ∑ β ∈ monos σ (d2 : ℤ), K α β := by
    rw [e, normsq_ofPoly, Int.toNat_natCast, ← sum_double d1 d2 K]
    apply Finset.sum_le_sum
    intro γ hγ
    rw [mem_monos_nat] at hγ
    set T := (monos σ (d1 : ℤ)).filter (· ≤ γ) with hT
    rw [coeff_mul_eq d1 _ _ hfa γ]
    set w : (σ →₀ ℕ) → ℝ := fun α => ∏ i, ((γ i).choose (α i) : ℝ) with hw
    have hwpos : ∀ α ∈ T, 0 < w α := by
      intro α hα
      have hle : α ≤ γ := (Finset.mem_filter.1 hα).2
      apply Finset.prod_pos
      intro i _
      exact_mod_cast Nat.choose_pos (hle i)
    have hwsum : ∑ α ∈ T, w α = ((d1 + d2).choose d1 : ℝ) := by
      rw [← hγ, ← vand γ d1, hT, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro α _
      split_ifs with h
      · rfl
      · symm
        simp only [Finsupp.le_def, not_forall, not_le] at h
        obtain ⟨i, hi⟩ := h
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact_mod_cast Nat.choose_eq_zero_of_lt hi
    have hCpos : (0:ℝ) < ((d1 + d2).choose d1 : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.le_add_right _ _)
    have sed := Finset.sq_sum_div_le_sum_sq_div T (fun α => a α * b (γ - α)) hwpos
    rw [hwsum, div_le_iff₀ hCpos] at sed
    have hfa2 : ((d1 + d2).factorial : ℝ) = ((d1 + d2).choose d1 : ℝ) * d1.factorial * d2.factorial := by
      rw [Nat.choose_symm_add]
      exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial d1 d2).symm
    have hD : (0:ℝ) < ((d1 + d2).factorial : ℝ) := by positivity
    have hmf := mfact_pos γ
    calc (∑ α ∈ T, a α * b (γ - α)) ^ 2 * mfact γ / ((d1 + d2).factorial : ℝ)
        ≤ ((∑ α ∈ T, (a α * b (γ - α)) ^ 2 / w α) * ((d1 + d2).choose d1 : ℝ)) * mfact γ /
            ((d1 + d2).factorial : ℝ) := by gcongr
      _ = ∑ α ∈ T, K α (γ - α) := by
          rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro α hα
          have hle : α ≤ γ := (Finset.mem_filter.1 hα).2
          have h1 := hwpos α hα
          have h2 : mfact γ = w α * mfact α * mfact (γ - α) := mfact_split α γ hle
          have h3 := mfact_pos α
          have h4 := mfact_pos (γ - α)
          have h5 : (0:ℝ) < d1.factorial := by positivity
          have h6 : (0:ℝ) < d2.factorial := by positivity
          rw [h2, hfa2]
          simp only [hK]
          field_simp
  have h2 : ‖ofPoly ((d1 : ℤ) + d2) (toPoly p * toPoly q)‖ ^ 2 ≤ (‖p‖ * ‖q‖) ^ 2 := by
    rw [hR]; exact hL
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

end ApproxSyzygies.Smoothed.Dev.A1

namespace ApproxSyzygies.Smoothed

end ApproxSyzygies.Smoothed
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L43

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1

/-! ### Generic facts about `toPoly`, `ofPoly` and homogeneity -/

section Generic

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- Total degree of a multi-index. -/
def deg (γ : σ →₀ ℕ) : ℕ := ∑ i, γ i

lemma mem_monos_iff (d : ℤ) (γ : σ →₀ ℕ) : γ ∈ monos σ d ↔ ((deg γ : ℕ) : ℤ) = d := by
  unfold monos deg
  split_ifs with h
  · rw [Finset.mem_finsuppAntidiag]
    simp only [Finset.subset_univ, and_true]
    show (∑ i, γ i) = d.toNat ↔ ((∑ i, γ i : ℕ) : ℤ) = d
    omega
  · simp only [Finset.notMem_empty, false_iff]
    omega

/-- Homogeneity of integer degree `d` (forces `f = 0` when `d < 0`). -/
def IsH (d : ℤ) (f : MvPolynomial σ ℝ) : Prop :=
  ∀ γ, coeff γ f ≠ 0 → ((deg γ : ℕ) : ℤ) = d

lemma coeff_toPoly' (d : ℤ) (p : Hom σ d) (α : σ →₀ ℕ) :
    coeff α (toPoly p) =
      if h : α ∈ monos σ d then p ⟨α, h⟩ * Real.sqrt ((d.toNat.factorial : ℝ) / mfact α) else 0 := by
  unfold toPoly
  rw [coeff_sum]
  simp only [coeff_smul, bmono, coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨α, h⟩]
    · have h1 := (mem_monos_iff d α).1 h
      have : Finsupp.degree α = d.toNat := by
        rw [Finsupp.degree_eq_sum]; unfold deg at h1; omega
      simp [this]
    · intro b _ hb
      have : (b : σ →₀ ℕ) ≠ α := fun e => hb (Subtype.ext e)
      simp [this]
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    have : (b : σ →₀ ℕ) ≠ α := fun e => h (e ▸ b.2)
    simp [this]

lemma IsH_toPoly {d : ℤ} (p : Hom σ d) : IsH d (toPoly p) := by
  intro γ h
  rw [coeff_toPoly'] at h
  split_ifs at h with hm
  · exact (mem_monos_iff d γ).1 hm
  · exact absurd rfl h

lemma toPoly_ofPoly (d : ℤ) (f : MvPolynomial σ ℝ) (hf : IsH d f) : toPoly (ofPoly d f) = f := by
  ext γ
  rw [coeff_toPoly']
  split_ifs with hm
  · simp only [ofPoly]
    have h1 := mfact_pos γ
    have h2 : (0:ℝ) < (d.toNat.factorial : ℝ) := by positivity
    rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
    rw [show mfact γ / (d.toNat.factorial : ℝ) * ((d.toNat.factorial : ℝ) / mfact γ) = 1 by
      field_simp]
    simp
  · by_contra hne
    exact hm ((mem_monos_iff d γ).2 (hf γ (Ne.symm hne)))

lemma ofPoly_toPoly {d : ℤ} (p : Hom σ d) : ofPoly d (toPoly p) = p := by
  ext ⟨γ, hγ⟩
  simp only [ofPoly]
  rw [coeff_toPoly', dif_pos hγ]
  have h1 := mfact_pos γ
  have h2 : (0:ℝ) < (d.toNat.factorial : ℝ) := by positivity
  rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
  rw [show (d.toNat.factorial : ℝ) / mfact γ * (mfact γ / (d.toNat.factorial : ℝ)) = 1 by
    field_simp]
  simp

lemma toPoly_inj {d : ℤ} {p q : Hom σ d} (h : toPoly p = toPoly q) : p = q := by
  rw [← ofPoly_toPoly p, h, ofPoly_toPoly]

lemma toPoly_add {d : ℤ} (p q : Hom σ d) : toPoly (p + q) = toPoly p + toPoly q :=
  (toPolyL (σ := σ) d).map_add p q

lemma toPoly_sub {d : ℤ} (p q : Hom σ d) : toPoly (p - q) = toPoly p - toPoly q :=
  (toPolyL (σ := σ) d).map_sub p q

lemma toPoly_zero {d : ℤ} : toPoly (0 : Hom σ d) = 0 :=
  (toPolyL (σ := σ) d).map_zero

lemma toPoly_smul {d : ℤ} (c : ℝ) (p : Hom σ d) : toPoly (c • p) = c • toPoly p :=
  (toPolyL (σ := σ) d).map_smul c p

lemma toPoly_sum {d : ℤ} {ι : Type} (s : Finset ι) (p : ι → Hom σ d) :
    toPoly (∑ i ∈ s, p i) = ∑ i ∈ s, toPoly (p i) :=
  map_sum (toPolyL (σ := σ) d) p s

lemma deg_add (a b : σ →₀ ℕ) : deg (a + b) = deg a + deg b := by
  unfold deg; simp [Finset.sum_add_distrib]

lemma IsH.mul {d d' : ℤ} {f g : MvPolynomial σ ℝ} (hf : IsH d f) (hg : IsH d' g) :
    IsH (d + d') (f * g) := by
  intro γ h
  rw [coeff_mul] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h1 := hf x.1 (left_ne_zero_of_mul hne)
  have h2 := hg x.2 (right_ne_zero_of_mul hne)
  rw [← hx, deg_add]; push_cast; omega

lemma IsH.of_eq {d d' : ℤ} {f : MvPolynomial σ ℝ} (hf : IsH d f) (h : d = d') : IsH d' f := h ▸ hf

lemma toPoly_mulMap {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) (t : ℤ)
    (u : Tup σ (fun i => t - e i)) :
    toPoly (mulMap p t u) = ∑ i, toPoly (p i) * toPoly (u i) := by
  have : mulMap p t u = ∑ i, ofPoly t (toPoly (p i) * toPoly (u i)) := by
    simp [mulMap, LinearMap.sum_apply, ofPolyL, toPolyL]
    rfl
  rw [this, toPoly_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  apply toPoly_ofPoly
  exact ((IsH_toPoly (p i)).mul (IsH_toPoly (u i))).of_eq (by ring)

lemma koszul_add {m : ℕ} {e : Fin m → ℤ} {p : ∀ i, Hom σ (e i)} {t : ℤ}
    {h h' : Tup σ (fun i => t - e i)} (hh : h ∈ koszul p t) (hh' : h' ∈ koszul p t) :
    h + h' ∈ koszul p t := by
  obtain ⟨Ω, h1, h2, h3⟩ := hh
  obtain ⟨Ω', h1', h2', h3'⟩ := hh'
  refine ⟨fun i j => Ω i j + Ω' i j, fun i j => add_mem (h1 i j) (h1' i j), fun i j => ?_, fun i => ?_⟩
  · show Ω i j + Ω' i j = -(Ω j i + Ω' j i)
    rw [h2 i j, h2' i j, neg_add]
  · rw [PiLp.add_apply, toPoly_add, h3 i, h3' i, ← Finset.sum_add_distrib]
    simp [add_mul]

lemma mulMap_koszul {m : ℕ} {e : Fin m → ℤ} {p : ∀ i, Hom σ (e i)} {t : ℤ}
    {h : Tup σ (fun i => t - e i)} (hh : h ∈ koszul p t) : mulMap p t h = 0 := by
  obtain ⟨Ω, _, h2, h3⟩ := hh
  apply toPoly_inj
  rw [toPoly_mulMap, toPoly_zero]
  simp_rw [h3, Finset.mul_sum]
  set S := ∑ i, ∑ j, toPoly (p i) * (Ω i j * toPoly (p j)) with hS
  have : S = -S := by
    conv_lhs => rw [hS, Finset.sum_comm]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h2 i j]; ring
  have h2S : (2 : ℝ) • S = 0 := by rw [two_smul]; nth_rewrite 2 [this]; exact add_neg_cancel S
  exact (smul_eq_zero.1 h2S).resolve_left two_ne_zero

end Generic

/-! ### Splitting variables `x = (y, z)` -/

section Split

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- The `y`-part of a multi-index. -/
noncomputable def yp (γ : (Y ⊕ Z) →₀ ℕ) : Y →₀ ℕ := (Finsupp.sumFinsuppEquivProdFinsupp γ).1
/-- The `z`-part of a multi-index. -/
noncomputable def zp (γ : (Y ⊕ Z) →₀ ℕ) : Z →₀ ℕ := (Finsupp.sumFinsuppEquivProdFinsupp γ).2
/-- Joining a `y`- and a `z`-multi-index. -/
noncomputable def join (β : Y →₀ ℕ) (α : Z →₀ ℕ) : (Y ⊕ Z) →₀ ℕ :=
  Finsupp.sumFinsuppEquivProdFinsupp.symm (β, α)

@[simp] lemma yp_apply (γ : (Y ⊕ Z) →₀ ℕ) (y : Y) : yp γ y = γ (Sum.inl y) := by
  simp [yp, Finsupp.fst_sumFinsuppEquivProdFinsupp]

@[simp] lemma zp_apply (γ : (Y ⊕ Z) →₀ ℕ) (z : Z) : zp γ z = γ (Sum.inr z) := by
  simp [zp, Finsupp.snd_sumFinsuppEquivProdFinsupp]

@[simp] lemma yp_join (β : Y →₀ ℕ) (α : Z →₀ ℕ) : yp (join β α) = β := by
  simp [yp, join]

@[simp] lemma zp_join (β : Y →₀ ℕ) (α : Z →₀ ℕ) : zp (join β α) = α := by
  simp [zp, join]

@[simp] lemma join_yp_zp (γ : (Y ⊕ Z) →₀ ℕ) : join (yp γ) (zp γ) = γ := by
  simp [yp, zp, join]

lemma eq_iff_yp_zp (γ γ' : (Y ⊕ Z) →₀ ℕ) : γ = γ' ↔ yp γ = yp γ' ∧ zp γ = zp γ' := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← join_yp_zp γ, ← join_yp_zp γ', h1, h2]

lemma deg_split (γ : (Y ⊕ Z) →₀ ℕ) : deg γ = deg (yp γ) + deg (zp γ) := by
  unfold deg; rw [Fintype.sum_sum_type]; simp

lemma deg_join (β : Y →₀ ℕ) (α : Z →₀ ℕ) : deg (join β α) = deg β + deg α := by
  rw [deg_split]; simp

lemma zdeg_eq (γ : (Y ⊕ Z) →₀ ℕ) : zdeg γ = deg (zp γ) := by
  simp [zdeg, deg]

lemma mfact_split (γ : (Y ⊕ Z) →₀ ℕ) : mfact γ = mfact (yp γ) * mfact (zp γ) := by
  unfold mfact; rw [Fintype.prod_sum_type]; simp

lemma mfact_join (β : Y →₀ ℕ) (α : Z →₀ ℕ) : mfact (join β α) = mfact β * mfact α := by
  rw [mfact_split]; simp

/-- Reading a polynomial in `x = (y, z)` as a polynomial in `z` with coefficients in `ℝ[y]`. -/
noncomputable def Phi : MvPolynomial (Y ⊕ Z) ℝ →ₐ[ℝ] MvPolynomial Z (MvPolynomial Y ℝ) :=
  aeval (Sum.elim (fun y => C (X y)) (fun z => X z))

lemma Phi_monomial (γ : (Y ⊕ Z) →₀ ℕ) (c : ℝ) :
    Phi (monomial γ c) = monomial (zp γ) (monomial (yp γ) c) := by
  rw [Phi, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  rw [monomial_eq, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [Sum.elim_inl, Sum.elim_inr, yp_apply, zp_apply, map_mul, map_prod, map_pow]
  simp only [MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  ring

/-- The coefficient of `z^α` of a polynomial in `(y, z)`, as a polynomial in `y`. -/
noncomputable def E (α : Z →₀ ℕ) (f : MvPolynomial (Y ⊕ Z) ℝ) : MvPolynomial Y ℝ :=
  coeff α (Phi f)

lemma coeff_E (f : MvPolynomial (Y ⊕ Z) ℝ) (γ : (Y ⊕ Z) →₀ ℕ) :
    coeff γ f = coeff (yp γ) (E (zp γ) f) := by
  unfold E
  induction f using MvPolynomial.induction_on' with
  | monomial γ' c =>
    rw [Phi_monomial, coeff_monomial, coeff_monomial]
    by_cases h : γ' = γ
    · subst h; simp
    · rw [if_neg h]
      rw [eq_iff_yp_zp] at h
      by_cases hz : zp γ' = zp γ
      · rw [if_pos hz, coeff_monomial, if_neg (fun h' => h ⟨h', hz⟩)]
      · rw [if_neg hz]; simp
  | add p q hp hq => simp [hp, hq]

lemma coeff_E_join (f : MvPolynomial (Y ⊕ Z) ℝ) (β : Y →₀ ℕ) (α : Z →₀ ℕ) :
    coeff β (E α f) = coeff (join β α) f := by
  rw [coeff_E]; simp

lemma E_add (α : Z →₀ ℕ) (f g : MvPolynomial (Y ⊕ Z) ℝ) : E α (f + g) = E α f + E α g := by
  simp [E]

lemma E_sum {ι : Type} (α : Z →₀ ℕ) (s : Finset ι) (f : ι → MvPolynomial (Y ⊕ Z) ℝ) :
    E α (∑ i ∈ s, f i) = ∑ i ∈ s, E α (f i) := by
  simp [E, map_sum, coeff_sum]

lemma ext_E {f g : MvPolynomial (Y ⊕ Z) ℝ} (h : ∀ α, E α f = E α g) : f = g := by
  ext γ; rw [coeff_E, coeff_E, h]

lemma hom_ext_E {d : ℤ} {x x' : Hom (Y ⊕ Z) d}
    (h : ∀ α, E α (toPoly x) = E α (toPoly x')) : x = x' :=
  toPoly_inj (ext_E h)

lemma Phi_rename_inl (g : MvPolynomial Y ℝ) : Phi (rename Sum.inl g : MvPolynomial (Y ⊕ Z) ℝ) = C g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [Phi, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p y hp => rw [map_mul, rename_X, map_mul, hp]; simp [Phi]

lemma E_rename_inl_mul (α : Z →₀ ℕ) (g : MvPolynomial Y ℝ) (f : MvPolynomial (Y ⊕ Z) ℝ) :
    E α (rename Sum.inl g * f) = g * E α f := by
  simp [E, Phi_rename_inl, coeff_C_mul]

lemma E_rename_inl (α : Z →₀ ℕ) (g : MvPolynomial Y ℝ) :
    E α (rename Sum.inl g : MvPolynomial (Y ⊕ Z) ℝ) = if α = 0 then g else 0 := by
  simp [E, Phi_rename_inl, coeff_C, eq_comm]

/-- The monomial `z^α` in `ℝ[y, z]`. -/
noncomputable def zmon (α : Z →₀ ℕ) : MvPolynomial (Y ⊕ Z) ℝ := monomial (join (0 : Y →₀ ℕ) α) 1

lemma Phi_zmon (α : Z →₀ ℕ) : Phi (zmon (Y := Y) α) = monomial α 1 := by
  simp [zmon, Phi_monomial]

lemma E_zmon_mul (α α' : Z →₀ ℕ) (f : MvPolynomial (Y ⊕ Z) ℝ) :
    E α' (zmon α * f) = if α ≤ α' then E (α' - α) f else 0 := by
  simp only [E, map_mul, Phi_zmon]
  rw [coeff_monomial_mul']
  split_ifs <;> simp

lemma E_zmon_mul_rename (α α' : Z →₀ ℕ) (g : MvPolynomial Y ℝ) :
    E α' (zmon α * rename Sum.inl g) = if α = α' then g else 0 := by
  rw [E_zmon_mul]
  split_ifs with h1 h2 h2
  · rw [E_rename_inl, if_pos (by rw [h2, tsub_self])]
  · rw [E_rename_inl, if_neg]
    intro h; apply h2
    exact le_antisymm h1 (tsub_eq_zero_iff_le.1 h)
  · exact absurd (h2 ▸ le_refl α) h1
  · rfl

lemma IsH_E {d : ℤ} {f : MvPolynomial (Y ⊕ Z) ℝ} (hf : IsH d f) (α : Z →₀ ℕ) :
    IsH (d - deg α) (E α f) := by
  intro β h
  rw [coeff_E_join] at h
  have := hf _ h
  rw [deg_join] at this; push_cast at this; omega

lemma IsH_rename_inl {d : ℤ} {g : MvPolynomial Y ℝ} (hg : IsH d g) :
    IsH d (rename Sum.inl g : MvPolynomial (Y ⊕ Z) ℝ) := by
  intro γ h
  rw [coeff_E, E_rename_inl] at h
  split_ifs at h with hz
  · have := hg _ h
    rw [deg_split, hz]; simpa [deg] using this
  · exact absurd (coeff_zero _) h

/-! ### `grade`, `yPart`, `liftY` in terms of `E` -/

lemma E_grade (r : ℕ) {d : ℤ} (f : Hom (Y ⊕ Z) d) (α : Z →₀ ℕ) :
    E α (toPoly (grade r f)) = if deg α = r then E α (toPoly f) else 0 := by
  ext β
  rw [coeff_E_join]
  split_ifs with h
  · rw [coeff_E_join, coeff_toPoly', coeff_toPoly']
    split_ifs with hm
    · simp [grade, zdeg_eq, h]
    · rfl
  · rw [coeff_toPoly']
    split_ifs with hm
    · simp [grade, zdeg_eq, h]
    · simp

lemma aeval_elim_eq_E (g : MvPolynomial (Y ⊕ Z) ℝ) :
    aeval (Sum.elim X (fun _ : Z => (0 : MvPolynomial Y ℝ))) g = E 0 g := by
  rw [show E 0 g = constantCoeff (Phi g) from rfl]
  induction g using MvPolynomial.induction_on with
  | C a => simp [Phi, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp]
    rcases v with y | z <;> simp [Phi]

lemma toPoly_yPart {d : ℤ} (f : Hom (Y ⊕ Z) d) : toPoly (yPart f) = E 0 (toPoly f) := by
  rw [yPart, aeval_elim_eq_E, toPoly_ofPoly]
  simpa [deg] using IsH_E (IsH_toPoly f) 0

lemma toPoly_liftY {d : ℤ} (u : Hom Y d) :
    toPoly (liftY (Z := Z) u) = rename Sum.inl (toPoly u) := by
  rw [liftY, toPoly_ofPoly]
  exact IsH_rename_inl (IsH_toPoly u)

lemma E_liftY {d : ℤ} (u : Hom Y d) (α : Z →₀ ℕ) :
    E α (toPoly (liftY (Z := Z) u)) = if α = 0 then toPoly u else 0 := by
  rw [toPoly_liftY, E_rename_inl]

lemma deg_eq_zero_iff (α : Z →₀ ℕ) : deg α = 0 ↔ α = 0 := by
  unfold deg
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h; ext z; simpa using h z (Finset.mem_univ z)
  · rintro rfl; simp

lemma grade_zero_eq {d : ℤ} (f : Hom (Y ⊕ Z) d) : grade 0 f = liftY (yPart f) := by
  apply hom_ext_E
  intro α
  rw [E_grade, E_liftY, toPoly_yPart]
  by_cases h : α = 0
  · subst h; simp [deg]
  · rw [if_neg ((deg_eq_zero_iff α).not.2 h), if_neg h]

lemma mem_monos_Z (R : ℕ) (α : Z →₀ ℕ) : α ∈ monos Z (R : ℤ) ↔ deg α = R := by
  rw [mem_monos_iff]; omega

lemma sum_monos_split (d : ℤ) (R : ℕ) (φ : ((Y ⊕ Z) →₀ ℕ) → ℝ)
    (hφ : ∀ γ, deg (zp γ) ≠ R → φ γ = 0) :
    ∑ γ ∈ monos (Y ⊕ Z) d, φ γ =
      ∑ α ∈ monos Z (R : ℤ), ∑ β ∈ monos Y (d - R), φ (join β α) := by
  rw [← Finset.sum_filter_of_ne (p := fun γ => deg (zp γ) = R)
    (fun γ _ h => by_contra fun h' => h (hφ γ h'))]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun γ => (zp γ, yp γ)) (fun x => join x.2 x.1) ?_ ?_ ?_ ?_ ?_
  · intro γ hγ
    simp only [Finset.mem_coe, Finset.mem_filter, mem_monos_iff] at hγ
    simp only [Finset.mem_coe, Finset.mem_product, mem_monos_iff]
    rw [deg_split] at hγ; push_cast at hγ ⊢; omega
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_product, mem_monos_iff] at hx
    simp only [Finset.mem_coe, Finset.mem_filter, mem_monos_iff, deg_join, zp_join]
    push_cast; omega
  · intro γ _; simp
  · intro x _; simp
  · intro γ _; simp

lemma coeff_zsum (R : ℕ) (G : (Z →₀ ℕ) → MvPolynomial Y ℝ) (γ : (Y ⊕ Z) →₀ ℕ) :
    coeff γ (∑ α ∈ monos Z (R : ℤ), zmon α * rename Sum.inl (G α)) =
      if zp γ ∈ monos Z (R : ℤ) then coeff (yp γ) (G (zp γ)) else 0 := by
  rw [coeff_E, E_sum]
  simp_rw [E_zmon_mul_rename]
  rw [Finset.sum_ite_eq']
  split_ifs <;> simp

lemma norm_sq_zsum (d : ℤ) (R : ℕ) (G : (Z →₀ ℕ) → MvPolynomial Y ℝ) :
    ‖ofPoly d (∑ α ∈ monos Z (R : ℤ), zmon α * rename Sum.inl (G α))‖ ^ 2 =
      ∑ α ∈ monos Z (R : ℤ), (mfact α * ((d - R).toNat.factorial : ℝ) / (d.toNat.factorial : ℝ)) *
        ‖ofPoly (d - R) (G α)‖ ^ 2 := by
  rw [normsq_ofPoly, sum_monos_split d R]
  · apply Finset.sum_congr rfl
    intro α hα
    rw [normsq_ofPoly, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    rw [coeff_zsum, yp_join, zp_join, if_pos hα, mfact_join]
    have h1 : ((d - R).toNat.factorial : ℝ) ≠ 0 := by positivity
    have h2 : (d.toNat.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · intro γ hγ
    rw [coeff_zsum, if_neg (by rwa [mem_monos_Z])]
    simp

lemma norm_sq_le_of_coord {d : ℤ} {σ : Type} [Fintype σ] [DecidableEq σ] (x x' : Hom σ d)
    (h : ∀ γ, |x γ| ≤ |x' γ|) : ‖x‖ ≤ ‖x'‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro γ _
  simp only [Real.norm_eq_abs, sq_abs]
  exact sq_le_sq.2 (h γ)

lemma norm_grade_le (r : ℕ) {d : ℤ} (f : Hom (Y ⊕ Z) d) : ‖grade r f‖ ≤ ‖f‖ := by
  apply norm_sq_le_of_coord
  intro γ
  simp only [grade]
  split_ifs <;> simp

lemma zmon_zero : zmon (Y := Y) (0 : Z →₀ ℕ) = 1 := by
  rw [zmon, show join (0 : Y →₀ ℕ) (0 : Z →₀ ℕ) = 0 by
    rw [eq_iff_yp_zp]; constructor <;> ext <;> simp]
  rfl

lemma norm_liftY {d : ℤ} (u : Hom Y d) : ‖liftY (Z := Z) u‖ = ‖u‖ := by
  have h0 : monos Z ((0 : ℕ) : ℤ) = {0} := by simp [monos]
  have : rename Sum.inl (toPoly u) =
      ∑ α ∈ monos Z ((0 : ℕ) : ℤ), zmon α * rename (R := ℝ) (Sum.inl (β := Z)) (toPoly u) := by
    rw [h0, Finset.sum_singleton, zmon_zero, one_mul]
  have h := norm_sq_zsum (Y := Y) (Z := Z) d 0 (fun _ => toPoly u)
  rw [← this, h0, Finset.sum_singleton] at h
  simp only [Nat.cast_zero, sub_zero, ofPoly_toPoly] at h
  have hm : mfact (0 : Z →₀ ℕ) = 1 := by simp [mfact]
  rw [hm, one_mul, div_self (by positivity), one_mul] at h
  rw [liftY]
  rw [show d - ((0:ℕ):ℤ) = d by simp, ofPoly_toPoly] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

end Split

end ApproxSyzygies.Smoothed.Dev.L43
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L43

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1

/-! ### The pseudoinverse of a linear map between finite-dimensional inner product spaces -/

section Pinv

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma pinvNorm_nonneg (M : E →ₗ[ℝ] F) : 0 ≤ pinvNorm M :=
  Real.sInf_nonneg fun _ hτ => hτ.1

end Pinv

lemma norm_ofPoly_toPoly_eq {σ : Type} [Fintype σ] [DecidableEq σ] {d d' : ℤ} (h : d = d')
    (x : Hom σ d) : ‖ofPoly d' (toPoly x)‖ = ‖x‖ := by
  subst h; rw [ofPoly_toPoly]

lemma norm_ofPoly_congr {σ : Type} [Fintype σ] [DecidableEq σ] {d d' : ℤ} (h : d = d')
    (f : MvPolynomial σ ℝ) : ‖ofPoly d f‖ = ‖ofPoly d' f‖ := by
  subst h; rfl

/-! ### The extended pseudoinverse `Ŵ_R` -/

section What

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {m : ℕ}

end What

end ApproxSyzygies.Smoothed.Dev.L43
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L43

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1

section Rec

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {m : ℕ}

variable (e : Fin m → ℕ) (t : ℕ)

variable (p : ∀ i, Hom (Y ⊕ Z) (e i : ℤ))

end Rec

/-! ### Norm bounds -/

section Bounds

lemma part3' {σ : Type} [Fintype σ] [DecidableEq σ] {d1 d2 d : ℤ} (hd : d = d1 + d2)
    (h1 : 0 ≤ d1) (h2 : 0 ≤ d2) (x : Hom σ d1) (y : Hom σ d2) :
    ‖ofPoly d (toPoly x * toPoly y)‖ ≤ ‖x‖ * ‖y‖ := by
  obtain ⟨n1, rfl⟩ := Int.eq_ofNat_of_zero_le h1
  obtain ⟨n2, rfl⟩ := Int.eq_ofNat_of_zero_le h2
  subst hd
  exact part3 n1 n2 x y

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {m : ℕ}

end Bounds

end ApproxSyzygies.Smoothed.Dev.L43
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L44

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1 ApproxSyzygies.Smoothed.Dev.L43

/-! ### Generic algebra -/

section Generic

variable {σ : Type} [Fintype σ] [DecidableEq σ]

lemma ofPoly_add' (d : ℤ) (f g : MvPolynomial σ ℝ) : ofPoly d (f + g) = ofPoly d f + ofPoly d g :=
  (ofPolyL d).map_add f g

lemma ofPoly_smul' (d : ℤ) (c : ℝ) (f : MvPolynomial σ ℝ) : ofPoly d (c • f) = c • ofPoly d f :=
  (ofPolyL d).map_smul c f

lemma ofPoly_zero' (d : ℤ) : ofPoly d (0 : MvPolynomial σ ℝ) = 0 := (ofPolyL d).map_zero

lemma IsH_pow {d : ℤ} {f : MvPolynomial σ ℝ} (hf : IsH d f) (n : ℕ) : IsH (d * n) (f ^ n) := by
  induction n with
  | zero =>
    intro γ h
    simp only [pow_zero, coeff_one] at h
    split_ifs at h with h0
    · subst h0; simp [deg]
    · exact absurd rfl h
  | succ n ih => rw [pow_succ]; exact (ih.mul hf).of_eq (by push_cast; ring)

lemma IsH.eq_zero_of_neg {d : ℤ} {f : MvPolynomial σ ℝ} (hf : IsH d f) (hd : d < 0) : f = 0 := by
  ext γ
  by_contra h
  have := hf γ (by simpa using h)
  omega

/-- `‖x^n w‖ ≤ ‖x‖^n ‖w‖`. -/
lemma norm_pow_mul_le {k s : ℤ} (hk : 0 ≤ k) (x : Hom σ k) (w : Hom σ s) (n : ℕ) (u : ℤ)
    (hu : u = k * n + s) : ‖ofPoly u (toPoly x ^ n * toPoly w)‖ ≤ ‖x‖ ^ n * ‖w‖ := by
  induction n generalizing u with
  | zero =>
    subst hu
    simp only [pow_zero, one_mul]
    rw [norm_ofPoly_toPoly_eq (by push_cast; ring)]
  | succ n ih =>
    set u' : ℤ := k * n + s
    by_cases hu' : 0 ≤ u'
    · have hH : IsH u' (toPoly x ^ n * toPoly w) :=
        ((IsH_pow (IsH_toPoly x) n).mul (IsH_toPoly w)).of_eq rfl
      have e1 : toPoly x ^ (n + 1) * toPoly w =
          toPoly x * toPoly (ofPoly u' (toPoly x ^ n * toPoly w)) := by
        rw [toPoly_ofPoly u' _ hH]; ring
      rw [e1]
      calc _ ≤ ‖x‖ * ‖ofPoly u' (toPoly x ^ n * toPoly w)‖ :=
            part3' (by rw [hu]; push_cast; ring) hk hu' x _
        _ ≤ ‖x‖ * (‖x‖ ^ n * ‖w‖) := mul_le_mul_of_nonneg_left (ih u' rfl) (norm_nonneg _)
        _ = _ := by ring
    · have hs : s < 0 := by
        have : (0 : ℤ) ≤ k * n := mul_nonneg hk (by positivity)
        omega
      rw [IsH.eq_zero_of_neg (IsH_toPoly w) hs, mul_zero, ofPoly_zero', norm_zero]
      positivity

lemma norm_tup_le_of {σ' : Type} [Fintype σ'] [DecidableEq σ'] {m : ℕ} {e e' : Fin m → ℤ}
    (x : Tup σ e) (y : Tup σ' e') (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ j, ‖x j‖ ≤ c * ‖y j‖) : ‖x‖ ≤ c * ‖y‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2, ← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h j) 2

lemma tupNorm_nonneg' {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) : 0 ≤ tupNorm p := by
  unfold tupNorm; exact norm_nonneg _

end Generic

/-! ### Splitting variables -/

section Split

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

lemma E0_eq (f : MvPolynomial (Y ⊕ Z) ℝ) : E 0 f = constantCoeff (Phi f) := rfl

lemma E0_pow (f : MvPolynomial (Y ⊕ Z) ℝ) (n : ℕ) : E 0 (f ^ n) = E 0 f ^ n := by
  rw [E0_eq, E0_eq, map_pow, map_pow]

lemma Phi_rename_inr (W : MvPolynomial Z ℝ) :
    Phi (rename Sum.inr W : MvPolynomial (Y ⊕ Z) ℝ) = map C W := by
  induction W using MvPolynomial.induction_on with
  | C a => simp [Phi, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p z hp => rw [map_mul, rename_X, map_mul, hp]; simp [Phi]

lemma E_rename_inr (α : Z →₀ ℕ) (W : MvPolynomial Z ℝ) :
    E α (rename Sum.inr W : MvPolynomial (Y ⊕ Z) ℝ) = C (coeff α W) := by
  rw [E, Phi_rename_inr, coeff_map]

lemma IsH_rename_inr {d : ℤ} {g : MvPolynomial Z ℝ} (hg : IsH d g) :
    IsH d (rename Sum.inr g : MvPolynomial (Y ⊕ Z) ℝ) := by
  intro γ h
  rw [coeff_E, E_rename_inr, coeff_C] at h
  split_ifs at h with hy
  · have := hg _ h
    rw [deg_split, ← hy]; simpa [deg] using this
  · exact absurd rfl h

lemma toPoly_liftZ {d : ℤ} (u : Hom Z d) :
    toPoly (liftZ (Y := Y) u) = rename Sum.inr (toPoly u) := by
  rw [liftZ, toPoly_ofPoly]
  exact IsH_rename_inr (IsH_toPoly u)

lemma E0_liftZ {d : ℤ} (hd : 1 ≤ d) (u : Hom Z d) : E 0 (toPoly (liftZ (Y := Y) u)) = 0 := by
  rw [toPoly_liftZ, E_rename_inr]
  have : coeff 0 (toPoly u) = 0 := by
    by_contra h
    have := IsH_toPoly u 0 h
    simp [deg] at this; omega
  rw [this, C_0]

lemma norm_yPart_le {d : ℤ} (f : Hom (Y ⊕ Z) d) : ‖yPart f‖ ≤ ‖f‖ := by
  rw [← norm_liftY (Z := Z), ← grade_zero_eq]; exact norm_grade_le 0 f

end Split

/-! ### The projection `Π^⊥_J` applied to the `y`-coefficients of the `z`-monomials of degree `R` -/

section Proj

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

end Proj

end ApproxSyzygies.Smoothed.Dev.L44
end

section
/-! # Blueprint for Theorem 4.1: the successive-shrinking step (paper pp. 37–40)

`shrink_prob`: on the split variables `Y ⊕ (Fin L × Fin q)`, outside an event of probability
`exp(−c₂ n^{min d})`, every coefficient vector `h` has `‖g‖ ≤ n^{C₂} ρ^{-C₂} ‖f‖`
(`f = M_b^{(t)} h`, `g = gVec … (h[0])`), on the inductive-hypothesis event and the Gaussian norm
event. Its proof is assembled in `Q428G41BPShrinkGlue.lean`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.G41

open ApproxSyzygies.Smoothed

/-- The shrinking event of the step: IH-good pure-`y` part, Gaussian norm event, and some `h` with
`K₂ ‖f‖ < ‖g‖`. -/
def ShrinkBad {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {m : ℕ}
    (d D : Fin m → ℕ) (abar : ∀ i, Hom (Y ⊕ Z) (d i : ℤ)) (ρ K₂ : ℝ) (t : ℕ)
    (G : Set (∀ i, monos Y (d i : ℤ) → ℝ)) : Set (∀ i, monos (Y ⊕ Z) (d i : ℤ) → ℝ) :=
  {ω | restrictY ω ∈ G ∧ Ngood d ω ∧
    ∃ h : Tup (Y ⊕ Z) (fun i => (t : ℤ) - ((d i : ℤ) * (D i : ℕ))),
      K₂ * ‖mulMap (bfam d D abar ρ ω) (t : ℤ) h‖ <
        ‖gVec d D t (yParts fun i => perturbOn (abar i) ρ (ω i)) (yPartTup h)‖}

end ApproxSyzygies.Smoothed.Dev.G41
end

section
open MvPolynomial

set_option autoImplicit false

namespace ApproxSyzygies.Smoothed.Dev.G41.AC

open ApproxSyzygies.Smoothed

variable {Z : Type} [Fintype Z] [DecidableEq Z]
set_option linter.unusedSectionVars false

/-- The Bombieri normalising factor `√(|α|!/α!)`. -/
noncomputable def bc (α : Z →₀ ℕ) : ℝ := Real.sqrt (((Finsupp.degree α).factorial : ℝ) / mfact α)

lemma mfact_eq_cast (α : Z →₀ ℕ) : mfact α = ((∏ i, (α i).factorial : ℕ) : ℝ) := by
  simp [mfact]

lemma one_le_mfact (α : Z →₀ ℕ) : 1 ≤ mfact α := by
  rw [mfact_eq_cast]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => Nat.factorial_ne_zero _)

lemma mfact_le_fact (α : Z →₀ ℕ) : mfact α ≤ ((Finsupp.degree α).factorial : ℝ) := by
  rw [mfact_eq_cast, Finsupp.degree_eq_sum]
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
    (Nat.prod_factorial_dvd_factorial_sum Finset.univ fun i => α i)

lemma one_le_bc (α : Z →₀ ℕ) : 1 ≤ bc α := by
  unfold bc
  rw [Real.one_le_sqrt, one_le_div (lt_of_lt_of_le one_pos (one_le_mfact α))]
  exact mfact_le_fact α

lemma toPoly_eq_sum {d : ℤ} (v : Hom Z d) :
    toPoly v = ∑ α : monos Z d, monomial (α : Z →₀ ℕ) (v α * bc (α : Z →₀ ℕ)) := by
  unfold toPoly bmono bc
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [smul_monomial, smul_eq_mul]

lemma coeff_toPoly_pow {d : ℤ} (v : Hom Z d) (D : ℕ) (γ : Z →₀ ℕ) :
    coeff γ (toPoly v ^ D) = ∑ k : Fin D → monos Z d,
      if ∑ j, (k j : Z →₀ ℕ) = γ then ∏ j, (v (k j) * bc (k j : Z →₀ ℕ)) else 0 := by
  rw [toPoly_eq_sum, ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ,
    MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← monomial_sum_prod, coeff_monomial]

/-- The splitting constant `√(γ!/(dD)!)` of `ofPoly`. -/
noncomputable def sg (e : ℤ) (γ : Z →₀ ℕ) : ℝ := Real.sqrt (mfact γ / (e.toNat.factorial : ℝ))

/-- The coefficient of the adjoint map. -/
noncomputable def wco (d e : ℤ) (D : ℕ) (k : Fin D → monos Z d) (γ : monos Z e) : ℝ :=
  (if (γ : Z →₀ ℕ) = ∑ j, (k j : Z →₀ ℕ) then sg e (γ : Z →₀ ℕ) else 0) * ∏ j, bc (k j : Z →₀ ℕ)

lemma wco_perm (d e : ℤ) (D : ℕ) (k : Fin D → monos Z d) (π : Equiv.Perm (Fin D))
    (γ : monos Z e) : wco d e D (k ∘ π) γ = wco d e D k γ := by
  unfold wco
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp π (fun j => (k j : Z →₀ ℕ)), Equiv.prod_comp π (fun j => bc (k j : Z →₀ ℕ))]

/-- The adjoint `Φ*` of the tensor-to-polynomial map, in coordinates `Fin D → Fin n'`. -/
noncomputable def Wmap (d e : ℤ) (D n' : ℕ) (eq : Fin n' ≃ monos Z d) :
    Hom Z e →ₗ[ℝ] EuclideanSpace ℝ (Fin D → Fin n') where
  toFun u := WithLp.toLp 2 fun k => ∑ γ, u γ * wco d e D (eq ∘ k) γ
  map_add' u u' := by
    ext k
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by
    ext k
    simp [Finset.mul_sum, mul_assoc]

lemma Wmap_apply (d e : ℤ) (D n' : ℕ) (eq : Fin n' ≃ monos Z d) (u : Hom Z e)
    (k : Fin D → Fin n') : Wmap d e D n' eq u k = ∑ γ, u γ * wco d e D (eq ∘ k) γ := rfl

lemma Wmap_mem_sym (d e : ℤ) (D n' : ℕ) (eq : Fin n' ≃ monos Z d) (u : Hom Z e) :
    Wmap d e D n' eq u ∈ symTensors n' D := by
  intro π k
  rw [Wmap_apply, Wmap_apply]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← wco_perm d e D (eq ∘ k) π]
  rfl

/-- The adjoint identity `⟪Φ* u, v^{⊗D}⟫ = ⟪u, v^D⟫`. -/
lemma inner_Wmap (d : ℤ) (D n' : ℕ) (eq : Fin n' ≃ monos Z d) (u : Hom Z (d * D))
    (v : Hom Z d) :
    inner ℝ (Wmap d (d * D) D n' eq u) (tensPow (fun i => v (eq i)) D) =
      inner ℝ u (powHom v D) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Wmap_apply, tensPow, powHom,
    ofPoly, coeff_toPoly_pow]
  -- reindex the tensor sum by `eq`
  rw [Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin D)) eq)
    (fun k : Fin D → Fin n' => (∏ j, v (eq (k j))) * ∑ γ, u γ * wco d (d * D) D (eq ∘ k) γ)
    (fun k : Fin D → monos Z d => (∏ j, v (k j)) * ∑ γ, u γ * wco d (d * D) D k γ)
    (fun k => rfl)]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold wco sg
  by_cases h : (γ : Z →₀ ℕ) = ∑ j, (k j : Z →₀ ℕ)
  · rw [if_pos h, if_pos h.symm, Finset.prod_mul_distrib]
    ring
  · rw [if_neg h, if_neg (Ne.symm h)]
    ring

lemma exists_le_sum (γ : Z →₀ ℕ) (m : ℕ) (hm : m ≤ ∑ i, γ i) : ∃ α ≤ γ, ∑ i, α i = m := by
  induction m with
  | zero => exact ⟨0, Finsupp.le_def.2 fun i => by simp, by simp⟩
  | succ m ih =>
    obtain ⟨α, hαγ, hα⟩ := ih (by omega)
    have : ∃ i, α i < γ i := by
      by_contra h
      push Not at h
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h i
      omega
    obtain ⟨i, hi⟩ := this
    refine ⟨α + Finsupp.single i 1, ?_, ?_⟩
    · rw [Finsupp.le_def]
      intro j
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
      by_cases hj : i = j
      · subst hj; simp; omega
      · simp [hj]; exact Finsupp.le_def.1 hαγ j
    · simp [Finset.sum_add_distrib, Finsupp.single_apply, hα]

lemma exists_split (d : ℕ) : ∀ (D : ℕ) (γ : Z →₀ ℕ), ∑ i, γ i = d * D →
    ∃ k : Fin D → (Z →₀ ℕ), (∀ j, ∑ i, k j i = d) ∧ ∑ j, k j = γ := by
  intro D
  induction D with
  | zero =>
    intro γ hγ
    refine ⟨Fin.elim0, fun j => j.elim0, ?_⟩
    have h0 : ∀ i, γ i = 0 := by simpa using hγ
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    ext i
    simp [h0 i]
  | succ D ih =>
    intro γ hγ
    obtain ⟨α, hαγ, hα⟩ := exists_le_sum γ d (by rw [hγ]; nlinarith)
    have hsplit : α + (γ - α) = γ := add_tsub_cancel_of_le hαγ
    have hsum : ∑ i, (γ - α) i = d * D := by
      have h1 : ∑ i, (α + (γ - α)) i = ∑ i, α i + ∑ i, (γ - α) i := by
        simp [Finset.sum_add_distrib]
      rw [hsplit, hγ, hα] at h1
      rw [Nat.mul_succ] at h1
      omega
    obtain ⟨k, hk, hks⟩ := ih (γ - α) hsum
    refine ⟨Fin.cons α k, fun j => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hα
      · simpa using hk j
    · rw [Fin.sum_cons, hks, hsplit]

lemma mem_monos_nat (d : ℕ) (α : Z →₀ ℕ) : α ∈ monos Z (d : ℤ) ↔ ∑ i, α i = d := by
  simp [monos, Finset.mem_finsuppAntidiag]

lemma mem_monos_of (e : ℤ) (m : ℕ) (he : e = m) (α : Z →₀ ℕ) :
    α ∈ monos Z e ↔ ∑ i, α i = m := by
  subst he; exact mem_monos_nat m α

lemma exists_split_monos (d D : ℕ) (γ : monos Z ((d : ℤ) * (D : ℤ))) :
    ∃ k : Fin D → monos Z (d : ℤ), ∑ j, (k j : Z →₀ ℕ) = γ := by
  have hγ : ∑ i, (γ : Z →₀ ℕ) i = d * D :=
    (mem_monos_of _ (d * D) (by push_cast; ring) _).1 γ.2
  obtain ⟨k, hk, hks⟩ := exists_split d D (γ : Z →₀ ℕ) hγ
  exact ⟨fun j => ⟨k j, (mem_monos_nat d (k j)).2 (hk j)⟩, hks⟩

lemma card_monos (m : ℕ) :
    Fintype.card (monos Z (m : ℤ)) = (Fintype.card Z + m - 1).choose m := by
  rw [Fintype.card_coe]
  simp [monos, Finset.card_finsuppAntidiag_nat_eq_choose]

lemma card_monos_mul (d D : ℕ) :
    Fintype.card (monos Z ((d : ℤ) * (D : ℤ))) = (Fintype.card Z + d * D - 1).choose (d * D) := by
  rw [← card_monos]
  congr 2

lemma sq_le_Wmap (d D n' : ℕ) (eq : Fin n' ≃ monos Z (d : ℤ)) (u : Hom Z ((d : ℤ) * (D : ℤ)))
    (γ : monos Z ((d : ℤ) * (D : ℤ))) :
    ∃ k : Fin D → Fin n', ∑ j, ((eq (k j)) : Z →₀ ℕ) = γ ∧
      u γ ^ 2 ≤ ((d * D).factorial : ℝ) * (Wmap (d : ℤ) ((d : ℤ) * (D : ℤ)) D n' eq u k) ^ 2 := by
  obtain ⟨k₀, hk₀⟩ := exists_split_monos d D γ
  refine ⟨eq.symm ∘ k₀, by simpa using hk₀, ?_⟩
  have hk : eq ∘ (eq.symm ∘ k₀) = k₀ := by ext j; simp
  rw [Wmap_apply, hk]
  have hW : ∑ γ', u γ' * wco (d : ℤ) ((d : ℤ) * (D : ℤ)) D k₀ γ' =
      u γ * (sg ((d : ℤ) * (D : ℤ)) (γ : Z →₀ ℕ) * ∏ j, bc (k₀ j : Z →₀ ℕ)) := by
    rw [Finset.sum_eq_single γ]
    · unfold wco; rw [if_pos hk₀.symm]
    · intro γ' _ hne
      unfold wco
      rw [if_neg, zero_mul, mul_zero]
      intro h
      exact hne (Subtype.ext (h.trans hk₀))
    · simp
  rw [hW]
  have hF : (0 : ℝ) < ((d * D).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have htn : ((d : ℤ) * (D : ℤ)).toNat = d * D := by
    rw [show ((d : ℤ) * (D : ℤ)) = ((d * D : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
  have hsg : sg ((d : ℤ) * (D : ℤ)) (γ : Z →₀ ℕ) ^ 2 = mfact (γ : Z →₀ ℕ) / ((d * D).factorial : ℝ) := by
    unfold sg
    rw [htn, Real.sq_sqrt (div_nonneg (le_trans zero_le_one (one_le_mfact _)) hF.le)]
  have hprod : 1 ≤ ∏ j, bc (k₀ j : Z →₀ ℕ) := by
    calc (1 : ℝ) = ∏ _j : Fin D, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j _ => one_le_bc _)
  have hm := one_le_mfact (γ : Z →₀ ℕ)
  have : ((d * D).factorial : ℝ) * (u γ * (sg ((d : ℤ) * (D : ℤ)) (γ : Z →₀ ℕ) * ∏ j, bc (k₀ j : Z →₀ ℕ))) ^ 2 =
      u γ ^ 2 * mfact (γ : Z →₀ ℕ) * (∏ j, bc (k₀ j : Z →₀ ℕ)) ^ 2 := by
    rw [mul_pow, mul_pow, hsg]
    field_simp
  rw [this]
  have h1 : 1 ≤ (∏ j, bc (k₀ j : Z →₀ ℕ)) ^ 2 := one_le_pow₀ hprod
  have h2 : 0 ≤ u γ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hm h2]

lemma norm_le_Wmap (d D n' : ℕ) (eq : Fin n' ≃ monos Z (d : ℤ)) (u : Hom Z ((d : ℤ) * (D : ℤ))) :
    ‖u‖ ≤ Real.sqrt ((d * D).factorial : ℝ) *
      ‖Wmap (d : ℤ) ((d : ℤ) * (D : ℤ)) D n' eq u‖ := by
  choose κ hκs hκ using sq_le_Wmap d D n' eq u
  have hinj : Function.Injective κ := by
    intro γ γ' h
    apply Subtype.ext
    rw [← hκs γ, ← hκs γ', h]
  set w := Wmap (d : ℤ) ((d : ℤ) * (D : ℤ)) D n' eq u
  have hsq : ‖u‖ ^ 2 ≤ ((d * D).factorial : ℝ) * ‖w‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    calc ∑ γ, u γ ^ 2 ≤ ∑ γ, ((d * D).factorial : ℝ) * w (κ γ) ^ 2 :=
          Finset.sum_le_sum fun γ _ => hκ γ
      _ = ((d * D).factorial : ℝ) * ∑ k ∈ Finset.univ.image κ, w k ^ 2 := by
          rw [Finset.sum_image (fun x _ y _ h => hinj h), Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          exact Finset.subset_univ _
  rw [← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_mul
    (by positivity)]
  exact Real.sqrt_le_sqrt hsq

lemma proj_bound {V U : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    (W : V →ₗ[ℝ] U) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ u, ‖u‖ ≤ K * ‖W u‖) (E : Submodule ℝ V)
    (x : U) (P : V) (hxP : ∀ u, inner ℝ (W u) x = inner ℝ u P) :
    ‖(E.map W).starProjection x‖ ≤ K * ‖E.starProjection P‖ := by
  set y := (E.map W).starProjection x
  obtain ⟨u, hu, hy⟩ := Submodule.mem_map.1 ((E.map W).starProjection_apply_mem x)
  replace hy : W u = y := hy
  have h1 : ‖y‖ ^ 2 = inner ℝ y x := by
    have := (E.map W).starProjection_inner_eq_zero x y ((E.map W).starProjection_apply_mem x)
    rw [inner_sub_left] at this
    change inner ℝ x y - inner ℝ y y = 0 at this
    rw [← real_inner_self_eq_norm_sq, real_inner_comm x y]
    linarith
  have h2 : inner ℝ u P = inner ℝ (E.starProjection P) u := by
    have := E.starProjection_inner_eq_zero P u hu
    rw [inner_sub_left] at this
    rw [real_inner_comm P u]
    linarith
  have h3 : ‖y‖ ^ 2 ≤ K * ‖y‖ * ‖E.starProjection P‖ := by
    rw [h1, ← hy, hxP, h2, hy]
    calc inner ℝ (E.starProjection P) u ≤ ‖E.starProjection P‖ * ‖u‖ := real_inner_le_norm _ _
      _ ≤ ‖E.starProjection P‖ * (K * ‖W u‖) := by gcongr; exact hK u
      _ = _ := by rw [hy]; ring
  rcases (norm_nonneg y).eq_or_lt with h | h
  · rw [← h]; positivity
  · nlinarith

lemma finrank_map_Wmap (d D n' : ℕ) (eq : Fin n' ≃ monos Z (d : ℤ))
    (E : Submodule ℝ (Hom Z ((d : ℤ) * (D : ℤ)))) :
    Module.finrank ℝ (E.map (Wmap (d : ℤ) ((d : ℤ) * (D : ℤ)) D n' eq)) = Module.finrank ℝ E := by
  have hinj : Function.Injective (Wmap (d : ℤ) ((d : ℤ) * (D : ℤ)) D n' eq) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have := norm_le_Wmap d D n' eq u
    rw [hu, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj E)).symm

lemma map_Wmap_le_sym (d D n' : ℕ) (eq : Fin n' ≃ monos Z (d : ℤ))
    (E : Submodule ℝ (Hom Z ((d : ℤ) * (D : ℤ)))) :
    E.map (Wmap (d : ℤ) ((d : ℤ) * (D : ℤ)) D n' eq) ≤ symTensors n' D := by
  rintro _ ⟨u, _, rfl⟩
  exact Wmap_mem_sym _ _ _ _ _ u

end ApproxSyzygies.Smoothed.Dev.G41.AC
end

section
open MeasureTheory ProbabilityTheory

set_option autoImplicit false

namespace ApproxSyzygies.Smoothed.Dev.G41.AC

open ApproxSyzygies.Smoothed

lemma choose_lower (n m : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ m / (m.factorial : ℝ) ≤ ((n + m - 1).choose m : ℝ) := by
  have := Nat.pow_le_choose (α := ℝ) m (n + m - 1)
  rwa [show n + m - 1 + 1 - m = n by omega] at this

lemma choose_upper (n m : ℕ) (hm : m ≤ n) : (n + m - 1).choose m ≤ (2 * n) ^ m :=
  (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)

theorem powHom_anticonc (d D : ℕ) (hd : 1 ≤ d) (hD : 1 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ ∃ c' : ℝ, 0 < c' ∧ ∃ N₁ : ℕ,
      ∀ (Z : Type) [Fintype Z] [DecidableEq Z], N₁ ≤ Fintype.card Z → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        SubspaceAnticonc (1 / 4) (c' * ρ ^ D / (Fintype.card Z : ℝ) ^ ((d * D : ℕ) : ℝ))
          (c * (Fintype.card Z : ℝ) ^ d)
          ((Measure.pi fun _ : monos Z (d : ℤ) => gaussianReal 0 1).map
            fun g => powHom (ρ • (WithLp.toLp 2 g : Hom Z (d : ℤ))) D) := by
  obtain ⟨cD, hcD, cD', hcD', h46⟩ := theorem_4_6 D hD
  have hF : (0 : ℝ) < ((d * D).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hK : 0 < Real.sqrt ((d * D).factorial : ℝ) := Real.sqrt_pos.2 hF
  refine ⟨cD * (1 / (4 * 4 ^ (d * D) * ((d * D).factorial : ℝ))) / (d.factorial : ℝ),
    by positivity, cD' / (Real.sqrt ((d * D).factorial : ℝ) * 2 ^ (d * D)), by positivity,
    d + D + 1, ?_⟩
  intro Z _ _ hZ ρ hρ hρ1
  set F : ℝ := ((d * D).factorial : ℝ) with hFdef
  set K : ℝ := Real.sqrt F with hKdef
  set θ : ℝ := 1 / (4 * 4 ^ (d * D) * F) with hθdef
  set n := Fintype.card Z with hndef
  have hn1 : 1 ≤ n := by omega
  have hnd : d ≤ n := by omega
  have hnD : D ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set n' := Fintype.card (monos Z (d : ℤ)) with hn'def
  have hn' : n' = (n + d - 1).choose d := card_monos d
  have hn'up : n' ≤ (2 * n) ^ d := hn' ▸ choose_upper n d hnd
  have hn'low : (n : ℝ) ^ d / (d.factorial : ℝ) ≤ n' := by
    rw [hn']; exact choose_lower n d hn1
  have hn'1 : 1 ≤ n' := by
    rw [hn']; exact Nat.choose_pos (by omega)
  have hn'R : (1 : ℝ) ≤ n' := by exact_mod_cast hn'1
  let eq : Fin n' ≃ monos Z (d : ℤ) := (Fintype.equivFin _).symm
  refine ⟨by positivity, by positivity, ?_⟩
  intro E hE
  set η₀ : ℝ := cD' / (K * 2 ^ (d * D)) * ρ ^ D / (n : ℝ) ^ ((d * D : ℕ) : ℝ) with hη₀
  have hs : MeasurableSet {x : Hom Z ((d : ℤ) * (D : ℤ)) | ‖E.starProjection x‖ ≤ η₀} :=
    measurableSet_le E.starProjection.continuous.norm.measurable measurable_const
  by_cases hf : AEMeasurable (fun g => powHom (ρ • (WithLp.toLp 2 g : Hom Z (d : ℤ))) D)
    (Measure.pi fun _ : monos Z (d : ℤ) => gaussianReal 0 1)
  swap
  · rw [Measure.map_of_not_aemeasurable hf]; simp
  rw [Measure.map_apply_of_aemeasurable hf hs]
  set W := Wmap (d : ℤ) ((d : ℤ) * (D : ℤ)) D n' eq with hWdef
  set E' := E.map W with hE'def
  have hE'sym : E' ≤ symTensors n' D := map_Wmap_le_sym d D n' eq E
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by
    rw [hθdef, div_lt_one (by positivity)]
    have h1 : (1 : ℝ) ≤ 4 ^ (d * D) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ F := by rw [hFdef]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    nlinarith
  have hdim : θ * ((n' + D - 1).choose D : ℝ) ≤ (Module.finrank ℝ E' : ℝ) := by
    rw [hE'def, finrank_map_Wmap]
    refine le_trans ?_ hE
    rw [card_monos_mul]
    have hc1 : (n' + D - 1).choose D ≤ ((4 * n) ^ d) ^ D := by
      refine (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left ?_ _)
      have a1 : n ≤ (2 * n) ^ d := le_trans (by omega) (Nat.le_self_pow (by omega) _)
      have a2 : 2 ≤ 2 ^ d := Nat.le_self_pow (by omega) 2
      have a3 : (4 * n) ^ d = 2 ^ d * (2 * n) ^ d := by
        rw [← mul_pow]; ring_nf
      have a4 : 2 * (2 * n) ^ d ≤ 2 ^ d * (2 * n) ^ d := Nat.mul_le_mul_right _ a2
      omega
    have hc1R : ((n' + D - 1).choose D : ℝ) ≤ 4 ^ (d * D) * (n : ℝ) ^ (d * D) := by
      have := (Nat.cast_le (α := ℝ)).2 hc1
      push_cast at this
      calc _ ≤ _ := this
        _ = _ := by rw [← pow_mul, mul_pow]
    have hc2 := choose_lower n (d * D) hn1
    calc θ * ((n' + D - 1).choose D : ℝ) ≤ θ * (4 ^ (d * D) * (n : ℝ) ^ (d * D)) := by gcongr
      _ = 1 / 4 * ((n : ℝ) ^ (d * D) / F) := by
        rw [hθdef]; field_simp
      _ ≤ _ := by gcongr
  have key := h46 n' θ hθ0 hθ1 E' hE'sym hdim 0 ρ hρ
  have hmp := measurePreserving_piCongrLeft (fun _ : monos Z (d : ℤ) => gaussianReal 0 1) eq
  rw [← hmp.map_eq, MeasurableEquiv.map_apply]
  have hthr : K * η₀ ≤ cD' * ρ ^ D / (n' : ℝ) ^ ((D : ℝ) / 2) := by
    have hpow : (n' : ℝ) ^ ((D : ℝ) / 2) ≤ (2 : ℝ) ^ (d * D) * (n : ℝ) ^ (d * D) := by
      calc (n' : ℝ) ^ ((D : ℝ) / 2) ≤ (n' : ℝ) ^ ((D : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn'R (by
              have : (0 : ℝ) ≤ D := Nat.cast_nonneg D
              linarith)
        _ = (n' : ℝ) ^ D := Real.rpow_natCast _ _
        _ ≤ (((2 * n) ^ d : ℕ) : ℝ) ^ D := by
            exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hn'up) _
        _ = _ := by push_cast; rw [← pow_mul, mul_pow]
    have hn'pos : 0 < (n' : ℝ) ^ ((D : ℝ) / 2) := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hn'R) _
    have heq : K * η₀ = cD' * ρ ^ D / ((2 : ℝ) ^ (d * D) * (n : ℝ) ^ (d * D)) := by
      rw [hη₀, Real.rpow_natCast]
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_left (by positivity) hn'pos hpow
  refine le_trans (measure_mono ?_) (key.trans ?_)
  · intro g' hg'
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hg' ⊢
    set g := (MeasurableEquiv.piCongrLeft (fun _ : monos Z (d : ℤ) => ℝ) eq) g' with hg
    have hb := proj_bound W K (Real.sqrt_nonneg _) (norm_le_Wmap d D n' eq) E
      (tensPow (fun i => (ρ • (WithLp.toLp 2 g : Hom Z (d : ℤ))) (eq i)) D)
      (powHom (ρ • (WithLp.toLp 2 g : Hom Z (d : ℤ))) D)
      (fun u => inner_Wmap (d : ℤ) D n' eq u _)
    have ht : tensPow (0 + ρ • g') D =
        tensPow (fun i => (ρ • (WithLp.toLp 2 g : Hom Z (d : ℤ))) (eq i)) D := by
      congr 1
      funext i
      simp [hg, MeasurableEquiv.piCongrLeft_apply_apply]
    rw [ht]
    refine hb.trans (le_trans ?_ hthr)
    exact mul_le_mul_of_nonneg_left hg' (Real.sqrt_nonneg _)
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have hdf : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    calc cD * θ / (d.factorial : ℝ) * (n : ℝ) ^ d
        = cD * θ * ((n : ℝ) ^ d / (d.factorial : ℝ)) := by ring
      _ ≤ cD * θ * n' := by gcongr

end ApproxSyzygies.Smoothed.Dev.G41.AC
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L44

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1 ApproxSyzygies.Smoothed.Dev.L43

section Fam

variable {m : ℕ} (d D : Fin m → ℕ) (i : Fin m)

lemma modDeg_self : modDeg d D i i = d i := by simp [modDeg]

lemma modDeg_ne {j : Fin m} (h : j ≠ i) : modDeg d D i j = (d j : ℤ) * (D j : ℤ) := by
  simp [modDeg, h]

lemma toPoly_powHom {σ : Type} [Fintype σ] [DecidableEq σ] {e : ℤ} (x : Hom σ e) (n : ℕ) :
    toPoly (powHom x n) = toPoly x ^ n :=
  toPoly_ofPoly _ _ (IsH_pow (IsH_toPoly x) n)

lemma toPoly_modGen {σ : Type} [Fintype σ] [DecidableEq σ] (c : MvPolynomial σ ℝ)
    (hc : IsH (d i : ℤ) c) (a : ∀ j, Hom σ (d j : ℤ)) (j : Fin m) :
    toPoly (modGen d D i c a j) = if j = i then c else toPoly (a j) ^ D j := by
  unfold modGen
  split_ifs with h
  · subst h; exact toPoly_ofPoly _ _ (hc.of_eq (modDeg_self d D _).symm)
  · exact toPoly_ofPoly _ _ ((IsH_pow (IsH_toPoly (a j)) (D j)).of_eq (modDeg_ne d D i h).symm)

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

variable (a : ∀ j, Hom (Y ⊕ Z) (d j : ℤ)) (v : Hom Z (d i : ℤ))

lemma yPart_eq {d : ℤ} (f : Hom (Y ⊕ Z) d) : yPart f = ofPoly d (E 0 (toPoly f)) := by
  rw [yPart, aeval_elim_eq_E]

end Fam

end ApproxSyzygies.Smoothed.Dev.L44
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L42

open ApproxSyzygies.Smoothed

/-! ### Homogeneity with integer degrees -/

section Hom

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Homogeneity of integer degree `d` (for `d < 0` only `0` qualifies). -/
def HH (f : MvPolynomial σ ℝ) (d : ℤ) : Prop :=
  IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) f d

lemma weight_one_int (α : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) α = ((∑ i, α i : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp

lemma HH_zero (d : ℤ) : HH (0 : MvPolynomial σ ℝ) d := isWeightedHomogeneous_zero _ _ _

lemma HH.smul {f : MvPolynomial σ ℝ} {d : ℤ} (hf : HH f d) (c : ℝ) : HH (c • f) d :=
  (weightedHomogeneousSubmodule ℝ (fun _ : σ => (1 : ℤ)) d).smul_mem c hf

lemma HH_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) (d : ℤ)
    (h : ∀ i ∈ s, HH (f i) d) : HH (∑ i ∈ s, f i) d :=
  IsWeightedHomogeneous.sum s f d h

lemma HH_X (ℓ : σ) : HH (X ℓ : MvPolynomial σ ℝ) 1 := isWeightedHomogeneous_X _ _ _

lemma HH.pow {f : MvPolynomial σ ℝ} {d : ℤ} (hf : HH f d) (n : ℕ) {k : ℤ} (hk : k = d * n) :
    HH (f ^ n) k := by
  have := IsWeightedHomogeneous.pow hf n
  subst hk; rw [nsmul_eq_mul] at this; rwa [mul_comm]

lemma HH.eq_zero_of_neg {f : MvPolynomial σ ℝ} {d : ℤ} (hf : HH f d) (hd : d < 0) : f = 0 := by
  apply IsWeightedHomogeneous.eq_zero_of_no_monomials hf
  intro α h
  rw [weight_one_int] at h
  omega

lemma HH_toPoly {d : ℤ} (p : Hom σ d) : HH (toPoly p) d := by
  unfold toPoly
  apply HH_sum
  intro α _
  apply HH.smul
  unfold bmono
  apply isWeightedHomogeneous_monomial
  rw [weight_one_int]
  have := α.2
  unfold monos at this
  split_ifs at this with hd
  · rw [Finset.mem_finsuppAntidiag] at this
    rw [this.1]; omega
  · simp at this

lemma toPoly_ofPoly {d : ℤ} {f : MvPolynomial σ ℝ} (hf : HH f d) : toPoly (ofPoly d f) = f := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [hf.eq_zero_of_neg hd]
    unfold toPoly
    have : monos σ d = ∅ := Dev.A1.monos_neg d hd
    apply Finset.sum_eq_zero
    intro α _
    exact absurd α.2 (Finset.eq_empty_iff_forall_notMem.1 this _)
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    ext α
    rw [Dev.A1.coeff_toPoly]
    split_ifs with h
    · simp only [ofPoly, Int.toNat_natCast]
      change coeff α f * Real.sqrt (mfact α / (n.factorial : ℝ)) *
        Real.sqrt ((n.factorial : ℝ) / mfact α) = coeff α f
      rw [mul_assoc, ← Real.sqrt_mul (div_nonneg (Dev.A1.mfact_pos α).le (by positivity))]
      have h1 := Dev.A1.mfact_pos α
      have h2 : (0 : ℝ) < n.factorial := by positivity
      rw [div_mul_div_comm, mul_comm (mfact α), div_self (by positivity), Real.sqrt_one, mul_one]
    · symm
      apply hf.coeff_eq_zero
      rw [weight_one_int]
      rw [Dev.A1.mem_monos_nat] at h
      omega

lemma mulMap_apply {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) (s : ℤ)
    (v : Tup σ (fun i => s - e i)) :
    mulMap p s v = ∑ i, ofPoly s (toPoly (p i) * toPoly (v i)) := by
  simp [mulMap, LinearMap.sum_apply, ofPolyL, toPolyL]
  rfl

end Hom

/-! ### The pure-`y` part -/

section YPart

variable {Y Z : Type*} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- The substitution `z ↦ 0`. -/
noncomputable abbrev rho : MvPolynomial (Y ⊕ Z) ℝ →ₐ[ℝ] MvPolynomial Y ℝ :=
  aeval (Sum.elim X (fun _ : Z => (0 : MvPolynomial Y ℝ)))

lemma HH_rho {f : MvPolynomial (Y ⊕ Z) ℝ} {d : ℤ} (hf : HH f d) :
    HH (rho (Y := Y) (Z := Z) f) d := by
  unfold HH at hf ⊢
  rw [← mem_weightedHomogeneousSubmodule, weightedHomogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single] at hf
  refine Submodule.span_induction ?_ ?_ (fun p q _ _ hp hq ↦ ?_) (fun r p _ h ↦ ?_) hf
  · rintro _ ⟨α, hα, rfl⟩
    rw [Set.mem_ofPred] at hα
    change IsWeightedHomogeneous _ (rho (monomial α (1:ℝ))) d
    rw [aeval_monomial, map_one, one_mul]
    have hfac : ∀ i : Y ⊕ Z, HH (Sum.elim X (fun _ : Z => (0 : MvPolynomial Y ℝ)) i) 1 := by
      intro i
      cases i with
      | inl y => exact HH_X y
      | inr z => exact HH_zero 1
    have : IsWeightedHomogeneous (fun _ : Y => (1 : ℤ)) (α.prod fun i k => (Sum.elim X (fun _ : Z => (0 : MvPolynomial Y ℝ)) i) ^ k) d := by
      unfold Finsupp.prod
      have := IsWeightedHomogeneous.prod (w := fun _ : Y => (1 : ℤ)) α.support
        (fun i => (Sum.elim X (fun _ : Z => (0 : MvPolynomial Y ℝ)) i) ^ (α i))
        (fun i => ((α i : ℕ) : ℤ)) (fun i _ => (hfac i).pow (α i) (by ring))
      convert this using 1
      rw [← hα, Finsupp.weight_apply]
      simp [Finsupp.sum]
    exact this
  · rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  · rw [map_add]; exact hp.add hq
  · rw [map_smul]; exact (weightedHomogeneousSubmodule ℝ _ d).smul_mem r h

lemma toPoly_yPart {d : ℤ} (f : Hom (Y ⊕ Z) d) : toPoly (yPart f) = rho (toPoly f) :=
  toPoly_ofPoly (HH_rho (HH_toPoly f))

lemma toPoly_yParts_pow {d : ℤ} (a : Hom (Y ⊕ Z) d) (D : ℕ) :
    toPoly (yPart (powHom a D)) = toPoly (yPart a) ^ D := by
  rw [toPoly_yPart, toPoly_yPart, powHom, toPoly_ofPoly ((HH_toPoly a).pow D rfl), map_pow]

end YPart

/-! ### The pseudoinverse -/

section Pinv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

end Pinv

end ApproxSyzygies.Smoothed.Dev.L42
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L44

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1 ApproxSyzygies.Smoothed.Dev.L43

section Eq

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
variable {m : ℕ} (d D : Fin m → ℕ) (i : Fin m) (t : ℕ)

lemma zero_mem_koszul {σ : Type} [Fintype σ] [DecidableEq σ] {e : Fin m → ℤ} (p : ∀ j, Hom σ (e j))
    (s : ℤ) : (0 : Tup σ (fun j => s - e j)) ∈ koszul p s :=
  ⟨fun _ _ => 0, fun _ _ => zero_mem _, fun _ _ => by simp, fun j => by
    simp [toPoly_zero]⟩

variable (a : ∀ j, Hom (Y ⊕ Z) (d j : ℤ)) (v : Hom Z (d i : ℤ))

end Eq

end ApproxSyzygies.Smoothed.Dev.L44
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MvPolynomial

namespace ApproxSyzygies.Smoothed.Dev.L44

open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.A1 ApproxSyzygies.Smoothed.Dev.L43

/-- Lemma 4.3 for a degree family `e'` equal to `fun j => (e j : ℤ)` (not definitionally). -/
lemma l43' (T : ℕ) {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    {m : ℕ} (e : Fin m → ℕ) (e' : Fin m → ℤ) (hee : e' = fun j => (e j : ℤ))
    (he : ∀ i, 1 ≤ e i) (t : ℕ) (htT : t ≤ T) (R : ℕ) (hR : R ≤ t) :
    ∃ F : (r : ℕ) → (∀ i, Hom (Y ⊕ Z) (e' i)) →
        ((PiLp 2 fun _ : Fin (r + 1) => Hom (Y ⊕ Z) (t : ℤ)) →L[ℝ]
          Tup (Y ⊕ Z) (fun i => (t : ℤ) - e' i)),
    ∃ H : (r : ℕ) → (∀ i, Hom (Y ⊕ Z) (e' i)) →
        (Tup Y (fun i => (t : ℤ) - e' i) →L[ℝ] Tup (Y ⊕ Z) (fun i => (t : ℤ) - e' i)),
      ∀ p : ∀ i, Hom (Y ⊕ Z) (e' i), KernelCond (yParts p) t →
        (∀ r, r ≤ R →
          ‖F r p‖ ≤ 1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t *
              max ((1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1))
                (tupNorm p *
                  (1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1)) ∧
          ‖H r p‖ ≤ 1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t *
              max ((1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1))
                (tupNorm p *
                  (1 + (2 : ℝ) ^ ((T : ℝ) / 2) * tauOf (yParts p) t * tupNorm p) ^ ((R : ℤ) - 1))) ∧
        ∀ (h : Tup (Y ⊕ Z) (fun i => (t : ℤ) - e' i)) (h₀ : Tup Y (fun i => (t : ℤ) - e' i)),
          h₀ - yPartTup h ∈ koszul (yParts p) (t : ℤ) →
          ∃ k ∈ koszul p (t : ℤ), yPartTup k = yPartTup h - h₀ ∧
            ∀ r, r ≤ R →
              gradeTup r h = gradeTup r k + F r p (gradeSeg r (mulMap p (t : ℤ) h)) + H r p h₀ := by
  subst hee
  obtain ⟨F, H, -, hFH⟩ := ApproxSyzygies.Smoothed.lemma_4_3 T (Y := Y) (Z := Z) e he t htT R hR
  exact ⟨F, H, hFH⟩

lemma tauOf_nonneg' {Y : Type} [Fintype Y] [DecidableEq Y] {m : ℕ} {e : Fin m → ℤ}
    (p0 : ∀ i, Hom Y (e i)) (t : ℕ) : 0 ≤ tauOf p0 t :=
  Real.iSup_nonneg fun _ => pinvNorm_nonneg _

section Bounds

variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
variable {m : ℕ} (d D : Fin m → ℕ) (i : Fin m) (t : ℕ)

end Bounds

end ApproxSyzygies.Smoothed.Dev.L44

namespace ApproxSyzygies.Smoothed

end ApproxSyzygies.Smoothed
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Module

namespace ApproxSyzygies.Smoothed.Dev.P48

open ApproxSyzygies.Smoothed

section Frame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A frame: pairwise orthogonal vectors, each of norm `0` or `1`. -/
def IsFrame {k : ℕ} (v : Fin k → E) : Prop :=
  (∀ a b, inner ℝ (v a) (v b) = if a = b then inner ℝ (v a) (v a) else 0) ∧
    ∀ a, ‖v a‖ = 0 ∨ ‖v a‖ = 1

/-- The projection `∑ₐ ⟪vₐ, g⟫ vₐ`. -/
noncomputable def proj {k : ℕ} (v : Fin k → E) (g : E) : E :=
  ∑ a, inner ℝ (v a) g • v a

lemma proj_mem {k : ℕ} (v : Fin k → E) (g : E) : proj v g ∈ Submodule.span ℝ (Set.range v) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

lemma inner_sub_proj {k : ℕ} {v : Fin k → E} (hv : IsFrame v) (g : E) (a : Fin k) :
    inner ℝ (v a) (g - proj v g) = 0 := by
  rw [inner_sub_right, proj, inner_sum]
  rw [Finset.sum_congr rfl (fun b _ => by rw [inner_smul_right, hv.1 a b])]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rcases hv.2 a with h | h
  · rw [norm_eq_zero.1 h]; simp
  · rw [real_inner_self_eq_norm_sq, h]; ring

lemma inner_sub_proj_of_mem {k : ℕ} {v : Fin k → E} (hv : IsFrame v) (g : E) {z : E}
    (hz : z ∈ Submodule.span ℝ (Set.range v)) : inner ℝ z (g - proj v g) = 0 := by
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact inner_sub_proj hv g a
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

lemma norm_sub_proj_le {k : ℕ} {v : Fin k → E} (hv : IsFrame v) (g : E) {z : E}
    (hz : z ∈ Submodule.span ℝ (Set.range v)) : ‖g - proj v g‖ ≤ ‖g - z‖ := by
  have hmem : proj v g - z ∈ Submodule.span ℝ (Set.range v) :=
    Submodule.sub_mem _ (proj_mem v g) hz
  have h0 : inner ℝ (g - proj v g) (proj v g - z) = 0 := by
    rw [real_inner_comm]; exact inner_sub_proj_of_mem hv g hmem
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real h0
  have he : g - proj v g + (proj v g - z) = g - z := by abel
  rw [he] at h
  have : ‖g - proj v g‖ ^ 2 ≤ ‖g - z‖ ^ 2 := by nlinarith [norm_nonneg (proj v g - z)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

lemma proj_of_isEmpty {k : ℕ} (hk : k = 0) (v : Fin k → E) (g : E) : proj v g = 0 := by
  subst hk; simp [proj]

lemma continuous_proj {X : Type*} [TopologicalSpace X] {k : ℕ} {v : X → Fin k → E} {g : X → E}
    (hv : Continuous v) (hg : Continuous g) : Continuous fun x => proj (v x) (g x) := by
  unfold proj
  refine continuous_finsetSum _ fun a _ => ?_
  have hva : Continuous fun x => v x a := (continuous_apply a).comp hv
  exact (hva.inner hg).smul hva

lemma isFrame_of_orthonormal {k : ℕ} {v : Fin k → E} (hv : Orthonormal ℝ v) : IsFrame v := by
  classical
  refine ⟨fun a b => ?_, fun a => Or.inr (hv.1 a)⟩
  rw [orthonormal_iff_ite.1 hv a b, orthonormal_iff_ite.1 hv a a]
  by_cases h : a = b <;> simp [h]

lemma isFrame_zero {k : ℕ} : IsFrame (fun _ : Fin k => (0 : E)) :=
  ⟨fun a b => by split_ifs <;> simp, fun _ => Or.inl norm_zero⟩

lemma isClosed_isFrame (k : ℕ) : IsClosed {v : Fin k → E | IsFrame v} := by
  have h1 : IsClosed {v : Fin k → E |
      ∀ a b, inner ℝ (v a) (v b) = if a = b then inner ℝ (v a) (v a) else 0} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
    have ha : Continuous fun v : Fin k → E => v a := continuous_apply a
    have hb : Continuous fun v : Fin k → E => v b := continuous_apply b
    split_ifs
    · exact isClosed_eq (ha.inner hb) (ha.inner ha)
    · exact isClosed_eq (ha.inner hb) continuous_const
  have h2 : IsClosed {v : Fin k → E | ∀ a, ‖v a‖ = 0 ∨ ‖v a‖ = 1} := by
    simp only [Set.ofPred_forall, Set.ofPred_or]
    refine isClosed_iInter fun a => ?_
    have ha : Continuous fun v : Fin k → E => ‖v a‖ := (continuous_apply a).norm
    exact (isClosed_eq ha continuous_const).union (isClosed_eq ha continuous_const)
  exact h1.inter h2

lemma isCompact_isFrame [FiniteDimensional ℝ E] (k : ℕ) :
    IsCompact {v : Fin k → E | IsFrame v} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_isFrame k) ?_
  refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun v hv => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  rcases hv.2 a with h | h <;> rw [h]; exact zero_le_one

end Frame

/-- Projection of a closed set along a compact factor is closed. -/
lemma isClosed_exists_mem_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} (hK : IsCompact K) {F : Set (X × Y)} (hF : IsClosed F) :
    IsClosed {y | ∃ x ∈ K, (x, y) ∈ F} := by
  have := isCompact_iff_compactSpace.mp hK
  have hc : Continuous fun p : K × Y => ((p.1 : X), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have h := isClosedMap_snd_of_compactSpace (X := K) (Y := Y) _ (hF.preimage hc)
  convert h using 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage, Prod.exists]
  constructor
  · rintro ⟨x, hx, hxy⟩; exact ⟨⟨x, hx⟩, y, hxy, rfl⟩
  · rintro ⟨x, y', hxy, rfl⟩; exact ⟨x, x.2, hxy⟩

section Tens

variable {ι κ : Type} [Fintype ι] [Fintype κ]

lemma norm_tens (u : EuclideanSpace ℝ ι) (w : EuclideanSpace ℝ κ) :
    ‖tens u w‖ = ‖u‖ * ‖w‖ := by
  have h : ‖tens u w‖ ^ 2 = (‖u‖ * ‖w‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp [tens, mul_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

lemma tens_sub (u : EuclideanSpace ℝ ι) (w w' : EuclideanSpace ℝ κ) :
    tens u w - tens u w' = tens u (w - w') := by
  ext p; simp [tens, mul_sub]

lemma continuous_tens {X : Type*} [TopologicalSpace X] {u : X → EuclideanSpace ℝ ι}
    {w : X → EuclideanSpace ℝ κ} (hu : Continuous u) (hw : Continuous w) :
    Continuous fun x => tens (u x) (w x) := by
  unfold tens
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
  exact ((PiLp.continuous_apply 2 _ p.1).comp hu).mul ((PiLp.continuous_apply 2 _ p.2).comp hw)

end Tens

end ApproxSyzygies.Smoothed.Dev.P48
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Module

namespace ApproxSyzygies.Smoothed.Dev.P48

open ApproxSyzygies.Smoothed

variable {m L : ℕ} {ι : Fin L → Fin m → Type} [∀ ℓ i, Fintype (ι ℓ i)]
  {κ : Fin m → Type} [∀ i, Fintype (κ i)]

/-- The ambient space `W = ⨁ᵢ Wᵢ`. -/
abbrev Wsp (κ : Fin m → Type) [∀ i, Fintype (κ i)] : Type :=
  PiLp 2 fun i => EuclideanSpace ℝ (κ i)

/-- The data of block `ℓ`: the vectors `ζᵢ` and the images `Cᵢ(b_k)` of a basis of `G₀`. -/
abbrev Dat (ι : Fin L → Fin m → Type) [∀ ℓ i, Fintype (ι ℓ i)] (κ : Fin m → Type)
    [∀ i, Fintype (κ i)] (d : ℕ) (ℓ : Fin L) : Type :=
  (∀ i, EuclideanSpace ℝ (ι ℓ i)) × (∀ i, Fin d → EuclideanSpace ℝ (ι ℓ i × κ i))

/-- The residual `‖ζᵢ ⊗ hᵢ + Cᵢ(Π h)‖` written through the data. -/
noncomputable def res {d : ℕ} (bW : Fin d → Wsp κ) {ℓ : Fin L} (t : Dat ι κ d ℓ) (i : Fin m)
    (h : Wsp κ) : ℝ :=
  ‖tens (t.1 i) (h i) + ∑ k, inner ℝ (bW k) h • t.2 i k‖

/-- One shrinking step from `span v` to `span v'`. -/
def Step {d : ℕ} (Q : ℝ) (bW : Fin d → Wsp κ) {ℓ : Fin L} (t : Dat ι κ d ℓ) {k k' : ℕ}
    (v : Fin k → Wsp κ) (v' : Fin k' → Wsp κ) : Prop :=
  ∀ g : Wsp κ, ∃ i, ‖proj v g - proj v' (proj v g)‖ ≤ Q * res bW t i (proj v g)

/-- The first `j` steps can be carried out. -/
def Good (kk : Fin (L + 1) → ℕ) (Q : ℝ) (bW : Fin (kk 0) → Wsp κ) (j : ℕ)
    (θ : ∀ ℓ, Dat ι κ (kk 0) ℓ) : Prop :=
  ∃ V : (j : Fin (L + 1)) → Fin (kk j) → Wsp κ, (∀ j, IsFrame (V j)) ∧ V 0 = bW ∧
    ∀ ℓ : Fin L, ℓ.val < j → Step Q bW (θ ℓ) (V ℓ.castSucc) (V ℓ.succ)

lemma continuous_res {X : Type*} [TopologicalSpace X] {d : ℕ} (bW : Fin d → Wsp κ) {ℓ : Fin L}
    {t : X → Dat ι κ d ℓ} {h : X → Wsp κ} (ht : Continuous t) (hh : Continuous h) (i : Fin m) :
    Continuous fun x => res bW (t x) i (h x) := by
  unfold res
  refine Continuous.norm (Continuous.add ?_ ?_)
  · exact continuous_tens ((continuous_apply i).comp (continuous_fst.comp ht))
      ((PiLp.continuous_apply 2 _ i).comp hh)
  · refine continuous_finsetSum _ fun k _ => ?_
    exact ((Continuous.inner (𝕜 := ℝ) continuous_const hh)).smul
      ((continuous_apply k).comp ((continuous_apply i).comp (continuous_snd.comp ht)))

lemma good_congr (kk : Fin (L + 1) → ℕ) (Q : ℝ) (bW : Fin (kk 0) → Wsp κ) (j : ℕ)
    {θ θ' : ∀ ℓ, Dat ι κ (kk 0) ℓ} (h : ∀ ℓ : Fin L, ℓ.val < j → θ ℓ = θ' ℓ) :
    Good kk Q bW j θ ↔ Good kk Q bW j θ' := by
  constructor
  · rintro ⟨V, h1, h2, h3⟩
    exact ⟨V, h1, h2, fun ℓ hℓ => h ℓ hℓ ▸ h3 ℓ hℓ⟩
  · rintro ⟨V, h1, h2, h3⟩
    exact ⟨V, h1, h2, fun ℓ hℓ => (h ℓ hℓ).symm ▸ h3 ℓ hℓ⟩

lemma good_zero (kk : Fin (L + 1) → ℕ) (Q : ℝ) (bW : Fin (kk 0) → Wsp κ) (hb : IsFrame bW)
    (θ : ∀ ℓ, Dat ι κ (kk 0) ℓ) : Good kk Q bW 0 θ := by
  classical
  refine ⟨Function.update (fun j => fun _ => 0) 0 bW, fun j => ?_, by simp, fun ℓ h => absurd h
    (Nat.not_lt_zero _)⟩
  by_cases hj : j = 0
  · subst hj; simpa using hb
  · rw [Function.update_of_ne hj]; exact isFrame_zero

lemma isClosed_good (kk : Fin (L + 1) → ℕ) (Q : ℝ) (bW : Fin (kk 0) → Wsp κ) (j : ℕ) :
    IsClosed {θ : ∀ ℓ, Dat ι κ (kk 0) ℓ | Good kk Q bW j θ} := by
  set K : Set ((j : Fin (L + 1)) → Fin (kk j) → Wsp κ) :=
    (Set.pi Set.univ fun j => {v | IsFrame v}) ∩ {V | V 0 = bW} with hK
  have hKc : IsCompact K :=
    (isCompact_univ_pi fun j => isCompact_isFrame _).inter_right
      (isClosed_eq (continuous_apply 0) continuous_const)
  set F : Set (((j : Fin (L + 1)) → Fin (kk j) → Wsp κ) × (∀ ℓ, Dat ι κ (kk 0) ℓ)) :=
    {p | ∀ ℓ : Fin L, ℓ.val < j → Step Q bW (p.2 ℓ) (p.1 ℓ.castSucc) (p.1 ℓ.succ)} with hF
  have hFc : IsClosed F := by
    rw [hF]
    simp only [Step, Set.ofPred_forall, Set.ofPred_exists]
    refine isClosed_iInter fun ℓ => isClosed_iInter fun _ => isClosed_iInter fun g =>
      isClosed_iUnion_of_finite fun i => ?_
    have hv : Continuous fun p : ((j : Fin (L + 1)) → Fin (kk j) → Wsp κ) ×
        (∀ ℓ, Dat ι κ (kk 0) ℓ) => p.1 ℓ.castSucc := (continuous_apply _).comp continuous_fst
    have hv' : Continuous fun p : ((j : Fin (L + 1)) → Fin (kk j) → Wsp κ) ×
        (∀ ℓ, Dat ι κ (kk 0) ℓ) => p.1 ℓ.succ := (continuous_apply _).comp continuous_fst
    have hpg := continuous_proj hv continuous_const (g := fun _ => g)
    exact isClosed_le (Continuous.norm (hpg.sub (continuous_proj hv' hpg)))
      (continuous_const.mul (continuous_res bW ((continuous_apply ℓ).comp continuous_snd) hpg i))
  convert isClosed_exists_mem_compact hKc hFc using 1
  ext θ
  simp only [Set.mem_ofPred_eq, Good, hK, hF, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
    forall_true_left]
  constructor
  · rintro ⟨V, h1, h2, h3⟩; exact ⟨V, ⟨h1, h2⟩, h3⟩
  · rintro ⟨V, ⟨h1, h2⟩, h3⟩; exact ⟨V, h1, h2, h3⟩

/-- The iterates `g⁽ʲ⁾`. -/
noncomputable def gseq {kk : Fin (L + 1) → ℕ} (V : (j : Fin (L + 1)) → Fin (kk j) → Wsp κ)
    (g : Wsp κ) : ℕ → Wsp κ
  | 0 => proj (V 0) g
  | j + 1 => if h : j + 1 < L + 1 then proj (V ⟨j + 1, h⟩) (gseq V g j) else gseq V g j

lemma iterate {kk : Fin (L + 1) → ℕ} {Q β η : ℝ} {bW : Fin (kk 0) → Wsp κ}
    {θ : ∀ ℓ, Dat ι κ (kk 0) ℓ} (hQ : 0 ≤ Q) (hβ : 0 ≤ β)
    (V : (j : Fin (L + 1)) → Fin (kk j) → Wsp κ) (hV0 : V 0 = bW)
    (hst : ∀ ℓ : Fin L, Step Q bW (θ ℓ) (V ℓ.castSucc) (V ℓ.succ))
    (hlast : kk (Fin.last L) = 0) (g : Wsp κ) (hg : proj bW g = g)
    (hres : ∀ ℓ i, res bW (θ ℓ) i g ≤ η)
    (hlip : ∀ ℓ i x, res bW (θ ℓ) i x ≤ res bW (θ ℓ) i g + β * ‖x - g‖) :
    β * ‖g‖ + η ≤ η * (1 + β * Q) ^ L := by
  have key : ∀ j : ℕ, (hj : j ≤ L) →
      (∃ g', gseq V g j = proj (V ⟨j, Nat.lt_succ_of_le hj⟩) g') ∧
        β * ‖g - gseq V g j‖ + η ≤ η * (1 + β * Q) ^ j := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨⟨g, rfl⟩, ?_⟩
      have : gseq V g 0 = g := by simp only [gseq, hV0, hg]
      rw [this]; simp
    | succ j ih =>
      intro hj
      obtain ⟨⟨g', hg'⟩, hb⟩ := ih (by omega)
      have hdef : gseq V g (j + 1) = proj (V ⟨j + 1, by omega⟩) (gseq V g j) := by
        simp only [gseq, dif_pos (show j + 1 < L + 1 by omega)]
      refine ⟨⟨gseq V g j, hdef⟩, ?_⟩
      set ℓ : Fin L := ⟨j, by omega⟩
      obtain ⟨i, hi⟩ := hst ℓ g'
      have e1 : (ℓ.castSucc : Fin (L + 1)) = ⟨j, by omega⟩ := rfl
      have e2 : (ℓ.succ : Fin (L + 1)) = ⟨j + 1, by omega⟩ := rfl
      rw [e1, e2, ← hg', ← hdef] at hi
      set x := gseq V g j
      have hstep : ‖x - gseq V g (j + 1)‖ ≤ Q * (η + β * ‖g - x‖) := by
        refine hi.trans (mul_le_mul_of_nonneg_left ?_ hQ)
        rw [← norm_neg (g - x), neg_sub]
        exact (hlip ℓ i x).trans (by linarith [hres ℓ i])
      have htri : ‖g - gseq V g (j + 1)‖ ≤ ‖g - x‖ + ‖x - gseq V g (j + 1)‖ := by
        have := norm_add_le (g - x) (x - gseq V g (j + 1))
        rwa [sub_add_sub_cancel] at this
      have hs := norm_nonneg (g - x)
      calc β * ‖g - gseq V g (j + 1)‖ + η
          ≤ β * (‖g - x‖ + Q * (η + β * ‖g - x‖)) + η := by
            gcongr; exact htri.trans (by linarith)
        _ = (1 + β * Q) * (β * ‖g - x‖ + η) := by ring
        _ ≤ (1 + β * Q) * (η * (1 + β * Q) ^ j) := by
            gcongr
        _ = η * (1 + β * Q) ^ (j + 1) := by ring
  obtain ⟨⟨g', hg'⟩, hb⟩ := key L le_rfl
  have h0 : gseq V g L = 0 := by
    rw [hg']; exact proj_of_isEmpty hlast _ _
  rwa [h0, sub_zero] at hb

/-- The deterministic dimension sequence. -/
noncomputable def kseq (d : ℕ) (n : ℕ → Fin m → ℕ) : ℕ → ℕ
  | 0 => d
  | j + 1 => min (kseq d n j) ⌊2 * ∑ i, (kseq d n j : ℝ) / (n j i : ℝ)⌋₊

lemma kseq_le (d : ℕ) (n : ℕ → Fin m → ℕ) (j : ℕ) :
    (kseq d n j : ℝ) ≤ d * ∏ t ∈ Finset.range j, (2 * ∑ i, (1 : ℝ) / (n t i : ℝ)) := by
  induction j with
  | zero => simp [kseq]
  | succ j ih =>
    have ha : 0 ≤ 2 * ∑ i, (1 : ℝ) / (n j i : ℝ) := by positivity
    calc (kseq d n (j + 1) : ℝ) ≤ ⌊2 * ∑ i, (kseq d n j : ℝ) / (n j i : ℝ)⌋₊ := by
          simp [kseq]
      _ ≤ 2 * ∑ i, (kseq d n j : ℝ) / (n j i : ℝ) := Nat.floor_le (by positivity)
      _ = (kseq d n j : ℝ) * (2 * ∑ i, (1 : ℝ) / (n j i : ℝ)) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ (d * ∏ t ∈ Finset.range j, (2 * ∑ i, (1 : ℝ) / (n t i : ℝ))) *
            (2 * ∑ i, (1 : ℝ) / (n j i : ℝ)) := mul_le_mul_of_nonneg_right ih ha
      _ = d * ∏ t ∈ Finset.range (j + 1), (2 * ∑ i, (1 : ℝ) / (n t i : ℝ)) := by
          rw [Finset.prod_range_succ]; ring

end ApproxSyzygies.Smoothed.Dev.P48
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Module

namespace ApproxSyzygies.Smoothed.Dev.P48

open ApproxSyzygies.Smoothed

section Pad

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An orthonormal family padded with zeros. -/
noncomputable def pad {r : ℕ} (k : ℕ) (e : Fin r → E) : Fin k → E :=
  fun a => if h : a.val < r then e ⟨a.val, h⟩ else 0

lemma isFrame_pad {r : ℕ} (k : ℕ) {e : Fin r → E} (he : Orthonormal ℝ e) : IsFrame (pad k e) := by
  classical
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · unfold pad
    by_cases ha : a.val < r <;> by_cases hb : b.val < r
    · simp only [ha, hb, dif_pos]
      rw [orthonormal_iff_ite.1 he, orthonormal_iff_ite.1 he]
      by_cases hab : a = b
      · subst hab; simp
      · have : (⟨a.val, ha⟩ : Fin r) ≠ ⟨b.val, hb⟩ := fun h => hab (Fin.ext (Fin.mk.inj h))
        simp [hab, this]
    · have hab : a ≠ b := fun h => hb (h ▸ ha)
      simp [ha, hb, hab]
    · simp [ha, hb]
    · simp [ha, hb]
  · unfold pad
    by_cases ha : a.val < r
    · simp only [ha, dif_pos]; exact Or.inr (he.1 _)
    · simp only [ha, dif_neg, not_false_eq_true, norm_zero, true_or]

lemma mem_span_pad {r k : ℕ} (hrk : r ≤ k) (e : Fin r → E) (c : Fin r) :
    e c ∈ Submodule.span ℝ (Set.range (pad k e)) := by
  refine Submodule.subset_span ⟨⟨c.val, lt_of_lt_of_le c.2 hrk⟩, ?_⟩
  simp [pad, c.2]

end Pad

variable {m L : ℕ} {ι : Fin L → Fin m → Type} [∀ ℓ i, Fintype (ι ℓ i)]
  {κ : Fin m → Type} [∀ i, Fintype (κ i)]

lemma indep_coord {β : Fin m → Type} [∀ i, MeasurableSpace (β i)] (μ : ∀ i, Measure (β i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin m) :
    Indep (MeasurableSpace.comap (fun y : ∀ j, β j => y i) inferInstance)
      (MeasurableSpace.comap (fun (y : ∀ j, β j) (j : {j : Fin m // j ≠ i}) => y j) inferInstance)
      (Measure.pi μ) := by
  have hind : iIndepFun (fun j (y : ∀ j, β j) => y j) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  rw [iIndepFun_iff_iIndep] at hind
  have h := indep_iSup_of_disjoint (fun j => (measurable_pi_apply j).comap_le) hind
    (S := {i}) (T := {i}ᶜ) (Set.disjoint_singleton_left.2 (fun h => h rfl))
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · exact le_iSup₂ (f := fun j (_ : j ∈ ({i} : Set (Fin m))) =>
      MeasurableSpace.comap (fun y : ∀ j, β j => y j) inferInstance) i rfl
  · show MeasurableSpace.comap _ MeasurableSpace.pi ≤ _
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun j => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂ (f := fun j (_ : j ∈ ({i}ᶜ : Set (Fin m))) =>
      MeasurableSpace.comap (fun y : ∀ j, β j => y j) inferInstance) j.val j.2

end ApproxSyzygies.Smoothed.Dev.P48
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
/-! # Blueprint for Theorem 4.1: deterministic stubs (algebra, reduction, norms) -/
/-! ### Proved helpers -/
/-- A larger constant gives a smaller bad event. -/
lemma badT_anti {σ : Type} [Fintype σ] [DecidableEq σ] {m : ℕ} (d D : Fin m → ℕ)
    (abar : ∀ i, Hom σ (d i : ℤ)) (ρ : ℝ) {K K' : ℝ} (hK : K ≤ K') (t : ℕ) :
    BadT d D abar ρ K' t ⊆ BadT d D abar ρ K t := by
  rintro ω ⟨h, hh⟩
  exact ⟨h, lt_of_le_of_lt (mul_le_mul_of_nonneg_right hK (norm_nonneg _)) hh⟩

lemma norm_yPart_le' {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    {d : ℤ} (f : Hom (Y ⊕ Z) d) : ‖yPart f‖ ≤ ‖f‖ :=
  Dev.L44.norm_yPart_le f

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartD
open ApproxSyzygies.Smoothed
variable {σ : Type} [Fintype σ] [DecidableEq σ] {m : ℕ} {e : Fin m → ℤ}
/-! # Theorem 4.1 Part D: stub D1 (`ih_consequence`) -/
/-- The Koszul syzygies as a submodule. -/
noncomputable def koszulSub (p : ∀ i, Hom σ (e i)) (s : ℤ) :
    Submodule ℝ (Tup σ (fun i => s - e i)) where
  carrier := koszul p s
  add_mem' := Dev.L43.koszul_add
  zero_mem' := Dev.L44.zero_mem_koszul p s
  smul_mem' c h hh := by
    obtain ⟨Ω, h1, h2, h3⟩ := hh
    refine ⟨fun i j => c • Ω i j, fun i j => Submodule.smul_mem _ c (h1 i j),
      fun i j => by simp [h2 i j], fun i => ?_⟩
    rw [PiLp.smul_apply, Dev.L43.toPoly_smul, h3 i, Finset.smul_sum]
    simp

lemma isClosed_koszul (p : ∀ i, Hom σ (e i)) (s : ℤ) : IsClosed (koszul p s) :=
  Submodule.closed_of_finiteDimensional (koszulSub p s)

lemma good_of_noBad (p : ∀ i, Hom σ (e i)) (K : ℝ) (hK : 0 ≤ K) (s : ℤ)
    (h : ∀ x, Metric.infDist x (koszul p s) ≤ K * ‖mulMap p s x‖) :
    (LinearMap.ker (mulMap p s) : Set (Tup σ (fun i => s - e i))) = koszul p s ∧
      pinvNorm (mulMap p s) ≤ K := by
  have hne : (koszul p s).Nonempty := ⟨0, Dev.L44.zero_mem_koszul p s⟩
  have hker : (LinearMap.ker (mulMap p s) : Set (Tup σ (fun i => s - e i))) = koszul p s := by
    ext x
    constructor
    · intro hx
      have hx0 : mulMap p s x = 0 := hx
      have h0 : Metric.infDist x (koszul p s) = 0 := by
        apply le_antisymm _ Metric.infDist_nonneg
        simpa [hx0] using h x
      rw [← (isClosed_koszul p s).closure_eq]
      exact (Metric.mem_closure_iff_infDist_zero hne).2 h0
    · intro hx
      exact Dev.L43.mulMap_koszul hx
  refine ⟨hker, ?_⟩
  unfold pinvNorm
  apply csInf_le ⟨0, fun τ hτ => hτ.1⟩
  refine ⟨hK, fun u hu => ?_⟩
  refine le_trans ?_ (h u)
  refine (Metric.le_infDist hne).2 fun y hy => ?_
  have hyk : y ∈ LinearMap.ker (mulMap p s) := by
    have : y ∈ (LinearMap.ker (mulMap p s) : Set (Tup σ (fun i => s - e i))) := by
      rw [hker]; exact hy
    exact this
  have hin : inner ℝ y u = 0 := Submodule.inner_right_of_mem_orthogonal hyk hu
  rw [real_inner_comm] at hin
  have hsq : ‖u - y‖ ^ 2 = ‖u‖ ^ 2 + ‖y‖ ^ 2 := by
    rw [norm_sub_sq_real, hin]; ring
  rw [dist_eq_norm]
  nlinarith [norm_nonneg u, norm_nonneg (u - y), sq_nonneg ‖y‖]

lemma cond_of_noBad (p : ∀ i, Hom σ (e i)) (K : ℝ) (hK : 0 ≤ K) (t : ℕ)
    (h : ∀ s : ℕ, s < t → ∀ x, Metric.infDist x (koszul p (s : ℤ)) ≤ K * ‖mulMap p (s : ℤ) x‖) :
    KernelCond p t ∧ tauOf p t ≤ K := by
  refine ⟨fun s hs => (good_of_noBad p K hK (s : ℤ) (h s hs)).1, ?_⟩
  unfold tauOf
  exact Real.iSup_le (fun s => (good_of_noBad p K hK ((s : ℕ) : ℤ) (h s s.2)).2) hK

lemma cond_transfer {e e' : Fin m → ℤ} (he : e = e') (p : ∀ j, Hom σ (e j))
    (p' : ∀ j, Hom σ (e' j)) (hp : ∀ j, toPoly (p j) = toPoly (p' j)) (t : ℕ) (K : ℝ)
    (h : KernelCond p t ∧ tauOf p t ≤ K) : KernelCond p' t ∧ tauOf p' t ≤ K := by
  subst he
  have : p = p' := funext fun j => Dev.L43.toPoly_inj (hp j)
  subst this
  exact h

end ApproxSyzygies.Smoothed.Dev.G41.PartD
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartD
open ApproxSyzygies.Smoothed
theorem ih_consequence {Y : Type} [Fintype Y] [DecidableEq Y] {m : ℕ} (d D : Fin m → ℕ)
    (abary : ∀ i, Hom Y (d i : ℤ)) (ρ K : ℝ) (hK : 0 ≤ K) (t : ℕ)
    (ωy : ∀ i, monos Y (d i : ℤ) → ℝ) (h : IHgood d D abary ρ K t ωy) :
    (KernelCond (bfam d D abary ρ ωy) t ∧ tauOf (bfam d D abary ρ ωy) t ≤ K) ∧
    ∀ i, KernelCond (modGen d D i (toPoly (perturbOn (abary i) ρ (ωy i)))
          (fun j => perturbOn (abary j) ρ (ωy j))) t ∧
        tauOf (modGen d D i (toPoly (perturbOn (abary i) ρ (ωy i)))
          (fun j => perturbOn (abary j) ρ (ωy j))) t ≤ K := by
  refine ⟨cond_of_noBad _ K hK t fun s hs x => not_lt.1 fun hlt => (h s hs).1 ⟨x, hlt⟩,
    fun i => ?_⟩
  have h1 := cond_of_noBad (bfam d (Function.update D i 1) abary ρ ωy) K hK t
    fun s hs x => not_lt.1 fun hlt => (h s hs).2 i ⟨x, hlt⟩
  refine cond_transfer ?_ _ _ (fun j => ?_) t K h1
  · funext j
    by_cases hj : j = i
    · subst hj; simp [modDeg]
    · simp [modDeg, hj]
  · rw [bfam, Dev.L44.toPoly_powHom,
      Dev.L44.toPoly_modGen d D i _ (Dev.L43.IsH_toPoly _) _ j]
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]

end ApproxSyzygies.Smoothed.Dev.G41.PartD
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
/-! ### Stubs -/
alias ih_consequence := ApproxSyzygies.Smoothed.Dev.G41.PartD.ih_consequence

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartD
open ApproxSyzygies.Smoothed
variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
/-! # Theorem 4.1 Part D: stub D2 (`reduction_bound`, Lemmas 4.2 + 4.3 with `R = t`) -/
/-- The gradation pieces are orthogonal: `‖f[0 : r]‖ ≤ ‖f‖`. -/
lemma norm_gradeSeg_le' (r : ℕ) {d : ℤ} (f : Hom (Y ⊕ Z) d) : ‖gradeSeg r f‖ ≤ ‖f‖ := by
  rw [PiLp.norm_eq_of_L2, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  have h1 : ∀ r' : Fin (r + 1), ‖(gradeSeg r f) r'‖ ^ 2 =
      ∑ α : monos (Y ⊕ Z) d,
        (if zdeg (α : (Y ⊕ Z) →₀ ℕ) = (r' : ℕ) then ‖f α‖ ^ 2 else 0) := by
    intro r'
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro α _
    simp only [gradeSeg, grade, PiLp.toLp_apply]
    split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro α _
  by_cases hz : zdeg (α : (Y ⊕ Z) →₀ ℕ) < r + 1
  · rw [Finset.sum_eq_single (⟨zdeg (α : (Y ⊕ Z) →₀ ℕ), hz⟩ : Fin (r + 1))]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext h.symm)
    · simp
  · rw [Finset.sum_eq_zero]
    · positivity
    · intro b _
      rw [if_neg]
      intro h
      exact hz (by rw [h]; exact b.2)

lemma zdeg_lt_of_mem {d : ℤ} (t : ℕ) (hd : d ≤ t) (α : (Y ⊕ Z) →₀ ℕ) (hα : α ∈ monos (Y ⊕ Z) d) :
    zdeg α < t + 1 := by
  have h1 := (Dev.L43.mem_monos_iff d α).1 hα
  have h2 := Dev.L43.deg_split α
  rw [Dev.L43.zdeg_eq]
  omega

lemma sum_gradeTup {m : ℕ} (t : ℕ) {e : Fin m → ℤ} (he : ∀ i, 0 ≤ e i)
    (x : Tup (Y ⊕ Z) (fun i => (t : ℤ) - e i)) :
    ∑ r ∈ Finset.range (t + 1), gradeTup r x = x := by
  ext i ⟨α, hα⟩
  simp only [WithLp.ofLp_sum, Finset.sum_apply, gradeTup, grade]
  rw [Finset.sum_ite_eq, if_pos]
  rw [Finset.mem_range]
  exact zdeg_lt_of_mem t (show (t : ℤ) - e i ≤ t by linarith [he i]) α hα

end ApproxSyzygies.Smoothed.Dev.G41.PartD
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartD
open ApproxSyzygies.Smoothed
/-- The norm bound of Lemma 4.3 in the form used by `redConst`. -/
lemma bound_M (t : ℕ) (ht : 1 ≤ t) (τ' τ₀ β N : ℝ) (hτ' : 0 ≤ τ') (hτ : τ' ≤ τ₀) (hβ : 0 ≤ β)
    (hβN : β ≤ N) (y : ℝ)
    (hy : y ≤ 1 + (2 : ℝ) ^ ((t : ℝ) / 2) * τ' *
      max ((1 + (2 : ℝ) ^ ((t : ℝ) / 2) * τ' * β) ^ ((t : ℤ) - 1))
        (β * (1 + (2 : ℝ) ^ ((t : ℝ) / 2) * τ' * β) ^ ((t : ℤ) - 1))) :
    y ≤ 1 + 2 ^ (t * t) * (1 + τ₀) ^ t * (1 + N) ^ t := by
  set c := (2 : ℝ) ^ ((t : ℝ) / 2) with hc
  have hc1 : 1 ≤ c := Real.one_le_rpow (by norm_num) (by positivity)
  have hcT : c ≤ (2 : ℝ) ^ t := by
    rw [hc, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have : (0 : ℝ) ≤ t := by positivity
      linarith)
  have hτ0 : 0 ≤ τ₀ := hτ'.trans hτ
  have hN0 : 0 ≤ N := hβ.trans hβN
  set X := 1 + c * τ' * β with hX
  have hX1 : 1 ≤ X := by
    have : 0 ≤ c * τ' * β := by positivity
    linarith
  have hz : X ^ ((t : ℤ) - 1) = X ^ (t - 1) := by
    rw [show (t : ℤ) - 1 = ((t - 1 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [hz] at hy
  have hXp : 0 ≤ X ^ (t - 1) := by positivity
  have hmax : max (X ^ (t - 1)) (β * X ^ (t - 1)) ≤ (1 + N) * X ^ (t - 1) :=
    max_le (by nlinarith) (by nlinarith)
  set G := c * (1 + τ₀) * (1 + N) with hG
  have hcτβ : c * τ' * β ≤ c * τ₀ * N :=
    mul_le_mul (mul_le_mul_of_nonneg_left hτ (by linarith)) hβN hβ (by positivity)
  have hXG : X ≤ G := by
    rw [hX, hG]
    nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ c by linarith) hτ0) hN0,
      mul_nonneg (show (0:ℝ) ≤ c by linarith) hτ0, mul_nonneg (show (0:ℝ) ≤ c by linarith) hN0]
  have hcτ : c * τ' * (1 + N) ≤ G := by
    rw [hG]
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    nlinarith
  have hXtG : X ^ (t - 1) ≤ G ^ (t - 1) := pow_le_pow_left₀ (by linarith) hXG _
  have hGt : G ^ t ≤ 2 ^ (t * t) * (1 + τ₀) ^ t * (1 + N) ^ t := by
    rw [hG, mul_pow, mul_pow, pow_mul]
    gcongr
  have hcτ0 : 0 ≤ c * τ' := by positivity
  calc y ≤ 1 + c * τ' * max (X ^ (t - 1)) (β * X ^ (t - 1)) := hy
    _ ≤ 1 + c * τ' * ((1 + N) * X ^ (t - 1)) := by gcongr
    _ = 1 + (c * τ' * (1 + N)) * X ^ (t - 1) := by ring
    _ ≤ 1 + G * G ^ (t - 1) := by
        gcongr
    _ = 1 + G ^ t := by
        rw [← pow_succ']; congr 2; omega
    _ ≤ _ := by linarith

theorem reduction_bound {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    {m : ℕ} (d D : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i) (hD : ∀ i, 1 ≤ D i) (t : ℕ) (ht : 1 ≤ t)
    (a : ∀ i, Hom (Y ⊕ Z) (d i : ℤ)) (τ₀ N : ℝ) (hτ₀ : 0 ≤ τ₀) (hN : 0 ≤ N)
    (hK : KernelCond (yParts fun i => powHom (a i) (D i)) t)
    (hτ : tauOf (yParts fun i => powHom (a i) (D i)) t ≤ τ₀)
    (hb : tupNorm (fun i => powHom (a i) (D i)) ≤ N)
    (h : Tup (Y ⊕ Z) (fun i => (t : ℤ) - ((d i : ℤ) * (D i : ℕ)))) :
    Metric.infDist h (koszul (fun i => powHom (a i) (D i)) (t : ℤ)) ≤
      redConst t τ₀ N * (‖mulMap (fun i => powHom (a i) (D i)) (t : ℤ) h‖ +
        ‖gVec d D t (yParts a) (yPartTup h)‖) := by
  -- Lemma 4.2
  obtain ⟨L₁, L₂, h42⟩ := ApproxSyzygies.Smoothed.lemma_4_2 (Y := Y) d D hd hD t ht
  have hK1 : (LinearMap.ker (mulMap (yParts fun i => powHom (a i) (D i)) ((t : ℤ) - 1)) :
      Set (Tup Y (fun i => (t : ℤ) - 1 - (d i : ℤ) * (D i : ℤ)))) =
        koszul (yParts fun i => powHom (a i) (D i)) ((t : ℤ) - 1) := by
    have := hK (t - 1) (by omega)
    rw [show ((t - 1 : ℕ) : ℤ) = (t : ℤ) - 1 by omega] at this
    exact this
  obtain ⟨hL₁, hL₂, hdec⟩ := h42 Z a hK1
  obtain ⟨k₀, hk₀, hh0⟩ := hdec h
  set b := fun i => powHom (a i) (D i) with hb_def
  set f := mulMap b (t : ℤ) h with hf
  set g := gVec d D t (yParts a) (yPartTup h) with hg
  set τ := tauOf (yParts b) t with hτdef
  set h₀ := L₁ (yParts b) g + L₂ (yParts b) (yPart f) with hh₀
  have hτ0 : 0 ≤ τ := Dev.L44.tauOf_nonneg' _ _
  have hβ0 : 0 ≤ tupNorm b := Dev.L44.tupNorm_nonneg' _
  have hβy : tupNorm (yParts b) ≤ tupNorm b := by
    have := Dev.L44.norm_tup_le_of (WithLp.toLp 2 (yParts b) : Tup Y _)
      (WithLp.toLp 2 b : Tup (Y ⊕ Z) _) 1 zero_le_one (fun j => by
        simpa [yParts] using Dev.L44.norm_yPart_le (b j))
    unfold tupNorm; simpa using this
  have hh₀n : ‖h₀‖ ≤ (1 + τ₀ * N) * ‖g‖ + τ₀ * ‖f‖ := by
    have e1 : ‖L₁ (yParts b) g‖ ≤ (1 + τ₀ * N) * ‖g‖ := by
      refine ((L₁ (yParts b)).le_opNorm g).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      refine hL₁.trans ?_
      have : τ * tupNorm (yParts b) ≤ τ₀ * N :=
        mul_le_mul hτ (hβy.trans hb) (Dev.L44.tupNorm_nonneg' _) hτ₀
      linarith
    have e2 : ‖L₂ (yParts b) (yPart f)‖ ≤ τ₀ * ‖f‖ := by
      refine ((L₂ (yParts b)).le_opNorm _).trans ?_
      exact mul_le_mul (hL₂.trans hτ) (Dev.L44.norm_yPart_le f) (norm_nonneg _) hτ₀
    exact (norm_add_le _ _).trans (add_le_add e1 e2)
  -- Lemma 4.3 with `T = R = t`
  obtain ⟨F, H, h43⟩ := Dev.L44.l43' t (Y := Y) (Z := Z) (fun j => d j * D j)
    (fun j => (d j : ℤ) * (D j : ℤ)) (by funext j; push_cast; ring)
    (fun j => by have := hd j; have := hD j; nlinarith) t le_rfl t le_rfl
  obtain ⟨hFH, hdec3⟩ := h43 b hK
  have hmem : h₀ - yPartTup h ∈ koszul (yParts b) (t : ℤ) := by
    have : h₀ - yPartTup h = -k₀ := by rw [hh0, hh₀]; abel
    rw [this]
    exact (koszulSub (yParts b) (t : ℤ)).neg_mem hk₀
  obtain ⟨k, hk, -, hgr⟩ := hdec3 h h₀ hmem
  have he0 : ∀ i, (0 : ℤ) ≤ (d i : ℤ) * (D i : ℤ) := fun i => by positivity
  have hsum : h - k = ∑ r ∈ Finset.range (t + 1), (F r b (gradeSeg r f) + H r b h₀) := by
    have e1 := sum_gradeTup t he0 h
    have e2 := sum_gradeTup t he0 k
    conv_lhs => rw [← e1, ← e2]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    rw [hgr r (by omega)]
    abel
  set M : ℝ := 1 + 2 ^ (t * t) * (1 + τ₀) ^ t * (1 + N) ^ t with hM
  have hFM : ∀ r, r ≤ t → ‖F r b‖ ≤ M ∧ ‖H r b‖ ≤ M := fun r hr =>
    ⟨bound_M t ht τ τ₀ (tupNorm b) N hτ0 hτ hβ0 hb _ (hFH r hr).1,
      bound_M t ht τ τ₀ (tupNorm b) N hτ0 hτ hβ0 hb _ (hFH r hr).2⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hterm : ∀ r ∈ Finset.range (t + 1),
      ‖F r b (gradeSeg r f) + H r b h₀‖ ≤ M * ‖f‖ + M * ‖h₀‖ := by
    intro r hr
    rw [Finset.mem_range] at hr
    obtain ⟨hF, hH⟩ := hFM r (by omega)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact ((F r b).le_opNorm _).trans
        (mul_le_mul hF (norm_gradeSeg_le' r f) (norm_nonneg _) hM0)
    · exact ((H r b).le_opNorm _).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  have hfg : ‖f‖ + ‖h₀‖ ≤ (2 + τ₀ + τ₀ * N) * (‖f‖ + ‖g‖) := by
    have := norm_nonneg f
    have := norm_nonneg g
    have : 0 ≤ τ₀ * N := mul_nonneg hτ₀ hN
    nlinarith
  calc Metric.infDist h (koszul b (t : ℤ)) ≤ dist h k := Metric.infDist_le_dist_of_mem hk
    _ = ‖h - k‖ := dist_eq_norm _ _
    _ = ‖∑ r ∈ Finset.range (t + 1), (F r b (gradeSeg r f) + H r b h₀)‖ := by rw [hsum]
    _ ≤ ∑ r ∈ Finset.range (t + 1), (M * ‖f‖ + M * ‖h₀‖) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = ((t : ℝ) + 1) * M * (‖f‖ + ‖h₀‖) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ ((t : ℝ) + 1) * M * ((2 + τ₀ + τ₀ * N) * (‖f‖ + ‖g‖)) :=
        mul_le_mul_of_nonneg_left hfg (by positivity)
    _ = redConst t τ₀ N * (‖f‖ + ‖g‖) := by rw [redConst, hM]; ring

end ApproxSyzygies.Smoothed.Dev.G41.PartD
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias reduction_bound := ApproxSyzygies.Smoothed.Dev.G41.PartD.reduction_bound

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartD
open ApproxSyzygies.Smoothed
/-! # Theorem 4.1 Part D: stubs D3–D6 (pure-`y` parts, generator norms, renaming) -/
/-! ### D6: renaming is an isometry -/
lemma mfact_domCongr {σ σ' : Type} [Fintype σ] [Fintype σ'] (e : σ ≃ σ') (α : σ' →₀ ℕ) :
    mfact (Finsupp.equivMapDomain e.symm α) = mfact α := by
  unfold mfact
  simp only [Finsupp.equivMapDomain_apply, Equiv.symm_symm]
  exact Equiv.prod_comp e (fun j => ((α j).factorial : ℝ))

lemma deg_domCongr {σ σ' : Type} [Fintype σ] [Fintype σ'] (e : σ ≃ σ') (α : σ' →₀ ℕ) :
    Dev.L43.deg (Finsupp.equivMapDomain e.symm α) = Dev.L43.deg α := by
  unfold Dev.L43.deg
  simp only [Finsupp.equivMapDomain_apply, Equiv.symm_symm]
  exact Equiv.sum_comp e (fun j => α j)

theorem norm_renameHom {σ σ' : Type} [Fintype σ] [DecidableEq σ] [Fintype σ'] [DecidableEq σ']
    (e : σ ≃ σ') {d : ℤ} (p : Hom σ d) : ‖renameHom e p‖ = ‖p‖ := by
  have key : ‖renameHom e p‖ ^ 2 = ‖p‖ ^ 2 := by
    rw [renameHom, Dev.A1.normsq_ofPoly]
    conv_rhs => rw [← Dev.L43.ofPoly_toPoly p, Dev.A1.normsq_ofPoly]
    refine Finset.sum_equiv (Finsupp.domCongr e.symm).toEquiv (fun α => ?_) (fun α _ => ?_)
    · simp only [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Finsupp.domCongr_apply,
        Dev.L43.mem_monos_iff, deg_domCongr]
    · simp only [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Finsupp.domCongr_apply,
        mfact_domCongr]
      have hα : α = Finsupp.mapDomain e (Finsupp.equivMapDomain e.symm α) := by
        rw [← Finsupp.equivMapDomain_eq_mapDomain]
        ext x
        simp
      have hc : coeff α (rename e (toPoly p)) =
          coeff (Finsupp.equivMapDomain e.symm α) (toPoly p) := by
        conv_lhs => rw [hα]
        exact coeff_rename_mapDomain _ e.injective _ _
      rw [hc]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 key

end ApproxSyzygies.Smoothed.Dev.G41.PartD
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartD
open ApproxSyzygies.Smoothed
variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
/-! ### D3: pure-`y` parts of the perturbed family -/
lemma yPart_add' {d : ℤ} (f g : Hom (Y ⊕ Z) d) : yPart (f + g) = yPart f + yPart g := by
  unfold yPart
  rw [Dev.L43.toPoly_add, map_add, Dev.L44.ofPoly_add']

lemma yPart_smul' {d : ℤ} (c : ℝ) (f : Hom (Y ⊕ Z) d) : yPart (c • f) = c • yPart f := by
  unfold yPart
  rw [Dev.L43.toPoly_smul, map_smul, Dev.L44.ofPoly_smul']

lemma join_zero_eq (β : Y →₀ ℕ) :
    Dev.L43.join β (0 : Z →₀ ℕ) = Finsupp.mapDomain Sum.inl β := by
  rw [Dev.L43.eq_iff_yp_zp]
  constructor
  · ext y
    simp [Finsupp.mapDomain_apply Sum.inl_injective]
  · ext z
    simp only [Dev.L43.zp_join, Dev.L43.zp_apply, Finsupp.coe_zero, Pi.zero_apply]
    rw [Finsupp.mapDomain_of_notMem_range]
    simp

lemma yPart_toLp {d : ℤ} (ω : monos (Y ⊕ Z) d → ℝ) :
    yPart (WithLp.toLp 2 ω : Hom (Y ⊕ Z) d) =
      WithLp.toLp 2 (fun β : monos Y d =>
        if h : Finsupp.mapDomain Sum.inl (β : Y →₀ ℕ) ∈ monos (Y ⊕ Z) d
          then ω ⟨_, h⟩ else 0) := by
  ext ⟨β, hβ⟩
  rw [Dev.L44.yPart_eq]
  simp only [ofPoly, PiLp.toLp_apply]
  rw [Dev.L43.coeff_E_join, Dev.L43.coeff_toPoly', join_zero_eq]
  split_ifs with h
  · have hm0 : mfact (0 : Z →₀ ℕ) = 1 := by simp [mfact]
    have hmf : mfact (Finsupp.mapDomain Sum.inl β : (Y ⊕ Z) →₀ ℕ) = mfact β := by
      rw [← join_zero_eq (Z := Z), Dev.L43.mfact_join, hm0, mul_one]
    rw [hmf]
    have h1 := Dev.A1.mfact_pos β
    have h2 : (0:ℝ) < (d.toNat.factorial : ℝ) := by positivity
    rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
    rw [show (d.toNat.factorial : ℝ) / mfact β * (mfact β / (d.toNat.factorial : ℝ)) = 1 by
      field_simp]
    simp only [Real.sqrt_one, mul_one]
  · simp

end ApproxSyzygies.Smoothed.Dev.G41.PartD
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartD
open ApproxSyzygies.Smoothed
theorem yParts_perturbOn {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    {m : ℕ} {d : Fin m → ℤ} (abar : ∀ i, Hom (Y ⊕ Z) (d i)) (ρ : ℝ)
    (ω : ∀ i, monos (Y ⊕ Z) (d i) → ℝ) :
    yParts (fun i => perturbOn (abar i) ρ (ω i)) =
      fun i => perturbOn (yPart (abar i)) ρ (restrictY ω i) := by
  funext i
  simp only [yParts, perturbOn]
  rw [yPart_add', yPart_smul', yPart_toLp (ω i)]
  rfl

end ApproxSyzygies.Smoothed.Dev.G41.PartD
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias yParts_perturbOn := ApproxSyzygies.Smoothed.Dev.G41.PartD.yParts_perturbOn

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartD
open ApproxSyzygies.Smoothed
/-! ### D4: pure-`y` parts of powers -/
lemma yPart_powHom {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    {d : ℤ} (a : Hom (Y ⊕ Z) d) (D : ℕ) : yPart (powHom a D) = powHom (yPart a) D := by
  apply Dev.L43.toPoly_inj
  rw [Dev.L42.toPoly_yParts_pow, Dev.L44.toPoly_powHom]

theorem yParts_bfam {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    {m : ℕ} (d D : Fin m → ℕ) (abar : ∀ i, Hom (Y ⊕ Z) (d i : ℤ)) (ρ : ℝ)
    (ω : ∀ i, monos (Y ⊕ Z) (d i : ℤ) → ℝ) :
    yParts (bfam d D abar ρ ω) = bfam d D (fun i => yPart (abar i)) ρ (restrictY ω) := by
  funext i
  have h := congrFun (yParts_perturbOn abar ρ ω) i
  simp only [yParts] at h
  simp only [yParts, bfam]
  rw [yPart_powHom, h]

end ApproxSyzygies.Smoothed.Dev.G41.PartD
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias yParts_bfam := ApproxSyzygies.Smoothed.Dev.G41.PartD.yParts_bfam

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartD
open ApproxSyzygies.Smoothed
/-! ### D5: generator norms -/
lemma choose_add_le_pow (n : ℕ) : ∀ d : ℕ, (n + d).choose d ≤ (n + 1) ^ d
  | 0 => by simp
  | d + 1 => by
    have ih := choose_add_le_pow n d
    have key := Nat.add_one_mul_choose_eq (n + d) d
    have h1 : (n + (d + 1)).choose (d + 1) * (d + 1) ≤ (n + 1) ^ (d + 1) * (d + 1) := by
      rw [show n + (d + 1) = n + d + 1 by omega, ← key, pow_succ]
      calc (n + d + 1) * (n + d).choose d ≤ (n + d + 1) * (n + 1) ^ d :=
            Nat.mul_le_mul_left _ ih
        _ ≤ ((n + 1) * (d + 1)) * (n + 1) ^ d := by
            apply Nat.mul_le_mul_right
            show n + d + 1 ≤ (n + 1) * (d + 1)
            nlinarith
        _ = (n + 1) ^ d * (n + 1) * (d + 1) := by ring
    exact Nat.le_of_mul_le_mul_right h1 (by omega)

lemma card_monos_le {σ : Type} [Fintype σ] [DecidableEq σ] (d : ℕ) :
    (monos σ (d : ℤ)).card ≤ (Fintype.card σ + 1) ^ d := by
  simp only [monos, Nat.cast_nonneg, if_true, Int.toNat_natCast]
  rw [Finset.card_finsuppAntidiag_nat_eq_choose]
  calc (Fintype.card σ + d - 1).choose d ≤ (Fintype.card σ + d).choose d :=
        Nat.choose_le_choose _ (by omega)
    _ ≤ _ := choose_add_le_pow _ d

lemma norm_one_hom {σ : Type} [Fintype σ] [DecidableEq σ] :
    ‖(ofPoly (0 : ℤ) (1 : MvPolynomial σ ℝ) : Hom σ 0)‖ ≤ 1 := by
  have h := Dev.A1.normsq_ofPoly (σ := σ) (0 : ℤ) 1
  have hm : monos σ (0 : ℤ) = {0} := by simp [monos]
  have hs : ∑ α ∈ monos σ (0 : ℤ), (coeff α (1 : MvPolynomial σ ℝ)) ^ 2 * mfact α /
      ((0 : ℤ).toNat.factorial : ℝ) = 1 := by
    rw [hm, Finset.sum_singleton]; simp [mfact]
  rw [hs] at h
  nlinarith [norm_nonneg (ofPoly (0 : ℤ) (1 : MvPolynomial σ ℝ) : Hom σ 0)]

lemma norm_powHom_le {σ : Type} [Fintype σ] [DecidableEq σ] {k : ℤ} (hk : 0 ≤ k) (a : Hom σ k)
    (D : ℕ) : ‖powHom a D‖ ≤ ‖a‖ ^ D := by
  have h := Dev.L44.norm_pow_mul_le hk a (ofPoly (0 : ℤ) (1 : MvPolynomial σ ℝ) : Hom σ 0) D
    (k * D) (by ring)
  have h1 : toPoly (ofPoly (0 : ℤ) (1 : MvPolynomial σ ℝ) : Hom σ 0) = 1 := by
    apply Dev.L43.toPoly_ofPoly
    intro γ hγ
    rw [coeff_one] at hγ
    split_ifs at hγ with h0
    · subst h0; simp [Dev.L43.deg]
    · exact absurd rfl hγ
  rw [h1, mul_one] at h
  calc ‖powHom a D‖ = ‖ofPoly (k * D) (toPoly a ^ D)‖ := rfl
    _ ≤ ‖a‖ ^ D * ‖(ofPoly (0 : ℤ) (1 : MvPolynomial σ ℝ) : Hom σ 0)‖ := h
    _ ≤ ‖a‖ ^ D * 1 := mul_le_mul_of_nonneg_left norm_one_hom (by positivity)
    _ = ‖a‖ ^ D := mul_one _

theorem tupNorm_bfam_le {σ : Type} [Fintype σ] [DecidableEq σ] {m : ℕ} (dmax Dmax : ℕ)
    (d D : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i ∧ d i ≤ dmax) (hD : ∀ i, 1 ≤ D i ∧ D i ≤ Dmax)
    (abar : ∀ i, Hom σ (d i : ℤ)) (habar : ∀ i, ‖abar i‖ ≤ 1) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (ω : ∀ i, monos σ (d i : ℤ) → ℝ) (hN : Ngood d ω) :
    tupNorm (bfam d D abar ρ ω) ≤
      (m : ℝ) * (1 + 2 * Real.sqrt (((Fintype.card σ + 1 : ℕ) : ℝ) ^ dmax)) ^ Dmax := by
  set A : ℝ := 1 + 2 * Real.sqrt (((Fintype.card σ + 1 : ℕ) : ℝ) ^ dmax) with hA
  have hA1 : 1 ≤ A := by
    have : 0 ≤ Real.sqrt (((Fintype.card σ + 1 : ℕ) : ℝ) ^ dmax) := Real.sqrt_nonneg _
    linarith
  have ha : ∀ i, ‖perturbOn (abar i) ρ (ω i)‖ ≤ A := by
    intro i
    unfold perturbOn
    have hc : ((monos σ (d i : ℤ)).card : ℝ) ≤ ((Fintype.card σ + 1 : ℕ) : ℝ) ^ dmax := by
      have h1 := card_monos_le (σ := σ) (d i)
      have h2 : (Fintype.card σ + 1) ^ d i ≤ (Fintype.card σ + 1) ^ dmax :=
        Nat.pow_le_pow_right (by omega) (hd i).2
      exact_mod_cast h1.trans h2
    have hs := Real.sqrt_le_sqrt hc
    calc ‖abar i + ρ • (WithLp.toLp 2 (ω i) : Hom σ (d i : ℤ))‖
        ≤ ‖abar i‖ + ‖ρ • (WithLp.toLp 2 (ω i) : Hom σ (d i : ℤ))‖ := norm_add_le _ _
      _ = ‖abar i‖ + ρ * ‖(WithLp.toLp 2 (ω i) : Hom σ (d i : ℤ))‖ := by
          rw [norm_smul, Real.norm_of_nonneg hρ.le]
      _ ≤ 1 + 1 * (2 * Real.sqrt ((monos σ (d i : ℤ)).card : ℝ)) := by
          gcongr
          · exact habar i
          · exact hN i
      _ ≤ A := by rw [hA]; linarith
  have hb : ∀ i, ‖bfam d D abar ρ ω i‖ ≤ A ^ Dmax := by
    intro i
    calc ‖bfam d D abar ρ ω i‖ ≤ ‖perturbOn (abar i) ρ (ω i)‖ ^ D i :=
          norm_powHom_le (by positivity) _ _
      _ ≤ A ^ D i := pow_le_pow_left₀ (norm_nonneg _) (ha i) _
      _ ≤ A ^ Dmax := pow_le_pow_right₀ hA1 (hD i).2
  unfold tupNorm
  rw [PiLp.norm_eq_of_L2, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc ∑ i, ‖(WithLp.toLp 2 (bfam d D abar ρ ω) : Tup σ _) i‖ ^ 2
      ≤ ∑ _i : Fin m, (A ^ Dmax) ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hb i) 2
    _ = (m : ℝ) * (A ^ Dmax) ^ 2 := by simp
    _ ≤ ((m : ℝ) * A ^ Dmax) ^ 2 := by
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        rcases Nat.eq_zero_or_pos m with h | h
        · simp [h]
        · have : (1 : ℝ) ≤ m := by exact_mod_cast h
          nlinarith

end ApproxSyzygies.Smoothed.Dev.G41.PartD
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias tupNorm_bfam_le := ApproxSyzygies.Smoothed.Dev.G41.PartD.tupNorm_bfam_le

alias norm_renameHom := ApproxSyzygies.Smoothed.Dev.G41.PartD.norm_renameHom

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartP
open ApproxSyzygies.Smoothed
/-! # Theorem 4.1 Part P: probabilistic stubs P1–P3 (marginal, norm event, renaming) -/
/-! ### Marginals of i.i.d. products along injections -/
lemma measurePreserving_comp_inj {ι ι' : Type} [Fintype ι] [Fintype ι'] (f : ι' → ι)
    (hf : Function.Injective f) (g : Measure ℝ) [IsProbabilityMeasure g] :
    MeasurePreserving (fun x : ι → ℝ => x ∘ f) (Measure.pi fun _ : ι => g)
      (Measure.pi fun _ : ι' => g) := by
  classical
  have hmeas : Measurable (fun x : ι → ℝ => x ∘ f) :=
    measurable_pi_lambda _ fun i' => measurable_pi_apply (f i')
  refine ⟨hmeas, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  let t : ι → Set ℝ := fun a => ⋂ i' : ι', if f i' = a then s i' else Set.univ
  have ht : ∀ a, MeasurableSet (t a) := fun a =>
    MeasurableSet.iInter fun i' => by split_ifs; exacts [hs i', MeasurableSet.univ]
  have hpre : (fun x : ι → ℝ => x ∘ f) ⁻¹' Set.univ.pi s = Set.univ.pi t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply, t, Set.mem_iInter]
    constructor
    · intro h a i'
      split_ifs with ha
      · subst ha; exact h i'
      · trivial
    · intro h i'
      simpa using h (f i') i'
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre, Measure.pi_pi]
  symm
  apply Fintype.prod_of_injective f hf
  · intro a ha
    have : t a = Set.univ := by
      ext y
      simp only [t, Set.mem_iInter, Set.mem_univ, iff_true]
      intro i'
      rw [if_neg (fun h => ha ⟨i', h⟩)]
      trivial
    rw [this, measure_univ]
  · intro i'
    congr 1
    ext y
    simp only [t, Set.mem_iInter]
    constructor
    · intro hy j
      split_ifs with hj
      · rw [hf hj]; exact hy
      · trivial
    · intro hy
      simpa using hy i'

/-! ### P1 -/
lemma inl_mem_monos {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    {d : ℤ} (β : monos Y d) :
    Finsupp.mapDomain Sum.inl (β : Y →₀ ℕ) ∈ monos (Y ⊕ Z) d := by
  rw [← PartD.join_zero_eq (Z := Z), Dev.L43.mem_monos_iff, Dev.L43.deg_join]
  have h := (Dev.L43.mem_monos_iff d (β : Y →₀ ℕ)).1 β.2
  simpa [Dev.L43.deg] using h

lemma inl_mono_injective {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (d : ℤ) :
    Function.Injective (fun β : monos Y d =>
      (⟨_, inl_mem_monos (Z := Z) β⟩ : monos (Y ⊕ Z) d)) := by
  intro β β' h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  exact Finsupp.mapDomain_injective Sum.inl_injective h'

theorem measurePreserving_restrictY {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z]
    [DecidableEq Z] {m : ℕ} (d : Fin m → ℤ) :
    MeasurePreserving (restrictY (Y := Y) (Z := Z) (d := d)) (gaussOn (Y ⊕ Z) m d)
      (gaussOn Y m d) := by
  have heq : (restrictY (Y := Y) (Z := Z) (d := d)) = fun ω i =>
      (fun x => x ∘ (fun β : monos Y (d i) =>
        (⟨_, inl_mem_monos (Z := Z) β⟩ : monos (Y ⊕ Z) (d i)))) (ω i) := by
    funext ω i β
    simp only [restrictY, Function.comp_apply]
    rw [dif_pos (inl_mem_monos β)]
  rw [heq]
  exact measurePreserving_pi _ _ fun i =>
    measurePreserving_comp_inj _ (inl_mono_injective (Z := Z) (d i)) _

end ApproxSyzygies.Smoothed.Dev.G41.PartP
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
/-! # Blueprint for Theorem 4.1: probabilistic stubs (marginals, norm event, transport) -/
alias measurePreserving_restrictY := ApproxSyzygies.Smoothed.Dev.G41.PartP.measurePreserving_restrictY

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartP
open ApproxSyzygies.Smoothed
/-! ### P2 -/
lemma norm_toLp_comp {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (x : ι → ℝ) :
    ‖(WithLp.toLp 2 (x ∘ e) : EuclideanSpace ℝ ι')‖ = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp e (fun j => ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι) j‖ ^ 2)

/-- One generator: `P[‖ω‖ > 2√N] ≤ e^{-N/2}` for `N = |ι| ≥ 1` standard Gaussians. -/
lemma gauss_norm_tail {ι : Type} [Fintype ι] (hN : 1 ≤ Fintype.card ι) :
    (Measure.pi fun _ : ι => gaussianReal 0 1)
        {x | 2 * Real.sqrt (Fintype.card ι : ℝ) < ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖} ≤
      ENNReal.ofReal (Real.exp (-(Fintype.card ι : ℝ) / 2)) := by
  set N := Fintype.card ι
  let e : Fin N ≃ ι := (Fintype.equivFin ι).symm
  have hmp := measurePreserving_comp_inj (fun j : Fin N => e j) e.injective (gaussianReal 0 1)
  have h2 := (lemma_a_2 N hN 1 one_pos 0).2
  have hg : (Measure.pi fun j : Fin N => gaussianReal ((0 : Fin N → ℝ) j) ((1 : ℝ) ^ 2).toNNReal)
      = Measure.pi fun _ : Fin N => gaussianReal 0 1 := by
    simp
  rw [hg] at h2
  set T : Set (Fin N → ℝ) :=
    {x | 2 * 1 * Real.sqrt N < ‖(WithLp.toLp 2 (x - 0) : EuclideanSpace ℝ (Fin N))‖}
  have hsub : {x : ι → ℝ | 2 * Real.sqrt (N : ℝ) < ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖} ⊆
      (fun x : ι → ℝ => x ∘ fun j : Fin N => e j) ⁻¹' T := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    simp only [T, Set.mem_preimage, Set.mem_ofPred_eq, sub_zero, mul_one]
    have := norm_toLp_comp e x
    simp only at this
    rw [show (fun j : Fin N => e j) = ⇑e from rfl, this]
    exact hx
  calc _ ≤ (Measure.pi fun _ : ι => gaussianReal 0 1)
          ((fun x : ι → ℝ => x ∘ fun j : Fin N => e j) ⁻¹' T) := measure_mono hsub
    _ ≤ ((Measure.pi fun _ : ι => gaussianReal 0 1).map
          (fun x : ι → ℝ => x ∘ fun j : Fin N => e j)) T :=
        Measure.le_map_apply hmp.measurable.aemeasurable T
    _ = _ := by rw [hmp.map_eq]
    _ ≤ _ := h2

lemma card_monos_ge {σ : Type} [Fintype σ] [DecidableEq σ] (d : ℕ) (hd : 1 ≤ d) :
    ((Fintype.card σ : ℝ) ^ d / (d.factorial : ℝ)) ≤ ((monos σ (d : ℤ)).card : ℝ) := by
  simp only [monos, Nat.cast_nonneg, if_true, Int.toNat_natCast]
  rw [Finset.card_finsuppAntidiag_nat_eq_choose]
  have h := Nat.pow_le_choose (α := ℝ) d (Fintype.card σ + d - 1)
  have he : Fintype.card σ + d - 1 + 1 - d = Fintype.card σ := by omega
  rwa [he] at h

theorem norm_event {σ : Type} [Fintype σ] [DecidableEq σ] {m : ℕ} [NeZero m] (dmax : ℕ)
    (d : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i ∧ d i ≤ dmax) :
    gaussOn σ m (fun i => (d i : ℤ)) {ω | ¬ Ngood d ω} ≤
      ENNReal.ofReal ((m : ℝ) * Real.exp (-((Fintype.card σ : ℝ) ^
        (Finset.univ.inf' Finset.univ_nonempty d) / (2 * (dmax.factorial : ℝ))))) := by
  set n := Fintype.card σ
  set dl := Finset.univ.inf' Finset.univ_nonempty d
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- no variables: the right side is at least `1`
    have hdl : 1 ≤ dl := Finset.le_inf' _ _ (fun i _ => (hd i).1)
    have : IsProbabilityMeasure (gaussOn σ m (fun i => (d i : ℤ))) := by
      unfold gaussOn; infer_instance
    have hz : (n : ℝ) ^ dl = 0 := by rw [hn]; simp; omega
    rw [hz, zero_div, neg_zero, Real.exp_zero, mul_one, ENNReal.ofReal_natCast]
    calc _ ≤ (1 : ENNReal) := prob_le_one
      _ ≤ (m : ENNReal) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set X : ℝ := Real.exp (-((n : ℝ) ^ dl / (2 * (dmax.factorial : ℝ))))
  let S : (i : Fin m) → Set (monos σ (d i : ℤ) → ℝ) := fun i =>
    {x | 2 * Real.sqrt ((monos σ (d i : ℤ)).card : ℝ) <
      ‖(WithLp.toLp 2 x : Hom σ (d i : ℤ))‖}
  have hU : {ω : ∀ i, monos σ (d i : ℤ) → ℝ | ¬ Ngood d ω} ⊆ ⋃ i, (fun ω => ω i) ⁻¹' S i := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Ngood, not_forall, not_le] at hω
    obtain ⟨i, hi⟩ := hω
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  have hterm : ∀ i, gaussOn σ m (fun i => (d i : ℤ)) ((fun ω => ω i) ⁻¹' S i) ≤
      ENNReal.ofReal X := by
    intro i
    have hmp := measurePreserving_eval (μ := fun i : Fin m =>
      Measure.pi fun _ : monos σ (d i : ℤ) => gaussianReal 0 1) i
    have hcard : ((monos σ (d i : ℤ)).card : ℝ) ≥ (n : ℝ) ^ d i / ((d i).factorial : ℝ) :=
      card_monos_ge (d i) (hd i).1
    have hN1 : 1 ≤ Fintype.card (monos σ (d i : ℤ)) := by
      rw [Fintype.card_coe]
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ d i := one_le_pow₀ hn1
      have hf : (1 : ℝ) ≤ ((d i).factorial : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
      have h2 : (0 : ℝ) < (n : ℝ) ^ d i / ((d i).factorial : ℝ) := by positivity
      have : (0 : ℝ) < ((monos σ (d i : ℤ)).card : ℝ) := lt_of_lt_of_le h2 hcard
      have : 0 < (monos σ (d i : ℤ)).card := by exact_mod_cast this
      omega
    have htail := gauss_norm_tail (ι := monos σ (d i : ℤ)) hN1
    rw [Fintype.card_coe] at htail
    calc gaussOn σ m (fun i => (d i : ℤ)) ((fun ω => ω i) ⁻¹' S i)
        ≤ (Measure.map (fun ω : ∀ i, monos σ (d i : ℤ) → ℝ => ω i)
            (gaussOn σ m (fun i => (d i : ℤ)))) (S i) :=
          Measure.le_map_apply hmp.measurable.aemeasurable _
      _ = (Measure.pi fun _ : monos σ (d i : ℤ) => gaussianReal 0 1) (S i) := by
          rw [show gaussOn σ m (fun i => (d i : ℤ)) = Measure.pi (fun i : Fin m =>
            Measure.pi fun _ : monos σ (d i : ℤ) => gaussianReal 0 1) from rfl]
          exact congrArg (fun μ => μ (S i)) hmp.map_eq
      _ ≤ ENNReal.ofReal (Real.exp (-((monos σ (d i : ℤ)).card : ℝ) / 2)) := htail
      _ ≤ ENNReal.ofReal X := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.2
          have hdl : dl ≤ d i := Finset.inf'_le _ (Finset.mem_univ i)
          have hp : (n : ℝ) ^ dl ≤ (n : ℝ) ^ d i := pow_le_pow_right₀ hn1 hdl
          have hf : ((d i).factorial : ℝ) ≤ (dmax.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le (hd i).2
          have hf0 : (0 : ℝ) < ((d i).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
          have h3 : (n : ℝ) ^ dl / (dmax.factorial : ℝ) ≤ (n : ℝ) ^ d i / ((d i).factorial : ℝ) :=
            div_le_div₀ (by positivity) hp hf0 hf
          have : (n : ℝ) ^ dl / (2 * (dmax.factorial : ℝ)) =
              (n : ℝ) ^ dl / (dmax.factorial : ℝ) / 2 := by ring
          rw [this, neg_div]
          linarith
  calc _ ≤ gaussOn σ m (fun i => (d i : ℤ)) (⋃ i, (fun ω => ω i) ⁻¹' S i) := measure_mono hU
    _ ≤ ∑ i, gaussOn σ m (fun i => (d i : ℤ)) ((fun ω => ω i) ⁻¹' S i) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin m, ENNReal.ofReal X := Finset.sum_le_sum fun i _ => hterm i
    _ = ENNReal.ofReal ((m : ℝ) * X) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

end ApproxSyzygies.Smoothed.Dev.G41.PartP
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias norm_event := ApproxSyzygies.Smoothed.Dev.G41.PartP.norm_event

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartP
open ApproxSyzygies.Smoothed
variable {σ σ' : Type} [Fintype σ] [DecidableEq σ] [Fintype σ'] [DecidableEq σ']
/-! # Theorem 4.1 Part P: stub P3 (renaming the variables transports the bad event) -/
lemma mem_monos_domCongr (e : σ ≃ σ') {d : ℤ} (α : σ' →₀ ℕ) (hα : α ∈ monos σ' d) :
    Finsupp.equivMapDomain e.symm α ∈ monos σ d := by
  rw [Dev.L43.mem_monos_iff, PartD.deg_domCongr]
  exact (Dev.L43.mem_monos_iff d α).1 hα

/-- Multi-indices of `σ'` pulled back to `σ`. -/
noncomputable def backE (e : σ ≃ σ') (d : ℤ) : monos σ' d ≃ monos σ d where
  toFun α := ⟨_, mem_monos_domCongr e α.1 α.2⟩
  invFun β := ⟨Finsupp.equivMapDomain e β.1, by
    have := mem_monos_domCongr e.symm β.1 β.2
    simpa using this⟩
  left_inv α := by
    apply Subtype.ext
    ext x
    simp
  right_inv β := by
    apply Subtype.ext
    ext x
    simp

omit [Fintype σ] [DecidableEq σ] [Fintype σ'] [DecidableEq σ'] in
lemma coeff_rename_equiv (e : σ ≃ σ') (f : MvPolynomial σ ℝ) (γ : σ' →₀ ℕ) :
    coeff γ (rename e f) = coeff (Finsupp.equivMapDomain e.symm γ) f := by
  have hγ : γ = Finsupp.mapDomain e (Finsupp.equivMapDomain e.symm γ) := by
    rw [← Finsupp.equivMapDomain_eq_mapDomain]
    ext x
    simp
  conv_lhs => rw [hγ]
  exact coeff_rename_mapDomain _ e.injective _ _

lemma renameHom_apply (e : σ ≃ σ') {d : ℤ} (p : Hom σ d) (α : monos σ' d) :
    renameHom e p α = p (backE e d α) := by
  simp only [renameHom, ofPoly, PiLp.toLp_apply]
  rw [coeff_rename_equiv, Dev.L43.coeff_toPoly', dif_pos (mem_monos_domCongr e α.1 α.2)]
  have hm : mfact (Finsupp.equivMapDomain e.symm α.1) = mfact α.1 := PartD.mfact_domCongr e α.1
  rw [hm]
  have h1 := Dev.A1.mfact_pos α.1
  have h2 : (0 : ℝ) < (d.toNat.factorial : ℝ) := by positivity
  rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
  rw [show (d.toNat.factorial : ℝ) / mfact α.1 * (mfact α.1 / (d.toNat.factorial : ℝ)) = 1 by
    field_simp]
  simp only [Real.sqrt_one, mul_one]
  rfl

lemma toPoly_renameHom (e : σ ≃ σ') {d : ℤ} (p : Hom σ d) :
    toPoly (renameHom e p) = rename e (toPoly p) := by
  unfold renameHom
  apply Dev.L43.toPoly_ofPoly
  intro γ hγ
  rw [coeff_rename_equiv] at hγ
  have := Dev.L43.IsH_toPoly p _ hγ
  rwa [PartD.deg_domCongr] at this

lemma renameHom_symm (e : σ ≃ σ') {d : ℤ} (p : Hom σ d) :
    renameHom e.symm (renameHom e p) = p := by
  apply Dev.L43.toPoly_inj
  rw [toPoly_renameHom, toPoly_renameHom, rename_rename]
  simp

lemma renameHom_sub (e : σ ≃ σ') {d : ℤ} (p q : Hom σ d) :
    renameHom e (p - q) = renameHom e p - renameHom e q := by
  apply Dev.L43.toPoly_inj
  rw [toPoly_renameHom, Dev.L43.toPoly_sub, Dev.L43.toPoly_sub, toPoly_renameHom,
    toPoly_renameHom, map_sub]

lemma perturbOn_rename (e : σ ≃ σ') {d : ℤ} (abar : Hom σ d) (ρ : ℝ) (ζ : monos σ d → ℝ) :
    perturbOn (renameHom e abar) ρ (ζ ∘ backE e d) = renameHom e (perturbOn abar ρ ζ) := by
  ext α
  simp only [perturbOn, PiLp.add_apply, PiLp.smul_apply, renameHom_apply,
    Function.comp_apply, smul_eq_mul]

lemma powHom_rename (e : σ ≃ σ') {d : ℤ} (a : Hom σ d) (D : ℕ) :
    powHom (renameHom e a) D = renameHom e (powHom a D) := by
  apply Dev.L43.toPoly_inj
  rw [toPoly_renameHom, Dev.L44.toPoly_powHom, Dev.L44.toPoly_powHom, toPoly_renameHom, map_pow]

/-- Renaming a tuple. -/
noncomputable def renTup (e : σ ≃ σ') {m : ℕ} {f : Fin m → ℤ} (h : Tup σ f) : Tup σ' f :=
  WithLp.toLp 2 fun i => renameHom e (h i)

lemma renTup_apply (e : σ ≃ σ') {m : ℕ} {f : Fin m → ℤ} (h : Tup σ f) (i : Fin m) :
    renTup e h i = renameHom e (h i) := rfl

lemma norm_renTup (e : σ ≃ σ') {m : ℕ} {f : Fin m → ℤ} (h : Tup σ f) :
    ‖renTup e h‖ = ‖h‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  simp only [renTup_apply, PartD.norm_renameHom]

lemma renTup_sub (e : σ ≃ σ') {m : ℕ} {f : Fin m → ℤ} (h k : Tup σ f) :
    renTup e (h - k) = renTup e h - renTup e k := by
  ext1 i
  simp only [renTup_apply, PiLp.sub_apply, renameHom_sub]

lemma renTup_symm (e : σ ≃ σ') {m : ℕ} {f : Fin m → ℤ} (h : Tup σ f) :
    renTup e.symm (renTup e h) = h := by
  ext1 i
  simp only [renTup_apply, renameHom_symm]

lemma mulMap_rename (e : σ ≃ σ') {m : ℕ} {f : Fin m → ℤ} (p : ∀ i, Hom σ (f i)) (t : ℤ)
    (h : Tup σ (fun i => t - f i)) :
    mulMap (fun i => renameHom e (p i)) t (renTup e h) = renameHom e (mulMap p t h) := by
  apply Dev.L43.toPoly_inj
  rw [Dev.L43.toPoly_mulMap, toPoly_renameHom, Dev.L43.toPoly_mulMap, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [renTup_apply, toPoly_renameHom, toPoly_renameHom, map_mul]

lemma koszul_rename (e : σ ≃ σ') {m : ℕ} {f : Fin m → ℤ} (p : ∀ i, Hom σ (f i)) (t : ℤ)
    (k : Tup σ (fun i => t - f i)) (hk : k ∈ koszul p t) :
    renTup e k ∈ koszul (fun i => renameHom e (p i)) t := by
  obtain ⟨Ω, hΩ, hanti, hkΩ⟩ := hk
  refine ⟨fun i j => rename e (Ω i j), fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · obtain ⟨w, hw⟩ := hΩ i j
    refine ⟨renameHom e w, ?_⟩
    show toPoly (renameHom e w) = _
    rw [toPoly_renameHom]
    exact congrArg (rename e) hw
  · show rename e (Ω i j) = -rename e (Ω j i)
    rw [hanti, map_neg]
  · rw [renTup_apply, toPoly_renameHom, hkΩ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, toPoly_renameHom]

lemma zero_mem_koszul {m : ℕ} {f : Fin m → ℤ} (p : ∀ i, Hom σ' (f i)) (t : ℤ) :
    (0 : Tup σ' (fun i => t - f i)) ∈ koszul p t := by
  refine ⟨fun _ _ => 0, fun i j => Submodule.zero_mem _, fun i j => by simp, fun i => ?_⟩
  simp only [PiLp.zero_apply, Dev.L43.toPoly_zero, zero_mul, Finset.sum_const_zero]

end ApproxSyzygies.Smoothed.Dev.G41.PartP
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartP
open ApproxSyzygies.Smoothed
theorem bad_transport {σ σ' : Type} [Fintype σ] [DecidableEq σ] [Fintype σ'] [DecidableEq σ']
    (e : σ ≃ σ') {m : ℕ} (d D : Fin m → ℕ) (abar : ∀ i, Hom σ (d i : ℤ)) (ρ K : ℝ) (t : ℕ) :
    gaussOn σ m (fun i => (d i : ℤ)) (BadT d D abar ρ K t) ≤
      gaussOn σ' m (fun i => (d i : ℤ)) (BadT d D (fun i => renameHom e (abar i)) ρ K t) := by
  set Ψ : (∀ i, monos σ (d i : ℤ) → ℝ) → (∀ i, monos σ' (d i : ℤ) → ℝ) :=
    fun ω i => (fun x => x ∘ (fun α => backE e (d i : ℤ) α)) (ω i) with hΨ
  have hmp : MeasurePreserving Ψ (gaussOn σ m (fun i => (d i : ℤ)))
      (gaussOn σ' m (fun i => (d i : ℤ))) :=
    measurePreserving_pi _ _ fun i =>
      measurePreserving_comp_inj _ (backE e (d i : ℤ)).injective _
  have hsub : BadT d D abar ρ K t ⊆ Ψ ⁻¹' BadT d D (fun i => renameHom e (abar i)) ρ K t := by
    intro ω hω
    obtain ⟨h, hlt⟩ := hω
    have hb : bfam d D (fun i => renameHom e (abar i)) ρ (Ψ ω) =
        fun i => renameHom e (bfam d D abar ρ ω i) := by
      funext i
      simp only [bfam, hΨ]
      rw [show (fun α => backE e (d i : ℤ) α) = ⇑(backE e (d i : ℤ)) from rfl,
        perturbOn_rename, powHom_rename]
    show ∃ h, _
    refine ⟨renTup e h, ?_⟩
    rw [hb, mulMap_rename, PartD.norm_renameHom]
    refine lt_of_lt_of_le hlt ?_
    rw [Metric.le_infDist ⟨0, zero_mem_koszul _ _⟩]
    intro y hy
    have hy' := koszul_rename e.symm _ _ y hy
    simp only [renameHom_symm] at hy'
    calc Metric.infDist h (koszul (bfam d D abar ρ ω) (t : ℤ))
        ≤ dist h (renTup e.symm y) := Metric.infDist_le_dist_of_mem hy'
      _ = dist (renTup e h) y := by
          rw [dist_eq_norm, dist_eq_norm, ← norm_renTup e.symm (renTup e h - y), renTup_sub,
            renTup_symm]
  calc _ ≤ gaussOn σ m (fun i => (d i : ℤ))
        (Ψ ⁻¹' BadT d D (fun i => renameHom e (abar i)) ρ K t) := measure_mono hsub
    _ ≤ (Measure.map Ψ (gaussOn σ m (fun i => (d i : ℤ))))
        (BadT d D (fun i => renameHom e (abar i)) ρ K t) :=
        Measure.le_map_apply hmp.measurable.aemeasurable _
    _ = _ := by rw [hmp.map_eq]

end ApproxSyzygies.Smoothed.Dev.G41.PartP
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias bad_transport := ApproxSyzygies.Smoothed.Dev.G41.PartP.bad_transport

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
namespace ApproxSyzygies.Smoothed.Dev.G41.PartP
open ApproxSyzygies.Smoothed
/-! # Theorem 4.1 Part P: arithmetic stubs A1–A5 (split sizes, slack, constants) -/
/-! ### A1 -/
theorem split_facts (n L : ℕ) (hL : 1 ≤ L) :
    (n : ℝ) / 2 ≤ (Ksplit n L : ℝ) ∧ Ksplit n L ≤ n ∧ Fintype.card (SplitVar n L) = n := by
  have hq : 2 * L * Qsplit n L ≤ n := by
    unfold Qsplit; rw [mul_comm]; exact Nat.div_mul_le_self n (2 * L)
  have hle : L * Qsplit n L ≤ n := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · unfold Ksplit
    rw [Nat.cast_sub hle]
    have : (2 * L * Qsplit n L : ℕ) ≤ (n : ℝ) := by exact_mod_cast hq
    push_cast at this ⊢
    linarith
  · unfold Ksplit; omega
  · show Fintype.card (Fin (Ksplit n L) ⊕ (Fin L × Fin (Qsplit n L))) = n
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_fin]
    unfold Ksplit; omega

end ApproxSyzygies.Smoothed.Dev.G41.PartP
end

section
set_option autoImplicit false
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
/-! # Blueprint for Theorem 4.1: arithmetic stubs (constants and thresholds) -/
alias split_facts := ApproxSyzygies.Smoothed.Dev.G41.PartP.split_facts

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
namespace ApproxSyzygies.Smoothed.Dev.G41.PartP
open ApproxSyzygies.Smoothed
/-! ### Nat-exponent normal form -/
lemma rpow_neg_natCast' (x : ℝ) (hx : 0 ≤ x) (e : ℕ) :
    x ^ (-((e : ℕ) : ℝ)) = (x ^ e)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_natCast]

/-! ### A3 -/
theorem m_le_of_sum (ε : ℝ) (hε : 0 < ε) (dmax Dmax n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (d D : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i ∧ d i ≤ dmax) (hD : ∀ i, 1 ≤ D i ∧ D i ≤ Dmax)
    (hsum : ∑ i, (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) ≤ (n : ℝ) ^ (-ε)) :
    (m : ℝ) ≤ (n : ℝ) ^ (dmax * Dmax) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hE : (0 : ℝ) < (n : ℝ) ^ (dmax * Dmax) := by positivity
  have hterm : ∀ i, ((n : ℝ) ^ (dmax * Dmax))⁻¹ ≤ (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) := by
    intro i
    rw [rpow_neg_natCast' _ hn0.le]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_right₀ hn1
    exact Nat.mul_le_mul (hd i).2 (hD i).2
  have h1 : (n : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hs : (m : ℝ) * ((n : ℝ) ^ (dmax * Dmax))⁻¹ ≤ 1 := by
    calc (m : ℝ) * ((n : ℝ) ^ (dmax * Dmax))⁻¹ = ∑ _i : Fin m, ((n : ℝ) ^ (dmax * Dmax))⁻¹ := by
          simp
      _ ≤ ∑ i, (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) := Finset.sum_le_sum fun i _ => hterm i
      _ ≤ 1 := hsum.trans h1
  rwa [← div_eq_mul_inv, div_le_one hE] at hs

/-! ### A2 -/
lemma term_le (n k e E : ℕ) (he : e ≤ E) (hk : (n : ℝ) / 2 ≤ k) (hn : 1 ≤ n) :
    (k : ℝ) ^ (-((e : ℕ) : ℝ)) ≤ 2 ^ E * (n : ℝ) ^ (-((e : ℕ) : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by linarith
  rw [rpow_neg_natCast' _ hk0.le, rpow_neg_natCast' _ hn0.le, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
  calc (n : ℝ) ^ e ≤ (2 * k) ^ e := pow_le_pow_left₀ hn0.le (by linarith) e
    _ = 2 ^ e * k ^ e := by ring
    _ ≤ 2 ^ E * k ^ e := by
        gcongr
        · norm_num
    _ = _ := by ring

theorem sum_cond_split (ε : ℝ) (hε : 0 < ε) (dmax Dmax : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (m : ℕ) (d D : Fin m → ℕ),
      (∀ i, 1 ≤ d i ∧ d i ≤ dmax) → (∀ i, 1 ≤ D i ∧ D i ≤ Dmax) →
      ∑ i, (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) ≤ (n : ℝ) ^ (-ε) →
      ∀ k : ℕ, (n : ℝ) / 2 ≤ k → k ≤ n →
        ∑ i, (k : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) ≤ (k : ℝ) ^ (-(min (ε / 2) (1 / 2))) ∧
        ∀ i₀, ∑ i, (k : ℝ) ^ (-((d i * Function.update D i₀ 1 i : ℕ) : ℝ)) ≤
          (k : ℝ) ^ (-(min (ε / 2) (1 / 2))) := by
  set E := dmax * Dmax
  refine ⟨max 16 ⌈((2 : ℝ) ^ (E + 1)) ^ (2 / ε)⌉₊, ?_⟩
  intro n hN m d D hd hD hsum k hk hkn
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hN
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hk1 : (1 : ℝ) ≤ k := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  set ε' := min (ε / 2) (1 / 2)
  -- the target is at least `n^{-ε/2}` and `n^{-1/2}`
  have hε' : 0 < ε' := lt_min (by linarith) (by norm_num)
  have hT : (n : ℝ) ^ (-ε') ≤ (k : ℝ) ^ (-ε') :=
    Real.rpow_le_rpow_of_nonpos hk0 hkn' (by linarith)
  have hT1 : (n : ℝ) ^ (-(ε / 2)) ≤ (n : ℝ) ^ (-ε') :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by simp only [ε']; linarith [min_le_left (ε / 2) (1 / 2)])
  have hT2 : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (n : ℝ) ^ (-ε') :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by simp only [ε']; linarith [min_le_right (ε / 2) (1 / 2)])
  -- `2^{E+1} ≤ n^{ε/2}`
  have hbig : (2 : ℝ) ^ (E + 1) ≤ (n : ℝ) ^ (ε / 2) := by
    have h1 : ((2 : ℝ) ^ (E + 1)) ^ (2 / ε) ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
    calc (2 : ℝ) ^ (E + 1) = (((2 : ℝ) ^ (E + 1)) ^ (2 / ε)) ^ (ε / 2) := by
          rw [← Real.rpow_mul (by positivity)]
          rw [show 2 / ε * (ε / 2) = 1 by field_simp, Real.rpow_one]
      _ ≤ (n : ℝ) ^ (ε / 2) := Real.rpow_le_rpow (by positivity) h1 (by linarith)
  -- the first sum
  have hS : ∑ i, (k : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) ≤ 2 ^ E * (n : ℝ) ^ (-ε) := by
    calc ∑ i, (k : ℝ) ^ (-((d i * D i : ℕ) : ℝ))
        ≤ ∑ i, 2 ^ E * (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) :=
          Finset.sum_le_sum fun i _ =>
            term_le n k _ E (Nat.mul_le_mul (hd i).2 (hD i).2) hk (by exact_mod_cast hn1)
      _ = 2 ^ E * ∑ i, (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ 2 ^ E * (n : ℝ) ^ (-ε) := by gcongr
  have hhalf : 2 ^ E * (n : ℝ) ^ (-ε) ≤ (n : ℝ) ^ (-(ε / 2)) / 2 := by
    have hsplit : (n : ℝ) ^ (-ε) = (n : ℝ) ^ (-(ε / 2)) * ((n : ℝ) ^ (ε / 2))⁻¹ := by
      rw [← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]; ring_nf
    rw [hsplit]
    have hp : 0 < (n : ℝ) ^ (ε / 2) := by positivity
    have hq : 0 < (n : ℝ) ^ (-(ε / 2)) := by positivity
    have h2 : (2 : ℝ) ^ E * ((n : ℝ) ^ (ε / 2))⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hp]
      have : (2 : ℝ) ^ (E + 1) = 2 ^ E * 2 := pow_succ _ _
      nlinarith
    calc (2 : ℝ) ^ E * ((n : ℝ) ^ (-(ε / 2)) * ((n : ℝ) ^ (ε / 2))⁻¹)
        = (n : ℝ) ^ (-(ε / 2)) * ((2 : ℝ) ^ E * ((n : ℝ) ^ (ε / 2))⁻¹) := by ring
      _ ≤ (n : ℝ) ^ (-(ε / 2)) * (1 / 2) := mul_le_mul_of_nonneg_left h2 hq.le
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · have hq : 0 < (n : ℝ) ^ (-(ε / 2)) := by positivity
    linarith
  · intro i₀
    -- the modified sum is at most the old sum plus `k^{-1}`
    have hmod : ∑ i, (k : ℝ) ^ (-((d i * Function.update D i₀ 1 i : ℕ) : ℝ)) ≤
        ∑ i, (k : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) + (k : ℝ)⁻¹ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      have hrest : ∑ i ∈ Finset.univ.erase i₀,
          (k : ℝ) ^ (-((d i * Function.update D i₀ 1 i : ℕ) : ℝ)) =
          ∑ i ∈ Finset.univ.erase i₀, (k : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [hrest, Function.update_self, rpow_neg_natCast' _ hk0.le]
      have h1 : ((k : ℝ) ^ (d i₀ * 1))⁻¹ ≤ (k : ℝ)⁻¹ := by
        apply inv_anti₀ hk0
        calc (k : ℝ) = k ^ 1 := (pow_one _).symm
          _ ≤ k ^ (d i₀ * 1) := pow_le_pow_right₀ hk1 (by simpa using (hd i₀).1)
      have h2 : 0 ≤ (k : ℝ) ^ (-((d i₀ * D i₀ : ℕ) : ℝ)) := by positivity
      linarith
    have hkinv : (k : ℝ)⁻¹ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) / 2 := by
      have hs : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt n)⁻¹ := by
        rw [Real.rpow_neg hn0.le, Real.sqrt_eq_rpow]
      rw [hs]
      have hsq : 4 ≤ Real.sqrt n := by
        rw [show (4 : ℝ) = Real.sqrt 16 by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hn16
      have hsq2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      rw [inv_le_iff_one_le_mul₀ hk0]
      have hpos : 0 < Real.sqrt n := by linarith
      have he : (Real.sqrt n)⁻¹ / 2 * k = k / (2 * Real.sqrt n) := by field_simp
      rw [he]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith

end ApproxSyzygies.Smoothed.Dev.G41.PartP
end

section
set_option autoImplicit false
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias sum_cond_split := ApproxSyzygies.Smoothed.Dev.G41.PartP.sum_cond_split

alias m_le_of_sum := ApproxSyzygies.Smoothed.Dev.G41.PartP.m_le_of_sum

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
namespace ApproxSyzygies.Smoothed.Dev.G41.PartP
open ApproxSyzygies.Smoothed
/-! ### A4 -/
theorem final_prob_arith (t dmax Dmax : ℕ) (cI c₂ : ℝ) (hcI : 0 < cI) (hc₂ : 0 < c₂) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k m dl : ℕ, (n : ℝ) / 2 ≤ k → 1 ≤ m →
      (m : ℝ) ≤ (n : ℝ) ^ (dmax * Dmax) → 1 ≤ dl → dl ≤ dmax →
      (t : ℝ) * ((m : ℝ) + 1) * Real.exp (-(cI * (k : ℝ) ^ dl)) +
        (m : ℝ) * Real.exp (-((n : ℝ) ^ dl / (2 * (dmax.factorial : ℝ)))) +
        Real.exp (-(c₂ * (n : ℝ) ^ dl)) ≤ Real.exp (-(c * (n : ℝ) ^ dl)) := by
  set E := dmax * Dmax
  set a : ℝ := min (min (cI / 2 ^ dmax) (1 / (2 * (dmax.factorial : ℝ)))) c₂ with ha_def
  have hfac : (0 : ℝ) < dmax.factorial := by exact_mod_cast Nat.factorial_pos dmax
  have ha : 0 < a := lt_min (lt_min (by positivity) (by positivity)) hc₂
  have ha1 : a ≤ cI / 2 ^ dmax := (min_le_left _ _).trans (min_le_left _ _)
  have ha2 : a ≤ 1 / (2 * (dmax.factorial : ℝ)) := (min_le_left _ _).trans (min_le_right _ _)
  have ha3 : a ≤ c₂ := min_le_right _ _
  set B : ℝ := 2 * ((t : ℝ) + 2) * ((E + 1).factorial : ℝ) / (a / 2) ^ (E + 1)
  refine ⟨a / 2, by positivity, max 1 ⌈B⌉₊, ?_⟩
  intro n hN k m dl hk hm hmE hdl hdlmax
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hN
  have hnB : B ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have hn0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) ≤ k := le_trans (by positivity) hk
  set x : ℝ := (n : ℝ) ^ dl with hx_def
  have hxn : (n : ℝ) ≤ x := by
    calc (n : ℝ) = n ^ 1 := (pow_one _).symm
      _ ≤ n ^ dl := pow_le_pow_right₀ hn1 hdl
  have hx0 : 0 ≤ x := by positivity
  -- the three exponents
  have e1 : a * x ≤ cI * (k : ℝ) ^ dl := by
    have hkx : x / 2 ^ dmax ≤ (k : ℝ) ^ dl := by
      calc x / 2 ^ dmax ≤ x / 2 ^ dl := by
            apply div_le_div_of_nonneg_left hx0 (by positivity)
            exact pow_le_pow_right₀ (by norm_num) hdlmax
        _ = ((n : ℝ) / 2) ^ dl := by rw [div_pow]
        _ ≤ (k : ℝ) ^ dl := pow_le_pow_left₀ (by positivity) hk dl
    calc a * x ≤ (cI / 2 ^ dmax) * x := mul_le_mul_of_nonneg_right ha1 hx0
      _ = cI * (x / 2 ^ dmax) := by ring
      _ ≤ cI * (k : ℝ) ^ dl := mul_le_mul_of_nonneg_left hkx hcI.le
  have e2 : a * x ≤ x / (2 * (dmax.factorial : ℝ)) := by
    rw [div_eq_mul_one_div, mul_comm x]
    exact mul_le_mul_of_nonneg_right ha2 hx0
  have e3 : a * x ≤ c₂ * x := mul_le_mul_of_nonneg_right ha3 hx0
  have E1 := Real.exp_le_exp.2 (neg_le_neg e1)
  have E2 := Real.exp_le_exp.2 (neg_le_neg e2)
  have E3 := Real.exp_le_exp.2 (neg_le_neg e3)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hsum : (t : ℝ) * ((m : ℝ) + 1) * Real.exp (-(cI * (k : ℝ) ^ dl)) +
      (m : ℝ) * Real.exp (-(x / (2 * (dmax.factorial : ℝ)))) + Real.exp (-(c₂ * x)) ≤
      ((t + 1) * ((m : ℝ) + 1)) * Real.exp (-(a * x)) := by
    have := mul_le_mul_of_nonneg_left E1 (by positivity : (0 : ℝ) ≤ t * (m + 1))
    have := mul_le_mul_of_nonneg_left E2 hm0
    nlinarith
  -- polynomial versus exponential
  have hpoly : ((t : ℝ) + 1) * ((m : ℝ) + 1) ≤ Real.exp (a / 2 * x) := by
    have hnE : (1 : ℝ) ≤ (n : ℝ) ^ E := one_le_pow₀ hn1
    have h1 : ((t : ℝ) + 1) * ((m : ℝ) + 1) ≤ 2 * ((t : ℝ) + 2) * (n : ℝ) ^ E := by nlinarith
    have h2 : (a / 2 * n) ^ (E + 1) / ((E + 1).factorial : ℝ) ≤ Real.exp (a / 2 * x) :=
      (Real.pow_div_factorial_le_exp (x := a / 2 * n) (by positivity) _).trans
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxn (by positivity)))
    have h3 : 2 * ((t : ℝ) + 2) * (n : ℝ) ^ E ≤ (a / 2 * n) ^ (E + 1) / ((E + 1).factorial : ℝ) := by
      have hf : (0 : ℝ) < ((E + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hp : (0 : ℝ) < (a / 2) ^ (E + 1) := by positivity
      rw [le_div_iff₀ hf, mul_pow, pow_succ (n : ℝ)]
      have hB' : 2 * ((t : ℝ) + 2) * ((E + 1).factorial : ℝ) ≤ (a / 2) ^ (E + 1) * n := by
        have := hnB
        simp only [B] at this
        rw [div_le_iff₀ hp] at this; linarith
      have hnE0 : (0 : ℝ) ≤ (n : ℝ) ^ E := by positivity
      nlinarith
    linarith
  calc _ ≤ ((t + 1) * ((m : ℝ) + 1)) * Real.exp (-(a * x)) := hsum
    _ ≤ Real.exp (a / 2 * x) * Real.exp (-(a * x)) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = Real.exp (-(a / 2 * x)) := by rw [← Real.exp_add]; ring_nf

end ApproxSyzygies.Smoothed.Dev.G41.PartP
end

section
set_option autoImplicit false
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias final_prob_arith := ApproxSyzygies.Smoothed.Dev.G41.PartP.final_prob_arith

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
namespace ApproxSyzygies.Smoothed.Dev.G41.PartP
open ApproxSyzygies.Smoothed
/-! ### A5 -/
lemma rpow_eq_div (n ρ C : ℝ) (hn : 0 ≤ n) (hρ : 0 < ρ) : n ^ C * ρ ^ (-C) = (n / ρ) ^ C := by
  rw [Real.rpow_neg hρ.le, Real.div_rpow hn hρ.le, div_eq_mul_inv]

theorem final_C_arith (t dmax Dmax : ℕ) (CI C₂ : ℝ) (hCI : 0 ≤ CI) (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ m : ℕ,
      (m : ℝ) ≤ (n : ℝ) ^ (dmax * Dmax) →
      redConst t ((n : ℝ) ^ CI * ρ ^ (-CI))
          ((m : ℝ) * (1 + 2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax)) ^ Dmax) *
        (1 + (n : ℝ) ^ C₂ * ρ ^ (-C₂)) ≤ (n : ℝ) ^ C * ρ ^ (-C) := by
  set E := dmax * Dmax
  set j := ⌈CI⌉₊
  set l := ⌈C₂⌉₊
  set M := j + 2 * E + l + 1
  set c1 : ℝ := (3 * 2 ^ dmax) ^ Dmax
  set K0 : ℝ := ((t : ℝ) + 1) * (1 + 2 ^ (t * t) * 2 ^ t * (1 + c1) ^ t) * (3 + c1) * 2
  refine ⟨((M * (2 * t + 4) + 1 : ℕ) : ℝ), by positivity, max 1 ⌈K0⌉₊, ?_⟩
  intro n hN ρ hρ hρ1 m hmE
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hN
  have hnK : K0 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have hn0 : (0 : ℝ) < n := by linarith
  set X : ℝ := (n : ℝ) / ρ with hX
  have hnX : (n : ℝ) ≤ X := by
    rw [hX, le_div_iff₀ hρ]; nlinarith
  have hX1 : 1 ≤ X := hn1.trans hnX
  set Y : ℝ := X ^ M with hY
  have hY1 : 1 ≤ Y := one_le_pow₀ hX1
  have hXY : ∀ p : ℕ, p ≤ M → X ^ p ≤ Y := fun p hp => pow_le_pow_right₀ hX1 hp
  rw [rpow_eq_div _ _ _ hn0.le hρ, rpow_eq_div _ _ _ hn0.le hρ, rpow_eq_div _ _ _ hn0.le hρ]
  rw [← hX]
  -- the basic bounds
  have hτ : X ^ CI ≤ Y := by
    calc X ^ CI ≤ X ^ (j : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (Nat.le_ceil _)
      _ = X ^ j := Real.rpow_natCast _ _
      _ ≤ Y := hXY j (by omega)
  have hC2 : X ^ C₂ ≤ Y := by
    calc X ^ C₂ ≤ X ^ (l : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (Nat.le_ceil _)
      _ = X ^ l := Real.rpow_natCast _ _
      _ ≤ Y := hXY l (by omega)
  have hτ0 : 0 ≤ X ^ CI := by positivity
  have hC20 : 0 ≤ X ^ C₂ := by positivity
  set Nb : ℝ := (m : ℝ) * (1 + 2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax)) ^ Dmax
  have hNb0 : 0 ≤ Nb := by positivity
  have hNb : Nb ≤ c1 * Y := by
    have hs : Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax) ≤ (2 * (n : ℝ)) ^ dmax := by
      have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ dmax := one_le_pow₀ (by push_cast; linarith)
      calc Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax) ≤ ((n + 1 : ℕ) : ℝ) ^ dmax := by
            rw [Real.sqrt_le_left (by positivity)]
            nlinarith
        _ ≤ (2 * (n : ℝ)) ^ dmax := pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _
    have h2 : 1 + 2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax) ≤ 3 * 2 ^ dmax * (n : ℝ) ^ dmax := by
      have : (1 : ℝ) ≤ (2 * (n : ℝ)) ^ dmax := one_le_pow₀ (by linarith)
      rw [mul_pow] at this hs
      nlinarith
    have h3 : (1 + 2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax)) ^ Dmax ≤ c1 * (n : ℝ) ^ E := by
      calc _ ≤ (3 * 2 ^ dmax * (n : ℝ) ^ dmax) ^ Dmax := pow_le_pow_left₀ (by positivity) h2 _
        _ = c1 * (n : ℝ) ^ E := by rw [mul_pow, ← pow_mul]
    have hnE : (n : ℝ) ^ E * (n : ℝ) ^ E ≤ Y := by
      rw [← pow_add]
      exact (pow_le_pow_left₀ hn0.le hnX _).trans (hXY _ (by omega))
    have hc10 : 0 ≤ c1 := by positivity
    calc Nb ≤ (n : ℝ) ^ E * (c1 * (n : ℝ) ^ E) := by
          apply mul_le_mul hmE h3 (by positivity) (by positivity)
      _ = c1 * ((n : ℝ) ^ E * (n : ℝ) ^ E) := by ring
      _ ≤ c1 * Y := mul_le_mul_of_nonneg_left hnE hc10
  have hc10 : 0 ≤ c1 := by positivity
  -- assemble
  have hR : redConst t (X ^ CI) Nb ≤ ((t : ℝ) + 1) *
      (1 + 2 ^ (t * t) * (1 + Y) ^ t * (1 + c1 * Y) ^ t) * (2 + Y + Y * (c1 * Y)) := by
    unfold redConst
    gcongr
  have hY0 : 0 ≤ Y := by linarith
  have hb1 : (1 + Y) ^ t ≤ 2 ^ t * Y ^ t := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hb2 : (1 + c1 * Y) ^ t ≤ (1 + c1) ^ t * Y ^ t := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have hYt : 1 ≤ Y ^ t := one_le_pow₀ hY1
  have hb3 : 1 + 2 ^ (t * t) * (1 + Y) ^ t * (1 + c1 * Y) ^ t ≤
      (1 + 2 ^ (t * t) * 2 ^ t * (1 + c1) ^ t) * Y ^ (2 * t) := by
    have hp : (0 : ℝ) ≤ 2 ^ (t * t) := by positivity
    have h12 : (1 + Y) ^ t * (1 + c1 * Y) ^ t ≤ 2 ^ t * (1 + c1) ^ t * Y ^ (2 * t) := by
      calc (1 + Y) ^ t * (1 + c1 * Y) ^ t ≤ (2 ^ t * Y ^ t) * ((1 + c1) ^ t * Y ^ t) :=
            mul_le_mul hb1 hb2 (by positivity) (by positivity)
        _ = 2 ^ t * (1 + c1) ^ t * Y ^ (2 * t) := by rw [two_mul, pow_add]; ring
    have hY2 : 1 ≤ Y ^ (2 * t) := one_le_pow₀ hY1
    calc 1 + 2 ^ (t * t) * (1 + Y) ^ t * (1 + c1 * Y) ^ t
        = 1 + 2 ^ (t * t) * ((1 + Y) ^ t * (1 + c1 * Y) ^ t) := by ring
      _ ≤ Y ^ (2 * t) + 2 ^ (t * t) * (2 ^ t * (1 + c1) ^ t * Y ^ (2 * t)) := by
          gcongr
      _ = _ := by ring
  have hb4 : 2 + Y + Y * (c1 * Y) ≤ (3 + c1) * Y ^ 2 := by nlinarith
  have hb5 : 1 + X ^ C₂ ≤ 2 * Y := by linarith
  have hK : K0 ≤ Y := hnK.trans (hnX.trans (by simpa using hXY 1 (by
    simp only [M]; omega)))
  calc redConst t (X ^ CI) Nb * (1 + X ^ C₂)
      ≤ (((t : ℝ) + 1) * (1 + 2 ^ (t * t) * (1 + Y) ^ t * (1 + c1 * Y) ^ t) *
          (2 + Y + Y * (c1 * Y))) * (2 * Y) :=
        mul_le_mul hR hb5 (by positivity) (by positivity)
    _ ≤ (((t : ℝ) + 1) * ((1 + 2 ^ (t * t) * 2 ^ t * (1 + c1) ^ t) * Y ^ (2 * t)) *
          ((3 + c1) * Y ^ 2)) * (2 * Y) := by gcongr
    _ = K0 * Y ^ (2 * t + 3) := by simp only [K0]; ring
    _ ≤ Y * Y ^ (2 * t + 3) := by gcongr
    _ = X ^ (M * (2 * t + 3 + 1)) := by rw [hY, ← pow_succ', ← pow_mul]
    _ ≤ X ^ (M * (2 * t + 4) + 1) := pow_le_pow_right₀ hX1 (by
        rw [show 2 * t + 3 + 1 = 2 * t + 4 by ring]; omega)
    _ = X ^ (((M * (2 * t + 4) + 1 : ℕ)) : ℝ) := (Real.rpow_natCast _ _).symm

end ApproxSyzygies.Smoothed.Dev.G41.PartP
end

section
set_option autoImplicit false
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias final_C_arith := ApproxSyzygies.Smoothed.Dev.G41.PartP.final_C_arith

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace ApproxSyzygies.Smoothed.Dev.G41.PartAC
open ApproxSyzygies.Smoothed
theorem powHom_anticonc (d D : ℕ) (hd : 1 ≤ d) (hD : 1 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ ∃ c' : ℝ, 0 < c' ∧ ∃ N₁ : ℕ,
      ∀ (Z : Type) [Fintype Z] [DecidableEq Z], N₁ ≤ Fintype.card Z → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        SubspaceAnticonc (1 / 4) (c' * ρ ^ D / (Fintype.card Z : ℝ) ^ ((d * D : ℕ) : ℝ))
          (c * (Fintype.card Z : ℝ) ^ d)
          ((Measure.pi fun _ : monos Z (d : ℤ) => gaussianReal 0 1).map
            fun g => powHom (ρ • (WithLp.toLp 2 g : Hom Z (d : ℤ))) D) :=
  ApproxSyzygies.Smoothed.Dev.G41.AC.powHom_anticonc d D hd hD

end ApproxSyzygies.Smoothed.Dev.G41.PartAC
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
/-! Assumed stub (being proved separately): subspace anticoncentration of the polynomial power
`v^D ∈ ℝ[z]_{=dD}` of a Gaussian `v = ρ g ∈ ℝ[z]_{=d}` in Bombieri coordinates. -/
alias powHom_anticonc := ApproxSyzygies.Smoothed.Dev.G41.PartAC.powHom_anticonc

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Module
namespace ApproxSyzygies.Smoothed.Dev.G41.PartF
open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.P48
variable {m L : ℕ} {ι : Fin L → Fin m → Type} [∀ ℓ i, Fintype (ι ℓ i)]
  {κ : Fin m → Type} [∀ i, Fintype (κ i)]
/-! # Theorem 4.1 Part F: stub F1 (`prop48_blocks`), the Fubini step and the assembly -/
/-- The data of all blocks, for underlying variables `u`. -/
noncomputable def thetaB {d : ℕ} (bW : Fin d → Wsp κ) {U : Fin L → Fin m → Type}
    (φ : ∀ ℓ i, U ℓ i → EuclideanSpace ℝ (ι ℓ i))
    (C : ∀ ℓ i, (∀ j, U ℓ j) → (Wsp κ →L[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i)))
    (u : ∀ ℓ i, U ℓ i) : ∀ ℓ, Dat ι κ d ℓ :=
  fun ℓ => (fun i => φ ℓ i (u ℓ i), fun i k => C ℓ i (u ℓ) (bW k))

lemma measurable_thetaB {d : ℕ} (bW : Fin d → Wsp κ) {U : Fin L → Fin m → Type}
    [∀ ℓ i, MeasurableSpace (U ℓ i)]
    (φ : ∀ ℓ i, U ℓ i → EuclideanSpace ℝ (ι ℓ i)) (hφ : ∀ ℓ i, Measurable (φ ℓ i))
    (C : ∀ ℓ i, (∀ j, U ℓ j) → (Wsp κ →L[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i)))
    (hCmeas : ∀ ℓ i (g : Wsp κ), Measurable fun x => C ℓ i x g) :
    Measurable (thetaB bW φ C) := by
  refine measurable_pi_lambda _ fun ℓ => Measurable.prodMk ?_ ?_
  · exact measurable_pi_lambda _ fun i =>
      (hφ ℓ i).comp ((measurable_pi_apply i).comp (measurable_pi_apply ℓ))
  · exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun k =>
      (hCmeas ℓ i (bW k)).comp (measurable_pi_apply ℓ)

end ApproxSyzygies.Smoothed.Dev.G41.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartF
open ApproxSyzygies.Smoothed
/-! # Theorem 4.1 Part F: stubs F2 (measurable choice) and F7 (counting monomials) -/
/-- **Stub F2 (measurable choice with slack).** -/
theorem exists_measurable_select {X E : Type*} [MeasurableSpace X] [PseudoMetricSpace E]
    [TopologicalSpace.SeparableSpace E] [Nonempty E] (S : X → Set E) (δ : ℝ) (hδ : 0 < δ)
    (hmeas : ∀ c : E, MeasurableSet {x | c ∈ S x}) (A : Set X)
    (hball : ∀ x ∈ A, ∃ c₀ : E, Metric.ball c₀ δ ⊆ S x) :
    ∃ (c : ℕ → E) (k : X → ℕ), Measurable k ∧ (∀ x x', S x = S x' → k x = k x') ∧
      ∀ x ∈ A, c (k x) ∈ S x := by
  classical
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq E
  let F : Set E → ℕ := fun T => if h : ∃ j, c j ∈ T then Nat.find h else 0
  refine ⟨c, fun x => F (S x), ?_, fun x x' h => by simp only [h], ?_⟩
  · apply measurable_to_countable'
    intro j
    have hE : (fun x => F (S x)) ⁻¹' {j} =
        ({x | c j ∈ S x} ∩ ⋂ i ∈ Finset.range j, {x | c i ∈ S x}ᶜ) ∪
          (if j = 0 then ⋂ i : ℕ, {x | c i ∈ S x}ᶜ else ∅) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, F, Set.mem_union, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]
      by_cases h : ∃ j, c j ∈ S x
      · rw [dif_pos h, Nat.find_eq_iff]
        constructor
        · rintro ⟨h1, h2⟩; exact Or.inl ⟨h1, fun i hi => h2 i hi⟩
        · rintro (⟨h1, h2⟩ | h3)
          · exact ⟨h1, fun i hi => h2 i hi⟩
          · split_ifs at h3 with hj
            · obtain ⟨i, hi⟩ := h; exact absurd hi (Set.mem_iInter.1 h3 i)
            · exact absurd h3 id
      · rw [dif_neg h]
        push Not at h
        constructor
        · rintro rfl; right; simp only [if_true, Set.mem_iInter, Set.mem_compl_iff,
            Set.mem_ofPred_eq]; exact h
        · rintro (⟨h1, _⟩ | h3)
          · exact absurd h1 (h j)
          · split_ifs at h3 with hj
            · exact hj.symm
            · exact absurd h3 id
    rw [hE]
    refine MeasurableSet.union ((hmeas _).inter (MeasurableSet.biInter (Set.to_countable _)
      fun i _ => (hmeas _).compl)) ?_
    split_ifs
    · exact MeasurableSet.iInter fun i => (hmeas _).compl
    · exact MeasurableSet.empty
  · intro x hx
    obtain ⟨c₀, hc₀⟩ := hball x hx
    obtain ⟨j, hj⟩ := hc.exists_mem_open Metric.isOpen_ball ⟨c₀, Metric.mem_ball_self hδ⟩
    have h : ∃ j, c j ∈ S x := ⟨j, hc₀ hj⟩
    show c (F (S x)) ∈ S x
    simp only [F, dif_pos h]
    exact Nat.find_spec h

end ApproxSyzygies.Smoothed.Dev.G41.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias exists_measurable_select := ApproxSyzygies.Smoothed.Dev.G41.PartF.exists_measurable_select

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartS
open ApproxSyzygies.Smoothed
variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
/-! # Part S: `lemma44_tensor` (stub F3), Lemma 4.4 in tensor coordinates -/
omit [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] in
lemma sumElim_eq_join (β : Y →₀ ℕ) (α : Z →₀ ℕ) :
    Finsupp.sumElim β α = Dev.L43.join β α := rfl

lemma join_mem_monos {R t : ℤ} (α : monos Z R) (β : monos Y (t - R)) :
    Dev.L43.join (β : Y →₀ ℕ) (α : Z →₀ ℕ) ∈ monos (Y ⊕ Z) t := by
  have hα := (Dev.L43.mem_monos_iff R (α : Z →₀ ℕ)).1 α.2
  have hβ := (Dev.L43.mem_monos_iff (t - R) (β : Y →₀ ℕ)).1 β.2
  rw [Dev.L43.mem_monos_iff, Dev.L43.deg_join]
  push_cast
  omega

/-- `‖toTens R t p‖ ≤ √binom(t, R) ‖p‖`. -/
lemma norm_toTens_le (R t : ℤ) (p : Hom (Y ⊕ Z) t) :
    ‖toTens R t p‖ ≤ Real.sqrt ((t.toNat.choose R.toNat : ℕ) : ℝ) * ‖p‖ := by
  classical
  set b : ℝ := ((t.toNat.choose R.toNat : ℕ) : ℝ) with hb
  have hb0 : 0 ≤ b := Nat.cast_nonneg _
  rw [← Real.sqrt_sq (norm_nonneg p), ← Real.sqrt_mul hb0,
    ← Real.sqrt_sq (norm_nonneg (toTens R t p))]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  set G : ((Y ⊕ Z) →₀ ℕ) → ℝ := fun γ => if h : γ ∈ monos (Y ⊕ Z) t then (p ⟨γ, h⟩) ^ 2 else 0
    with hG
  have hL : ∀ ab : monos Z R × monos Y (t - R),
      ‖(toTens R t p) ab‖ ^ 2 = b * G (Dev.L43.join (ab.2 : Y →₀ ℕ) (ab.1 : Z →₀ ℕ)) := by
    intro ab
    simp only [toTens, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, Real.norm_eq_abs,
      sq_abs, hG]
    rw [dif_pos (show Finsupp.sumElim (ab.2 : Y →₀ ℕ) (ab.1 : Z →₀ ℕ) ∈ monos (Y ⊕ Z) t from
      join_mem_monos ab.1 ab.2), dif_pos (join_mem_monos ab.1 ab.2), mul_pow,
      Real.sq_sqrt hb0]
    rfl
  simp_rw [hL]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hb0
  have hinj : Function.Injective fun ab : monos Z R × monos Y (t - R) =>
      Dev.L43.join (ab.2 : Y →₀ ℕ) (ab.1 : Z →₀ ℕ) := by
    intro ab ab' h
    have h1 := congrArg Dev.L43.yp h
    have h2 := congrArg Dev.L43.zp h
    simp only [Dev.L43.yp_join, Dev.L43.zp_join] at h1 h2
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h1)
  have hm : ∑ ab : monos Z R × monos Y (t - R), G (Dev.L43.join (ab.2 : Y →₀ ℕ) (ab.1 : Z →₀ ℕ))
      = ∑ γ ∈ Finset.univ.map ⟨_, hinj⟩, G γ := by
    rw [Finset.sum_map]; rfl
  rw [hm]
  have hR : ∑ x : monos (Y ⊕ Z) t, ‖p x‖ ^ 2 = ∑ γ ∈ monos (Y ⊕ Z) t, G γ := by
    rw [← Finset.sum_coe_sort (monos (Y ⊕ Z) t)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hG, dif_pos x.2, Real.norm_eq_abs, sq_abs]
  rw [hR]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun γ _ _ => ?_
  · intro γ hγ
    obtain ⟨ab, -, rfl⟩ := Finset.mem_map.1 hγ
    exact join_mem_monos ab.1 ab.2
  · simp only [hG]; split_ifs; positivity

/-- `toTens` of a product of a pure-`z` and a pure-`y` polynomial is the tensor product. -/
lemma toTens_tens (R t : ℤ) (hR : 0 ≤ R) (ζ : Hom Z R) (g : Hom Y (t - R)) :
    toTens R t (ofPoly t (rename Sum.inr (toPoly ζ) * rename Sum.inl (toPoly g))) = tens ζ g := by
  classical
  ext ab
  obtain ⟨α, β⟩ := ab
  have hα := (Dev.L43.mem_monos_iff R (α : Z →₀ ℕ)).1 α.2
  have hβ := (Dev.L43.mem_monos_iff (t - R) (β : Y →₀ ℕ)).1 β.2
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hR
  obtain ⟨s, hs⟩ : ∃ s : ℕ, t - (r : ℤ) = s := ⟨Dev.L43.deg (β : Y →₀ ℕ), hβ.symm⟩
  obtain rfl : t = (r : ℤ) + s := by omega
  simp only [toTens, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, tens]
  rw [dif_pos (show Finsupp.sumElim (β : Y →₀ ℕ) (α : Z →₀ ℕ) ∈ monos (Y ⊕ Z) _ from
    join_mem_monos α β)]
  simp only [ofPoly, PiLp.toLp_apply, sumElim_eq_join]
  rw [← Dev.L43.coeff_E_join, mul_comm (rename Sum.inr _), Dev.L43.E_rename_inl_mul,
    Dev.L44.E_rename_inr, mul_comm _ (C _), coeff_C_mul, Dev.L43.coeff_toPoly', Dev.L43.coeff_toPoly',
    dif_pos α.2, dif_pos β.2, Dev.L43.mfact_join]
  have e1 : ((r : ℤ) + (s : ℤ)).toNat = r + s := by omega
  have e2 : ((r : ℤ) + (s : ℤ) - (r : ℤ)).toNat = s := by omega
  have e3 : (r : ℤ).toNat = r := by omega
  rw [e1, e2, e3]
  have ha := Dev.A1.mfact_pos (α : Z →₀ ℕ)
  have hb := Dev.A1.mfact_pos (β : Y →₀ ℕ)
  have hch : ((r + s).choose r : ℝ) * (r.factorial : ℝ) * (s.factorial : ℝ) =
      ((r + s).factorial : ℝ) := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right r s)
    rw [Nat.add_sub_cancel_left] at this
    exact_mod_cast this
  have hfac : (0 : ℝ) < ((r + s).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have key : Real.sqrt (((r + s).choose r : ℕ) : ℝ) *
      Real.sqrt ((s.factorial : ℝ) / mfact (β : Y →₀ ℕ)) *
      Real.sqrt ((r.factorial : ℝ) / mfact (α : Z →₀ ℕ)) *
      Real.sqrt (mfact (β : Y →₀ ℕ) * mfact (α : Z →₀ ℕ) / ((r + s).factorial : ℝ)) = 1 := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
      ← Real.sqrt_mul (by positivity), Real.sqrt_eq_one]
    field_simp
    linear_combination hch
  linear_combination (ζ α * g β) * key

/-- A two-variable polynomial is bounded by `A (1 + X)^k (1 + Y)^k` on `[0, X] × [0, Y]`. -/
lemma eval_two_le (π : MvPolynomial (Fin 2) ℝ) (x y X Y : ℝ) (hx : 0 ≤ x) (hxX : x ≤ X)
    (hy : 0 ≤ y) (hyY : y ≤ Y) :
    eval ![x, y] π ≤ (∑ s ∈ π.support, |coeff s π|) * (1 + X) ^ π.totalDegree *
      (1 + Y) ^ π.totalDegree := by
  rw [eval_eq', Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun s hs => ?_
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hdeg : s 0 + s 1 ≤ π.totalDegree := by
    have := le_totalDegree hs
    rwa [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at this
  have h1 : x ^ s 0 ≤ (1 + X) ^ π.totalDegree :=
    (pow_le_pow_left₀ hx (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
  have h2 : y ^ s 1 ≤ (1 + Y) ^ π.totalDegree :=
    (pow_le_pow_left₀ hy (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
  calc coeff s π * (x ^ s 0 * y ^ s 1) ≤ |coeff s π| * (x ^ s 0 * y ^ s 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |coeff s π| * ((1 + X) ^ π.totalDegree * (1 + Y) ^ π.totalDegree) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (pow_nonneg (by linarith) _))
          (abs_nonneg _)
    _ = _ := by ring

end ApproxSyzygies.Smoothed.Dev.G41.PartS
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartS
open ApproxSyzygies.Smoothed
lemma tauOf_nonneg'' {Y : Type} [Fintype Y] [DecidableEq Y] {m : ℕ} {e : Fin m → ℤ}
    (p : ∀ i, Hom Y (e i)) (t : ℕ) : 0 ≤ tauOf p t :=
  Real.iSup_nonneg fun _ => Real.sInf_nonneg fun _ hx => hx.1

/-- **Stub F3 (Lemma 4.4 in tensor coordinates).** -/
theorem lemma44_tensor (T : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ k : ℕ,
      ∀ {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {m : ℕ}
        (d D : Fin m → ℕ), (∀ j, 1 ≤ d j) → (∀ j, 1 ≤ D j) →
        ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ i : Fin m,
        ∃ CC : (∀ j, Hom (Y ⊕ Z) (modDeg d D i j)) →
            (Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)) →L[ℝ]
              EuclideanSpace ℝ (monos Z ((d i : ℤ) * (D i : ℤ)) ×
                monos Y ((t : ℤ) - (d i : ℤ) * (D i : ℤ)))),
        ∀ (c : Hom (Y ⊕ Z) (d i : ℤ)) (a : ∀ j, Hom (Y ⊕ Z) (d j : ℤ)) (v : Hom Z (d i : ℤ)),
          a i = c + liftZ v → ∀ τ₀ N : ℝ, 0 ≤ τ₀ → 0 ≤ N →
          KernelCond (yParts fun j => powHom (a j) (D j)) t →
          tauOf (yParts fun j => powHom (a j) (D j)) t ≤ τ₀ →
          KernelCond (yParts (modGen d D i (toPoly c) a)) t →
          tauOf (yParts (modGen d D i (toPoly c) a)) t ≤ τ₀ →
          tupNorm (modGen d D i (toPoly c) a) ≤ N →
          ‖CC (modGen d D i (toPoly c) a)‖ ≤ A * (1 + τ₀) ^ k * (1 + N) ^ k ∧
          ∀ h : Tup (Y ⊕ Z) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)),
            ‖tens (powHom v (D i)) (gVec d D t (yParts a) (yPartTup h) i) +
                CC (modGen d D i (toPoly c) a) (gVec d D t (yParts a) (yPartTup h))‖ ≤
              A * (1 + τ₀) ^ k * (1 + N) ^ k *
                ‖mulMap (fun j => powHom (a j) (D j)) (t : ℤ) h‖ := by
  obtain ⟨π, hπ⟩ := lemma_4_4 T
  set S := ∑ s ∈ π.support, |coeff s π| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨Real.sqrt (2 ^ T) * S, by positivity, π.totalDegree, ?_⟩
  intro Y Z _ _ _ _ m d D hd hD t ht1 htT i
  obtain ⟨Cmap, hC⟩ := hπ (Y := Y) (Z := Z) d D hd hD t ht1 htT i
  set Tl : Hom (Y ⊕ Z) (t : ℤ) →L[ℝ] EuclideanSpace ℝ (monos Z ((d i : ℤ) * (D i : ℤ)) ×
      monos Y ((t : ℤ) - (d i : ℤ) * (D i : ℤ))) :=
    LinearMap.toContinuousLinearMap (toTens ((d i : ℤ) * (D i : ℤ)) (t : ℤ)) with hTl
  have hTlb : ∀ p, ‖Tl p‖ ≤ Real.sqrt (2 ^ T) * ‖p‖ := by
    intro p
    refine (norm_toTens_le _ _ p).trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_)
      (norm_nonneg _))
    have h1 := Nat.choose_le_two_pow ((t : ℤ).toNat) (((d i : ℤ) * (D i : ℤ)).toNat)
    have h2 : 2 ^ ((t : ℤ).toNat) ≤ 2 ^ T := Nat.pow_le_pow_right (by norm_num) (by simpa using htT)
    exact_mod_cast h1.trans h2
  have hTlop : ‖Tl‖ ≤ Real.sqrt (2 ^ T) :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) hTlb
  refine ⟨fun b => Tl.comp (Cmap b), ?_⟩
  intro c a v hav τ₀ N hτ₀ hN K1 T1 K2 T2 hNb
  have hb : toPoly (a i) - toPoly (liftZ (Y := Y) v) = toPoly c := by
    rw [hav, Dev.L43.toPoly_add]; ring
  have hCa := hC a v K1 (by rw [hb]; exact K2)
  rw [hb] at hCa
  obtain ⟨h1, h2⟩ := hCa
  have hE := eval_two_le π _ _ τ₀ N (le_max_of_le_left (tauOf_nonneg'' _ t)) (max_le T1 T2)
    (norm_nonneg _) hNb
  rw [← hS] at hE
  constructor
  · calc ‖Tl.comp (Cmap (modGen d D i (toPoly c) a))‖ ≤ ‖Tl‖ * ‖Cmap (modGen d D i (toPoly c) a)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Real.sqrt (2 ^ T) * (S * (1 + τ₀) ^ π.totalDegree * (1 + N) ^ π.totalDegree) :=
          mul_le_mul hTlop (h1.trans hE) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · intro h
    have hX : Tl (ofPoly (t : ℤ) (toPoly (liftZ (Y := Y) v) ^ D i *
        toPoly (liftY (Z := Z) (gVec d D t (yParts a) (yPartTup h) i)))) =
        tens (powHom v (D i)) (gVec d D t (yParts a) (yPartTup h) i) := by
      rw [hTl, LinearMap.coe_toContinuousLinearMap', Dev.L44.toPoly_liftZ, Dev.L43.toPoly_liftY,
        ← map_pow, ← Dev.L44.toPoly_powHom]
      exact toTens_tens _ _ (by positivity) _ _
    have hf0 := norm_nonneg (mulMap (fun j => powHom (a j) (D j)) (t : ℤ) h)
    calc _ = ‖Tl (ofPoly (t : ℤ) (toPoly (liftZ (Y := Y) v) ^ D i *
            toPoly (liftY (Z := Z) (gVec d D t (yParts a) (yPartTup h) i))) +
            Cmap (modGen d D i (toPoly c) a) (gVec d D t (yParts a) (yPartTup h)))‖ := by
          rw [map_add, hX]; rfl
      _ ≤ Real.sqrt (2 ^ T) * ‖ofPoly (t : ℤ) (toPoly (liftZ (Y := Y) v) ^ D i *
            toPoly (liftY (Z := Z) (gVec d D t (yParts a) (yPartTup h) i))) +
            Cmap (modGen d D i (toPoly c) a) (gVec d D t (yParts a) (yPartTup h))‖ := hTlb _
      _ ≤ Real.sqrt (2 ^ T) * ((S * (1 + τ₀) ^ π.totalDegree * (1 + N) ^ π.totalDegree) *
            ‖mulMap (fun j => powHom (a j) (D j)) (t : ℤ) h‖) :=
          mul_le_mul_of_nonneg_left ((h2 h).trans (mul_le_mul_of_nonneg_right hE hf0))
            (Real.sqrt_nonneg _)
      _ = _ := by ring

end ApproxSyzygies.Smoothed.Dev.G41.PartS
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartN
open ApproxSyzygies.Smoothed
variable {Y : Type} [Fintype Y] [DecidableEq Y] {L q : ℕ}
/-! # Theorem 4.1 Part N: stub F4 (`restr_facts`) and the block coordinates of `replaceV` -/
lemma ne_zero_of_mem_monos {σ : Type} [Fintype σ] [DecidableEq σ] {e : ℤ} (he : 1 ≤ e)
    {α : σ →₀ ℕ} (hα : α ∈ monos σ e) : α ≠ 0 := by
  rintro rfl
  rw [Dev.L43.mem_monos_iff] at hα
  simp [Dev.L43.deg] at hα
  omega

end ApproxSyzygies.Smoothed.Dev.G41.PartN
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartN
open ApproxSyzygies.Smoothed
variable {σ X : Type} [Fintype σ] [DecidableEq σ] [TopologicalSpace X]
/-! # Theorem 4.1 Part N: stub F5 (continuity of the multiplication map in the coefficients) -/
/-- Every coefficient depends continuously on the parameter. -/
def CoeffCont (F : X → MvPolynomial σ ℝ) : Prop := ∀ β, Continuous fun x => coeff β (F x)

lemma CoeffCont.const (f : MvPolynomial σ ℝ) : CoeffCont (fun _ : X => f) :=
  fun _ => continuous_const

lemma CoeffCont.mul {F G : X → MvPolynomial σ ℝ} (hF : CoeffCont F) (hG : CoeffCont G) :
    CoeffCont (fun x => F x * G x) := by
  intro β
  simp only [coeff_mul]
  exact continuous_finsetSum _ fun p _ => (hF p.1).mul (hG p.2)

lemma CoeffCont.pow {F : X → MvPolynomial σ ℝ} (hF : CoeffCont F) (n : ℕ) :
    CoeffCont (fun x => F x ^ n) := by
  induction n with
  | zero => simpa using CoeffCont.const (X := X) (1 : MvPolynomial σ ℝ)
  | succ n ih => simpa [pow_succ] using ih.mul hF

lemma CoeffCont.toPoly {d : ℤ} {P : X → Hom σ d} (hP : Continuous P) :
    CoeffCont (fun x => toPoly (P x)) := by
  intro β
  simp only [ApproxSyzygies.Smoothed.toPoly, coeff_sum, coeff_smul, smul_eq_mul]
  refine continuous_finsetSum _ fun α _ => Continuous.mul ?_ continuous_const
  exact (PiLp.continuous_apply 2 _ α).comp hP

lemma continuous_ofPoly {d : ℤ} {F : X → MvPolynomial σ ℝ} (hF : CoeffCont F) :
    Continuous fun x => (ofPoly d (F x) : Hom σ d) := by
  unfold ofPoly
  refine (PiLp.continuous_toLp 2 _).comp ?_
  exact continuous_pi fun α => (hF _).mul continuous_const

end ApproxSyzygies.Smoothed.Dev.G41.PartN
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartN
open ApproxSyzygies.Smoothed
theorem continuous_mulMap_pow {σ X : Type} [Fintype σ] [DecidableEq σ] [TopologicalSpace X]
    {m : ℕ} (d D : Fin m → ℕ) (a : X → ∀ i, Hom σ (d i : ℤ)) (ha : ∀ i, Continuous fun x => a x i)
    (s : ℤ) (h : Tup σ (fun i => s - (d i : ℤ) * (D i : ℤ))) :
    Continuous fun x => mulMap (fun i => powHom (a x i) (D i)) s h := by
  simp only [Dev.L42.mulMap_apply]
  refine continuous_finsetSum _ fun i _ => continuous_ofPoly ?_
  refine CoeffCont.mul ?_ (CoeffCont.const _)
  refine CoeffCont.toPoly (P := fun x => powHom (a x i) (D i)) ?_
  unfold powHom
  exact continuous_ofPoly ((CoeffCont.toPoly (ha i)).pow _)

end ApproxSyzygies.Smoothed.Dev.G41.PartN
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias continuous_mulMap_pow := ApproxSyzygies.Smoothed.Dev.G41.PartN.continuous_mulMap_pow

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace ApproxSyzygies.Smoothed.Dev.G41.PartN
open ApproxSyzygies.Smoothed
/-! # Theorem 4.1 Part N: stub F6 (uniform anticoncentration) -/
/-- Subspace anticoncentration is monotone: smaller `η₀` and smaller `γ`. -/
lemma subspaceAnticonc_mono {ι : Type*} [Fintype ι] {θ η₀ η₀' γ γ' : ℝ}
    {μ : Measure (EuclideanSpace ℝ ι)} (h : SubspaceAnticonc θ η₀ γ μ) (hη : 0 < η₀')
    (hηle : η₀' ≤ η₀) (hγ : 0 < γ') (hγle : γ' ≤ γ) : SubspaceAnticonc θ η₀' γ' μ := by
  obtain ⟨_, _, hE⟩ := h
  refine ⟨hγ, hη, fun E hE' => ?_⟩
  calc μ {x | ‖E.starProjection x‖ ≤ η₀'} ≤ μ {x | ‖E.starProjection x‖ ≤ η₀} :=
        measure_mono fun x hx => le_trans (show ‖E.starProjection x‖ ≤ η₀' from hx) hηle
    _ ≤ ENNReal.ofReal (Real.exp (-γ)) := hE E hE'
    _ ≤ ENNReal.ofReal (Real.exp (-γ')) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))

lemma powHom_anticonc_all (d D : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ c' : ℝ, 0 < c' ∧ ∃ N₁ : ℕ, (1 ≤ d → 1 ≤ D →
      ∀ (Z : Type) [Fintype Z] [DecidableEq Z], N₁ ≤ Fintype.card Z → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        SubspaceAnticonc (1 / 4) (c' * ρ ^ D / (Fintype.card Z : ℝ) ^ ((d * D : ℕ) : ℝ))
          (c * (Fintype.card Z : ℝ) ^ d)
          ((Measure.pi fun _ : monos Z (d : ℤ) => gaussianReal 0 1).map
            fun g => powHom (ρ • (WithLp.toLp 2 g : Hom Z (d : ℤ))) D)) := by
  by_cases h : 1 ≤ d ∧ 1 ≤ D
  · obtain ⟨c, hc, c', hc', N₁, hN⟩ := powHom_anticonc d D h.1 h.2
    exact ⟨c, hc, c', hc', N₁, fun _ _ => hN⟩
  · exact ⟨1, one_pos, 1, one_pos, 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩

theorem anticonc_uniform (dmax Dmax : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ c' : ℝ, 0 < c' ∧ ∃ N₁ : ℕ,
      ∀ d D : ℕ, 1 ≤ d → d ≤ dmax → 1 ≤ D → D ≤ Dmax → ∀ dl : ℕ, dl ≤ d →
      ∀ (Z : Type) [Fintype Z] [DecidableEq Z], N₁ ≤ Fintype.card Z →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        SubspaceAnticonc (1 / 4) (c' * ρ ^ Dmax / (Fintype.card Z : ℝ) ^ (dmax * Dmax))
          (c * (Fintype.card Z : ℝ) ^ dl)
          ((Measure.pi fun _ : monos Z (d : ℤ) => gaussianReal 0 1).map
            fun g => powHom (ρ • (WithLp.toLp 2 g : Hom Z (d : ℤ))) D) := by
  choose cf hcf cf' hcf' Nf hNf using powHom_anticonc_all
  set B : Finset (ℕ × ℕ) := Finset.range (dmax + 1) ×ˢ Finset.range (Dmax + 1) with hB
  have hBne : B.Nonempty := ⟨(0, 0), by simp [hB]⟩
  have hmem : ∀ d D, d ≤ dmax → D ≤ Dmax → (d, D) ∈ B := fun d D h1 h2 => by
    simp only [hB, Finset.mem_product, Finset.mem_range]; omega
  refine ⟨B.inf' hBne fun p => cf p.1 p.2, ?_, B.inf' hBne fun p => cf' p.1 p.2, ?_,
    B.sup (fun p => Nf p.1 p.2) + 1, ?_⟩
  · exact (Finset.lt_inf'_iff _).2 fun p _ => hcf _ _
  · exact (Finset.lt_inf'_iff _).2 fun p _ => hcf' _ _
  intro d D hd hdm hD hDm dl hdl Z _ _ hZ ρ hρ hρ1
  have hdD := hmem d D hdm hDm
  have hc_le : B.inf' hBne (fun p => cf p.1 p.2) ≤ cf d D := Finset.inf'_le (fun p => cf p.1 p.2) hdD
  have hc'_le : B.inf' hBne (fun p => cf' p.1 p.2) ≤ cf' d D :=
    Finset.inf'_le (fun p => cf' p.1 p.2) hdD
  have hc_pos : 0 < B.inf' hBne (fun p => cf p.1 p.2) := (Finset.lt_inf'_iff _).2 fun p _ => hcf _ _
  have hc'_pos : 0 < B.inf' hBne (fun p => cf' p.1 p.2) :=
    (Finset.lt_inf'_iff _).2 fun p _ => hcf' _ _
  have hN : Nf d D ≤ Fintype.card Z := by
    have := Finset.le_sup (f := fun p : ℕ × ℕ => Nf p.1 p.2) hdD
    simp only at this; omega
  have hZ1 : (1 : ℝ) ≤ (Fintype.card Z : ℝ) := by exact_mod_cast (show 1 ≤ Fintype.card Z by omega)
  have hZ0 : (0 : ℝ) < (Fintype.card Z : ℝ) := by linarith
  refine subspaceAnticonc_mono (hNf d D hd hD Z hN ρ hρ hρ1) (by positivity) ?_ (by positivity) ?_
  · rw [Real.rpow_natCast]
    have h1 : ρ ^ Dmax ≤ ρ ^ D := pow_le_pow_of_le_one hρ.le hρ1 hDm
    have h2 : (Fintype.card Z : ℝ) ^ (d * D) ≤ (Fintype.card Z : ℝ) ^ (dmax * Dmax) :=
      pow_le_pow_right₀ hZ1 (Nat.mul_le_mul hdm hDm)
    have h3 : 0 < (Fintype.card Z : ℝ) ^ (d * D) := by positivity
    rw [div_le_div_iff₀ (by positivity) h3]
    exact mul_le_mul (mul_le_mul hc'_le h1 (by positivity) (hcf' d D).le) h2 (by positivity)
      (by nlinarith [hcf' d D, pow_pos hρ D])
  · have h2 : (Fintype.card Z : ℝ) ^ dl ≤ (Fintype.card Z : ℝ) ^ d := pow_le_pow_right₀ hZ1 hdl
    gcongr
    exact (hcf d D).le

end ApproxSyzygies.Smoothed.Dev.G41.PartN
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias anticonc_uniform := ApproxSyzygies.Smoothed.Dev.G41.PartN.anticonc_uniform

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartF
open ApproxSyzygies.Smoothed
lemma card_monos_nat (σ : Type) [Fintype σ] [DecidableEq σ] (e : ℕ) :
    (monos σ (e : ℤ)).card = (Fintype.card σ + e - 1).choose e := by
  simp [monos, Finset.card_finsuppAntidiag_nat_eq_choose]

lemma choose_le_pow' (n : ℕ) (hn : 1 ≤ n) : ∀ e : ℕ, (n + e - 1).choose e ≤ n ^ e
  | 0 => by simp
  | e + 1 => by
    have ih := choose_le_pow' n hn e
    have h1 := Nat.add_one_mul_choose_eq (n + e - 1) e
    have h2 : n + e - 1 + 1 = n + (e + 1) - 1 := by omega
    rw [h2] at h1
    have h3 : (n + (e + 1) - 1).choose (e + 1) * (e + 1) ≤ n ^ (e + 1) * (e + 1) := by
      rw [← h1]
      calc (n + (e + 1) - 1) * (n + e - 1).choose e ≤ (n * (e + 1)) * n ^ e := by
            apply Nat.mul_le_mul _ ih
            have : n + (e + 1) - 1 = n + e := by omega
            rw [this]; nlinarith
        _ = n ^ (e + 1) * (e + 1) := by ring
    exact Nat.le_of_mul_le_mul_right h3 (by omega)

/-- **Stub F7 (counting monomials).** -/
theorem card_monos_bounds (σ : Type) [Fintype σ] [DecidableEq σ] (e : ℕ) (he : 1 ≤ e) :
    (Fintype.card σ : ℝ) ^ e / (e.factorial : ℝ) ≤ ((monos σ (e : ℤ)).card : ℝ) ∧
      (monos σ (e : ℤ)).card ≤ Fintype.card σ ^ e := by
  rw [card_monos_nat]
  set n := Fintype.card σ
  constructor
  · rw [div_le_iff₀ (by exact_mod_cast e.factorial_pos)]
    have h1 := Nat.ascFactorial_eq_factorial_mul_choose' n e
    have h2 := Nat.pow_succ_le_ascFactorial n e
    have h3 : n ^ e ≤ (n + e - 1).choose e * e.factorial := by
      rw [h1] at h2; linarith [Nat.mul_comm e.factorial ((n + e - 1).choose e)]
    exact_mod_cast h3
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, Nat.choose_eq_zero_of_lt (by omega)]; exact Nat.zero_le _
    · exact choose_le_pow' n hpos e

end ApproxSyzygies.Smoothed.Dev.G41.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias card_monos_bounds := ApproxSyzygies.Smoothed.Dev.G41.PartF.card_monos_bounds

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartF
open ApproxSyzygies.Smoothed
/-! # Theorem 4.1 Part F: stubs F8 (`hprod_bound`) and F9 (`shrink_arith`) -/
lemma one_le_Lsplit (ε : ℝ) (t : ℕ) : 1 ≤ Lsplit ε t := by
  unfold Lsplit; omega

lemma t_lt_Lsplit (ε : ℝ) (hε : 0 < ε) (t : ℕ) : (t : ℝ) < Lsplit ε t * ε := by
  unfold Lsplit
  have h := Nat.lt_floor_add_one ((t : ℝ) / ε)
  push_cast
  rw [div_lt_iff₀ hε] at h
  linarith

/-- `q = ⌊n/(2L)⌋ ≥ n/(4L)` once `n ≥ 4L`. -/
lemma qsplit_ge (n L : ℕ) (hL : 1 ≤ L) (hn : 4 * L ≤ n) :
    (n : ℝ) / (4 * L) ≤ (Qsplit n L : ℝ) := by
  unfold Qsplit
  have h := Nat.lt_mul_div_succ n (show 0 < 2 * L by omega)
  have h' : (n : ℝ) < 2 * L * ((n / (2 * L) : ℕ) + 1) := by exact_mod_cast h
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hn' : (4 * L : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma qsplit_pos (n L : ℕ) (hL : 1 ≤ L) (hn : 4 * L ≤ n) : 1 ≤ Qsplit n L := by
  unfold Qsplit
  rw [Nat.le_div_iff_mul_le (by omega)]; omega

lemma card_monos_le_pow (σ : Type) [Fintype σ] [DecidableEq σ] (n : ℕ) (hn : 1 ≤ n)
    (hσ : Fintype.card σ ≤ n) (j : ℕ) : (monos σ (j : ℤ)).card ≤ n ^ j := by
  rw [card_monos_nat]
  calc (Fintype.card σ + j - 1).choose j ≤ (n + j - 1).choose j :=
        Nat.choose_le_choose _ (by omega)
    _ ≤ n ^ j := choose_le_pow' n hn j

/-- The first factor: `|monos(Fin k)(t − e)| ≤ n^t n^{-e}`. -/
lemma card_monos_sub_le (k n t e : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    ((monos (Fin k) ((t : ℤ) - (e : ℤ))).card : ℝ) ≤ (n : ℝ) ^ (t : ℝ) * (n : ℝ) ^ (-(e : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases lt_or_ge t e with h | h
  · have : monos (Fin k) ((t : ℤ) - (e : ℤ)) = ∅ := by
      simp only [monos]; rw [if_neg (by omega)]
    rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    have h1 : ((e + j : ℕ) : ℤ) - (e : ℤ) = (j : ℤ) := by push_cast; ring
    rw [h1]
    have h2 := card_monos_le_pow (Fin k) n hn (by simpa using hk) j
    have h3 : ((n : ℝ) ^ ((e + j : ℕ) : ℝ) * (n : ℝ) ^ (-(e : ℝ))) = (n : ℝ) ^ j := by
      rw [← Real.rpow_add hn0, ← Real.rpow_natCast]; congr 1; push_cast; ring
    rw [h3]; exact_mod_cast h2

/-- Each term of the second factor: `1/|monos(Fin q)(e)| ≤ E! (4L)^E n^{-e}`. -/
lemma inv_card_monos_le (n L q e E : ℕ) (hL : 1 ≤ L) (hn : 4 * L ≤ n)
    (hq : (n : ℝ) / (4 * L) ≤ q) (he : 1 ≤ e) (heE : e ≤ E) :
    (1 : ℝ) / ((monos (Fin q) (e : ℤ)).card : ℝ) ≤
      (E.factorial : ℝ) * (4 * L : ℝ) ^ E * (n : ℝ) ^ (-(e : ℝ)) := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hn0 : (0 : ℝ) < n := by
    have : (4 * L : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hb := (card_monos_bounds (Fin q) e he).1
  simp only [Fintype.card_fin] at hb
  have hx : 0 < (n : ℝ) / (4 * L) := by positivity
  have hqe : ((n : ℝ) / (4 * L)) ^ e / (e.factorial : ℝ) ≤ (q : ℝ) ^ e / (e.factorial : ℝ) := by
    gcongr
  have hpos : 0 < ((n : ℝ) / (4 * L)) ^ e / (e.factorial : ℝ) := by positivity
  calc (1 : ℝ) / ((monos (Fin q) (e : ℤ)).card : ℝ)
      ≤ 1 / (((n : ℝ) / (4 * L)) ^ e / (e.factorial : ℝ)) :=
        one_div_le_one_div_of_le hpos (hqe.trans hb)
    _ = (e.factorial : ℝ) * (4 * L : ℝ) ^ e * (n : ℝ) ^ (-(e : ℝ)) := by
        rw [Real.rpow_neg hn0.le, Real.rpow_natCast, div_pow]; field_simp
    _ ≤ (E.factorial : ℝ) * (4 * L : ℝ) ^ E * (n : ℝ) ^ (-(e : ℝ)) := by
        gcongr; all_goals first | exact_mod_cast Nat.factorial_le heE | linarith

/-- **Stub F8 (the dimension product of Proposition 4.8 is `< 1`).** -/
theorem hprod_bound (ε : ℝ) (hε : 0 < ε) (dmax Dmax t : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (m : ℕ) (d D : Fin m → ℕ),
      (∀ i, 1 ≤ d i ∧ d i ≤ dmax) → (∀ i, 1 ≤ D i ∧ D i ≤ Dmax) →
      ∑ i, (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) ≤ (n : ℝ) ^ (-ε) →
        ((∑ i, (monos (Fin (Ksplit n (Lsplit ε t))) ((t : ℤ) - (d i : ℤ) * (D i : ℤ))).card :
            ℕ) : ℝ) *
          ∏ _ℓ : Fin (Lsplit ε t), (2 * ∑ i, (1 : ℝ) /
            ((monos (Fin (Qsplit n (Lsplit ε t))) ((d i : ℤ) * (D i : ℤ))).card : ℝ)) < 1 := by
  set L := Lsplit ε t with hLdef
  have hL : 1 ≤ L := one_le_Lsplit ε t
  have hLt := t_lt_Lsplit ε hε t
  set E := dmax * Dmax
  set C₀ : ℝ := 2 * (E.factorial : ℝ) * (4 * L : ℝ) ^ E with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  set δ : ℝ := (L : ℝ) * ε + ε - t with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  refine ⟨max (4 * L) ⌈(C₀ ^ L + 1) ^ δ⁻¹⌉₊, fun n hn m d D hd hD hsum => ?_⟩
  have hn4 : 4 * L ≤ n := le_of_max_le_left hn
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hq := qsplit_ge n L hL hn4
  have hkn : Ksplit n L ≤ n := by unfold Ksplit; omega
  -- first factor
  have hS1 : ((∑ i, (monos (Fin (Ksplit n L)) ((t : ℤ) - (d i : ℤ) * (D i : ℤ))).card : ℕ) : ℝ)
      ≤ (n : ℝ) ^ (t : ℝ) * (n : ℝ) ^ (-ε) := by
    push_cast
    calc ∑ i, ((monos (Fin (Ksplit n L)) ((t : ℤ) - (d i : ℤ) * (D i : ℤ))).card : ℝ)
        ≤ ∑ i, (n : ℝ) ^ (t : ℝ) * (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) := by
          gcongr with i
          have := card_monos_sub_le (Ksplit n L) n t (d i * D i) hn1 hkn
          push_cast at this ⊢; exact this
      _ = (n : ℝ) ^ (t : ℝ) * ∑ i, (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ _ := by gcongr
  -- second factor
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 2 * ∑ i, (1 : ℝ) /
      ((monos (Fin (Qsplit n L)) ((d i : ℤ) * (D i : ℤ))).card : ℝ) := ⟨_, rfl⟩
  rw [← hX]
  have hX0 : 0 ≤ X := by
    rw [hX]; exact mul_nonneg two_pos.le (Finset.sum_nonneg fun i _ => by positivity)
  have hXle : X ≤ C₀ * (n : ℝ) ^ (-ε) := by
    rw [hX, hC₀]
    calc 2 * ∑ i, (1 : ℝ) / ((monos (Fin (Qsplit n L)) ((d i : ℤ) * (D i : ℤ))).card : ℝ)
        ≤ 2 * ∑ i, (E.factorial : ℝ) * (4 * L : ℝ) ^ E * (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) := by
          gcongr with i
          have h := inv_card_monos_le n L (Qsplit n L) (d i * D i) E hL hn4 hq
            (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := (hd i).1; omega)
              (by have := (hD i).1; omega)))
            (Nat.mul_le_mul (hd i).2 (hD i).2)
          push_cast at h ⊢; exact h
      _ = 2 * ((E.factorial : ℝ) * (4 * L : ℝ) ^ E) *
            ∑ i, (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ 2 * ((E.factorial : ℝ) * (4 * L : ℝ) ^ E) * (n : ℝ) ^ (-ε) := by gcongr
      _ = _ := by ring
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hfin : C₀ ^ L < (n : ℝ) ^ δ := by
    have h1 : ((C₀ ^ L + 1) ^ δ⁻¹ : ℝ) ≤ n := by
      have := le_of_max_le_right hn
      exact (Nat.le_ceil _).trans (by exact_mod_cast this)
    have h2 : ((C₀ ^ L + 1) ^ δ⁻¹) ^ δ ≤ (n : ℝ) ^ δ :=
      Real.rpow_le_rpow (by positivity) h1 hδ0.le
    rw [Real.rpow_inv_rpow (by positivity) hδ0.ne'] at h2
    linarith
  calc ((∑ i, (monos (Fin (Ksplit n L)) ((t : ℤ) - (d i : ℤ) * (D i : ℤ))).card : ℕ) : ℝ) * X ^ L
      ≤ ((n : ℝ) ^ (t : ℝ) * (n : ℝ) ^ (-ε)) * (C₀ * (n : ℝ) ^ (-ε)) ^ L := by
        gcongr
    _ = C₀ ^ L * (n : ℝ) ^ (-δ) := by
        have he : (n : ℝ) ^ (-δ) = (n : ℝ) ^ (t : ℝ) * (n : ℝ) ^ (-ε) * ((n : ℝ) ^ (-ε)) ^ L := by
          rw [← Real.rpow_natCast ((n : ℝ) ^ (-ε)), ← Real.rpow_mul hn0.le,
            ← Real.rpow_add hn0, ← Real.rpow_add hn0, hδ]
          congr 1; ring
        rw [he, mul_pow]; ring
    _ < 1 := by
        rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, div_lt_one (by positivity)]
        exact hfin

end ApproxSyzygies.Smoothed.Dev.G41.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias hprod_bound := ApproxSyzygies.Smoothed.Dev.G41.PartF.hprod_bound

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartF
open ApproxSyzygies.Smoothed
variable {P : Type} (S : Set P) (x : P → ℝ)
/-! ### F9: polynomial bounds -/
/-- `f` is bounded on `S` by `K x^j` with constants `K, j`, and is nonnegative there. -/
def PB (f : P → ℝ) : Prop := ∃ K : ℝ, 0 ≤ K ∧ ∃ j : ℕ, ∀ p ∈ S, 0 ≤ f p ∧ f p ≤ K * x p ^ j

end ApproxSyzygies.Smoothed.Dev.G41.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartF
open ApproxSyzygies.Smoothed
variable {P : Type} (S : Set P) (x : P → ℝ)
variable {S x}
lemma PB.const (c : ℝ) (hc : 0 ≤ c) : PB S x fun _ => c :=
  ⟨c, hc, 0, fun _ _ => ⟨hc, by simp⟩⟩

lemma PB.self (hx : ∀ p ∈ S, 1 ≤ x p) : PB S x x :=
  ⟨1, zero_le_one, 1, fun p hp => ⟨by linarith [hx p hp], by simp⟩⟩

lemma PB.mono {f g : P → ℝ} (hg : PB S x g) (hfg : ∀ p ∈ S, 0 ≤ f p ∧ f p ≤ g p) : PB S x f := by
  obtain ⟨K, hK, j, h⟩ := hg
  exact ⟨K, hK, j, fun p hp => ⟨(hfg p hp).1, (hfg p hp).2.trans (h p hp).2⟩⟩

lemma PB.add (hx : ∀ p ∈ S, 1 ≤ x p) {f g : P → ℝ} (hf : PB S x f) (hg : PB S x g) :
    PB S x fun p => f p + g p := by
  obtain ⟨K, hK, j, h⟩ := hf
  obtain ⟨K', hK', j', h'⟩ := hg
  refine ⟨K + K', by positivity, j + j', fun p hp => ⟨by linarith [(h p hp).1, (h' p hp).1], ?_⟩⟩
  have h1 : x p ^ j ≤ x p ^ (j + j') := pow_le_pow_right₀ (hx p hp) (by omega)
  have h2 : x p ^ j' ≤ x p ^ (j + j') := pow_le_pow_right₀ (hx p hp) (by omega)
  nlinarith [(h p hp).2, (h' p hp).2]

lemma PB.mul (hx : ∀ p ∈ S, 1 ≤ x p) {f g : P → ℝ} (hf : PB S x f) (hg : PB S x g) :
    PB S x fun p => f p * g p := by
  obtain ⟨K, hK, j, h⟩ := hf
  obtain ⟨K', hK', j', h'⟩ := hg
  refine ⟨K * K', by positivity, j + j', fun p hp => ⟨mul_nonneg (h p hp).1 (h' p hp).1, ?_⟩⟩
  have hx0 : 0 ≤ x p := by linarith [hx p hp]
  calc f p * g p ≤ (K * x p ^ j) * (K' * x p ^ j') :=
        mul_le_mul (h p hp).2 (h' p hp).2 (h' p hp).1 (by positivity)
    _ = K * K' * x p ^ (j + j') := by ring

lemma PB.pow (hx : ∀ p ∈ S, 1 ≤ x p) {f : P → ℝ} (hf : PB S x f) (e : ℕ) :
    PB S x fun p => f p ^ e := by
  induction e with
  | zero => simpa using PB.const (S := S) (x := x) 1 zero_le_one
  | succ e ih => simpa [pow_succ] using PB.mul hx ih hf

end ApproxSyzygies.Smoothed.Dev.G41.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartF
open ApproxSyzygies.Smoothed
lemma sqrt_le_self' {y : ℝ} (hy : 1 ≤ y) : Real.sqrt y ≤ y := by
  rw [Real.sqrt_le_left (by linarith)]; nlinarith

lemma rpow_le_ceil_pow {y : ℝ} (hy : 1 ≤ y) (a : ℝ) : y ^ a ≤ y ^ ⌈a⌉₊ := by
  rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hy (Nat.le_ceil a)

/-- **Stub F9 (the constants of the shrinking step).** -/
theorem shrink_arith (ε : ℝ) (hε : 0 < ε) (dmax Dmax t : ℕ) (CI A c c' : ℝ) (k N₁ : ℕ)
    (hCI : 0 ≤ CI) (hA : 0 ≤ A) (hc : 0 < c) (hc' : 0 < c') :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n →
      ∀ (m : ℕ), 1 ≤ m → (m : ℝ) ≤ (n : ℝ) ^ (dmax * Dmax) → ∀ dl : ℕ, 1 ≤ dl → dl ≤ dmax →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      N₁ ≤ Qsplit n (Lsplit ε t) ∧ 4 * (dmax * Dmax).factorial ≤ Qsplit n (Lsplit ε t) ∧
      (let L := Lsplit ε t
       let q := Qsplit n L
       let Abd : ℝ := 1 + 2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax)
       let Nbt : ℝ := (m : ℝ) * Abd ^ Dmax + 2 * Abd
       let B : ℝ := A * (1 + (n : ℝ) ^ CI * ρ ^ (-CI)) ^ k * (1 + Nbt) ^ k
       let β : ℝ := Abd ^ Dmax + B + 1
       let η₀ : ℝ := c' * ρ ^ Dmax / (q : ℝ) ^ (dmax * Dmax)
       let Qb : ℝ := (m : ℝ) * (q : ℝ) ^ (dmax * Dmax) / η₀
       2 * (m : ℝ) * (1 + β * Qb) ^ L * B ≤ (n : ℝ) ^ C₂ * ρ ^ (-C₂) ∧
       (m : ℝ) * L * Real.exp (-(c * (q : ℝ) ^ dl)) ≤ Real.exp (-(c₂ * (n : ℝ) ^ dl))) := by
  set L := Lsplit ε t with hLdef
  have hL : 1 ≤ L := one_le_Lsplit ε t
  set E := dmax * Dmax with hE
  -- the polynomial bound
  let S : Set (ℕ × ℕ × ℝ) := {p | 4 * L ≤ p.1 ∧ 1 ≤ p.2.1 ∧ (p.2.1 : ℝ) ≤ (p.1 : ℝ) ^ E ∧
    0 < p.2.2 ∧ p.2.2 ≤ 1}
  let x : ℕ × ℕ × ℝ → ℝ := fun p => ((p.1 : ℝ) + 1) / p.2.2
  have hS : ∀ p ∈ S, 1 ≤ p.1 ∧ 1 ≤ Qsplit p.1 L ∧ Qsplit p.1 L ≤ p.1 ∧ 0 < p.2.2 ∧ p.2.2 ≤ 1 ∧
      1 ≤ p.2.1 ∧ (p.2.1 : ℝ) ≤ (p.1 : ℝ) ^ E := by
    rintro ⟨n, m, ρ⟩ ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, qsplit_pos n L hL h1, Nat.div_le_self _ _, h4, h5, h2, h3⟩
  have hxn : ∀ p ∈ S, (p.1 : ℝ) + 1 ≤ x p := by
    intro p hp
    obtain ⟨-, -, -, h4, h5, -⟩ := hS p hp
    show (p.1 : ℝ) + 1 ≤ ((p.1 : ℝ) + 1) / p.2.2
    rw [le_div_iff₀ h4]; nlinarith
  have hxR : ∀ p ∈ S, 1 / p.2.2 ≤ x p := by
    intro p hp
    obtain ⟨-, -, -, h4, -, -⟩ := hS p hp
    show 1 / p.2.2 ≤ ((p.1 : ℝ) + 1) / p.2.2
    gcongr; linarith [(Nat.cast_nonneg p.1 : (0 : ℝ) ≤ p.1)]
  have hx : ∀ p ∈ S, 1 ≤ x p := fun p hp => by
    linarith [hxn p hp, (Nat.cast_nonneg p.1 : (0 : ℝ) ≤ p.1)]
  have Pn : PB S x fun p => (p.1 : ℝ) := (PB.self hx).mono fun p hp =>
    ⟨Nat.cast_nonneg _, by linarith [hxn p hp]⟩
  have Pn1 : PB S x fun p => (((p.1 + 1 : ℕ) : ℝ)) := (PB.self hx).mono fun p hp =>
    ⟨Nat.cast_nonneg _, by push_cast; exact hxn p hp⟩
  have PR : PB S x fun p => 1 / p.2.2 := (PB.self hx).mono fun p hp =>
    ⟨by have := (hS p hp).2.2.2.1; positivity, hxR p hp⟩
  have Pq : PB S x fun p => (Qsplit p.1 L : ℝ) := Pn.mono fun p hp =>
    ⟨Nat.cast_nonneg _, by exact_mod_cast (hS p hp).2.2.1⟩
  have Pm : PB S x fun p => (p.2.1 : ℝ) := (Pn.pow hx E).mono fun p hp =>
    ⟨Nat.cast_nonneg _, (hS p hp).2.2.2.2.2.2⟩
  have PAbd : PB S x fun p => 1 + 2 * Real.sqrt (((p.1 + 1 : ℕ) : ℝ) ^ dmax) :=
    (PB.add hx (PB.const 1 zero_le_one) (PB.mul hx (PB.const 2 zero_le_two) (Pn1.pow hx dmax))).mono
      fun p hp => ⟨by positivity, by
        have h1 : (1 : ℝ) ≤ ((p.1 + 1 : ℕ) : ℝ) ^ dmax := one_le_pow₀ (by push_cast; linarith
          [(Nat.cast_nonneg p.1 : (0 : ℝ) ≤ p.1)])
        have := sqrt_le_self' h1
        linarith⟩
  have Ptau : PB S x fun p => 1 + (p.1 : ℝ) ^ CI * p.2.2 ^ (-CI) :=
    (PB.add hx (PB.const 1 zero_le_one) (PB.mul hx (Pn.pow hx ⌈CI⌉₊) (PR.pow hx ⌈CI⌉₊))).mono
      fun p hp => by
        obtain ⟨h1, -, -, h4, h5, -⟩ := hS p hp
        have hn1 : (1 : ℝ) ≤ p.1 := by exact_mod_cast h1
        have hR : (1 : ℝ) ≤ 1 / p.2.2 := by rw [le_div_iff₀ h4]; linarith
        have e1 : p.2.2 ^ (-CI) = (1 / p.2.2) ^ CI := by
          rw [Real.rpow_neg h4.le, one_div, Real.inv_rpow h4.le]
        rw [e1]
        refine ⟨by positivity, ?_⟩
        have := rpow_le_ceil_pow hn1 CI
        have := rpow_le_ceil_pow hR CI
        gcongr
  have PNbt : PB S x fun p => (p.2.1 : ℝ) * (1 + 2 * Real.sqrt (((p.1 + 1 : ℕ) : ℝ) ^ dmax)) ^ Dmax
      + 2 * (1 + 2 * Real.sqrt (((p.1 + 1 : ℕ) : ℝ) ^ dmax)) :=
    PB.add hx (PB.mul hx Pm (PAbd.pow hx Dmax)) (PB.mul hx (PB.const 2 zero_le_two) PAbd)
  have PB' : PB S x fun p => A * (1 + (p.1 : ℝ) ^ CI * p.2.2 ^ (-CI)) ^ k *
      (1 + ((p.2.1 : ℝ) * (1 + 2 * Real.sqrt (((p.1 + 1 : ℕ) : ℝ) ^ dmax)) ^ Dmax
      + 2 * (1 + 2 * Real.sqrt (((p.1 + 1 : ℕ) : ℝ) ^ dmax)))) ^ k :=
    PB.mul hx (PB.mul hx (PB.const A hA) (Ptau.pow hx k))
      ((PB.add hx (PB.const 1 zero_le_one) PNbt).pow hx k)
  have Pβ := PB.add hx (PB.add hx (PAbd.pow hx Dmax) PB') (PB.const 1 zero_le_one)
  have PQb : PB S x fun p => (p.2.1 : ℝ) * (Qsplit p.1 L : ℝ) ^ E /
      (c' * p.2.2 ^ Dmax / (Qsplit p.1 L : ℝ) ^ E) :=
    (PB.mul hx (PB.mul hx (PB.mul hx (PB.const (1 / c') (by positivity)) Pm)
      (PB.mul hx (Pq.pow hx E) (Pq.pow hx E))) (PR.pow hx Dmax)).mono fun p hp => by
        obtain ⟨-, hq, -, h4, -, -⟩ := hS p hp
        have hq0 : (0 : ℝ) < Qsplit p.1 L := by exact_mod_cast hq
        refine ⟨by positivity, le_of_eq ?_⟩
        field_simp
        have hρD : p.2.2 ^ Dmax * (1 / p.2.2) ^ Dmax = 1 := by
          rw [← mul_pow, mul_one_div_cancel h4.ne', one_pow]
        rw [mul_assoc, hρD, mul_one]
  have PT := PB.mul hx (PB.mul hx (PB.mul hx (PB.const 2 zero_le_two) Pm)
    ((PB.add hx (PB.const 1 zero_le_one) (PB.mul hx Pβ PQb)).pow hx L)) PB'
  obtain ⟨K, hK, j, hT⟩ := PT
  -- the exponential bound
  set c₂ : ℝ := c / (2 * (4 * L : ℝ) ^ dmax) with hc₂
  have hc₂0 : 0 < c₂ := by positivity
  refine ⟨(j + 1 : ℕ), Nat.cast_nonneg _, c₂, hc₂0,
    max (max (4 * L) (2 * L * (N₁ + 4 * E.factorial + 1)))
      (max ⌈K * 2 ^ j⌉₊ ⌈(L : ℝ) * (E + 1).factorial / c₂ ^ (E + 1)⌉₊),
    fun n hn m hm1 hmn dl hdl1 hdl ρ hρ hρ1 => ?_⟩
  have hn4 : 4 * L ≤ n := le_of_max_le_left (le_of_max_le_left hn)
  have hnN : 2 * L * (N₁ + 4 * E.factorial + 1) ≤ n := le_of_max_le_right (le_of_max_le_left hn)
  have hnK : (K * 2 ^ j : ℝ) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_left (le_of_max_le_right hn))
  have hnE : (L : ℝ) * (E + 1).factorial / c₂ ^ (E + 1) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right (le_of_max_le_right hn))
  have hqN : N₁ + 4 * E.factorial + 1 ≤ Qsplit n L := by
    unfold Qsplit; rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]; exact hnN
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  refine ⟨by omega, by omega, ?_⟩
  intro L' q Abd Nbt B β η₀ Qb
  have hpS : ((n, m, ρ) : ℕ × ℕ × ℝ) ∈ S := ⟨hn4, hm1, hmn, hρ, hρ1⟩
  refine ⟨?_, ?_⟩
  · have h := (hT _ hpS).2
    refine h.trans ?_
    show K * (((n : ℝ) + 1) / ρ) ^ j ≤ (n : ℝ) ^ ((j + 1 : ℕ) : ℝ) * ρ ^ (-((j + 1 : ℕ) : ℝ))
    rw [Real.rpow_natCast, Real.rpow_neg hρ.le, Real.rpow_natCast]
    have hR : (1 : ℝ) ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; linarith
    have hx2 : ((n : ℝ) + 1) / ρ ≤ 2 * (n * (1 / ρ)) := by
      rw [div_le_iff₀ hρ]; field_simp; linarith
    calc K * (((n : ℝ) + 1) / ρ) ^ j ≤ K * (2 * (n * (1 / ρ))) ^ j := by
          gcongr
      _ = (K * 2 ^ j) * (n * (1 / ρ)) ^ j := by ring
      _ ≤ (n * (1 / ρ)) * (n * (1 / ρ)) ^ j := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact hnK.trans (le_mul_of_one_le_right hn0.le hR)
      _ = (n : ℝ) ^ (j + 1) * (ρ ^ (j + 1))⁻¹ := by
          rw [← pow_succ', mul_pow, one_div, inv_pow]
  · show (m : ℝ) * L * Real.exp (-(c * (Qsplit n L : ℝ) ^ dl)) ≤ Real.exp (-(c₂ * (n : ℝ) ^ dl))
    have hq := qsplit_ge n L hL hn4
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hqdl : (n : ℝ) ^ dl / (4 * L : ℝ) ^ dmax ≤ (Qsplit n L : ℝ) ^ dl := by
      calc (n : ℝ) ^ dl / (4 * L : ℝ) ^ dmax ≤ (n : ℝ) ^ dl / (4 * L : ℝ) ^ dl := by
            gcongr; linarith
        _ = ((n : ℝ) / (4 * L)) ^ dl := by rw [div_pow]
        _ ≤ _ := by gcongr
    have h1 : 2 * c₂ * (n : ℝ) ^ dl ≤ c * (Qsplit n L : ℝ) ^ dl := by
      calc 2 * c₂ * (n : ℝ) ^ dl = c * ((n : ℝ) ^ dl / (4 * L : ℝ) ^ dmax) := by
            rw [hc₂]; field_simp
        _ ≤ _ := by gcongr
    have hndl : (n : ℝ) ≤ (n : ℝ) ^ dl := by
      calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hn1 hdl1
    have h2 : (m : ℝ) * L ≤ Real.exp (c₂ * (n : ℝ) ^ dl) := by
      have he := Real.pow_div_factorial_le_exp (c₂ * (n : ℝ)) (by positivity) (E + 1)
      have hfac : (0 : ℝ) < (E + 1).factorial := by exact_mod_cast Nat.factorial_pos _
      have h3 : (L : ℝ) * (E + 1).factorial ≤ c₂ ^ (E + 1) * n := by
        rw [div_le_iff₀ (by positivity)] at hnE; linarith
      calc (m : ℝ) * L ≤ (n : ℝ) ^ E * L := by gcongr
        _ ≤ (c₂ * n) ^ (E + 1) / (E + 1).factorial := by
            rw [le_div_iff₀ hfac, mul_pow, pow_succ (n : ℝ) E]
            nlinarith [pow_pos hn0 E]
        _ ≤ Real.exp (c₂ * n) := he
        _ ≤ _ := Real.exp_le_exp.2 (by gcongr)
    calc (m : ℝ) * L * Real.exp (-(c * (Qsplit n L : ℝ) ^ dl))
        ≤ Real.exp (c₂ * (n : ℝ) ^ dl) * Real.exp (-(2 * c₂ * (n : ℝ) ^ dl)) := by
          gcongr
      _ = Real.exp (-(c₂ * (n : ℝ) ^ dl)) := by rw [← Real.exp_add]; congr 1; ring

end ApproxSyzygies.Smoothed.Dev.G41.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias shrink_arith := ApproxSyzygies.Smoothed.Dev.G41.PartF.shrink_arith

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartN
open ApproxSyzygies.Smoothed
/-! # Theorem 4.1 Part N: stub F10 (norms on the Gaussian norm event, block by block) -/
lemma norm_le_sum_norm' {m : ℕ} {β : Fin m → Type} [∀ i, SeminormedAddCommGroup (β i)]
    (g : PiLp 2 β) : ‖g‖ ≤ ∑ i, ‖g i‖ := by
  have h0 : 0 ≤ ∑ i, ‖g i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine le_of_pow_le_pow_left₀ two_ne_zero h0 ?_
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _

end ApproxSyzygies.Smoothed.Dev.G41.PartN
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial Set
namespace ApproxSyzygies.Smoothed.Dev.G41.PartM
open ApproxSyzygies.Smoothed
variable {σ : Type} [Fintype σ] [DecidableEq σ] {X : Type} [TopologicalSpace X]
/-! # Part M: stub S1 (`measurableSet_shrinkBad`)

The main point is that `ω ↦ ‖Π_{(range M(ω))^⊥} y‖` is measurable when `M(ω)` depends
continuously on `ω`: it equals `⨅_w ‖y − M(ω) w‖`, an infimum that may be taken over a countable
dense set of `w`. The existential over `h` reduces to a countable dense set because the condition
is open in `h`. -/
/-- Every coefficient of the family of polynomials `f x` is continuous in `x`. -/
def CoeffCont (f : X → MvPolynomial σ ℝ) : Prop := ∀ γ, Continuous fun x => coeff γ (f x)

lemma cc_toPoly {d : ℤ} {a : X → Hom σ d} (ha : Continuous a) :
    CoeffCont fun x => toPoly (a x) := fun γ =>
  ((lcoeff ℝ γ).comp (toPolyL (σ := σ) d)).continuous_of_finiteDimensional.comp ha

lemma cc_const (f : MvPolynomial σ ℝ) : CoeffCont fun _ : X => f := fun _ => continuous_const

lemma cc_mul {f g : X → MvPolynomial σ ℝ} (hf : CoeffCont f) (hg : CoeffCont g) :
    CoeffCont fun x => f x * g x := fun γ => by
  simp only [coeff_mul]
  exact continuous_finsetSum _ fun p _ => (hf _).mul (hg _)

lemma cc_pow {f : X → MvPolynomial σ ℝ} (hf : CoeffCont f) (D : ℕ) :
    CoeffCont fun x => f x ^ D := by
  induction D with
  | zero => intro γ; simp only [pow_zero]; exact continuous_const
  | succ D ih => simp only [pow_succ]; exact cc_mul ih hf

lemma continuous_ofPoly' {f : X → MvPolynomial σ ℝ} (hf : CoeffCont f) (e : ℤ) :
    Continuous fun x => (ofPoly e (f x) : Hom σ e) := by
  unfold ofPoly
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun α => (hf _).mul continuous_const)

lemma mulMap_apply' {m : ℕ} {e : Fin m → ℤ} (p : ∀ i, Hom σ (e i)) (t : ℤ)
    (h : Tup σ fun i => t - e i) :
    mulMap p t h = ∑ i, ofPoly t (toPoly (p i) * toPoly (h i)) := by
  simp [mulMap]
  rfl

lemma continuous_mulMap' {m : ℕ} {e : Fin m → ℤ} (p : X → ∀ i, Hom σ (e i))
    (hp : ∀ i, CoeffCont fun x => toPoly (p x i)) (t : ℤ) (h : Tup σ fun i => t - e i) :
    Continuous fun x => mulMap (p x) t h := by
  simp only [mulMap_apply']
  exact continuous_finsetSum _ fun i _ => continuous_ofPoly' (cc_mul (hp i) (cc_const _)) t

end ApproxSyzygies.Smoothed.Dev.G41.PartM
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial Set
namespace ApproxSyzygies.Smoothed.Dev.G41.PartM
open ApproxSyzygies.Smoothed
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
lemma norm_starProjection_orth_range (M : E →ₗ[ℝ] F) (y : F) :
    ‖(LinearMap.range M)ᗮ.starProjection y‖ = ⨅ w, ‖y - M w‖ := by
  rw [Submodule.starProjection_orthogonal', ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, Submodule.starProjection_minimal]
  exact ((LinearMap.surjective_rangeRestrict M).iInf_comp
    (fun x : LinearMap.range M => ‖y - x‖)).symm

lemma iInf_dense_seq {W : Type} [TopologicalSpace W] [Nonempty W] {c : ℕ → W}
    (hc : DenseRange c) {G : W → ℝ} (hG : Continuous G) (h0 : ∀ w, 0 ≤ G w) :
    ⨅ w, G w = ⨅ n, G (c n) := by
  have hbdd : BddBelow (range G) := ⟨0, by rintro _ ⟨w, rfl⟩; exact h0 w⟩
  have hbdd' : BddBelow (range fun n => G (c n)) := ⟨0, by rintro _ ⟨n, rfl⟩; exact h0 _⟩
  refine le_antisymm (le_ciInf fun n => ciInf_le hbdd (c n)) (le_ciInf fun w => ?_)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := hc.exists_mem_open (isOpen_Iio.preimage hG)
    (⟨w, by simp only [mem_preimage, mem_Iio]; linarith⟩ : (G ⁻¹' Iio (G w + ε)).Nonempty)
  exact (ciInf_le hbdd' n).trans_lt hn

/-- The main measurability fact: `ω ↦ ‖Π_{(range M(ω))^⊥} y‖` is measurable. -/
lemma measurable_norm_starProjection {Ω : Type} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] (M : Ω → E →ₗ[ℝ] F) (hM : ∀ w, Continuous fun ω => M ω w)
    (y : F) : Measurable fun ω => ‖(LinearMap.range (M ω))ᗮ.starProjection y‖ := by
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq E
  have : (fun ω => ‖(LinearMap.range (M ω))ᗮ.starProjection y‖) =
      fun ω => ⨅ n, ‖y - M ω (c n)‖ := by
    funext ω
    rw [norm_starProjection_orth_range,
      iInf_dense_seq (G := fun w => ‖y - M ω w‖) hc
        (continuous_const.sub (M ω).continuous_of_finiteDimensional).norm
        fun _ => norm_nonneg _]
  rw [this]
  exact Measurable.iInf fun n => (continuous_const.sub (hM (c n))).norm.measurable

end ApproxSyzygies.Smoothed.Dev.G41.PartM
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial Set
namespace ApproxSyzygies.Smoothed.Dev.G41.PartM
open ApproxSyzygies.Smoothed
variable {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
lemma continuous_yPart {d : ℤ} : Continuous (yPart : Hom (Y ⊕ Z) d → Hom Y d) := by
  have : (yPart : Hom (Y ⊕ Z) d → Hom Y d) =
      ((ofPolyL d) ∘ₗ (aeval (Sum.elim X (fun _ : Z => (0 : MvPolynomial Y ℝ)))).toLinearMap
        ∘ₗ toPolyL d : Hom (Y ⊕ Z) d →ₗ[ℝ] Hom Y d) := by
    funext u; rfl
  rw [this]
  exact LinearMap.continuous_of_finiteDimensional _

lemma measurable_restrictY {m : ℕ} {d : Fin m → ℤ} :
    Measurable (restrictY : (∀ i, monos (Y ⊕ Z) (d i) → ℝ) → ∀ i, monos Y (d i) → ℝ) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun β => ?_
  simp only [restrictY]
  split_ifs
  · exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact measurable_const

lemma continuous_perturb {m : ℕ} {d : Fin m → ℕ} (abar : ∀ i, Hom (Y ⊕ Z) (d i : ℤ)) (ρ : ℝ)
    (i : Fin m) :
    Continuous fun ω : (∀ i, monos (Y ⊕ Z) (d i : ℤ) → ℝ) => perturbOn (abar i) ρ (ω i) := by
  unfold perturbOn
  have : Continuous fun ω : (∀ i, monos (Y ⊕ Z) (d i : ℤ) → ℝ) =>
      (WithLp.toLp 2 (ω i) : Hom (Y ⊕ Z) (d i : ℤ)) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_apply i)
  exact continuous_const.add (this.const_smul ρ)

lemma continuous_yPartTup {m : ℕ} {e : Fin m → ℤ} :
    Continuous (yPartTup : Tup (Y ⊕ Z) e → Tup Y e) := by
  unfold yPartTup
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    continuous_yPart.comp (PiLp.continuous_apply 2 _ i))

lemma continuous_gVec {m : ℕ} (d D : Fin m → ℕ) (t : ℕ) (a₀ : ∀ j, Hom Y (d j : ℤ)) :
    Continuous (gVec d D t a₀) := by
  unfold gVec
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    (Submodule.starProjection _).continuous.comp (PiLp.continuous_apply 2 _ i))

lemma norm_gVec {m : ℕ} (d D : Fin m → ℕ) (t : ℕ) (a₀ : ∀ j, Hom Y (d j : ℤ))
    (h₀ : Tup Y (fun i => (t : ℤ) - (d i : ℤ) * (D i : ℤ))) :
    ‖gVec d D t a₀ h₀‖ = Real.sqrt (∑ i, ‖(Jpiece d D t a₀ i)ᗮ.starProjection (h₀ i)‖ ^ 2) := by
  rw [PiLp.norm_eq_of_L2]
  rfl

lemma measurable_norm_J {Ω : Type} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {m : ℕ} (d D : Fin m → ℕ) (t : ℕ) (i : Fin m)
    (a : Ω → ∀ j, Hom Y (d j : ℤ)) (ha : ∀ j, Continuous fun ω => a ω j)
    (y : Hom Y ((t : ℤ) - (d i : ℤ) * (D i : ℤ))) :
    Measurable fun ω => ‖(Jpiece d D t (a ω) i)ᗮ.starProjection y‖ := by
  have hmod : ∀ j, CoeffCont fun ω =>
      (if j = i then toPoly (a ω i) else toPoly (a ω j) ^ D j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [if_true]
      exact cc_toPoly (ha j)
    · simp only [hj, if_false]
      exact cc_pow (cc_toPoly (ha j)) _
  have hslot : ∀ j, CoeffCont fun ω => toPoly (modGen d D i (toPoly (a ω i)) (a ω) j) :=
    fun j => cc_toPoly (a := fun ω => modGen d D i (toPoly (a ω i)) (a ω) j)
      (continuous_ofPoly' (hmod j) _)
  unfold Jpiece idealDeg
  exact measurable_norm_starProjection
    (fun ω => mulMap (modGen d D i (toPoly (a ω i)) (a ω)) ((t : ℤ) - (d i : ℤ) * (D i : ℤ)))
    (fun w => continuous_mulMap' _ hslot _ w) y

end ApproxSyzygies.Smoothed.Dev.G41.PartM
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial Set
namespace ApproxSyzygies.Smoothed.Dev.G41.PartM
open ApproxSyzygies.Smoothed
/-- **Stub S1 (measurability of the shrinking event).** -/
theorem measurableSet_shrinkBad {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z]
    [DecidableEq Z] {m : ℕ} (d D : Fin m → ℕ) (abar : ∀ i, Hom (Y ⊕ Z) (d i : ℤ)) (ρ K₂ : ℝ)
    (t : ℕ) (G : Set (∀ i, monos Y (d i : ℤ) → ℝ)) (hG : MeasurableSet G) :
    MeasurableSet (ShrinkBad d D abar ρ K₂ t G) := by
  have h1 : MeasurableSet {ω : ∀ i, monos (Y ⊕ Z) (d i : ℤ) → ℝ | restrictY ω ∈ G} :=
    measurable_restrictY hG
  have h2 : MeasurableSet {ω : ∀ i, monos (Y ⊕ Z) (d i : ℤ) → ℝ | Ngood d ω} := by
    simp only [Ngood, ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le
      ((PiLp.continuous_toLp 2 _).comp (continuous_apply i)).norm.measurable measurable_const
  -- the generators and their pure-`y` parts depend continuously on `ω`
  have ha : ∀ i, Continuous fun ω : (∀ i, monos (Y ⊕ Z) (d i : ℤ) → ℝ) =>
      perturbOn (abar i) ρ (ω i) := continuous_perturb abar ρ
  have ha₀ : ∀ i, Continuous fun ω : (∀ i, monos (Y ⊕ Z) (d i : ℤ) → ℝ) =>
      yParts (fun j => perturbOn (abar j) ρ (ω j)) i := fun i => continuous_yPart.comp (ha i)
  have hb : ∀ i, CoeffCont fun ω : (∀ i, monos (Y ⊕ Z) (d i : ℤ) → ℝ) =>
      toPoly (bfam d D abar ρ ω i) := fun i =>
    cc_toPoly (a := fun ω => bfam d D abar ρ ω i)
      (continuous_ofPoly' (cc_pow (cc_toPoly (ha i)) _) _)
  -- the two sides of the defining inequality
  let lhs : (∀ i, monos (Y ⊕ Z) (d i : ℤ) → ℝ) → Tup (Y ⊕ Z) (fun i => (t : ℤ) - ((d i : ℤ) * (D i : ℕ))) → ℝ := fun ω h =>
    K₂ * ‖mulMap (bfam d D abar ρ ω) (t : ℤ) h‖
  let rhs : (∀ i, monos (Y ⊕ Z) (d i : ℤ) → ℝ) → Tup (Y ⊕ Z) (fun i => (t : ℤ) - ((d i : ℤ) * (D i : ℕ))) → ℝ := fun ω h =>
    ‖gVec d D t (yParts fun i => perturbOn (abar i) ρ (ω i)) (yPartTup h)‖
  have hlhs : ∀ h, Measurable fun ω => lhs ω h := fun h =>
    (continuous_const.mul (continuous_mulMap' _ hb _ h).norm).measurable
  have hrhs : ∀ h, Measurable fun ω => rhs ω h := by
    intro h
    simp only [rhs, norm_gVec]
    refine (Finset.measurable_sum _ fun i _ => ?_).sqrt
    exact (measurable_norm_J d D t i _ ha₀ _).pow_const 2
  have hcont : ∀ ω, Continuous fun h => rhs ω h - lhs ω h := fun ω =>
    ((continuous_gVec d D t _).comp continuous_yPartTup).norm.sub
      (continuous_const.mul (LinearMap.continuous_of_finiteDimensional _).norm)
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq (Tup (Y ⊕ Z) (fun i => (t : ℤ) - ((d i : ℤ) * (D i : ℕ))))
  have h3 : {ω : ∀ i, monos (Y ⊕ Z) (d i : ℤ) → ℝ | ∃ h : Tup (Y ⊕ Z) (fun i => (t : ℤ) - ((d i : ℤ) * (D i : ℕ))), lhs ω h < rhs ω h} =
      ⋃ n, {ω | lhs ω (c n) < rhs ω (c n)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨h, hh⟩
      obtain ⟨n, hn⟩ := hc.exists_mem_open ((isOpen_Ioi (a := (0 : ℝ))).preimage (hcont ω))
        ⟨h, by simp only [mem_preimage, mem_Ioi]; linarith⟩
      simp only [mem_preimage, mem_Ioi] at hn
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      exact ⟨c n, hn⟩
  have h3' : MeasurableSet {ω : ∀ i, monos (Y ⊕ Z) (d i : ℤ) → ℝ | ∃ h : Tup (Y ⊕ Z) (fun i => (t : ℤ) - ((d i : ℤ) * (D i : ℕ))), lhs ω h < rhs ω h} := by
    rw [h3]
    exact MeasurableSet.iUnion fun n => measurableSet_lt (hlhs _) (hrhs _)
  exact h1.inter (h2.inter h3')

end ApproxSyzygies.Smoothed.Dev.G41.PartM
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
/-! # Blueprint for Theorem 4.1: outer layer of the shrinking step (stubs)

The shrinking event is bounded for each fixed value `ω₀` of the coordinates outside the
`z`-blocks (`shrink_fixed`), then integrated (`fubini_blocks`). -/
alias measurableSet_shrinkBad := ApproxSyzygies.Smoothed.Dev.G41.PartM.measurableSet_shrinkBad

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial Set
namespace ApproxSyzygies.Smoothed.Dev.G41.PartM
open ApproxSyzygies.Smoothed
/-! # Part M: stubs S2 (`fubini_blocks`) and S3 (`restrictY_replaceV`) -/
/-- **Stub S3 (replacing block coordinates keeps the pure-`y` coordinates).** -/
theorem restrictY_replaceV {Y : Type} [Fintype Y] [DecidableEq Y] {L q m : ℕ}
    (d : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i)
    (ω₀ : ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i : ℤ) → ℝ)
    (u : Fin L → ∀ i, monos (Fin q) (d i : ℤ) → ℝ) :
    restrictY (replaceV ω₀ u) = restrictY ω₀ := by
  funext i β
  simp only [restrictY]
  split_ifs with h
  · simp only [replaceV]
    rw [dif_neg]
    rintro ⟨p, hp⟩
    have hβ := β.2
    simp only [monos, show (0 : ℤ) ≤ (d i : ℤ) by positivity, if_true,
      Finset.mem_finsuppAntidiag] at hβ
    obtain ⟨y, hy⟩ : ∃ y, (β : Y →₀ ℕ) y ≠ 0 := by
      by_contra hne
      push Not at hne
      have h0 := hβ.1
      rw [Finset.sum_eq_zero fun y _ => hne y] at h0
      have := hd i
      omega
    have h1 := congrArg (fun f : (Y ⊕ (Fin L × Fin q)) →₀ ℕ => f (Sum.inl y)) hp
    rw [Finsupp.mapDomain_apply Sum.inl_injective,
      Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨j, hj⟩; cases hj)] at h1
    exact hy h1.symm
  · rfl

end ApproxSyzygies.Smoothed.Dev.G41.PartM
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial Set
namespace ApproxSyzygies.Smoothed.Dev.G41.PartM
open ApproxSyzygies.Smoothed
variable {Y : Type} [Fintype Y] [DecidableEq Y] {L q m : ℕ} {d : Fin m → ℤ}
/-- The coordinates `(i, β)` that `replaceV` takes from the blocks. -/
def BCond (i : Fin m) (β : monos (Y ⊕ (Fin L × Fin q)) (d i)) : Prop :=
  ∃ h : (∃ p : Fin L × (Fin q →₀ ℕ),
      Finsupp.mapDomain (fun j => (Sum.inr (p.1, j) : Y ⊕ (Fin L × Fin q))) p.2 = β.1),
    h.choose.2 ∈ monos (Fin q) (d i)

/-- The block coordinate a block coordinate of `replaceV` is read from. -/
noncomputable def bch {i : Fin m} {β : monos (Y ⊕ (Fin L × Fin q)) (d i)} (hc : BCond i β) :
    Fin L × monos (Fin q) (d i) :=
  (hc.1.choose.1, ⟨hc.1.choose.2, hc.2⟩)

lemma bch_inj {i : Fin m} {β β' : monos (Y ⊕ (Fin L × Fin q)) (d i)} (hc : BCond i β)
    (hc' : BCond i β') (h : bch hc = bch hc') : β = β' := by
  apply Subtype.ext
  rw [← hc.1.choose_spec, ← hc'.1.choose_spec]
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun x => (x.2 : Fin q →₀ ℕ)) h
  simp only [bch] at h1 h2
  rw [h1, h2]

lemma replaceV_of_cond (ω₀ : ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i) → ℝ)
    (u : Fin L → ∀ i, monos (Fin q) (d i) → ℝ) (i : Fin m)
    (β : monos (Y ⊕ (Fin L × Fin q)) (d i)) (hc : BCond i β) :
    replaceV ω₀ u i β = u (bch hc).1 i (bch hc).2 := by
  simp only [replaceV, dif_pos hc.1, dif_pos hc.2]
  rfl

lemma replaceV_of_not (ω₀ : ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i) → ℝ)
    (u : Fin L → ∀ i, monos (Fin q) (d i) → ℝ) (i : Fin m)
    (β : monos (Y ⊕ (Fin L × Fin q)) (d i)) (hc : ¬ BCond i β) :
    replaceV ω₀ u i β = ω₀ i β := by
  simp only [replaceV]
  split_ifs with h1 h2
  · exact absurd ⟨h1, h2⟩ hc
  · rfl
  · rfl

lemma measurable_replaceV :
    Measurable (fun p : (∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i) → ℝ) ×
        (Fin L → ∀ i, monos (Fin q) (d i) → ℝ) => replaceV p.1 p.2) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun β => ?_
  by_cases hc : BCond i β
  · simp only [replaceV_of_cond _ _ i β hc]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp measurable_snd))
  · simp only [replaceV_of_not _ _ i β hc]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_fst)

/-- The per-generator product identity behind the Fubini decomposition. -/
lemma prod_split (i : Fin m) (s : monos (Y ⊕ (Fin L × Fin q)) (d i) → Set ℝ)
    (γ : Measure ℝ) [IsProbabilityMeasure γ] :
    (∏ β, γ {x | ¬ BCond i β → x ∈ s β}) *
      ∏ p : Fin L × monos (Fin q) (d i),
        γ {x | ∀ β (hc : BCond i β), bch hc = p → x ∈ s β} = ∏ β, γ (s β) := by
  classical
  have hb : ∏ p : Fin L × monos (Fin q) (d i),
        γ {x | ∀ β (hc : BCond i β), bch hc = p → x ∈ s β} =
      ∏ β, (if BCond i β then γ (s β) else 1) := by
    symm
    refine Finset.prod_bij_ne_one (fun β _ hne => bch (by
        by_contra hc; rw [if_neg hc] at hne; exact hne rfl)) (fun _ _ _ => Finset.mem_univ _)
      (fun β₁ _ _ β₂ _ _ h => bch_inj _ _ h) ?_ ?_
    · intro p _ hne
      by_contra hno
      push Not at hno
      apply hne
      have : {x | ∀ β (hc : BCond i β), bch hc = p → x ∈ s β} = univ := by
        ext x
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        intro β hc hp
        exact absurd hp (hno β (Finset.mem_univ _) (by
          rw [if_pos hc]
          intro h1
          apply hne
          have : {x | ∀ β (hc : BCond i β), bch hc = p → x ∈ s β} = s β := by
            ext x
            simp only [mem_ofPred_eq]
            constructor
            · intro hx; exact hx β hc hp
            · intro hx β' hc' hp'
              have := bch_inj hc' hc (hp'.trans hp.symm)
              subst this
              exact hx
          rw [this, h1]))
      rw [this, measure_univ]
    · intro β _ hne
      have hc : BCond i β := by by_contra hc; rw [if_neg hc] at hne; exact hne rfl
      simp only [if_pos hc]
      congr 1
      ext x
      simp only [mem_ofPred_eq]
      constructor
      · intro hx β' hc' hp'
        have := bch_inj hc' hc hp'
        subst this
        exact hx
      · intro hx; exact hx β hc rfl
  rw [hb, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun β _ => ?_
  by_cases hc : BCond i β
  · rw [if_pos hc]
    have : {x | ¬ BCond i β → x ∈ s β} = univ := by
      ext x; simp [hc]
    rw [this, measure_univ, one_mul]
  · rw [if_neg hc, mul_one]
    congr 1
    ext x; simp [hc]

instance (L q : ℕ) {m : ℕ} (d : Fin m → ℤ) : IsProbabilityMeasure (gaussV L q d) := by
  unfold gaussV; infer_instance

instance (σ : Type) [Fintype σ] [DecidableEq σ] (m : ℕ) (d : Fin m → ℤ) :
    IsProbabilityMeasure (gaussOn σ m d) := by
  unfold gaussOn; infer_instance

/-- `replaceV` pushes the product of the full Gaussian law and the block law to the full law. -/
lemma map_replaceV :
    ((gaussOn (Y ⊕ (Fin L × Fin q)) m d).prod (gaussV L q d)).map
        (fun p => replaceV p.1 p.2) = gaussOn (Y ⊕ (Fin L × Fin q)) m d := by
  symm
  refine Measure.pi_eq_generateFrom (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun i => ?_) ?_
  · exact
      { set := fun _ => univ
        set_mem := fun _ => ⟨fun _ => univ, fun _ _ => by simp, by simp⟩
        finite := fun _ => measure_lt_top _ _
        spanning := iUnion_const _ }
  intro S hS
  choose s hs hsS using hS
  simp only [mem_pi, mem_univ, forall_const, mem_ofPred_eq] at hs
  obtain rfl : S = fun i => univ.pi (s i) := funext fun i => (hsS i).symm
  have hbox : MeasurableSet (univ.pi fun i => univ.pi (s i)) :=
    MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun β => hs i β
  rw [Measure.map_apply measurable_replaceV hbox]
  have hpre : (fun p : (∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i) → ℝ) ×
        (Fin L → ∀ i, monos (Fin q) (d i) → ℝ) => replaceV p.1 p.2) ⁻¹'
        (univ.pi fun i => univ.pi (s i)) =
      (univ.pi fun i => univ.pi fun β => {x | ¬ BCond i β → x ∈ s i β}) ×ˢ
        (univ.pi fun ℓ => univ.pi fun i => univ.pi fun α =>
          {x | ∀ β (hc : BCond i β), bch hc = (ℓ, α) → x ∈ s i β}) := by
    ext ⟨ω₀, u⟩
    simp only [mem_preimage, mem_pi, mem_univ, forall_const, mem_prod, mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨fun i β hc => ?_, fun ℓ i α β hc hp => ?_⟩
      · have := h i β; rwa [replaceV_of_not _ _ i β hc] at this
      · have := h i β; rw [replaceV_of_cond _ _ i β hc, hp] at this; exact this
    · rintro ⟨h1, h2⟩ i β
      by_cases hc : BCond i β
      · rw [replaceV_of_cond _ _ i β hc]
        exact h2 _ i _ β hc rfl
      · rw [replaceV_of_not _ _ i β hc]; exact h1 i β hc
  rw [hpre, Measure.prod_prod]
  simp only [gaussOn, gaussV, Measure.pi_pi]
  rw [Finset.prod_comm]
  simp_rw [← Fintype.prod_prod_type']
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact prod_split i (s i) _

end ApproxSyzygies.Smoothed.Dev.G41.PartM
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial Set
namespace ApproxSyzygies.Smoothed.Dev.G41.PartM
open ApproxSyzygies.Smoothed
/-- **Stub S2 (Fubini over the block coordinates).** -/
theorem fubini_blocks {Y : Type} [Fintype Y] [DecidableEq Y] {L q m : ℕ} (d : Fin m → ℤ)
    (E : Set (∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i) → ℝ)) (hE : MeasurableSet E)
    (b : ENNReal) (hb : ∀ ω₀, gaussV L q d {u | replaceV ω₀ u ∈ E} ≤ b) :
    gaussOn (Y ⊕ (Fin L × Fin q)) m d E ≤ b := by
  rw [← map_replaceV, Measure.map_apply measurable_replaceV hE,
    Measure.prod_apply (measurable_replaceV hE)]
  calc ∫⁻ ω₀, gaussV L q d (Prod.mk ω₀ ⁻¹' ((fun p => replaceV p.1 p.2) ⁻¹' E))
        ∂gaussOn (Y ⊕ (Fin L × Fin q)) m d
      ≤ ∫⁻ _, b ∂gaussOn (Y ⊕ (Fin L × Fin q)) m d := lintegral_mono fun ω₀ => hb ω₀
    _ = b := by simp [gaussOn]

end ApproxSyzygies.Smoothed.Dev.G41.PartM
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias fubini_blocks := ApproxSyzygies.Smoothed.Dev.G41.PartM.fubini_blocks

alias restrictY_replaceV := ApproxSyzygies.Smoothed.Dev.G41.PartM.restrictY_replaceV

/-! # Blueprint for Theorem 4.1: the induction step `Q(s) (s < t) ⇒ Q(t)` (glue, proved) -/
lemma K_mono {n : ℕ} {C C' ρ : ℝ} (hC : 0 < C) (hCC : C ≤ C') (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (n : ℝ) ^ C * ρ ^ (-C) ≤ (n : ℝ) ^ C' * ρ ^ (-C') := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow hC.ne', Real.zero_rpow (lt_of_lt_of_le hC hCC).ne']
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn1 hCC)
      (Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)) (by positivity) (by positivity)

lemma K_mono_base {k n : ℕ} (hkn : k ≤ n) {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ) :
    (k : ℝ) ^ C * ρ ^ (-C) ≤ (n : ℝ) ^ C * ρ ^ (-C) :=
  mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkn) hC)
    (by positivity)

lemma exp_bound_mono {c c' x : ℝ} (hcc : c' ≤ c) (hx : 0 ≤ x) :
    ENNReal.ofReal (Real.exp (-(c * x))) ≤ ENNReal.ofReal (Real.exp (-(c' * x))) :=
  ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hcc hx)))

/-- Finitely many constants `(C, c, N)` can be made uniform. -/
lemma uniform_consts {ι : Type} [Fintype ι] (P : ι → ℝ → ℝ → ℕ → Prop)
    (hmono : ∀ i C C' c c' N N', 0 < C → C ≤ C' → 0 < c' → c' ≤ c → N ≤ N' →
      P i C c N → P i C' c' N')
    (h : ∀ i, ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, P i C c N) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ i, P i C c N := by
  classical
  choose C hC c hc N hN using h
  by_cases hne : Nonempty ι
  · have hCle : ∀ i, C i ≤ ∑ j, C j := fun i =>
      Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty c
    refine ⟨∑ j, C j, ?_, Finset.univ.inf' Finset.univ_nonempty c, ?_, ∑ j, N j, fun i => ?_⟩
    · obtain ⟨i⟩ := hne
      exact lt_of_lt_of_le (hC i) (hCle i)
    · rw [hi₀]; exact hc i₀
    · refine hmono i _ _ _ _ _ _ (hC i) (hCle i) (by rw [hi₀]; exact hc i₀)
        (Finset.inf'_le _ (Finset.mem_univ i))
        (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)) (hN i)
  · exact ⟨1, one_pos, 1, one_pos, 0, fun i => (hne ⟨i⟩).elim⟩

lemma degBound_mono {t : ℕ} {ε : ℝ} {dmax Dmax : ℕ} {C C' c c' : ℝ} {N N' : ℕ} (hC : 0 < C)
    (hCC : C ≤ C') (hcc : c' ≤ c) (hNN : N ≤ N') (h : DegBound t ε dmax Dmax C c N) :
    DegBound t ε dmax Dmax C' c' N' := by
  intro n hn m _ d D hd hD hsum ρ hρ hρ1 abar habar
  refine le_trans (measure_mono (badT_anti d D abar ρ (K_mono hC hCC hρ hρ1) t)) ?_
  refine le_trans (h n (hNN.trans hn) m d D hd hD hsum ρ hρ hρ1 abar habar) ?_
  exact exp_bound_mono hcc (by positivity)

lemma perDegree_uniform (t : ℕ) (IH : ∀ s < t, PerDegree s) (ε : ℝ) (hε : 0 < ε)
    (dmax Dmax : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ s : Fin t,
      DegBound (s : ℕ) ε dmax Dmax C c N₀ :=
  uniform_consts (fun (s : Fin t) C c N => DegBound (s : ℕ) ε dmax Dmax C c N)
    (fun _ _ _ _ _ _ _ hC hCC _ hcc hNN h => degBound_mono hC hCC hcc hNN h)
    (fun s => IH s s.2 ε hε dmax Dmax)

/-- `Q(0)`: the coefficient space is `0` and `0` is a Koszul syzygy. -/
theorem perDegree_zero : PerDegree 0 := by
  intro ε _ dmax Dmax
  refine ⟨1, one_pos, 1, one_pos, 0, ?_⟩
  intro n _ m _ d D hd hD _ ρ _ _ abar _
  refine le_trans (measure_mono (t := ∅) ?_) (by simp)
  rintro ω ⟨h, hh⟩
  have hempty : ∀ i, monos (Fin n) ((0 : ℕ) - ((d i : ℤ) * (D i : ℕ))) = ∅ := by
    intro i
    have hneg : ((0 : ℕ) : ℤ) - ((d i : ℤ) * (D i : ℕ)) < 0 := by
      have h1 : 1 ≤ (d i : ℤ) := by exact_mod_cast (hd i).1
      have h2 : 1 ≤ ((D i : ℕ) : ℤ) := by exact_mod_cast (hD i).1
      push_cast; nlinarith
    unfold monos
    rw [if_neg (not_le.2 hneg)]
  have h0 : h = 0 := by
    ext i α
    exact absurd α.2 (Finset.eq_empty_iff_forall_notMem.1 (hempty i) α.1)
  subst h0
  have hk : (0 : Tup (Fin n) (fun i => ((0 : ℕ) : ℤ) - ((d i : ℤ) * (D i : ℕ)))) ∈
      koszul (bfam d D abar ρ ω) ((0 : ℕ) : ℤ) := by
    refine ⟨fun _ _ => 0, fun _ _ => Submodule.zero_mem _, fun _ _ => by simp, fun i => ?_⟩
    simp only [zero_mul, Finset.sum_const_zero]
    exact (toPolyL (σ := Fin n) _).map_zero
  have := Metric.infDist_zero_of_mem hk
  rw [this, map_zero, norm_zero, mul_zero] at hh
  exact lt_irrefl _ hh

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
open MeasureTheory ProbabilityTheory
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
/-- `T e^{-c x} ≤ e^{-(c/2) x}` for `x ≥ 2T/c`. -/
lemma union_exp_arith (T : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ x : ℝ, (N : ℝ) ≤ x → (T : ℝ) * Real.exp (-(c * x)) ≤ Real.exp (-(c / 2 * x)) := by
  refine ⟨⌈2 * T / c⌉₊, fun x hx => ?_⟩
  have hx' : 2 * (T : ℝ) / c ≤ x := (Nat.le_ceil _).trans hx
  have hT : (T : ℝ) ≤ c / 2 * x := by
    rw [div_le_iff₀ hc] at hx'
    linarith
  have h1 : (T : ℝ) ≤ Real.exp (c / 2 * x) := by
    have := Real.add_one_le_exp (c / 2 * x)
    linarith
  calc (T : ℝ) * Real.exp (-(c * x)) ≤ Real.exp (c / 2 * x) * Real.exp (-(c * x)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (-(c / 2 * x)) := by rw [← Real.exp_add]; ring_nf

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Module
namespace ApproxSyzygies.Smoothed.Dev.G41.PartF
open ApproxSyzygies.Smoothed ApproxSyzygies.Smoothed.Dev.P48
variable {m L : ℕ} {ι : Fin L → Fin m → Type} [∀ ℓ i, Fintype (ι ℓ i)]
  {κ : Fin m → Type} [∀ i, Fintype (κ i)]
/-! # Theorem 4.1 Part F: stub F1 (`prop48_blocks`)

Proposition 4.8 for independent blocks of underlying variables, adapted from the proof of
`chk_proposition_4_8` (`Q428P48*.lean`): Lemma 4.7 is applied on the product space of one block
with the σ-algebras `𝓕_i = σ(u_j : j ≠ i)`, and the conditioning step becomes Fubini over the
block `ℓ` against the remaining blocks. -/
/-- The extension of `z` off the coordinate `i` by a fixed value `x₀ i` at `i`. -/
def extOff {β : Fin m → Type} (x₀ : ∀ j, β j) (i : Fin m) (z : (j : {j : Fin m // j ≠ i}) → β j) :
    ∀ j, β j :=
  fun j => if h : j = i then x₀ j else z ⟨j, h⟩

lemma measurable_extOff {β : Fin m → Type} [∀ j, MeasurableSpace (β j)] (x₀ : ∀ j, β j)
    (i : Fin m) : Measurable (extOff x₀ i) := by
  refine measurable_pi_lambda _ fun j => ?_
  unfold extOff
  rcases eq_or_ne j i with h | h
  · simp only [h, dif_pos]; exact measurable_const
  · simp only [h, dif_neg, not_false_eq_true]
    exact measurable_pi_apply (⟨j, h⟩ : {j : Fin m // j ≠ i})

lemma extOff_apply_ne {β : Fin m → Type} (x₀ : ∀ j, β j) (i : Fin m) (y : ∀ j, β j) (j : Fin m)
    (h : j ≠ i) : extOff x₀ i (fun j : {j : Fin m // j ≠ i} => y j) j = y j := by
  simp [extOff, h]

/-- One block: Lemma 4.7 on the product space of the block, for underlying variables. -/
lemma section_bound_blocks (hm : 0 < m) (kk : Fin (L + 1) → ℕ) (Q η₀ γ : ℝ)
    (bW : Fin (kk 0) → Wsp κ) (ℓ : Fin L)
    (θ₀ : ∀ ℓ, Dat ι κ (kk 0) ℓ) (hgood : Good kk Q bW ℓ.val θ₀)
    {U : Fin m → Type} [∀ i, MeasurableSpace (U i)]
    (ν : ∀ i, Measure (U i)) [∀ i, IsProbabilityMeasure (ν i)]
    (φ : ∀ i, U i → EuclideanSpace ℝ (ι ℓ i)) (hφ : ∀ i, Measurable (φ i))
    (hsa : ∀ i, SubspaceAnticonc (1 / 4) η₀ γ ((ν i).map (φ i)))
    (hdim : ∀ i, 4 ≤ Fintype.card (ι ℓ i))
    (Φ : ∀ i, Fin (kk 0) → (∀ j, U j) → EuclideanSpace ℝ (ι ℓ i × κ i))
    (hΦ : ∀ i k, Measurable (Φ i k))
    (hΦloc : ∀ i k (x x' : ∀ j, U j), (∀ j, j ≠ i → x j = x' j) → Φ i k x = Φ i k x')
    (hk : ∀ r : ℕ, r ≤ kk ℓ.castSucc →
      (r : ℝ) ≤ 2 * ∑ i, (kk ℓ.castSucc : ℝ) / (Fintype.card (ι ℓ i) : ℝ) → r ≤ kk ℓ.succ)
    (hQ : Real.sqrt (∑ i, ((Fintype.card (ι ℓ i) : ℝ)) ^ 2) / η₀ ≤ Q) :
    (Measure.pi ν)
      {y | ¬ Good kk Q bW (ℓ.val + 1)
        (Function.update θ₀ ℓ (fun i => φ i (y i), fun i k => Φ i k y))}
      ≤ ENNReal.ofReal (m * Real.exp (-γ)) := by
  classical
  have : ∀ j, Nonempty (U j) := fun j => nonempty_of_isProbabilityMeasure (ν j)
  let x₀ : ∀ j, U j := fun j => Classical.arbitrary (U j)
  obtain ⟨V, hVf, hV0, hVst⟩ := hgood
  set G : Submodule ℝ (Wsp κ) := Submodule.span ℝ (Set.range (V ℓ.castSucc)) with hGdef
  have hG : finrank ℝ G ≤ kk ℓ.castSucc := by
    have := finrank_range_le_card (R := ℝ) (V ℓ.castSucc)
    simpa [Set.finrank] using this
  set μ := Measure.pi ν with hμ
  let Cl : ∀ i, (∀ j, U j) → (G →ₗ[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i)) :=
    fun i y =>
    { toFun := fun h => ∑ k, inner ℝ (bW k) (h : Wsp κ) • Φ i k y
      map_add' := fun a b => by
        simp only [Submodule.coe_add, inner_add_right, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, inner_smul_right, mul_smul, RingHom.id_apply,
          Finset.smul_sum] }
  let C : ∀ i, (∀ j, U j) → (G →L[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i)) :=
    fun i y => LinearMap.toContinuousLinearMap (Cl i y)
  have hCapp : ∀ i y (h : G), C i y h = ∑ k, inner ℝ (bW k) (h : Wsp κ) • Φ i k y :=
    fun _ _ _ => rfl
  have hind : iIndepFun (fun i (y : ∀ j, U j) => φ i (y i)) μ :=
    iIndepFun_pi (X := φ) (fun i => (hφ i).aemeasurable)
  have hsa' : ∀ i, SubspaceAnticonc (1 / 4) η₀ γ (μ.map fun y : ∀ j, U j => φ i (y i)) := by
    intro i
    have h1 : (fun y : ∀ j, U j => φ i (y i)) = φ i ∘ (fun y : ∀ j, U j => y i) := rfl
    rw [h1, ← Measure.map_map (hφ i) (measurable_pi_apply i),
      (measurePreserving_eval ν i).map_eq]
    exact hsa i
  have h47 := lemma_4_7 (ι := ι ℓ) (κ := κ) G (kk ℓ.castSucc) hG η₀ γ μ
    (fun i y => φ i (y i)) (fun i => (hφ i).comp (measurable_pi_apply i)) hind hsa' hdim C
    (fun i => MeasurableSpace.comap
      (fun (y : ∀ j, U j) (j : {j : Fin m // j ≠ i}) => y j) inferInstance)
    (fun i => (measurable_pi_lambda _ fun j => measurable_pi_apply _).comap_le)
    (fun i g => by
      have hF : Measurable fun z : ((j : {j : Fin m // j ≠ i}) → U j) =>
          ∑ k, inner ℝ (bW k) (g : Wsp κ) • Φ i k (extOff x₀ i z) :=
        Finset.measurable_sum _ fun k _ => by
          exact ((hΦ i k).comp (measurable_extOff x₀ i)).const_smul (inner ℝ (bW k) (g : Wsp κ))
      have heq : (fun y => C i y g) = (fun z : ((j : {j : Fin m // j ≠ i}) → U j) =>
          ∑ k, inner ℝ (bW k) (g : Wsp κ) • Φ i k (extOff x₀ i z)) ∘
            (fun (y : ∀ j, U j) (j : {j : Fin m // j ≠ i}) => y j) := by
        funext y
        simp only [hCapp, Function.comp_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hΦloc i k y (extOff x₀ i fun j => y j) fun j hj => (extOff_apply_ne x₀ i y j hj).symm]
      rw [heq]
      exact hF.comp (comap_measurable _))
    (fun i => by
      refine indep_of_indep_of_le_left (indep_coord ν i) ?_
      have : (fun y : ∀ j, U j => φ i (y i)) = φ i ∘ (fun y : ∀ j, U j => y i) := rfl
      rw [this, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (hφ i).comap_le)
  refine le_trans (measure_mono ?_) h47
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy ⊢
  intro hex
  apply hy
  obtain ⟨G', hG'G, hG'dim, hG'⟩ := hex
  set r := finrank ℝ G'
  let e : Fin r → Wsp κ := fun c => ((stdOrthonormalBasis ℝ G') c : Wsp κ)
  have he : Orthonormal ℝ e := (stdOrthonormalBasis ℝ G').orthonormal.comp_linearIsometry G'.subtypeₗᵢ
  have hr : r ≤ kk ℓ.succ := by
    refine hk r ((Submodule.finrank_mono hG'G).trans hG) ?_
    exact hG'dim
  set v' : Fin (kk ℓ.succ) → Wsp κ := pad (kk ℓ.succ) e
  have hv' : IsFrame v' := isFrame_pad _ he
  have hG'sp : ∀ z ∈ G', z ∈ Submodule.span ℝ (Set.range v') := by
    intro z hz
    have hsum := congrArg Subtype.val ((stdOrthonormalBasis ℝ G').sum_repr ⟨z, hz⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    rw [← hsum]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (mem_span_pad hr e c)
  refine ⟨Function.update V ℓ.succ v', fun j => ?_, ?_, fun ℓ' hℓ' => ?_⟩
  · by_cases hj : j = ℓ.succ
    · subst hj; rw [Function.update_self]; exact hv'
    · rw [Function.update_of_ne hj]; exact hVf j
  · rw [Function.update_of_ne (Fin.succ_ne_zero ℓ).symm]; exact hV0
  · have hcs : ℓ'.castSucc ≠ ℓ.succ := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    rw [Function.update_of_ne hcs]
    rcases eq_or_ne ℓ' ℓ with rfl | hne
    · rw [Function.update_self, Function.update_self]
      intro g
      set h := proj (V ℓ'.castSucc) g
      have hmem : h ∈ G := proj_mem _ g
      obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ
        (fun i => res bW (ℓ := ℓ') ((fun i => φ i (y i), fun i k => Φ i k y) :
          Dat ι κ (kk 0) ℓ') i h)
        ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      refine ⟨i₀, ?_⟩
      set η := res bW (ℓ := ℓ') ((fun i => φ i (y i), fun i k => Φ i k y) : Dat ι κ (kk 0) ℓ')
        i₀ h
      have hη : 0 ≤ η := norm_nonneg _
      have hb := hG' η ⟨h, hmem⟩ (fun i => hi₀ i (Finset.mem_univ _))
      have h1 : ‖h - proj v' h‖ ≤ Metric.infDist h G' := by
        refine (Metric.le_infDist ⟨0, G'.zero_mem⟩).2 fun z hz => ?_
        rw [dist_eq_norm]
        exact norm_sub_proj_le hv' h (hG'sp z hz)
      refine h1.trans (hb.trans ?_)
      rw [mul_div_assoc, mul_comm Q]
      exact mul_le_mul_of_nonneg_left hQ hη
    · have hs : ℓ'.succ ≠ ℓ.succ := fun h => hne (Fin.succ_inj.1 h)
      rw [Function.update_of_ne hs, Function.update_of_ne hne]
      have hlt : ℓ'.val < ℓ.val := by
        have : ℓ'.val ≠ ℓ.val := fun h => hne (Fin.ext h)
        omega
      exact hVst ℓ' hlt

/-- One step, by Fubini over block `ℓ` against the other blocks. -/
lemma prob_step_blocks (hm : 0 < m) (kk : Fin (L + 1) → ℕ) (Q η₀ γ : ℝ)
    (bW : Fin (kk 0) → Wsp κ)
    {U : Fin L → Fin m → Type} [∀ ℓ i, MeasurableSpace (U ℓ i)]
    (ν : ∀ ℓ i, Measure (U ℓ i)) [∀ ℓ i, IsProbabilityMeasure (ν ℓ i)]
    (φ : ∀ ℓ i, U ℓ i → EuclideanSpace ℝ (ι ℓ i)) (hφ : ∀ ℓ i, Measurable (φ ℓ i))
    (C : ∀ ℓ i, (∀ j, U ℓ j) → (Wsp κ →L[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i)))
    (hCloc : ∀ ℓ i (x x' : ∀ j, U ℓ j), (∀ j, j ≠ i → x j = x' j) → C ℓ i x = C ℓ i x')
    (hCmeas : ∀ ℓ i (g : Wsp κ), Measurable fun x => C ℓ i x g) (ℓ : Fin L)
    (hsa : ∀ i, SubspaceAnticonc (1 / 4) η₀ γ ((ν ℓ i).map (φ ℓ i)))
    (hdim : ∀ i, 4 ≤ Fintype.card (ι ℓ i))
    (hk : ∀ r : ℕ, r ≤ kk ℓ.castSucc →
      (r : ℝ) ≤ 2 * ∑ i, (kk ℓ.castSucc : ℝ) / (Fintype.card (ι ℓ i) : ℝ) → r ≤ kk ℓ.succ)
    (hQ : Real.sqrt (∑ i, ((Fintype.card (ι ℓ i) : ℝ)) ^ 2) / η₀ ≤ Q) :
    (Measure.pi fun ℓ => Measure.pi fun i => ν ℓ i)
      ({u | Good kk Q bW ℓ.val (thetaB bW φ C u)} \
        {u | Good kk Q bW (ℓ.val + 1) (thetaB bW φ C u)})
      ≤ ENNReal.ofReal (m * Real.exp (-γ)) := by
  classical
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by have := ℓ.pos; omega⟩
  have : ∀ ℓ i, Nonempty (U ℓ i) := fun ℓ i => nonempty_of_isProbabilityMeasure (ν ℓ i)
  let μ : ∀ ℓ, Measure (∀ i, U ℓ i) := fun ℓ => Measure.pi (ν ℓ)
  have hmp := measurePreserving_piFinSuccAbove μ ℓ
  set e := MeasurableEquiv.piFinSuccAbove (fun ℓ => ∀ i, U ℓ i) ℓ with he
  have hθm := measurable_thetaB bW φ hφ C hCmeas
  have : ∀ ℓ', BorelSpace (Dat ι κ (kk 0) ℓ') := fun ℓ' => inferInstance
  have : ∀ ℓ', SecondCountableTopology (Dat ι κ (kk 0) ℓ') := fun ℓ' => inferInstance
  set S := thetaB bW φ C ⁻¹' ({θ | Good kk Q bW ℓ.val θ} \ {θ | Good kk Q bW (ℓ.val + 1) θ})
    with hS
  have hSm : MeasurableSet S :=
    hθm ((isClosed_good kk Q bW _).measurableSet.diff (isClosed_good kk Q bW _).measurableSet)
  have hSe : MeasurableSet (e.symm ⁻¹' S) := e.symm.measurable hSm
  have hset : {u | Good kk Q bW ℓ.val (thetaB bW φ C u)} \
      {u | Good kk Q bW (ℓ.val + 1) (thetaB bW φ C u)} = e ⁻¹' (e.symm ⁻¹' S) := by
    ext u; simp [hS]
  rw [hset, hmp.measure_preimage hSe.nullMeasurableSet, Measure.prod_apply_symm hSe]
  calc ∫⁻ r, μ ℓ ((fun b => (b, r)) ⁻¹' (e.symm ⁻¹' S))
        ∂(Measure.pi fun j => μ (ℓ.succAbove j))
      ≤ ∫⁻ _, ENNReal.ofReal (m * Real.exp (-γ)) ∂(Measure.pi fun j => μ (ℓ.succAbove j)) := by
        refine lintegral_mono fun r => ?_
        let x₀ : ∀ i, U ℓ i := fun i => Classical.arbitrary (U ℓ i)
        set θ₀ := thetaB bW φ C (e.symm (x₀, r)) with hθ₀
        have hupd : ∀ b, thetaB bW φ C (e.symm (b, r)) = Function.update θ₀ ℓ
            ((fun i => φ ℓ i (b i), fun i k => C ℓ i b (bW k)) : Dat ι κ (kk 0) ℓ) := by
          intro b; funext ℓ'
          rcases eq_or_ne ℓ' ℓ with rfl | hne
          · rw [Function.update_self]
            simp [thetaB, he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
          · rw [Function.update_of_ne hne]
            obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hne
            simp [hθ₀, thetaB, he, MeasurableEquiv.piFinSuccAbove_symm_apply,
              Fin.insertNthEquiv]
        by_cases hg : Good kk Q bW ℓ.val θ₀
        · refine le_trans (measure_mono ?_) (section_bound_blocks hm kk Q η₀ γ bW ℓ θ₀ hg
            (ν ℓ) (φ ℓ) (hφ ℓ) hsa hdim (fun i k b => C ℓ i b (bW k))
            (fun i k => hCmeas ℓ i (bW k))
            (fun i k x x' h => by simp only [hCloc ℓ i x x' h]) hk hQ)
          intro b hb
          simp only [Set.mem_preimage, hS, Set.mem_sdiff, Set.mem_ofPred_eq, hupd] at hb ⊢
          exact hb.2
        · have hemp : (fun b => (b, r)) ⁻¹' (e.symm ⁻¹' S) = ∅ := by
            ext b
            simp only [Set.mem_preimage, hS, Set.mem_sdiff, Set.mem_ofPred_eq, hupd,
              Set.mem_empty_iff_false, iff_false, not_and, not_not]
            intro hb
            refine absurd ((good_congr kk Q bW ℓ.val (θ' := θ₀) fun ℓ' h => ?_).1 hb) hg
            exact Function.update_of_ne (fun e => by rw [e] at h; omega) _ _
          rw [hemp, measure_empty]; exact zero_le
    _ = ENNReal.ofReal (m * Real.exp (-γ)) := by
        rw [lintegral_const, measure_univ, mul_one]

lemma res_thetaB_eq {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Wsp κ)) {ℓ : Fin L}
    (z : ∀ i, EuclideanSpace ℝ (ι ℓ i))
    (C : ∀ i, Wsp κ →L[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i)) (i : Fin m) (x : Wsp κ) :
    res (fun k => b k) (ℓ := ℓ) ((z, fun i k => C i (b k)) : Dat ι κ d ℓ) i x =
      ‖tens (z i) (x i) + C i x‖ := by
  have h : ∑ k, inner ℝ (b k) x • C i (b k) = C i x := by
    conv_rhs => rw [← b.sum_repr' x]
    simp [map_sum, map_smul]
  simp only [res, h]

lemma finrank_Wsp : finrank ℝ (Wsp κ) = ∑ i, Fintype.card (κ i) := by
  rw [(WithLp.linearEquiv 2 ℝ (∀ i, EuclideanSpace ℝ (κ i))).finrank_eq,
    Module.finrank_pi_fintype]
  simp

/-- **Stub F1 (Proposition 4.8 for independent blocks of underlying variables).** -/
theorem prop48_blocks {m L : ℕ} {ι : Fin L → Fin m → Type} [∀ ℓ i, Fintype (ι ℓ i)]
    {κ : Fin m → Type} [∀ i, Fintype (κ i)]
    {U : Fin L → Fin m → Type} [∀ ℓ i, MeasurableSpace (U ℓ i)]
    (ν : ∀ ℓ i, Measure (U ℓ i)) [∀ ℓ i, IsProbabilityMeasure (ν ℓ i)]
    (φ : ∀ ℓ i, U ℓ i → EuclideanSpace ℝ (ι ℓ i)) (hφ : ∀ ℓ i, Measurable (φ ℓ i))
    (η₀ γ β : ℝ)
    (hsa : ∀ ℓ i, SubspaceAnticonc (1 / 4) η₀ γ ((ν ℓ i).map (φ ℓ i)))
    (hdim : ∀ ℓ i, 4 ≤ Fintype.card (ι ℓ i))
    (C : ∀ ℓ i, (∀ j, U ℓ j) →
      ((PiLp 2 fun i => EuclideanSpace ℝ (κ i)) →L[ℝ] EuclideanSpace ℝ (ι ℓ i × κ i)))
    (hCloc : ∀ ℓ i (x x' : ∀ j, U ℓ j), (∀ j, j ≠ i → x j = x' j) → C ℓ i x = C ℓ i x')
    (hCmeas : ∀ ℓ i (g : PiLp 2 fun i => EuclideanSpace ℝ (κ i)),
      Measurable fun x => C ℓ i x g)
    (hprod : ((∑ i, Fintype.card (κ i) : ℕ) : ℝ) *
      ∏ ℓ, (2 * ∑ i, (1 : ℝ) / (Fintype.card (ι ℓ i) : ℝ)) < 1)
    (hβ1 : 1 ≤ β) :
    (Measure.pi fun ℓ => Measure.pi fun i => ν ℓ i)
      {u | (∀ ℓ i, ‖φ ℓ i (u ℓ i)‖ + ‖C ℓ i (u ℓ)‖ ≤ β) ∧
        ¬ ∀ η : ℝ, 0 ≤ η → ∀ g : PiLp 2 (fun i => EuclideanSpace ℝ (κ i)),
          (∀ ℓ i, ‖tens (φ ℓ i (u ℓ i)) (g i) + C ℓ i (u ℓ) g‖ ≤ η) →
          ∀ i, ‖g i‖ ≤ η * (1 + β * (⨆ ℓ : Fin L,
            Real.sqrt (∑ i, ((Fintype.card (ι ℓ i) : ℝ)) ^ 2) / η₀)) ^ L}
      ≤ ENNReal.ofReal (m * L * Real.exp (-γ)) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    refine le_trans (measure_mono (t := ∅) ?_) (by simp)
    intro u hu
    exact hu.2 (fun η _ g _ i => i.elim0)
  set P := Measure.pi fun ℓ => Measure.pi fun i => ν ℓ i with hP
  set NG := ∑ i, Fintype.card (κ i) with hNG
  set d := Module.finrank ℝ (Wsp κ) with hd
  have hG : d ≤ NG := by rw [hd, finrank_Wsp]
  set n : ℕ → Fin m → ℕ := fun j i => if h : j < L then Fintype.card (ι ⟨j, h⟩ i) else 1 with hn
  set kk : Fin (L + 1) → ℕ := fun j => kseq d n j.val with hkk
  have hkk0 : kk 0 = d := by simp [hkk, kseq]
  let bGb : OrthonormalBasis (Fin (kk 0)) ℝ (Wsp κ) :=
    (stdOrthonormalBasis ℝ (Wsp κ)).reindex (finCongr hkk0.symm)
  set bW : Fin (kk 0) → Wsp κ := fun k => bGb k with hbW
  have hbWf : IsFrame bW := isFrame_of_orthonormal bGb.orthonormal
  set Q := ⨆ ℓ : Fin L, Real.sqrt (∑ i, ((Fintype.card (ι ℓ i) : ℝ)) ^ 2) / η₀ with hQ
  have hQle : ∀ ℓ : Fin L, Real.sqrt (∑ i, ((Fintype.card (ι ℓ i) : ℝ)) ^ 2) / η₀ ≤ Q := by
    intro ℓ
    rw [hQ]
    exact le_ciSup (f := fun ℓ : Fin L => Real.sqrt (∑ i, ((Fintype.card (ι ℓ i) : ℝ)) ^ 2) / η₀)
      (Set.finite_range _).bddAbove ℓ
  have hQ0 : 0 ≤ Q := by
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL; simp [hQ]
    · have hη₀ := (hsa ⟨0, hL⟩ ⟨0, hm⟩).2.1
      exact (div_nonneg (Real.sqrt_nonneg _) hη₀.le).trans (hQle ⟨0, hL⟩)
  have hnℓ : ∀ ℓ : Fin L, ∀ i, n ℓ.val i = Fintype.card (ι ℓ i) := fun ℓ i => by simp [hn, ℓ.2]
  have hk : ∀ ℓ : Fin L, ∀ r : ℕ, r ≤ kk ℓ.castSucc →
      (r : ℝ) ≤ 2 * ∑ i, (kk ℓ.castSucc : ℝ) / (Fintype.card (ι ℓ i) : ℝ) → r ≤ kk ℓ.succ := by
    intro ℓ r h1 h2
    show r ≤ kseq d n (ℓ.val + 1)
    simp only [kseq]
    refine le_min h1 (Nat.le_floor ?_)
    simp only [hnℓ]
    exact h2
  have hlast : kk (Fin.last L) = 0 := by
    have h1 := kseq_le d n L
    have hp : ∏ t ∈ Finset.range L, (2 * ∑ i, (1 : ℝ) / (n t i : ℝ)) =
        ∏ ℓ : Fin L, (2 * ∑ i, (1 : ℝ) / (Fintype.card (ι ℓ i) : ℝ)) := by
      rw [← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun ℓ _ => ?_
      simp only [hnℓ]
    have hnn : 0 ≤ ∏ ℓ : Fin L, (2 * ∑ i, (1 : ℝ) / (Fintype.card (ι ℓ i) : ℝ)) :=
      Finset.prod_nonneg fun _ _ => by positivity
    have : (kseq d n L : ℝ) < 1 := by
      calc (kseq d n L : ℝ) ≤ d * ∏ ℓ : Fin L, (2 * ∑ i, (1 : ℝ) / (Fintype.card (ι ℓ i) : ℝ)) := by
            rw [← hp]; exact h1
        _ ≤ NG * ∏ ℓ : Fin L, (2 * ∑ i, (1 : ℝ) / (Fintype.card (ι ℓ i) : ℝ)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hG) hnn
        _ < 1 := hprod
    show kseq d n L = 0
    exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)
  set θ := thetaB bW φ C with hθ
  have hstep : ∀ ℓ : Fin L, P ({u | Good kk Q bW ℓ.val (θ u)} \
      {u | Good kk Q bW (ℓ.val + 1) (θ u)}) ≤ ENNReal.ofReal (m * Real.exp (-γ)) :=
    fun ℓ => prob_step_blocks hm kk Q η₀ γ bW ν φ hφ C hCloc hCmeas ℓ (hsa ℓ) (hdim ℓ) (hk ℓ)
      (hQle ℓ)
  have hA : ∀ j : ℕ, j ≤ L → P {u | ¬ Good kk Q bW j (θ u)} ≤
      j * ENNReal.ofReal (m * Real.exp (-γ)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp [good_zero kk Q bW hbWf]
    | succ j ih =>
      intro hj
      calc P {u | ¬ Good kk Q bW (j + 1) (θ u)}
          ≤ P ({u | ¬ Good kk Q bW j (θ u)} ∪ ({u | Good kk Q bW j (θ u)} \
              {u | Good kk Q bW (j + 1) (θ u)})) := by
            refine measure_mono fun u h => ?_
            by_cases hg : Good kk Q bW j (θ u)
            · exact Or.inr ⟨hg, h⟩
            · exact Or.inl hg
        _ ≤ P {u | ¬ Good kk Q bW j (θ u)} + P ({u | Good kk Q bW j (θ u)} \
              {u | Good kk Q bW (j + 1) (θ u)}) := measure_union_le _ _
        _ ≤ j * ENNReal.ofReal (m * Real.exp (-γ)) + ENNReal.ofReal (m * Real.exp (-γ)) :=
            add_le_add (ih (by omega)) (hstep ⟨j, by omega⟩)
        _ = (j + 1 : ℕ) * ENNReal.ofReal (m * Real.exp (-γ)) := by push_cast; ring
  refine le_trans (measure_mono (t := {u | ¬ Good kk Q bW L (θ u)}) ?_) ?_
  · intro u hu
    obtain ⟨hβu, hu⟩ := hu
    simp only [Set.mem_ofPred_eq]
    rintro ⟨V, -, hV0, hVst⟩
    apply hu
    intro η hη g hres i
    have hit := iterate (θ := θ u) (Q := Q) (β := β) (η := η) hQ0 (by linarith) V hV0
      (fun ℓ => hVst ℓ ℓ.2) hlast g (by simpa [proj] using bGb.sum_repr' g)
      (fun ℓ i => by
        have := res_thetaB_eq bGb (fun i => φ ℓ i (u ℓ i)) (C ℓ · (u ℓ)) i g
        exact (le_of_eq this).trans (hres ℓ i))
      (fun ℓ i x => by
        have e1 := res_thetaB_eq bGb (fun i => φ ℓ i (u ℓ i)) (C ℓ · (u ℓ)) i x
        have e2 := res_thetaB_eq bGb (fun i => φ ℓ i (u ℓ i)) (C ℓ · (u ℓ)) i g
        change res bW (θ u ℓ) i x = _ at e1
        change res bW (θ u ℓ) i g = _ at e2
        rw [e1, e2]
        have hd : tens (φ ℓ i (u ℓ i)) (x i) + C ℓ i (u ℓ) x -
            (tens (φ ℓ i (u ℓ i)) (g i) + C ℓ i (u ℓ) g) =
            tens (φ ℓ i (u ℓ i)) ((x - g) i) + C ℓ i (u ℓ) (x - g) := by
          rw [map_sub, PiLp.sub_apply, ← tens_sub]; abel
        have h1 := norm_sub_norm_le (tens (φ ℓ i (u ℓ i)) (x i) + C ℓ i (u ℓ) x)
          (tens (φ ℓ i (u ℓ i)) (g i) + C ℓ i (u ℓ) g)
        rw [hd] at h1
        have h2 : ‖tens (φ ℓ i (u ℓ i)) ((x - g) i) + C ℓ i (u ℓ) (x - g)‖ ≤
            (‖φ ℓ i (u ℓ i)‖ + ‖C ℓ i (u ℓ)‖) * ‖x - g‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_tens, add_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ _) (norm_nonneg _))
            ((C ℓ i (u ℓ)).le_opNorm _)
        have h3 := mul_le_mul_of_nonneg_right (hβu ℓ i) (norm_nonneg (x - g))
        linarith)
    have h1 := PiLp.norm_apply_le g i
    have h2 : ‖g‖ ≤ β * ‖g‖ := le_mul_of_one_le_left (norm_nonneg _) hβ1
    linarith
  · calc P {u | ¬ Good kk Q bW L (θ u)}
        ≤ L * ENNReal.ofReal (m * Real.exp (-γ)) := hA L le_rfl
      _ = ENNReal.ofReal (m * L * Real.exp (-γ)) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1; ring

end ApproxSyzygies.Smoothed.Dev.G41.PartF
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
/-! # Blueprint for Theorem 4.1: the ingredients of `shrink_fixed` (stubs)

`shrink_fixed` (in `Q428G41BPShrinkFix.lean`) is to be assembled from these statements, as
described in `BLUEPRINT-G41.md` (section "Assembly of shrink_fixed"). -/
alias prop48_blocks := ApproxSyzygies.Smoothed.Dev.G41.PartF.prop48_blocks

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartN
open ApproxSyzygies.Smoothed
variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
/-! # Theorem 4.1 Part N: stub F4 (restriction to a block), helper lemmas -/
/-! ### Generic: injective renamings of multi-indices -/
lemma mfact_eq_prod (α : σ →₀ ℕ) : mfact α = α.prod (fun _ k => ((k.factorial : ℕ) : ℝ)) := by
  rw [Finsupp.prod_fintype _ _ (by simp)]; rfl

lemma mfact_pos (α : σ →₀ ℕ) : 0 < mfact α :=
  Finset.prod_pos fun _ _ => by positivity

lemma mfact_mapDomain {f : σ → τ} (hf : Function.Injective f) (α : σ →₀ ℕ) :
    mfact (Finsupp.mapDomain f α) = mfact α := by
  rw [mfact_eq_prod, mfact_eq_prod, Finsupp.prod_mapDomain_index_inj hf]

lemma deg_mapDomain {f : σ → τ} (hf : Function.Injective f) (α : σ →₀ ℕ) :
    Dev.L43.deg (Finsupp.mapDomain f α) = Dev.L43.deg α := by
  unfold Dev.L43.deg
  rw [← Finsupp.sum_fintype _ (fun _ k => k) (by simp),
    ← Finsupp.sum_fintype _ (fun _ k => k) (by simp), Finsupp.sum_mapDomain_index_inj hf]

lemma mapDomain_mem_monos {f : σ → τ} (hf : Function.Injective f) (α : σ →₀ ℕ) (e : ℤ) :
    Finsupp.mapDomain f α ∈ monos τ e ↔ α ∈ monos σ e := by
  rw [Dev.L43.mem_monos_iff, Dev.L43.mem_monos_iff, deg_mapDomain hf]

lemma sqrt_cancel (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a / b) * Real.sqrt (b / a) = 1 := by
  rw [← Real.sqrt_mul (by positivity), div_mul_div_comm, mul_comm a b,
    div_self (by positivity), Real.sqrt_one]

lemma coeff_killCompl {f : σ → τ} (hf : Function.Injective f) (F : MvPolynomial τ ℝ)
    (γ : σ →₀ ℕ) : coeff γ (killCompl hf F) = coeff (Finsupp.mapDomain f γ) F := by
  induction F using MvPolynomial.induction_on' with
  | monomial s c =>
    by_cases hs : (↑s.support : Set τ) ⊆ Set.range f
    · obtain ⟨s', rfl⟩ : ∃ s', Finsupp.mapDomain f s' = s :=
        ⟨_, Finsupp.mapDomain_comapDomain f hf s hs⟩
      rw [killCompl_monomial_mapDomain, coeff_monomial, coeff_monomial]
      simp only [(Finsupp.mapDomain_injective hf).eq_iff]
    · rw [killCompl_monomial_eq_zero_of_not_subset hf c hs, coeff_zero, coeff_monomial, if_neg]
      rintro rfl
      apply hs
      intro x hx
      by_contra hx'
      exact (Finsupp.mem_support_iff.1 hx) (Finsupp.mapDomain_of_notMem_range _ _ hx')
  | add p q hp hq => simp [hp, hq]

lemma isH_killCompl {f : σ → τ} (hf : Function.Injective f) {e : ℤ} {F : MvPolynomial τ ℝ}
    (hF : Dev.L43.IsH e F) : Dev.L43.IsH e (killCompl hf F) := by
  intro γ hγ
  rw [coeff_killCompl] at hγ
  rw [← deg_mapDomain hf]
  exact hF _ hγ

/-- Coordinates of `ofPoly e (killCompl F)`, `F = toPoly p`. -/
lemma ofPoly_killCompl_apply {f : σ → τ} (hf : Function.Injective f) {e : ℤ} (p : Hom τ e)
    (γ : σ →₀ ℕ) (hγ : γ ∈ monos σ e) :
    (ofPoly e (killCompl hf (toPoly p)) : Hom σ e) ⟨γ, hγ⟩ =
      p ⟨Finsupp.mapDomain f γ, (mapDomain_mem_monos hf γ e).2 hγ⟩ := by
  simp only [ofPoly, PiLp.toLp_apply]
  rw [coeff_killCompl, Dev.L43.coeff_toPoly', dif_pos ((mapDomain_mem_monos hf γ e).2 hγ),
    mfact_mapDomain hf, mul_assoc, sqrt_cancel _ _ (by positivity) (mfact_pos γ), mul_one]

/-- Coordinates of `ofPoly e (rename f (toPoly v))` at a renamed multi-index. -/
lemma ofPoly_rename_apply {f : σ → τ} (hf : Function.Injective f) {e : ℤ} (v : Hom σ e)
    (α : σ →₀ ℕ) (hα : α ∈ monos σ e) (h : Finsupp.mapDomain f α ∈ monos τ e) :
    (ofPoly e (rename f (toPoly v)) : Hom τ e) ⟨Finsupp.mapDomain f α, h⟩ = v ⟨α, hα⟩ := by
  simp only [ofPoly, PiLp.toLp_apply]
  rw [coeff_rename_mapDomain f hf, Dev.L43.coeff_toPoly', dif_pos hα,
    mfact_mapDomain hf, mul_assoc, sqrt_cancel _ _ (by positivity) (mfact_pos α), mul_one]

/-- Coordinates of `ofPoly e (rename f (toPoly v))` off the renamed multi-indices. -/
lemma ofPoly_rename_apply_of_not {f : σ → τ} {e : ℤ} (v : Hom σ e) (γ : monos τ e)
    (hγ : ∀ α : σ →₀ ℕ, Finsupp.mapDomain f α ≠ γ.1) :
    (ofPoly e (rename f (toPoly v)) : Hom τ e) γ = 0 := by
  simp only [ofPoly, PiLp.toLp_apply]
  rw [coeff_rename_eq_zero f _ _ (fun u hu => absurd hu (hγ u)), zero_mul]

/-- A coordinatewise dominated injective pullback has smaller norm. -/
lemma norm_le_of_coord {ι κ : Type} [Fintype ι] [Fintype κ] (x : EuclideanSpace ℝ ι)
    (y : EuclideanSpace ℝ κ) (g : ι → κ) (hg : Function.Injective g)
    (h : ∀ i, |x i| ≤ |y (g i)|) : ‖x‖ ≤ ‖y‖ := by
  classical
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, ‖y (g i)‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = ∑ k ∈ Finset.univ.image g, ‖y k‖ ^ 2 := by
        rw [Finset.sum_image fun a _ b _ hab => hg hab]
    _ ≤ ∑ k, ‖y k‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity

end ApproxSyzygies.Smoothed.Dev.G41.PartN
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartN
open ApproxSyzygies.Smoothed
variable {Y : Type} [Fintype Y] [DecidableEq Y] {L q : ℕ}
/-! ### The block restriction -/
/-- The embedding `Y ⊕ Fin q → Y ⊕ (Fin L × Fin q)` of block `ℓ`. -/
def iota (ℓ : Fin L) : Y ⊕ Fin q → Y ⊕ (Fin L × Fin q) :=
  Sum.elim Sum.inl (fun j => Sum.inr (ℓ, j))

lemma iota_injective (ℓ : Fin L) : Function.Injective (iota (Y := Y) (q := q) ℓ) := by
  rintro (a | a) (b | b) h <;> simp_all [iota]

/-- The block-`ℓ` monomial embedding `Fin q → Y ⊕ (Fin L × Fin q)`. -/
def blk (ℓ : Fin L) : Fin q → Y ⊕ (Fin L × Fin q) := fun j => Sum.inr (ℓ, j)

lemma blk_injective (ℓ : Fin L) : Function.Injective (blk (Y := Y) (q := q) ℓ) := by
  intro a b h; simpa [blk] using h

/-- Block monomials of nonzero multi-indices determine their block and multi-index. -/
lemma blk_unique (p : Fin L × (Fin q →₀ ℕ)) (ℓ : Fin L) (α : Fin q →₀ ℕ) (hα : α ≠ 0)
    (hp : Finsupp.mapDomain (fun j => (Sum.inr (p.1, j) : Y ⊕ (Fin L × Fin q))) p.2 =
      Finsupp.mapDomain (blk ℓ) α) : p = (ℓ, α) := by
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 hα
  have h1 := congrArg (fun f => f (blk (Y := Y) ℓ j)) hp
  simp only [Finsupp.mapDomain_apply (blk_injective ℓ)] at h1
  have hl : p.1 = ℓ := by
    by_contra hne
    rw [Finsupp.mapDomain_of_notMem_range] at h1
    · exact hj h1.symm
    · rintro ⟨k, hk⟩
      simp [blk] at hk
      exact hne hk.1
  obtain ⟨p1, p2⟩ := p
  simp only at hl hp
  subst hl
  rw [Prod.mk.injEq]
  exact ⟨rfl, Finsupp.mapDomain_injective (blk_injective (Y := Y) p1) hp⟩

/-- `replaceV` at a block monomial reads `u`. -/
lemma replaceV_blk {m : ℕ} {d : Fin m → ℤ} (ω₀ : ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i) → ℝ)
    (u : Fin L → ∀ i, monos (Fin q) (d i) → ℝ) (i : Fin m) (hd : 1 ≤ d i) (ℓ : Fin L)
    (α : Fin q →₀ ℕ) (hα : α ∈ monos (Fin q) (d i))
    (h : Finsupp.mapDomain (blk ℓ) α ∈ monos (Y ⊕ (Fin L × Fin q)) (d i)) :
    replaceV ω₀ u i ⟨_, h⟩ = u ℓ i ⟨α, hα⟩ := by
  unfold replaceV
  have hex : ∃ p : Fin L × (Fin q →₀ ℕ),
      Finsupp.mapDomain (fun j => (Sum.inr (p.1, j) : Y ⊕ (Fin L × Fin q))) p.2 =
        Finsupp.mapDomain (blk ℓ) α := ⟨(ℓ, α), rfl⟩
  rw [dif_pos hex]
  have key : hex.choose = (ℓ, α) := blk_unique _ ℓ α (ne_zero_of_mem_monos hd hα) hex.choose_spec
  split_ifs with h2
  · revert h2
    rw [key]
    intro h2
    rfl
  · exact absurd (key ▸ hα) h2

/-- `replaceV` off the block monomials reads `ω₀`. -/
lemma replaceV_of_not {m : ℕ} {d : Fin m → ℤ} (ω₀ : ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i) → ℝ)
    (u : Fin L → ∀ i, monos (Fin q) (d i) → ℝ) (i : Fin m) (β : monos (Y ⊕ (Fin L × Fin q)) (d i))
    (hβ : ∀ p : Fin L × (Fin q →₀ ℕ),
      Finsupp.mapDomain (fun j => (Sum.inr (p.1, j) : Y ⊕ (Fin L × Fin q))) p.2 ≠ β.1) :
    replaceV ω₀ u i β = ω₀ i β := by
  unfold replaceV
  rw [dif_neg]
  rintro ⟨p, hp⟩
  exact hβ p hp

/-- Setting the block coordinates to `0` decreases every coordinate in absolute value. -/
lemma abs_replaceV_zero_le {m : ℕ} {d : Fin m → ℤ}
    (ω₀ : ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i) → ℝ) (u : Fin L → ∀ i, monos (Fin q) (d i) → ℝ)
    (i : Fin m) (β : monos (Y ⊕ (Fin L × Fin q)) (d i)) :
    |replaceV ω₀ (fun _ _ _ => 0) i β| ≤ |replaceV ω₀ u i β| := by
  unfold replaceV
  split_ifs <;> simp

end ApproxSyzygies.Smoothed.Dev.G41.PartN
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartN
open ApproxSyzygies.Smoothed
variable {Y : Type} [Fintype Y] [DecidableEq Y] {L q m : ℕ}
/-- The block vector `u ℓ i` is a subvector of `replaceV ω₀ u i`. -/
lemma norm_u_le (d : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i)
    (ω₀ : ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i : ℤ) → ℝ)
    (u : Fin L → ∀ i, monos (Fin q) (d i : ℤ) → ℝ) (ℓ : Fin L) (i : Fin m) :
    ‖(WithLp.toLp 2 (u ℓ i) : Hom (Fin q) (d i : ℤ))‖ ≤
      ‖(WithLp.toLp 2 (replaceV ω₀ u i) : Hom (Y ⊕ (Fin L × Fin q)) (d i : ℤ))‖ := by
  have hdi : (1 : ℤ) ≤ (d i : ℤ) := by exact_mod_cast hd i
  refine norm_le_of_coord _ _ (fun α : monos (Fin q) (d i : ℤ) =>
      (⟨Finsupp.mapDomain (blk (Y := Y) ℓ) α.1,
        (mapDomain_mem_monos (blk_injective ℓ) α.1 _).2 α.2⟩ :
          monos (Y ⊕ (Fin L × Fin q)) (d i : ℤ))) ?_ fun α => ?_
  · intro a b h
    exact Subtype.ext (Finsupp.mapDomain_injective (blk_injective ℓ) (congrArg Subtype.val h))
  · simp only [PiLp.toLp_apply]
    rw [replaceV_blk ω₀ u i hdi ℓ α.1 α.2]

lemma norm_replaceV_zero_le (d : Fin m → ℕ)
    (ω₀ : ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i : ℤ) → ℝ)
    (u : Fin L → ∀ i, monos (Fin q) (d i : ℤ) → ℝ) (i : Fin m) :
    ‖(WithLp.toLp 2 (replaceV ω₀ (fun _ _ _ => 0) i) : Hom (Y ⊕ (Fin L × Fin q)) (d i : ℤ))‖ ≤
      ‖(WithLp.toLp 2 (replaceV ω₀ u i) : Hom (Y ⊕ (Fin L × Fin q)) (d i : ℤ))‖ :=
  norm_le_of_coord _ _ id Function.injective_id fun β => by
    simp only [PiLp.toLp_apply, id]
    exact abs_replaceV_zero_le ω₀ u i β

end ApproxSyzygies.Smoothed.Dev.G41.PartN
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartN
open ApproxSyzygies.Smoothed
variable {Y : Type} [Fintype Y] [DecidableEq Y] {L q : ℕ}
lemma aeval_restr_eq (ℓ : Fin L) :
    (aeval (Sum.elim (fun y => (X (Sum.inl y) : MvPolynomial (Y ⊕ Fin q) ℝ))
      (fun z : Fin L × Fin q => if z.1 = ℓ then X (Sum.inr z.2) else 0)) :
        MvPolynomial (Y ⊕ (Fin L × Fin q)) ℝ →ₐ[ℝ] MvPolynomial (Y ⊕ Fin q) ℝ) =
      killCompl (iota_injective ℓ) := by
  apply MvPolynomial.algHom_ext
  rintro (y | ⟨ℓ', j⟩)
  · rw [aeval_X, killCompl, aeval_X]
    simp only [Sum.elim_inl]
    split_ifs with hh
    · congr 1
      apply (iota_injective (Y := Y) (q := q) ℓ)
      exact (Equiv.apply_ofInjective_symm (iota_injective _) ⟨_, hh⟩).symm
    · exact absurd ⟨Sum.inl y, rfl⟩ hh
  · rw [aeval_X, killCompl, aeval_X]
    simp only [Sum.elim_inr]
    by_cases h : ℓ' = ℓ
    · subst h
      rw [if_pos rfl]
      split_ifs with hh
      · congr 1
        apply (iota_injective (Y := Y) (q := q) ℓ')
        exact (Equiv.apply_ofInjective_symm (iota_injective _) ⟨_, hh⟩).symm
      · exact absurd ⟨Sum.inr j, rfl⟩ hh
    · rw [if_neg h]
      split_ifs with hh
      · exfalso
        obtain ⟨w, hw⟩ := hh
        rcases w with w | w <;> simp [iota] at hw
        exact h hw.1.symm
      · rfl

lemma restr_eq (ℓ : Fin L) {e : ℤ} (p : Hom (Y ⊕ (Fin L × Fin q)) e) :
    restr ℓ p = ofPoly e (killCompl (iota_injective ℓ) (toPoly p)) := by
  unfold restr; rw [aeval_restr_eq]

lemma toPoly_restr (ℓ : Fin L) {e : ℤ} (p : Hom (Y ⊕ (Fin L × Fin q)) e) :
    toPoly (restr ℓ p) = killCompl (iota_injective ℓ) (toPoly p) := by
  rw [restr_eq, Dev.L43.toPoly_ofPoly]
  exact isH_killCompl _ (Dev.L43.IsH_toPoly p)

lemma restr_apply (ℓ : Fin L) {e : ℤ} (p : Hom (Y ⊕ (Fin L × Fin q)) e) (γ : monos (Y ⊕ Fin q) e) :
    restr ℓ p γ = p ⟨Finsupp.mapDomain (iota ℓ) γ.1,
      (mapDomain_mem_monos (iota_injective ℓ) γ.1 e).2 γ.2⟩ := by
  rw [restr_eq]
  exact ofPoly_killCompl_apply (iota_injective ℓ) p γ.1 γ.2

/-- Item 1: the block coordinates enter additively through `liftZ`. -/
lemma restr_perturbOn_replaceV {m : ℕ} (ℓ : Fin L) (d : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i)
    (abar : ∀ i, Hom (Y ⊕ (Fin L × Fin q)) (d i : ℤ)) (ρ : ℝ)
    (ω₀ : ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i : ℤ) → ℝ)
    (u : Fin L → ∀ i, monos (Fin q) (d i : ℤ) → ℝ) (i : Fin m) :
    restr ℓ (perturbOn (abar i) ρ (replaceV ω₀ u i)) =
      restr ℓ (perturbOn (abar i) ρ (replaceV ω₀ (fun _ _ _ => 0) i)) +
        liftZ (ρ • (WithLp.toLp 2 (u ℓ i) : Hom (Fin q) (d i : ℤ))) := by
  have hdi : (1 : ℤ) ≤ (d i : ℤ) := by exact_mod_cast hd i
  ext γ
  rw [PiLp.add_apply, restr_apply, restr_apply]
  simp only [perturbOn, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases hA : (↑γ.1.support : Set (Y ⊕ Fin q)) ⊆ Set.range Sum.inr
  · -- `γ = mapDomain inr α`: a block monomial after `iota ℓ`
    set α : Fin q →₀ ℕ := Finsupp.comapDomain Sum.inr γ.1 Sum.inr_injective.injOn with hαdef
    have hγ : Finsupp.mapDomain Sum.inr α = γ.1 :=
      Finsupp.mapDomain_comapDomain _ Sum.inr_injective _ hA
    have hαm : α ∈ monos (Fin q) (d i : ℤ) := by
      rw [← mapDomain_mem_monos (Sum.inr_injective (α := Y)), hγ]; exact γ.2
    have hiota : Finsupp.mapDomain (iota ℓ) γ.1 = Finsupp.mapDomain (blk (Y := Y) ℓ) α := by
      rw [← hγ, ← Finsupp.mapDomain_comp]; rfl
    have hmem : Finsupp.mapDomain (blk (Y := Y) ℓ) α ∈ monos (Y ⊕ (Fin L × Fin q)) (d i : ℤ) := by
      rw [← hiota]; exact (mapDomain_mem_monos (iota_injective ℓ) γ.1 _).2 γ.2
    have e1 : (⟨Finsupp.mapDomain (iota ℓ) γ.1,
        (mapDomain_mem_monos (iota_injective ℓ) γ.1 _).2 γ.2⟩ :
          monos (Y ⊕ (Fin L × Fin q)) (d i : ℤ)) = ⟨_, hmem⟩ := Subtype.ext hiota
    have e2 : γ = ⟨Finsupp.mapDomain Sum.inr α,
        (mapDomain_mem_monos Sum.inr_injective α _).2 hαm⟩ := Subtype.ext hγ.symm
    rw [e1, replaceV_blk ω₀ u i hdi ℓ α hαm hmem, replaceV_blk ω₀ (fun _ _ _ => 0) i hdi ℓ α hαm hmem]
    unfold liftZ
    rw [e2, ofPoly_rename_apply Sum.inr_injective _ α hαm]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  · -- `γ` has a `y`-variable: not a block monomial, and `liftZ` vanishes there
    obtain ⟨x, hx, hxr⟩ := Set.not_subset.1 hA
    rcases x with y | j
    swap
    · exact absurd ⟨j, rfl⟩ hxr
    have hy : γ.1 (Sum.inl y) ≠ 0 := Finsupp.mem_support_iff.1 hx
    have hnot : ∀ p : Fin L × (Fin q →₀ ℕ),
        Finsupp.mapDomain (fun j => (Sum.inr (p.1, j) : Y ⊕ (Fin L × Fin q))) p.2 ≠
          Finsupp.mapDomain (iota ℓ) γ.1 := by
      intro p hp
      have h1 := congrArg (fun f => f (iota (Y := Y) (q := q) ℓ (Sum.inl y))) hp
      simp only [Finsupp.mapDomain_apply (iota_injective ℓ)] at h1
      rw [Finsupp.mapDomain_of_notMem_range] at h1
      · exact hy h1.symm
      · rintro ⟨k, hk⟩
        simp [iota] at hk
    rw [replaceV_of_not _ _ _ _ hnot, replaceV_of_not _ _ _ _ hnot]
    unfold liftZ
    rw [ofPoly_rename_apply_of_not]
    · ring
    · intro α hα
      have h1 := congrArg (fun f => f (Sum.inl y : Y ⊕ Fin q)) hα
      rw [Finsupp.mapDomain_of_notMem_range] at h1
      · exact hy h1.symm
      · rintro ⟨k, hk⟩
        simp at hk

/-- Item 3: `restr` is a contraction. -/
lemma norm_restr_le (ℓ : Fin L) {e : ℤ} (p : Hom (Y ⊕ (Fin L × Fin q)) e) :
    ‖restr ℓ p‖ ≤ ‖p‖ := by
  refine norm_le_of_coord _ _ (fun γ : monos (Y ⊕ Fin q) e => (⟨Finsupp.mapDomain (iota ℓ) γ.1,
      (mapDomain_mem_monos (iota_injective ℓ) γ.1 e).2 γ.2⟩ : monos (Y ⊕ (Fin L × Fin q)) e))
    ?_ fun γ => ?_
  · intro a b h
    exact Subtype.ext (Finsupp.mapDomain_injective (iota_injective ℓ) (congrArg Subtype.val h))
  · rw [restr_apply]

end ApproxSyzygies.Smoothed.Dev.G41.PartN
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartN
open ApproxSyzygies.Smoothed
theorem norm_blocks_le {Y : Type} [Fintype Y] [DecidableEq Y] {L q m : ℕ} (dmax Dmax : ℕ)
    (d D : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i ∧ d i ≤ dmax) (hD : ∀ i, 1 ≤ D i ∧ D i ≤ Dmax)
    (abar : ∀ i, Hom (Y ⊕ (Fin L × Fin q)) (d i : ℤ)) (habar : ∀ i, ‖abar i‖ ≤ 1) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (ω₀ : ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i : ℤ) → ℝ)
    (u : Fin L → ∀ i, monos (Fin q) (d i : ℤ) → ℝ) (hN : Ngood d (replaceV ω₀ u)) (ℓ : Fin L)
    (i : Fin m) :
    ‖powHom (ρ • (WithLp.toLp 2 (u ℓ i) : Hom (Fin q) (d i : ℤ))) (D i)‖ ≤
        (1 + 2 * Real.sqrt (((Fintype.card (Y ⊕ (Fin L × Fin q)) + 1 : ℕ) : ℝ) ^ dmax)) ^ Dmax ∧
      tupNorm (modGen d D i
          (toPoly (restr ℓ (perturbOn (abar i) ρ (replaceV ω₀ (fun _ _ _ => 0) i))))
          (fun j => restr ℓ (perturbOn (abar j) ρ (replaceV ω₀ u j)))) ≤
        (m : ℝ) * (1 + 2 * Real.sqrt (((Fintype.card (Y ⊕ (Fin L × Fin q)) + 1 : ℕ) : ℝ) ^
          dmax)) ^ Dmax +
          2 * (1 + 2 * Real.sqrt (((Fintype.card (Y ⊕ (Fin L × Fin q)) + 1 : ℕ) : ℝ) ^ dmax)) := by
  set σ := Y ⊕ (Fin L × Fin q)
  set A : ℝ := 1 + 2 * Real.sqrt (((Fintype.card σ + 1 : ℕ) : ℝ) ^ dmax) with hA
  have hS0 : 0 ≤ Real.sqrt (((Fintype.card σ + 1 : ℕ) : ℝ) ^ dmax) := Real.sqrt_nonneg _
  have hA1 : 1 ≤ A := by linarith
  -- the Gaussian vectors are bounded by `2 √((|σ|+1)^dmax)`
  have hω : ∀ j, ‖(WithLp.toLp 2 (replaceV ω₀ u j) : Hom σ (d j : ℤ))‖ ≤
      2 * Real.sqrt (((Fintype.card σ + 1 : ℕ) : ℝ) ^ dmax) := by
    intro j
    have hc : ((monos σ (d j : ℤ)).card : ℝ) ≤ ((Fintype.card σ + 1 : ℕ) : ℝ) ^ dmax := by
      have h1 := PartD.card_monos_le (σ := σ) (d j)
      have h2 : (Fintype.card σ + 1) ^ d j ≤ (Fintype.card σ + 1) ^ dmax :=
        Nat.pow_le_pow_right (by omega) (hd j).2
      exact_mod_cast h1.trans h2
    exact (hN j).trans (by gcongr)
  have hpert : ∀ j (w : monos σ (d j : ℤ) → ℝ),
      ‖(WithLp.toLp 2 w : Hom σ (d j : ℤ))‖ ≤ 2 * Real.sqrt (((Fintype.card σ + 1 : ℕ) : ℝ) ^ dmax) →
      ‖perturbOn (abar j) ρ w‖ ≤ A := by
    intro j w hw
    unfold perturbOn
    calc ‖abar j + ρ • (WithLp.toLp 2 w : Hom σ (d j : ℤ))‖
        ≤ ‖abar j‖ + ‖ρ • (WithLp.toLp 2 w : Hom σ (d j : ℤ))‖ := norm_add_le _ _
      _ = ‖abar j‖ + ρ * ‖(WithLp.toLp 2 w : Hom σ (d j : ℤ))‖ := by
          rw [norm_smul, Real.norm_of_nonneg hρ.le]
      _ ≤ 1 + 1 * (2 * Real.sqrt (((Fintype.card σ + 1 : ℕ) : ℝ) ^ dmax)) := by
          gcongr
          exact habar j
      _ = A := by rw [hA]; ring
  have ha : ∀ j, ‖restr ℓ (perturbOn (abar j) ρ (replaceV ω₀ u j))‖ ≤ A := fun j =>
    (norm_restr_le ℓ _).trans (hpert j _ (hω j))
  have hc : ‖restr ℓ (perturbOn (abar i) ρ (replaceV ω₀ (fun _ _ _ => 0) i))‖ ≤ A :=
    (norm_restr_le ℓ _).trans (hpert i _ ((norm_replaceV_zero_le d ω₀ u i).trans (hω i)))
  constructor
  · have hv : ‖ρ • (WithLp.toLp 2 (u ℓ i) : Hom (Fin q) (d i : ℤ))‖ ≤ A := by
      rw [norm_smul, Real.norm_of_nonneg hρ.le]
      have h1 := (norm_u_le d (fun j => (hd j).1) ω₀ u ℓ i).trans (hω i)
      have h2 : 0 ≤ ‖(WithLp.toLp 2 (u ℓ i) : Hom (Fin q) (d i : ℤ))‖ := norm_nonneg _
      calc ρ * ‖(WithLp.toLp 2 (u ℓ i) : Hom (Fin q) (d i : ℤ))‖
          ≤ 1 * (2 * Real.sqrt (((Fintype.card σ + 1 : ℕ) : ℝ) ^ dmax)) := by gcongr
        _ ≤ A := by rw [hA]; linarith
    calc _ ≤ ‖ρ • (WithLp.toLp 2 (u ℓ i) : Hom (Fin q) (d i : ℤ))‖ ^ D i :=
          PartD.norm_powHom_le (by positivity) _ _
      _ ≤ A ^ D i := pow_le_pow_left₀ (norm_nonneg _) hv _
      _ ≤ A ^ Dmax := pow_le_pow_right₀ hA1 (hD i).2
  · set a' : ∀ j, Hom (Y ⊕ Fin q) (d j : ℤ) := fun j => restr ℓ (perturbOn (abar j) ρ (replaceV ω₀ u j))
    set c := restr ℓ (perturbOn (abar i) ρ (replaceV ω₀ (fun _ _ _ => 0) i))
    have hslot : ∀ j, ‖modGen d D i (toPoly c) a' j‖ ≤ A ^ Dmax + (if j = i then 2 * A else 0) := by
      intro j
      unfold modGen
      by_cases hj : j = i
      · subst hj
        simp only [if_true]
        rw [Dev.L43.norm_ofPoly_toPoly_eq (by simp [modDeg])]
        have : 0 ≤ A ^ Dmax := by positivity
        linarith
      · simp only [hj, if_false, add_zero]
        rw [Dev.L43.norm_ofPoly_congr (Dev.L44.modDeg_ne d D i hj)]
        calc ‖powHom (a' j) (D j)‖ ≤ ‖a' j‖ ^ D j := PartD.norm_powHom_le (by positivity) _ _
          _ ≤ A ^ D j := pow_le_pow_left₀ (norm_nonneg _) (ha j) _
          _ ≤ A ^ Dmax := pow_le_pow_right₀ hA1 (hD j).2
    unfold tupNorm
    refine (norm_le_sum_norm' _).trans ?_
    calc ∑ j, ‖(WithLp.toLp 2 (modGen d D i (toPoly c) a') : Tup (Y ⊕ Fin q) _) j‖
        ≤ ∑ j, (A ^ Dmax + (if j = i then 2 * A else 0)) := Finset.sum_le_sum fun j _ => hslot j
      _ = (m : ℝ) * A ^ Dmax + 2 * A := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp

end ApproxSyzygies.Smoothed.Dev.G41.PartN
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias norm_blocks_le := ApproxSyzygies.Smoothed.Dev.G41.PartN.norm_blocks_le

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartN
open ApproxSyzygies.Smoothed
variable {Y : Type} [Fintype Y] [DecidableEq Y] {L q : ℕ}
/-- Item 2: `restr` commutes with multiplication maps of powers. -/
lemma restr_mulMap {m : ℕ} (ℓ : Fin L) (d D : Fin m → ℕ)
    (a : ∀ i, Hom (Y ⊕ (Fin L × Fin q)) (d i : ℤ)) (s : ℤ)
    (h : Tup (Y ⊕ (Fin L × Fin q)) (fun i => s - (d i : ℤ) * (D i : ℤ))) :
    restr ℓ (mulMap (fun i => powHom (a i) (D i)) s h) =
      mulMap (fun i => powHom (restr ℓ (a i)) (D i)) s (restrTup ℓ h) := by
  apply Dev.L43.toPoly_inj
  rw [toPoly_restr, Dev.L43.toPoly_mulMap, Dev.L43.toPoly_mulMap, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Dev.L44.toPoly_powHom, Dev.L44.toPoly_powHom, map_pow, toPoly_restr]
  show _ = _ * toPoly (restr ℓ (h i))
  rw [toPoly_restr]

/-- Item 4: `restr` keeps the pure-`y` part. -/
lemma yPart_restr (ℓ : Fin L) {e : ℤ} (p : Hom (Y ⊕ (Fin L × Fin q)) e) :
    yPart (restr ℓ p) = yPart p := by
  unfold yPart
  rw [toPoly_restr]
  congr 1
  rw [← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  rintro (y | ⟨ℓ', j⟩)
  · rw [AlgHom.comp_apply, ← aeval_restr_eq, aeval_X, aeval_X]
    simp
  · rw [AlgHom.comp_apply, ← aeval_restr_eq, aeval_X, aeval_X]
    simp only [Sum.elim_inr]
    split_ifs <;> simp

/-- Item 5: `liftZ` has no pure-`y` part. -/
lemma yPart_add_liftZ {Z : Type} [Fintype Z] [DecidableEq Z] (e : ℤ) (he : 1 ≤ e)
    (c : Hom (Y ⊕ Z) e) (v : Hom Z e) : yPart (c + liftZ v) = yPart c := by
  apply Dev.L43.toPoly_inj
  rw [Dev.L43.toPoly_yPart, Dev.L43.toPoly_yPart, Dev.L43.toPoly_add, Dev.L43.E_add,
    Dev.L44.E0_liftZ he, add_zero]

/-- Item 6: pure-`y` parts of a modified family. -/
lemma yParts_modGen {Z : Type} [Fintype Z] [DecidableEq Z] {m : ℕ} (d D : Fin m → ℕ) (i : Fin m)
    (c : Hom (Y ⊕ Z) (d i : ℤ)) (a : ∀ j, Hom (Y ⊕ Z) (d j : ℤ)) :
    yParts (modGen d D i (toPoly c) a) = modGen d D i (toPoly (yPart c)) (yParts a) := by
  funext j
  apply Dev.L43.toPoly_inj
  show toPoly (yPart (modGen d D i (toPoly c) a j)) = _
  rw [Dev.L43.toPoly_yPart, Dev.L44.toPoly_modGen d D i _ (Dev.L43.IsH_toPoly c),
    Dev.L44.toPoly_modGen d D i _ (Dev.L43.IsH_toPoly _)]
  split_ifs
  · rw [Dev.L43.toPoly_yPart]
  · rw [Dev.L44.E0_pow]; simp only [yParts, Dev.L43.toPoly_yPart]

end ApproxSyzygies.Smoothed.Dev.G41.PartN
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartN
open ApproxSyzygies.Smoothed
theorem restr_facts {Y : Type} [Fintype Y] [DecidableEq Y] {L q m : ℕ} (ℓ : Fin L)
    (d D : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i) :
    (∀ (abar : ∀ i, Hom (Y ⊕ (Fin L × Fin q)) (d i : ℤ)) (ρ : ℝ)
        (ω₀ : ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i : ℤ) → ℝ)
        (u : Fin L → ∀ i, monos (Fin q) (d i : ℤ) → ℝ) (i : Fin m),
        restr ℓ (perturbOn (abar i) ρ (replaceV ω₀ u i)) =
          restr ℓ (perturbOn (abar i) ρ (replaceV ω₀ (fun _ _ _ => 0) i)) +
            liftZ (ρ • (WithLp.toLp 2 (u ℓ i) : Hom (Fin q) (d i : ℤ)))) ∧
    (∀ (a : ∀ i, Hom (Y ⊕ (Fin L × Fin q)) (d i : ℤ)) (s : ℤ)
        (h : Tup (Y ⊕ (Fin L × Fin q)) (fun i => s - (d i : ℤ) * (D i : ℤ))),
        restr ℓ (mulMap (fun i => powHom (a i) (D i)) s h) =
          mulMap (fun i => powHom (restr ℓ (a i)) (D i)) s (restrTup ℓ h)) ∧
    (∀ (e : ℤ) (p : Hom (Y ⊕ (Fin L × Fin q)) e), ‖restr ℓ p‖ ≤ ‖p‖) ∧
    (∀ (e : ℤ) (p : Hom (Y ⊕ (Fin L × Fin q)) e), yPart (restr ℓ p) = yPart p) ∧
    (∀ (e : ℤ), 1 ≤ e → ∀ (c : Hom (Y ⊕ Fin q) e) (v : Hom (Fin q) e),
        yPart (c + liftZ v) = yPart c) ∧
    (∀ (i : Fin m) (c : Hom (Y ⊕ Fin q) (d i : ℤ)) (a : ∀ j, Hom (Y ⊕ Fin q) (d j : ℤ)),
        yParts (modGen d D i (toPoly c) a) = modGen d D i (toPoly (yPart c)) (yParts a)) :=
  ⟨fun abar ρ ω₀ u i => restr_perturbOn_replaceV ℓ d hd abar ρ ω₀ u i,
    fun a s h => restr_mulMap ℓ d D a s h,
    fun _ p => norm_restr_le ℓ p,
    fun _ p => yPart_restr ℓ p,
    fun e he c v => yPart_add_liftZ e he c v,
    fun i c a => yParts_modGen d D i c a⟩

end ApproxSyzygies.Smoothed.Dev.G41.PartN
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias restr_facts := ApproxSyzygies.Smoothed.Dev.G41.PartN.restr_facts

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41.PartS
open ApproxSyzygies.Smoothed
/-! # Part S: small helpers for the assembly of `shrink_fixed` -/
lemma yPart_powHom {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] {d : ℤ}
    (a : Hom (Y ⊕ Z) d) (D : ℕ) : yPart (powHom a D) = powHom (yPart a) D := by
  apply Dev.L43.toPoly_inj
  rw [Dev.L43.toPoly_yPart, Dev.L44.toPoly_powHom, Dev.L44.toPoly_powHom, Dev.L43.toPoly_yPart,
    Dev.L44.E0_pow]

lemma modGen_congr {σ : Type} [Fintype σ] [DecidableEq σ] {m : ℕ} (d D : Fin m → ℕ) (i : Fin m)
    (c : MvPolynomial σ ℝ) (a a' : ∀ j, Hom σ (d j : ℤ)) (h : ∀ j, j ≠ i → a j = a' j) :
    modGen d D i c a = modGen d D i c a' := by
  funext j
  unfold modGen
  by_cases hj : j = i
  · simp [hj]
  · simp [hj, h j hj]

lemma continuous_liftZ {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    {d : ℤ} : Continuous (fun u : Hom Z d => (liftZ u : Hom (Y ⊕ Z) d)) := by
  have : (fun u : Hom Z d => (liftZ u : Hom (Y ⊕ Z) d)) =
      ((ofPolyL d) ∘ₗ (rename Sum.inr : MvPolynomial Z ℝ →ₐ[ℝ] MvPolynomial (Y ⊕ Z) ℝ).toLinearMap
        ∘ₗ toPolyL d : Hom Z d →ₗ[ℝ] Hom (Y ⊕ Z) d) := by
    funext u; rfl
  rw [this]
  exact LinearMap.continuous_of_finiteDimensional _

lemma continuous_powHom {σ X : Type} [Fintype σ] [DecidableEq σ] [TopologicalSpace X] {d : ℕ}
    (D : ℕ) (a : X → Hom σ (d : ℤ)) (ha : Continuous a) :
    Continuous fun x => powHom (a x) D := by
  have key := continuous_mulMap_pow (fun _ : Fin 1 => d) (fun _ => D) (fun x _ => a x)
    (fun _ => ha) ((d : ℤ) * (D : ℤ))
    (WithLp.toLp 2 fun _ => ofPoly _ (1 : MvPolynomial σ ℝ))
  refine key.congr fun x => ?_
  apply Dev.L43.toPoly_inj
  rw [Dev.L43.toPoly_mulMap, Fin.sum_univ_one, Dev.L44.toPoly_powHom]
  have h1 : toPoly (ofPoly ((d : ℤ) * (D : ℤ) - (d : ℤ) * (D : ℤ)) (1 : MvPolynomial σ ℝ)) = 1 := by
    apply Dev.L43.toPoly_ofPoly
    intro γ hγ
    rw [coeff_one] at hγ
    split_ifs at hγ with h
    · subst h; simp [Dev.L43.deg]
    · exact absurd rfl hγ
  rw [h1, mul_one]

lemma norm_le_sum_norm {m : ℕ} {β : Fin m → Type} [∀ i, SeminormedAddCommGroup (β i)]
    (g : PiLp 2 β) : ‖g‖ ≤ ∑ i, ‖g i‖ := by
  have h0 : 0 ≤ ∑ i, ‖g i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine le_of_pow_le_pow_left₀ two_ne_zero h0 ?_
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _

/-! # Part S: `shrink_fixed` (stub S4), assembled from F1–F10, D1, D3, S3, A1, A3 -/
/-- The core of `shrink_fixed` for general `Y, L, q`, with the constants as parameters. -/
theorem core {Y : Type} [Fintype Y] [DecidableEq Y] {L q m : ℕ} (hm : 1 ≤ m)
    (dmax Dmax : ℕ) (d D : Fin m → ℕ) (hd : ∀ i, 1 ≤ d i ∧ d i ≤ dmax)
    (hD : ∀ i, 1 ≤ D i ∧ D i ≤ Dmax) (t : ℕ)
    (abar : ∀ i, Hom (Y ⊕ (Fin L × Fin q)) (d i : ℤ)) (habar : ∀ i, ‖abar i‖ ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (G : Set (∀ i, monos Y (d i : ℤ) → ℝ)) (τ₀ : ℝ) (hτ₀ : 0 ≤ τ₀)
    (hG : ∀ ωy ∈ G, IHgood d D (fun i => yPart (abar i)) ρ τ₀ t ωy)
    (ω₀ : ∀ i, monos (Y ⊕ (Fin L × Fin q)) (d i : ℤ) → ℝ) (hω₀ : restrictY ω₀ ∈ G)
    (Abd : ℝ)
    (hAbd : Abd = 1 + 2 * Real.sqrt (((Fintype.card (Y ⊕ (Fin L × Fin q)) + 1 : ℕ) : ℝ) ^ dmax))
    (B : ℝ) (hB : 0 ≤ B)
    (hF3 : ∀ i : Fin m, ∃ CC : (∀ j, Hom (Y ⊕ Fin q) (modDeg d D i j)) →
            (Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)) →L[ℝ]
              EuclideanSpace ℝ (monos (Fin q) ((d i : ℤ) * (D i : ℤ)) ×
                monos Y ((t : ℤ) - (d i : ℤ) * (D i : ℤ)))),
        ∀ (c : Hom (Y ⊕ Fin q) (d i : ℤ)) (a : ∀ j, Hom (Y ⊕ Fin q) (d j : ℤ))
          (v : Hom (Fin q) (d i : ℤ)),
          a i = c + liftZ v →
          KernelCond (yParts fun j => powHom (a j) (D j)) t →
          tauOf (yParts fun j => powHom (a j) (D j)) t ≤ τ₀ →
          KernelCond (yParts (modGen d D i (toPoly c) a)) t →
          tauOf (yParts (modGen d D i (toPoly c) a)) t ≤ τ₀ →
          tupNorm (modGen d D i (toPoly c) a) ≤ (m : ℝ) * Abd ^ Dmax + 2 * Abd →
          ‖CC (modGen d D i (toPoly c) a)‖ ≤ B ∧
          ∀ h : Tup (Y ⊕ Fin q) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)),
            ‖tens (powHom v (D i)) (gVec d D t (yParts a) (yPartTup h) i) +
                CC (modGen d D i (toPoly c) a) (gVec d D t (yParts a) (yPartTup h))‖ ≤
              B * ‖mulMap (fun j => powHom (a j) (D j)) (t : ℤ) h‖)
    (η₀ γ : ℝ) (hη₀ : 0 < η₀)
    (hsa : ∀ i : Fin m, SubspaceAnticonc (1 / 4) η₀ γ
      ((Measure.pi fun _ : monos (Fin q) (d i : ℤ) => gaussianReal 0 1).map
        fun g => powHom (ρ • (WithLp.toLp 2 g : Hom (Fin q) (d i : ℤ))) (D i)))
    (hdim : ∀ i : Fin m, 4 ≤ (monos (Fin q) ((d i : ℤ) * (D i : ℤ))).card)
    (hcardle : ∀ i : Fin m,
      ((monos (Fin q) ((d i : ℤ) * (D i : ℤ))).card : ℝ) ≤ (q : ℝ) ^ (dmax * Dmax))
    (hprod : ((∑ i, (monos Y ((t : ℤ) - (d i : ℤ) * (D i : ℤ))).card : ℕ) : ℝ) *
          ∏ _ℓ : Fin L, (2 * ∑ i, (1 : ℝ) /
            ((monos (Fin q) ((d i : ℤ) * (D i : ℤ))).card : ℝ)) < 1)
    (K₂ : ℝ)
    (hK₂ : 2 * (m : ℝ) * (1 + (Abd ^ Dmax + B + 1) *
      ((m : ℝ) * (q : ℝ) ^ (dmax * Dmax) / η₀)) ^ L * B ≤ K₂) :
    gaussV L q (fun i => (d i : ℤ)) {u | replaceV ω₀ u ∈ ShrinkBad d D abar ρ K₂ t G}
      ≤ ENNReal.ofReal ((m : ℝ) * L * Real.exp (-γ)) := by
  classical
  have hd1 : ∀ i, 1 ≤ d i := fun i => (hd i).1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set a₀ : ∀ j, Hom Y (d j : ℤ) := fun j => perturbOn (yPart (abar j)) ρ (restrictY ω₀ j)
    with ha₀
  have hIH := ih_consequence d D (fun i => yPart (abar i)) ρ τ₀ hτ₀ t (restrictY ω₀) (hG _ hω₀)
  have hRF := fun ℓ : Fin L => restr_facts (Y := Y) (q := q) ℓ d D hd1
  obtain ⟨cB, hcB⟩ : ∃ cB : Fin L → ∀ j, Hom (Y ⊕ Fin q) (d j : ℤ),
      cB = fun ℓ j => restr ℓ (perturbOn (abar j) ρ (replaceV ω₀ (fun _ _ _ => 0) j)) :=
    ⟨_, rfl⟩
  obtain ⟨aB, haB⟩ : ∃ aB : Fin L → (∀ j, monos (Fin q) (d j : ℤ) → ℝ) →
      ∀ j, Hom (Y ⊕ Fin q) (d j : ℤ),
      aB = fun ℓ x j => cB ℓ j + liftZ (ρ • (WithLp.toLp 2 (x j) : Hom (Fin q) (d j : ℤ))) :=
    ⟨_, rfl⟩
  have hrestr : ∀ ℓ (u : Fin L → ∀ i, monos (Fin q) (d i : ℤ) → ℝ) j,
      restr ℓ (perturbOn (abar j) ρ (replaceV ω₀ u j)) = aB ℓ (u ℓ) j := by
    intro ℓ u j
    rw [haB, hcB]
    exact (hRF ℓ).1 abar ρ ω₀ u j
  have hyu : ∀ u : Fin L → ∀ i, monos (Fin q) (d i : ℤ) → ℝ,
      yParts (fun j => perturbOn (abar j) ρ (replaceV ω₀ u j)) = a₀ := by
    intro u
    rw [yParts_perturbOn, restrictY_replaceV d hd1]
  have hyc : ∀ ℓ j, yPart (cB ℓ j) = a₀ j := by
    intro ℓ j
    rw [hcB]
    dsimp only
    rw [(hRF ℓ).2.2.2.1]
    exact congrFun (hyu (fun _ _ _ => 0)) j
  have hya : ∀ ℓ x j, yPart (aB ℓ x j) = a₀ j := by
    intro ℓ x j
    rw [haB]
    dsimp only
    rw [(hRF ℓ).2.2.2.2.1 _ (by exact_mod_cast hd1 j), hyc]
  have hyas : ∀ ℓ x, yParts (aB ℓ x) = a₀ := fun ℓ x => funext (hya ℓ x)
  have hpow : ∀ ℓ x, yParts (fun j => powHom (aB ℓ x j) (D j)) =
      bfam d D (fun i => yPart (abar i)) ρ (restrictY ω₀) := by
    intro ℓ x
    funext j
    simp only [yParts]
    rw [yPart_powHom, hya]
    rfl
  have hmod : ∀ ℓ x i, yParts (modGen d D i (toPoly (cB ℓ i)) (aB ℓ x)) =
      modGen d D i (toPoly (perturbOn (yPart (abar i)) ρ (restrictY ω₀ i)))
        (fun j => perturbOn (yPart (abar j)) ρ (restrictY ω₀ j)) := by
    intro ℓ x i
    rw [(hRF ℓ).2.2.2.2.2, hyc, hyas]
  -- constants
  have hAbd0 : 0 ≤ Abd := by rw [hAbd]; positivity
  set β : ℝ := Abd ^ Dmax + B + 1 with hβ
  have hβ1 : 1 ≤ β := by have := pow_nonneg hAbd0 Dmax; rw [hβ]; linarith
  set Qb : ℝ := (m : ℝ) * (q : ℝ) ^ (dmax * Dmax) / η₀ with hQb
  have hQb0 : 0 ≤ Qb := by positivity
  set Kb : ℝ := (1 + β * Qb) ^ L with hKb
  have hKb1 : 1 ≤ Kb := one_le_pow₀ (by nlinarith)
  set δ : ℝ := 1 / (2 * m * Kb) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδm : (m : ℝ) * Kb * δ = 1 / 2 := by
    rw [hδ]; field_simp
  have hδ1 : δ ≤ 1 := by
    have : (1 : ℝ) ≤ m * Kb := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hm) hKb1
    nlinarith
  obtain ⟨gY, hgY⟩ : ∃ gY : Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)) →
      Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)), gY = gVec d D t a₀ := ⟨_, rfl⟩
  obtain ⟨fB, hfB⟩ : ∃ fB : Fin L → (∀ j, monos (Fin q) (d j : ℤ) → ℝ) →
      Tup (Y ⊕ Fin q) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)) → Hom (Y ⊕ Fin q) (t : ℤ),
      fB = fun ℓ x h => mulMap (fun j => powHom (aB ℓ x j) (D j)) (t : ℤ) h := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Fin L → ∀ i : Fin m, (∀ j, monos (Fin q) (d j : ℤ) → ℝ) →
      Set (Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)) →L[ℝ]
        EuclideanSpace ℝ (monos (Fin q) ((d i : ℤ) * (D i : ℤ)) ×
          monos Y ((t : ℤ) - (d i : ℤ) * (D i : ℤ)))),
      S = fun ℓ i x => {C' | ‖C'‖ ≤ B + 1 ∧
        ∀ (y : monos (Fin q) (d i : ℤ) → ℝ)
          (h' : Tup (Y ⊕ Fin q) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ))),
          ‖tens (powHom (ρ • (WithLp.toLp 2 y : Hom (Fin q) (d i : ℤ))) (D i))
              (gY (yPartTup h') i) + C' (gY (yPartTup h'))‖ ≤
            B * ‖fB ℓ (Function.update x i y) h'‖ + δ * ‖gY (yPartTup h')‖} := ⟨_, rfl⟩
  obtain ⟨Aset, hA⟩ : ∃ Aset : Fin L → Fin m → Set (∀ j, monos (Fin q) (d j : ℤ) → ℝ),
      Aset = fun ℓ i => {x | tupNorm (modGen d D i (toPoly (cB ℓ i)) (aB ℓ x)) ≤
        (m : ℝ) * Abd ^ Dmax + 2 * Abd} := ⟨_, rfl⟩
  -- `S ℓ i x` ignores `x i`
  have hSloc : ∀ ℓ i (x x' : ∀ j, monos (Fin q) (d j : ℤ) → ℝ),
      (∀ j, j ≠ i → x j = x' j) → S ℓ i x = S ℓ i x' := by
    intro ℓ i x x' hxx'
    have e : ∀ y, Function.update x i y = Function.update x' i y := by
      intro y
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj, hxx' j hj]
    rw [hS]
    simp only [e]
  -- measurability of `{x | C' ∈ S x}`
  have hcontA : ∀ ℓ (i : Fin m) (y : monos (Fin q) (d i : ℤ) → ℝ) j,
      Continuous fun x : (∀ j, monos (Fin q) (d j : ℤ) → ℝ) => aB ℓ (Function.update x i y) j := by
    intro ℓ i y j
    rw [haB]
    refine continuous_const.add (continuous_liftZ.comp (Continuous.const_smul ?_ ρ))
    exact (PiLp.continuous_toLp 2 _).comp
      ((continuous_apply j).comp (continuous_id.update i continuous_const))
  have hmeas : ∀ ℓ i C', MeasurableSet {x | C' ∈ S ℓ i x} := by
    intro ℓ i C'
    apply IsClosed.measurableSet
    have e : {x | C' ∈ S ℓ i x} = {_x | ‖C'‖ ≤ B + 1} ∩
        ⋂ (y : monos (Fin q) (d i : ℤ) → ℝ),
          ⋂ (h' : Tup (Y ⊕ Fin q) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ))),
            {x | ‖tens (powHom (ρ • (WithLp.toLp 2 y : Hom (Fin q) (d i : ℤ))) (D i))
              (gY (yPartTup h') i) + C' (gY (yPartTup h'))‖ ≤
              B * ‖fB ℓ (Function.update x i y) h'‖ + δ * ‖gY (yPartTup h')‖} := by
      ext x
      rw [hS]
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [e]
    refine isClosed_const.inter (isClosed_iInter fun y => isClosed_iInter fun h' =>
      isClosed_le continuous_const ?_)
    refine (continuous_const.mul (continuous_norm.comp ?_)).add continuous_const
    rw [hfB]
    exact continuous_mulMap_pow d D (fun x => aB ℓ (Function.update x i y))
      (fun j => hcontA ℓ i y j) (t : ℤ) h'
  -- the δ-ball (Lemma 4.4 in tensor coordinates)
  have hball : ∀ ℓ i, ∀ x ∈ Aset ℓ i, ∃ c₀, Metric.ball c₀ δ ⊆ S ℓ i x := by
    intro ℓ i x hx
    rw [hA] at hx
    obtain ⟨CC, hCC⟩ := hF3 i
    refine ⟨CC (modGen d D i (toPoly (cB ℓ i)) (aB ℓ x)), ?_⟩
    have key : ∀ y : monos (Fin q) (d i : ℤ) → ℝ,
        ‖CC (modGen d D i (toPoly (cB ℓ i)) (aB ℓ x))‖ ≤ B ∧
        ∀ h' : Tup (Y ⊕ Fin q) (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ)),
          ‖tens (powHom (ρ • (WithLp.toLp 2 y : Hom (Fin q) (d i : ℤ))) (D i))
              (gY (yPartTup h') i) +
            CC (modGen d D i (toPoly (cB ℓ i)) (aB ℓ x)) (gY (yPartTup h'))‖ ≤
            B * ‖fB ℓ (Function.update x i y) h'‖ := by
      intro y
      have hmg : modGen d D i (toPoly (cB ℓ i)) (aB ℓ (Function.update x i y)) =
          modGen d D i (toPoly (cB ℓ i)) (aB ℓ x) :=
        modGen_congr d D i _ _ _ fun j hj => by rw [haB]; simp [Function.update_of_ne hj]
      have := hCC (cB ℓ i) (aB ℓ (Function.update x i y)) (ρ • WithLp.toLp 2 y)
        (by rw [haB]; simp) (by rw [hpow]; exact hIH.1.1) (by rw [hpow]; exact hIH.1.2)
        (by rw [hmod]; exact (hIH.2 i).1) (by rw [hmod]; exact (hIH.2 i).2)
        (by rw [hmg]; exact hx)
      rw [hmg, hyas] at this
      rw [hgY, hfB]
      exact this
    intro C' hC'
    rw [Metric.mem_ball, dist_eq_norm] at hC'
    rw [hS]
    refine ⟨?_, fun y h' => ?_⟩
    · have h1 := (key (x i)).1
      calc ‖C'‖ = ‖(C' - CC (modGen d D i (toPoly (cB ℓ i)) (aB ℓ x))) +
            CC (modGen d D i (toPoly (cB ℓ i)) (aB ℓ x))‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
        _ ≤ B + 1 := by linarith
    · have hk' := (key y).2 h'
      set c₀ := CC (modGen d D i (toPoly (cB ℓ i)) (aB ℓ x))
      calc _ = ‖(tens (powHom (ρ • (WithLp.toLp 2 y : Hom (Fin q) (d i : ℤ))) (D i))
              (gY (yPartTup h') i) + c₀ (gY (yPartTup h'))) +
              (C' - c₀) (gY (yPartTup h'))‖ := by
            congr 1
            rw [sub_apply]
            abel
        _ ≤ _ := norm_add_le _ _
        _ ≤ B * ‖fB ℓ (Function.update x i y) h'‖ + δ * ‖gY (yPartTup h')‖ :=
            add_le_add hk' ((C' - c₀).le_opNorm _ |>.trans
              (mul_le_mul_of_nonneg_right hC'.le (norm_nonneg _)))
  -- measurable choice
  have hsel := fun ℓ i => exists_measurable_select (S ℓ i) δ hδ0 (hmeas ℓ i) (Aset ℓ i)
    (hball ℓ i)
  choose cs ks hks hkS hkA using hsel
  have hCloc : ∀ ℓ i (x x' : ∀ j, monos (Fin q) (d j : ℤ) → ℝ),
      (∀ j, j ≠ i → x j = x' j) → cs ℓ i (ks ℓ i x) = cs ℓ i (ks ℓ i x') := by
    intro ℓ i x x' hxx'
    rw [hkS ℓ i x x' (hSloc ℓ i x x' hxx')]
  have hCmeas : ∀ ℓ i (g : Tup Y (fun j => (t : ℤ) - (d j : ℤ) * (D j : ℤ))),
      Measurable fun x => cs ℓ i (ks ℓ i x) g := fun ℓ i g =>
    (measurable_from_nat (f := fun n => cs ℓ i n g)).comp (hks ℓ i)
  have hφ : ∀ i : Fin m, Measurable fun y : monos (Fin q) (d i : ℤ) → ℝ =>
      powHom (ρ • (WithLp.toLp 2 y : Hom (Fin q) (d i : ℤ))) (D i) := fun i =>
    (continuous_powHom (D i) _ ((PiLp.continuous_toLp 2 _).const_smul ρ)).measurable
  -- Proposition 4.8 for the blocks
  have hF1 := prop48_blocks (L := L)
    (ι := fun _ i => ↥(monos (Fin q) ((d i : ℤ) * (D i : ℤ))))
    (κ := fun i => ↥(monos Y ((t : ℤ) - (d i : ℤ) * (D i : ℤ))))
    (U := fun _ i => monos (Fin q) (d i : ℤ) → ℝ)
    (fun _ i => Measure.pi fun _ : monos (Fin q) (d i : ℤ) => gaussianReal 0 1)
    (fun _ i y => powHom (ρ • (WithLp.toLp 2 y : Hom (Fin q) (d i : ℤ))) (D i))
    (fun _ i => hφ i) η₀ γ β (fun _ i => hsa i) (fun _ i => by simpa using hdim i)
    (fun ℓ i x => cs ℓ i (ks ℓ i x)) hCloc hCmeas (by simpa using hprod) hβ1
  have hQle : (⨆ ℓ : Fin L, Real.sqrt (∑ i, ((Fintype.card
      ↥(monos (Fin q) ((d i : ℤ) * (D i : ℤ))) : ℝ)) ^ 2) / η₀) ≤ Qb := by
    refine Real.iSup_le (fun ℓ => ?_) hQb0
    rw [hQb]
    refine div_le_div_of_nonneg_right ?_ hη₀.le
    have hs0 : 0 ≤ ∑ i, ((Fintype.card ↥(monos (Fin q) ((d i : ℤ) * (D i : ℤ))) : ℝ)) := by
      positivity
    calc _ ≤ Real.sqrt ((∑ i, ((Fintype.card
            ↥(monos (Fin q) ((d i : ℤ) * (D i : ℤ))) : ℝ))) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => by positivity)
      _ = ∑ i, ((Fintype.card ↥(monos (Fin q) ((d i : ℤ) * (D i : ℤ))) : ℝ)) :=
          Real.sqrt_sq hs0
      _ ≤ ∑ _i : Fin m, (q : ℝ) ^ (dmax * Dmax) :=
          Finset.sum_le_sum fun i _ => by rw [Fintype.card_coe]; exact hcardle i
      _ = _ := by simp
  have hQ0 : 0 ≤ (⨆ ℓ : Fin L, Real.sqrt (∑ i, ((Fintype.card
      ↥(monos (Fin q) ((d i : ℤ) * (D i : ℤ))) : ℝ)) ^ 2) / η₀) :=
    Real.iSup_nonneg fun ℓ => div_nonneg (Real.sqrt_nonneg _) hη₀.le
  have hX : (1 + β * (⨆ ℓ : Fin L, Real.sqrt (∑ i, ((Fintype.card
      ↥(monos (Fin q) ((d i : ℤ) * (D i : ℤ))) : ℝ)) ^ 2) / η₀)) ^ L ≤ Kb := by
    rw [hKb]
    refine pow_le_pow_left₀ (by positivity) ?_ L
    have := mul_le_mul_of_nonneg_left hQle (by linarith : (0 : ℝ) ≤ β)
    linarith
  rw [show gaussV L q (fun i => (d i : ℤ)) = Measure.pi fun _ : Fin L => Measure.pi fun i =>
    Measure.pi fun _ : monos (Fin q) (d i : ℤ) => gaussianReal 0 1 from rfl]
  refine le_trans (measure_mono ?_) hF1
  intro u hu
  obtain ⟨-, hN, h, hlt⟩ := hu
  have hAmem : ∀ ℓ i, u ℓ ∈ Aset ℓ i := by
    intro ℓ i
    have := (norm_blocks_le dmax Dmax d D hd hD abar habar ρ hρ hρ1 ω₀ u hN ℓ i).2
    rw [← hAbd] at this
    have e : aB ℓ (u ℓ) = fun j => restr ℓ (perturbOn (abar j) ρ (replaceV ω₀ u j)) :=
      funext fun j => (hrestr ℓ u j).symm
    rw [hA]
    show tupNorm _ ≤ _
    rw [e, hcB]
    exact this
  refine ⟨fun ℓ i => ?_, fun H => ?_⟩
  · have h1 := (norm_blocks_le dmax Dmax d D hd hD abar habar ρ hρ hρ1 ω₀ u hN ℓ i).1
    rw [← hAbd] at h1
    have h2 := hkA ℓ i (u ℓ) (hAmem ℓ i)
    rw [hS] at h2
    have h2' := h2.1
    show ‖powHom (ρ • (WithLp.toLp 2 (u ℓ i) : Hom (Fin q) (d i : ℤ))) (D i)‖ +
      ‖cs ℓ i (ks ℓ i (u ℓ))‖ ≤ β
    rw [hβ]
    linarith
  · set f := mulMap (bfam d D abar ρ (replaceV ω₀ u)) (t : ℤ) h with hf
    have hg : gVec d D t (yParts fun i => perturbOn (abar i) ρ (replaceV ω₀ u i))
        (yPartTup h) = gY (yPartTup h) := by rw [hyu, hgY]
    rw [hg] at hlt
    set g := gY (yPartTup h) with hgdef
    have hyt : ∀ ℓ, yPartTup (restrTup ℓ h) = yPartTup h := by
      intro ℓ
      unfold yPartTup restrTup
      congr 1
      funext j
      exact (hRF ℓ).2.2.2.1 _ _
    have hfl : ∀ ℓ, fB ℓ (u ℓ) (restrTup ℓ h) = restr ℓ f := by
      intro ℓ
      rw [hfB, hf]
      show _ = restr ℓ (mulMap (fun j => powHom (perturbOn (abar j) ρ (replaceV ω₀ u j)) (D j))
        (t : ℤ) h)
      rw [(hRF ℓ).2.1]
      simp only [hrestr]
    have hres : ∀ ℓ i, ‖tens (powHom (ρ • (WithLp.toLp 2 (u ℓ i) : Hom (Fin q) (d i : ℤ))) (D i))
        (g i) + cs ℓ i (ks ℓ i (u ℓ)) g‖ ≤ B * ‖f‖ + δ * ‖g‖ := by
      intro ℓ i
      have h2 := hkA ℓ i (u ℓ) (hAmem ℓ i)
      rw [hS] at h2
      have h3 := h2.2 (u ℓ i) (restrTup ℓ h)
      rw [Function.update_eq_self, hyt, hfl] at h3
      have h4 := (hRF ℓ).2.2.1 _ f
      calc _ ≤ _ := h3
        _ ≤ B * ‖f‖ + δ * ‖g‖ := by gcongr
    clear_value f g
    have hH := H (B * ‖f‖ + δ * ‖g‖)
      (add_nonneg (mul_nonneg hB (norm_nonneg _)) (mul_nonneg hδ0.le (norm_nonneg _))) g hres
    have hgsum : ‖g‖ ≤ m * ((B * ‖f‖ + δ * ‖g‖) * Kb) := by
      calc ‖g‖ ≤ ∑ i, ‖g i‖ := norm_le_sum_norm g
        _ ≤ ∑ _i : Fin m, (B * ‖f‖ + δ * ‖g‖) * Kb :=
          Finset.sum_le_sum fun i _ => (hH i).trans
            (mul_le_mul_of_nonneg_left hX
              (add_nonneg (mul_nonneg hB (norm_nonneg _)) (mul_nonneg hδ0.le (norm_nonneg _))))
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have e : (m : ℝ) * ((B * ‖f‖ + δ * ‖g‖) * Kb) =
        m * Kb * B * ‖f‖ + (m * Kb * δ) * ‖g‖ := by ring
    rw [e, hδm] at hgsum
    have hK₂f := mul_le_mul_of_nonneg_right hK₂ (norm_nonneg f)
    linarith

/-- **S4 `shrink_fixed`** (stub statement verbatim). -/
theorem shrink_fixed (ε : ℝ) (hε : 0 < ε) (dmax Dmax t : ℕ) (ht : 1 ≤ t) (CI : ℝ)
    (hCI : 0 ≤ CI) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n →
      ∀ (m : ℕ) [NeZero m] (d D : Fin m → ℕ),
      (∀ i, 1 ≤ d i ∧ d i ≤ dmax) → (∀ i, 1 ≤ D i ∧ D i ≤ Dmax) →
      ∑ i, (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) ≤ (n : ℝ) ^ (-ε) →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ abar : ∀ i, Hom (SplitVar n (Lsplit ε t)) (d i : ℤ), (∀ i, ‖abar i‖ ≤ 1) →
      ∀ G : Set (∀ i, monos (Fin (Ksplit n (Lsplit ε t))) (d i : ℤ) → ℝ),
      (∀ ωy ∈ G, IHgood d D (fun i => yPart (abar i)) ρ ((n : ℝ) ^ CI * ρ ^ (-CI)) t ωy) →
      ∀ ω₀ : ∀ i, monos (SplitVar n (Lsplit ε t)) (d i : ℤ) → ℝ, restrictY ω₀ ∈ G →
        gaussV (Lsplit ε t) (Qsplit n (Lsplit ε t)) (fun i => (d i : ℤ))
            {u | replaceV ω₀ u ∈ ShrinkBad d D abar ρ ((n : ℝ) ^ C₂ * ρ ^ (-C₂)) t G}
          ≤ ENNReal.ofReal
              (Real.exp (-(c₂ * (n : ℝ) ^ (Finset.univ.inf' Finset.univ_nonempty d)))) := by
  obtain ⟨A, hA, k, hF3⟩ := lemma44_tensor t
  obtain ⟨c, hc, c', hc', N₁, hF6⟩ := anticonc_uniform dmax Dmax
  obtain ⟨N₈, hF8⟩ := hprod_bound ε hε dmax Dmax t
  obtain ⟨C₂, hC₂, c₂, hc₂, N₉, hF9⟩ :=
    shrink_arith ε hε dmax Dmax t CI A c c' k N₁ hCI hA hc hc'
  refine ⟨C₂, hC₂, c₂, hc₂, max (max N₈ N₉) 1, ?_⟩
  intro n hn m _ d D hd hD hsum ρ hρ hρ1 abar habar G hG ω₀ hω₀
  have hn8 : N₈ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn9 : N₉ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hL : 1 ≤ Lsplit ε t := Nat.le_add_left 1 _
  obtain ⟨-, -, hcardS⟩ := split_facts n (Lsplit ε t) hL
  have hm1 : 1 ≤ m := NeZero.one_le
  have hmn := m_le_of_sum ε hε dmax Dmax n hn1 m d D hd hD hsum
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin m)) d
  have hdl1 : 1 ≤ Finset.univ.inf' Finset.univ_nonempty d := by rw [hi₀]; exact (hd i₀).1
  have hdlmax : Finset.univ.inf' Finset.univ_nonempty d ≤ dmax := by rw [hi₀]; exact (hd i₀).2
  have hdle : ∀ i, Finset.univ.inf' Finset.univ_nonempty d ≤ d i := fun i =>
    Finset.inf'_le _ (Finset.mem_univ i)
  obtain ⟨hqN₁, hq4, hlet⟩ := hF9 n hn9 m hm1 hmn _ hdl1 hdlmax ρ hρ hρ1
  dsimp only at hlet
  obtain ⟨hK₂, hexp⟩ := hlet
  have hfac0 := Nat.factorial_pos (dmax * Dmax)
  have hq1 : 1 ≤ Qsplit n (Lsplit ε t) := le_trans (by omega) hq4
  have hτ₀ : (0 : ℝ) ≤ (n : ℝ) ^ CI * ρ ^ (-CI) := by positivity
  have hAbd0 : (0 : ℝ) ≤ 1 + 2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax) := by positivity
  have hNbt0 : (0 : ℝ) ≤ (m : ℝ) * (1 + 2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax)) ^ Dmax +
      2 * (1 + 2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax)) := by positivity
  have he : ∀ i, (((d i * D i : ℕ) : ℤ)) = (d i : ℤ) * (D i : ℤ) := fun i => by push_cast; ring
  have he1 : ∀ i, 1 ≤ d i * D i := fun i => Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := (hd i).1; omega) (by have := (hD i).1; omega))
  have hsa : ∀ i : Fin m, SubspaceAnticonc (1 / 4)
      (c' * ρ ^ Dmax / (Qsplit n (Lsplit ε t) : ℝ) ^ (dmax * Dmax))
      (c * (Qsplit n (Lsplit ε t) : ℝ) ^ (Finset.univ.inf' Finset.univ_nonempty d))
      ((Measure.pi fun _ : monos (Fin (Qsplit n (Lsplit ε t))) (d i : ℤ) => gaussianReal 0 1).map
        fun g => powHom (ρ • (WithLp.toLp 2 g : Hom (Fin (Qsplit n (Lsplit ε t))) (d i : ℤ)))
          (D i)) := by
    intro i
    have := hF6 (d i) (D i) (hd i).1 (hd i).2 (hD i).1 (hD i).2 _ (hdle i)
      (Fin (Qsplit n (Lsplit ε t))) (by rw [Fintype.card_fin]; exact hqN₁) ρ hρ hρ1
    rw [Fintype.card_fin] at this
    exact this
  have hdim : ∀ i : Fin m, 4 ≤ (monos (Fin (Qsplit n (Lsplit ε t)))
      ((d i : ℤ) * (D i : ℤ))).card := by
    intro i
    have h7 := (card_monos_bounds (Fin (Qsplit n (Lsplit ε t))) (d i * D i) (he1 i)).1
    rw [he i, Fintype.card_fin] at h7
    have hfac : ((d i * D i).factorial : ℝ) ≤ ((dmax * Dmax).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.mul_le_mul (hd i).2 (hD i).2)
    have hqpow : (Qsplit n (Lsplit ε t) : ℝ) ≤ (Qsplit n (Lsplit ε t) : ℝ) ^ (d i * D i) := by
      exact_mod_cast Nat.le_self_pow (by have := he1 i; omega) _
    have hq4' : (4 : ℝ) * ((dmax * Dmax).factorial : ℝ) ≤ (Qsplit n (Lsplit ε t) : ℝ) := by
      exact_mod_cast hq4
    have hpos : (0 : ℝ) < ((d i * D i).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have h4 : (4 : ℝ) ≤ (Qsplit n (Lsplit ε t) : ℝ) ^ (d i * D i) / ((d i * D i).factorial : ℝ) := by
      rw [le_div_iff₀ hpos]; nlinarith
    exact_mod_cast h4.trans h7
  have hcardle : ∀ i : Fin m, ((monos (Fin (Qsplit n (Lsplit ε t)))
      ((d i : ℤ) * (D i : ℤ))).card : ℝ) ≤ (Qsplit n (Lsplit ε t) : ℝ) ^ (dmax * Dmax) := by
    intro i
    have h7 := (card_monos_bounds (Fin (Qsplit n (Lsplit ε t))) (d i * D i) (he1 i)).2
    rw [he i, Fintype.card_fin] at h7
    calc _ ≤ (Qsplit n (Lsplit ε t) : ℝ) ^ (d i * D i) := by exact_mod_cast h7
      _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast hq1) (Nat.mul_le_mul (hd i).2 (hD i).2)
  have hcore := core (Y := Fin (Ksplit n (Lsplit ε t))) hm1 dmax Dmax d D hd hD t abar habar ρ
    hρ hρ1 G _ hτ₀ hG ω₀ hω₀ (1 + 2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax))
    (by rw [hcardS])
    (A * (1 + (n : ℝ) ^ CI * ρ ^ (-CI)) ^ k * (1 + ((m : ℝ) *
      (1 + 2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax)) ^ Dmax +
      2 * (1 + 2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax)))) ^ k) (by positivity)
    (fun i => by
      obtain ⟨CC, hCC⟩ := hF3 (Y := Fin (Ksplit n (Lsplit ε t)))
        (Z := Fin (Qsplit n (Lsplit ε t))) d D (fun j => (hd j).1) (fun j => (hD j).1) t ht
        le_rfl i
      exact ⟨CC, fun c a v hav h1 h2 h3 h4 h5 => hCC c a v hav _ _ hτ₀ hNbt0 h1 h2 h3 h4 h5⟩)
    _ _ (hsa i₀).2.1 hsa hdim hcardle (hF8 n hn8 m d D hd hD hsum) _ hK₂
  exact hcore.trans (ENNReal.ofReal_le_ofReal hexp)

end ApproxSyzygies.Smoothed.Dev.G41.PartS
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
alias shrink_fixed := ApproxSyzygies.Smoothed.Dev.G41.PartS.shrink_fixed

/-- **The shrinking step** (paper pp. 37–40), assembled from S1–S4. `CI` is the exponent of the
inductive hypothesis. -/
theorem shrink_prob (ε : ℝ) (hε : 0 < ε) (dmax Dmax t : ℕ) (ht : 1 ≤ t) (CI : ℝ) (hCI : 0 ≤ CI) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n →
      ∀ (m : ℕ) [NeZero m] (d D : Fin m → ℕ),
      (∀ i, 1 ≤ d i ∧ d i ≤ dmax) → (∀ i, 1 ≤ D i ∧ D i ≤ Dmax) →
      ∑ i, (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) ≤ (n : ℝ) ^ (-ε) →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ abar : ∀ i, Hom (SplitVar n (Lsplit ε t)) (d i : ℤ), (∀ i, ‖abar i‖ ≤ 1) →
      ∀ G : Set (∀ i, monos (Fin (Ksplit n (Lsplit ε t))) (d i : ℤ) → ℝ), MeasurableSet G →
      (∀ ωy ∈ G, IHgood d D (fun i => yPart (abar i)) ρ ((n : ℝ) ^ CI * ρ ^ (-CI)) t ωy) →
        gaussOn (SplitVar n (Lsplit ε t)) m (fun i => (d i : ℤ))
            (ShrinkBad d D abar ρ ((n : ℝ) ^ C₂ * ρ ^ (-C₂)) t G)
          ≤ ENNReal.ofReal
              (Real.exp (-(c₂ * (n : ℝ) ^ (Finset.univ.inf' Finset.univ_nonempty d)))) := by
  obtain ⟨C₂, hC₂, c₂, hc₂, N₂, hfix⟩ := shrink_fixed ε hε dmax Dmax t ht CI hCI
  refine ⟨C₂, hC₂, c₂, hc₂, N₂, ?_⟩
  intro n hn m _ d D hd hD hsum ρ hρ hρ1 abar habar G hGm hG
  refine fubini_blocks _ _ (measurableSet_shrinkBad d D abar ρ _ t G hGm) _ fun ω₀ => ?_
  by_cases hω₀ : restrictY ω₀ ∈ G
  · exact hfix n hn m d D hd hD hsum ρ hρ hρ1 abar habar G hG ω₀ hω₀
  · refine le_trans (measure_mono (t := ∅) ?_) (by simp)
    intro u hu
    apply hω₀
    have h1 := hu.1
    rwa [restrictY_replaceV d (fun i => (hd i).1)] at h1

/-- **The induction step** `Q(s)` for all `s < t` ⇒ `Q(t)`, `t ≥ 1` (paper §4.6). -/
theorem perDegree_step (t : ℕ) (ht : 1 ≤ t) (IH : ∀ s < t, PerDegree s) : PerDegree t := by
  intro ε hε dmax Dmax
  have hε' : 0 < min (ε / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  obtain ⟨CI, hCI, cI, hcI, NI, hIH⟩ := perDegree_uniform t IH _ hε' dmax Dmax
  obtain ⟨C₂, hC₂, c₂, hc₂, N₂, hshrink⟩ := shrink_prob ε hε dmax Dmax t ht CI hCI.le
  obtain ⟨NS, hNS⟩ := sum_cond_split ε hε dmax Dmax
  obtain ⟨c, hc, NP, hNP⟩ := final_prob_arith t dmax Dmax cI c₂ hcI hc₂
  obtain ⟨C, hC, NC, hNC⟩ := final_C_arith t dmax Dmax CI C₂ hCI.le hC₂
  refine ⟨C, hC, c, hc, 2 * NI + N₂ + NS + NP + NC + 1, ?_⟩
  intro n hn m _ d D hd hD hsum ρ hρ hρ1 abar habar
  have hn1 : 1 ≤ n := by omega
  set L := Lsplit ε t with hLdef
  have hL : 1 ≤ L := Nat.succ_le_succ (Nat.zero_le _)
  obtain ⟨hk2, hkn, hcard⟩ := split_facts n L hL
  set k := Ksplit n L with hkdef
  have hkNI : NI ≤ k := by
    have h1 : ((2 * NI : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * NI ≤ n)
    have h2 : (NI : ℝ) ≤ k := by push_cast at h1; linarith
    exact_mod_cast h2
  let e : Fin n ≃ SplitVar n L := (Fintype.equivFinOfCardEq hcard).symm
  set abar' : ∀ i, Hom (SplitVar n L) (d i : ℤ) := fun i => renameHom e (abar i) with habar'def
  have habar' : ∀ i, ‖abar' i‖ ≤ 1 := fun i => by
    rw [habar'def, norm_renameHom]; exact habar i
  set abary : ∀ i, Hom (Fin k) (d i : ℤ) := fun i => yPart (abar' i) with habarydef
  have habary : ∀ i, ‖abary i‖ ≤ 1 := fun i => (norm_yPart_le' _).trans (habar' i)
  set K : ℝ := (n : ℝ) ^ C * ρ ^ (-C) with hKdef
  set KI : ℝ := (n : ℝ) ^ CI * ρ ^ (-CI) with hKIdef
  set K₂ : ℝ := (n : ℝ) ^ C₂ * ρ ^ (-C₂) with hK₂def
  have hKI0 : 0 ≤ KI := by positivity
  set dl : ℕ := Finset.univ.inf' Finset.univ_nonempty d with hdldef
  have hdl1 : 1 ≤ dl := Finset.le_inf' _ _ fun i _ => (hd i).1
  have hdl2 : dl ≤ dmax :=
    (Finset.inf'_le _ (Finset.mem_univ (⟨0, NeZero.pos m⟩ : Fin m))).trans (hd _).2
  have hm1 : 1 ≤ m := NeZero.pos m
  have hm_le := m_le_of_sum ε hε dmax Dmax n hn1 m d D hd hD hsum
  set IHbad : Set (∀ i, monos (Fin k) (d i : ℤ) → ℝ) :=
    {ωy | ¬ IHgood d D abary ρ KI t ωy} with hIHbaddef
  set μY := gaussOn (Fin k) m (fun i => (d i : ℤ)) with hμY
  set M := toMeasurable μY IHbad with hMdef
  have hMm : MeasurableSet M := measurableSet_toMeasurable _ _
  set μ := gaussOn (SplitVar n L) m (fun i => (d i : ℤ)) with hμ
  set Nb : ℝ := (m : ℝ) * (1 + 2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ dmax)) ^ Dmax with hNbdef
  have hNb0 : 0 ≤ Nb := by positivity
  -- transport to the split variables
  refine le_trans (bad_transport (σ := Fin n) e d D abar ρ K t) ?_
  -- deterministic inclusion
  have hsub : BadT d D abar' ρ K t ⊆
      (restrictY ⁻¹' M ∪ {ω | ¬ Ngood d ω}) ∪ ShrinkBad d D abar' ρ K₂ t Mᶜ := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, not_or, not_not] at hcon
    obtain ⟨⟨hM, hNg⟩, hS⟩ := hcon
    have hgood : IHgood d D abary ρ KI t (restrictY ω) := by
      by_contra hb
      exact hM (subset_toMeasurable _ _ hb)
    have hg : ∀ h : Tup (SplitVar n L) (fun i => (t : ℤ) - ((d i : ℤ) * (D i : ℕ))),
        ‖gVec d D t (yParts fun i => perturbOn (abar' i) ρ (ω i)) (yPartTup h)‖ ≤
          K₂ * ‖mulMap (bfam d D abar' ρ ω) (t : ℤ) h‖ := by
      intro h
      by_contra hlt
      exact hS ⟨hM, hNg, h, lt_of_not_ge hlt⟩
    obtain ⟨⟨hKC, hτ⟩, -⟩ := ih_consequence d D abary ρ KI hKI0 t (restrictY ω) hgood
    have hy := yParts_bfam d D abar' ρ ω
    rw [← hy] at hKC hτ
    have hb := tupNorm_bfam_le dmax Dmax d D hd hD abar' habar' ρ hρ hρ1 ω hNg
    rw [hcard] at hb
    obtain ⟨h, hh⟩ := hω
    have hred : Metric.infDist h (koszul (bfam d D abar' ρ ω) (t : ℤ)) ≤
        redConst t KI Nb * (‖mulMap (bfam d D abar' ρ ω) (t : ℤ) h‖ +
          ‖gVec d D t (yParts fun i => perturbOn (abar' i) ρ (ω i)) (yPartTup h)‖) :=
      reduction_bound d D (fun i => (hd i).1) (fun i => (hD i).1) t ht
        (fun i => perturbOn (abar' i) ρ (ω i)) KI Nb hKI0 hNb0 hKC hτ hb h
    have hr0 : 0 ≤ redConst t KI Nb := by unfold redConst; positivity
    have hCb := hNC n (by omega) ρ hρ hρ1 m hm_le
    have hf0 := norm_nonneg (mulMap (bfam d D abar' ρ ω) (t : ℤ) h)
    have h1 : Metric.infDist h (koszul (bfam d D abar' ρ ω) (t : ℤ)) ≤
        redConst t KI Nb * (1 + K₂) * ‖mulMap (bfam d D abar' ρ ω) (t : ℤ) h‖ := by
      refine hred.trans ?_
      have := mul_le_mul_of_nonneg_left (add_le_add_left (hg h)
        ‖mulMap (bfam d D abar' ρ ω) (t : ℤ) h‖) hr0
      linarith
    have h2 : redConst t KI Nb * (1 + K₂) * ‖mulMap (bfam d D abar' ρ ω) (t : ℤ) h‖ ≤
        K * ‖mulMap (bfam d D abar' ρ ω) (t : ℤ) h‖ :=
      mul_le_mul_of_nonneg_right hCb hf0
    linarith
  -- the inductive-hypothesis event
  have hIHbad : μY IHbad ≤ ENNReal.ofReal
      ((t : ℝ) * ((m : ℝ) + 1) * Real.exp (-(cI * (k : ℝ) ^ dl))) := by
    have hsumk := hNS n (by omega) m d D hd hD hsum k hk2 hkn
    have hD' : ∀ i₀ j, 1 ≤ Function.update D i₀ 1 j ∧ Function.update D i₀ 1 j ≤ Dmax := by
      intro i₀ j
      rw [Function.update_apply]
      split_ifs with hj
      · exact ⟨le_rfl, (hD i₀).1.trans (hD i₀).2⟩
      · exact hD j
    set E := ENNReal.ofReal (Real.exp (-(cI * (k : ℝ) ^ dl))) with hE
    have hone : ∀ (s : Fin t) (D' : Fin m → ℕ), (∀ j, 1 ≤ D' j ∧ D' j ≤ Dmax) →
        ∑ i, (k : ℝ) ^ (-((d i * D' i : ℕ) : ℝ)) ≤ (k : ℝ) ^ (-(min (ε / 2) (1 / 2))) →
        μY (BadT d D' abary ρ KI s) ≤ E := by
      intro s D' hD'b hs'
      refine le_trans (measure_mono (badT_anti d D' abary ρ
        (K_mono_base hkn hCI.le hρ) s)) ?_
      exact hIH s k hkNI m d D' hd hD'b hs' ρ hρ hρ1 abary habary
    have hcover : IHbad ⊆ ⋃ s ∈ Finset.range t,
        (BadT d D abary ρ KI s ∪ ⋃ i, BadT d (Function.update D i 1) abary ρ KI s) := by
      intro ωy hωy
      simp only [hIHbaddef, Set.mem_ofPred_eq, IHgood, not_forall] at hωy
      obtain ⟨s, hs, hns⟩ := hωy
      simp only [Set.mem_iUnion, Set.mem_union, Finset.mem_range]
      refine ⟨s, hs, ?_⟩
      by_contra hc'
      simp only [not_or, not_exists] at hc'
      exact hns ⟨hc'.1, hc'.2⟩
    calc μY IHbad ≤ μY (⋃ s ∈ Finset.range t,
          (BadT d D abary ρ KI s ∪ ⋃ i, BadT d (Function.update D i 1) abary ρ KI s)) :=
          measure_mono hcover
      _ ≤ ∑ s ∈ Finset.range t,
          μY (BadT d D abary ρ KI s ∪ ⋃ i, BadT d (Function.update D i 1) abary ρ KI s) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ s ∈ Finset.range t, (E + ∑ _i : Fin m, E) := by
          refine Finset.sum_le_sum fun s hs => ?_
          rw [Finset.mem_range] at hs
          refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
          · exact hone ⟨s, hs⟩ D hD hsumk.1
          · refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            exact hone ⟨s, hs⟩ _ (hD' i) (hsumk.2 i)
      _ = ENNReal.ofReal ((t : ℝ) * ((m : ℝ) + 1) * Real.exp (-(cI * (k : ℝ) ^ dl))) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
            ENNReal.ofReal_one, hE]
          ring
  have hA : μ (restrictY ⁻¹' M) ≤ ENNReal.ofReal
      ((t : ℝ) * ((m : ℝ) + 1) * Real.exp (-(cI * (k : ℝ) ^ dl))) := by
    have hmp := measurePreserving_restrictY (Y := Fin k) (Z := Fin L × Fin (Qsplit n L))
      (m := m) (fun i => (d i : ℤ))
    rw [hμ, hmp.measure_preimage hMm.nullMeasurableSet, hMdef, measure_toMeasurable]
    exact hIHbad
  have hB : μ {ω | ¬ Ngood d ω} ≤ ENNReal.ofReal ((m : ℝ) *
      Real.exp (-((n : ℝ) ^ dl / (2 * (dmax.factorial : ℝ))))) := by
    have := norm_event (σ := SplitVar n L) (m := m) dmax d hd
    rw [hcard] at this
    exact this
  have hS : μ (ShrinkBad d D abar' ρ K₂ t Mᶜ) ≤
      ENNReal.ofReal (Real.exp (-(c₂ * (n : ℝ) ^ dl))) := by
    refine hshrink n (by omega) m d D hd hD hsum ρ hρ hρ1 abar' habar' Mᶜ hMm.compl ?_
    intro ωy hωy
    by_contra hb
    exact hωy (subset_toMeasurable _ _ hb)
  calc μ (BadT d D abar' ρ K t)
      ≤ μ ((restrictY ⁻¹' M ∪ {ω | ¬ Ngood d ω}) ∪ ShrinkBad d D abar' ρ K₂ t Mᶜ) :=
        measure_mono hsub
    _ ≤ μ (restrictY ⁻¹' M) + μ {ω | ¬ Ngood d ω} + μ (ShrinkBad d D abar' ρ K₂ t Mᶜ) :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal ((t : ℝ) * ((m : ℝ) + 1) * Real.exp (-(cI * (k : ℝ) ^ dl))) +
          ENNReal.ofReal ((m : ℝ) * Real.exp (-((n : ℝ) ^ dl / (2 * (dmax.factorial : ℝ))))) +
          ENNReal.ofReal (Real.exp (-(c₂ * (n : ℝ) ^ dl))) := add_le_add (add_le_add hA hB) hS
    _ = ENNReal.ofReal ((t : ℝ) * ((m : ℝ) + 1) * Real.exp (-(cI * (k : ℝ) ^ dl)) +
          (m : ℝ) * Real.exp (-((n : ℝ) ^ dl / (2 * (dmax.factorial : ℝ)))) +
          Real.exp (-(c₂ * (n : ℝ) ^ dl))) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (Real.exp (-(c * (n : ℝ) ^ dl))) :=
        ENNReal.ofReal_le_ofReal (hNP n (by omega) k m dl hk2 hm1 hm_le hdl1 hdl2)

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
open MeasureTheory ProbabilityTheory
namespace ApproxSyzygies.Smoothed.Dev.G41
open ApproxSyzygies.Smoothed
/-- Strong induction on the output degree. -/
theorem perDegree_all (t : ℕ) : PerDegree t := by
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact perDegree_zero
    · exact perDegree_step t ht IH

end ApproxSyzygies.Smoothed.Dev.G41
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MvPolynomial
open MeasureTheory ProbabilityTheory
namespace ApproxSyzygies.Smoothed
open ApproxSyzygies.Smoothed.Dev.G41 in
theorem chk_theorem_4_1 (ε : ℝ) (hε : 0 < ε) (dmax Dmax T : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n → ∀ (m : ℕ) [NeZero m] (d D : Fin m → ℕ),
        (∀ i, 1 ≤ d i ∧ d i ≤ dmax) → (∀ i, 1 ≤ D i ∧ D i ≤ Dmax) →
        ∑ i, (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) ≤ (n : ℝ) ^ (-ε) →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        ∀ abar : ∀ i, Hom (Fin n) (d i : ℤ), (∀ i, ‖abar i‖ ≤ 1) →
          gaussCoeffs n m (fun i => (d i : ℤ))
            {ω | ∃ t : ℕ, 1 ≤ t ∧ t ≤ T ∧
              ∃ h : Tup (Fin n) (fun i => (t : ℤ) - ((d i : ℤ) * (D i : ℕ))),
                (n : ℝ) ^ C * ρ ^ (-C) *
                    ‖mulMap (fun i => powHom (perturb (abar i) ρ (ω i)) (D i)) (t : ℤ) h‖ <
                  Metric.infDist h
                    (koszul (fun i => powHom (perturb (abar i) ρ (ω i)) (D i)) (t : ℤ))}
            ≤ ENNReal.ofReal
                (Real.exp (-(c * (n : ℝ) ^ (Finset.univ.inf' Finset.univ_nonempty d)))) := by
  obtain ⟨C, hC, c, hc, N, hall⟩ := uniform_consts
    (fun (t : Finset.Icc 1 T) C c N => DegBound (t : ℕ) ε dmax Dmax C c N)
    (fun _ _ _ _ _ _ _ hC hCC _ hcc hNN h => degBound_mono hC hCC hcc hNN h)
    (fun t => perDegree_all t ε hε dmax Dmax)
  obtain ⟨NA, hNA⟩ := union_exp_arith T c hc
  refine ⟨C, hC, c / 2, by positivity, N + NA + 1, ?_⟩
  intro n hn m _ d D hd hD hsum ρ hρ hρ1 abar habar
  set dl : ℕ := Finset.univ.inf' Finset.univ_nonempty d with hdl
  have hdl1 : 1 ≤ dl := Finset.le_inf' _ _ fun i _ => (hd i).1
  have hx : (NA : ℝ) ≤ (n : ℝ) ^ dl := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    calc (NA : ℝ) ≤ n := by exact_mod_cast (by omega : NA ≤ n)
      _ = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ dl := pow_le_pow_right₀ hn1 hdl1
  set K : ℝ := (n : ℝ) ^ C * ρ ^ (-C)
  have hsub : {ω : ∀ i, monos (Fin n) (d i : ℤ) → ℝ | ∃ t : ℕ, 1 ≤ t ∧ t ≤ T ∧
      ∃ h : Tup (Fin n) (fun i => (t : ℤ) - ((d i : ℤ) * (D i : ℕ))),
        K * ‖mulMap (fun i => powHom (perturb (abar i) ρ (ω i)) (D i)) (t : ℤ) h‖ <
          Metric.infDist h (koszul (fun i => powHom (perturb (abar i) ρ (ω i)) (D i)) (t : ℤ))}
      ⊆ ⋃ t ∈ Finset.Icc 1 T, BadT d D abar ρ K t := by
    rintro ω ⟨t, ht1, htT, h, hh⟩
    simp only [Set.mem_iUnion, Finset.mem_Icc]
    exact ⟨t, ⟨ht1, htT⟩, h, hh⟩
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  calc ∑ t ∈ Finset.Icc 1 T, gaussCoeffs n m (fun i => (d i : ℤ)) (BadT d D abar ρ K t)
      ≤ ∑ _t ∈ Finset.Icc 1 T, ENNReal.ofReal (Real.exp (-(c * (n : ℝ) ^ dl))) := by
        refine Finset.sum_le_sum fun t ht => ?_
        exact hall ⟨t, ht⟩ n (by omega) m d D hd hD hsum ρ hρ hρ1 abar habar
    _ = ENNReal.ofReal ((T : ℝ) * Real.exp (-(c * (n : ℝ) ^ dl))) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Real.exp (-(c / 2 * (n : ℝ) ^ dl))) :=
        ENNReal.ofReal_le_ofReal (hNA _ hx)

end ApproxSyzygies.Smoothed
end

theorem solution : type_of% @ApproxSyzygies.Smoothed.chk_theorem_4_1 := @ApproxSyzygies.Smoothed.chk_theorem_4_1
