-- Prove2me | Definitions.Def_RPLib_S3_RRB
-- name    : RPLib_S3_RRB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:21:31.305515+00:00
-- url     : https://prove2.me/theorems/5c8419c2-6704-4768-8122-a543d5aea870
-- title:
--   Weight-two Ramanujan-Petersson library: the index formula, Weil differentials and the Riemann-Roch theorem
-- statement:
--   The index formula, Weil differentials and the Riemann-Roch theorem.
--
--   Abstract setting of part A (`RamanujanPetersson.RR.Data` with `Data.Axioms`).  Following
--   Stichtenoth ch. 1.4-1.5 (with `Fq`-dimensions and `Fq`-degrees; `ℓ 0 = [k : Fq]` for the full
--   constant field `k`, so the classical statements are the case `ℓ 0 = 1`):
--
--   * `ell_eq_zero_of_degD_neg`, `defect_le` (Riemann's bound), `gamma = max_D (deg D - ℓ D)`;
--   * `rI_adeles`: `[A : A(D) + F] = q ^ iota D` with `iota D = ℓ D - deg D + γ`; `genus = iota 0`;
--   * Weil differentials `Omega D` (linear forms on the adeles vanishing on `A(D) + F`), the `F`-action
--     `wsmul`, `finrank_Omega : dim Ω(D) = iota D`, one-dimensionality over `F`
--     (`exists_eq_wsmul`, `exists_weilDiff_ne_zero`), the divisor of a differential (`exists_divisor`);
--   * `riemannRoch`: `ℓ D - ℓ (W - D) = deg D + ℓ 0 - g` for a canonical divisor `W`, and the
--     corollaries `ell_canonical`, `degD_canonical`, `ell_eq_of_large_degD`, `ell_le_degD_add`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_RRA

/-!
# Riemann-Roch, part B: the index formula, Weil differentials and the Riemann-Roch theorem

Abstract setting of part A (`RamanujanPetersson.RR.Data` with `Data.Axioms`).  Following
Stichtenoth ch. 1.4-1.5 (with `Fq`-dimensions and `Fq`-degrees; `ℓ 0 = [k : Fq]` for the full
constant field `k`, so the classical statements are the case `ℓ 0 = 1`):

* `ell_eq_zero_of_degD_neg`, `defect_le` (Riemann's bound), `gamma = max_D (deg D - ℓ D)`;
* `rI_adeles`: `[A : A(D) + F] = q ^ iota D` with `iota D = ℓ D - deg D + γ`; `genus = iota 0`;
* Weil differentials `Omega D` (linear forms on the adeles vanishing on `A(D) + F`), the `F`-action
  `wsmul`, `finrank_Omega : dim Ω(D) = iota D`, one-dimensionality over `F`
  (`exists_eq_wsmul`, `exists_weilDiff_ne_zero`), the divisor of a differential (`exists_divisor`);
* `riemannRoch`: `ℓ D - ℓ (W - D) = deg D + ℓ 0 - g` for a canonical divisor `W`, and the
  corollaries `ell_canonical`, `degD_canonical`, `ell_eq_of_large_degD`, `ell_le_degD_add`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero

namespace RamanujanPetersson.RR

namespace Data

section General

variable {Fq F ι : Type*} [Field Fq] [Field F] [Algebra Fq F] (d : Data Fq F ι)

/-! ### Definitions -/

/-- The maximal defect `γ = sup_D (deg D - ℓ D)` (finite under the axioms, `defect_le`). -/
noncomputable def gamma : ℤ := sSup (Set.range fun D : ι →₀ ℤ => d.degD D - d.ell D)

/-- The index exponent `iota D = ℓ D - deg D + γ`, so that `[A : A(D) + F] = q ^ iota D`. -/
noncomputable def iota (D : ι →₀ ℤ) : ℕ := ((d.ell D : ℤ) - d.degD D + d.gamma).toNat

/-- The genus (over `Fq`): `g = iota 0 = dim_Fq A / (A(0) + F)`. -/
noncomputable def genus : ℕ := d.iota 0

theorem AD_sup (D1 D2 : ι →₀ ℤ) : d.AD (D1 ⊔ D2) = d.AD D1 ⊔ d.AD D2 := by
  classical
  apply le_antisymm
  · intro α hα
    rw [mem_AD] at hα
    refine Submodule.mem_sup.2 ⟨fun i => if D2 i ≤ D1 i then α i else 0, ?_,
      fun i => if D2 i ≤ D1 i then 0 else α i, ?_, ?_⟩
    · rw [mem_AD]; intro i
      split_ifs with h
      · have := hα i; rwa [Finsupp.sup_apply, sup_eq_left.2 h] at this
      · simp
    · rw [mem_AD]; intro i
      split_ifs with h
      · simp
      · have := hα i; rwa [Finsupp.sup_apply, sup_eq_right.2 (not_le.1 h).le] at this
    · funext i; simp only [Pi.add_apply]; split_ifs <;> simp
  · exact sup_le (d.AD_mono le_sup_left) (d.AD_mono le_sup_right)

/-- Every adele lies in some `A(E)`. -/
theorem exists_AD_of_mem_adeles {α : ι → F} (hα : α ∈ d.adeles) : ∃ E : ι →₀ ℤ, α ∈ d.AD E := by
  classical
  refine ⟨Finsupp.ofSupportFinite (fun i => if 1 < d.v i (α i) then log (d.v i (α i)) else 0) ?_, ?_⟩
  · refine (d.mem_adeles.1 hα).subset fun i hi => ?_
    by_contra h
    exact hi (if_neg h)
  · rw [mem_AD]
    intro i
    rw [Finsupp.ofSupportFinite_coe]
    split_ifs with h
    · rw [exp_log (zero_lt_one.trans h).ne']
    · rw [exp_zero]; exact not_lt.1 h

theorem mul_mem_adeles (x : F) {α : ι → F} (hα : α ∈ d.adeles) : (fun i => x * α i) ∈ d.adeles := by
  by_cases hx : x = 0
  · subst hx
    have : (fun i => (0 : F) * α i) = 0 := funext fun i => zero_mul _
    rw [this]; exact d.adeles.zero_mem
  · refine ((d.finite_ne_one x hx).union (d.mem_adeles.1 hα)).subset fun i hi => ?_
    simp only [Set.mem_setOf_eq, map_mul] at hi
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_not] at h
    rw [h.1, one_mul] at hi
    exact absurd hi (not_lt.2 h.2)

/-- Multiplication of repartitions by `x ∈ F`. -/
def mulA (x : F) : d.adeles →ₗ[Fq] d.adeles where
  toFun α := ⟨fun i => x * (α : ι → F) i, d.mul_mem_adeles x α.2⟩
  map_add' α β := by
    apply Subtype.ext; funext i; simp [mul_add]
  map_smul' c α := by
    apply Subtype.ext; funext i; simp

@[simp] theorem mulA_apply (x : F) (α : d.adeles) (i : ι) :
    ((d.mulA x α : d.adeles) : ι → F) i = x * (α : ι → F) i := rfl

/-- The `F`-action on linear forms on the adeles: `(x • ω) α = ω (x α)`. -/
def wsmul (x : F) (ω : Module.Dual Fq d.adeles) : Module.Dual Fq d.adeles := ω ∘ₗ d.mulA x

theorem wsmul_apply (x : F) (ω : Module.Dual Fq d.adeles) (α : d.adeles) :
    d.wsmul x ω α = ω (d.mulA x α) := rfl

theorem wsmul_wsmul (x y : F) (ω : Module.Dual Fq d.adeles) :
    d.wsmul x (d.wsmul y ω) = d.wsmul (y * x) ω := by
  refine LinearMap.ext fun α => ?_
  simp only [wsmul_apply]
  congr 1
  apply Subtype.ext; funext i; simp only [mulA_apply]; ring

theorem one_wsmul (ω : Module.Dual Fq d.adeles) : d.wsmul 1 ω = ω := by
  refine LinearMap.ext fun α => ?_
  simp only [wsmul_apply]
  congr 1
  apply Subtype.ext; funext i; simp only [mulA_apply, one_mul]

theorem zero_wsmul (ω : Module.Dual Fq d.adeles) : d.wsmul 0 ω = 0 := by
  refine LinearMap.ext fun α => ?_
  simp only [wsmul_apply, LinearMap.zero_apply]
  have : d.mulA 0 α = 0 := by apply Subtype.ext; funext i; simp
  rw [this, map_zero]

theorem wsmul_zero (x : F) : d.wsmul x 0 = 0 := rfl

theorem add_wsmul (x y : F) (ω : Module.Dual Fq d.adeles) :
    d.wsmul (x + y) ω = d.wsmul x ω + d.wsmul y ω := by
  refine LinearMap.ext fun α => ?_
  simp only [wsmul_apply, LinearMap.add_apply]
  rw [← map_add]
  congr 1
  apply Subtype.ext; funext i; simp [add_mul]

theorem smul_wsmul (c : Fq) (x : F) (ω : Module.Dual Fq d.adeles) :
    d.wsmul (c • x) ω = c • d.wsmul x ω := by
  refine LinearMap.ext fun α => ?_
  simp only [wsmul_apply, LinearMap.smul_apply]
  rw [← map_smul]
  congr 1
  apply Subtype.ext; funext i; simp

theorem inv_wsmul_wsmul {x : F} (hx : x ≠ 0) (ω : Module.Dual Fq d.adeles) :
    d.wsmul x⁻¹ (d.wsmul x ω) = ω := by
  rw [wsmul_wsmul, mul_inv_cancel₀ hx, one_wsmul]

/-- `x ↦ x • ω` as an `Fq`-linear map. -/
def wsmulL (ω : Module.Dual Fq d.adeles) : F →ₗ[Fq] Module.Dual Fq d.adeles where
  toFun x := d.wsmul x ω
  map_add' x y := d.add_wsmul x y ω
  map_smul' c x := d.smul_wsmul c x ω

@[simp] theorem wsmulL_apply (ω : Module.Dual Fq d.adeles) (x : F) : d.wsmulL ω x = d.wsmul x ω := rfl

theorem wsmulL_injective {ω : Module.Dual Fq d.adeles} (hω : ω ≠ 0) : Function.Injective (d.wsmulL ω) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  by_contra hx0
  apply hω
  rw [← d.inv_wsmul_wsmul hx0 ω]
  rw [wsmulL_apply] at hx
  rw [hx, wsmul_zero]

/-! ### Weil differentials -/

/-- `Ω(D)`: the linear forms on the adeles vanishing on `A(D) + F` (Weil differentials of
divisor `≥ D`). -/
def Omega (D : ι →₀ ℤ) : Submodule Fq (Module.Dual Fq d.adeles) :=
  ((d.AD D ⊔ d.Fs).comap d.adeles.subtype).dualAnnihilator

theorem mem_Omega {D : ι →₀ ℤ} {ω : Module.Dual Fq d.adeles} :
    ω ∈ d.Omega D ↔ ∀ α : d.adeles, (α : ι → F) ∈ d.AD D ⊔ d.Fs → ω α = 0 := by
  simp [Omega, Submodule.mem_dualAnnihilator]

/-- A Weil differential: a linear form on the adeles vanishing on some `A(D) + F`. -/
def IsWeilDiff (ω : Module.Dual Fq d.adeles) : Prop := ∃ D, ω ∈ d.Omega D

/-- `W` is a canonical divisor: the divisor of a nonzero Weil differential. -/
def IsCanonical (W : ι →₀ ℤ) : Prop :=
  ∃ ω : Module.Dual Fq d.adeles, ω ≠ 0 ∧ ∀ D, ω ∈ d.Omega D ↔ D ≤ W

theorem Omega_anti {D D' : ι →₀ ℤ} (h : D ≤ D') : d.Omega D' ≤ d.Omega D := fun ω hω =>
  d.mem_Omega.2 fun α hα => d.mem_Omega.1 hω α (sup_le_sup_right (d.AD_mono h) _ hα)

theorem Omega_sup (D1 D2 : ι →₀ ℤ) : d.Omega (D1 ⊔ D2) = d.Omega D1 ⊓ d.Omega D2 := by
  apply le_antisymm
  · exact le_inf (d.Omega_anti le_sup_left) (d.Omega_anti le_sup_right)
  · rintro ω ⟨h1, h2⟩
    rw [SetLike.mem_coe, mem_Omega] at h1 h2
    rw [mem_Omega]
    intro α hα
    rw [AD_sup, sup_sup_distrib_right] at hα
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hα
    have ha' : a ∈ d.adeles := sup_le (d.AD_le_adeles _) d.Fs_le_adeles ha
    have hb' : b ∈ d.adeles := sup_le (d.AD_le_adeles _) d.Fs_le_adeles hb
    have : α = ⟨a, ha'⟩ + ⟨b, hb'⟩ := Subtype.ext hab.symm
    rw [this, map_add, h1 _ ha, h2 _ hb, add_zero]

theorem mul_mem_AD {x : F} (hx : x ≠ 0) {D : ι →₀ ℤ} {α : ι → F} (hα : α ∈ d.AD D) :
    (fun i => x * α i) ∈ d.AD (D - d.div x) := by
  rw [mem_AD] at hα ⊢
  intro i
  rw [map_mul, d.v_eq_exp hx, exp_mul_le_exp_iff]
  simpa using hα i

theorem mul_mem_AD_sup_Fs {x : F} (hx : x ≠ 0) {D : ι →₀ ℤ} {β : ι → F} (hβ : β ∈ d.AD D ⊔ d.Fs) :
    (fun i => x * β i) ∈ d.AD (D - d.div x) ⊔ d.Fs := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hβ
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.1 hb
  refine Submodule.mem_sup.2 ⟨_, d.mul_mem_AD hx ha, d.const (x * f), LinearMap.mem_range_self _ _, ?_⟩
  funext i; simp [mul_add]

/-- `x • ω ∈ Ω(D) ↔ ω ∈ Ω(D - (x))` for `x ≠ 0`. -/
theorem wsmul_mem_Omega_iff {x : F} (hx : x ≠ 0) {D : ι →₀ ℤ} {ω : Module.Dual Fq d.adeles} :
    d.wsmul x ω ∈ d.Omega D ↔ ω ∈ d.Omega (D - d.div x) := by
  simp only [mem_Omega, wsmul_apply]
  constructor
  · intro h β hβ
    have hβ' := d.mul_mem_AD_sup_Fs (inv_ne_zero hx) hβ
    rw [d.div_inv hx, sub_neg_eq_add, sub_add_cancel] at hβ'
    have := h (d.mulA x⁻¹ β) hβ'
    rwa [show d.mulA x (d.mulA x⁻¹ β) = β from
      Subtype.ext (funext fun i => by simp [hx])] at this
  · intro h α hα
    exact h (d.mulA x α) (d.mul_mem_AD_sup_Fs hx hα)

/-- `x ∈ L(D' - D)` and `ω ∈ Ω(D')` give `x • ω ∈ Ω(D)`. -/
theorem wsmul_mem_Omega {x : F} {D D' : ι →₀ ℤ} (hx : x ∈ d.LD (D' - D))
    {ω : Module.Dual Fq d.adeles} (hω : ω ∈ d.Omega D') : d.wsmul x ω ∈ d.Omega D := by
  by_cases hx0 : x = 0
  · subst hx0; rw [zero_wsmul]; exact zero_mem _
  rw [d.wsmul_mem_Omega_iff hx0]
  refine d.Omega_anti ?_ hω
  have := (d.mem_LD_iff_div hx0).1 hx
  rw [Finsupp.le_def] at this ⊢
  intro i
  have := this i
  simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.coe_zero,
    Pi.zero_apply] at this ⊢
  omega

end General

/-! ### Results under the axioms -/

variable {Fq F ι : Type*} [Field Fq] [Field F] [Algebra Fq F] [Fintype Fq] {d : Data Fq F ι}

theorem LD_eq_bot_of_degD_neg (hd : d.Axioms) {D : ι →₀ ℤ} (hD : d.degD D < 0) : d.LD D = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  by_contra hf0
  have h := d.degD_nonneg ((d.mem_LD_iff_div hf0).1 hf)
  rw [degD_add, hd.deg_div f hf0] at h
  linarith

theorem ell_eq_zero_of_degD_neg (hd : d.Axioms) {D : ι →₀ ℤ} (hD : d.degD D < 0) : d.ell D = 0 := by
  rw [ell, LD_eq_bot_of_degD_neg hd hD, finrank_bot]

theorem exists_ne_zero_of_ell_pos {D : ι →₀ ℤ} (h : 0 < d.ell D) : ∃ f ∈ d.LD D, f ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have : d.LD D = ⊥ := (Submodule.eq_bot_iff _).2 hcon
  rw [ell, this, finrank_bot] at h
  exact lt_irrefl 0 h

/-- The defect of effective divisors is bounded by the Riemann-input constant. -/
theorem defect_le_of_nonneg (hd : d.Axioms) {B : ι →₀ ℤ} (hBdeg : 0 < d.degD B) {c : ℤ}
    (hc : ∀ n : ℕ, (n : ℤ) * d.degD B - c ≤ d.ell (n • B)) {A : ι →₀ ℤ} (hA : 0 ≤ A) :
    d.degD A - d.ell A ≤ c := by
  set n : ℕ := (c + d.degD A).toNat + 1 with hn
  have h1 : (n : ℤ) ≥ c + d.degD A + 1 := by omega
  have h2 : (n : ℤ) * d.degD B ≥ n := by
    have : (1 : ℤ) ≤ d.degD B := hBdeg
    nlinarith
  have hle : n • B - A ≤ n • B := sub_le_self _ hA
  have h3 := (ell_sub_le hd.1 hle).1
  rw [degD_sub] at h3
  have hcn := hc n
  have hpos : 0 < d.ell (n • B - A) := by
    rw [degD_nsmul] at h3
    omega
  obtain ⟨z, hz, hz0⟩ := exists_ne_zero_of_ell_pos hpos
  have hdiv := (d.mem_LD_iff_div hz0).1 hz
  have hA2 : A + d.div z⁻¹ ≤ n • B := by
    rw [d.div_inv hz0, Finsupp.le_def]
    intro i
    have := Finsupp.le_def.1 hdiv i
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Finsupp.coe_neg, Pi.add_apply, Pi.sub_apply,
      Pi.neg_apply, Finsupp.coe_zero, Pi.zero_apply] at this ⊢
    omega
  have h4 := (ell_sub_le hd.1 hA2).1
  rw [d.ell_add_div (inv_ne_zero hz0), degD_add, hd.deg_div _ (inv_ne_zero hz0), degD_nsmul] at h4
  linarith

/-- Riemann's bound: `deg D - ℓ D` is bounded above. -/
theorem defect_le (hd : d.Axioms) : ∃ c : ℤ, ∀ D : ι →₀ ℤ, d.degD D - d.ell D ≤ c := by
  obtain ⟨B, _, hBdeg, C, hC, c0, hc0⟩ := hd.riemannInput
  have hc : ∀ n : ℕ, (n : ℤ) * d.degD B - (c0 + d.degD C) ≤ d.ell (n • B) := fun n => by
    have h1 := (ell_sub_le hd.1 (le_add_of_nonneg_right hC : n • B ≤ n • B + C)).1
    rw [degD_add] at h1
    have := hc0 n
    linarith
  refine ⟨c0 + d.degD C, fun D => ?_⟩
  have h1 := (ell_sub_le hd.1 (le_sup_left : D ≤ D ⊔ 0)).1
  have h2 := defect_le_of_nonneg hd hBdeg hc (le_sup_right : (0 : ι →₀ ℤ) ≤ D ⊔ 0)
  linarith

theorem bddAbove_defect (hd : d.Axioms) :
    BddAbove (Set.range fun D : ι →₀ ℤ => d.degD D - d.ell D) := by
  obtain ⟨c, hc⟩ := defect_le hd
  exact ⟨c, by rintro _ ⟨D, rfl⟩; exact hc D⟩

theorem defect_le_gamma (hd : d.Axioms) (D : ι →₀ ℤ) : d.degD D - d.ell D ≤ d.gamma :=
  le_csSup (bddAbove_defect hd) ⟨D, rfl⟩

theorem exists_gamma (hd : d.Axioms) : ∃ D0 : ι →₀ ℤ, d.degD D0 - d.ell D0 = d.gamma :=
  Int.csSup_mem (Set.range_nonempty _) (bddAbove_defect hd)

theorem defect_eq_gamma (hd : d.Axioms) {D0 D : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (h : D0 ≤ D) : d.degD D - d.ell D = d.gamma := by
  have h1 := (ell_sub_le hd.1 h).1
  have h2 := defect_le_gamma hd D
  linarith

theorem AD_le_AD_sup_Fs (hd : d.Axioms) {D0 D D' : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (h : D0 ≤ D) (h' : D ≤ D') : d.AD D' ≤ d.AD D ⊔ d.Fs := by
  have e1 := defect_eq_gamma hd h0 h
  have e2 := defect_eq_gamma hd h0 (h.trans h')
  have hle := (ell_le_of_le hd.1 h').1
  have hr := (ell_sub_le hd.1 h').2
  have hexp : (d.degD D' - d.degD D).toNat - (d.ell D' - d.ell D) = 0 := by omega
  rw [hexp, pow_zero, rI_eq_one_iff] at hr
  exact le_sup_left.trans hr

/-- `A = A(D) + F` once `D ≥ D0` (`D0` of maximal defect). -/
theorem adeles_eq (hd : d.Axioms) {D0 D : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (h : D0 ≤ D) : d.adeles = d.AD D ⊔ d.Fs := by
  apply le_antisymm
  · intro α hα
    obtain ⟨E, hE⟩ := d.exists_AD_of_mem_adeles hα
    exact AD_le_AD_sup_Fs hd h0 h (le_sup_left : D ≤ D ⊔ E) (d.AD_mono le_sup_right hE)
  · exact sup_le (d.AD_le_adeles D) d.Fs_le_adeles

theorem iota_eq (hd : d.Axioms) (D : ι →₀ ℤ) : (d.iota D : ℤ) = d.ell D - d.degD D + d.gamma := by
  have := defect_le_gamma hd D
  unfold iota; omega

theorem genus_eq (hd : d.Axioms) : (d.genus : ℤ) = d.ell 0 + d.gamma := by
  rw [genus, iota_eq hd, degD_zero, sub_zero]

/-- The index formula `[A : A(D) + F] = q ^ (ℓ D - deg D + γ)`. -/
theorem rI_adeles (hd : d.Axioms) (D : ι →₀ ℤ) :
    rI (d.AD D ⊔ d.Fs) d.adeles = Fintype.card Fq ^ d.iota D := by
  obtain ⟨D0, h0⟩ := exists_gamma hd
  have hD : D ≤ D ⊔ D0 := le_sup_left
  rw [adeles_eq hd h0 (le_sup_right : D0 ≤ D ⊔ D0), (ell_sub_le hd.1 hD).2]
  congr 1
  have e2 := defect_eq_gamma hd h0 (le_sup_right : D0 ≤ D ⊔ D0)
  have hle := (ell_le_of_le hd.1 hD).1
  have h1 := (ell_sub_le hd.1 hD).1
  have := iota_eq hd D
  omega

/-- `A = A(D) + F` once `deg D > deg D0 + γ`. -/
theorem adeles_le_of_degD (hd : d.Axioms) {D0 D : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (hD : d.degD D0 + d.gamma < d.degD D) : d.adeles ≤ d.AD D ⊔ d.Fs := by
  have hpos : 0 < d.ell (D - D0) := by
    have := defect_le_gamma hd (D - D0); rw [degD_sub] at this; omega
  obtain ⟨z, hz, hz0⟩ := exists_ne_zero_of_ell_pos hpos
  have hzD : D0 ≤ D + d.div z := by
    have := (d.mem_LD_iff_div hz0).1 hz
    rw [Finsupp.le_def] at this ⊢
    intro i
    have := this i
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.coe_zero,
      Pi.zero_apply] at this ⊢
    omega
  intro α hα
  have hβ : (fun i => z⁻¹ * α i) ∈ d.AD (D + d.div z) ⊔ d.Fs :=
    (adeles_eq hd h0 hzD).le (d.mul_mem_adeles z⁻¹ hα)
  have := d.mul_mem_AD_sup_Fs hz0 hβ
  rw [add_sub_cancel_right] at this
  convert this using 1
  funext i; simp [hz0]

theorem Omega_eq_bot_of_degD (hd : d.Axioms) {D0 D : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (hD : d.degD D0 + d.gamma < d.degD D) : d.Omega D = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro ω hω
  refine LinearMap.ext fun α => ?_
  exact d.mem_Omega.1 hω α (adeles_le_of_degD hd h0 hD α.2)

/-! ### Dimension of `Ω(D)` -/

theorem card_quot_adeles (hd : d.Axioms) (D : ι →₀ ℤ) :
    Nat.card (d.adeles ⧸ (d.AD D ⊔ d.Fs).comap d.adeles.subtype) = Fintype.card Fq ^ d.iota D := by
  rw [← rI_adeles hd D]
  have e : ((d.AD D ⊔ d.Fs).comap d.adeles.subtype).toAddSubgroup =
      (d.AD D ⊔ d.Fs).toAddSubgroup.comap d.adeles.subtype.toAddMonoidHom := rfl
  have e2 : d.adeles.subtype.toAddMonoidHom.range = d.adeles.toAddSubgroup := by
    ext x; simp
  show ((d.AD D ⊔ d.Fs).comap d.adeles.subtype).toAddSubgroup.index = _
  rw [e, AddSubgroup.index_comap, e2]
  rfl

theorem finite_quot_adeles (hd : d.Axioms) (D : ι →₀ ℤ) :
    Module.Finite Fq (d.adeles ⧸ (d.AD D ⊔ d.Fs).comap d.adeles.subtype) := by
  have hc := card_quot_adeles hd D
  have : Finite (d.adeles ⧸ (d.AD D ⊔ d.Fs).comap d.adeles.subtype) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ Fintype.card_ne_zero)
  exact Module.Finite.of_finite

theorem finite_Omega (hd : d.Axioms) (D : ι →₀ ℤ) : Module.Finite Fq (d.Omega D) := by
  have := finite_quot_adeles hd D
  exact Module.Finite.equiv
    (Submodule.dualQuotEquivDualAnnihilator ((d.AD D ⊔ d.Fs).comap d.adeles.subtype))

/-- `dim_Fq Ω(D) = iota D = ℓ D - deg D + γ`. -/
theorem finrank_Omega (hd : d.Axioms) (D : ι →₀ ℤ) : Module.finrank Fq (d.Omega D) = d.iota D := by
  have := finite_quot_adeles hd D
  have hc := card_quot_adeles hd D
  have h2 : Module.finrank Fq (d.adeles ⧸ (d.AD D ⊔ d.Fs).comap d.adeles.subtype) = d.iota D := by
    rw [Module.natCard_eq_pow_finrank (K := Fq), Nat.card_eq_fintype_card] at hc
    exact Nat.pow_right_injective (by have := one_lt_q (Fq := Fq); omega) hc
  rw [← h2, ← Subspace.dual_finrank_eq]
  exact (LinearEquiv.finrank_eq
    (Submodule.dualQuotEquivDualAnnihilator ((d.AD D ⊔ d.Fs).comap d.adeles.subtype))).symm

/-! ### One-dimensionality over `F` -/

/-- Any two Weil differentials, the first nonzero, satisfy `ω₂ = x • ω₁` (Stichtenoth 1.5.9). -/
theorem exists_eq_wsmul (hd : d.Axioms) {ω1 ω2 : Module.Dual Fq d.adeles} {A1 A2 : ι →₀ ℤ}
    (h1 : ω1 ∈ d.Omega A1) (h2 : ω2 ∈ d.Omega A2) (hω1 : ω1 ≠ 0) : ∃ x : F, ω2 = d.wsmul x ω1 := by
  by_cases hω2 : ω2 = 0
  · exact ⟨0, by rw [hω2, zero_wsmul]⟩
  obtain ⟨P⟩ := hd.nonempty
  have hP := hd.deg_pos P
  set n : ℕ := (3 * d.gamma - d.degD A1 - d.degD A2).toNat + 1 with hn
  set B : ι →₀ ℤ := n • Finsupp.single P 1 with hB
  have hdegB : d.degD B = n * d.deg P := by rw [hB, degD_nsmul, degD_single, one_mul]
  have hnP : (n : ℤ) ≤ n * d.deg P := by
    have : (1 : ℤ) ≤ d.deg P := by exact_mod_cast hP
    nlinarith
  have hn1 : (n : ℤ) ≥ 3 * d.gamma - d.degD A1 - d.degD A2 + 1 := by omega
  -- dimension of Ω(-B)
  have hneg : d.degD (-B) < 0 := by rw [degD_neg, hdegB]; omega
  have hiota : (Module.finrank Fq (d.Omega (-B)) : ℤ) = n * d.deg P + d.gamma := by
    rw [finrank_Omega hd, iota_eq hd, ell_eq_zero_of_degD_neg hd hneg, degD_neg, hdegB]; ring
  have := finite_Omega hd (-B)
  -- the two subspaces
  have hU : ∀ {ω : Module.Dual Fq d.adeles} {A : ι →₀ ℤ}, ω ∈ d.Omega A →
      (d.LD (A + B)).map (d.wsmulL ω) ≤ d.Omega (-B) := by
    rintro ω A hω _ ⟨x, hx, rfl⟩
    refine d.wsmul_mem_Omega (D' := A) ?_ hω
    rwa [sub_neg_eq_add]
  have hdim : ∀ {ω : Module.Dual Fq d.adeles} {A : ι →₀ ℤ}, ω ≠ 0 →
      Module.finrank Fq ((d.LD (A + B)).map (d.wsmulL ω)) = d.ell (A + B) := fun hω =>
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (d.wsmulL_injective hω) _)).symm
  have hl : ∀ A : ι →₀ ℤ, d.degD A + n * d.deg P - d.gamma ≤ d.ell (A + B) := fun A => by
    have := defect_le_gamma hd (A + B); rw [degD_add, hdegB] at this; linarith
  set U1 := (d.LD (A1 + B)).map (d.wsmulL ω1)
  set U2 := (d.LD (A2 + B)).map (d.wsmulL ω2)
  have hU1 : U1 ≤ d.Omega (-B) := hU h1
  have hU2 : U2 ≤ d.Omega (-B) := hU h2
  have : FiniteDimensional Fq U1 := Submodule.finiteDimensional_of_le hU1
  have : FiniteDimensional Fq U2 := Submodule.finiteDimensional_of_le hU2
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U1 U2
  have hsup : Module.finrank Fq ↥(U1 ⊔ U2) ≤ Module.finrank Fq (d.Omega (-B)) :=
    Submodule.finrank_mono (sup_le hU1 hU2)
  rw [hdim hω1, hdim hω2] at hsum
  have hinf : U1 ⊓ U2 ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot, add_zero] at hsum
    have := hl A1
    have := hl A2
    have : (Module.finrank Fq ↥(U1 ⊔ U2) : ℤ) ≤ Module.finrank Fq (d.Omega (-B)) := by exact_mod_cast hsup
    have hs : (Module.finrank Fq ↥(U1 ⊔ U2) : ℤ) = d.ell (A1 + B) + d.ell (A2 + B) := by exact_mod_cast hsum
    nlinarith
  obtain ⟨η, hη, hη0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨⟨x1, -, hx1⟩, ⟨x2, -, hx2⟩⟩ := hη
  simp only [wsmulL_apply] at hx1 hx2
  have hx20 : x2 ≠ 0 := by
    rintro rfl; rw [zero_wsmul] at hx2; exact hη0 hx2.symm
  refine ⟨x1 * x2⁻¹, ?_⟩
  rw [← wsmul_wsmul, hx1, ← hx2, inv_wsmul_wsmul _ hx20]

/-- There is a nonzero Weil differential. -/
theorem exists_weilDiff_ne_zero (hd : d.Axioms) :
    ∃ (ω : Module.Dual Fq d.adeles) (A : ι →₀ ℤ), ω ∈ d.Omega A ∧ ω ≠ 0 := by
  obtain ⟨P⟩ := hd.nonempty
  have hP := hd.deg_pos P
  set n : ℕ := (-d.gamma).toNat + 1 with hn
  set B : ι →₀ ℤ := n • Finsupp.single P 1 with hB
  have hdegB : d.degD B = n * d.deg P := by rw [hB, degD_nsmul, degD_single, one_mul]
  have hnP : (n : ℤ) ≤ n * d.deg P := by
    have : (1 : ℤ) ≤ d.deg P := by exact_mod_cast hP
    nlinarith
  have hneg : d.degD (-B) < 0 := by rw [degD_neg, hdegB]; omega
  have hiota : (Module.finrank Fq (d.Omega (-B)) : ℤ) = n * d.deg P + d.gamma := by
    rw [finrank_Omega hd, iota_eq hd, ell_eq_zero_of_degD_neg hd hneg, degD_neg, hdegB]; ring
  have hne : d.Omega (-B) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hiota
    omega
  obtain ⟨ω, hω, hω0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨ω, -B, hω, hω0⟩

/-- The Weil differentials form a one-dimensional `F`-space: a nonzero `ω` and, for every Weil
differential `ω'`, a unique `x` with `ω' = x • ω`. -/
theorem weilDiff_one_dim (hd : d.Axioms) :
    ∃ ω : Module.Dual Fq d.adeles, d.IsWeilDiff ω ∧ ω ≠ 0 ∧
      ∀ ω' : Module.Dual Fq d.adeles, d.IsWeilDiff ω' → ∃! x : F, ω' = d.wsmul x ω := by
  obtain ⟨ω, A, hA, hω⟩ := exists_weilDiff_ne_zero hd
  refine ⟨ω, ⟨A, hA⟩, hω, fun ω' ⟨A', hA'⟩ => ?_⟩
  obtain ⟨x, hx⟩ := exists_eq_wsmul hd hA hA' hω
  refine ⟨x, hx, fun y hy => d.wsmulL_injective hω ?_⟩
  simp only [wsmulL_apply]
  rw [← hy, hx]

/-! ### The divisor of a Weil differential -/

/-- A nonzero Weil differential `ω` has a divisor `W`: `ω ∈ Ω(D) ↔ D ≤ W`. -/
theorem exists_divisor (hd : d.Axioms) {ω : Module.Dual Fq d.adeles} (hω : ω ≠ 0) {A : ι →₀ ℤ}
    (hA : ω ∈ d.Omega A) : ∃ W : ι →₀ ℤ, ∀ D, ω ∈ d.Omega D ↔ D ≤ W := by
  obtain ⟨D0, h0⟩ := exists_gamma hd
  have hb : ∀ D, ω ∈ d.Omega D → d.degD D ≤ d.degD D0 + d.gamma := fun D hD => by
    by_contra hlt
    push Not at hlt
    rw [Omega_eq_bot_of_degD hd h0 hlt] at hD
    exact hω ((Submodule.mem_bot _).1 hD)
  obtain ⟨m, ⟨W, hW, rfl⟩, hm⟩ := Int.exists_greatest_of_bdd
    (P := fun m => ∃ D, ω ∈ d.Omega D ∧ d.degD D = m)
    ⟨d.degD D0 + d.gamma, by rintro z ⟨D, hD, rfl⟩; exact hb D hD⟩ ⟨_, A, hA, rfl⟩
  refine ⟨W, fun D => ⟨fun hD => ?_, fun hle => d.Omega_anti hle hW⟩⟩
  have hsup : ω ∈ d.Omega (D ⊔ W) := by rw [Omega_sup]; exact ⟨hD, hW⟩
  have h1 := hm _ ⟨_, hsup, rfl⟩
  have h2 : (D ⊔ W) - W = 0 := by
    apply d.eq_zero_of_degD_eq_zero hd.deg_pos (sub_nonneg.2 le_sup_right)
    have := d.degD_mono (le_sup_right : W ≤ D ⊔ W)
    rw [degD_sub]; linarith
  have : D ⊔ W = W := sub_eq_zero.1 h2
  exact le_sup_left.trans this.le

theorem exists_isCanonical (hd : d.Axioms) : ∃ W : ι →₀ ℤ, d.IsCanonical W := by
  obtain ⟨ω, A, hA, hω⟩ := exists_weilDiff_ne_zero hd
  obtain ⟨W, hW⟩ := exists_divisor hd hω hA
  exact ⟨W, ω, hω, hW⟩

/-- `(x ω) = (x) + (ω)`. -/
theorem isCanonical_add_div {W : ι →₀ ℤ} (hW : d.IsCanonical W) {x : F} (hx : x ≠ 0) :
    d.IsCanonical (W + d.div x) := by
  obtain ⟨ω, hω, hWω⟩ := hW
  refine ⟨d.wsmul x ω, fun h => hω ?_, fun D => ?_⟩
  · rw [← d.inv_wsmul_wsmul hx ω, h, wsmul_zero]
  · rw [d.wsmul_mem_Omega_iff hx, hWω, Finsupp.le_def, Finsupp.le_def]
    refine forall_congr' fun i => ?_
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply]
    omega

/-- Canonical divisors form one linear equivalence class. -/
theorem isCanonical_eq_add_div (hd : d.Axioms) {W W' : ι →₀ ℤ} (hW : d.IsCanonical W)
    (hW' : d.IsCanonical W') : ∃ x : F, x ≠ 0 ∧ W' = W + d.div x := by
  obtain ⟨ω, hω, hWω⟩ := hW
  obtain ⟨ω', hω', hWω'⟩ := hW'
  obtain ⟨x, rfl⟩ := exists_eq_wsmul hd ((hWω W).2 le_rfl) ((hWω' W').2 le_rfl) hω
  have hx : x ≠ 0 := by rintro rfl; exact hω' (d.zero_wsmul ω)
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · have h := (hWω' W').2 le_rfl
    rw [d.wsmul_mem_Omega_iff hx, hWω] at h
    rw [Finsupp.le_def] at h ⊢
    intro i; have := h i
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply] at this ⊢
    omega
  · have h : W + d.div x - d.div x ≤ W := by rw [add_sub_cancel_right]
    rw [← hWω, ← d.wsmul_mem_Omega_iff hx, hWω'] at h
    exact h

/-! ### The Riemann-Roch theorem -/

/-- `Ω(D) = L(W - D) • ω` for `ω` with divisor `W`. -/
theorem map_LD_eq_Omega (hd : d.Axioms) {ω : Module.Dual Fq d.adeles} (hω : ω ≠ 0) {W : ι →₀ ℤ}
    (hW : ∀ D, ω ∈ d.Omega D ↔ D ≤ W) (D : ι →₀ ℤ) :
    (d.LD (W - D)).map (d.wsmulL ω) = d.Omega D := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact d.wsmul_mem_Omega hx ((hW W).2 le_rfl)
  · intro η hη
    obtain ⟨x, rfl⟩ := exists_eq_wsmul hd ((hW W).2 le_rfl) hη hω
    refine ⟨x, ?_, rfl⟩
    by_cases hx : x = 0
    · subst hx; exact zero_mem _
    rw [d.wsmul_mem_Omega_iff hx, hW] at hη
    rw [SetLike.mem_coe, d.mem_LD_iff_div hx, Finsupp.le_def]
    rw [Finsupp.le_def] at hη
    intro i; have := hη i
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.coe_zero,
      Pi.zero_apply] at this ⊢
    omega

/-- `dim Ω(D) = ℓ(W - D)`. -/
theorem iota_eq_ell (hd : d.Axioms) {W : ι →₀ ℤ} (hW : d.IsCanonical W) (D : ι →₀ ℤ) :
    d.iota D = d.ell (W - D) := by
  obtain ⟨ω, hω, hWω⟩ := hW
  rw [← finrank_Omega hd, ← map_LD_eq_Omega hd hω hWω D, ell]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (d.wsmulL_injective hω) _)).symm

/-- **Riemann-Roch**: `ℓ D - ℓ (W - D) = deg D + ℓ 0 - g` (`ℓ 0 = 1` for constant field `Fq`). -/
theorem riemannRoch (hd : d.Axioms) {W : ι →₀ ℤ} (hW : d.IsCanonical W) (D : ι →₀ ℤ) :
    (d.ell D : ℤ) - d.ell (W - D) = d.degD D + d.ell 0 - d.genus := by
  have h1 := iota_eq_ell hd hW D
  have h2 := iota_eq hd D
  have h3 := genus_eq hd
  rw [h1] at h2
  linarith

/-- Riemann's inequality `ℓ D ≥ deg D + ℓ 0 - g`. -/
theorem riemann_inequality (hd : d.Axioms) (D : ι →₀ ℤ) :
    d.degD D + d.ell 0 - d.genus ≤ d.ell D := by
  have := defect_le_gamma hd D
  have := genus_eq hd
  linarith

/-- `ℓ W = g`. -/
theorem ell_canonical (hd : d.Axioms) {W : ι →₀ ℤ} (hW : d.IsCanonical W) : d.ell W = d.genus := by
  have := riemannRoch hd hW 0
  rw [sub_zero, degD_zero] at this
  omega

/-- `deg W = 2g - 2ℓ 0` (`= 2g - 2` for constant field `Fq`). -/
theorem degD_canonical (hd : d.Axioms) {W : ι →₀ ℤ} (hW : d.IsCanonical W) :
    d.degD W = 2 * d.genus - 2 * d.ell 0 := by
  have h1 := riemannRoch hd hW W
  have h2 := ell_canonical hd hW
  rw [sub_self] at h1
  rw [h2] at h1
  linarith

/-- `ℓ D = deg D + ℓ 0 - g` once `deg D > 2g - 2ℓ 0`. -/
theorem ell_eq_of_large_degD (hd : d.Axioms) {D : ι →₀ ℤ}
    (hD : 2 * (d.genus : ℤ) - 2 * d.ell 0 < d.degD D) :
    (d.ell D : ℤ) = d.degD D + d.ell 0 - d.genus := by
  obtain ⟨W, hW⟩ := exists_isCanonical hd
  have h1 := riemannRoch hd hW D
  have h0 : d.ell (W - D) = 0 := by
    apply ell_eq_zero_of_degD_neg hd
    rw [degD_sub, degD_canonical hd hW]; linarith
  rw [h0, Nat.cast_zero, sub_zero] at h1
  exact h1

/-- `ℓ D ≤ deg D + ℓ 0` for `deg D ≥ 0` (`ℓ D ≤ deg D + 1` for constant field `Fq`). -/
theorem ell_le_degD_add (hd : d.Axioms) {D : ι →₀ ℤ} (hD : 0 ≤ d.degD D) :
    (d.ell D : ℤ) ≤ d.degD D + d.ell 0 := by
  rcases Nat.eq_zero_or_pos (d.ell D) with h | h
  · rw [h]; have := Nat.zero_le (d.ell 0); omega
  obtain ⟨z, hz, hz0⟩ := exists_ne_zero_of_ell_pos h
  have hnn : 0 ≤ D + d.div z := by rw [add_comm]; exact (d.mem_LD_iff_div hz0).1 hz
  have := (ell_sub_le hd.1 hnn).1
  rw [d.ell_add_div hz0, degD_add, hd.deg_div z hz0, degD_zero] at this
  linarith

end Data

end RamanujanPetersson.RR


