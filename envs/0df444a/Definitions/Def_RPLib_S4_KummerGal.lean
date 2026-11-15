-- Prove2me | Definitions.Def_RPLib_S4_KummerGal
-- name    : RPLib_S4_KummerGal
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:01:51.080097+00:00
-- url     : https://prove2.me/theorems/feace5ab-f558-4745-bc26-c2606b82ef41
-- title:
--   Kummer characters for a subgroup of a Galois group
-- statement:
--   Let $K \subseteq E$ be fields, $\Gamma \le \operatorname{Gal}(E/K)$ any subgroup, $N \ne 0$ and $\zeta \in E$ a primitive $N$-th root of unity fixed by $\Gamma$. For a unit $\alpha$ with $\alpha^N$ fixed by $\Gamma$ (a Kummer radical) the Kummer character $\kappa_\alpha : \Gamma \to \mathbb{Z}/N$ is defined by $$\sigma(\alpha) = \zeta^{\kappa_\alpha(\sigma)}\,\alpha.$$ The file proves that it is additive in $\sigma$ and in $\alpha$, vanishes exactly when $\Gamma$ fixes $\alpha$, is locally constant for the Krull topology when $E/K$ is integral, that every locally constant homomorphism $\Gamma \to \mathbb{Z}/N$ is a Kummer character (Hilbert 90 at a finite level), and the equivariance $\kappa_{\varphi\alpha}(\sigma) = w\,\kappa_\alpha(\varphi^{-1}\sigma\varphi)$ when $\varphi\zeta = \zeta^w$ and $\varphi$ normalises $\Gamma$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter IV, Section 3 (Kummer theory)

import Mathlib

/-!
# S4-Kummer, part 1: Kummer characters for a subgroup of a Galois group (generic field theory)

Setting: fields `K ⊆ E`, ANY subgroup `Γ ≤ Gal(E/K)` (later `π₁(U ⊗ F̄) ≤ π₁(U)`, with `E = K_U`), `N ≠ 0` and a
primitive `N`-th root of unity `ζ ∈ E` fixed by `Γ`.

* `epow ζ k = ζ ^ k` for `k : ZMod N`, `dlog` its inverse on `μ_N`;
* `rad Γ N`: the Kummer radicals, units `α` with `α ^ N` fixed by `Γ`;
* `kchar hζ α : Γ → ZMod N`, `σ α = ζ ^ (kchar α σ) α` (`kchar_spec`);
* `kchar_mul` / `kchar_mul_left`: additive in `σ` and in `α`; `kchar_eq_zero_iff`: `kchar α = 0 ↔ Γ fixes α`;
* `isLocallyConstant_kchar` (`E/K` integral, Krull topology);
* `exists_kchar_eq`: EVERY locally constant additive character `Γ → ZMod N` is a Kummer character (Hilbert 90 at a
  finite level, by Dedekind's independence of the finitely many `K`-embeddings `L₁ → E`; no normality needed);
* `kchar_conj`: equivariance, `kchar (φ α) σ = w * kchar α (φ⁻¹ σ φ)` when `φ ζ = ζ ^ w` and `φ` normalises `Γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

noncomputable section

/-! ## Powers of `ζ` indexed by `ZMod N` and the discrete logarithm -/

section DLog

variable {E : Type} [Field E] {N : ℕ} [NeZero N] {ζ : E}

/-- `epow ζ k = ζ ^ k` for `k : ZMod N`. -/
def epow (ζ : E) (k : ZMod N) : E := ζ ^ k.val

theorem pow_mod_N (hζ : IsPrimitiveRoot ζ N) (m : ℕ) : ζ ^ (m % N) = ζ ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m N]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

@[simp] theorem epow_zero : epow ζ (0 : ZMod N) = 1 := by
  simp [epow]

theorem epow_add (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) : epow ζ (a + b) = epow ζ a * epow ζ b := by
  unfold epow
  rw [ZMod.val_add, pow_mod_N hζ, pow_add]

theorem epow_ne_zero (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) : epow ζ a ≠ 0 :=
  pow_ne_zero _ (hζ.ne_zero (NeZero.ne N))

theorem epow_pow_N (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) : epow ζ a ^ N = 1 := by
  unfold epow
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem epow_injective (hζ : IsPrimitiveRoot ζ N) {a b : ZMod N} (h : epow ζ a = epow ζ b) : a = b :=
  ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

theorem epow_neg_mul (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) : epow ζ (-a) * epow ζ a = 1 := by
  rw [← epow_add hζ, neg_add_cancel, epow_zero]

theorem epow_pow (hζ : IsPrimitiveRoot ζ N) (w k : ZMod N) : epow ζ w ^ k.val = epow ζ (w * k) := by
  unfold epow
  rw [← pow_mul, ZMod.val_mul, pow_mod_N hζ]

open Classical in
/-- The discrete logarithm on `μ_N` (junk value `0` off `μ_N`). -/
def dlog (hζ : IsPrimitiveRoot ζ N) (x : E) : ZMod N :=
  if h : x ^ N = 1 then ((hζ.eq_pow_of_pow_eq_one h).choose : ZMod N) else 0

theorem epow_dlog (hζ : IsPrimitiveRoot ζ N) {x : E} (h : x ^ N = 1) : epow ζ (dlog hζ x) = x := by
  have hs := (hζ.eq_pow_of_pow_eq_one h).choose_spec
  unfold dlog epow
  rw [dif_pos h, ZMod.val_natCast, Nat.mod_eq_of_lt hs.1, hs.2]

theorem dlog_epow (hζ : IsPrimitiveRoot ζ N) (k : ZMod N) : dlog hζ (epow ζ k) = k :=
  epow_injective hζ (epow_dlog hζ (epow_pow_N hζ k))

end DLog

/-! ## Kummer radicals and Kummer characters -/

section Radicals

variable {K E : Type} [Field K] [Field E] [Algebra K E] (Γ : Subgroup (E ≃ₐ[K] E)) (N : ℕ)

/-- Kummer radicals: units `α` whose `N`-th power is fixed by `Γ`. -/
def rad : Subgroup Eˣ where
  carrier := {α | ∀ σ ∈ Γ, σ ((α : E) ^ N) = (α : E) ^ N}
  mul_mem' := by
    intro a b ha hb σ hσ
    simp only [Units.val_mul, mul_pow, map_mul, ha σ hσ, hb σ hσ]
  one_mem' := by
    intro σ _
    simp
  inv_mem' := by
    intro a ha σ hσ
    simp only [Units.val_inv_eq_inv_val, inv_pow, map_inv₀, ha σ hσ]

theorem mem_rad (α : Eˣ) : α ∈ rad Γ N ↔ ∀ σ ∈ Γ, σ ((α : E) ^ N) = (α : E) ^ N := Iff.rfl

/-- Units fixed by `Γ` (the multiplicative group of the fixed field). -/
def fixUnits : Subgroup Eˣ where
  carrier := {α | ∀ σ ∈ Γ, σ (α : E) = α}
  mul_mem' := by
    intro a b ha hb σ hσ
    simp only [Units.val_mul, map_mul, ha σ hσ, hb σ hσ]
  one_mem' := by
    intro σ _
    simp
  inv_mem' := by
    intro a ha σ hσ
    simp only [Units.val_inv_eq_inv_val, map_inv₀, ha σ hσ]

theorem mem_fixUnits (α : Eˣ) : α ∈ fixUnits Γ ↔ ∀ σ ∈ Γ, σ (α : E) = α := Iff.rfl

theorem fixUnits_le_rad : fixUnits Γ ≤ rad Γ N := by
  intro α hα σ hσ
  rw [map_pow, hα σ hσ]

variable {Γ N}

theorem ratio_pow {α : Eˣ} (hα : α ∈ rad Γ N) (σ : Γ) :
    ((σ : E ≃ₐ[K] E) (α : E) / α) ^ N = 1 := by
  rw [div_pow, ← map_pow, hα σ σ.2, div_self (pow_ne_zero _ α.ne_zero)]

variable [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N)

/-- The Kummer character of `α`: `σ α = ζ ^ (kchar α σ) α`. -/
def kchar (α : Eˣ) (σ : Γ) : ZMod N := dlog hζ ((σ : E ≃ₐ[K] E) (α : E) / α)

theorem kchar_spec {α : Eˣ} (hα : α ∈ rad Γ N) (σ : Γ) :
    (σ : E ≃ₐ[K] E) (α : E) = epow ζ (kchar hζ α σ) * α := by
  rw [kchar, epow_dlog hζ (ratio_pow hα σ), div_mul_cancel₀ _ α.ne_zero]

theorem kchar_eq_iff {α : Eˣ} (hα : α ∈ rad Γ N) (σ : Γ) (k : ZMod N) :
    kchar hζ α σ = k ↔ (σ : E ≃ₐ[K] E) (α : E) = epow ζ k * α := by
  constructor
  · rintro rfl
    exact kchar_spec hζ hα σ
  · intro h
    rw [kchar, h, mul_div_cancel_right₀ _ α.ne_zero, dlog_epow]

theorem map_epow {σ : E ≃ₐ[K] E} (hσ : σ ζ = ζ) (k : ZMod N) : σ (epow ζ k) = epow ζ k := by
  unfold epow
  rw [map_pow, hσ]

variable (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ)
include hζΓ

/-- `kchar α` is a homomorphism `Γ → ZMod N`. -/
theorem kchar_mul {α : Eˣ} (hα : α ∈ rad Γ N) (σ τ : Γ) :
    kchar hζ α (σ * τ) = kchar hζ α σ + kchar hζ α τ := by
  rw [kchar_eq_iff hζ hα, epow_add hζ]
  have e : ((σ * τ : Γ) : E ≃ₐ[K] E) (α : E) = (σ : E ≃ₐ[K] E) ((τ : E ≃ₐ[K] E) (α : E)) := rfl
  rw [e, kchar_spec hζ hα τ, map_mul, kchar_spec hζ hα σ, map_epow (hζΓ σ σ.2)]
  ring

theorem kchar_one {α : Eˣ} (hα : α ∈ rad Γ N) : kchar hζ α (1 : Γ) = 0 := by
  have h := kchar_mul hζ hζΓ hα 1 1
  rw [mul_one] at h
  linear_combination -h

end Radicals

section Radicals2

variable {K E : Type} [Field K] [Field E] [Algebra K E] {Γ : Subgroup (E ≃ₐ[K] E)} {N : ℕ} [NeZero N]
  {ζ : E} (hζ : IsPrimitiveRoot ζ N)

/-- `kchar` is additive in the radical. -/
theorem kchar_mul_left {α β : Eˣ} (hα : α ∈ rad Γ N) (hβ : β ∈ rad Γ N) (σ : Γ) :
    kchar hζ (α * β) σ = kchar hζ α σ + kchar hζ β σ := by
  rw [kchar_eq_iff hζ ((rad Γ N).mul_mem hα hβ), epow_add hζ, Units.val_mul, map_mul, kchar_spec hζ hα σ,
    kchar_spec hζ hβ σ]
  ring

theorem kchar_eq_zero_iff {α : Eˣ} (hα : α ∈ rad Γ N) :
    (∀ σ : Γ, kchar hζ α σ = 0) ↔ α ∈ fixUnits Γ := by
  constructor
  · intro h σ hσ
    have := (kchar_eq_iff hζ hα ⟨σ, hσ⟩ 0).1 (h ⟨σ, hσ⟩)
    rw [epow_zero, one_mul] at this
    exact this
  · intro h σ
    rw [kchar_eq_iff hζ hα, epow_zero, one_mul]
    exact h σ σ.2

theorem kchar_of_fix {α : Eˣ} (hα : α ∈ fixUnits Γ) (σ : Γ) : kchar hζ α σ = 0 :=
  (kchar_eq_zero_iff hζ (fixUnits_le_rad Γ N hα)).2 hα σ

/-- For `E/K` integral, `σ ↦ σ x` is locally constant on `Gal(E/K)` (Krull topology). -/
theorem isLocallyConstant_apply [Algebra.IsIntegral K E] (x : E) :
    IsLocallyConstant (fun σ : E ≃ₐ[K] E => σ x) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  rw [isOpen_iff_mem_nhds]
  intro σ₀ hσ₀
  have hσ₀' : σ₀ x = y := hσ₀
  have hS : IsOpen (MulAction.stabilizer (E ≃ₐ[K] E) x : Set (E ≃ₐ[K] E)) := stabilizer_isOpen_of_isIntegral x
  have hT : IsOpen ((fun τ => σ₀ * τ) '' (MulAction.stabilizer (E ≃ₐ[K] E) x : Set (E ≃ₐ[K] E))) :=
    isOpenMap_mul_left σ₀ _ hS
  refine Filter.mem_of_superset (hT.mem_nhds ⟨1, (MulAction.stabilizer (E ≃ₐ[K] E) x).one_mem, mul_one σ₀⟩) ?_
  rintro _ ⟨τ, hτ, rfl⟩
  have hτ' : τ x = x := hτ
  show (σ₀ * τ) x = y
  rw [AlgEquiv.mul_apply, hτ', hσ₀']

theorem isLocallyConstant_kchar [Algebra.IsIntegral K E] (α : Eˣ) : IsLocallyConstant (kchar hζ (Γ := Γ) α) := by
  have h1 : IsLocallyConstant (fun σ : Γ => (σ : E ≃ₐ[K] E) (α : E)) :=
    (isLocallyConstant_apply (α : E)).comp_continuous continuous_subtype_val
  exact h1.comp (fun y => dlog hζ (y / α))

/-- Kummer characters are equivariant: if `φ` normalises `Γ` and `φ ζ = ζ ^ w`, then
`kchar (φ α) σ = w * kchar α (φ⁻¹ σ φ)`. -/
theorem kchar_conj (φ : E ≃ₐ[K] E) (hφ : ∀ σ ∈ Γ, φ⁻¹ * σ * φ ∈ Γ) {w : ZMod N}
    (hw : φ ζ = epow ζ w) {α : Eˣ} (hα : α ∈ rad Γ N) (hφα : Units.map (φ : E →* E) α ∈ rad Γ N) (σ : Γ) :
    kchar hζ (Units.map (φ : E →* E) α) σ = w * kchar hζ α ⟨φ⁻¹ * (σ : E ≃ₐ[K] E) * φ, hφ σ σ.2⟩ := by
  rw [kchar_eq_iff hζ hφα]
  have e : (σ : E ≃ₐ[K] E) (φ (α : E)) = φ ((φ⁻¹ * σ * φ) (α : E)) := by
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
    congr 1
    group
  have e2 := kchar_spec hζ hα ⟨φ⁻¹ * (σ : E ≃ₐ[K] E) * φ, hφ σ σ.2⟩
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [e]
  rw [show (φ⁻¹ * (σ : E ≃ₐ[K] E) * φ) (α : E) = _ from e2, map_mul]
  unfold epow
  rw [map_pow, hw]
  rw [show epow ζ w ^ (kchar hζ α ⟨φ⁻¹ * (σ : E ≃ₐ[K] E) * φ, hφ σ σ.2⟩).val = _ from epow_pow hζ _ _]
  rfl

/-! ## Surjectivity: every locally constant character is a Kummer character (Hilbert 90) -/

/-- Every locally constant additive character `c : Γ → ZMod N` is `kchar α` for a radical `α`. -/
theorem exists_kchar_eq (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ) (c : Γ → ZMod N) (hc : IsLocallyConstant c)
    (hhom : ∀ σ τ : Γ, c (σ * τ) = c σ + c τ) : ∃ α ∈ rad Γ N, ∀ σ : Γ, kchar hζ α σ = c σ := by
  classical
  have hc1 : c 1 = 0 := by
    have h := hhom 1 1
    rw [mul_one] at h
    linear_combination -h
  have hcinv : ∀ σ : Γ, c σ⁻¹ = - c σ := by
    intro σ
    have h := hhom σ⁻¹ σ
    rw [inv_mul_cancel, hc1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  -- a finite level `L₁` with `Fix(L₁) ∩ Γ ⊆ ker c`
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp (hc.isOpen_fiber (0 : ZMod N))
  have h1t : (1 : E ≃ₐ[K] E) ∈ t := by
    have : (1 : Γ) ∈ Subtype.val ⁻¹' t := by
      rw [hts]
      exact hc1
    exact this
  obtain ⟨L₁, hfin, hL₁⟩ := (krullTopology_mem_nhds_one_iff K E t).mp (ht.mem_nhds h1t)
  have hker : ∀ σ : Γ, (σ : E ≃ₐ[K] E) ∈ L₁.fixingSubgroup → c σ = 0 := by
    intro σ hσ
    have : σ ∈ Subtype.val ⁻¹' t := hL₁ hσ
    rw [hts] at this
    exact this
  -- restriction to `L₁`
  let res : Γ → (L₁ →ₐ[K] E) := fun σ => ((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp L₁.val
  have hres : ∀ σ τ : Γ, res σ = res τ → c σ = c τ := by
    intro σ τ h
    have hfix : ((σ⁻¹ * τ : Γ) : E ≃ₐ[K] E) ∈ L₁.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hx' : (σ : E ≃ₐ[K] E) x = (τ : E ≃ₐ[K] E) x := DFunLike.congr_fun h ⟨x, hx⟩
      show (σ : E ≃ₐ[K] E)⁻¹ ((τ : E ≃ₐ[K] E) x) = x
      rw [← hx', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have h0 := hker _ hfix
    have h2 := hhom σ (σ⁻¹ * τ)
    rw [mul_inv_cancel_left, h0, add_zero] at h2
    exact h2.symm
  -- the coefficients
  let f : (L₁ →ₐ[K] E) → E := fun h => if hh : ∃ σ : Γ, res σ = h then epow ζ (-c hh.choose) else 0
  have f_res : ∀ σ : Γ, f (res σ) = epow ζ (-c σ) := by
    intro σ
    have hh : ∃ τ : Γ, res τ = res σ := ⟨σ, rfl⟩
    simp only [f, dif_pos hh]
    rw [hres _ _ hh.choose_spec]
  have hcomp : ∀ (σ τ : Γ), (((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp (res τ)) = res (σ * τ) := by
    intro σ τ
    ext x
    rfl
  have f_comp : ∀ (σ : Γ) (h : L₁ →ₐ[K] E),
      f ((((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h)) = epow ζ (-c σ) * f h := by
    intro σ h
    by_cases hh : ∃ τ : Γ, res τ = h
    · obtain ⟨τ, rfl⟩ := hh
      rw [hcomp, f_res, f_res, hhom, neg_add, epow_add hζ]
    · have hh' : ¬ ∃ τ : Γ, res τ = (((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h) := by
        rintro ⟨τ, hτ⟩
        apply hh
        refine ⟨σ⁻¹ * τ, ?_⟩
        rw [← hcomp, hτ]
        ext x
        show (σ : E ≃ₐ[K] E)⁻¹ ((σ : E ≃ₐ[K] E) (h x)) = h x
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      simp only [f, dif_neg hh, dif_neg hh', mul_zero]
  -- Dedekind independence of the finitely many embeddings `L₁ → E`
  have : Finite (L₁ →ₐ[K] E) := Finite.algHom K L₁ E
  let _ : Fintype (L₁ →ₐ[K] E) := Fintype.ofFinite _
  have hLI : LinearIndependent E (fun h : L₁ →ₐ[K] E => (h : L₁ → E)) := by
    have := (linearIndependent_monoidHom L₁ E).comp (fun h : L₁ →ₐ[K] E => (h : L₁ →* E))
      (fun a b hab => AlgHom.ext fun x => DFunLike.congr_fun hab x)
    exact this
  have hsum : ∃ z : L₁, ∑ h, f h * h z ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    have hz : ∑ h, f h • (h : L₁ → E) = 0 := by
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hcon z
    have := (Fintype.linearIndependent_iff.mp hLI) f hz (res 1)
    rw [f_res, hc1, neg_zero, epow_zero] at this
    exact one_ne_zero this
  obtain ⟨z, hz⟩ := hsum
  set β := ∑ h, f h * h z with hβdef
  have hfσ : ∀ (σ : Γ) (h : L₁ →ₐ[K] E), (σ : E ≃ₐ[K] E) (f h) = f h := by
    intro σ h
    by_cases hh : ∃ τ : Γ, res τ = h
    · simp only [f, dif_pos hh]
      exact map_epow (hζΓ σ σ.2) _
    · simp only [f, dif_neg hh, map_zero]
  have hσβ : ∀ σ : Γ, (σ : E ≃ₐ[K] E) β = epow ζ (c σ) * β := by
    intro σ
    let e : (L₁ →ₐ[K] E) ≃ (L₁ →ₐ[K] E) :=
      { toFun := fun h => (((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h)
        invFun := fun h => ((((σ : E ≃ₐ[K] E)⁻¹ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h)
        left_inv := fun h => by
          ext x
          show (σ : E ≃ₐ[K] E)⁻¹ ((σ : E ≃ₐ[K] E) (h x)) = h x
          rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
        right_inv := fun h => by
          ext x
          show (σ : E ≃ₐ[K] E) ((σ : E ≃ₐ[K] E)⁻¹ (h x)) = h x
          rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] }
    have step1 : (σ : E ≃ₐ[K] E) β = ∑ h, f h * (e h) z := by
      rw [hβdef, map_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [map_mul, hfσ]
      rfl
    have step2 : ∀ h, f h = epow ζ (c σ) * f (e h) := by
      intro h
      show f h = epow ζ (c σ) * f ((((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h))
      rw [f_comp, ← mul_assoc, mul_comm (epow ζ (c σ)), epow_neg_mul hζ, one_mul]
    rw [step1]
    have step3 : ∑ h, f h * (e h) z = ∑ h, epow ζ (c σ) * (f (e h) * (e h) z) :=
      Finset.sum_congr rfl fun h _ => by rw [← mul_assoc, ← step2 h]
    rw [step3, ← Finset.mul_sum, Equiv.sum_comp e (fun h => f h * h z)]
  refine ⟨Units.mk0 β hz, ?_, ?_⟩
  · intro σ hσ
    rw [Units.val_mk0, map_pow, hσβ ⟨σ, hσ⟩, mul_pow, epow_pow_N hζ, one_mul]
  · intro σ
    rw [kchar_eq_iff hζ (by
      intro σ hσ
      rw [Units.val_mk0, map_pow, hσβ ⟨σ, hσ⟩, mul_pow, epow_pow_N hζ, one_mul]), Units.val_mk0]
    exact hσβ σ

end Radicals2

end

end Kummer
end RamanujanPetersson


