-- Prove2me | Definitions.Def_RPLib_S4_SwanSlope1a
-- name    : RPLib_S4_SwanSlope1a
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:28:45.072501+00:00
-- url     : https://prove2.me/theorems/78105f90-e61e-4ce9-add9-f0f79ac71520
-- title:
--   Slope-one structure of a ramification filtration: the abstract part
-- statement:
--   Let $G$ carry a ramification function and let $\Phi : G^1 \to \mathbb{F}_q$ be a homomorphism from the upper ramification group $G^1$ to the additive group of $\mathbb{F}_q$. The file proves the group-theoretic and linear-algebra steps behind the slope-one analysis of Katz: sections of $\Phi$, the existence of an additive character $\psi'$ of $\mathbb{F}_q$ with $\chi = \psi' \circ \Phi$ for characters $\chi$ trivial on $\ker \Phi$, eigenvectors of the abelian quotient on a representation, and the conclusion that if a twist $\rho \otimes \chi$ has nonzero invariants under $G^1$ while all breaks of $\rho$ are $\le 1$, then $$\mathrm{Sw}(\rho \otimes \chi) < \dim \rho.$$ It also contains valuation lemmas for shifting the ramification function by one.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Exponential Sums and Differential Equations, Annals of Mathematics Studies 124, Princeton University Press (1990), Section 7.8; J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter IV

import Mathlib
import Definitions.Def_RPLib_S4_SwanBrk
import Definitions.Def_RPLib_S4_SwanLoc

/-!
# S4-Swan (K2), part 28: slope-1 local structure (abstract part)

* `mem_of_map_eq_one`: a homomorphism `Φ : G → Fq` mapping `U` onto `Fq` and killing `W ≤ U` with `|U/W| ≤ q`
  has kernel on `U` exactly `W`; then every character of `U` trivial on `W` is `ψ' ∘ Φ` (`exists_addChar_eq`).
* `exists_eigen`: a representation on which `W` acts trivially has, for a primitive `ψ`, a common eigenvector of
  `U` with eigencharacter `ψ(a Φ(·))`, so `fixd (ρ ⊗ ψ(b Φ)) U ≠ ⊥` for some `b` (`exists_fixd_twist_ne_bot`).
* `RamFn.swan_lt_of_fixd`: all breaks `≤ 1` and `V^{G^1} ≠ 0` give `Sw(ρ) < dim V`.
* `LocData.card_lower_quot_le`: `|G_m / G_{m+1}| ≤ |T|` for a residue map `L → T`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Swan

noncomputable section

open Module

section Group

variable {G : Type*} [Group G] {Fq : Type*} [Field Fq] [Fintype Fq]
variable {U W : Subgroup G} (Φ : G →* Multiplicative Fq)

/-- Counting: `ker (Φ|U) = W` when `Φ(U) = Fq`, `Φ(W) = 1` and `|U/W| ≤ q`. -/
theorem mem_of_map_eq_one [Finite G] (_hWU : W ≤ U)
    (hsurj : ∀ c : Fq, ∃ σ ∈ U, Φ σ = Multiplicative.ofAdd c) (hW : ∀ σ ∈ W, Φ σ = 1)
    (hcard : Nat.card (U ⧸ W.subgroupOf U) ≤ Nat.card Fq) {σ : G} (hσU : σ ∈ U) (hσ : Φ σ = 1) : σ ∈ W := by
  set Φ' : U →* Multiplicative Fq := Φ.comp U.subtype
  have hs : Function.Surjective Φ' := fun c => by
    obtain ⟨τ, hτ, h⟩ := hsurj (Multiplicative.toAdd c)
    exact ⟨⟨τ, hτ⟩, h⟩
  have hle : W.subgroupOf U ≤ Φ'.ker := fun τ hτ => hW τ hτ
  have h1 : Nat.card U = Nat.card (U ⧸ Φ'.ker) * Nat.card Φ'.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card (U ⧸ Φ'.ker) = Nat.card Fq := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective Φ' hs).toEquiv]
    exact Nat.card_congr Multiplicative.toAdd
  have h3 : Nat.card U = Nat.card (U ⧸ W.subgroupOf U) * Nat.card (W.subgroupOf U) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hq : 0 < Nat.card Fq := Nat.card_pos
  have h4 : Nat.card Φ'.ker ≤ Nat.card (W.subgroupOf U) := by
    rw [h2] at h1
    have h5 : Nat.card Fq * Nat.card Φ'.ker ≤ Nat.card Fq * Nat.card (W.subgroupOf U) := by
      calc Nat.card Fq * Nat.card Φ'.ker = Nat.card U := by rw [h1]
        _ = Nat.card (U ⧸ W.subgroupOf U) * Nat.card (W.subgroupOf U) := h3
        _ ≤ Nat.card Fq * Nat.card (W.subgroupOf U) := Nat.mul_le_mul_right _ hcard
    exact Nat.le_of_mul_le_mul_left h5 hq
  have heq : W.subgroupOf U = Φ'.ker := Subgroup.eq_of_le_of_card_ge hle h4
  have hmem : (⟨σ, hσU⟩ : U) ∈ Φ'.ker := hσ
  rw [← heq] at hmem
  exact hmem

section Sect

variable (hsurj : ∀ c : Fq, ∃ σ ∈ U, Φ σ = Multiplicative.ofAdd c)

/-- A section of `Φ` on `U`. -/
def sect (c : Fq) : G := (hsurj c).choose

theorem sect_mem (c : Fq) : sect Φ hsurj c ∈ U := (hsurj c).choose_spec.1

theorem sect_spec (c : Fq) : Φ (sect Φ hsurj c) = Multiplicative.ofAdd c := (hsurj c).choose_spec.2

end Sect

variable [Finite G] (hWU : W ≤ U) (hsurj : ∀ c : Fq, ∃ σ ∈ U, Φ σ = Multiplicative.ofAdd c)
  (hW : ∀ σ ∈ W, Φ σ = 1) (hcard : Nat.card (U ⧸ W.subgroupOf U) ≤ Nat.card Fq)
include hWU hsurj hW hcard

/-- Two elements of `U` with the same `Φ`-value differ by an element of `W`. -/
theorem inv_mul_mem {σ τ : G} (hσ : σ ∈ U) (hτ : τ ∈ U) (h : Φ σ = Φ τ) : σ⁻¹ * τ ∈ W :=
  mem_of_map_eq_one Φ hWU hsurj hW hcard (U.mul_mem (U.inv_mem hσ) hτ)
    (by rw [map_mul, map_inv, h, inv_mul_cancel])

theorem sect_zero_mem : sect Φ hsurj 0 ∈ W := by
  have h := inv_mul_mem Φ hWU hsurj hW hcard U.one_mem (sect_mem Φ hsurj 0)
    (by rw [map_one, sect_spec]; rfl)
  rwa [inv_one, one_mul] at h

/-- **Characters of `U/W`**: every character of `U` trivial on `W` is `ψ' ∘ Φ`. -/
theorem exists_addChar_eq {k : Type*} [Field k] (χ : G →* kˣ) (hχ : ∀ σ ∈ W, χ σ = 1) :
    ∃ ψ' : AddChar Fq k, ∀ σ ∈ U, ((χ σ : kˣ) : k) = ψ' (Multiplicative.toAdd (Φ σ)) := by
  have key : ∀ σ τ : G, σ ∈ U → τ ∈ U → Φ σ = Φ τ → χ σ = χ τ := fun σ τ hσ hτ h => by
    have h1 := hχ _ (inv_mul_mem Φ hWU hsurj hW hcard hσ hτ h)
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  let s := sect Φ hsurj
  refine ⟨{ toFun := fun c => ((χ (s c) : kˣ) : k), map_zero_eq_one' := ?_, map_add_eq_mul' := ?_ }, ?_⟩
  · rw [hχ _ (sect_zero_mem Φ hWU hsurj hW hcard), Units.val_one]
  · intro a b
    have h := key (s (a + b)) (s a * s b) (sect_mem Φ hsurj _)
      (U.mul_mem (sect_mem Φ hsurj a) (sect_mem Φ hsurj b))
      (by rw [map_mul, sect_spec, sect_spec, sect_spec]; rfl)
    rw [h, map_mul, Units.val_mul]
  · intro σ hσ
    have h := key σ (s (Multiplicative.toAdd (Φ σ))) hσ (sect_mem Φ hsurj _) (by rw [sect_spec]; rfl)
    show ((χ σ : kˣ) : k) = ((χ (s (Multiplicative.toAdd (Φ σ))) : kˣ) : k)
    rw [h]

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- **Common eigenvector** of `U` when `W` acts trivially (`ψ` primitive, `q` invertible in `k`). -/
theorem exists_eigen (hρW : ∀ σ ∈ W, ∀ w : V, ρ σ w = w) (ψ : AddChar Fq k) (hψ : ψ.IsPrimitive)
    (hq : (Fintype.card Fq : k) ≠ 0) [Nontrivial V] :
    ∃ a : Fq, ∃ w : V, w ≠ 0 ∧ ∀ σ ∈ U, ρ σ w = ψ (a * Multiplicative.toAdd (Φ σ)) • w := by
  classical
  let s := sect Φ hsurj
  have hshift : ∀ τ ∈ U, ∀ (c : Fq) (u : V), ρ τ (ρ (s c) u) = ρ (s (Multiplicative.toAdd (Φ τ) + c)) u := by
    intro τ hτ c u
    have hm := inv_mul_mem Φ hWU hsurj hW hcard (sect_mem Φ hsurj (Multiplicative.toAdd (Φ τ) + c))
      (U.mul_mem hτ (sect_mem Φ hsurj c)) (by rw [map_mul, sect_spec, sect_spec]; rfl)
    have hg : τ * s c = s (Multiplicative.toAdd (Φ τ) + c) *
        ((s (Multiplicative.toAdd (Φ τ) + c))⁻¹ * (τ * s c)) := by group
    rw [← Module.End.mul_apply, ← map_mul, hg, map_mul, Module.End.mul_apply]
    congr 1
    exact hρW _ hm u
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  let e : Fq → V := fun a => ∑ c : Fq, ψ (-(a * c)) • ρ (s c) u
  have hsum : ∑ a : Fq, e a = (Fintype.card Fq : k) • u := by
    simp only [e]
    rw [Finset.sum_comm]
    have h1 : ∀ c : Fq, ∑ a : Fq, ψ (-(a * c)) • ρ (s c) u =
        (if -c = 0 then (Fintype.card Fq : k) else 0) • ρ (s c) u := by
      intro c
      rw [← Finset.sum_smul]
      congr 1
      have := AddChar.sum_mulShift (R' := k) (ψ := ψ) (-c) hψ
      simpa [mul_neg] using this
    rw [Finset.sum_congr rfl fun c _ => h1 c]
    rw [Finset.sum_eq_single (0 : Fq)]
    · rw [neg_zero, if_pos rfl, hρW _ (sect_zero_mem Φ hWU hsurj hW hcard)]
    · intro c _ hc
      rw [if_neg (neg_ne_zero.2 hc), zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hne : ∑ a : Fq, e a ≠ 0 := by
    rw [hsum]; exact smul_ne_zero hq hu
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨a, e a, ha, fun σ hσ => ?_⟩
  simp only [e]
  rw [map_sum, Finset.smul_sum]
  simp_rw [map_smul, hshift σ hσ]
  refine Fintype.sum_equiv (Equiv.addLeft (Multiplicative.toAdd (Φ σ))) _ _ fun c => ?_
  simp only [Equiv.coe_addLeft, smul_smul]
  congr 1
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Twist form: `ρ ⊗ ψ(b Φ)` has nonzero `U`-invariants for some `b`. -/
theorem exists_fixd_twist_ne_bot (hρW : ∀ σ ∈ W, ∀ w : V, ρ σ w = w) (ψ : AddChar Fq k)
    (hψ : ψ.IsPrimitive) (hq : (Fintype.card Fq : k) ≠ 0) [Nontrivial V] :
    ∃ b : Fq, fixd (twist ρ ((ψ.mulShift b).toMonoidHom.comp Φ).toHomUnits) U ≠ ⊥ := by
  obtain ⟨a, w, hw, hσ⟩ := exists_eigen Φ hWU hsurj hW hcard ρ hρW ψ hψ hq
  refine ⟨-a, fun hbot => hw ?_⟩
  have hmem : w ∈ fixd (twist ρ ((ψ.mulShift (-a)).toMonoidHom.comp Φ).toHomUnits) U := by
    rw [mem_fixd]
    intro σ hσU
    rw [twist_apply, LinearMap.smul_apply, hσ σ hσU, smul_smul]
    have h1 : (((((ψ.mulShift (-a)).toMonoidHom.comp Φ).toHomUnits σ : kˣ) : k)) =
        ψ (-a * Multiplicative.toAdd (Φ σ)) := rfl
    rw [h1, ← AddChar.map_add_eq_mul, neg_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul]
  rw [hbot] at hmem
  exact (Submodule.mem_bot k).1 hmem

end Group

namespace RamFn

variable {G : Type*} [Group G] [Fintype G] (R : RamFn G)
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (ρ : Representation k G V)

/-- `φ(m-1) < 1 ≤ φ(m)` for `m = upperIdx 1`. -/
theorem phi_upperIdx_one : R.phi (R.upperIdx 1 - 1) < 1 ∧ 1 ≤ R.phi (R.upperIdx 1) := by
  have hm := R.one_le_upperIdx (x := 1) one_pos
  refine ⟨?_, (R.upperIdx_le_iff 1 _).1 le_rfl⟩
  by_contra h
  have := (R.upperIdx_le_iff 1 (R.upperIdx 1 - 1)).2 (not_lt.1 h)
  omega

/-- **Slope ≤ 1 with `G^1`-invariants**: `Sw(ρ) < dim V`. -/
theorem swan_lt_of_fixd (hB : R.BrkLE ρ 1) (hfix : fixd ρ (R.upper 1) ≠ ⊥) :
    R.swan ρ < finrank k V := by
  obtain ⟨hlt, hge⟩ := R.phi_upperIdx_one
  have hm1 : 1 ≤ R.upperIdx 1 := R.one_le_upperIdx one_pos
  have hfix0 : fixd ρ (R.lower (R.upperIdx 1)) ≠ ⊥ := hfix
  obtain ⟨m, hmdef⟩ : ∃ m, R.upperIdx 1 = m := ⟨_, rfl⟩
  rw [hmdef] at hlt hge hm1 hfix0
  have hcod_le : ∀ H : Subgroup G, (cod ρ H : ℚ) ≤ finrank k V := fun H => by
    have : cod ρ H ≤ finrank k V := Nat.sub_le _ _
    exact_mod_cast this
  have hfr : 1 ≤ finrank k (fixd ρ (R.lower m)) := by
    rw [Nat.one_le_iff_ne_zero]; intro h0
    exact hfix0 (Submodule.finrank_eq_zero.1 h0)
  have hfr' : finrank k (fixd ρ (R.lower m)) ≤ finrank k V := Submodule.finrank_le _
  have hcm : (cod ρ (R.lower m) : ℚ) + 1 ≤ finrank k V := by
    have : cod ρ (R.lower m) + 1 ≤ finrank k V := by unfold cod; omega
    exact_mod_cast this
  have htriv : ∀ j : ℕ, m + 1 ≤ j → cod ρ (R.lower j) = 0 := fun j hj => by
    have h1 : fixd ρ (R.lower (m + 1)) = ⊤ := by
      rw [← R.upper_phi]; exact hB _ (lt_of_le_of_lt hge (R.phi_lt_succ m))
    have h2 : fixd ρ (R.lower j) = ⊤ := eq_top_iff.2 (h1 ▸ fixd_anti ρ (R.lower_antitone hj))
    unfold cod; rw [h2, finrank_top, Nat.sub_self]
  have hcm0 : 1 < R.phi m → cod ρ (R.lower m) = 0 := fun h => by
    have h2 : fixd ρ (R.lower m) = ⊤ := by rw [← R.upper_phi]; exact hB _ h
    unfold cod; rw [h2, finrank_top, Nat.sub_self]
  have hd1 : (1 : ℚ) ≤ finrank k V := by exact_mod_cast hfr.trans hfr'
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (le_max_right R.top m)
  rw [R.swan_eq_phi ρ (le_max_left R.top m), ht, Finset.sum_range_add]
  have htail : ∑ x ∈ Finset.range t, (R.phi (m + x + 1) - R.phi (m + x)) * (cod ρ (R.lower (m + x + 1)) : ℚ) = 0 :=
    Finset.sum_eq_zero fun x _ => by rw [htriv _ (by omega), Nat.cast_zero, mul_zero]
  rw [htail, add_zero]
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  subst hm'
  rw [Finset.sum_range_succ]
  have hhead : ∑ x ∈ Finset.range m', (R.phi (x + 1) - R.phi x) * (cod ρ (R.lower (x + 1)) : ℚ) ≤
      R.phi m' * (finrank k V : ℚ) := by
    calc ∑ x ∈ Finset.range m', (R.phi (x + 1) - R.phi x) * (cod ρ (R.lower (x + 1)) : ℚ)
        ≤ ∑ x ∈ Finset.range m', (R.phi (x + 1) - R.phi x) * (finrank k V : ℚ) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hcod_le _)
            (sub_nonneg.2 (R.phi_lt_succ x).le)
      _ = R.phi m' * (finrank k V : ℚ) := by rw [← Finset.sum_mul, Finset.sum_range_sub (f := R.phi), R.phi_zero, sub_zero]
  have hm'1 : m' + 1 - 1 = m' := by omega
  rw [hm'1] at hlt
  have hpos : 0 < R.phi (m' + 1) - R.phi m' := sub_pos.2 (R.phi_lt_succ m')
  have hphi0 : 0 ≤ R.phi m' := by
    have := R.phi_ge m'; have : (0 : ℚ) ≤ m' / Nat.card G := by positivity
    linarith
  by_cases hc : cod ρ (R.lower (m' + 1)) = 0
  · rw [hc, Nat.cast_zero, mul_zero, add_zero]
    nlinarith
  · have hphi : R.phi (m' + 1) = 1 := le_antisymm (not_lt.1 fun h => hc (hcm0 h)) hge
    rw [hphi] at hpos ⊢
    nlinarith

end RamFn

namespace LocData

variable {G L : Type*} [Group G] [Field L] [MulSemiringAction G L] (D : LocData G L)

theorem natCast_le_toENat {n : ℕ} {w : WithTop ℤ} (h : (n : WithTop ℤ) ≤ w) : (n : ℕ∞) ≤ toENat w := by
  have := toENat_mono h
  rwa [← WithTop.coe_natCast, toENat_coe, Int.toNat_natCast] at this

theorem le_of_natCast_le_toENat {n : ℕ} (hn : 1 ≤ n) {w : WithTop ℤ} (h : (n : ℕ∞) ≤ toENat w) :
    (n : WithTop ℤ) ≤ w := by
  induction w with
  | top => exact le_top
  | coe z =>
    rw [toENat_coe, Nat.cast_le] at h
    rw [← WithTop.coe_natCast, WithTop.coe_le_coe]
    omega

theorem ϖ_ne_zero : D.ϖ ≠ 0 := fun h0 => by
  have h := D.v_ϖ
  rw [h0, AddValuation.map_zero] at h
  exact WithTop.top_ne_coe h

/-- `x = (x ϖ^{-n}) ϖ^n` and the valuation shift. -/
theorem v_shift (x : L) (n : ℕ) : D.v x = D.v (x * (D.ϖ ^ n)⁻¹) + (n : WithTop ℤ) := by
  have h : x = x * (D.ϖ ^ n)⁻¹ * D.ϖ ^ n := by
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero n D.ϖ_ne_zero), mul_one]
  conv_lhs => rw [h]
  rw [AddValuation.map_mul, AddValuation.map_pow, D.v_ϖ, nsmul_one]

theorem nonneg_shift {x : L} {n : ℕ} (h : (n : WithTop ℤ) ≤ D.v x) : 0 ≤ D.v (x * (D.ϖ ^ n)⁻¹) := by
  rw [D.v_shift x n, ← WithTop.coe_natCast] at h
  have h' : (0 : WithTop ℤ) + ((n : ℤ) : WithTop ℤ) ≤ D.v (x * (D.ϖ ^ n)⁻¹) + ((n : ℤ) : WithTop ℤ) := by
    rwa [zero_add]
  exact (WithTop.add_le_add_iff_right WithTop.coe_ne_top).1 h'

theorem shift_sub (x x' : L) (n : ℕ) :
    x * (D.ϖ ^ n)⁻¹ - x' * (D.ϖ ^ n)⁻¹ = (x - x') * (D.ϖ ^ n)⁻¹ := by ring

theorem le_of_one_le_shift {x : L} {n : ℕ} (h : 1 ≤ D.v (x * (D.ϖ ^ n)⁻¹)) :
    ((n + 1 : ℕ) : WithTop ℤ) ≤ D.v x := by
  rw [D.v_shift x n, ← WithTop.coe_natCast, ← WithTop.coe_natCast]
  have h' : (1 : WithTop ℤ) + ((n : ℤ) : WithTop ℤ) ≤ D.v (x * (D.ϖ ^ n)⁻¹) + ((n : ℤ) : WithTop ℤ) :=
    add_le_add h le_rfl
  calc (((n + 1 : ℕ) : ℤ) : WithTop ℤ) = (1 : WithTop ℤ) + ((n : ℤ) : WithTop ℤ) := by
        rw [← WithTop.coe_one, ← WithTop.coe_add]; congr 1; omega
    _ ≤ _ := h'

/-- **Residue bound**: `|G_m / G_{m+1}| ≤ |T|` for a map `red : L → T` separating residues of integers. -/
theorem card_lower_quot_le [Finite G] {T : Type*} [Finite T] (red : L → T)
    (hred : ∀ x x' : L, 0 ≤ D.v x → 0 ≤ D.v x' → red x = red x' → 1 ≤ D.v (x - x')) (m : ℕ) :
    Nat.card (D.ramFn.lower m ⧸ (D.ramFn.lower (m + 1)).subgroupOf (D.ramFn.lower m)) ≤ Nat.card T := by
  set U := D.ramFn.lower m
  let F : U → T := fun σ => red (((σ : G) • D.ϖ - D.ϖ) * (D.ϖ ^ (m + 1))⁻¹)
  have hint : ∀ σ : U, 0 ≤ D.v (((σ : G) • D.ϖ - D.ϖ) * (D.ϖ ^ (m + 1))⁻¹) := fun σ =>
    D.nonneg_shift (le_of_natCast_le_toENat (by omega) σ.2)
  have hF : ∀ σ τ : U, F σ = F τ → σ⁻¹ * τ ∈ (D.ramFn.lower (m + 1)).subgroupOf U := by
    intro σ τ h
    have h1 := hred _ _ (hint σ) (hint τ) h
    rw [D.shift_sub] at h1
    have h2 := D.le_of_one_le_shift h1
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, RamFn.mem_lower, LocData.ramFn_i]
    apply natCast_le_toENat
    have h3 : ((σ : G)⁻¹ * τ) • D.ϖ - D.ϖ = (σ : G)⁻¹ • ((τ : G) • D.ϖ - (σ : G) • D.ϖ) := by
      rw [smul_sub, mul_smul, inv_smul_smul]
    rw [h3, D.v_smul]
    have h4 : (τ : G) • D.ϖ - (σ : G) • D.ϖ = -(((σ : G) • D.ϖ - D.ϖ) - ((τ : G) • D.ϖ - D.ϖ)) := by ring
    rw [h4, AddValuation.map_neg]
    exact h2
  let g : U ⧸ (D.ramFn.lower (m + 1)).subgroupOf U → T := fun x => F x.out
  have hg : Function.Injective g := by
    intro x y hxy
    rw [← Quotient.out_eq' x, ← Quotient.out_eq' y]
    exact QuotientGroup.eq.2 (hF _ _ hxy)
  exact Nat.card_le_card_of_injective g hg

end LocData

end

end Swan
end RamanujanPetersson


