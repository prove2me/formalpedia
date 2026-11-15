-- Prove2me | Definitions.Def_RPLib_S4_SwanLoc
-- name    : RPLib_S4_SwanLoc
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:18:29.302544+00:00
-- url     : https://prove2.me/theorems/0cc1f74b-9189-4254-8118-e502d57488e5
-- title:
--   Totally ramified local data and their ramification functions
-- statement:
--   Local data consist of a field $L$ with a discrete valuation $v$ (values in $\mathbb{Z} \cup \{\infty\}$), a uniformiser $\varpi$ and a finite group $G$ acting on $L$ by valuation-preserving automorphisms that act trivially on the residue field, with $\varpi$ generating the valuation ring over the fixed part (the totally ramified case). The file shows that $$i(\sigma) = v(\sigma\varpi - \varpi)$$ is a ramification function on $G$ (independent of the uniformiser) and that $v(\sigma x - x) \ge i(\sigma)$ for every integral $x$, so the lower ramification groups are $G_u = \{\sigma : v(\sigma x - x) \ge u + 1 \text{ for all integral } x\}$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter IV, Section 1

import Mathlib
import Definitions.Def_RPLib_S4_SwanHerb

/-!
# S4-Swan (K2), part 6: local totally ramified data give a ramification function

`LocData G L`: a finite group `G` acting faithfully on a field `L`, a `G`-invariant discrete valuation
`v : L → ℤ ∪ {⊤}` with a uniformizer `ϖ` (`v ϖ = 1`), and the residue condition `res`: every integral `x` is
congruent mod `𝔭` to a `G`-invariant element (residue field of `L^G` = residue field of `L`, `G` acts trivially on it).
No completeness and no monogenicity are assumed: `res` gives the successive approximation that replaces
`B = A[ϖ]` (Serre, Local Fields IV §1). Then (`lb`) `v(σ ϖ_H - ϖ_H) ≤ v(σ x - x)` for every integral `H`-invariant
`x` and every element `ϖ_H` of `L^H` of minimal valuation, so `i(σ) = v(σ ϖ - ϖ)` is independent of `ϖ` and
defines a `RamFn G` (`LocData.ramFn`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

/-- `ℤ ∪ {⊤} → ℕ∞`, truncating negatives. -/
def toENat (w : WithTop ℤ) : ℕ∞ := WithTop.map Int.toNat w

theorem toENat_top : toENat ⊤ = ⊤ := rfl

theorem toENat_coe (m : ℤ) : toENat (m : WithTop ℤ) = (m.toNat : ℕ∞) := rfl

theorem toENat_eq_top_iff (w : WithTop ℤ) : toENat w = ⊤ ↔ w = ⊤ := WithTop.map_eq_top_iff

theorem toENat_mono : Monotone toENat := by
  intro a b h
  induction b with
  | top => rw [toENat_top]; exact le_top
  | coe b =>
    induction a with
    | top => exact absurd h (by simp)
    | coe a =>
      rw [toENat_coe, toENat_coe]
      exact_mod_cast Int.toNat_le_toNat (WithTop.coe_le_coe.1 h)

theorem eq_top_of_forall_nat_le {w : WithTop ℤ} (h : ∀ n : ℕ, (n : WithTop ℤ) ≤ w) : w = ⊤ := by
  induction w with
  | top => rfl
  | coe m =>
    exfalso
    have := h (m.toNat + 1)
    rw [← WithTop.coe_natCast, WithTop.coe_le_coe] at this
    omega

variable (G L : Type*) [Group G] [Field L] [MulSemiringAction G L]

/-- Local totally ramified data (see the module docstring). -/
structure LocData where
  v : AddValuation L (WithTop ℤ)
  v_smul : ∀ (σ : G) (x : L), v (σ • x) = v x
  faithful : ∀ σ : G, (∀ x : L, σ • x = x) → σ = 1
  ϖ : L
  v_ϖ : v ϖ = 1
  res : ∀ x : L, 0 ≤ v x → ∃ a : L, (∀ σ : G, σ • a = a) ∧ 1 ≤ v (x - a)

namespace LocData

variable {G L} (D : LocData G L)

theorem v_sub_smul_nonneg (σ : G) {x : L} (hx : 0 ≤ D.v x) : 0 ≤ D.v (σ • x - x) :=
  D.v.map_le_sub (by rw [D.v_smul]; exact hx) hx

/-- Successive approximation through `res`, the key estimate: for `ϖH ∈ L^H` with `v ϖH = e` and `res` at
level `e` on `L^H`, `v(σ ϖH - ϖH) ≤ v(σ x - x)` for integral `x ∈ L^H`. -/
theorem lb (H : Subgroup G) (e : ℕ) (he : 1 ≤ e) {ϖH : L} (hfix : ∀ h ∈ H, h • ϖH = ϖH)
    (hv : D.v ϖH = e)
    (resH : ∀ x : L, (∀ h ∈ H, h • x = x) → 0 ≤ D.v x →
      ∃ a : L, (∀ σ : G, σ • a = a) ∧ (e : WithTop ℤ) ≤ D.v (x - a))
    (σ : G) {x : L} (hxH : ∀ h ∈ H, h • x = x) (hx : 0 ≤ D.v x) :
    D.v (σ • ϖH - ϖH) ≤ D.v (σ • x - x) := by
  set V := D.v (σ • ϖH - ϖH)
  have hne : ϖH ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hv
    exact WithTop.top_ne_coe hv
  have hϖ0 : 0 ≤ D.v ϖH := by rw [hv]; exact_mod_cast Nat.zero_le e
  have hV0 : 0 ≤ V := D.v_sub_smul_nonneg σ hϖ0
  have step : ∀ n : ℕ, ∀ x : L, (∀ h ∈ H, h • x = x) → 0 ≤ D.v x →
      min V (n : WithTop ℤ) ≤ D.v (σ • x - x) := by
    intro n
    induction n with
    | zero =>
      intro x _ hx
      exact (min_le_right _ _).trans (by exact_mod_cast D.v_sub_smul_nonneg σ hx)
    | succ n ih =>
      intro x hxH hx
      obtain ⟨a, ha, hva⟩ := resH x hxH hx
      set y := (x - a) * ϖH⁻¹ with hy
      have hxy : x = a + ϖH * y := by rw [hy]; field_simp; ring
      have hyH : ∀ h ∈ H, h • y = y := fun h hh => by
        rw [hy, smul_mul', smul_sub, smul_inv'', hxH h hh, ha h, hfix h hh]
      have hy0 : 0 ≤ D.v y := by
        have h1 : D.v (x - a) = e + D.v y := by
          rw [show x - a = ϖH * y by rw [hxy]; ring, AddValuation.map_mul, hv]
        rw [h1] at hva
        have h2 : (e : WithTop ℤ) + 0 ≤ (e : WithTop ℤ) + D.v y := by rwa [add_zero]
        exact (WithTop.add_le_add_iff_left (WithTop.natCast_ne_top e)).1 h2
      have hσx : σ • x - x = (σ • ϖH - ϖH) * (σ • y) + ϖH * (σ • y - y) := by
        rw [hxy, smul_add, smul_mul', ha σ]; ring
      rw [hσx]
      refine le_trans ?_ (D.v.map_add _ _)
      refine le_min ?_ ?_
      · rw [AddValuation.map_mul, D.v_smul]
        exact (min_le_left _ _).trans (le_add_of_nonneg_right hy0)
      · rw [AddValuation.map_mul, hv]
        have := ih y hyH hy0
        calc min V ((n + 1 : ℕ) : WithTop ℤ) ≤ (e : WithTop ℤ) + min V (n : WithTop ℤ) := by
              rcases min_choice V (n : WithTop ℤ) with h | h <;> rw [h]
              · exact (min_le_left _ _).trans (le_add_of_nonneg_left (by exact_mod_cast Nat.zero_le e))
              · refine (min_le_right _ _).trans ?_
                rw [← Nat.cast_add]; exact_mod_cast (by omega : n + 1 ≤ e + n)
          _ ≤ (e : WithTop ℤ) + D.v (σ • y - y) := add_le_add le_rfl this
  rcases eq_or_ne V ⊤ with hVt | hVt
  · have hall : ∀ n : ℕ, (n : WithTop ℤ) ≤ D.v (σ • x - x) := fun n => by
      have h := step n x hxH hx
      rwa [hVt, min_eq_right le_top] at h
    rw [eq_top_of_forall_nat_le hall]; exact le_top
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hVt
    have hm0 : 0 ≤ m := by rw [← hm] at hV0; exact_mod_cast hV0
    have h := step m.toNat x hxH hx
    have hc : ((m.toNat : ℕ) : WithTop ℤ) = (m : WithTop ℤ) := by
      rw [← WithTop.coe_natCast, Int.toNat_of_nonneg hm0]
    rw [← hm, hc, min_self] at h
    rw [← hm]; exact h

theorem mem_bot_fix (x : L) : ∀ h ∈ (⊥ : Subgroup G), h • x = x := fun h hh => by
  rw [Subgroup.mem_bot.1 hh, one_smul]

/-- `v(σ ϖ - ϖ) ≤ v(σ x - x)` for all integral `x`, for any uniformizer `ϖ'`. -/
theorem lb_bot {ϖ' : L} (hv : D.v ϖ' = 1) (σ : G) {x : L} (hx : 0 ≤ D.v x) :
    D.v (σ • ϖ' - ϖ') ≤ D.v (σ • x - x) :=
  D.lb ⊥ 1 le_rfl (mem_bot_fix ϖ') (by rw [hv]; rfl)
    (fun x _ hx => by obtain ⟨a, ha, h⟩ := D.res x hx; exact ⟨a, ha, by exact_mod_cast h⟩) σ
    (mem_bot_fix x) hx

/-- Independence of the uniformizer. -/
theorem v_unif_eq {ϖ₁ ϖ₂ : L} (h₁ : D.v ϖ₁ = 1) (h₂ : D.v ϖ₂ = 1) (σ : G) :
    D.v (σ • ϖ₁ - ϖ₁) = D.v (σ • ϖ₂ - ϖ₂) :=
  le_antisymm (D.lb_bot h₁ σ (by rw [h₂]; exact zero_le_one))
    (D.lb_bot h₂ σ (by rw [h₁]; exact zero_le_one))

theorem v_inv_nonneg {x : L} (hx : D.v x < 0) : 0 ≤ D.v x⁻¹ := by
  rw [AddValuation.map_inv]
  induction hvx : D.v x with
  | top => rw [hvx] at hx; exact absurd hx (not_lt.2 le_top)
  | coe m =>
    rw [hvx] at hx
    have : m < 0 := by exact_mod_cast hx
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
    exact_mod_cast (by omega : (0 : ℤ) ≤ -m)

theorem eq_one_of_fix_ϖ {σ : G} (h : σ • D.ϖ = D.ϖ) : σ = 1 := by
  have hO : ∀ x : L, 0 ≤ D.v x → σ • x = x := fun x hx => by
    have := D.lb_bot D.v_ϖ σ hx
    rw [h, sub_self, AddValuation.map_zero, top_le_iff, AddValuation.top_iff] at this
    exact sub_eq_zero.1 this
  refine D.faithful σ fun x => ?_
  rcases le_or_gt 0 (D.v x) with hx | hx
  · exact hO x hx
  · have := hO x⁻¹ (D.v_inv_nonneg hx)
    rw [smul_inv''] at this
    exact inv_injective this

/-- The ramification function `i(σ) = v(σ ϖ - ϖ)`. -/
def ramFn : RamFn G where
  i σ := toENat (D.v (σ • D.ϖ - D.ϖ))
  i_eq_top σ := by
    rw [toENat_eq_top_iff, AddValuation.top_iff, sub_eq_zero]
    exact ⟨D.eq_one_of_fix_ϖ, fun h => by rw [h, one_smul]⟩
  one_le σ := by
    have : (1 : WithTop ℤ) ≤ D.v (σ • D.ϖ - D.ϖ) :=
      D.v.map_le_sub (by rw [D.v_smul, D.v_ϖ]) (by rw [D.v_ϖ])
    have h2 := toENat_mono this
    rwa [show toENat 1 = 1 from rfl] at h2
  le_mul σ τ := by
    rw [← toENat_mono.map_min]
    apply toENat_mono
    have : (σ * τ) • D.ϖ - D.ϖ = σ • (τ • D.ϖ - D.ϖ) + (σ • D.ϖ - D.ϖ) := by
      rw [mul_smul, smul_sub]; ring
    rw [this, min_comm]
    refine le_trans ?_ (D.v.map_add _ _)
    rw [D.v_smul]
  i_inv σ := by
    congr 1
    have : σ⁻¹ • D.ϖ - D.ϖ = σ⁻¹ • (D.ϖ - σ • D.ϖ) := by
      rw [smul_sub, inv_smul_smul]
    rw [this, D.v_smul, AddValuation.map_sub_swap]
  i_conj σ τ := by
    congr 1
    have : (τ * σ * τ⁻¹) • D.ϖ - D.ϖ = τ • (σ • (τ⁻¹ • D.ϖ) - τ⁻¹ • D.ϖ) := by
      rw [mul_smul, mul_smul, smul_sub, smul_inv_smul]
    rw [this, D.v_smul]
    exact D.v_unif_eq (by rw [D.v_smul, D.v_ϖ]) D.v_ϖ σ

theorem ramFn_i (σ : G) : D.ramFn.i σ = toENat (D.v (σ • D.ϖ - D.ϖ)) := rfl

/-- `i(σ)` through any uniformizer. -/
theorem ramFn_i_of_unif {ϖ' : L} (h : D.v ϖ' = 1) (σ : G) :
    D.ramFn.i σ = toENat (D.v (σ • ϖ' - ϖ')) := by
  rw [ramFn_i, D.v_unif_eq D.v_ϖ h]

end LocData

end

end Swan
end RamanujanPetersson


