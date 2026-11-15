-- Prove2me | Definitions.Def_RPLib_S4_SwanLocQc
-- name    : RPLib_S4_SwanLocQc
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:26:01.743484+00:00
-- url     : https://prove2.me/theorems/2c908d2d-b4e5-42d4-a030-9d7f11991101
-- title:
--   The quotient ramification function and Herbrand's theorem for local data
-- statement:
--   For local data with group $G$ and a normal subgroup $H$, the fixed field of $H$ carries local data for $G/H$ with valuation normalised by $e_H = |H|$. Combining the quotient formula with descent, the file proves that the ramification function of $G/H$ satisfies $$i_{G/H}(\bar\sigma) = \frac{1}{|H|}\sum_{\tau \in \sigma H} i_G(\tau),$$ hence Herbrand's theorem $(G/H)^v = G^v H/H$ for local data, and that the Swan conductor of a representation inflated from $G/H$ is the Swan conductor computed with the local data of $G/H$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter IV, Sections 1 and 3

import Mathlib
import Definitions.Def_RPLib_S4_SwanLocQb
import Definitions.Def_RPLib_S4_SwanDesc
import Definitions.Def_RPLib_S4_SwanRepQ

/-!
# S4-Swan (K2), part 10: the quotient ramification function and Herbrand for local data

For `H ⊴ G` and `ϖH` with `D.QData H ϖH`, `nq σ = v(σ ϖH - ϖH)` is right-`H`-invariant, divisible by `|H|`
off `H`, and (quotient formula, part 9) `nq σ = ∑_{h ∈ H} i_G(σ h)`. So `i_{G/H}(σH) := nq σ / |H|` is a
`RamFn (G ⧸ H)` (`QData.ram`) satisfying Serre's `QuotFormula` (`QData.quotFormula`); hence Herbrand's theorem
`π(G^v) = (G/H)^v` (`QData.map_upper`) and `Sw_G(inf ρ) = Sw_{G/H}(ρ)` (`QData.swan_comp`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

theorem natCast_le_iff' {a b : ℕ} : ((a : ℕ) : WithTop ℤ) ≤ (b : WithTop ℤ) ↔ a ≤ b := by
  rw [← WithTop.coe_natCast, ← WithTop.coe_natCast, WithTop.coe_le_coe, Nat.cast_le]

theorem natCast_inj' {a b : ℕ} : ((a : ℕ) : WithTop ℤ) = (b : WithTop ℤ) ↔ a = b := by
  rw [← WithTop.coe_natCast, ← WithTop.coe_natCast, WithTop.coe_eq_coe, Nat.cast_inj]

theorem eq_natCast {w : WithTop ℤ} (h0 : 0 ≤ w) (ht : w ≠ ⊤) :
    w = ((toENat w).toNat : WithTop ℤ) := by
  induction w with
  | top => exact absurd rfl ht
  | coe a =>
    have ha : 0 ≤ a := by exact_mod_cast h0
    rw [toENat_coe, ENat.toNat_natCast, ← WithTop.coe_natCast, Int.toNat_of_nonneg ha]

namespace LocData

variable {G L : Type*} [Group G] [Field L] [MulSemiringAction G L] (D : LocData G L)

/-- `v(σ ϖH - ϖH)` as a natural number. -/
def nq (ϖH : L) (σ : G) : ℕ := (toENat (D.v (σ • ϖH - ϖH))).toNat

theorem nq_inv (ϖH : L) (σ : G) : D.nq ϖH σ⁻¹ = D.nq ϖH σ := by
  have : σ⁻¹ • ϖH - ϖH = σ⁻¹ • (ϖH - σ • ϖH) := by rw [smul_sub, inv_smul_smul]
  rw [nq, nq, this, D.v_smul, AddValuation.map_sub_swap]

variable {D} {H : Subgroup G} [Fintype H] {ϖH : L}

theorem QData.v_nonneg (hq : D.QData H ϖH) : 0 ≤ D.v ϖH := by
  rw [hq.v_eq]; exact_mod_cast Nat.zero_le _

theorem QData.fix_conj [H.Normal] (hq : D.QData H ϖH) (τ : G) : ∀ h ∈ H, h • τ • ϖH = τ • ϖH :=
  fun h hh => by
    have hc : τ⁻¹ * h * τ⁻¹⁻¹ ∈ H := ‹H.Normal›.conj_mem h hh τ⁻¹
    rw [smul_smul, show h * τ = τ * (τ⁻¹ * h * τ⁻¹⁻¹) by group, ← smul_smul, hq.fix _ hc]

theorem QData.conj [H.Normal] (hq : D.QData H ϖH) (τ : G) : D.QData H (τ • ϖH) :=
  ⟨hq.fix_conj τ, by rw [D.v_smul, hq.v_eq], hq.val⟩

/-- `v(σ ϖH - ϖH)` does not depend on the choice of `ϖH`. -/
theorem QData.v_indep {ϖ' : L} (hq : D.QData H ϖH) (hq' : D.QData H ϖ') (σ : G) :
    D.v (σ • ϖH - ϖH) = D.v (σ • ϖ' - ϖ') := by
  have he : 1 ≤ Fintype.card H := Fintype.card_pos
  exact le_antisymm (D.lb H _ he hq.fix hq.v_eq hq.resH σ hq'.fix hq'.v_nonneg)
    (D.lb H _ he hq'.fix hq'.v_eq hq'.resH σ hq.fix hq.v_nonneg)

theorem QData.nq_mul_right (hq : D.QData H ϖH) (σ : G) : ∀ h ∈ H, D.nq ϖH (σ * h) = D.nq ϖH σ :=
  fun h hh => by rw [nq, nq, mul_smul, hq.fix h hh]

theorem QData.nq_conj [H.Normal] (hq : D.QData H ϖH) (σ τ : G) :
    D.nq ϖH (τ * σ * τ⁻¹) = D.nq ϖH σ := by
  have : (τ * σ * τ⁻¹) • ϖH - ϖH = τ • (σ • (τ⁻¹ • ϖH) - τ⁻¹ • ϖH) := by
    rw [mul_smul, mul_smul, smul_sub, smul_inv_smul]
  rw [nq, nq, this, D.v_smul, (hq.conj τ⁻¹).v_indep hq σ]

theorem QData.v_eq_nq [H.Normal] (hq : D.QData H ϖH) {σ : G} (hσ : σ ∉ H) :
    D.v (σ • ϖH - ϖH) = (D.nq ϖH σ : WithTop ℤ) :=
  eq_natCast (D.v_sub_smul_nonneg σ hq.v_nonneg) (hq.v_ne_top hσ)

theorem QData.card_le_nq [H.Normal] (hq : D.QData H ϖH) {σ : G} (hσ : σ ∉ H) :
    Fintype.card H ≤ D.nq ϖH σ := by
  have h := D.v.map_le_sub (x := σ • ϖH) (y := ϖH) (g := ((Fintype.card H : ℕ) : WithTop ℤ))
    (by rw [D.v_smul, hq.v_eq]) (by rw [hq.v_eq])
  rw [hq.v_eq_nq hσ] at h
  exact natCast_le_iff'.1 h

theorem QData.dvd_nq [H.Normal] (hq : D.QData H ϖH) {σ : G} (hσ : σ ∉ H) :
    Fintype.card H ∣ D.nq ϖH σ := by
  have hfix : ∀ h ∈ H, h • (σ • ϖH - ϖH) = σ • ϖH - ϖH := fun h hh => by
    rw [smul_sub, hq.fix_conj σ h hh, hq.fix h hh]
  obtain ⟨k, hk⟩ := hq.val _ hfix (fun h => hq.v_ne_top hσ ((D.v.top_iff).2 h))
  rw [hq.v_eq_nq hσ, ← WithTop.coe_natCast, WithTop.coe_eq_coe] at hk
  exact Int.natCast_dvd_natCast.1 ⟨k, hk⟩

theorem QData.nq_mul [H.Normal] (hq : D.QData H ϖH) {σ τ : G} (hσ : σ ∉ H) (hτ : τ ∉ H)
    (hστ : σ * τ ∉ H) : min (D.nq ϖH σ) (D.nq ϖH τ) ≤ D.nq ϖH (σ * τ) := by
  have h : σ • (τ • ϖH - ϖH) + (σ • ϖH - ϖH) = (σ * τ) • ϖH - ϖH := by
    rw [mul_smul, smul_sub]; ring
  have h2 := D.v.map_add (σ • (τ • ϖH - ϖH)) (σ • ϖH - ϖH)
  rw [h, D.v_smul, hq.v_eq_nq hσ, hq.v_eq_nq hτ, hq.v_eq_nq hστ] at h2
  rcases le_total (D.nq ϖH σ) (D.nq ϖH τ) with hle | hle
  · rw [min_eq_right (natCast_le_iff'.2 hle)] at h2
    rw [min_eq_left hle]; exact natCast_le_iff'.1 h2
  · rw [min_eq_left (natCast_le_iff'.2 hle)] at h2
    rw [min_eq_right hle]; exact natCast_le_iff'.1 h2

/-- `nq σ = ∑_{h ∈ H} i_G(σ h)` (the quotient formula in `ℕ`). -/
theorem QData.nq_sum [H.Normal] (hq : D.QData H ϖH) {σ : G} (hσ : σ ∉ H) :
    D.nq ϖH σ = ∑ h : H, (D.ramFn.i (σ * h)).toNat := by
  have h1 := hq.v_quot hσ
  rw [hq.v_eq_nq hσ] at h1
  have h2 : ∀ h : H, D.v ((σ * h) • D.ϖ - D.ϖ) = ((D.ramFn.i (σ * h)).toNat : WithTop ℤ) := by
    intro h
    rw [ramFn_i]
    refine eq_natCast (D.v_sub_smul_nonneg _ (by rw [D.v_ϖ]; exact zero_le_one)) fun ht => ?_
    have h3 := D.eq_one_of_fix_ϖ (sub_eq_zero.1 ((D.v.top_iff).1 ht))
    rw [mul_eq_one_iff_eq_inv] at h3
    exact hσ (h3 ▸ H.inv_mem h.2)
  rw [Finset.sum_congr rfl fun h _ => h2 h, ← Nat.cast_sum] at h1
  exact natCast_inj'.1 h1

/-- The ramification function of `G ⧸ H`: `i(σH) = v(σ ϖH - ϖH) / |H|`. -/
def QData.ram [H.Normal] (hq : D.QData H ϖH) : RamFn (G ⧸ H) :=
  RamFn.desc H (fun σ => D.nq ϖH σ / Fintype.card H)
    (fun σ h hh => by simp only [hq.nq_mul_right σ h hh])
    (fun σ hσ => (Nat.le_div_iff_mul_le Fintype.card_pos).2 (by rw [one_mul]; exact hq.card_le_nq hσ))
    (fun σ τ hσ hτ hστ => by
      have h := hq.nq_mul hσ hτ hστ
      rcases le_total (D.nq ϖH σ) (D.nq ϖH τ) with hle | hle
      · rw [min_eq_left hle] at h
        exact (min_le_left _ _).trans (Nat.div_le_div_right h)
      · rw [min_eq_right hle] at h
        exact (min_le_right _ _).trans (Nat.div_le_div_right h))
    (fun σ => by simp only [nq_inv])
    (fun σ τ => by simp only [hq.nq_conj])

theorem QData.ram_i_mk [H.Normal] (hq : D.QData H ϖH) {σ : G} (hσ : σ ∉ H) :
    hq.ram.i (σ : G ⧸ H) = ((D.nq ϖH σ / Fintype.card H : ℕ) : ℕ∞) :=
  RamFn.desc_i_mk H _ _ _ _ _ _ hσ

theorem sum_fib_mk [H.Normal] [Fintype G] [DecidableEq (G ⧸ H)] {M : Type*} [AddCommMonoid M] (σ : G)
    (g : G → M) : ∑ τ ∈ RamFn.fib (QuotientGroup.mk' H) (σ : G ⧸ H), g τ = ∑ h : H, g (σ * h) := by
  symm
  refine Finset.sum_bij (fun h _ => σ * h) (fun h _ => ?_) (fun a _ b _ hab => ?_)
    (fun τ hτ => ?_) (fun _ _ => rfl)
  · simp only [RamFn.fib, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq, mul_inv_rev, inv_mul_cancel_right]
    exact H.inv_mem h.2
  · exact Subtype.ext (mul_left_cancel hab)
  · simp only [RamFn.fib, Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    rw [QuotientGroup.mk'_apply] at hτ
    exact ⟨⟨σ⁻¹ * τ, QuotientGroup.eq.1 hτ.symm⟩, Finset.mem_univ _, mul_inv_cancel_left _ _⟩

/-- **Serre IV §1 Prop 3** for local data: `(D.ramFn, hq.ram)` satisfy the quotient formula. -/
theorem QData.quotFormula [H.Normal] [Fintype G] [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)]
    (hq : D.QData H ϖH) : RamFn.QuotFormula D.ramFn hq.ram (QuotientGroup.mk' H) := by
  intro s
  refine QuotientGroup.induction_on s fun σ hs => ?_
  have hσ : σ ∉ H := fun h => hs ((QuotientGroup.eq_one_iff σ).2 h)
  rw [hq.ram_i_mk hσ, ENat.toNat_natCast, QuotientGroup.ker_mk', Nat.card_eq_fintype_card,
    Nat.div_mul_cancel (hq.dvd_nq hσ), hq.nq_sum hσ, sum_fib_mk]

/-- **Herbrand's theorem** for local data: `(G^v)H/H = (G/H)^v`. -/
theorem QData.map_upper [H.Normal] [Fintype G] [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)]
    (hq : D.QData H ϖH) (v : ℚ) : (D.ramFn.upper v).map (QuotientGroup.mk' H) = hq.ram.upper v :=
  RamFn.map_upper D.ramFn hq.ram (QuotientGroup.mk'_surjective H) hq.quotFormula v

/-- The Swan conductor is compatible with inflation from `G ⧸ H`. -/
theorem QData.swan_comp [H.Normal] [Fintype G] [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)]
    (hq : D.QData H ϖH) {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k (G ⧸ H) W) :
    D.ramFn.swan (ρ.comp (QuotientGroup.mk' H)) = hq.ram.swan ρ :=
  RamFn.swan_comp D.ramFn hq.ram ρ (QuotientGroup.mk'_surjective H) hq.quotFormula

end LocData

end

end Swan
end RamanujanPetersson


