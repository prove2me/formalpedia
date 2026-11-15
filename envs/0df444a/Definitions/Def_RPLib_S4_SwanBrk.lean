-- Prove2me | Definitions.Def_RPLib_S4_SwanBrk
-- name    : RPLib_S4_SwanBrk
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:25:38.288872+00:00
-- url     : https://prove2.me/theorems/7b1bd875-2116-4269-bbaa-4766978f1d0c
-- title:
--   Breaks of a representation, twists by characters, and totally wild representations
-- statement:
--   For a representation $\rho$ of a group $G$ with a ramification function, $\rho$ has all breaks $\le b$ if the upper ramification groups $G^v$ act trivially for all $v > b$, and all breaks $= b$ if moreover $V^{G^v} = 0$ for $v \le b$ (and $v > 0$). The file defines these conditions, the twist $\rho \otimes \chi$ by a character, and proves the standard facts: $$\text{all breaks} \le b \implies \mathrm{Sw}(\rho) \le b \dim \rho, \qquad \text{all breaks} = b \implies \mathrm{Sw}(\rho) = b \dim \rho,$$ and that twisting by a character with all breaks $b$ larger than the breaks of $\rho$ gives a representation with all breaks $b$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), Chapter 1 (breaks and Swan conductors); J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter VI

import Mathlib
import Definitions.Def_RPLib_S4_SwanRepQ

/-!
# S4-Swan (K2), part 5: breaks, twists by characters, totally wild representations

Break conditions through the upper numbering (Katz, Gauss sums, Kloosterman sums and monodromy, 1.0-1.1):
* `BrkLE ρ x` : all breaks `≤ x` (`G^v` acts trivially for `v > x`);
* `BrkGT ρ x` : all breaks `> x` (`V^{G^v} = 0` for some `v > x`);
* `AllBrk ρ x` : all breaks equal `x`.
Results: every break is `≤ Sw` (`brkLE_swan`); `Sw = x dim V` when all breaks are `x > 0` (`swan_of_allBrk`);
twisting by a character `χ` with all breaks `x > Sw(ρ)` gives all breaks `x` (`allBrk_twist`, `swan_twist`,
Katz p.13), and then `V^{G_1} = 0` (totally wild) and the `G_1`-coinvariants vanish (`span_sub_eq_top`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

open Module

/-- Twist of a representation by a character `χ : G → kˣ` (`ρ ⊗ χ` on the same space). -/
def twist {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (χ : G →* kˣ) : Representation k G V where
  toFun σ := ((χ σ : kˣ) : k) • ρ σ
  map_one' := by simp
  map_mul' σ τ := by
    simp only [map_mul, Units.val_mul]
    rw [smul_mul_smul_comm]

theorem twist_apply {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (χ : G →* kˣ) (σ : G) : twist ρ χ σ = ((χ σ : kˣ) : k) • ρ σ := rfl

namespace RamFn

variable {G : Type*} [Group G] [Fintype G] (R : RamFn G)

theorem upperIdx_phi (n : ℕ) : R.upperIdx (R.phi n) = n :=
  le_antisymm ((R.upperIdx_le_iff _ n).2 le_rfl) (R.phi_le_iff.1 ((R.upperIdx_le_iff _ _).1 le_rfl))

theorem upper_phi (n : ℕ) : R.upper (R.phi n) = R.lower n := by
  rw [upper, upperIdx_phi]

theorem one_le_upperIdx {x : ℚ} (hx : 0 < x) : 1 ≤ R.upperIdx x := by
  by_contra h
  have := (R.upperIdx_le_iff x 0).1 (by omega)
  rw [R.phi_zero] at this
  linarith

theorem upper_le_lower_one {x : ℚ} (hx : 0 < x) : R.upper x ≤ R.lower 1 :=
  R.lower_antitone (R.one_le_upperIdx hx)

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- All breaks are `≤ x`. -/
def BrkLE (x : ℚ) : Prop := ∀ v : ℚ, x < v → fixd ρ (R.upper v) = ⊤

/-- All breaks are `> x`. -/
def BrkGT (x : ℚ) : Prop := ∃ v : ℚ, x < v ∧ fixd ρ (R.upper v) = ⊥

/-- All breaks equal `x`. -/
def AllBrk (x : ℚ) : Prop := R.BrkLE ρ x ∧ fixd ρ (R.upper x) = ⊥

theorem le_swan_of_fixd_ne_top [FiniteDimensional k V] {v : ℚ} (h : fixd ρ (R.upper v) ≠ ⊤) :
    v ≤ R.swan ρ := by
  set m := R.upperIdx v
  have hv : v ≤ R.phi m := (R.upperIdx_le_iff v m).1 le_rfl
  have hc : 1 ≤ cod ρ (R.lower m) := by
    have := Submodule.finrank_lt h
    unfold cod
    change 1 ≤ finrank k V - finrank k (fixd ρ (R.upper v))
    omega
  have hΔ : ∀ u : ℕ, 0 ≤ R.phi (u + 1) - R.phi u := fun u => by linarith [R.phi_lt_succ u]
  rw [R.swan_eq_phi ρ (le_max_left R.top m)]
  calc v ≤ R.phi m := hv
    _ = ∑ u ∈ Finset.range m, (R.phi (u + 1) - R.phi u) * (1 : ℕ) := by
        rw [Nat.cast_one]; simp only [mul_one]
        rw [Finset.sum_range_sub R.phi m, R.phi_zero, sub_zero]
    _ ≤ ∑ u ∈ Finset.range m, (R.phi (u + 1) - R.phi u) * cod ρ (R.lower (u + 1)) := by
        refine Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left ?_ (hΔ u)
        have : u + 1 ≤ m := Finset.mem_range.1 hu
        exact_mod_cast hc.trans (cod_mono ρ (R.lower_antitone this))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (le_max_right _ _)) fun u _ _ => mul_nonneg (hΔ u) (by positivity)

/-- Every break is at most the Swan conductor. -/
theorem brkLE_swan [FiniteDimensional k V] : R.BrkLE ρ (R.swan ρ) := fun v hv => by
  by_contra h
  have := R.le_swan_of_fixd_ne_top ρ h
  linarith

/-- If all breaks equal `x > 0` then `Sw = x dim V`. -/
theorem swan_of_allBrk [FiniteDimensional k V] {x : ℚ} (_hx : 0 < x) (h : R.AllBrk ρ x) :
    R.swan ρ = x * finrank k V := by
  set m := R.upperIdx x
  have hxm : x ≤ R.phi m := (R.upperIdx_le_iff x m).1 le_rfl
  have hbot : fixd ρ (R.lower m) = ⊥ := h.2
  rcases eq_or_lt_of_le hxm with heq | hlt
  · rw [R.swan_eq_phi ρ (le_max_left R.top m)]
    have hterm : ∀ u ∈ Finset.range (max R.top m), (R.phi (u + 1) - R.phi u) * (cod ρ (R.lower (u + 1)) : ℚ)
        = if u < m then (R.phi (u + 1) - R.phi u) * finrank k V else 0 := by
      intro u _
      split_ifs with hu
      · have hf : fixd ρ (R.lower (u + 1)) = ⊥ :=
          eq_bot_iff.2 (hbot ▸ fixd_anti ρ (R.lower_antitone (show u + 1 ≤ m by omega)))
        rw [cod, hf, finrank_bot, Nat.sub_zero]
      · have hlt' : x < R.phi (u + 1) := heq ▸ R.phi_strictMono (show m < u + 1 by omega)
        have hf : fixd ρ (R.lower (u + 1)) = ⊤ := by
          rw [← R.upper_phi]; exact h.1 _ hlt'
        rw [cod, hf, finrank_top, Nat.sub_self]
        simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    have hfil : (Finset.range (max R.top m)).filter (fun u => u < m) = Finset.range m := by
      ext u; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfil, ← Finset.sum_mul, Finset.sum_range_sub R.phi m, R.phi_zero, sub_zero, ← heq]
  · have htop : fixd ρ (R.lower m) = ⊤ := by
      rw [← R.upper_phi]; exact h.1 _ hlt
    have hd : finrank k V = 0 := by
      rw [← finrank_top k V, ← htop, hbot, finrank_bot]
    rw [hd]
    unfold swan
    simp [cod, hd]

/-- All breaks `x > 0` forces `V^{G_1} = 0` (totally wild). -/
theorem fixd_lower_one_of_allBrk {x : ℚ} (hx : 0 < x) (h : R.AllBrk ρ x) : fixd ρ (R.lower 1) = ⊥ :=
  eq_bot_iff.2 ((fixd_anti ρ (R.upper_le_lower_one hx)).trans h.2.le)

/-- `χ` has all breaks `x`: trivial on `G^v` for `v > x`, nontrivial on `G^x`. -/
def ChiAllBrk (χ : G →* kˣ) (x : ℚ) : Prop :=
  (∀ v : ℚ, x < v → ∀ σ ∈ R.upper v, χ σ = 1) ∧ ∃ σ ∈ R.upper x, χ σ ≠ 1

/-- Katz p.13: if `G^x` acts trivially on `V` and `χ` has all breaks `x`, then `V ⊗ χ` has all breaks `x`. -/
theorem allBrk_twist (χ : G →* kˣ) {x : ℚ} (hρ : fixd ρ (R.upper x) = ⊤) (hχ : R.ChiAllBrk χ x) :
    R.AllBrk (twist ρ χ) x := by
  have hfix : ∀ σ ∈ R.upper x, ∀ w : V, ρ σ w = w := fun σ hσ w =>
    (mem_fixd ρ).1 (hρ ▸ Submodule.mem_top) σ hσ
  constructor
  · intro v hv
    rw [eq_top_iff]
    intro w _
    rw [mem_fixd]
    intro σ hσ
    rw [twist_apply, hχ.1 v hv σ hσ, Units.val_one, one_smul]
    exact hfix σ (R.upper_antitone hv.le hσ) w
  · obtain ⟨σ, hσ, hχσ⟩ := hχ.2
    rw [eq_bot_iff]
    intro w hw
    have h1 := (mem_fixd _).1 hw σ hσ
    rw [twist_apply, LinearMap.smul_apply, hfix σ hσ w] at h1
    have h2 : (((χ σ : kˣ) : k) - 1) • w = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd (Units.val_eq_one.1 (sub_eq_zero.1 h3)) hχσ
    · rw [h3]; exact Submodule.zero_mem _

/-- Katz p.13: `Sw(V ⊗ χ) = x dim V` when `χ` has all breaks `x > Sw(V)`. -/
theorem swan_twist [FiniteDimensional k V] (χ : G →* kˣ) {x : ℚ} (hx : 0 < x) (hρ : R.swan ρ < x)
    (hχ : R.ChiAllBrk χ x) : R.swan (twist ρ χ) = x * finrank k V :=
  R.swan_of_allBrk _ hx (R.allBrk_twist ρ χ (R.brkLE_swan ρ x hρ) hχ)

theorem allBrk_twist_of_lt [FiniteDimensional k V] (χ : G →* kˣ) {x : ℚ} (hρ : R.swan ρ < x)
    (hχ : R.ChiAllBrk χ x) : R.AllBrk (twist ρ χ) x :=
  R.allBrk_twist ρ χ (R.brkLE_swan ρ x hρ) hχ

/-- Totally wild: `(V ⊗ χ)^{G_1} = 0`. -/
theorem fixd_twist_lower_one [FiniteDimensional k V] (χ : G →* kˣ) {x : ℚ} (hx : 0 < x)
    (hρ : R.swan ρ < x) (hχ : R.ChiAllBrk χ x) : fixd (twist ρ χ) (R.lower 1) = ⊥ :=
  R.fixd_lower_one_of_allBrk _ hx (R.allBrk_twist_of_lt ρ χ hρ hχ)

end RamFn

/-- Coinvariants vanish when invariants do (`|H|` invertible): `V = span {ρ σ v - v : σ ∈ H}`. -/
theorem span_sub_eq_top {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) [Fintype H] (hc : (Fintype.card H : k) ≠ 0)
    (h : fixd ρ H = ⊥) : Submodule.span k {w | ∃ σ ∈ H, ∃ v, w = ρ σ v - v} = ⊤ := by
  let _ : Invertible (Fintype.card H : k) := invertibleOfNonzero hc
  rw [eq_top_iff]
  intro v _
  have h0 : Representation.averageMap (ρ.comp H.subtype) v = 0 := by
    have := Representation.averageMap_invariant (ρ.comp H.subtype) v
    rw [← fixd, h] at this
    exact (Submodule.mem_bot k).1 this
  have hav : Representation.averageMap (ρ.comp H.subtype) v = ⅟(Fintype.card H : k) • ∑ τ : H, ρ τ v := by
    simp [Representation.averageMap, GroupAlgebra.average, map_sum]
  have hv : v = -(⅟(Fintype.card H : k) • ∑ τ : H, (ρ τ v - v)) := by
    rw [Finset.sum_sub_distrib, smul_sub, ← hav, h0, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul k, smul_smul, invOf_mul_self, one_smul, zero_sub, neg_neg]
  rw [hv]
  refine Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun τ _ => ?_))
  exact Submodule.subset_span ⟨τ, τ.2, v, rfl⟩

end

end Swan
end RamanujanPetersson


