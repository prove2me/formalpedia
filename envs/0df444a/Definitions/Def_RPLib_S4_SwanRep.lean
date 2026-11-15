-- Prove2me | Definitions.Def_RPLib_S4_SwanRep
-- name    : RPLib_S4_SwanRep
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:19:17.820062+00:00
-- url     : https://prove2.me/theorems/55da87a9-906f-4774-bc8e-8f5cd95e3f97
-- title:
--   The Swan conductor of a representation of a group with a ramification function
-- statement:
--   For a ramification function on a finite group $G$ and a finite-dimensional representation $\rho$ of $G$ on $V$ over a field $k$, let $V^{G_u}$ be the invariants of the lower ramification group $G_u$ and $\operatorname{cod}(G_u) = \dim V - \dim V^{G_u}$. The Swan conductor is $$\mathrm{Sw}(\rho) = \sum_{u \ge 1} \frac{|G_u|}{|G_0|}\, \operatorname{cod}(G_u),$$ a finite sum since $G_u = 1$ for $u$ large. The file proves it is nonnegative, expresses it through $\varphi$ and the breaks of the filtration, and proves inflation compatibility of invariants and codimensions.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter VI, Section 2; N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), Chapter 1

import Mathlib
import Definitions.Def_RPLib_S4_SwanHerbQ

/-!
# S4-Swan (K2), part 3: the Swan conductor of a representation

For a ramification function `R` on a finite group `G` (totally ramified, `G = G_0`) and a finite-dimensional
representation `ρ` of `G` over a field `k`, the Swan conductor (Serre, Local Fields VI §2)
`Sw(ρ) = ∑_{u ≥ 1} (|G_u|/|G|) codim V^{G_u}` (`swan`). It needs no hypothesis on `k`.
In characteristic zero it has the character form
`|G| Sw(ρ) = ∑_σ (i(σ) - 1)(dim V - tr ρ(σ))` (`card_mul_swan`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

open Module

section Fix

variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- The subspace fixed by a subgroup `H`. -/
def fixd (H : Subgroup G) : Submodule k V := Representation.invariants (ρ.comp H.subtype)

theorem mem_fixd {H : Subgroup G} {v : V} : v ∈ fixd ρ H ↔ ∀ σ ∈ H, ρ σ v = v :=
  ⟨fun h σ hσ => h ⟨σ, hσ⟩, fun h τ => h τ τ.2⟩

/-- Codimension of the fixed space of `H`. -/
def cod (H : Subgroup G) : ℕ := finrank k V - finrank k (fixd ρ H)

theorem fixd_bot : fixd ρ ⊥ = ⊤ := by
  rw [eq_top_iff]; intro v _
  rw [mem_fixd]; intro σ hσ
  rw [Subgroup.mem_bot.1 hσ, map_one, Module.End.one_apply]

theorem cod_bot : cod ρ ⊥ = 0 := by
  rw [cod, fixd_bot, finrank_top, Nat.sub_self]

theorem fixd_anti {H K : Subgroup G} (h : H ≤ K) : fixd ρ K ≤ fixd ρ H := fun _ hv =>
  (mem_fixd ρ).2 fun σ hσ => (mem_fixd ρ).1 hv σ (h hσ)

/-- Inflation: fixed vectors of `H` acting through `π` are the fixed vectors of `π(H)`. -/
theorem fixd_comp {Q : Type*} [Group Q] (ρ' : Representation k Q V) (π : G →* Q) (H : Subgroup G) :
    fixd (ρ'.comp π) H = fixd ρ' (H.map π) := by
  ext v
  rw [mem_fixd, mem_fixd]
  constructor
  · rintro h _ ⟨σ, hσ, rfl⟩
    exact h σ hσ
  · intro h σ hσ
    exact h (π σ) ⟨σ, hσ, rfl⟩

theorem cod_comp {Q : Type*} [Group Q] (ρ' : Representation k Q V) (π : G →* Q) (H : Subgroup G) :
    cod (ρ'.comp π) H = cod ρ' (H.map π) := by
  rw [cod, cod, fixd_comp]

theorem card_mul_finrank_fixd [CharZero k] [FiniteDimensional k V] (H : Subgroup G) [Fintype H] :
    (Fintype.card H : k) * finrank k (fixd ρ H) = ∑ h : H, LinearMap.trace k V (ρ h) := by
  have hc : (Fintype.card H : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let _ : Invertible (Fintype.card H : k) := invertibleOfNonzero hc
  rw [fixd, ← (Representation.isProj_averageMap (ρ.comp H.subtype)).trace]
  simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
    Representation.asAlgebraHom_of, smul_eq_mul]
  rw [← mul_assoc, mul_invOf_self, one_mul]
  rfl

end Fix

namespace RamFn

variable {G : Type*} [Group G] [Fintype G] (R : RamFn G)

/-- An index past every jump of the lower filtration. -/
def top : ℕ := Finset.univ.sup R.jdx

theorem jdx_le_top (σ : G) : R.jdx σ ≤ R.top := Finset.le_sup (Finset.mem_univ σ)

theorem lower_eq_bot {u : ℕ} (hu : R.top ≤ u) : R.lower (u + 1) = ⊥ := by
  rw [eq_bot_iff]; intro σ hσ
  rw [Subgroup.mem_bot]
  by_contra h
  have h1 := (R.mem_lower_iff h (u + 1)).1 hσ
  have h2 := R.jdx_le_top σ
  omega

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- The Swan conductor `Sw(ρ) = ∑_{u ≥ 1} (|G_u|/|G|) codim V^{G_u}` (Serre VI §2). -/
def swan : ℚ := ∑ u ∈ Finset.range R.top,
  (Nat.card (R.lower (u + 1)) : ℚ) / Nat.card G * cod ρ (R.lower (u + 1))

theorem swan_eq_range {n : ℕ} (hn : R.top ≤ n) : R.swan ρ = ∑ u ∈ Finset.range n,
    (Nat.card (R.lower (u + 1)) : ℚ) / Nat.card G * cod ρ (R.lower (u + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [swan, Finset.sum_range_add]
  have h0 : ∀ x ∈ Finset.range d, (Nat.card (R.lower (R.top + x + 1)) : ℚ) / Nat.card G *
      cod ρ (R.lower (R.top + x + 1)) = 0 := by
    intro x _
    rw [R.lower_eq_bot (by omega : R.top ≤ R.top + x), cod_bot]
    simp
  rw [Finset.sum_eq_zero h0, add_zero]

/-- The Swan conductor as a sum of `φ`-increments (the integral of `codim V^{G^v}` over `v > 0`). -/
theorem swan_eq_phi {n : ℕ} (hn : R.top ≤ n) : R.swan ρ = ∑ u ∈ Finset.range n,
    (R.phi (u + 1) - R.phi u) * cod ρ (R.lower (u + 1)) := by
  rw [R.swan_eq_range ρ hn]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [R.phi_succ u, add_sub_cancel_left]

theorem swan_nonneg : 0 ≤ R.swan ρ := by
  unfold swan
  positivity

theorem sum_range_ite_lt {M : Type*} [AddCommMonoid M] (x : M) {j n : ℕ} (h : j ≤ n) :
    ∑ u ∈ Finset.range n, (if u < j then x else 0) = j • x := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  congr 1
  have : (Finset.range n).filter (fun u => u < j) = Finset.range j := by
    ext u; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

open Classical in
theorem card_mul_cod [CharZero k] [FiniteDimensional k V] (H : Subgroup G) :
    (Nat.card H : k) * (cod ρ H : k) = ∑ σ : G,
      if σ ∈ H then ((finrank k V : k) - LinearMap.trace k V (ρ σ)) else 0 := by
  rw [cod, Nat.cast_sub (Submodule.finrank_le _), mul_sub, Nat.card_eq_fintype_card,
    card_mul_finrank_fixd, ← Finset.sum_filter,
    Finset.sum_subtype (p := (· ∈ H)) (F := inferInstance) (Finset.univ.filter (· ∈ H)) (fun x => by simp),
    Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

open Classical in
/-- Character form of the Swan conductor (char 0): `|G| Sw = ∑_σ (i(σ) - 1)(dim V - tr ρ(σ))`. -/
theorem card_mul_swan [CharZero k] [FiniteDimensional k V] :
    (Nat.card G : k) * (R.swan ρ : k) = ∑ σ : G,
      (R.jdx σ : k) * ((finrank k V : k) - LinearMap.trace k V (ρ σ)) := by
  have hG : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h1 : (Nat.card G : k) * (R.swan ρ : k) = ∑ u ∈ Finset.range R.top,
      (Nat.card (R.lower (u + 1)) : k) * (cod ρ (R.lower (u + 1)) : k) := by
    rw [swan, Rat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    push_cast
    field_simp
  rw [h1]
  simp_rw [card_mul_cod]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : σ = 1
  · subst hσ
    simp
  · have : ∀ u, (σ ∈ R.lower (u + 1)) ↔ u < R.jdx σ := fun u => by
      rw [R.mem_lower_iff hσ]; omega
    simp_rw [this]
    rw [sum_range_ite_lt _ (R.jdx_le_top σ), nsmul_eq_mul]

end RamFn

end

end Swan
end RamanujanPetersson


