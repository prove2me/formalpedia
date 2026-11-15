-- Prove2me | Definitions.Def_RPLib_S4_TameInertiaCoef
-- name    : RPLib_S4_TameInertiaCoef
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:02:12.680517+00:00
-- url     : https://prove2.me/theorems/9caf5890-24a0-4eec-8e5b-f7712bf0e495
-- title:
--   Homomorphisms into $N$-torsion groups from a generator of $\mathrm{Hom}(\Gamma, \mathbb{Z}/N)$
-- statement:
--   Let $\Gamma$ be a topological group and $\theta : \Gamma \to \mathbb{Z}/N$ with $\theta(\sigma_0) = 1$ such that every locally constant homomorphism $\Gamma \to \mathbb{Z}/N$ is a multiple of $\theta$. Then for every abelian group $M$ with $N M = 0$, every locally constant homomorphism $\chi : \Gamma \to M$ is $$\chi(\sigma) = \theta(\sigma) \cdot \chi(\sigma_0),$$ and conversely $\sigma \mapsto \theta(\sigma) m$ is a locally constant homomorphism with value $m$ at $\sigma_0$; so evaluation at $\sigma_0$ is a bijection $\mathrm{Hom}(\Gamma, M) \cong M$. The proof separates points of $M$ by characters $M \to \mathbb{Q}/\mathbb{Z}$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Galois Cohomology, Springer (1997), Chapter I, Section 2; J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter IV, Section 2

import Mathlib

/-!
# Tame inertia, part Coef: homomorphisms to `N`-torsion modules (S4-PD item (2), T9)

Abstract step: let `θ : Γ → ℤ/N` with `θ σ₀ = 1` be such that every locally constant homomorphism `Γ → ℤ/N` is a
multiple of `θ`. Then for every abelian group `M` killed by `N`, every locally constant homomorphism `χ : Γ → M` is
`σ ↦ (θ σ).val • χ σ₀` (`eq_val_nsmul_of_gen`), and conversely `σ ↦ (θ σ).val • m` is a locally constant homomorphism
for every `m` with value `m` at `σ₀`. So `Hom(Γ, M) ≅ M` by evaluation at `σ₀`. The proof separates points of `M` by
characters `M → ℚ/ℤ` (`CharacterModule`) and identifies the `N`-torsion of `ℚ/ℤ` with `ℤ/N` (`toQCircle`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

noncomputable section

section Circ

variable (N : ℕ) [NeZero N]

/-- `ℤ/N → ℚ/ℤ`, `j ↦ j / N`. -/
def toQCircle : ZMod N →+ AddCircle (1 : ℚ) :=
  ZMod.lift N ⟨AddMonoidHom.mk' (fun j : ℤ ↦ ((j / N : ℚ) : AddCircle (1 : ℚ))) (by simp [add_div]),
    by simp [div_self (NeZero.ne _)]⟩

theorem toQCircle_intCast (j : ℤ) : toQCircle N (j : ZMod N) = ((j / N : ℚ) : AddCircle (1 : ℚ)) := by
  simp [toQCircle]

theorem toQCircle_natCast (j : ℕ) : toQCircle N (j : ZMod N) = ((j / N : ℚ) : AddCircle (1 : ℚ)) := by
  simpa using toQCircle_intCast N j

theorem toQCircle_apply (j : ZMod N) : toQCircle N j = ((j.val / N : ℚ) : AddCircle (1 : ℚ)) := by
  rw [← toQCircle_natCast, ZMod.natCast_zmod_val]

theorem toQCircle_injective : Function.Injective (toQCircle N) := by
  haveI : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩
  intro x y hxy
  have : (0 : ℚ) < N := Nat.cast_pos.mpr (NeZero.pos _)
  rwa [toQCircle_apply, toQCircle_apply, AddCircle.coe_eq_coe_iff_of_mem_Ico,
    div_left_inj' this.ne', Nat.cast_inj, (ZMod.val_injective N).eq_iff] at hxy <;>
  exact ⟨by positivity, by simpa only [zero_add, div_lt_one this, Nat.cast_lt] using ZMod.val_lt _⟩

/-- The `N`-torsion of `ℚ/ℤ` is the image of `ℤ/N`. -/
theorem exists_toQCircle_eq {y : AddCircle (1 : ℚ)} (hy : N • y = 0) : ∃ k : ZMod N, toQCircle N k = y := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) y
  have h : (((N : ℚ) * q : ℚ) : AddCircle (1 : ℚ)) = 0 := by
    rw [← nsmul_eq_mul, AddCircle.coe_nsmul]
    exact hy
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).1 h
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hq : (m : ℚ) / N = q := by
    rw [zsmul_eq_mul, mul_one] at hm
    rw [hm, mul_div_cancel_left₀ _ hN]
  refine ⟨(m : ZMod N), ?_⟩
  rw [toQCircle_intCast, hq]

end Circ

section Gen

variable {Γ : Type*} [Mul Γ] [TopologicalSpace Γ] {N : ℕ} [NeZero N] {θ : Γ → ZMod N}
  {M : Type*} [AddCommGroup M] (hM : ∀ m : M, N • m = 0)

include hM in
theorem nsmul_mod_eq (k : ℕ) (m : M) : (k % N) • m = k • m := by
  conv_rhs => rw [← Nat.mod_add_div k N]
  rw [add_nsmul, mul_nsmul', hM, add_zero]

include hM in
theorem one_val_nsmul (m : M) : (1 : ZMod N).val • m = m := by
  rw [ZMod.val_one_eq_one_mod, nsmul_mod_eq hM, one_nsmul]

include hM in
/-- `σ ↦ (θ σ).val • m` is a homomorphism. -/
theorem val_nsmul_mul (hθm : ∀ σ τ, θ (σ * τ) = θ σ + θ τ) (m : M) (σ τ : Γ) :
    (θ (σ * τ)).val • m = (θ σ).val • m + (θ τ).val • m := by
  rw [hθm, ZMod.val_add, nsmul_mod_eq hM, add_nsmul]

theorem isLocallyConstant_val_nsmul (hθc : IsLocallyConstant θ) (m : M) :
    IsLocallyConstant (fun σ => (θ σ).val • m) :=
  hθc.comp (fun k : ZMod N => k.val • m)

include hM in
/-- **T9.** If every locally constant homomorphism `Γ → ℤ/N` is a multiple of `θ` and `θ σ₀ = 1`, then every locally
constant homomorphism `χ : Γ → M` to an abelian group killed by `N` is `σ ↦ (θ σ).val • χ σ₀`. -/
theorem eq_val_nsmul_of_gen {σ₀ : Γ} (hθ : θ σ₀ = 1)
    (hgen : ∀ χ : Γ → ZMod N, IsLocallyConstant χ → (∀ σ τ, χ (σ * τ) = χ σ + χ τ) →
      ∃ k : ZMod N, ∀ σ, χ σ = k * θ σ)
    (χ : Γ → M) (hχc : IsLocallyConstant χ) (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ) (σ : Γ) :
    χ σ = (θ σ).val • χ σ₀ := by
  classical
  rw [← sub_eq_zero]
  refine CharacterModule.eq_zero_of_character_apply fun c => ?_
  have hex : ∀ σ, ∃ k : ZMod N, toQCircle N k = c (χ σ) := fun σ =>
    exists_toQCircle_eq N (by rw [← map_nsmul, hM, map_zero])
  let g : AddCircle (1 : ℚ) → ZMod N := fun y => if h : ∃ k, toQCircle N k = y then h.choose else 0
  have hg : ∀ σ, toQCircle N (g (c (χ σ))) = c (χ σ) := fun σ => by
    simp only [g, dif_pos (hex σ)]
    exact (hex σ).choose_spec
  have hgc : IsLocallyConstant (fun σ => g (c (χ σ))) := hχc.comp (fun m => g (c m))
  have hgm : ∀ σ τ, g (c (χ (σ * τ))) = g (c (χ σ)) + g (c (χ τ)) := fun σ τ =>
    toQCircle_injective N (by rw [map_add, hg, hg, hg, hχ, map_add])
  obtain ⟨k, hk⟩ := hgen _ hgc hgm
  have e : ∀ τ, c (χ τ) = (θ τ).val • toQCircle N k := fun τ => by
    rw [← hg τ, hk τ, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  have e0 : c (χ σ₀) = toQCircle N k := by
    rw [← hg σ₀, hk σ₀, hθ, mul_one]
  rw [map_sub, map_nsmul, e σ, e0, sub_self]

end Gen

end

end TameInertia
end RamanujanPetersson


