-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_CoordMapInjective
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL6_CoordMapInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:28.162616+00:00
-- url     : https://prove2.me/theorems/8fc88a37-c249-433c-9415-c5ebf3b8866f
-- title:
--   Coord Map Injective
-- statement:
--   Definitions and structural lemmas for Coord Map Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/CoordMapInjective.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open Classical
section Induced
@[instance_reducible] def productMulActionFirstFactor (G Y : Type) [CommGroup G] : MulAction G (G × Y) where
  smul g x := (g * x.1, x.2)
  one_smul x := by
    show ((1 : G) * x.1, x.2) = x
    rw [one_mul]
  mul_smul g h x := by
    show ((g * h) * x.1, x.2) = (g * (h * x.1), x.2)
    rw [mul_assoc]
variable {G : Type} [CommGroup G] [Fintype G] {Cl : Type} [Fintype Cl] [MulAction G Cl] {d : ℕ}
  {M : Type} [AddCommGroup M] [Module ℂ M]
def t2xE (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M)) :
    M →ₗ[ℂ] (G × (MulAction.orbitRel.Quotient G Cl × Fin d) → ℂ) where
  toFun φ x := Φ (ρ x.1 φ) (Quotient.out x.2.1) x.2.2
  map_add' φ ψ := by funext x; simp
  map_smul' a φ := by funext x; simp
theorem exists_smul_out_eq (c : Cl) : ∃ g : G, g • Quotient.out (Quotient.mk (MulAction.orbitRel G Cl) c) = c := by
  have h := Quotient.mk_out (s := MulAction.orbitRel G Cl) c
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
theorem t2xE_injective_of_monomial (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M))
    (hmono : ∀ (g : G) (c : Cl) (φ : M), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0) :
    Function.Injective (t2xE Φ ρ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hE
  have h0 : ∀ (g : G) (q : MulAction.orbitRel.Quotient G Cl), Φ (ρ g φ) (Quotient.out q) = 0 :=
    fun g q => funext fun b => congrFun hE (g, q, b)
  have h1 : Φ φ = 0 := by
    funext c
    obtain ⟨g, hg⟩ := exists_smul_out_eq (G := G) c
    have := hmono g _ φ (h0 g (Quotient.mk (MulAction.orbitRel G Cl) c))
    rw [hg] at this
    exact this
  exact Φ.map_eq_zero_iff.1 h1
theorem card_mul_card_orbits (hfree : ∀ (g : G) (c : Cl), g • c = c → g = 1) :
    Fintype.card G * Fintype.card (MulAction.orbitRel.Quotient G Cl) = Fintype.card Cl := by
  rw [← Fintype.card_prod]
  refine Fintype.card_of_bijective (f := fun x : G × MulAction.orbitRel.Quotient G Cl => x.1 • Quotient.out x.2) ⟨?_, ?_⟩
  · rintro ⟨g, q⟩ ⟨g', q'⟩ h
    simp only at h
    have hq : ∀ (g0 : G) (q0 : MulAction.orbitRel.Quotient G Cl),
        (Quotient.mk (MulAction.orbitRel G Cl) (g0 • Quotient.out q0)) = q0 := by
      intro g0 q0
      conv_rhs => rw [← Quotient.out_eq q0]
      exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit _ g0))
    have hqq : q = q' := by rw [← hq g q, ← hq g' q', h]
    subst hqq
    have h2 : (g'⁻¹ * g) • Quotient.out q = Quotient.out q := by rw [mul_smul, h, inv_smul_smul]
    have h3 := hfree _ _ h2
    rw [inv_mul_eq_one] at h3
    rw [h3]
  · intro c
    obtain ⟨g, hg⟩ := exists_smul_out_eq (G := G) c
    exact ⟨(g, _), hg⟩
theorem coordMap_bijective (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M))
    (hmono : ∀ (g : G) (c : Cl) (φ : M), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0)
    (hfree : ∀ (g : G) (c : Cl), g • c = c → g = 1) :
    Function.Bijective (t2xE Φ ρ) := by
  have : FiniteDimensional ℂ M := LinearEquiv.finiteDimensional Φ.symm
  have hinj := t2xE_injective_of_monomial Φ ρ hmono
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [Φ.finrank_eq, Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype]
  simp only [Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod,
    Fintype.card_fin]
  rw [← card_mul_card_orbits hfree]
  ring
def orbitDecompositionLinearEquiv (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M))
    (hmono : ∀ (g : G) (c : Cl) (φ : M), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0)
    (hfree : ∀ (g : G) (c : Cl), g • c = c → g = 1) :
    M ≃ₗ[ℂ] (G × (MulAction.orbitRel.Quotient G Cl × Fin d) → ℂ) :=
  LinearEquiv.ofBijective (t2xE Φ ρ) (coordMap_bijective Φ ρ hmono hfree)
end Induced
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end


