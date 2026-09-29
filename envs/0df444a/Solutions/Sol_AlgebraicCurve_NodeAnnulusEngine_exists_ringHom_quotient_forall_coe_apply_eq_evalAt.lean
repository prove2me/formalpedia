-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.exists_ringHom_quotient_forall_coe_apply_eq_evalAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/118c07e9-9dfa-511d-b9d5-3915d76b7362

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_ringHom_quotient_forall_coe_apply_eq_evalAt

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace FwdAux

open AlgebraicCurve

variable {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']

theorem evalAt_add_of_mem (v : Place K' F') (hv : v.IsRational) {f g : F'}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

end FwdAux

open FwdAux AlgebraicCurve.GaussReduction in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]

    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]

    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))

    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))

    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)

    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (𝔭 : Ideal ↥𝒩₀) [𝔭.IsPrime] (h𝔭0 : 𝔭 ≠ ⊥) (h𝔭ϖ : (⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ : ↥𝒩₀) ∉ 𝔭)
    (P : Place L F) (hP : P ∈ S) (hP𝔭 : ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭) :
    ∃ φ : (↥𝒩₀ ⧸ 𝔭) →+* ↥A,
      (∀ c : ↥C, φ (Ideal.Quotient.mk 𝔭 ⟨algebraMap L F (c : L), hCmem c c.2⟩) = ⟨(c : L), hC c c.2⟩) ∧
      ∀ g : ↥𝒩₀, ((φ (Ideal.Quotient.mk 𝔭 g) : ↥A) : L) = P.evalAt (g : F) := by
  classical
  obtain ⟨hNP, hSmax⟩ := (hS P).mp hP
  have hratP : P.IsRational := hrat P hP

  have hval : ∀ g : ↥𝒩₀, P.evalAt (g : F) ∈ A := by
    intro g
    obtain ⟨o, ho⟩ := hres g
    obtain ⟨hA, -⟩ := hSmax _ ho
    have hsplit : (g : F) = ((g - ⟨algebraMap L F (o : L), hCmem o o.2⟩ : ↥𝒩₀) : F) + algebraMap L F (o : L) := by
      push_cast; ring
    rw [hsplit, evalAt_add_of_mem P hratP (hNP _ (g - _).2) (P.algebraMap_mem' _),
      evalAt_algebraMap_const P hratP]
    exact add_mem hA (hC o o.2)

  let ψ : ↥𝒩₀ →+* ↥A :=
    { toFun := fun g => ⟨P.evalAt (g : F), hval g⟩
      map_one' := Subtype.ext (by simp [Place.evalAt_one])
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subring.coe_mul, MulMemClass.coe_mul]
        exact evalAt_mul_of_mem P hratP (hNP _ a.2) (hNP _ b.2))
      map_zero' := Subtype.ext (by
        simp only [Subring.coe_zero, ZeroMemClass.coe_zero]
        have := evalAt_algebraMap_const P hratP (0 : L)
        rwa [map_zero] at this)
      map_add' := fun a b => Subtype.ext (by
        simp only [Subring.coe_add, AddMemClass.coe_add]
        exact evalAt_add_of_mem P hratP (hNP _ a.2) (hNP _ b.2)) }
  have hψ : ∀ g : ↥𝒩₀, ((ψ g : ↥A) : L) = P.evalAt (g : F) := fun g => rfl

  have hker : ∀ g ∈ 𝔭, ψ g = 0 := fun g hg => Subtype.ext ((hP𝔭 g).mpr hg)
  refine ⟨Ideal.Quotient.lift 𝔭 ψ hker, fun c => ?_, fun g => ?_⟩
  · rw [Ideal.Quotient.lift_mk]
    apply Subtype.ext
    show P.evalAt (algebraMap L F (c : L)) = (c : L)
    exact evalAt_algebraMap_const P hratP (c : L)
  · rw [Ideal.Quotient.lift_mk]
    exact hψ g

end S_AlgebraicCurve_NodeAnnulusEngine_exists_ringHom_quotient_forall_coe_apply_eq_evalAt
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_ringHom_quotient_forall_coe_apply_eq_evalAt (solution)
