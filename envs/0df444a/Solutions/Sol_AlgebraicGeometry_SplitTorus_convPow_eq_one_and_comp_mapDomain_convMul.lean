-- Prove2me | solution 1 for AlgebraicGeometry.SplitTorus.convPow_eq_one_and_comp_mapDomain_convMul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8b4864cd-6c22-5ef6-95e8-333420c4b1de

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SplitTorus_convPow_eq_one_and_comp_mapDomain_convMul

set_option autoImplicit false

universe u v

open AlgebraicGeometry AlgebraicGeometry.SplitTorus

theorem solution
    (S : Type u) [CommRing S] (T : Type u) [CommRing T] [Algebra S T] (t m : ℕ) :
    (∀ χ : WithConv (muCoord S t m →ₐ[S] T), χ ^ m = 1) ∧
    (∀ χ χ' : WithConv (muCoord S t m →ₐ[S] T),
      WithConv.toConv ((χ * χ').ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S
          (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)))) =
        WithConv.toConv (χ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S
          (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)))) * WithConv.toConv (χ'.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S
          (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i))))) ∧
    (WithConv.toConv ((1 : WithConv (muCoord S t m →ₐ[S] T)).ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S
          (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)))) =
      (1 : WithConv (torusCoord S t →ₐ[S] T))) := by
  classical

  set F : torusCoord S t →ₐ[S] muCoord S t m := AddMonoidAlgebra.mapDomainAlgHom S S
    (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)) with hF

  have hglμ : ∀ (χ ψ : WithConv (muCoord S t m →ₐ[S] T)) (g : Fin t → ZMod m),
      (χ * ψ).ofConv (AddMonoidAlgebra.single g 1) =
        χ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
    intro χ ψ g
    rw [AlgHom.convMul_def]
    simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]
  have hglT : ∀ (χ ψ : WithConv (torusCoord S t →ₐ[S] T)) (g : Fin t → ℤ),
      (χ * ψ).ofConv (AddMonoidAlgebra.single g 1) =
        χ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
    intro χ ψ g
    rw [AlgHom.convMul_def]
    simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]
  have honeμ : ∀ g : Fin t → ZMod m,
      (1 : WithConv (muCoord S t m →ₐ[S] T)).ofConv (AddMonoidAlgebra.single g 1) = 1 := by
    intro g
    rw [AlgHom.convOne_def]
    simp [AddMonoidAlgebra.counit_single]
  have honeT : ∀ g : Fin t → ℤ,
      (1 : WithConv (torusCoord S t →ₐ[S] T)).ofConv (AddMonoidAlgebra.single g 1) = 1 := by
    intro g
    rw [AlgHom.convOne_def]
    simp [AddMonoidAlgebra.counit_single]
  have hFs : ∀ g : Fin t → ℤ, F (AddMonoidAlgebra.single g 1) =
      AddMonoidAlgebra.single ((AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp
        (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)) g) 1 := by
    intro g
    simp [hF, AddMonoidAlgebra.mapDomain_single]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro χ
    have hpow : ∀ (k : ℕ) (g : Fin t → ZMod m),
        (χ ^ k).ofConv (AddMonoidAlgebra.single g 1) = (χ.ofConv (AddMonoidAlgebra.single g 1)) ^ k := by
      intro k g
      induction k with
      | zero => rw [pow_zero, pow_zero, honeμ]
      | succ k ih => rw [pow_succ, hglμ, ih, pow_succ]
    have hext : (χ ^ m).ofConv = (1 : WithConv (muCoord S t m →ₐ[S] T)).ofConv := by
      apply AddMonoidAlgebra.algHom_ext
      intro g
      rw [hpow, honeμ, ← map_pow, AddMonoidAlgebra.single_pow, one_pow]
      have hmg : m • g = 0 := by
        funext j; simp
      rw [hmg]
      exact map_one χ.ofConv
      exact Subsingleton.elim _ _
    exact congrArg WithConv.toConv hext
  ·
    intro χ χ'
    apply WithConv.ofConv_injective
    show (χ * χ').ofConv.comp F =
      (WithConv.toConv (χ.ofConv.comp F) * WithConv.toConv (χ'.ofConv.comp F)).ofConv
    apply AddMonoidAlgebra.algHom_ext
    intro g
    rw [hglT, AlgHom.comp_apply, hFs, hglμ]
    simp only [WithConv.ofConv_toConv, AlgHom.comp_apply, hFs]
    exact Subsingleton.elim _ _
  ·
    apply WithConv.ofConv_injective
    show (1 : WithConv (muCoord S t m →ₐ[S] T)).ofConv.comp F = (1 : WithConv (torusCoord S t →ₐ[S] T)).ofConv
    apply AddMonoidAlgebra.algHom_ext
    intro g
    rw [AlgHom.comp_apply, hFs, honeμ, honeT]
    exact Subsingleton.elim _ _

end S_AlgebraicGeometry_SplitTorus_convPow_eq_one_and_comp_mapDomain_convMul
end P2MW
export P2MW.S_AlgebraicGeometry_SplitTorus_convPow_eq_one_and_comp_mapDomain_convMul (solution)
