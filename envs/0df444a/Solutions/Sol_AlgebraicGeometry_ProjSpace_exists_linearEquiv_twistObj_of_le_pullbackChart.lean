-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/611636b6-06ae-57b1-8fdb-56e99c5e252a

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mTwistChartTriv

open AlgebraicGeometry.ProjSpace

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))
  (m : ℕ) {i : Fin (N + 1)} {W : X.Opens}

theorem le_inf_chart (hW : W ≤ pullbackChart φ i) : W ≤ W ⊓ pullbackChart φ i := le_inf le_rfl hW

theorem res_down_up (hW : W ≤ pullbackChart φ i) (x : Γ(X, W ⊓ pullbackChart φ i)) :
    restrictFun (inf_le_left : W ⊓ pullbackChart φ i ≤ W) (restrictFun (le_inf_chart φ hW) x) = x := by
  rw [restrictFun_restrictFun]; exact restrictFun_refl x

theorem res_up_down (hW : W ≤ pullbackChart φ i) (a : Γ(X, W)) :
    restrictFun (le_inf_chart φ hW) (restrictFun (inf_le_left : W ⊓ pullbackChart φ i ≤ W) a) = a := by
  rw [restrictFun_restrictFun]; exact restrictFun_refl a

noncomputable def fwd (hW : W ≤ pullbackChart φ i) : twistObj π φ m W →ₗ[Γ(X, W)] Γ(X, W) where
  toFun g := restrictFun (le_inf_chart φ hW) (g.val i)
  map_add' g g' := by
    show restrictFun _ ((g + g').val i) = _
    rw [twistObj.add_val, Pi.add_apply, map_add]
  map_smul' a g := by
    show restrictFun _ ((a • g).val i) = a * restrictFun _ (g.val i)
    rw [twistObj.smul_val, map_mul, res_up_down φ hW]

theorem fwd_apply (hW : W ≤ pullbackChart φ i) (g : twistObj π φ m W) :
    fwd π φ m hW g = restrictFun (le_inf_chart φ hW) (g.val i) := rfl

noncomputable def invVal (i : Fin (N + 1)) (a : Γ(X, W)) (j : Fin (N + 1)) : Γ(X, W ⊓ pullbackChart φ j) :=
  restrictFun (inf_le_right : W ⊓ pullbackChart φ j ≤ pullbackChart φ j) (frameUnit φ j i) ^ m *
    restrictFun (inf_le_left : W ⊓ pullbackChart φ j ≤ W) a

theorem cocycle_res (i j l : Fin (N + 1)) :
    restrictFun (le_trans inf_le_left inf_le_right : (W ⊓ pullbackChart φ j) ⊓ pullbackChart φ l ≤ pullbackChart φ j)
        (frameUnit φ j l) *
      restrictFun (inf_le_right : (W ⊓ pullbackChart φ j) ⊓ pullbackChart φ l ≤ pullbackChart φ l) (frameUnit φ l i)
      = restrictFun (le_trans inf_le_left inf_le_right : (W ⊓ pullbackChart φ j) ⊓ pullbackChart φ l ≤ pullbackChart φ j)
        (frameUnit φ j i) := by
  have hO : (W ⊓ pullbackChart φ j) ⊓ pullbackChart φ l ≤ pullbackOverlap φ j l := by
    rw [pullbackOverlap_eq_inf]; exact le_inf (le_trans inf_le_left inf_le_right) inf_le_right
  have key := congrArg (restrictFun hO) (frameUnit_cocycle φ j l i)
  rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at key
  exact key

theorem invVal_compat (i : Fin (N + 1)) (a : Γ(X, W)) : TwistCompat φ m W (invVal φ m i a) := by
  intro j l
  simp only [invVal, map_mul, map_pow, restrictFun_restrictFun]
  rw [← cocycle_res φ i j l, mul_pow]

  have ha : restrictFun ((inf_le_left : (W ⊓ pullbackChart φ j) ⊓ pullbackChart φ l ≤ W ⊓ pullbackChart φ j).trans
        (inf_le_left : W ⊓ pullbackChart φ j ≤ W)) a
      = restrictFun ((le_inf (le_trans inf_le_left inf_le_left) inf_le_right :
          (W ⊓ pullbackChart φ j) ⊓ pullbackChart φ l ≤ W ⊓ pullbackChart φ l).trans
        (inf_le_left : W ⊓ pullbackChart φ l ≤ W)) a := rfl
  have hu : restrictFun ((le_inf (le_trans inf_le_left inf_le_left) inf_le_right :
          (W ⊓ pullbackChart φ j) ⊓ pullbackChart φ l ≤ W ⊓ pullbackChart φ l).trans
        (inf_le_right : W ⊓ pullbackChart φ l ≤ pullbackChart φ l)) (frameUnit φ l i)
      = restrictFun (inf_le_right : (W ⊓ pullbackChart φ j) ⊓ pullbackChart φ l ≤ pullbackChart φ l) (frameUnit φ l i) := rfl
  rw [ha, hu]
  ring

noncomputable def inv (i : Fin (N + 1)) (a : Γ(X, W)) : twistObj π φ m W := ⟨invVal φ m i a, invVal_compat φ m i a⟩

theorem inv_val (a : Γ(X, W)) (j : Fin (N + 1)) : (inv π φ m i a).val j = invVal φ m i a j := rfl

theorem fwd_inv (hW : W ≤ pullbackChart φ i) (a : Γ(X, W)) : fwd π φ m hW (inv π φ m i a) = a := by
  rw [fwd_apply, inv_val, invVal, frameUnit_self, map_one, one_pow, one_mul, res_up_down φ hW]

theorem inv_fwd (hW : W ≤ pullbackChart φ i) (g : twistObj π φ m W) : inv π φ m i (fwd π φ m hW g) = g := by
  refine twistObj.ext (funext fun j => ?_)
  rw [inv_val, invVal, fwd_apply, restrictFun_restrictFun]

  have hle : W ⊓ pullbackChart φ j ≤ (W ⊓ pullbackChart φ j) ⊓ pullbackChart φ i :=
    le_inf le_rfl (inf_le_left.trans hW)
  have hc := congrArg (restrictFun hle) (g.compat j i)
  rw [map_mul, map_pow, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun,
    restrictFun_refl] at hc
  rw [hc]

noncomputable def equiv (hW : W ≤ pullbackChart φ i) : twistObj π φ m W ≃ₗ[Γ(X, W)] Γ(X, W) :=
  { fwd π φ m hW with
    invFun := inv π φ m i
    left_inv := inv_fwd π φ m hW
    right_inv := fwd_inv π φ m hW }

theorem equiv_apply (hW : W ≤ pullbackChart φ i) (g : twistObj π φ m W) :
    equiv π φ m hW g = restrictFun (le_inf_chart φ hW) (g.val i) := rfl

theorem equiv_symm_apply (hW : W ≤ pullbackChart φ i) (a : Γ(X, W)) : (equiv π φ m hW).symm a = inv π φ m i a := rfl

theorem main (hW : W ≤ pullbackChart φ i) :
    ∃ e : twistObj π φ m W ≃ₗ[Γ(X, W)] Γ(X, W),
      (∀ g : twistObj π φ m W,
        restrictFun (inf_le_left : W ⊓ pullbackChart φ i ≤ W) (e g) = g.val i) ∧
      (∀ (a : Γ(X, W)) (j : Fin (N + 1)),
        (e.symm a).val j =
          restrictFun (inf_le_right : W ⊓ pullbackChart φ j ≤ pullbackChart φ j) (frameUnit φ j i) ^ m *
            restrictFun (inf_le_left : W ⊓ pullbackChart φ j ≤ W) a) :=
  ⟨equiv π φ m hW, fun g => by rw [equiv_apply, res_down_up φ hW], fun a j => by rw [equiv_symm_apply, inv_val, invVal]⟩

end P2mTwistChartTriv

theorem solution
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))
    (m : ℕ) {i : Fin (N + 1)} {W : X.Opens} (hW : W ≤ ProjSpace.pullbackChart φ i) :
    ∃ e : ProjSpace.twistObj π φ m W ≃ₗ[Γ(X, W)] Γ(X, W),
      (∀ g : ProjSpace.twistObj π φ m W,
        ProjSpace.restrictFun (inf_le_left : W ⊓ ProjSpace.pullbackChart φ i ≤ W) (e g) = g.val i) ∧
      (∀ (a : Γ(X, W)) (j : Fin (N + 1)),
        (e.symm a).val j =
          ProjSpace.restrictFun (inf_le_right : W ⊓ ProjSpace.pullbackChart φ j ≤ ProjSpace.pullbackChart φ j)
              (ProjSpace.frameUnit φ j i) ^ m *
            ProjSpace.restrictFun (inf_le_left : W ⊓ ProjSpace.pullbackChart φ j ≤ W) a) :=
  P2mTwistChartTriv.main π φ m hW

end S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart (solution)
