-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N18RouteC_PushPull_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N18RouteC_PushPull_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:45:34.44599+00:00
-- url     : https://prove2.me/theorems/313dc864-38c4-4671-a3a7-51c2e36a2a82
-- title:
--   FLT.Assumptions.MazurProof.N18RouteC_PushPull source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N18RouteC_PushPull

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N18RouteC_PushPull
Original leading source comments and nonproject imports are retained below. -/
import Mathlib

set_option autoImplicit false




/-!
# Generic push-pull algebra for N18 Route C

All geometry is concentrated in four identities in `PushPullData`.  The
hyperelliptic sign, `Ψ ∘ Φ = [2]`, and the two-torsion kernel bound are then
formal consequences in additive commutative groups.
-/

namespace MazurProof.N18RouteC

noncomputable section

section Transport

variable {M A : Type*} [AddCommGroup M] [AddCommGroup A]

def transportEnd (e : M ≃+ A) (α : M →+ M) : A →+ A :=
  e.toAddMonoidHom.comp (α.comp e.symm.toAddMonoidHom)

@[simp] theorem transportEnd_apply (e : M ≃+ A) (α : M →+ M) (x : A) :
    transportEnd e α x = e (α (e.symm x)) := rfl

theorem transportEnd_comp (e : M ≃+ A) (α β : M →+ M) :
    transportEnd e (α.comp β) =
      (transportEnd e α).comp (transportEnd e β) := by
  ext x
  simp [transportEnd]

theorem transportEnd_eq_neg_id (e : M ≃+ A) (α : M →+ M)
    (hα : ∀ x : M, α x = -x) :
    transportEnd e α = -(AddMonoidHom.id A) := by
  ext x
  simp [transportEnd, hα]

end Transport

section Generic

variable {J EPlus EMinus : Type*}
variable [AddCommGroup J] [AddCommGroup EPlus] [AddCommGroup EMinus]

def twoTorsion (A : Type*) [AddCommGroup A] : AddSubgroup A :=
  (((2 : ℕ) • AddMonoidHom.id A)).ker

@[simp] theorem mem_twoTorsion_iff (x : J) :
    x ∈ twoTorsion J ↔ (2 : ℕ) • x = 0 := by
  simp [twoTorsion]

structure PushPullData
    (J EPlus EMinus : Type*)
    [AddCommGroup J] [AddCommGroup EPlus] [AddCommGroup EMinus] where
  hStar : J →+ J
  sigmaStar : J →+ J
  tauStar : J →+ J
  pushPlus : J →+ EPlus
  pushMinus : J →+ EMinus
  pullPlus : EPlus →+ J
  pullMinus : EMinus →+ J
  h_add : ∀ D : J, D + hStar D = 0
  tau_comp : tauStar = hStar.comp sigmaStar
  plus_push_pull :
    pullPlus.comp pushPlus = AddMonoidHom.id J + sigmaStar
  minus_push_pull :
    pullMinus.comp pushMinus = AddMonoidHom.id J + tauStar

namespace PushPullData

variable (d : PushPullData J EPlus EMinus)

theorem hStar_apply_eq_neg (D : J) : d.hStar D = -D := by
  calc
    d.hStar D = -D + (D + d.hStar D) := by abel
    _ = -D := by rw [d.h_add D]; simp

theorem hStar_eq_neg_id :
    d.hStar = -(AddMonoidHom.id J) := by
  ext D
  exact d.hStar_apply_eq_neg D

theorem tauStar_apply_eq_neg_sigmaStar (D : J) :
    d.tauStar D = -d.sigmaStar D := by
  calc
    d.tauStar D = d.hStar (d.sigmaStar D) := by
      have h := congrArg (fun f : J →+ J ↦ f D) d.tau_comp
      simpa using h
    _ = -d.sigmaStar D := d.hStar_apply_eq_neg (d.sigmaStar D)

theorem tauStar_eq_neg_sigmaStar : d.tauStar = -d.sigmaStar := by
  ext D
  exact d.tauStar_apply_eq_neg_sigmaStar D

theorem pullPlus_pushPlus_apply (D : J) :
    d.pullPlus (d.pushPlus D) = D + d.sigmaStar D := by
  have h := congrArg (fun f : J →+ J ↦ f D) d.plus_push_pull
  simpa using h

theorem pullMinus_pushMinus_apply (D : J) :
    d.pullMinus (d.pushMinus D) = D + d.tauStar D := by
  have h := congrArg (fun f : J →+ J ↦ f D) d.minus_push_pull
  simpa using h

def Phi : J →+ EPlus × EMinus where
  toFun D := (d.pushPlus D, d.pushMinus D)
  map_zero' := by simp
  map_add' x y := by simp

def Psi : EPlus × EMinus →+ J where
  toFun P := d.pullPlus P.1 + d.pullMinus P.2
  map_zero' := by simp
  map_add' x y := by
    change d.pullPlus (x.1 + y.1) + d.pullMinus (x.2 + y.2) =
      (d.pullPlus x.1 + d.pullMinus x.2) +
        (d.pullPlus y.1 + d.pullMinus y.2)
    rw [map_add, map_add]
    abel

theorem PsiPhi_apply (D : J) : d.Psi (d.Phi D) = (2 : ℕ) • D := by
  change d.pullPlus (d.pushPlus D) + d.pullMinus (d.pushMinus D) =
    (2 : ℕ) • D
  rw [d.pullPlus_pushPlus_apply D, d.pullMinus_pushMinus_apply D,
    d.tauStar_apply_eq_neg_sigmaStar D]
  simp only [two_nsmul]
  abel

theorem Psi_comp_Phi :
    d.Psi.comp d.Phi = (2 : ℕ) • AddMonoidHom.id J := by
  ext D
  exact d.PsiPhi_apply D

theorem ker_Phi_le_twoTorsion : d.Phi.ker ≤ twoTorsion J := by
  intro D hD
  rw [mem_twoTorsion_iff]
  change d.Phi D = 0 at hD
  calc
    (2 : ℕ) • D = d.Psi (d.Phi D) := (d.PsiPhi_apply D).symm
    _ = d.Psi 0 := by rw [hD]
    _ = 0 := by simp

theorem Phi_injective_of_no_twoTorsion
    (h2 : ∀ D : J, (2 : ℕ) • D = 0 → D = 0) :
    Function.Injective d.Phi := by
  intro x y hxy
  have hsub : d.Phi (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hmem : x - y ∈ d.Phi.ker := hsub
  have htwo : (2 : ℕ) • (x - y) = 0 :=
    (mem_twoTorsion_iff (x - y)).mp (d.ker_Phi_le_twoTorsion hmem)
  exact sub_eq_zero.mp (h2 (x - y) htwo)

theorem Phi_injOn_of_no_twoTorsion
    (H : AddSubgroup J)
    (hH : ∀ D : J, D ∈ H → (2 : ℕ) • D = 0 → D = 0) :
    Set.InjOn d.Phi (H : Set J) := by
  intro x hx y hy hxy
  have hsub : d.Phi (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hmem : x - y ∈ d.Phi.ker := hsub
  have htwo : (2 : ℕ) • (x - y) = 0 :=
    (mem_twoTorsion_iff (x - y)).mp (d.ker_Phi_le_twoTorsion hmem)
  exact sub_eq_zero.mp (hH (x - y) (H.sub_mem hx hy) htwo)

end PushPullData

end Generic

end


end MazurProof.N18RouteC


