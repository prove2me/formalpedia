-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8e984d5d-94ad-52bc-b033-23136285108d

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme IsAffineOpen Scheme.Modules"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "mk Γ isBasis_affineOpens Modules Opens Modules.map_smul"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf isSheaf map_smul"
namespace RGlue
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}} (M : X.Modules)

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op x) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem res_res' {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op x) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem res_sum_smul {U W : X.Opens} (h : W ≤ U) {d : ℕ} (c : Fin d → Γ(X, U)) (v : Fin d → Γ(M, U)) :
    M.presheaf.map (homOfLE h).op (∑ i, c i • v i) =
      ∑ i, X.presheaf.map (homOfLE h).op (c i) • M.presheaf.map (homOfLE h).op (v i) := by
  rw [map_sum]
  simp only [Modules.map_smul]

variable {V : X.Opens} {d : ℕ} (e : Fin d → Γ(M, V))
  (he : ∀ (W : X.Opens) (hW : W ≤ V), IsAffineOpen W →
    ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i))

abbrev ι (W : X.Opens) : Type u := { W' : X.Opens // W' ≤ W ∧ IsAffineOpen W' }

theorem cover (W : X.Opens) : W ≤ ⨆ i : ι W, i.1 := by
  intro x hx
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  exact Opens.mem_iSup.mpr ⟨⟨W', hle, hW'⟩, hxW'⟩

include he in

private theorem _root_.AlgebraicGeometry.Scheme.Modules.RGlue.linearIndependent (W : X.Opens) (hW : W ≤ V) :
    ∀ c : Fin d → Γ(X, W), ∑ i, c i • M.presheaf.map (homOfLE hW).op (e i) = 0 → c = 0 := by
  intro c hc
  funext i

  refine X.sheaf.eq_of_locally_eq' (fun j : ι W => j.1) W (fun j => homOfLE j.2.1) (cover W) (c i) 0 ?_
  intro j
  rw [map_zero]
  obtain ⟨b, hb⟩ := he j.1 (j.2.1.trans hW) j.2.2
  have hc' := congrArg (M.presheaf.map (homOfLE j.2.1).op) hc
  rw [res_sum_smul, map_zero] at hc'
  simp only [res_res] at hc'

  have hli := b.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have := hli (fun i => X.presheaf.map (homOfLE j.2.1).op (c i)) (by
    simpa only [hb] using hc')
  exact this i

p2m_export "AlgebraicGeometry.Scheme.Modules.RGlue" "linearIndependent"
include he in

theorem exists_coords (W : X.Opens) (hW : W ≤ V) (s : Γ(M, W)) :
    ∃ c : Fin d → Γ(X, W), ∑ i, c i • M.presheaf.map (homOfLE hW).op (e i) = s := by

  have hloc : ∀ j : ι W, ∃ c : Fin d → Γ(X, j.1),
      ∑ i, c i • M.presheaf.map (homOfLE (j.2.1.trans hW)).op (e i) = M.presheaf.map (homOfLE j.2.1).op s := by
    intro j
    obtain ⟨b, hb⟩ := he j.1 (j.2.1.trans hW) j.2.2
    refine ⟨fun i => b.repr (M.presheaf.map (homOfLE j.2.1).op s) i, ?_⟩
    conv_rhs => rw [← b.sum_repr (M.presheaf.map (homOfLE j.2.1).op s)]
    simp only [hb]
  choose c hc using hloc

  have hcompat : ∀ i, TopCat.Presheaf.IsCompatible X.presheaf (fun j : ι W => j.1) (fun j => c j i) := by
    intro i j k
    have key := linearIndependent M e he (j.1 ⊓ k.1) ((inf_le_left.trans j.2.1).trans hW)
      (fun i => X.presheaf.map (Opens.infLELeft j.1 k.1).op (c j i) - X.presheaf.map (Opens.infLERight j.1 k.1).op (c k i)) ?_
    · have := congrFun key i
      exact sub_eq_zero.mp this
    · simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      have hj := congrArg (M.presheaf.map (Opens.infLELeft j.1 k.1).op) (hc j)
      have hk := congrArg (M.presheaf.map (Opens.infLERight j.1 k.1).op) (hc k)
      rw [show (Opens.infLELeft j.1 k.1 : j.1 ⊓ k.1 ⟶ j.1) = homOfLE inf_le_left from rfl] at hj ⊢
      rw [show (Opens.infLERight j.1 k.1 : j.1 ⊓ k.1 ⟶ k.1) = homOfLE inf_le_right from rfl] at hk ⊢
      rw [res_sum_smul, res_res] at hj hk
      simp only [res_res] at hj hk
      rw [hj, hk]

  have hglue : ∀ i, ∃ ci : Γ(X, W), ∀ j : ι W, X.presheaf.map (homOfLE j.2.1).op ci = c j i := fun i =>
    (X.sheaf.existsUnique_gluing' (fun j : ι W => j.1) W (fun j => homOfLE j.2.1) (cover W)
      (fun j => c j i) (hcompat i)).exists
  choose cg hcg using hglue
  refine ⟨cg, ?_⟩

  refine TopCat.Sheaf.eq_of_locally_eq' (C := Ab) ⟨M.presheaf, M.isSheaf⟩ (fun j : ι W => j.1) W
    (fun j => homOfLE j.2.1) (cover W) _ _ ?_
  intro j
  change M.presheaf.map (homOfLE j.2.1).op _ = M.presheaf.map (homOfLE j.2.1).op s
  rw [res_sum_smul]
  simp only [res_res, hcg]
  exact hc j

include he in
theorem main (W : X.Opens) (hW : W ≤ V) :
    ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i) := by
  have hli : LinearIndependent Γ(X, W) (fun i => M.presheaf.map (homOfLE hW).op (e i)) :=
    Fintype.linearIndependent_iff.mpr fun g hg i => congrFun (linearIndependent M e he W hW g hg) i
  have hsp : ⊤ ≤ Submodule.span (X.presheaf.obj (op W)) (Set.range fun i => M.presheaf.map (homOfLE hW).op (e i)) := by
    intro s _
    obtain ⟨c, hc⟩ := exists_coords M e he W hW s
    rw [← hc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => Module.Basis.mk_apply hli hsp i⟩

end AlgebraicGeometry.Scheme.Modules.RGlue

theorem solution
    {X : Scheme.{u}} (M : X.Modules) {V : X.Opens} {d : ℕ} (e : Fin d → Γ(M, V))
    (he : ∀ (W : X.Opens) (hW : W ≤ V), IsAffineOpen W →
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)) :
    ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i) :=
  fun W hW => AlgebraicGeometry.Scheme.Modules.RGlue.main M e he W hW

end S_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen (solution)
