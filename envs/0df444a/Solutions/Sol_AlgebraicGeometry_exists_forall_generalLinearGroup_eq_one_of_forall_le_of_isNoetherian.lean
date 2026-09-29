-- Prove2me | solution 1 for AlgebraicGeometry.exists_forall_generalLinearGroup_eq_one_of_forall_le_of_isNoetherian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/99aec83b-b264-57cd-af82-e00fe7125cb4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_forall_generalLinearGroup_eq_one_of_forall_le_of_isNoetherian

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_forall_generalLinearGroup_eq_one_of_forall_le_of_isNoetherian.AlgebraicGeometry TopologicalSpace Opposite"

universe u

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Scheme IsLocallyNoetherian.component_noetherian IsNoetherian"
namespace KernelTowerStabilization
p2m_open "AlgebraicGeometry"

section Vanishing

variable {G : Scheme.{u}}

abbrev res (U : G.Opens) (e : Γ(G, ⊤)) : Γ(G, U) :=
  G.presheaf.map (homOfLE le_top).op e

theorem app_res {T : Scheme.{u}} (x : T ⟶ G) (U : G.Opens) (e : Γ(G, ⊤)) :
    x.app U (res U e) = T.presheaf.map (homOfLE le_top).op (x.appTop e) := by
  have h := x.naturality (homOfLE (le_top : U ≤ ⊤)).op
  have h' := congrArg (fun φ => φ.hom e) h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h'
  exact h'

theorem eq_zero_of_forall_res_eq_zero {T : Scheme.{u}} (x : T ⟶ G) {ι : Type*} (U : ι → G.Opens)
    (hU : ∀ g : G, ∃ i, g ∈ U i) (s : Γ(T, ⊤))
    (hs : ∀ i, T.presheaf.map (homOfLE (le_top : x ⁻¹ᵁ U i ≤ ⊤)).op s = 0) : s = 0 := by
  apply TopCat.Presheaf.IsSheaf.section_ext T.IsSheaf
  intro t _
  obtain ⟨i, hi⟩ := hU (x.base t)
  refine ⟨x ⁻¹ᵁ U i, le_top, hi, ?_⟩
  rw [hs i, map_zero]

end Vanishing

section Stabilization

variable {G : Scheme.{u}}

def Kills {A : ℕ → Type*} (e : ∀ n, A n → Γ(G, ⊤)) (n : ℕ) {T : Scheme.{u}} (x : T ⟶ G) : Prop :=
  ∀ a, x.appTop (e n a) = 0

def J {A : ℕ → Type*} (e : ∀ n, A n → Γ(G, ⊤)) (U : G.Opens) (n : ℕ) : Ideal Γ(G, U) :=
  Ideal.span (⋃ m ∈ Set.Iic n, Set.range fun a : A m => res U (e m a))

theorem J_mono {A : ℕ → Type*} (e : ∀ n, A n → Γ(G, ⊤)) (U : G.Opens) : Monotone (J e U) := by
  intro n n' h
  apply Ideal.span_mono
  intro s hs
  simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_range, exists_prop] at hs ⊢
  obtain ⟨m, hm, a, ha⟩ := hs
  exact ⟨m, hm.trans h, a, ha⟩

theorem res_mem_J {A : ℕ → Type*} (e : ∀ n, A n → Γ(G, ⊤)) (U : G.Opens) {m n : ℕ} (h : m ≤ n)
    (a : A m) : res U (e m a) ∈ J e U n := by
  apply Ideal.subset_span
  simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_range, exists_prop]
  exact ⟨m, h, a, rfl⟩

theorem exists_J_stable {A : ℕ → Type*} (e : ∀ n, A n → Γ(G, ⊤)) (U : G.Opens)
    [IsNoetherianRing Γ(G, U)] : ∃ N, ∀ n, N ≤ n → J e U N = J e U n :=
  (monotone_stabilizes_iff_noetherian.mpr inferInstance) ⟨J e U, J_mono e U⟩

theorem J_le_ker {A : ℕ → Type*} (e : ∀ n, A n → Γ(G, ⊤)) (U : G.Opens) (n : ℕ)
    {T : Scheme.{u}} (x : T ⟶ G) (hx : ∀ m ≤ n, Kills e m x) :
    J e U n ≤ RingHom.ker (x.app U).hom := by
  apply Ideal.span_le.mpr
  intro s hs
  simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_range, exists_prop] at hs
  obtain ⟨m, hm, a, rfl⟩ := hs
  rw [SetLike.mem_coe, RingHom.mem_ker, app_res, hx m hm a, map_zero]

theorem exists_forall_kills_of_isNoetherian [IsNoetherian G] {A : ℕ → Type*}
    (e : ∀ n, A n → Γ(G, ⊤)) :
    ∃ N : ℕ, ∀ {T : Scheme.{u}} (x : T ⟶ G), (∀ n ≤ N, Kills e n x) → ∀ n, Kills e n x := by

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : G.affineOpens => (U.1 : Set G))
    (fun U => U.1.2) (fun g _ => by
      obtain ⟨_, ⟨U, hU, rfl⟩, hgU, -⟩ :=
        G.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ g) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hgU⟩)

  have hst : ∀ U : G.affineOpens, ∃ N, ∀ n, N ≤ n → J e U.1 N = J e U.1 n := fun U => by
    haveI : IsNoetherianRing Γ(G, U) := IsLocallyNoetherian.component_noetherian U
    exact exists_J_stable e U.1
  choose Nf hNf using hst
  refine ⟨t.sup Nf, fun {T} x hx n a => ?_⟩
  by_cases hn : n ≤ t.sup Nf
  · exact hx n hn a
  push Not at hn
  apply eq_zero_of_forall_res_eq_zero x (fun U : t => (U.1.1 : G.Opens))
  · intro g
    obtain ⟨U, hU, hgU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ g))
    exact ⟨⟨U, hU⟩, hgU⟩
  · rintro ⟨U, hU⟩
    have hle : Nf U ≤ t.sup Nf := Finset.le_sup hU
    have h1 : res U.1 (e n a) ∈ J e U.1 (t.sup Nf) := by
      have h2 : res U.1 (e n a) ∈ J e U.1 n := res_mem_J e U.1 le_rfl a
      rw [← hNf U n (hle.trans hn.le)] at h2
      exact J_mono e U.1 hle h2
    have h3 := J_le_ker e U.1 (t.sup Nf) x hx h1
    rw [RingHom.mem_ker, app_res] at h3
    exact h3

end Stabilization

section Matrix

variable {G : Scheme.{u}}

def eqns (d : ℕ → ℕ) (ρ : ∀ (n : ℕ) {T : Scheme.{u}}, (T ⟶ G) → GL (Fin (d n)) Γ(T, ⊤)) (n : ℕ)
    (ij : Fin (d n) × Fin (d n)) : Γ(G, ⊤) :=
  (ρ n (𝟙 G) : Matrix (Fin (d n)) (Fin (d n)) Γ(G, ⊤)) ij.1 ij.2 -
    (1 : Matrix (Fin (d n)) (Fin (d n)) Γ(G, ⊤)) ij.1 ij.2

theorem eq_one_iff_kills (d : ℕ → ℕ)
    (ρ : ∀ (n : ℕ) {T : Scheme.{u}}, (T ⟶ G) → GL (Fin (d n)) Γ(T, ⊤))
    (hρ : ∀ (n : ℕ) {T T' : Scheme.{u}} (ψ : T' ⟶ T) (x : T ⟶ G),
      ρ n (ψ ≫ x) = Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ n x))
    (n : ℕ) {T : Scheme.{u}} (x : T ⟶ G) :
    ρ n x = 1 ↔ Kills (eqns d ρ) n x := by
  have hx : ρ n x = Matrix.GeneralLinearGroup.map x.appTop.hom (ρ n (𝟙 G)) := by
    rw [← hρ n x (𝟙 G), Category.comp_id]
  constructor
  · intro h ij
    have h1 : (ρ n x : Matrix (Fin (d n)) (Fin (d n)) Γ(T, ⊤)) ij.1 ij.2 =
        (1 : GL (Fin (d n)) Γ(T, ⊤)) ij.1 ij.2 := by rw [h]
    rw [hx, Matrix.GeneralLinearGroup.map_apply] at h1
    simp only [eqns, map_sub, h1, Units.val_one]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro h
    apply Units.ext
    ext i j
    have h1 := h (i, j)
    simp only [eqns, map_sub, sub_eq_zero] at h1
    rw [hx, Matrix.GeneralLinearGroup.map_apply, h1, Units.val_one, Matrix.one_apply,
      Matrix.one_apply]
    split_ifs <;> simp

end Matrix

end AlgebraicGeometry.KernelTowerStabilization

end

open AlgebraicGeometry.KernelTowerStabilization in
theorem solution
    {G : Scheme.{u}} [IsNoetherian G] (d : ℕ → ℕ)
    (ρ : ∀ (n : ℕ) {T : Scheme.{u}}, (T ⟶ G) → GL (Fin (d n)) Γ(T, ⊤))
    (hρ : ∀ (n : ℕ) {T T' : Scheme.{u}} (ψ : T' ⟶ T) (x : T ⟶ G),
      ρ n (ψ ≫ x) = Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ n x)) :
    ∃ N : ℕ, ∀ {T : Scheme.{u}} (x : T ⟶ G), (∀ n ≤ N, ρ n x = 1) → ∀ n, ρ n x = 1 := by
  obtain ⟨N, hN⟩ := exists_forall_kills_of_isNoetherian (G := G) (eqns d ρ)
  refine ⟨N, fun {T} x hx n => ?_⟩
  rw [eq_one_iff_kills d ρ hρ]
  exact hN x (fun m hm => (eq_one_iff_kills d ρ hρ m x).mp (hx m hm)) n

end S_AlgebraicGeometry_exists_forall_generalLinearGroup_eq_one_of_forall_le_of_isNoetherian
end P2MW
export P2MW.S_AlgebraicGeometry_exists_forall_generalLinearGroup_eq_one_of_forall_le_of_isNoetherian (solution)
