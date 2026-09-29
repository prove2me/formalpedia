-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_finite_basicOpen_cover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/235d7f03-47bb-5178-905c-0a9b0fed2238

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules AffineScheme"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "basicOpen_res Γ affineOpens basicOpen Modules Opens basicOpen_le"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf isSheaf map_smul"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"
namespace LocGlue

variable {X : Scheme.{u}} (M : X.Modules)

noncomputable abbrev rM {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) := fun y => M.presheaf.map (homOfLE h).op y

noncomputable abbrev rO {V W : X.Opens} (h : V ≤ W) : Γ(X, W) → Γ(X, V) := fun g => X.presheaf.map (homOfLE h).op g

theorem rM_rM {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    rM M h₃₂ (rM M h₂₁ y) = rM M (h₃₂.trans h₂₁) y := by
  show (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

omit M in
theorem rO_rO {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (g : Γ(X, V₁)) :
    rO h₃₂ (rO h₂₁ g) = rO (h₃₂.trans h₂₁) g := by
  show (X.presheaf.map (homOfLE h₂₁).op ≫ X.presheaf.map (homOfLE h₃₂).op).hom g = _
  rw [← Functor.map_comp]; rfl

theorem rM_smul {V W : X.Opens} (h : V ≤ W) (g : Γ(X, W)) (y : Γ(M, W)) :
    rM M h (g • y) = rO h g • rM M h y := M.map_smul _ _ _

theorem rM_add {V W : X.Opens} (h : V ≤ W) (y z : Γ(M, W)) : rM M h (y + z) = rM M h y + rM M h z := map_add _ _ _
theorem rM_sub {V W : X.Opens} (h : V ≤ W) (y z : Γ(M, W)) : rM M h (y - z) = rM M h y - rM M h z := map_sub _ _ _
theorem rM_zero {V W : X.Opens} (h : V ≤ W) : rM M h (0 : Γ(M, W)) = 0 := map_zero _

omit M in
theorem rO_pow {V W : X.Opens} (h : V ≤ W) (g : Γ(X, W)) (n : ℕ) : rO h (g ^ n) = rO h g ^ n := map_pow _ _ _

noncomputable def F : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

theorem eq_of_forall_rM_eq {ι : Type u} (W : ι → X.Opens) (V : X.Opens) (hWV : ∀ i, W i ≤ V)
    (hcov : V ≤ iSup W) (y z : Γ(M, V)) (h : ∀ i, rM M (hWV i) y = rM M (hWV i) z) : y = z :=
  TopCat.Sheaf.eq_of_locally_eq' (F M) W V (fun i => homOfLE (hWV i)) hcov y z h

theorem exists_of_compatible {ι : Type u} (W : ι → X.Opens) (V : X.Opens) (hWV : ∀ i, W i ≤ V)
    (hcov : V ≤ iSup W) (z : ∀ i, Γ(M, W i))
    (hz : ∀ i j, rM M (inf_le_left : W i ⊓ W j ≤ W i) (z i) = rM M (inf_le_right : W i ⊓ W j ≤ W j) (z j)) :
    ∃ y : Γ(M, V), ∀ i, rM M (hWV i) y = z i := by
  obtain ⟨y, hy, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F M) W V (fun i => homOfLE (hWV i)) hcov z
    (fun i j => hz i j)
  exact ⟨y, hy⟩

end LocGlue

open LocGlue

def LocProp {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) (g : Γ(X, V)) : Prop :=
  (∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, V)),
      M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
        = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
    ∧ (∀ y : Γ(M, V), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
        ∃ n : ℕ, (g ^ n : Γ(X, V)) • y = 0)

namespace LocGlue

variable {X : Scheme.{u}} (M : X.Modules)

theorem pow_smul_eq_zero_of_le {V : X.Opens} (g : Γ(X, V)) (y : Γ(M, V)) {n k : ℕ} (hnk : n ≤ k)
    (h : (g ^ n : Γ(X, V)) • y = 0) : (g ^ k : Γ(X, V)) • y = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
  rw [add_comm, pow_add, mul_smul, h, smul_zero]

theorem exists_of_le {V : X.Opens} (g : Γ(X, V)) (x : Γ(M, X.basicOpen g)) {n k : ℕ} (hnk : n ≤ k)
    (y : Γ(M, V)) (h : rM M (X.basicOpen_le g) y = rO (X.basicOpen_le g) (g ^ n) • x) :
    rM M (X.basicOpen_le g) ((g ^ (k - n) : Γ(X, V)) • y) = rO (X.basicOpen_le g) (g ^ k) • x := by
  rw [rM_smul, h, ← mul_smul, ← map_mul, ← pow_add, Nat.sub_add_cancel hnk]

end LocGlue

open LocGlue in
theorem isLocalization_basicOpen_of_finite_basicOpen_cover'
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens) (s : Finset Γ(X, U.1))
    (hs : U.1 ≤ ⨆ h ∈ s, X.basicOpen h)
    (hloc : ∀ h ∈ s, ∀ g : Γ(X, X.basicOpen h),
      ((∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, X.basicOpen h)),
          M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
        ∧ (∀ y : Γ(M, X.basicOpen h), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n : Γ(X, X.basicOpen h)) • y = 0)))
    (hloc₂ : ∀ h ∈ s, ∀ h' ∈ s, ∀ g : Γ(X, X.basicOpen h ⊓ X.basicOpen h'),
      ((∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, (X.basicOpen h ⊓ X.basicOpen h'))),
          M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
        ∧ (∀ y : Γ(M, (X.basicOpen h ⊓ X.basicOpen h')), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n : Γ(X, (X.basicOpen h ⊓ X.basicOpen h'))) • y = 0)))
    (f : Γ(X, U.1)) :
    ((∀ x : Γ(M, X.basicOpen f), ∃ (n : ℕ) (y : Γ(M, U.1)),
          M.presheaf.map (homOfLE (X.basicOpen_le f)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • x)
        ∧ (∀ y : Γ(M, U.1), M.presheaf.map (homOfLE (X.basicOpen_le f)).op y = 0 →
            ∃ n : ℕ, (f ^ n : Γ(X, U.1)) • y = 0)) := by
  classical

  let ι : Type u := {h // h ∈ s}
  let D : ι → X.Opens := fun i => X.basicOpen i.1
  have hDU : ∀ i, D i ≤ U.1 := fun i => X.basicOpen_le _
  have hcovU : U.1 ≤ iSup D := by
    refine hs.trans ?_
    simp only [iSup_le_iff]
    intro h hh
    exact le_iSup D ⟨h, hh⟩

  let W : ι → X.Opens := fun i => X.basicOpen (rO (hDU i) f)
  have hW_eq : ∀ i, W i = D i ⊓ X.basicOpen f := fun i => X.basicOpen_res f (homOfLE (hDU i)).op
  have hWD : ∀ i, W i ≤ D i := fun i => X.basicOpen_le _
  have hWf : ∀ i, W i ≤ X.basicOpen f := fun i => by rw [hW_eq]; exact inf_le_right
  have hcovf : X.basicOpen f ≤ iSup W := by
    intro p hp
    have hpU : p ∈ (iSup D : X.Opens) := hcovU (X.basicOpen_le f hp)
    rw [Opens.mem_iSup] at hpU ⊢
    obtain ⟨i, hi⟩ := hpU
    exact ⟨i, by rw [hW_eq]; exact ⟨hi, hp⟩⟩
  refine ⟨?_, ?_⟩
  ·
    intro x
    have step1 : ∀ i, ∃ (n : ℕ) (yi : Γ(M, D i)),
        rM M (hWD i) yi = rO (hWD i) (rO (hDU i) f ^ n) • rM M (hWf i) x :=
      fun i => (hloc i.1 i.2 (rO (hDU i) f)).1 (rM M (hWf i) x)
    choose n0 y0 hy0 using step1
    let n : ℕ := Finset.univ.sup n0

    obtain ⟨y1, hy1⟩ : ∃ y1 : ∀ i, Γ(M, D i),
        ∀ i, rM M (hWD i) (y1 i) = rO ((hWD i).trans (hDU i)) f ^ n • rM M (hWf i) x := by
      refine ⟨fun i => (rO (hDU i) f ^ (n - n0 i) : Γ(X, D i)) • y0 i, fun i => ?_⟩
      have := exists_of_le M (rO (hDU i) f) (rM M (hWf i) x) (Finset.le_sup (f := n0) (Finset.mem_univ i))
        (y0 i) (hy0 i)
      rw [rO_pow, rO_rO] at this
      exact this

    have step2 : ∀ ij : ι × ι, ∃ m : ℕ,
        (rO ((inf_le_left : D ij.1 ⊓ D ij.2 ≤ D ij.1).trans (hDU ij.1)) f ^ m : Γ(X, D ij.1 ⊓ D ij.2))
          • (rM M inf_le_left (y1 ij.1) - rM M inf_le_right (y1 ij.2)) = 0 := by
      rintro ⟨i, j⟩

      have hg : rO ((inf_le_left : D i ⊓ D j ≤ D i).trans (hDU i)) f = rO (inf_le_left : D i ⊓ D j ≤ D i) (rO (hDU i) f) :=
        (rO_rO _ _ f).symm
      have hg' : rO ((inf_le_left : D i ⊓ D j ≤ D i).trans (hDU i)) f = rO (inf_le_right : D i ⊓ D j ≤ D j) (rO (hDU j) f) :=
        (rO_rO _ _ f).symm
      have hWij_i : X.basicOpen (rO ((inf_le_left : D i ⊓ D j ≤ D i).trans (hDU i)) f) ≤ W i := by
        rw [hg, X.basicOpen_res (rO (hDU i) f) (homOfLE (inf_le_left : D i ⊓ D j ≤ D i)).op]; exact inf_le_right
      have hWij_j : X.basicOpen (rO ((inf_le_left : D i ⊓ D j ≤ D i).trans (hDU i)) f) ≤ W j := by
        rw [hg', X.basicOpen_res (rO (hDU j) f) (homOfLE (inf_le_right : D i ⊓ D j ≤ D j)).op]; exact inf_le_right
      apply (hloc₂ i.1 i.2 j.1 j.2 (rO ((inf_le_left : D i ⊓ D j ≤ D i).trans (hDU i)) f)).2
      show rM M (X.basicOpen_le _) (rM M inf_le_left (y1 i) - rM M inf_le_right (y1 j)) = 0
      rw [rM_sub, rM_rM, rM_rM]
      have hi : rM M ((X.basicOpen_le _).trans inf_le_left) (y1 i) = rM M hWij_i (rM M (hWD i) (y1 i)) := by
        rw [rM_rM]
      have hj : rM M ((X.basicOpen_le _).trans inf_le_right) (y1 j) = rM M hWij_j (rM M (hWD j) (y1 j)) := by
        rw [rM_rM]
      rw [hi, hj, hy1, hy1]
      simp only [rM_smul, rM_rM, rO_pow, rO_rO, sub_self]
    choose m0 hm0 using step2
    let m : ℕ := Finset.univ.sup m0
    obtain ⟨z, hzdef⟩ : ∃ z : ∀ i, Γ(M, D i), ∀ i, z i = (rO (hDU i) f ^ m : Γ(X, D i)) • y1 i :=
      ⟨fun i => (rO (hDU i) f ^ m : Γ(X, D i)) • y1 i, fun i => rfl⟩
    have hz : ∀ i j, rM M (inf_le_left : D i ⊓ D j ≤ D i) (z i) = rM M (inf_le_right : D i ⊓ D j ≤ D j) (z j) := by
      intro i j
      rw [hzdef, hzdef, rM_smul, rM_smul, rO_pow, rO_pow, rO_rO, rO_rO, ← sub_eq_zero, ← smul_sub]
      exact pow_smul_eq_zero_of_le M _ _ (Finset.le_sup (f := m0) (Finset.mem_univ (i, j))) (hm0 (i, j))
    obtain ⟨y, hy⟩ := exists_of_compatible M D U.1 hDU hcovU z hz
    refine ⟨m + n, y, ?_⟩

    apply eq_of_forall_rM_eq M W (X.basicOpen f) hWf hcovf
    intro i
    show rM M (hWf i) (rM M (X.basicOpen_le f) y) = rM M (hWf i) (rO (X.basicOpen_le f) (f ^ (m + n)) • x)
    have : rM M (hWf i) (rM M (X.basicOpen_le f) y) = rM M (hWD i) (rM M (hDU i) y) := by rw [rM_rM, rM_rM]
    rw [this, hy, hzdef, rM_smul, hy1, rM_smul]
    simp only [rO_pow, rO_rO, ← mul_smul, ← pow_add]
  ·
    intro y hy
    have step : ∀ i, ∃ n : ℕ, (rO (hDU i) f ^ n : Γ(X, D i)) • rM M (hDU i) y = 0 := by
      intro i
      apply (hloc i.1 i.2 (rO (hDU i) f)).2
      show rM M (hWD i) (rM M (hDU i) y) = 0
      have : rM M (hWD i) (rM M (hDU i) y) = rM M (hWf i) (rM M (X.basicOpen_le f) y) := by rw [rM_rM, rM_rM]
      rw [this]
      show rM M (hWf i) (M.presheaf.map (homOfLE (X.basicOpen_le f)).op y) = 0
      rw [hy, rM_zero]
    choose nOf hnOf using step
    refine ⟨Finset.univ.sup nOf, ?_⟩
    apply eq_of_forall_rM_eq M D U.1 hDU hcovU
    intro i
    rw [rM_smul, rM_zero, rO_pow]
    exact pow_smul_eq_zero_of_le M _ _ (Finset.le_sup (f := nOf) (Finset.mem_univ i)) (hnOf i)

end AlgebraicGeometry.Scheme.Modules

theorem solution
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens) (s : Finset Γ(X, U.1))
    (hs : U.1 ≤ ⨆ h ∈ s, X.basicOpen h)
    (hloc : ∀ h ∈ s, ∀ g : Γ(X, X.basicOpen h),
      ((∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, X.basicOpen h)),
          M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
        ∧ (∀ y : Γ(M, X.basicOpen h), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n : Γ(X, X.basicOpen h)) • y = 0)))
    (hloc₂ : ∀ h ∈ s, ∀ h' ∈ s, ∀ g : Γ(X, X.basicOpen h ⊓ X.basicOpen h'),
      ((∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, (X.basicOpen h ⊓ X.basicOpen h'))),
          M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
        ∧ (∀ y : Γ(M, (X.basicOpen h ⊓ X.basicOpen h')), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n : Γ(X, (X.basicOpen h ⊓ X.basicOpen h'))) • y = 0)))
    (f : Γ(X, U.1)) :
    ((∀ x : Γ(M, X.basicOpen f), ∃ (n : ℕ) (y : Γ(M, U.1)),
          M.presheaf.map (homOfLE (X.basicOpen_le f)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • x)
        ∧ (∀ y : Γ(M, U.1), M.presheaf.map (homOfLE (X.basicOpen_le f)).op y = 0 →
            ∃ n : ℕ, (f ^ n : Γ(X, U.1)) • y = 0)) :=
  AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_finite_basicOpen_cover' M U s hs hloc hloc₂ f

end S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover (solution)
