-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial_of_qcqs
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0545ddb9-9135-5876-bf94-07bbd16bca34

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial_of_qcqs

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial_of_qcqs.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "compact_open_induction_on Scheme.Modules.pullback isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens Scheme Scheme.Modules"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "basicOpen_res ringCatSheaf Modules.pullback Γ basicOpen Modules Opens basicOpen_le"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf isSheaf map_smul isLocalization_basicOpen_of_locallyTrivial"
namespace SectLoc
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}} (M : X.Modules)

noncomputable abbrev rM {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) := fun y => M.presheaf.map (homOfLE h).op y

noncomputable abbrev rO {V W : X.Opens} (h : V ≤ W) : Γ(X, W) → Γ(X, V) :=
  fun g => (X.presheaf.map (homOfLE h).op).hom g

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

theorem rM_zero {V W : X.Opens} (h : V ≤ W) : rM M h 0 = 0 := map_zero _
theorem rM_sub {V W : X.Opens} (h : V ≤ W) (a b : Γ(M, W)) : rM M h (a - b) = rM M h a - rM M h b := map_sub _ _ _

omit M in
theorem rO_pow {V W : X.Opens} (h : V ≤ W) (g : Γ(X, W)) (n : ℕ) : rO h (g ^ n) = rO h g ^ n := map_pow _ _ _

noncomputable def F : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

theorem eq_of_le_bot {W : X.Opens} (hW : W ≤ ⊥) (s t : Γ(M, W)) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (F M) (fun _ : Empty => (⊥ : X.Opens)) W (fun i => i.elim)
    (hW.trans bot_le) s t (fun i => i.elim)

theorem glue₂ {S V : X.Opens} (a : Γ(M, S)) (b : Γ(M, V))
    (h : rM M (inf_le_left : S ⊓ V ≤ S) a = rM M (inf_le_right : S ⊓ V ≤ V) b) :
    ∃ y : Γ(M, S ⊔ V), rM M le_sup_left y = a ∧ rM M le_sup_right y = b := by
  let U2 : Bool → X.Opens := fun c => cond c V S
  have hsup : S ⊔ V ≤ iSup U2 := sup_le (le_iSup U2 false) (le_iSup U2 true)
  let sf : ∀ c : Bool, (F M).1.obj (op (U2 c)) := fun c => match c with
    | false => a
    | true => b
  have hle : ∀ c : Bool, U2 c ≤ S ⊔ V := fun c => by cases c <;> simp [U2]
  have hcomp : TopCat.Presheaf.IsCompatible (F M).1 U2 sf := by
    intro i j
    show M.presheaf.map _ (sf i) = M.presheaf.map _ (sf j)
    rw [Subsingleton.elim ((U2 i).infLELeft (U2 j)) (homOfLE inf_le_left),
      Subsingleton.elim ((U2 i).infLERight (U2 j)) (homOfLE inf_le_right)]
    cases i <;> cases j
    · rfl
    · exact h
    · show rM M (inf_le_left : V ⊓ S ≤ V) b = rM M (inf_le_right : V ⊓ S ≤ S) a
      have h10 : V ⊓ S ≤ S ⊓ V := le_of_eq (inf_comm _ _)
      rw [← rM_rM M inf_le_right h10, ← rM_rM M inf_le_left h10, h]
    · rfl
  obtain ⟨y, hy, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F M) U2 (S ⊔ V) (fun c => homOfLE (hle c))
    hsup sf hcomp
  exact ⟨y, hy false, hy true⟩

variable (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
  Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))

include htriv in

theorem ker_of_isCompact {U : X.Opens} (hU : IsCompact (U : Set X)) (f : Γ(X, U)) (y : Γ(M, U))
    (hy : rM M (X.basicOpen_le f) y = 0) : ∃ n : ℕ, (f ^ n : Γ(X, U)) • y = 0 := by
  classical
  obtain ⟨s, hs, e⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU, U.2⟩
  replace e : U = iSup fun i : s => (i : X.Opens) := by ext1; simpa using e
  have h₁ : ∀ i : s, (i : X.Opens) ≤ U := fun i => by
    rw [e]; exact le_iSup (fun i : s => (i : X.Opens)) i

  have H' : ∀ i : s, ∃ n : ℕ, (rO (h₁ i) f ^ n) • rM M (h₁ i) y = 0 := by
    intro i
    have hle : X.basicOpen (rO (h₁ i) f) ≤ X.basicOpen f := by
      rw [show rO (h₁ i) f = X.presheaf.map (homOfLE (h₁ i)).op f from rfl, X.basicOpen_res]
      exact inf_le_right
    refine (isLocalization_basicOpen_of_locallyTrivial M htriv i.1 (rO (h₁ i) f)).2 _ ?_
    show rM M (X.basicOpen_le _) (rM M (h₁ i) y) = 0
    rw [rM_rM, ← rM_rM M (X.basicOpen_le f) hle, hy, rM_zero]
  choose n hn using H'
  haveI := hs.to_subtype
  cases nonempty_fintype s
  refine ⟨Finset.univ.sup n, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' (F M) (fun i : s => (i : X.Opens)) U (fun i => homOfLE (h₁ i)) (le_of_eq e)
  intro i
  show rM M (h₁ i) _ = rM M (h₁ i) 0
  rw [rM_zero, rM_smul, rO_pow, ← tsub_add_cancel_of_le (Finset.le_sup (f := n) (Finset.mem_univ i)), pow_add,
    mul_smul, hn, smul_zero]

include htriv in

theorem surj_of_qcqs {U : X.Opens} (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X))
    (f : Γ(X, U)) (x : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (y : Γ(M, U)), rM M (X.basicOpen_le f) y = rO (X.basicOpen_le f) (f ^ n) • x := by
  revert hU' f x
  refine compact_open_induction_on U hU ?_ ?_
  · intro _ f x
    exact ⟨0, 0, eq_of_le_bot M (X.basicOpen_le f) _ _⟩
  · intro S hS V IH hqs f x
    have hqsS : IsQuasiSeparated (S : Set X) := hqs.of_subset Set.subset_union_left

    set f₁ : Γ(X, S) := rO le_sup_left f with hf₁
    set f₂ : Γ(X, V.1) := rO le_sup_right f with hf₂
    have hD₁ : X.basicOpen f₁ = S ⊓ X.basicOpen f := X.basicOpen_res f (homOfLE le_sup_left).op
    have hD₂ : X.basicOpen f₂ = V.1 ⊓ X.basicOpen f := X.basicOpen_res f (homOfLE le_sup_right).op
    have h₁f : X.basicOpen f₁ ≤ X.basicOpen f := hD₁.trans_le inf_le_right
    have h₂f : X.basicOpen f₂ ≤ X.basicOpen f := hD₂.trans_le inf_le_right
    obtain ⟨n₁, y₁, hy₁⟩ := IH hqsS f₁ (rM M h₁f x)
    obtain ⟨n₂, y₂, hy₂⟩ := (isLocalization_basicOpen_of_locallyTrivial M htriv V f₂).1 (rM M h₂f x)
    change rM M (X.basicOpen_le f₂) y₂ = rO (X.basicOpen_le f₂) (f₂ ^ n₂) • rM M h₂f x at hy₂

    have hT : IsCompact ((S ⊓ V.1 : X.Opens) : Set X) :=
      hqs _ _ Set.subset_union_left S.2 hS Set.subset_union_right V.1.2 V.2.isCompact
    have hTS : (S ⊓ V.1 : X.Opens) ≤ S := inf_le_left
    have hTV : (S ⊓ V.1 : X.Opens) ≤ V.1 := inf_le_right
    set g : Γ(X, S ⊓ V.1) := rO (hTS.trans le_sup_left) f with hg
    have hg₁ : rO hTS f₁ = g := by rw [hf₁, hg, rO_rO]
    have hg₂ : rO hTV f₂ = g := by rw [hf₂, hg, rO_rO]
    have hDg : X.basicOpen g = (S ⊓ V.1) ⊓ X.basicOpen f :=
      X.basicOpen_res f (homOfLE (hTS.trans le_sup_left)).op
    have hgf : X.basicOpen g ≤ X.basicOpen f := hDg.trans_le inf_le_right
    have hgU : X.basicOpen g ≤ S ⊔ V.1 := (X.basicOpen_le g).trans (hTS.trans le_sup_left)
    have hg1 : X.basicOpen g ≤ X.basicOpen f₁ := by
      rw [hDg, hD₁]; exact inf_le_inf_right _ inf_le_left
    have hg2 : X.basicOpen g ≤ X.basicOpen f₂ := by
      rw [hDg, hD₂]; exact inf_le_inf_right _ inf_le_right

    let z : Γ(M, S ⊓ V.1) := rM M hTS (f₁ ^ n₂ • y₁) - rM M hTV (f₂ ^ n₁ • y₂)

    have key₁ : rM M (X.basicOpen_le g) (rM M hTS y₁) = rO hgU (f ^ n₁) • rM M hgf x := by
      rw [rM_rM, ← rM_rM M (X.basicOpen_le f₁) hg1, hy₁, rM_smul, rM_rM, rO_rO]
      simp only [hf₁, rO_pow, rO_rO]
    have key₂ : rM M (X.basicOpen_le g) (rM M hTV y₂) = rO hgU (f ^ n₂) • rM M hgf x := by
      rw [rM_rM, ← rM_rM M (X.basicOpen_le f₂) hg2, hy₂, rM_smul, rM_rM, rO_rO]
      simp only [hf₂, rO_pow, rO_rO]
    have kf₁ : rO (X.basicOpen_le g) (rO hTS f₁) = rO hgU f := by rw [hf₁, rO_rO, rO_rO]
    have kf₂ : rO (X.basicOpen_le g) (rO hTV f₂) = rO hgU f := by rw [hf₂, rO_rO, rO_rO]
    have hz : rM M (X.basicOpen_le g) z = 0 := by
      show rM M (X.basicOpen_le g) (rM M hTS (f₁ ^ n₂ • y₁) - rM M hTV (f₂ ^ n₁ • y₂)) = 0
      rw [rM_sub, rM_smul, rM_smul, rM_smul, rM_smul, rO_pow, rO_pow, rO_pow, rO_pow, kf₁, kf₂, key₁, key₂,
        ← mul_smul, ← mul_smul, rO_pow, rO_pow, ← pow_add, ← pow_add, add_comm, sub_self]
    obtain ⟨m, hm⟩ := ker_of_isCompact M htriv hT g z hz

    have hagree : rM M (inf_le_left : S ⊓ V.1 ≤ S) (f₁ ^ (m + n₂) • y₁)
        = rM M (inf_le_right : S ⊓ V.1 ≤ V.1) (f₂ ^ (m + n₁) • y₂) := by
      have hm' : g ^ m • rM M hTS (f₁ ^ n₂ • y₁) = g ^ m • rM M hTV (f₂ ^ n₁ • y₂) := by
        rw [← sub_eq_zero, ← smul_sub]; exact hm
      rw [pow_add, mul_smul, rM_smul, rO_pow, hg₁, pow_add, mul_smul, rM_smul _ hTV (f₂ ^ m), rO_pow, hg₂]
      exact hm'
    obtain ⟨y, hyS, hyV⟩ := glue₂ M _ _ hagree
    refine ⟨m + n₁ + n₂, y, ?_⟩

    have hcov : X.basicOpen f ≤ X.basicOpen f₁ ⊔ X.basicOpen f₂ := by
      intro p hp
      have hp' : p ∈ S ⊔ V.1 := X.basicOpen_le f hp
      rcases Opens.mem_sup.mp hp' with h | h
      · exact Opens.mem_sup.mpr (Or.inl (by rw [hD₁]; exact ⟨h, hp⟩))
      · exact Opens.mem_sup.mpr (Or.inr (by rw [hD₂]; exact ⟨h, hp⟩))
    apply TopCat.Sheaf.eq_of_locally_eq₂ (F M) (homOfLE h₁f) (homOfLE h₂f) hcov
    · show rM M h₁f (rM M (X.basicOpen_le f) y) = rM M h₁f (rO (X.basicOpen_le f) (f ^ (m + n₁ + n₂)) • x)
      rw [rM_rM, ← rM_rM M (le_sup_left : S ≤ S ⊔ V.1) (X.basicOpen_le f₁), hyS, rM_smul, hy₁, rM_smul,
        ← mul_smul, rO_pow, rO_pow, rO_rO, rO_rO, ← pow_add]
      show rO _ f ^ (m + n₂ + n₁) • rM M h₁f x = _
      rw [show m + n₂ + n₁ = m + n₁ + n₂ by omega, rO_pow]
    · show rM M h₂f (rM M (X.basicOpen_le f) y) = rM M h₂f (rO (X.basicOpen_le f) (f ^ (m + n₁ + n₂)) • x)
      rw [rM_rM, ← rM_rM M (le_sup_right : V.1 ≤ S ⊔ V.1) (X.basicOpen_le f₂), hyV, rM_smul, hy₂, rM_smul,
        ← mul_smul, rO_pow, rO_pow, rO_rO, rO_rO, ← pow_add]
      show rO _ f ^ (m + n₁ + n₂) • rM M h₂f x = _
      rw [rO_pow]

end AlgebraicGeometry.Scheme.Modules.SectLoc

theorem solution
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    {U : X.Opens} (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) :
    ((∀ x : Γ(M, X.basicOpen f), ∃ (n : ℕ) (y : Γ(M, U)),
          M.presheaf.map (homOfLE (X.basicOpen_le f)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • x)
        ∧ (∀ y : Γ(M, U), M.presheaf.map (homOfLE (X.basicOpen_le f)).op y = 0 →
            ∃ n : ℕ, (f ^ n : Γ(X, U)) • y = 0)) :=
  ⟨fun x => AlgebraicGeometry.Scheme.Modules.SectLoc.surj_of_qcqs M htriv hU hU' f x,
    fun y hy => AlgebraicGeometry.Scheme.Modules.SectLoc.ker_of_isCompact M htriv hU f y hy⟩

end S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial_of_qcqs
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial_of_qcqs (solution)
