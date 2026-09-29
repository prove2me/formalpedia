-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b8474915-565e-5212-bae5-270c402df798

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GluedPres

variable {Y : Scheme.{0}} {r : ℕ} {V : Fin r → Y.Opens} (c : UnitCocycle V)

def Compat (x : ∀ j : Fin r, Γ(Y, V j)) : Prop :=
  ∀ i j, rO (inf_le_left : V i ⊓ V j ≤ V i) (x i) = c.u i j * rO (inf_le_right : V i ⊓ V j ≤ V j) (x j)

noncomputable def sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) : Γ(glueOfCocycle c, ⊤) :=
  glueMk c ⊤ (fun j => rO (inf_le_right : ⊤ ⊓ V j ≤ V j) (x j)) fun i j => by
    rw [rO_rO, rO_rO]
    have h := congrArg (rO (leij ⊤ i j)) (hx i j)
    rw [map_mul, rO_rO, rO_rO] at h
    exact h

theorem glueComponent_sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (j : Fin r) :
    glueComponent c ⊤ j (sec c x hx) = rO (inf_le_right : ⊤ ⊓ V j ≤ V j) (x j) := rfl

theorem glueComponent_map_sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) {W : Y.Opens} (j : Fin r) :
    glueComponent c W j ((glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (sec c x hx)) =
      rO (inf_le_right : W ⊓ V j ≤ V j) (x j) := by
  rw [glueComponent_map, glueComponent_sec, rO_rO]

theorem map_sec_eq_glueFrame (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (i : Fin r)
    (hxi : ∀ j, rO (inf_le_left : V j ⊓ V i ≤ V j) (x j) = c.u j i) :
    (glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (sec c x hx) = glueFrame c i := by
  apply glue_ext
  intro j
  rw [glueComponent_map_sec, glueComponent_glueFrame, ← hxi j, rO_rO]

theorem bijective_smul_of_map_eq_glueFrame (s : Γ(glueOfCocycle c, ⊤)) (i : Fin r)
    (hs : (glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op s = glueFrame c i)
    (W : Y.Opens) (hW : W ≤ V i) :
    Function.Bijective fun g : Γ(Y, W) => g • ((glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s : Γ(glueOfCocycle c, W)) := by
  have key : (glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s =
      (glueOfCocycle c).presheaf.map (homOfLE hW).op (glueFrame c i) := by
    rw [← hs]
    change _ = ((glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op ≫
      (glueOfCocycle c).presheaf.map (homOfLE hW).op) s
    rw [← Functor.map_comp]; rfl
  rw [key]
  exact isFrameOn_glueFrame c i hW hW

theorem subsingleton_sections_bot (M : Y.Modules) : Subsingleton (M.val.obj (op (⊥ : Y.Opens))) := by
  have hbot : (⊥ : Sieve (⊥ : Y.Opens)) ∈ (Opens.grothendieckTopology ↥Y) (⊥ : Y.Opens) :=
    fun x hx => (Opens.mem_bot.1 hx).elim
  have hT : Limits.IsTerminal (M.val.presheaf.obj (op (⊥ : Y.Opens))) :=
    Sheaf.isTerminalOfBotCover ⟨M.val.presheaf, M.isSheaf⟩ (⊥ : Y.Opens) hbot
  have h0 : (𝟙 (M.val.presheaf.obj (op (⊥ : Y.Opens))) : _ ⟶ _) = 0 := hT.hom_ext _ _
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) a) h0
    simp at this
    exact this
  have hb : b = 0 := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) b) h0
    simp at this
    exact this
  rw [ha, hb]

theorem subsingleton_functions_bot : Subsingleton (Γ(Y, (⊥ : Y.Opens)) : Type _) := by
  have hbot : (⊥ : Sieve (⊥ : Y.Opens)) ∈ (Opens.grothendieckTopology ↥Y) (⊥ : Y.Opens) :=
    fun x hx => (Opens.mem_bot.1 hx).elim
  have hT : Limits.IsTerminal (Y.sheaf.val.obj (op (⊥ : Y.Opens))) :=
    Sheaf.isTerminalOfBotCover Y.sheaf (⊥ : Y.Opens) hbot
  let e := hT.uniqueUpToIso CommRingCat.punitIsTerminal
  refine ⟨fun a b => ?_⟩
  have h1 : ∀ x : Γ(Y, (⊥ : Y.Opens)), e.inv.hom (e.hom.hom x) = x := fun x => by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) x) e.hom_inv_id
    simpa using this
  rw [← h1 a, ← h1 b, Subsingleton.elim (e.hom.hom a) (e.hom.hom b)]

theorem bijective_smul_bot (M : Y.Modules) (s : Γ(M, ⊤)) (W : Y.Opens) (hW : W ≤ ⊥) :
    Function.Bijective fun g : Γ(Y, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s : Γ(M, W)) := by
  have hW' : W = ⊥ := le_bot_iff.1 hW
  subst hW'
  haveI : Subsingleton (Γ(M, (⊥ : Y.Opens)) : Type _) := subsingleton_sections_bot M
  haveI : Subsingleton (Γ(Y, (⊥ : Y.Opens)) : Type _) := subsingleton_functions_bot
  exact ⟨fun a b _ => Subsingleton.elim a b, fun m => ⟨0, Subsingleton.elim _ _⟩⟩

theorem isUnit_of_frames {M : Y.Modules} {W : Y.Opens} (s t : Γ(M, W))
    (hs : Function.Bijective fun g : Γ(Y, W) => g • s) (ht : Function.Bijective fun g : Γ(Y, W) => g • t)
    (f : Γ(Y, W)) (h : s = f • t) : IsUnit f := by
  obtain ⟨f', hf'⟩ := hs.2 t
  have hf'' : f' • s = t := hf'
  have h1 : (f * f') • s = (1 : Γ(Y, W)) • s := by
    rw [one_smul, mul_smul, hf'', ← h]
  exact isUnit_iff_exists_inv.2 ⟨f', hs.1 h1⟩

theorem inf_le_basicOpen_of_frame (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (W : Y.Opens)
    (hW : ∀ W' : Y.Opens, W' ≤ W → Function.Bijective fun g : Γ(Y, W') =>
      g • ((glueOfCocycle c).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (sec c x hx) : Γ(glueOfCocycle c, W')))
    (j : Fin r) : W ⊓ V j ≤ Y.basicOpen (x j) := by

  set W' : Y.Opens := W ⊓ V j with hW'
  let s : Γ(glueOfCocycle c, W') := (glueOfCocycle c).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (sec c x hx)
  let t : Γ(glueOfCocycle c, W') := (glueOfCocycle c).presheaf.map (homOfLE (inf_le_right : W' ≤ V j)).op (glueFrame c j)
  have hs : Function.Bijective fun g : Γ(Y, W') => g • s := hW W' inf_le_left
  have ht : Function.Bijective fun g : Γ(Y, W') => g • t := isFrameOn_glueFrame c j (inf_le_right : W' ≤ V j) inf_le_right
  obtain ⟨f, hf⟩ := ht.2 s
  have hfu : IsUnit f := isUnit_of_frames s t hs ht f hf.symm

  have hcomp : rO (inf_le_right : W' ⊓ V j ≤ V j) (x j) = rO (inf_le_left : W' ⊓ V j ≤ W') f := by
    have h1 := congrArg (glueComponent c W' j) hf
    rw [glueComponent_smul, glueComponent_map, glueComponent_glueFrame, rO_rO,
      show rO ((inf_le_inf_right (V j) (inf_le_right : W' ≤ V j)).trans (le_of_eq (inf_comm (V j) (V j)))) (c.u j j) = 1 by
        rw [c.refl, map_one], mul_one] at h1
    rw [h1]
    exact (glueComponent_map_sec c x hx j).symm
  have hu : IsUnit (rO (inf_le_right : W' ⊓ V j ≤ V j) (x j)) := by rw [hcomp]; exact hfu.map _
  have hb := Y.basicOpen_of_isUnit hu
  rw [show rO (inf_le_right : W' ⊓ V j ≤ V j) (x j) = Y.presheaf.map (homOfLE (inf_le_right : W' ⊓ V j ≤ V j)).op (x j) from rfl,
    Scheme.basicOpen_res] at hb
  calc W ⊓ V j = W' ⊓ V j := by rw [hW', inf_assoc, inf_idem]
    _ = W' ⊓ V j ⊓ Y.basicOpen (x j) := hb.symm
    _ ≤ Y.basicOpen (x j) := inf_le_right

theorem eq_of_smul_sec_eq {x x' : ∀ j : Fin r, Γ(Y, V j)} (hx : Compat c x) (hx' : Compat c x') (i : Fin r)
    (hxi : x i = 1) {D : Y.Opens} (hD : V i ≤ D) (g : Γ(Y, D))
    (h : g • (glueOfCocycle c).presheaf.map (homOfLE (le_top : D ≤ ⊤)).op (sec c x hx) =
      (glueOfCocycle c).presheaf.map (homOfLE (le_top : D ≤ ⊤)).op (sec c x' hx')) :
    rO hD g = x' i := by

  have h2 := congrArg (glueComponent c D i) h
  rw [glueComponent_smul, glueComponent_map_sec, glueComponent_map_sec, hxi, map_one, mul_one] at h2

  have hinj := (rO_bijective_of_le_le (inf_le_right : D ⊓ V i ≤ V i) (le_inf hD le_rfl)).1
  apply hinj
  rw [rO_rO]
  exact h2

end GluedPres

open GluedPres in
theorem solution
    (B : Type) [CommRing B] (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of B))
    (r : ℕ) (V : Fin r → Y.Opens) (hVaff : ∀ i, IsAffineOpen (V i)) (hcov : (⨆ i, V i) = ⊤)
    (w : ∀ i j : Fin r, Γ(Y, V i)) (hw1 : ∀ i, w i i = 1)
    (hw3 : ∀ i j : Fin r, Y.basicOpen (w i j) = V i ⊓ V j)
    (k : ℕ) (hk : 0 < k) (c : Scheme.Modules.UnitCocycle V)
    (hc : ∀ i j : Fin r, c.u i j = Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) ^ k)
    (N : ℕ) (a : Fin (N + 1) → ∀ j : Fin r, Γ(Y, V j))
    (ha : ∀ (α : Fin (N + 1)) (j m : Fin r),
      Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (a α j) =
        Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
          Y.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (a α m))
    (e : Fin r → Fin (N + 1)) (he : Function.Injective e) (hae : ∀ i j : Fin r, a (e i) j = w j i ^ k) :
    ∃ 𝔓 : (Scheme.Modules.glueOfCocycle c).ProjPresentation πY N,
      (∀ (α : Fin (N + 1)) (j : Fin r), Scheme.Modules.glueComponent c ⊤ j (𝔓.σ α) =
        Y.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V j ≤ V j)).op (a α j)) ∧
      ∃ hV : ∀ i : Fin r, V i ≤ 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)),
        (∀ i : Fin r, 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)) = V i) ∧
        (∀ (i : Fin r) (α : Fin (N + 1)),
          𝔓.toProj.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)))
              (V i) (hV i)
            (Proj.awayToSection _ (MvPolynomial.X (e i)) (ProjSpace.ratio B N (e i) α)) = a α i) := by
  classical

  have hx : ∀ α : Fin (N + 1), Compat c (a α) := by
    intro α i j
    show rO _ (a α i) = c.u i j * rO _ (a α j)
    rw [hc]
    exact ha α i j
  let σ : Fin (N + 1) → Γ(Scheme.Modules.glueOfCocycle c, ⊤) := fun α => sec c (a α) (hx α)

  have hσe : ∀ i : Fin r,
      (Scheme.Modules.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (σ (e i)) = Scheme.Modules.glueFrame c i := by
    intro i
    refine map_sec_eq_glueFrame c (a (e i)) (hx _) i fun j => ?_
    show rO _ (a (e i) j) = c.u j i
    rw [hae, map_pow, hc]

  let U' : Fin (N + 1) → Y.Opens := fun α => if h : ∃ i, e i = α then V h.choose else ⊥
  have hU'e : ∀ i, U' (e i) = V i := by
    intro i
    have h : ∃ i', e i' = e i := ⟨i, rfl⟩
    simp only [U', dif_pos h]
    rw [he h.choose_spec]
  have hU' : iSup U' = ⊤ := by
    apply top_le_iff.1
    rw [← hcov]
    exact iSup_le fun i => (hU'e i).symm.le.trans (le_iSup U' (e i))
  have hframe : ∀ (α : Fin (N + 1)) (W : Y.Opens), W ≤ U' α →
      Function.Bijective fun g : Γ(Y, W) =>
        g • ((Scheme.Modules.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (σ α) : Γ(Scheme.Modules.glueOfCocycle c, W)) := by
    intro α W hW
    by_cases h : ∃ i, e i = α
    · obtain ⟨i, rfl⟩ := h
      rw [hU'e] at hW
      exact bijective_smul_of_map_eq_glueFrame c (σ (e i)) i (hσe i) W hW
    · have hbot : U' α = ⊥ := dif_neg h
      rw [hbot] at hW
      exact bijective_smul_bot _ _ W hW
  obtain ⟨𝔓, h𝔓σ, h𝔓U⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top πY (Scheme.Modules.glueOfCocycle c) N σ U' hU' hframe
  have hV : ∀ i : Fin r, V i ≤ 𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)) :=
    fun i => (hU'e i).symm.le.trans (h𝔓U (e i))
  refine ⟨𝔓, ?_, hV, ?_, ?_⟩
  ·
    intro α j
    rw [h𝔓σ]
    exact glueComponent_sec c (a α) (hx α) j
  ·
    intro i
    refine le_antisymm ?_ (hV i)
    intro y hy
    have hy' : y ∈ (⊤ : Y.Opens) := trivial
    rw [← hcov] at hy'
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hy'
    have hle := inf_le_basicOpen_of_frame c (a (e i)) (hx (e i))
      (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)))
      (fun W' hW' => by have hf := 𝔓.frame (e i) W' hW'; rw [h𝔓σ] at hf; exact hf) j
    have hyj : y ∈ Y.basicOpen (a (e i) j) := hle ⟨hy, hj⟩
    rw [hae, Y.basicOpen_pow _ hk, hw3] at hyj
    exact hyj.2
  ·
    intro i α
    have hr := 𝔓.app_ratio_smul (e i) α
    rw [h𝔓σ] at hr
    have h1 := eq_of_smul_sec_eq c (hx (e i)) (hx α) i (by rw [hae, hw1, one_pow]) (hV i) _ hr
    exact h1

end S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf (solution)
