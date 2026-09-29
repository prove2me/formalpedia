-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/596b9b58-82c4-5d1e-b82c-f7d901c3a915

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_isUnit

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace TwoChartGlue

variable {X : Scheme.{u}} (U V : X.Opens) (t : Γ(X, U ⊓ V))

set_option maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

noncomputable abbrev rO {A B : X.Opens} (h : B ≤ A) : Γ(X, A) →+* Γ(X, B) :=
  (X.presheaf.map (homOfLE h).op).hom

theorem rO_rO {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (g : Γ(X, A)) :
    rO hCB (rO hBA g) = rO (hCB.trans hBA) g := by
  change (X.presheaf.map (homOfLE hBA).op ≫ X.presheaf.map (homOfLE hCB).op).hom g = _
  rw [← Functor.map_comp]; rfl

theorem rO_irrel {A B : X.Opens} (h h' : B ≤ A) (g : Γ(X, A)) : rO h g = rO h' g := rfl

theorem rO_refl {A : X.Opens} (g : Γ(X, A)) : rO (le_refl A) g = g := by
  change (X.presheaf.map (homOfLE (le_refl A)).op).hom g = g
  rw [Subsingleton.elim (homOfLE (le_refl A)) (𝟙 A), op_id, X.presheaf.map_id]; rfl

section Pairs

variable (T : X.Opens)

theorem leTU : T ⊓ (U ⊓ V) ≤ T ⊓ U := inf_le_inf_left T inf_le_left
theorem leTV : T ⊓ (U ⊓ V) ≤ T ⊓ V := inf_le_inf_left T inf_le_right
theorem leW : T ⊓ (U ⊓ V) ≤ U ⊓ V := inf_le_right

def pairs : AddSubgroup (Γ(X, T ⊓ U) × Γ(X, T ⊓ V)) where
  carrier := {p | rO (leTU U V T) p.1 = rO (leW U V T) t * rO (leTV U V T) p.2}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, map_add] at hp hq ⊢
    rw [hp, hq, mul_add]
  neg_mem' := by
    intro p hp
    simp only [Set.mem_setOf_eq, Prod.fst_neg, Prod.snd_neg, map_neg] at hp ⊢
    rw [hp, mul_neg]

variable {U V t T}

theorem mem_pairs {p : Γ(X, T ⊓ U) × Γ(X, T ⊓ V)} :
    p ∈ pairs U V t T ↔ rO (leTU U V T) p.1 = rO (leW U V T) t * rO (leTV U V T) p.2 := Iff.rfl

variable (U V t T)

noncomputable scoped instance : SMul Γ(X, T) (pairs U V t T) where
  smul g p := ⟨(rO inf_le_left g * p.1.1, rO inf_le_left g * p.1.2), by
    have hp := p.2
    rw [mem_pairs] at hp ⊢
    simp only [map_mul, rO_rO]
    rw [hp]
    have : rO ((leTU U V T).trans inf_le_left) g = rO ((leTV U V T).trans inf_le_left) g := rfl
    rw [this]; ring⟩

theorem smul_val (g : Γ(X, T)) (p : pairs U V t T) :
    (g • p).1 = (rO inf_le_left g * p.1.1, rO inf_le_left g * p.1.2) := rfl

noncomputable scoped instance : Module Γ(X, T) (pairs U V t T) where
  one_smul p := by apply Subtype.ext; rw [smul_val]; simp
  mul_smul a b p := by apply Subtype.ext; simp only [smul_val, map_mul]; ext <;> simp [mul_assoc]
  smul_zero a := by apply Subtype.ext; rw [smul_val]; simp
  smul_add a p q := by apply Subtype.ext; simp only [smul_val, AddSubgroup.coe_add, Prod.fst_add, Prod.snd_add, mul_add, Prod.mk_add_mk]
  add_smul a b p := by apply Subtype.ext; simp only [smul_val, map_add, add_mul, AddSubgroup.coe_add, Prod.mk_add_mk]
  zero_smul p := by apply Subtype.ext; rw [smul_val]; simp

end Pairs

noncomputable def resPairs {T T' : X.Opens} (h : T' ≤ T) : pairs U V t T →+ pairs U V t T' where
  toFun p := ⟨(rO (inf_le_inf_right U h) p.1.1, rO (inf_le_inf_right V h) p.1.2), by
    have hp := p.2
    rw [mem_pairs] at hp ⊢
    rw [rO_rO, rO_rO]
    have e1 : rO ((leTU U V T').trans (inf_le_inf_right U h)) p.1.1 =
        rO (inf_le_inf_right (U ⊓ V) h) (rO (leTU U V T) p.1.1) := by rw [rO_rO]
    have e2 : rO ((leTV U V T').trans (inf_le_inf_right V h)) p.1.2 =
        rO (inf_le_inf_right (U ⊓ V) h) (rO (leTV U V T) p.1.2) := by rw [rO_rO]
    rw [e1, e2, hp, map_mul, rO_rO]⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' p q := by apply Subtype.ext; simp

theorem resPairs_val {T T' : X.Opens} (h : T' ≤ T) (p : pairs U V t T) :
    (resPairs U V t h p).1 = (rO (inf_le_inf_right U h) p.1.1, rO (inf_le_inf_right V h) p.1.2) := rfl

noncomputable def prePt : (Opens X)ᵒᵖ ⥤ Ab where
  obj T := AddCommGrpCat.of (pairs U V t T.unop)
  map {T T'} f := AddCommGrpCat.ofHom (resPairs U V t f.unop.le)
  map_id T := by
    ext p
    · exact rO_refl _
    · exact rO_refl _
  map_comp {T₁ T₂ T₃} f g := by
    ext p
    · exact (rO_rO _ _ _).symm
    · exact (rO_rO _ _ _).symm

noncomputable scoped instance instModulePrePt (T : (Opens X)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj T) ((prePt U V t).obj T) :=
  inferInstanceAs (Module Γ(X, T.unop) (pairs U V t T.unop))

theorem prePt_map_smul ⦃T T' : (Opens X)ᵒᵖ⦄ (f : T ⟶ T') (r : X.ringCatSheaf.obj.obj T) (m : (prePt U V t).obj T) :
    (prePt U V t).map f (r • m) = X.ringCatSheaf.obj.map f r • (prePt U V t).map f m := by
  apply Subtype.ext
  change (rO _ (rO _ r * m.1.1), rO _ (rO _ r * m.1.2)) =
    (rO _ (rO _ r) * rO _ m.1.1, rO _ (rO _ r) * rO _ m.1.2)
  simp only [map_mul, rO_rO]

noncomputable def P : PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (prePt U V t) (prePt_map_smul U V t)

set_option maxHeartbeats 1600000 in
theorem prePt_isSheaf : TopCat.Presheaf.IsSheaf (prePt U V t) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι W sf hsf

  let T : X.Opens := iSup W
  have hWT : ∀ i, W i ≤ T := fun i => le_iSup W i

  let xs : ∀ i, Γ(X, W i ⊓ U) := fun i => (sf i).1.1
  let ys : ∀ i, Γ(X, W i ⊓ V) := fun i => (sf i).1.2

  have hx : TopCat.Presheaf.IsCompatible X.sheaf.obj (fun i => W i ⊓ U) xs := by
    intro i j
    have h := congrArg (fun p : pairs U V t (W i ⊓ W j) => p.1.1) (hsf i j)

    change rO (inf_le_left : (W i ⊓ U) ⊓ (W j ⊓ U) ≤ W i ⊓ U) (xs i) =
      rO (inf_le_right : (W i ⊓ U) ⊓ (W j ⊓ U) ≤ W j ⊓ U) (xs j)
    have hle : (W i ⊓ U) ⊓ (W j ⊓ U) ≤ (W i ⊓ W j) ⊓ U :=
      le_inf (inf_le_inf inf_le_left inf_le_left) (inf_le_left.trans inf_le_right)
    have e1 : rO (inf_le_left : (W i ⊓ U) ⊓ (W j ⊓ U) ≤ W i ⊓ U) (xs i) =
        rO hle (rO (inf_le_inf_right U inf_le_left) (xs i)) := by rw [rO_rO]
    have e2 : rO (inf_le_right : (W i ⊓ U) ⊓ (W j ⊓ U) ≤ W j ⊓ U) (xs j) =
        rO hle (rO (inf_le_inf_right U inf_le_right) (xs j)) := by rw [rO_rO]
    rw [e1, e2]
    exact congrArg _ h
  have hy : TopCat.Presheaf.IsCompatible X.sheaf.obj (fun i => W i ⊓ V) ys := by
    intro i j
    have h := congrArg (fun p : pairs U V t (W i ⊓ W j) => p.1.2) (hsf i j)
    change rO (inf_le_left : (W i ⊓ V) ⊓ (W j ⊓ V) ≤ W i ⊓ V) (ys i) =
      rO (inf_le_right : (W i ⊓ V) ⊓ (W j ⊓ V) ≤ W j ⊓ V) (ys j)
    have hle : (W i ⊓ V) ⊓ (W j ⊓ V) ≤ (W i ⊓ W j) ⊓ V :=
      le_inf (inf_le_inf inf_le_left inf_le_left) (inf_le_left.trans inf_le_right)
    have e1 : rO (inf_le_left : (W i ⊓ V) ⊓ (W j ⊓ V) ≤ W i ⊓ V) (ys i) =
        rO hle (rO (inf_le_inf_right V inf_le_left) (ys i)) := by rw [rO_rO]
    have e2 : rO (inf_le_right : (W i ⊓ V) ⊓ (W j ⊓ V) ≤ W j ⊓ V) (ys j) =
        rO hle (rO (inf_le_inf_right V inf_le_right) (ys j)) := by rw [rO_rO]
    rw [e1, e2]
    exact congrArg _ h

  have hcovU : T ⊓ U ≤ ⨆ i, W i ⊓ U := by rw [← iSup_inf_eq]
  have hcovV : T ⊓ V ≤ ⨆ i, W i ⊓ V := by rw [← iSup_inf_eq]
  have hcovW : T ⊓ (U ⊓ V) ≤ ⨆ i, W i ⊓ (U ⊓ V) := by rw [← iSup_inf_eq]

  obtain ⟨x, hxg, hxu⟩ := X.sheaf.existsUnique_gluing' (fun i => W i ⊓ U) (T ⊓ U)
    (fun i => homOfLE (inf_le_inf_right U (hWT i))) hcovU xs hx
  obtain ⟨y, hyg, hyu⟩ := X.sheaf.existsUnique_gluing' (fun i => W i ⊓ V) (T ⊓ V)
    (fun i => homOfLE (inf_le_inf_right V (hWT i))) hcovV ys hy

  have hxy : ((show Γ(X, T ⊓ U) from x), (show Γ(X, T ⊓ V) from y)) ∈ pairs U V t T := by
    rw [mem_pairs]
    apply X.sheaf.eq_of_locally_eq' (fun i => W i ⊓ (U ⊓ V)) (T ⊓ (U ⊓ V))
      (fun i => homOfLE (inf_le_inf_right (U ⊓ V) (hWT i))) hcovW
    intro i
    change rO (inf_le_inf_right (U ⊓ V) (hWT i)) (rO (leTU U V T) x) =
      rO (inf_le_inf_right (U ⊓ V) (hWT i)) (rO (leW U V T) t * rO (leTV U V T) y)
    rw [map_mul, rO_rO, rO_rO, rO_rO]
    have ex : rO ((inf_le_inf_right (U ⊓ V) (hWT i)).trans (leTU U V T)) (show Γ(X, T ⊓ U) from x) =
        rO (leTU U V (W i)) (xs i) := by
      rw [← hxg i]; exact (rO_rO _ _ _).symm
    have ey : rO ((inf_le_inf_right (U ⊓ V) (hWT i)).trans (leTV U V T)) (show Γ(X, T ⊓ V) from y) =
        rO (leTV U V (W i)) (ys i) := by
      rw [← hyg i]; exact (rO_rO _ _ _).symm
    rw [ex, ey]
    exact (sf i).2
  refine ⟨⟨(x, y), hxy⟩, fun i => ?_, fun s hs => ?_⟩
  ·
    apply Subtype.ext
    change (rO _ x, rO _ y) = (sf i).1
    ext
    · exact hxg i
    · exact hyg i
  ·
    apply Subtype.ext
    have h1 : s.1.1 = x := hxu s.1.1 fun i => congrArg (fun p : pairs U V t (W i) => p.1.1) (hs i)
    have h2 : s.1.2 = y := hyu s.1.2 fun i => congrArg (fun p : pairs U V t (W i) => p.1.2) (hs i)
    exact Prod.ext h1 h2

noncomputable def L : X.Modules :=
  ⟨P U V t, prePt_isSheaf U V t⟩

theorem sections_eq (T : X.Opens) : (Γ(L U V t, T) : Type u) = pairs U V t T := rfl

section Frames

theorem rO_rO_self {A B : X.Opens} (h : B ≤ A) (h' : A ≤ B) (g : Γ(X, B)) : rO h (rO h' g) = g := by
  rw [rO_rO]; exact rO_refl g

theorem rO_bijective_of_le_le {A B : X.Opens} (h : B ≤ A) (h' : A ≤ B) : Function.Bijective (rO h) :=
  Function.bijective_iff_has_inverse.2 ⟨rO h', fun g => rO_rO_self h' h g, fun g => rO_rO_self h h' g⟩

noncomputable def tinv (ht : IsUnit t) : Γ(X, U ⊓ V) := ht.unit⁻¹.1

theorem tinv_mul (ht : IsUnit t) : tinv U V t ht * t = 1 := ht.unit.inv_val
theorem mul_tinv (ht : IsUnit t) : t * tinv U V t ht = 1 := ht.unit.val_inv

noncomputable def sU (ht : IsUnit t) : Γ(L U V t, U) :=
  ⟨((1 : Γ(X, U ⊓ U)), tinv U V t ht), by
    rw [mem_pairs]
    simp only [map_one]
    have : rO (leW U V U) t = rO (leTV U V U) t := rfl
    rw [this, ← map_mul, mul_tinv, map_one]⟩

noncomputable def sV (ht : IsUnit t) : Γ(L U V t, V) :=
  ⟨(rO (le_of_eq (inf_comm V U) : V ⊓ U ≤ U ⊓ V) t, (1 : Γ(X, V ⊓ V))), by
    rw [mem_pairs]
    simp only [map_one, mul_one]
    rw [rO_rO]⟩

theorem sU_val (ht : IsUnit t) : (sU U V t ht).1 = (1, tinv U V t ht) := rfl
theorem sV_val (ht : IsUnit t) : (sV U V t ht).1 = (rO (le_of_eq (inf_comm V U) : V ⊓ U ≤ U ⊓ V) t, 1) := rfl

theorem L_map {T T' : X.Opens} (h : T' ≤ T) (p : Γ(L U V t, T)) :
    ((L U V t).presheaf.map (homOfLE h).op p : Γ(L U V t, T')) = resPairs U V t h p := rfl

theorem L_smul {T : X.Opens} (g : Γ(X, T)) (p : Γ(L U V t, T)) :
    ((g • p : Γ(L U V t, T)) : pairs U V t T) = g • (show pairs U V t T from p) := rfl

theorem sV_res_eq_smul_sU_res (ht : IsUnit t) :
    ((L U V t).presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (sV U V t ht) : Γ(L U V t, U ⊓ V)) =
      t • (L U V t).presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (sU U V t ht) := by
  rw [L_map, L_map]
  apply Subtype.ext
  rw [L_smul, smul_val, resPairs_val, resPairs_val, sU_val, sV_val]
  simp only [map_one, mul_one, rO_rO]
  ext
  · rfl
  · change (1 : Γ(X, (U ⊓ V) ⊓ V)) = rO inf_le_left t * rO _ (tinv U V t ht)
    have : rO (inf_le_left : (U ⊓ V) ⊓ V ≤ U ⊓ V) t = rO (inf_le_inf_right V (inf_le_left : U ⊓ V ≤ U)) t := rfl
    rw [this, ← map_mul, mul_tinv, map_one]

theorem isFrameOn_sU (ht : IsUnit t) : Scheme.Modules.IsFrameOn (sU U V t ht) U := by
  intro W hWU _

  have key : ∀ g : Γ(X, W), ((g • ((L U V t).presheaf.map (homOfLE hWU).op (sU U V t ht) : Γ(L U V t, W))
      : Γ(L U V t, W)) : pairs U V t W).1 =
      (rO (inf_le_left : W ⊓ U ≤ W) g, rO (inf_le_left : W ⊓ V ≤ W) g *
        rO (inf_le_inf_right V hWU) (tinv U V t ht)) := by
    intro g
    rw [L_smul, smul_val, L_map, resPairs_val, sU_val]
    simp only [map_one, mul_one, rO_rO]
  constructor
  · intro g g' hgg'
    have h := congrArg (fun p : Γ(L U V t, W) => (p : pairs U V t W).1.1) hgg'
    simp only [key] at h
    exact (rO_bijective_of_le_le (inf_le_left : W ⊓ U ≤ W) (le_inf le_rfl hWU)).1 h
  · intro p
    refine ⟨rO (le_inf le_rfl hWU : W ≤ W ⊓ U) (p : pairs U V t W).1.1, ?_⟩
    apply Subtype.ext
    rw [key, rO_rO_self]
    ext
    · rfl
    ·
      have hp := (p : pairs U V t W).2
      rw [mem_pairs] at hp

      apply (rO_bijective_of_le_le (leTV U V W) (le_inf inf_le_left (le_inf (inf_le_left.trans hWU) inf_le_right))).1
      change rO (leTV U V W) (rO inf_le_left (rO _ (p : pairs U V t W).1.1) * rO _ (tinv U V t ht)) =
        rO (leTV U V W) (p : pairs U V t W).1.2
      rw [map_mul, rO_rO, rO_rO, rO_rO]

      have hp' : rO (leTV U V W) (p : pairs U V t W).1.2 =
          rO (leW U V W) (tinv U V t ht) * rO (leTU U V W) (p : pairs U V t W).1.1 := by
        rw [hp, ← mul_assoc, ← map_mul, tinv_mul, map_one, one_mul]
      rw [hp', mul_comm]

theorem isFrameOn_sV (ht : IsUnit t) : Scheme.Modules.IsFrameOn (sV U V t ht) V := by
  intro W hWV _
  have key : ∀ g : Γ(X, W), ((g • ((L U V t).presheaf.map (homOfLE hWV).op (sV U V t ht) : Γ(L U V t, W))
      : Γ(L U V t, W)) : pairs U V t W).1 =
      (rO (inf_le_left : W ⊓ U ≤ W) g *
        rO ((inf_le_inf_right U hWV).trans (le_of_eq (inf_comm V U))) t, rO (inf_le_left : W ⊓ V ≤ W) g) := by
    intro g
    rw [L_smul, smul_val, L_map, resPairs_val, sV_val]
    simp only [map_one, mul_one, rO_rO]
  constructor
  · intro g g' hgg'
    have h := congrArg (fun p : Γ(L U V t, W) => (p : pairs U V t W).1.2) hgg'
    simp only [key] at h
    exact (rO_bijective_of_le_le (inf_le_left : W ⊓ V ≤ W) (le_inf le_rfl hWV)).1 h
  · intro p
    refine ⟨rO (le_inf le_rfl hWV : W ≤ W ⊓ V) (p : pairs U V t W).1.2, ?_⟩
    apply Subtype.ext
    rw [key, rO_rO_self]
    ext
    · have hp := (p : pairs U V t W).2
      rw [mem_pairs] at hp
      apply (rO_bijective_of_le_le (leTU U V W) (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hWV)))).1
      change rO (leTU U V W) (rO inf_le_left (rO _ (p : pairs U V t W).1.2) * rO _ t) =
        rO (leTU U V W) (p : pairs U V t W).1.1
      rw [map_mul, rO_rO, rO_rO, rO_rO, hp, mul_comm]
    · rfl

end Frames

theorem exists_isFrameOn'_of_isUnit (ht : IsUnit t) :
    ∃ (M : X.Modules) (a : Γ(M, U)) (b : Γ(M, V)), Scheme.Modules.IsFrameOn a U ∧ Scheme.Modules.IsFrameOn b V ∧
      (M.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b : Γ(M, U ⊓ V)) =
        t • M.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a :=
  ⟨L U V t, sU U V t ht, sV U V t ht, isFrameOn_sU U V t ht, isFrameOn_sV U V t ht, sV_res_eq_smul_sU_res U V t ht⟩

end TwoChartGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_isUnit.TwoChartGlue"

open AlgebraicGeometry in
set_option maxHeartbeats 1600000 in
theorem solution
    {X : Scheme.{u}} (U V : X.Opens) (t : Γ(X, U ⊓ V)) (ht : IsUnit t) :
    ∃ (M : X.Modules) (a : Γ(M, U)) (b : Γ(M, V)),
      Scheme.Modules.IsFrameOn a U ∧ Scheme.Modules.IsFrameOn b V ∧
      M.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b =
        t • M.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a :=
  TwoChartGlue.exists_isFrameOn'_of_isUnit U V t ht

end S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_isUnit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_isUnit (solution)
