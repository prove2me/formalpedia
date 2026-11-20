-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.smallEtale_additive_cohomology_equiv_orderedCech
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-20T00:48:29.414491+00:00
-- url     : https://prove2.me/submissions/2e8454de-3178-420b-b325-d36e7deb5c4f

import Definitions.Def_AlgebraicGeometry_SmallEtaleAdditive
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Theorems.Thm_AlgebraicGeometry_Scheme_subsingleton_smallEtale_additive_succ_of_isAffine
import Theorems.Thm_AlgebraicGeometry_Scheme_smallEtale_additive_succ_equiv_orderedCech_of_acyclic_intersections

noncomputable section

section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


namespace AlgebraicGeometry.SmallEtaleAdditive

universe u

private def identityObject (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

private def identityObjectIsTerminal (X : Scheme.{u}) : IsTerminal (identityObject X) :=
  IsTerminal.ofUniqueHom
    (fun U => MorphismProperty.Over.homMk U.hom (Category.comp_id _) trivial)
    (fun U f => by
      apply MorphismProperty.Over.Hom.ext
      have h := MorphismProperty.Over.w f
      change f.left ≫ 𝟙 X = U.hom at h
      change f.left = U.hom
      exact (Category.comp_id f.left).symm.trans h)

/-- In degree zero the cohomology of the additive sheaf is the space of
global functions, for the same scalar action used in the comparison theorem. -/
def degreeZeroGlobalSections {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) :
    letI := cohomologyModule π 0
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
    (sheaf X).H 0 ≃ₗ[K] Γ(X, ⊤) := by
  letI := cohomologyModule π 0
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
  let T := identityObject X
  let s : CommRingCat.of K ⟶ Γ(X, ⊤) := scalar π T
  let e : (sheaf X).H 0 ≃+ Γ(X, ⊤) :=
    Sheaf.H.equiv₀ (sheaf X) (identityObjectIsTerminal X)
  refine { e with map_smul' := ?_ }
  intro a x
  have h := Sheaf.H.equiv₀_naturality (identityObjectIsTerminal X) (mulScalar π a) x
  change s a * e x = e (Sheaf.H.map (mulScalar π a) 0 x) at h
  change e (Sheaf.H.map (mulScalar π a) 0 x) =
    (algebraMap K Γ(X, ⊤) a) * e x
  rw [← h]
  have hs : s.hom = algebraMap K Γ(X, ⊤) := by
    change ((Scheme.ΓSpecIso (.of K)).inv ≫ (𝟙 X ≫ π).appTop).hom =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ ⊤ le_top).hom
    rw [Category.id_comp]
    have htop : π.appLE ⊤ ⊤ le_top = π.appTop :=
      Scheme.Hom.appLE_eq_app π (U := ⊤)
    exact congrArg (fun k : Γ(Spec (.of K), ⊤) ⟶ Γ(X, ⊤) =>
      ((Scheme.ΓSpecIso (.of K)).inv ≫ k).hom) htop.symm
  rw [show s a = algebraMap K Γ(X, ⊤) a from RingHom.congr_fun hs a]

end AlgebraicGeometry.SmallEtaleAdditive

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.OrderedAffineCover

universe u
variable {X : Scheme.{u}} (U : X.OrderedAffineCover)

private def vertex (i : U.ι) : U.Idx 0 :=
  ⟨fun _ => i, fun a b h => False.elim ((lt_irrefl (0 : Fin 1)) (by
    simpa only [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b] using h))⟩

private theorem inter_zero (s : U.Idx 0) : U.inter s = U.U (s.val 0) :=
  le_antisymm (iInf_le _ 0) (le_iInf fun j => by rw [Fin.fin_one_eq_zero j])

private theorem iSup_inter_zero : (⨆ s : U.Idx 0, U.inter s) = ⊤ := by
  rw [eq_top_iff, ← U.iSup_eq_top]
  refine iSup_le (fun i => le_trans ?_ (le_iSup (fun s : U.Idx 0 => U.inter s) (vertex U i)))
  rw [inter_zero]
  exact le_rfl

private def edge (i j : U.ι) (h : i < j) : U.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr (fun k => by
    have hk : k = 0 := Fin.fin_one_eq_zero k
    subst k
    exact h)⟩

private theorem face_eq_of_value_eq (s t : U.Idx 0) (h : s.val 0 = t.val 0) : s = t :=
  Subtype.ext (funext fun j => by rw [Fin.fin_one_eq_zero j, h])

private theorem inter_edge (i j : U.ι) (h : i < j) :
    U.inter (edge U i j h) = U.U i ⊓ U.U j :=
  le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1))
    (le_iInf fun k => by fin_cases k <;> first | exact inf_le_left | exact inf_le_right)

variable {R : Type u} [CommRing R] (π : X ⟶ Spec (.of R))
local notation "F" => OModulePresheaf.unit π

private theorem differential_zero (c : (F).cochain U 0) (e : U.Idx 1) :
    (F).d U 0 c e =
      (F).res (U.inter_le_inter_face e 0) (c (U.face e 0)) -
      (F).res (U.inter_le_inter_face e 1) (c (U.face e 1)) := by
  rw [OModulePresheaf.d_apply]
  change (∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) •
    (F).res (U.inter_le_inter_face e j) (c (U.face e j))) = _
  rw [Fin.sum_univ_two]
  simp [sub_eq_add_neg]

private def restrictAll : (F).obj ⊤ →ₗ[R] (F).cochain U 0 :=
  LinearMap.pi fun _ => (F).res le_top

private def toH0 : (F).obj ⊤ →ₗ[R] (F).H0 U :=
  LinearMap.codRestrict _ (restrictAll U π) (by
    intro x
    apply LinearMap.mem_ker.mpr
    funext e
    change (F).d U 0 (restrictAll U π x) e = 0
    rw [differential_zero]
    simp only [restrictAll, LinearMap.pi_apply, OModulePresheaf.res_res, sub_self])

private theorem res_congr_index {s t : U.Idx 0} (h : s = t) {W : X.Opens}
    (hs : W ≤ U.inter s) (ht : W ≤ U.inter t) (c : (F).cochain U 0) :
    (F).res hs (c s) = (F).res ht (c t) := by
  subst t
  rfl

private theorem compatible_lt (c : (F).H0 U) (s t : U.Idx 0) (h : s.val 0 < t.val 0) :
    (F).res (inf_le_left : U.inter s ⊓ U.inter t ≤ U.inter s) (c.val s) =
      (F).res (inf_le_right : U.inter s ⊓ U.inter t ≤ U.inter t) (c.val t) := by
  let e := edge U (s.val 0) (t.val 0) h
  have hs : U.face e 1 = s := face_eq_of_value_eq U _ _ rfl
  have ht : U.face e 0 = t := face_eq_of_value_eq U _ _ rfl
  have he : U.inter s ⊓ U.inter t ≤ U.inter e := by
    rw [inter_zero U s, inter_zero U t, inter_edge]
  have hd : (F).d U 0 c.val e = 0 :=
    congrFun (LinearMap.mem_ker.mp c.property) e
  rw [differential_zero] at hd
  have hr := congrArg ((F).res he) (sub_eq_zero.mp hd).symm
  rw [(F).res_res, (F).res_res] at hr
  exact (res_congr_index U π hs _ _ c.val).symm.trans
    (hr.trans (res_congr_index U π ht _ _ c.val))

private theorem compatible (c : (F).H0 U) :
    TopCat.Presheaf.IsCompatible X.sheaf.obj (fun s : U.Idx 0 => U.inter s) c.val := by
  intro s t
  change (F).res (inf_le_left : U.inter s ⊓ U.inter t ≤ U.inter s) (c.val s) =
    (F).res (inf_le_right : U.inter s ⊓ U.inter t ≤ U.inter t) (c.val t)
  rcases lt_trichotomy (s.val 0) (t.val 0) with h | h | h
  · exact compatible_lt U π c s t h
  · have e := face_eq_of_value_eq U s t h
    subst t
    rfl
  · have e := inf_comm (U.inter s) (U.inter t)
    have hr := congrArg ((F).res e.le) (compatible_lt U π c t s h).symm
    rwa [(F).res_res, (F).res_res] at hr

private theorem existsUnique_gluing (c : (F).H0 U) :
    ∃! x : (F).obj ⊤, ∀ s : U.Idx 0, (F).res (le_top : U.inter s ≤ ⊤) x = c.val s := by
  exact TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun s : U.Idx 0 => U.inter s) ⊤
    (fun _ => homOfLE le_top) (le_of_eq (iSup_inter_zero U).symm) c.val (compatible U π c)

/-- Degree-zero ordered Čech cohomology of the structure sheaf is global sections. -/
def globalFunctionsEquiv : (F).obj ⊤ ≃ₗ[R] (F).H0 U := by
  refine LinearEquiv.ofBijective (toH0 U π) ⟨?_, ?_⟩
  · intro x y h
    obtain ⟨b, _, hb⟩ := existsUnique_gluing U π (toH0 U π x)
    exact (hb x (fun _ => rfl)).trans (hb y (fun s =>
      (congrArg (fun c : (F).H0 U => c.val s) h).symm)).symm
  · intro c
    obtain ⟨x, hx, _⟩ := existsUnique_gluing U π c
    exact ⟨x, Subtype.ext (funext hx)⟩

end AlgebraicGeometry.Scheme.OrderedAffineCover

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory


namespace AlgebraicGeometry.SmallEtaleAdditive

universe u

/-- In degree zero, the comparison with the actual ordered Čech complex
is the composition of evaluation at the terminal étale object and gluing. -/
def degreeZeroOrderedCech {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (U : X.OrderedAffineCover) :
    letI := cohomologyModule π 0
    (sheaf X).H 0 ≃ₗ[K] (OModulePresheaf.unit π).H0 U := by
  letI := cohomologyModule π 0
  exact (degreeZeroGlobalSections π).trans (U.globalFunctionsEquiv π)

end AlgebraicGeometry.SmallEtaleAdditive

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem solution
    (K : Type u) [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [IsSeparated π]
    (U : X.OrderedAffineCover) :
    letI : ∀ q : ℕ, Module K ((SmallEtaleAdditive.sheaf X).H q) :=
      fun q => SmallEtaleAdditive.cohomologyModule π q
    Nonempty (((SmallEtaleAdditive.sheaf X).H 0) ≃ₗ[K] (OModulePresheaf.unit π).H0 U) ∧
      ∀ q : ℕ, Nonempty (((SmallEtaleAdditive.sheaf X).H (q + 1)) ≃ₗ[K]
        (OModulePresheaf.unit π).HSucc U q) := by
  letI : ∀ q : ℕ, Module K ((SmallEtaleAdditive.sheaf X).H q) :=
    fun q => SmallEtaleAdditive.cohomologyModule π q
  refine ⟨⟨SmallEtaleAdditive.degreeZeroOrderedCech π U⟩, ?_⟩
  apply Scheme.smallEtale_additive_succ_equiv_orderedCech_of_acyclic_intersections K π U
  haveI : X.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  intro m s q
  letI : IsAffine (U.inter s : Scheme.{u}) :=
    IsAffineOpen.iInf (fun j => U.isAffineOpen (s.val j))
  exact Scheme.subsingleton_smallEtale_additive_succ_of_isAffine _ q

end
