-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_H1_sectionsOf_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T18:42:17.996376+00:00
-- url     : https://prove2.me/submissions/7fdba1a5-c257-470b-b4d2-98ef166cc8e0

import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Order
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_sections_sub_of_isAffineOpen_sup_of_isInvertible

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover.CoverComparison
open CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (c : X ⟶ Spec (.of R)) (M : X.Modules)

/-- Sections with the base map retained in the type for scalar inference. -/
abbrev Sec (c : X ⟶ Spec (.of R)) (M : X.Modules) (U : X.Opens) : Type u := Γ(M, U)

instance sectionsModule (U : X.Opens) : Module R (Sec c M U) :=
  moduleSectionsOfHom c M U

abbrev res {U V : X.Opens} (h : V ≤ U) : Sec c M U →ₗ[R] Sec c M V :=
  restrictSections c M h

@[simp] theorem res_res {U V W : X.Opens} (hUV : V ≤ U) (hVW : W ≤ V)
    (s : Sec c M U) : res c M hVW (res c M hUV s) = res c M (hVW.trans hUV) s := by
  change M.presheaf.map _ (M.presheaf.map _ s) = M.presheaf.map _ s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

@[simp] theorem res_self {U : X.Opens} (h : U ≤ U) (s : Sec c M U) :
    res c M h s = s := by
  change M.presheaf.map (𝟙 (op U)) s = s
  simp

theorem res_of_res_eq {U V W : X.Opens} (hUV : V ≤ U) (hVW : W ≤ V)
    (hUW : W ≤ U) {s : Sec c M U} {t : Sec c M V} (h : res c M hUV s = t) :
    res c M hUW s = res c M hVW t :=
  (res_res c M hUV hVW s).symm.trans (congrArg (res c M hVW) h)

/-- Equality of sections can be checked on two opens covering their domain. -/
theorem ext_two {U V W : X.Opens} (hU : U ≤ W) (hV : V ≤ W)
    (hcover : U ⊔ V = W) {s t : Sec c M W}
    (h0 : res c M hU s = res c M hU t)
    (h1 : res c M hV s = res c M hV t) : s = t := by
  apply M.isSheaf.section_ext
  intro x hx
  have h : x ∈ U ⊔ V := by rw [hcover]; exact hx
  rcases h with hxU | hxV
  · exact ⟨U, hU, hxU, h0⟩
  · exact ⟨V, hV, hxV, h1⟩

/-- Two compatible sections glue on any open that they cover. -/
theorem glue_two {U V W : X.Opens} (hU : U ≤ W) (hV : V ≤ W)
    (hcover : U ⊔ V = W) (s : Sec c M U) (t : Sec c M V)
    (hc : res c M inf_le_left s = res c M inf_le_right t) :
    ∃ z : Sec c M W, res c M hU z = s ∧ res c M hV z = t := by
  let A : Bool → X.Opens := fun b => if b then V else U
  let sf : ∀ b, Γ(M, A b) := fun b => by cases b; exact s; exact t
  have compatible : TopCat.Presheaf.IsCompatible M.presheaf A sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact hc
    · apply (ConcreteCategory.bijective_of_isIso
        (M.presheaf.map (eqToHom (inf_comm U V)).op)).injective
      change res c M (inf_comm U V).le
          (res c M (inf_le_left : V ⊓ U ≤ V) t) =
        res c M (inf_comm U V).le (res c M (inf_le_right : V ⊓ U ≤ U) s)
      simpa only [res_res] using hc.symm
    · rfl
  have cover : W ≤ iSup A := by
    rw [iSup_bool_eq]
    change W ≤ V ⊔ U
    rw [sup_comm, hcover]
  let incl : ∀ b, A b ⟶ W := fun b => by cases b; exact homOfLE hU; exact homOfLE hV
  obtain ⟨z, hz, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    A W incl cover sf compatible
  exact ⟨z, hz false, hz true⟩

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.CoverComparison

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover.CoverComparison
open CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (c : X ⟶ Spec (.of R)) (M : X.Modules)

abbrev chart (𝒰 : X.TwoAffineOpenCover) (i : Bool) : X.Opens :=
  if i then 𝒰.U1 else 𝒰.U0

theorem chart_affine (𝒰 : X.TwoAffineOpenCover) (i : Bool) : IsAffineOpen (chart 𝒰 i) := by
  cases i
  · exact 𝒰.isAffineOpen_U0
  · exact 𝒰.isAffineOpen_U1

/-- Sections on the four intersections of the two covers. -/
abbrev Matrix (𝒰 𝒱 : X.TwoAffineOpenCover) :=
  ∀ i j : Bool, Sec c M (chart 𝒰 i ⊓ chart 𝒱 j)

def horizontal (𝒰 𝒱 : X.TwoAffineOpenCover) (j : Bool) :
    Matrix c M 𝒰 𝒱 →ₗ[R] Sec c M ((𝒰.U0 ⊓ 𝒰.U1) ⊓ chart 𝒱 j) where
  toFun a := res c M (by dsimp [chart]; order) (a true j) -
    res c M (by dsimp [chart]; order) (a false j)
  map_add' a b := by simp only [Pi.add_apply, map_add]; abel
  map_smul' r a := by simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply]

def vertical (𝒰 𝒱 : X.TwoAffineOpenCover) (i : Bool) :
    Matrix c M 𝒰 𝒱 →ₗ[R] Sec c M (chart 𝒰 i ⊓ (𝒱.U0 ⊓ 𝒱.U1)) where
  toFun a := res c M (by dsimp [chart]; order) (a i true) -
    res c M (by dsimp [chart]; order) (a i false)
  map_add' a b := by simp only [Pi.add_apply, map_add]; abel
  map_smul' r a := by simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply]

/-- A rectangle of local sections compares two degree-one cocycles. -/
def Compatible (𝒰 𝒱 : X.TwoAffineOpenCover)
    (s : Sec c M (𝒰.U0 ⊓ 𝒰.U1)) (t : Sec c M (𝒱.U0 ⊓ 𝒱.U1)) : Prop :=
  ∃ a : Matrix c M 𝒰 𝒱,
    (∀ j, horizontal c M 𝒰 𝒱 j a = res c M inf_le_left s) ∧
    (∀ i, vertical c M 𝒰 𝒱 i a = res c M inf_le_right t)

def transpose {𝒰 𝒱 : X.TwoAffineOpenCover} (a : Matrix c M 𝒰 𝒱) :
    Matrix c M 𝒱 𝒰 := fun i j => res c M (by order) (a j i)

theorem compatible_symm {𝒰 𝒱 : X.TwoAffineOpenCover}
    {s : Sec c M (𝒰.U0 ⊓ 𝒰.U1)} {t : Sec c M (𝒱.U0 ⊓ 𝒱.U1)}
    (h : Compatible c M 𝒰 𝒱 s t) : Compatible c M 𝒱 𝒰 t s := by
  rcases h with ⟨a, ha, hb⟩
  refine ⟨transpose c M a, ?_, ?_⟩
  · intro j
    have h := congrArg (res c M (show (𝒱.U0 ⊓ 𝒱.U1) ⊓ chart 𝒰 j ≤
      chart 𝒰 j ⊓ (𝒱.U0 ⊓ 𝒱.U1) by order)) (hb j)
    simpa only [horizontal, vertical, transpose, LinearMap.coe_mk,
      AddHom.coe_mk, map_sub, res_res] using h
  · intro i
    have h := congrArg (res c M (show chart 𝒱 i ⊓ (𝒰.U0 ⊓ 𝒰.U1) ≤
      (𝒰.U0 ⊓ 𝒰.U1) ⊓ chart 𝒱 i by order)) (ha i)
    simpa only [horizontal, vertical, transpose, LinearMap.coe_mk,
      AddHom.coe_mk, map_sub, res_res] using h

def classOf (𝒰 : X.TwoAffineOpenCover) :
    Sec c M (𝒰.U0 ⊓ 𝒰.U1) →ₗ[R] (𝒰.sectionsOf c M).H1 :=
  (LinearMap.range (𝒰.sectionsOf c M).cechDiff).mkQ

theorem classOf_surjective (𝒰 : X.TwoAffineOpenCover) :
    Function.Surjective (classOf c M 𝒰) := Submodule.mkQ_surjective _

theorem classOf_eq_zero_iff (𝒰 : X.TwoAffineOpenCover) (s : Sec c M (𝒰.U0 ⊓ 𝒰.U1)) :
    classOf c M 𝒰 s = 0 ↔ ∃ a : Sec c M 𝒰.U0, ∃ b : Sec c M 𝒰.U1,
      res c M inf_le_right b - res c M inf_le_left a = s := by
  change Submodule.Quotient.mk s = (0 : (𝒰.sectionsOf c M).H1) ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨⟨a, b⟩, h⟩
    exact ⟨a, b, ((𝒰.sectionsOf c M).cechDiff_apply (a, b)).symm.trans h⟩
  · rintro ⟨a, b, h⟩
    exact ⟨(a, b), ((𝒰.sectionsOf c M).cechDiff_apply (a, b)).trans h⟩

/-- The pairs of cohomology classes joined by a rectangle form a submodule. -/
def relation (𝒰 𝒱 : X.TwoAffineOpenCover) :
    Submodule R ((𝒰.sectionsOf c M).H1 × (𝒱.sectionsOf c M).H1) where
  carrier p := ∃ s t, classOf c M 𝒰 s = p.1 ∧ classOf c M 𝒱 t = p.2 ∧
    Compatible c M 𝒰 𝒱 s t
  zero_mem' := by
    refine ⟨0, 0, map_zero _, map_zero _, 0, ?_, ?_⟩ <;> intro i <;> simp
  add_mem' := by
    rintro p q ⟨s, t, hs, ht, a, ha, hb⟩ ⟨s', t', hs', ht', a', ha', hb'⟩
    refine ⟨s + s', t + t', ?_, ?_, a + a', ?_, ?_⟩
    · simpa only [map_add, hs, hs'] using (Prod.fst_add p q).symm
    · simpa only [map_add, ht, ht'] using (Prod.snd_add p q).symm
    · intro j; rw [map_add, ha, ha', map_add]
    · intro i; rw [map_add, hb, hb', map_add]
  smul_mem' := by
    rintro r p ⟨s, t, hs, ht, a, ha, hb⟩
    refine ⟨r • s, r • t, ?_, ?_, r • a, ?_, ?_⟩
    · rw [map_smul, hs]; rfl
    · rw [map_smul, ht]; rfl
    · intro j; rw [map_smul, ha, map_smul]
    · intro i; rw [map_smul, hb, map_smul]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.CoverComparison

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover.CoverComparison
open CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (c : X ⟶ Spec (.of R)) (M : X.Modules)

/-- The geometric input: exactness at the overlap when the union is affine. -/
def AffineExact : Prop :=
  ∀ U V : X.Opens, IsAffineOpen (U ⊔ V) → ∀ s : Sec c M (U ⊓ V),
    ∃ a : Sec c M U, ∃ b : Sec c M V,
      res c M inf_le_right b - res c M inf_le_left a = s

/-- Split a cocycle on each chart of the second cover, then glue its differences. -/
theorem exists_compatible (hexact : AffineExact c M) (𝒰 𝒱 : X.TwoAffineOpenCover)
    (s : Sec c M (𝒰.U0 ⊓ 𝒰.U1)) :
    ∃ t : Sec c M (𝒱.U0 ⊓ 𝒱.U1), Compatible c M 𝒰 𝒱 s t := by
  classical
  have hs : ∀ j : Bool, ∃ a₀ : Sec c M (𝒰.U0 ⊓ chart 𝒱 j),
      ∃ a₁ : Sec c M (𝒰.U1 ⊓ chart 𝒱 j),
        res c M (by order) a₁ - res c M (by order) a₀ =
          res c M (show (𝒰.U0 ⊓ 𝒰.U1) ⊓ chart 𝒱 j ≤ 𝒰.U0 ⊓ 𝒰.U1 by order) s := by
    intro j
    have hc : (𝒰.U0 ⊓ chart 𝒱 j) ⊔ (𝒰.U1 ⊓ chart 𝒱 j) = chart 𝒱 j := by
      rw [← inf_sup_right, 𝒰.sup_eq_top, top_inf_eq]
    have hf : IsAffineOpen ((𝒰.U0 ⊓ chart 𝒱 j) ⊔ (𝒰.U1 ⊓ chart 𝒱 j)) := by
      rw [hc]; exact chart_affine 𝒱 j
    obtain ⟨a₀, a₁, h⟩ := hexact (𝒰.U0 ⊓ chart 𝒱 j) (𝒰.U1 ⊓ chart 𝒱 j) hf
      (res c M (by order) s)
    refine ⟨a₀, a₁, ?_⟩
    have hh := congrArg (res c M (show (𝒰.U0 ⊓ 𝒰.U1) ⊓ chart 𝒱 j ≤
      (𝒰.U0 ⊓ chart 𝒱 j) ⊓ (𝒰.U1 ⊓ chart 𝒱 j) by order)) h
    simpa only [map_sub, res_res] using hh
  choose a₀ a₁ ha using hs
  let a : Matrix c M 𝒰 𝒱 := fun i j => by cases i; exact a₀ j; exact a₁ j
  have hh : ∀ j, horizontal c M 𝒰 𝒱 j a = res c M inf_le_left s := ha
  let t₀ := vertical c M 𝒰 𝒱 false a
  let t₁ := vertical c M 𝒰 𝒱 true a
  have hc : res c M inf_le_left t₀ = res c M inf_le_right t₁ := by
    let W := (𝒰.U0 ⊓ (𝒱.U0 ⊓ 𝒱.U1)) ⊓ (𝒰.U1 ⊓ (𝒱.U0 ⊓ 𝒱.U1))
    have h₀ := congrArg (res c M (show W ≤ (𝒰.U0 ⊓ 𝒰.U1) ⊓ chart 𝒱 false by
      dsimp [W, chart]; order)) (hh false)
    have h₁ := congrArg (res c M (show W ≤ (𝒰.U0 ⊓ 𝒰.U1) ⊓ chart 𝒱 true by
      dsimp [W, chart]; order)) (hh true)
    simp only [horizontal, LinearMap.coe_mk, AddHom.coe_mk, map_sub, res_res] at h₀ h₁
    dsimp only [t₀, t₁, vertical, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [map_sub, res_res]
    have h := h₀.trans h₁.symm
    have cross {A : Type u} [AddCommGroup A] (x y z w : A)
        (h : z - x = w - y) : y - x = w - z := by
      apply sub_eq_zero.mp
      calc
        (y - x) - (w - z) = (z - x) - (w - y) := by abel
        _ = 0 := sub_eq_zero.mpr h
    exact cross _ _ _ _ h
  have cover : (𝒰.U0 ⊓ (𝒱.U0 ⊓ 𝒱.U1)) ⊔ (𝒰.U1 ⊓ (𝒱.U0 ⊓ 𝒱.U1)) =
      𝒱.U0 ⊓ 𝒱.U1 := by rw [← inf_sup_right, 𝒰.sup_eq_top, top_inf_eq]
  obtain ⟨t, ht₀, ht₁⟩ := glue_two c M inf_le_right inf_le_right cover t₀ t₁ hc
  refine ⟨t, a, hh, ?_⟩
  intro i
  cases i
  · exact ht₀.symm
  · exact ht₁.symm

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.CoverComparison

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover.CoverComparison
open CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (c : X ⟶ Spec (.of R)) (M : X.Modules)

/-- A rectangle with zero horizontal differences glues columnwise. -/
theorem compatible_zero_left (𝒰 𝒱 : X.TwoAffineOpenCover)
    (t : Sec c M (𝒱.U0 ⊓ 𝒱.U1)) (h : Compatible c M 𝒰 𝒱 0 t) :
    classOf c M 𝒱 t = 0 := by
  classical
  rcases h with ⟨a, ha, hb⟩
  have hs : ∀ j : Bool, ∃ b : Sec c M (chart 𝒱 j),
      res c M inf_le_right b = a false j ∧ res c M inf_le_right b = a true j := by
    intro j
    have cover : (𝒰.U0 ⊓ chart 𝒱 j) ⊔ (𝒰.U1 ⊓ chart 𝒱 j) = chart 𝒱 j := by
      rw [← inf_sup_right, 𝒰.sup_eq_top, top_inf_eq]
    apply glue_two c M inf_le_right inf_le_right cover (a false j) (a true j)
    have h := congrArg (res c M (show (𝒰.U0 ⊓ chart 𝒱 j) ⊓ (𝒰.U1 ⊓ chart 𝒱 j) ≤
      (𝒰.U0 ⊓ 𝒰.U1) ⊓ chart 𝒱 j by order)) (ha j)
    simp only [horizontal, LinearMap.coe_mk, AddHom.coe_mk, map_sub, res_res, map_zero] at h
    exact (sub_eq_zero.mp h).symm
  choose b hb₀ hb₁ using hs
  apply (classOf_eq_zero_iff c M 𝒱 t).mpr
  refine ⟨b false, b true, ?_⟩
  apply ext_two c M (U := 𝒰.U0 ⊓ (𝒱.U0 ⊓ 𝒱.U1))
    (V := 𝒰.U1 ⊓ (𝒱.U0 ⊓ 𝒱.U1)) inf_le_right inf_le_right
    (by rw [← inf_sup_right, 𝒰.sup_eq_top, top_inf_eq])
  · have h₀ := res_of_res_eq c M inf_le_right
      (show 𝒰.U0 ⊓ (𝒱.U0 ⊓ 𝒱.U1) ≤ 𝒰.U0 ⊓ chart 𝒱 false by dsimp [chart]; order)
      (by dsimp [chart]; order) (hb₀ false)
    have h₁ := res_of_res_eq c M inf_le_right
      (show 𝒰.U0 ⊓ (𝒱.U0 ⊓ 𝒱.U1) ≤ 𝒰.U0 ⊓ chart 𝒱 true by dsimp [chart]; order)
      (by dsimp [chart]; order) (hb₀ true)
    have e₀ := (res_res c M (U := 𝒱.U0) (V := 𝒱.U0 ⊓ 𝒱.U1)
      (W := 𝒰.U0 ⊓ (𝒱.U0 ⊓ 𝒱.U1)) inf_le_left inf_le_right (b false)).trans h₀
    have e₁ := (res_res c M (U := 𝒱.U1) (V := 𝒱.U0 ⊓ 𝒱.U1)
      (W := 𝒰.U0 ⊓ (𝒱.U0 ⊓ 𝒱.U1)) inf_le_right inf_le_right (b true)).trans h₁
    exact (map_sub (res c M inf_le_right) _ _).trans ((congrArg₂ (· - ·) e₁ e₀).trans (hb false))
  · have h₀ := res_of_res_eq c M inf_le_right
      (show 𝒰.U1 ⊓ (𝒱.U0 ⊓ 𝒱.U1) ≤ 𝒰.U1 ⊓ chart 𝒱 false by dsimp [chart]; order)
      (by dsimp [chart]; order) (hb₁ false)
    have h₁ := res_of_res_eq c M inf_le_right
      (show 𝒰.U1 ⊓ (𝒱.U0 ⊓ 𝒱.U1) ≤ 𝒰.U1 ⊓ chart 𝒱 true by dsimp [chart]; order)
      (by dsimp [chart]; order) (hb₁ true)
    have e₀ := (res_res c M (U := 𝒱.U0) (V := 𝒱.U0 ⊓ 𝒱.U1)
      (W := 𝒰.U1 ⊓ (𝒱.U0 ⊓ 𝒱.U1)) inf_le_left inf_le_right (b false)).trans h₀
    have e₁ := (res_res c M (U := 𝒱.U1) (V := 𝒱.U0 ⊓ 𝒱.U1)
      (W := 𝒰.U1 ⊓ (𝒱.U0 ⊓ 𝒱.U1)) inf_le_right inf_le_right (b true)).trans h₁
    exact (map_sub (res c M inf_le_right) _ _).trans ((congrArg₂ (· - ·) e₁ e₀).trans (hb true))

/-- Restricting two sections supplies a rectangle for their coboundary. -/
def rowSections (𝒰 𝒱 : X.TwoAffineOpenCover)
    (p : Sec c M 𝒰.U0 × Sec c M 𝒰.U1) : Matrix c M 𝒰 𝒱 := fun i j => by
  cases i
  · exact res c M inf_le_left p.1
  · exact res c M inf_le_left p.2

theorem horizontal_rowSections (𝒰 𝒱 : X.TwoAffineOpenCover)
    (p : Sec c M 𝒰.U0 × Sec c M 𝒰.U1) (j : Bool) :
    horizontal c M 𝒰 𝒱 j (rowSections c M 𝒰 𝒱 p) =
      res c M inf_le_left (res c M inf_le_right p.2 - res c M inf_le_left p.1) := by
  simp only [horizontal, rowSections, LinearMap.coe_mk, AddHom.coe_mk, map_sub, res_res]
  rfl

theorem vertical_rowSections (𝒰 𝒱 : X.TwoAffineOpenCover)
    (p : Sec c M 𝒰.U0 × Sec c M 𝒰.U1) (i : Bool) :
    vertical c M 𝒰 𝒱 i (rowSections c M 𝒰 𝒱 p) = 0 := by
  cases i <;> simp only [vertical, rowSections, LinearMap.coe_mk, AddHom.coe_mk,
    res_res, sub_self]

/-- Comparison preserves zero cohomology classes, using only sheaf gluing. -/
theorem compatible_class_zero_left (𝒰 𝒱 : X.TwoAffineOpenCover)
    (s : Sec c M (𝒰.U0 ⊓ 𝒰.U1)) (t : Sec c M (𝒱.U0 ⊓ 𝒱.U1))
    (h : Compatible c M 𝒰 𝒱 s t) (hs : classOf c M 𝒰 s = 0) :
    classOf c M 𝒱 t = 0 := by
  rcases h with ⟨a, ha, hb⟩
  obtain ⟨p₀, p₁, hp⟩ := (classOf_eq_zero_iff c M 𝒰 s).mp hs
  apply compatible_zero_left c M 𝒰 𝒱 t
  refine ⟨a - rowSections c M 𝒰 𝒱 (p₀, p₁), ?_, ?_⟩
  · intro j
    rw [map_sub, ha, horizontal_rowSections, hp, sub_self, map_zero]
  · intro i
    rw [map_sub, hb, vertical_rowSections, sub_zero]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.CoverComparison

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover.CoverComparison
open CategoryTheory CategoryTheory.Limits Opposite
universe u

/-- A total linear relation with trivial fibers over zero is a linear equivalence. -/
def linearEquivOfRelation {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : Submodule R (A × B))
    (hA : ∀ a, ∃ b, (a, b) ∈ P) (hB : ∀ b, ∃ a, (a, b) ∈ P)
    (hzA : ∀ p ∈ P, p.1 = 0 → p.2 = 0)
    (hzB : ∀ p ∈ P, p.2 = 0 → p.1 = 0) : A ≃ₗ[R] B := by
  let f : P →ₗ[R] A := (LinearMap.fst R A B).comp P.subtype
  let g : P →ₗ[R] B := (LinearMap.snd R A B).comp P.subtype
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have hh := hzA (x.val - y.val) (P.sub_mem x.property y.property)
        (sub_eq_zero.mpr h)
      exact Subtype.ext (Prod.ext h (sub_eq_zero.mp hh))
    · intro a
      obtain ⟨b, hb⟩ := hA a
      exact ⟨⟨(a, b), hb⟩, rfl⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y h
      have hh := hzB (x.val - y.val) (P.sub_mem x.property y.property)
        (sub_eq_zero.mpr h)
      exact Subtype.ext (Prod.ext (sub_eq_zero.mp hh) h)
    · intro b
      obtain ⟨a, ha⟩ := hB b
      exact ⟨⟨(a, b), ha⟩, rfl⟩
  exact (LinearEquiv.ofBijective f hf).symm.trans (LinearEquiv.ofBijective g hg)

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The common-intersection relation identifies the two concrete cokernels. -/
def coverEquiv (c : X ⟶ Spec (.of R)) (M : X.Modules) (hexact : AffineExact c M)
    (𝒰 𝒱 : X.TwoAffineOpenCover) :
    (𝒰.sectionsOf c M).H1 ≃ₗ[R] (𝒱.sectionsOf c M).H1 := by
  apply linearEquivOfRelation (relation c M 𝒰 𝒱)
  · intro q
    obtain ⟨s, hs⟩ := classOf_surjective c M 𝒰 q
    obtain ⟨t, ht⟩ := exists_compatible c M hexact 𝒰 𝒱 s
    exact ⟨classOf c M 𝒱 t, s, t, hs, rfl, ht⟩
  · intro q
    obtain ⟨t, ht⟩ := classOf_surjective c M 𝒱 q
    obtain ⟨s, hs⟩ := exists_compatible c M hexact 𝒱 𝒰 t
    exact ⟨classOf c M 𝒰 s, s, t, rfl, ht, compatible_symm c M hs⟩
  · rintro p ⟨s, t, hs, ht, h⟩ hp
    exact ht.symm.trans (compatible_class_zero_left c M 𝒰 𝒱 s t h (hs.trans hp))
  · rintro p ⟨s, t, hs, ht, h⟩ hp
    exact hs.symm.trans (compatible_class_zero_left c M 𝒱 𝒰 t s
      (compatible_symm c M h) (ht.trans hp))

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.CoverComparison

open AlgebraicGeometry CategoryTheory
universe u

theorem solution
    (R : Type u) [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (𝒰 𝒱 : X.TwoAffineOpenCover)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Nonempty ((𝒰.sectionsOf c M).H1 ≃ₗ[R] (𝒱.sectionsOf c M).H1) := by
  refine ⟨Scheme.TwoAffineOpenCover.CoverComparison.coverEquiv c M ?_ 𝒰 𝒱⟩
  intro U V hUV s
  exact Scheme.Modules.exists_sections_sub_of_isAffineOpen_sup_of_isInvertible M hM U V hUV s
