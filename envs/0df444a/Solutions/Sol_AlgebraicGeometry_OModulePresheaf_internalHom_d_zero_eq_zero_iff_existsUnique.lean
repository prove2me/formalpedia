-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.internalHom_d_zero_eq_zero_iff_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4e3f1ef4-9820-58b8-b760-e004dcda9fd7

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

namespace HomGlueAux

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

namespace Idx

variable (K : V.OrderedAffineCover)

def single (i : K.ι) : K.Idx 0 :=
  ⟨fun _ => i, fun a b h => by fin_cases a; fin_cases b; exact absurd h (lt_irrefl _)⟩

@[scoped simp] theorem single_val (i : K.ι) (x : Fin 1) : (single K i).1 x = i := rfl

theorem eq_single (s : K.Idx 0) : s = single K (s.1 0) := by
  refine Subtype.ext (funext fun x => ?_)
  rw [Fin.fin_one_eq_zero x]
  rfl

theorem ext0 {s s' : K.Idx 0} (h : s.1 0 = s'.1 0) : s = s' := by
  rw [eq_single K s, eq_single K s', h]

theorem U_le_inter_single (i : K.ι) : K.U i ≤ K.inter (single K i) :=
  le_iInf fun _ => le_rfl

theorem inter_single_le (i : K.ι) : K.inter (single K i) ≤ K.U i :=
  K.inter_le (single K i) 0

theorem inter_le_U0 (s : K.Idx 0) : K.inter s ≤ K.U (s.1 0) := K.inter_le s 0

def pair (a b : K.ι) (h : a < b) : K.Idx 1 :=
  ⟨![a, b], fun x y hxy => by
    fin_cases x <;> fin_cases y
    · exact absurd hxy (lt_irrefl _)
    · exact h
    · exact absurd hxy (by decide)
    · exact absurd hxy (lt_irrefl _)⟩

theorem face_pair_zero (a b : K.ι) (h : a < b) : K.face (pair K a b h) 0 = single K b := by
  refine Subtype.ext (funext fun x => ?_)
  rw [Fin.fin_one_eq_zero x]
  rfl

theorem face_pair_one (a b : K.ι) (h : a < b) : K.face (pair K a b h) 1 = single K a := by
  refine Subtype.ext (funext fun x => ?_)
  rw [Fin.fin_one_eq_zero x]
  rfl

theorem inter_pair_le_left (a b : K.ι) (h : a < b) : K.inter (pair K a b h) ≤ K.U a :=
  K.inter_le (pair K a b h) 0

theorem inter_pair_le_right (a b : K.ι) (h : a < b) : K.inter (pair K a b h) ≤ K.U b :=
  K.inter_le (pair K a b h) 1

theorem le_inter_pair {a b : K.ι} (h : a < b) {W : V.Opens} (ha : W ≤ K.U a) (hb : W ≤ K.U b) :
    W ≤ K.inter (pair K a b h) :=
  le_iInf fun j => by
    fin_cases j
    · exact ha
    · exact hb

end Idx
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx"

theorem d_zero_apply (H : OModulePresheaf π) (K : V.OrderedAffineCover) (c : H.cochain K 0) (t : K.Idx 1) :
    H.d K 0 c t = H.res (K.inter_le_inter_face t 0) (c (K.face t 0)) -
      H.res (K.inter_le_inter_face t 1) (c (K.face t 1)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, one_smul]
  rw [sub_eq_add_neg]

theorem d_zero_res_eq_zero (H : OModulePresheaf π) (K : V.OrderedAffineCover) (x : H.obj ⊤) :
    H.d K 0 (fun s => H.res (le_top : K.inter s ≤ ⊤) x) = 0 := by
  funext t
  rw [d_zero_apply]
  change H.res _ (H.res _ x) - H.res _ (H.res _ x) = 0
  rw [H.res_res, H.res_res, sub_self]

section InternalHom

variable {F G : OModulePresheaf π} (K : V.OrderedAffineCover)

theorem res_val {U U' : V.Opens} (h : U ≤ U') (φ : (internalHom F G).obj U') (W : AffBelow U) :
    ((internalHom F G).res h φ).1 W = φ.1 ⟨W.1, W.2.trans h⟩ := rfl

def comp (c : (internalHom F G).cochain K 0) (s : K.Idx 0) (D : V.affineOpens) (hD : D.1 ≤ K.inter s) :
    F.obj D.1 →ₗ[R] G.obj D.1 :=
  (c s).1 ⟨D, hD⟩

theorem comp_apply (c : (internalHom F G).cochain K 0) (s : K.Idx 0) (D : V.affineOpens) (hD : D.1 ≤ K.inter s)
    (x : F.obj D.1) : comp K c s D hD x = (c s).1 ⟨D, hD⟩ x := rfl

theorem comp_smul (c : (internalHom F G).cochain K 0) (s : K.Idx 0) (D : V.affineOpens) (hD : D.1 ≤ K.inter s)
    (a : Γ(V, D.1)) (x : F.obj D.1) : comp K c s D hD (a • x) = a • comp K c s D hD x :=
  (c s).2.1 ⟨D, hD⟩ a x

theorem comp_natural (c : (internalHom F G).cochain K 0) (s : K.Idx 0) (D D' : V.affineOpens) (hD : D.1 ≤ K.inter s)
    (hD' : D'.1 ≤ K.inter s) (h : D.1 ≤ D'.1) (x : F.obj D'.1) :
    comp K c s D hD (F.res h x) = G.res h (comp K c s D' hD' x) :=
  (c s).2.2 ⟨D, hD⟩ ⟨D', hD'⟩ h x

theorem agree_of_lt (c : (internalHom F G).cochain K 0) (hc : (internalHom F G).d K 0 c = 0) {a b : K.ι} (hab : a < b)
    (D : V.affineOpens) (ha : D.1 ≤ K.U a) (hb : D.1 ≤ K.U b) (x : F.obj D.1) :
    comp K c (Idx.single K a) D (ha.trans (Idx.U_le_inter_single K a)) x =
      comp K c (Idx.single K b) D (hb.trans (Idx.U_le_inter_single K b)) x := by
  have hDt : D.1 ≤ K.inter (Idx.pair K a b hab) := Idx.le_inter_pair K hab ha hb
  have h0 := congrFun hc (Idx.pair K a b hab)
  rw [d_zero_apply, Pi.zero_apply, sub_eq_zero] at h0

  have key : ∀ (s : K.Idx 0) (i : K.ι) (hs : s = Idx.single K i) (h : K.inter (Idx.pair K a b hab) ≤ K.inter s)
      (hi : D.1 ≤ K.U i),
      ((internalHom F G).res h (c s)).1 ⟨D, hDt⟩ x = comp K c (Idx.single K i) D (hi.trans (Idx.U_le_inter_single K i)) x := by
    rintro s i rfl h hi
    rfl
  have e0 := key (K.face (Idx.pair K a b hab) 0) b (Idx.face_pair_zero K a b hab)
    (K.inter_le_inter_face _ 0) hb
  have e1 := key (K.face (Idx.pair K a b hab) 1) a (Idx.face_pair_one K a b hab)
    (K.inter_le_inter_face _ 1) ha
  rw [← e0, ← e1, h0]

theorem agree (c : (internalHom F G).cochain K 0) (hc : (internalHom F G).d K 0 c = 0) (s s' : K.Idx 0)
    (D : V.affineOpens) (hs : D.1 ≤ K.inter s) (hs' : D.1 ≤ K.inter s') (x : F.obj D.1) :
    comp K c s D hs x = comp K c s' D hs' x := by
  have hsU : D.1 ≤ K.U (s.1 0) := hs.trans (Idx.inter_le_U0 K s)
  have hs'U : D.1 ≤ K.U (s'.1 0) := hs'.trans (Idx.inter_le_U0 K s')

  have red : ∀ (s : K.Idx 0) (hs : D.1 ≤ K.inter s) (hsU : D.1 ≤ K.U (s.1 0)),
      comp K c s D hs x = comp K c (Idx.single K (s.1 0)) D (hsU.trans (Idx.U_le_inter_single K _)) x := by
    intro s hs hsU
    have key : ∀ (s₀ : K.Idx 0) (h₀ : s₀ = s) (h : D.1 ≤ K.inter s₀), comp K c s₀ D h x = comp K c s D hs x := by
      rintro s₀ rfl h; rfl
    exact (key _ (Idx.eq_single K s).symm _).symm
  rw [red s hs hsU, red s' hs' hs'U]
  rcases lt_trichotomy (s.1 0) (s'.1 0) with hlt | heq | hgt
  · exact agree_of_lt K c hc hlt D hsU hs'U x
  · have key : ∀ (i j : K.ι) (hij : i = j) (hi : D.1 ≤ K.U i) (hj : D.1 ≤ K.U j),
        comp K c (Idx.single K i) D (hi.trans (Idx.U_le_inter_single K i)) x =
          comp K c (Idx.single K j) D (hj.trans (Idx.U_le_inter_single K j)) x := by
      rintro i j rfl hi hj; rfl
    exact key _ _ heq hsU hs'U
  · exact (agree_of_lt K c hc hgt D hs'U hsU x).symm

structure CoverData (W : V.affineOpens) where

  n : ℕ

  g : Fin n → Γ(V, W.1)

  s : Fin n → K.Idx 0
  le_inter : ∀ j, V.basicOpen (g j) ≤ K.inter (s j)
  cover : W.1 ≤ ⨆ j, V.basicOpen (g j)

theorem nonempty_coverData (W : V.affineOpens) : Nonempty (CoverData K W) := by
  classical
  have hpt : ∀ x : W.1, ∃ (i : K.ι) (r : Γ(V, W.1)), V.basicOpen r ≤ K.U i ∧ (x : V) ∈ V.basicOpen r := by
    intro x
    have hx : (x : V) ∈ (⊤ : V.Opens) := trivial
    rw [← K.iSup_eq_top, Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    obtain ⟨r, hr, hxr⟩ := W.2.exists_basicOpen_le ⟨(x : V), hi⟩ x.2
    exact ⟨i, r, hr, hxr⟩
  choose i r hrU hxr using hpt
  have hcov : (W.1 : Set V) ⊆ ⋃ x : W.1, (V.basicOpen (r x) : Set V) :=
    fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxr ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := W.2.isCompact.elim_finite_subcover (fun x : W.1 => (V.basicOpen (r x) : Set V))
    (fun x => (V.basicOpen (r x)).isOpen) hcov
  refine ⟨{ n := t.card
            g := fun j => r (t.equivFin.symm j)
            s := fun j => Idx.single K (i (t.equivFin.symm j))
            le_inter := fun j => (hrU _).trans (Idx.U_le_inter_single K _)
            cover := fun y hy => ?_ }⟩
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (ht hy)
  obtain ⟨hxt, hyx⟩ := Set.mem_iUnion.mp hx
  refine Opens.mem_iSup.mpr ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
  simpa using hyx

def coverData (W : V.affineOpens) : CoverData K W := Classical.choice (nonempty_coverData K W)

namespace CoverData

variable {K} {W : V.affineOpens} (𝒟 : CoverData K W)

abbrev D (j : Fin 𝒟.n) : V.affineOpens := ⟨V.basicOpen (𝒟.g j), W.2.basicOpen (𝒟.g j)⟩

theorem D_le (j : Fin 𝒟.n) : (𝒟.D j).1 ≤ W.1 := V.basicOpen_le _

abbrev DD (j k : Fin 𝒟.n) : V.affineOpens := ⟨V.basicOpen (𝒟.g j * 𝒟.g k), W.2.basicOpen _⟩

theorem DD_le_left (j k : Fin 𝒟.n) : (𝒟.DD j k).1 ≤ (𝒟.D j).1 :=
  (V.basicOpen_mul (𝒟.g j) (𝒟.g k)).trans_le inf_le_left

theorem DD_le_right (j k : Fin 𝒟.n) : (𝒟.DD j k).1 ≤ (𝒟.D k).1 :=
  (V.basicOpen_mul (𝒟.g j) (𝒟.g k)).trans_le inf_le_right

end CoverData
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx"

section Glue

variable {K}
variable (c : (internalHom F G).cochain K 0) (hc : (internalHom F G).d K 0 c = 0) (hGq : G.IsQuasicoherent)

def loc {W : V.affineOpens} (𝒟 : CoverData K W) (x : F.obj W.1) (j : Fin 𝒟.n) : G.obj (𝒟.D j).1 :=
  comp K c (𝒟.s j) (𝒟.D j) (𝒟.le_inter j) (F.res (𝒟.D_le j) x)

include hc in
theorem loc_compat {W : V.affineOpens} (𝒟 : CoverData K W) (x : F.obj W.1) (j k : Fin 𝒟.n) :
    G.res (𝒟.DD_le_left j k) (loc c 𝒟 x j) = G.res (𝒟.DD_le_right j k) (loc c 𝒟 x k) := by
  unfold loc
  rw [← comp_natural K c (𝒟.s j) (𝒟.DD j k) (𝒟.D j) ((𝒟.DD_le_left j k).trans (𝒟.le_inter j)),
    ← comp_natural K c (𝒟.s k) (𝒟.DD j k) (𝒟.D k) ((𝒟.DD_le_right j k).trans (𝒟.le_inter k)),
    F.res_res, F.res_res]
  exact agree K c hc (𝒟.s j) (𝒟.s k) (𝒟.DD j k) _ _ _

include hc hGq in
theorem exists_glue {W : V.affineOpens} (𝒟 : CoverData K W) (x : F.obj W.1) :
    ∃ y : G.obj W.1, ∀ j, G.res (𝒟.D_le j) y = loc c 𝒟 x j :=
  AlgebraicGeometry.OModulePresheaf.exists_forall_res_basicOpen_eq hGq W 𝒟.g 𝒟.cover (loc c 𝒟 x)
    (fun j k => loc_compat c hc 𝒟 x j k)

include hGq in
theorem glue_unique {W : V.affineOpens} (𝒟 : CoverData K W) {y y' : G.obj W.1}
    (h : ∀ j, G.res (𝒟.D_le j) y = G.res (𝒟.D_le j) y') : y = y' := by
  rw [← sub_eq_zero]
  refine AlgebraicGeometry.OModulePresheaf.eq_zero_of_forall_res_basicOpen_eq_zero hGq W 𝒟.g 𝒟.cover _
    fun j => ?_
  rw [map_sub, h j, sub_self]

def glueFun (W : V.affineOpens) (x : F.obj W.1) : G.obj W.1 :=
  Classical.choose (exists_glue c hc hGq (coverData K W) x)

theorem glueFun_spec (W : V.affineOpens) (x : F.obj W.1) (j : Fin (coverData K W).n) :
    G.res ((coverData K W).D_le j) (glueFun c hc hGq W x) = loc c (coverData K W) x j :=
  Classical.choose_spec (exists_glue c hc hGq (coverData K W) x) j

theorem eq_glueFun (W : V.affineOpens) (x : F.obj W.1) (y : G.obj W.1)
    (hy : ∀ j : Fin (coverData K W).n, G.res ((coverData K W).D_le j) y = loc c (coverData K W) x j) :
    y = glueFun c hc hGq W x :=
  glue_unique hGq (coverData K W) fun j => (hy j).trans (glueFun_spec c hc hGq W x j).symm

theorem glueFun_add (W : V.affineOpens) (x x' : F.obj W.1) :
    glueFun c hc hGq W (x + x') = glueFun c hc hGq W x + glueFun c hc hGq W x' := by
  refine (eq_glueFun c hc hGq W (x + x') _ fun j => ?_).symm
  rw [map_add, glueFun_spec, glueFun_spec]
  unfold loc
  rw [map_add, map_add]

theorem glueFun_smul (W : V.affineOpens) (a : Γ(V, W.1)) (x : F.obj W.1) :
    glueFun c hc hGq W (a • x) = a • glueFun c hc hGq W x := by
  refine (eq_glueFun c hc hGq W (a • x) _ fun j => ?_).symm
  rw [G.res_smul, glueFun_spec]
  unfold loc
  rw [F.res_smul, comp_smul]

theorem glueFun_smulR (W : V.affineOpens) (r : R) (x : F.obj W.1) :
    glueFun c hc hGq W (r • x) = r • glueFun c hc hGq W x := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π W.1
  rw [← algebraMap_smul (A := Γ(V, W.1)) r x, glueFun_smul, algebraMap_smul]

def glueLin (W : V.affineOpens) : F.obj W.1 →ₗ[R] G.obj W.1 where
  toFun := glueFun c hc hGq W
  map_add' := glueFun_add c hc hGq W
  map_smul' := glueFun_smulR c hc hGq W

theorem glueLin_apply (W : V.affineOpens) (x : F.obj W.1) : glueLin c hc hGq W x = glueFun c hc hGq W x := rfl

theorem basicOpen_res_eq {D W : V.Opens} (h : D ≤ W) (g : Γ(V, W)) :
    V.basicOpen ((V.presheaf.map (homOfLE h).op).hom g) = D ⊓ V.basicOpen g :=
  V.basicOpen_res g (homOfLE h).op

include hc hGq in

theorem char_of_spec {W : V.affineOpens} (𝒟 : CoverData K W) (x : F.obj W.1) (y : G.obj W.1)
    (hy : ∀ j, G.res (𝒟.D_le j) y = loc c 𝒟 x j) (D : V.affineOpens) (hDW : D.1 ≤ W.1)
    (s : K.Idx 0) (hDs : D.1 ≤ K.inter s) :
    G.res hDW y = comp K c s D hDs (F.res hDW x) := by

  let e : Fin 𝒟.n → Γ(V, D.1) := fun j => (V.presheaf.map (homOfLE hDW).op).hom (𝒟.g j)
  have he : ∀ j, V.basicOpen (e j) = D.1 ⊓ V.basicOpen (𝒟.g j) := fun j => basicOpen_res_eq hDW (𝒟.g j)
  have hcovD : D.1 ≤ ⨆ j, V.basicOpen (e j) := by
    intro z hz
    have hz' : z ∈ (⨆ j, V.basicOpen (𝒟.g j) : V.Opens) := 𝒟.cover (hDW hz)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hz'
    exact Opens.mem_iSup.mpr ⟨j, by rw [he j]; exact Opens.mem_inf.mpr ⟨hz, hj⟩⟩
  rw [← sub_eq_zero]
  refine AlgebraicGeometry.OModulePresheaf.eq_zero_of_forall_res_basicOpen_eq_zero hGq D e hcovD _
    fun j => ?_
  rw [map_sub, sub_eq_zero]

  have hED : V.basicOpen (e j) ≤ D.1 := V.basicOpen_le (e j)
  have hEDj : V.basicOpen (e j) ≤ (𝒟.D j).1 := (he j).le.trans inf_le_right
  have hEs : V.basicOpen (e j) ≤ K.inter s := hED.trans hDs
  have hEsj : V.basicOpen (e j) ≤ K.inter (𝒟.s j) := hEDj.trans (𝒟.le_inter j)
  change G.res hED (G.res hDW y) = G.res hED (comp K c s D hDs (F.res hDW x))

  rw [← comp_natural K c s ⟨V.basicOpen (e j), D.2.basicOpen (e j)⟩ D hEs hDs hED, F.res_res,
    agree K c hc s (𝒟.s j) ⟨V.basicOpen (e j), D.2.basicOpen (e j)⟩ hEs hEsj]

  rw [G.res_res, ← G.res_res hEDj (𝒟.D_le j), hy j]
  unfold loc
  rw [← comp_natural K c (𝒟.s j) ⟨V.basicOpen (e j), D.2.basicOpen (e j)⟩ (𝒟.D j) hEsj (𝒟.le_inter j) hEDj,
    F.res_res]

theorem glueFun_char (W : V.affineOpens) (x : F.obj W.1) (D : V.affineOpens) (hDW : D.1 ≤ W.1)
    (s : K.Idx 0) (hDs : D.1 ≤ K.inter s) :
    G.res hDW (glueFun c hc hGq W x) = comp K c s D hDs (F.res hDW x) :=
  char_of_spec c hc hGq (coverData K W) x (glueFun c hc hGq W x) (glueFun_spec c hc hGq W x) D hDW s hDs

theorem glueFun_natural (W W' : V.affineOpens) (h : W'.1 ≤ W.1) (x : F.obj W.1) :
    glueFun c hc hGq W' (F.res h x) = G.res h (glueFun c hc hGq W x) := by
  refine (eq_glueFun c hc hGq W' (F.res h x) _ fun j => ?_).symm
  rw [G.res_res, glueFun_char c hc hGq W x ((coverData K W').D j) (((coverData K W').D_le j).trans h)
    ((coverData K W').s j) ((coverData K W').le_inter j)]
  unfold loc
  rw [F.res_res]

def glued : (internalHom F G).obj ⊤ :=
  ⟨fun W => glueLin c hc hGq W.1,
    ⟨fun W a x => glueFun_smul c hc hGq W.1 a x, fun W W' h x => glueFun_natural c hc hGq W'.1 W.1 h x⟩⟩

theorem glued_val_apply (W : AffBelow (⊤ : V.Opens)) (x : F.obj W.1.1) :
    (glued c hc hGq).1 W x = glueFun c hc hGq W.1 x := rfl

theorem res_glued (s : K.Idx 0) : (internalHom F G).res (le_top : K.inter s ≤ ⊤) (glued c hc hGq) = c s := by
  refine Subtype.ext (funext fun W => LinearMap.ext fun x => ?_)
  rw [res_val]
  change glueFun c hc hGq W.1 x = (c s).1 W x
  have h := glueFun_char c hc hGq W.1 x W.1 le_rfl s W.2
  rw [F.res_refl_apply, G.res_refl_apply] at h
  exact h

end Glue
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx"

theorem res_top_ext (hGq : G.IsQuasicoherent) (φ ψ : (internalHom F G).obj ⊤)
    (h : ∀ s : K.Idx 0, (internalHom F G).res (le_top : K.inter s ≤ ⊤) φ = (internalHom F G).res (le_top : K.inter s ≤ ⊤) ψ) :
    φ = ψ := by
  refine Subtype.ext (funext fun W => LinearMap.ext fun x => ?_)
  obtain ⟨n, g, s, hle, hcov⟩ := coverData K W.1
  rw [← sub_eq_zero]
  refine AlgebraicGeometry.OModulePresheaf.eq_zero_of_forall_res_basicOpen_eq_zero hGq W.1 g hcov _
    fun j => ?_
  rw [map_sub, sub_eq_zero]
  have hDW : V.basicOpen (g j) ≤ W.1.1 := V.basicOpen_le (g j)
  have eφ := φ.2.2 ⟨⟨V.basicOpen (g j), W.1.2.basicOpen (g j)⟩, le_top⟩ W hDW x
  have eψ := ψ.2.2 ⟨⟨V.basicOpen (g j), W.1.2.basicOpen (g j)⟩, le_top⟩ W hDW x
  change φ.1 ⟨⟨V.basicOpen (g j), W.1.2.basicOpen (g j)⟩, le_top⟩ (F.res hDW x) = G.res hDW (φ.1 W x) at eφ
  change ψ.1 ⟨⟨V.basicOpen (g j), W.1.2.basicOpen (g j)⟩, le_top⟩ (F.res hDW x) = G.res hDW (ψ.1 W x) at eψ
  change G.res hDW (φ.1 W x) = G.res hDW (ψ.1 W x)
  rw [← eφ, ← eψ]

  exact congrArg
    (fun θ : (internalHom F G).obj (K.inter (s j)) => θ.1 ⟨⟨V.basicOpen (g j), W.1.2.basicOpen (g j)⟩, hle j⟩ (F.res hDW x))
    (h (s j))

theorem main (hGq : G.IsQuasicoherent) (c : (internalHom F G).cochain K 0) :
    (internalHom F G).d K 0 c = 0 ↔ ∃! φ : (internalHom F G).obj ⊤, ∀ s : K.Idx 0, c s = (internalHom F G).res le_top φ := by
  constructor
  · intro hc
    refine ⟨glued c hc hGq, fun s => (res_glued c hc hGq s).symm, fun ψ hψ => ?_⟩
    exact res_top_ext K hGq ψ (glued c hc hGq) fun s => by rw [← hψ s, res_glued]
  · rintro ⟨φ, hφ, -⟩
    have hcφ : c = fun s => (internalHom F G).res (le_top : K.inter s ≤ ⊤) φ := funext hφ
    rw [hcφ]
    exact d_zero_res_eq_zero (internalHom F G) K φ

end InternalHom
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx"

end HomGlueAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux"

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}
    (hGq : G.IsQuasicoherent) (K : V.OrderedAffineCover) (c : (OModulePresheaf.internalHom F G).cochain K 0) :
    (OModulePresheaf.internalHom F G).d K 0 c = 0 ↔
      ∃! φ : (OModulePresheaf.internalHom F G).obj ⊤,
        ∀ s : K.Idx 0, c s = (OModulePresheaf.internalHom F G).res le_top φ :=
  HomGlueAux.main K hGq c

end S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique (solution)
