-- Prove2me | Definitions.Def_CategoryTheory_OverTotalPresheaf
-- name    : CategoryTheory_OverTotalPresheaf
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/bfa7b3d7-f61f-52b8-963f-4ecec99cf124
-- title:
--   Total presheaf of a presheaf on an over category
-- statement:
--   Fix a category $\mathcal C$ with an object $S$ and a presheaf $G \colon (\mathcal C/S)^{\mathrm{op}} \to \mathrm{Type}\,w$. For $T$ an object of $\mathcal C$, `OverTotal G T` is the dependent sum $\Sigma\,(t \colon T \to S),\ G(\mathrm{Over.mk}\ t)$, i.e. the set of pairs $(t,x)$ with $t$ a morphism $T \to S$ and $x$ an element of the value of $G$ at the object $t$ of $\mathcal C/S$; it lives in $\mathrm{Type}\,(\max w\, v)$, $v$ being the universe of morphisms of $\mathcal C$. These sets are assembled into a presheaf `overTotal G` $\colon \mathcal C^{\mathrm{op}} \to \mathrm{Type}\,(\max w\, v)$: a morphism $\varphi \colon T' \to T$ of $\mathcal C$ sends $(t,x)$ to $(\varphi \circ' t, G(\varphi)x)$, where $\varphi$ is viewed as a morphism $\mathrm{Over.mk}(\varphi \circ' t) \to \mathrm{Over.mk}\,t$ in $\mathcal C/S$; functoriality rests on the fact that $G$ applied to a morphism of $\mathcal C/S$ depends only on the underlying morphism of $\mathcal C$, recorded in the group of transport lemmas `map_op_apply_eq_of_left_eq`, `map_op_apply_eq_self` and the composite variants.
--
--   For $T$ an object of $\mathcal C/S$, the maps `OverTotal.toFibre` and `OverTotal.ofFibre` identify $G(T)$ with the elements of `OverTotal G T.left` whose first component equals the structure morphism `T.hom`; `toFibre_ofFibre`, `ofFibre_toFibre` and `toFibre_naturality` state that these are mutually inverse and natural in $T$, and `OverTotal.ext'` is the corresponding extensionality principle for pairs.
--
--   Finally, given `e : (overTotal G).RepresentableBy Y`, `overTotalBase e` is the morphism $Y \to S$ obtained as the first component of the universal element $e(\mathrm{id}_Y)$; `overTotal_homEquiv_fst` says every $k \colon T \to Y$ satisfies $e(k)_1 = k$ followed by this base morphism, and `ofOverTotal` produces from $e$ a `RepresentableBy` witness for $G$ with representing object $Y \to S$ of $\mathcal C/S$, the bijection $\mathrm{Hom}_{\mathcal C/S}((T,t),(Y,p)) \simeq G(T,t)$ being $g \mapsto$ the fibre element attached to $e(g_{\mathrm{left}})$.
--
--   **Relation to Mathlib.** Built on Mathlib's `Over` category and `CategoryTheory.Functor.RepresentableBy`; the total-presheaf construction and the transfer of representability from the total presheaf to the presheaf on the over category are the project's own, and are set up with independent universes for the values of $G$ and the morphisms of $\mathcal C$.
--
--   **Where it is used.** The construction lets representability criteria proved for presheaves on the category of all schemes be applied to functors on schemes over a fixed base: one forms the total presheaf, represents it, and reads off a representing object over the base. It is used in this way for relative Picard-type functors appearing in the construction of the moduli spaces underlying the modularity arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CategoryTheory_OverTotalPresheaf.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Category Opposite

namespace CategoryTheory.Functor

universe w v u

variable {C : Type u} [Category.{v} C] {S : C} (G : (Over S)ᵒᵖ ⥤ Type w)

abbrev OverTotal (T : C) : Type (max w v) := Σ t : T ⟶ S, G.obj (op (Over.mk t))

variable {G}

lemma map_op_apply_eq_of_left_eq {A B : Over S} (k k' : A ⟶ B) (h : k.left = k'.left) (x : G.obj (op B)) :
    G.map k.op x = G.map k'.op x := by
  rw [Over.OverMorphism.ext h]

lemma map_op_apply_eq_self {A : Over S} (k : A ⟶ A) (h : k.left = 𝟙 _) (x : G.obj (op A)) :
    G.map k.op x = x := by
  rw [show k = 𝟙 A from Over.OverMorphism.ext (by simpa using h), op_id, Functor.map_id_apply]

lemma map_op_map_op_apply {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B') (x : G.obj (op B')) :
    G.map k.op (G.map k'.op x) = G.map (k ≫ k').op x := by
  rw [op_comp, Functor.map_comp_apply]

lemma map_op_map_op_apply_eq_self {A B : Over S} (k : A ⟶ B) (k' : B ⟶ A) (h : (k ≫ k').left = 𝟙 _)
    (x : G.obj (op A)) : G.map k.op (G.map k'.op x) = x := by
  rw [map_op_map_op_apply]
  exact map_op_apply_eq_self _ h x

lemma map_op_map_op_map_op_apply_eq_self {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B') (k'' : B' ⟶ A)
    (h : (k ≫ k' ≫ k'').left = 𝟙 _) (x : G.obj (op A)) : G.map k.op (G.map k'.op (G.map k''.op x)) = x := by
  rw [map_op_map_op_apply, map_op_map_op_apply]
  exact map_op_apply_eq_self _ (by rw [assoc]; exact h) x

lemma map_op_map_op_apply_eq {A B B' D : Over S} (k : A ⟶ B) (k' : B ⟶ B') (l : A ⟶ D) (l' : D ⟶ B')
    (h : (k ≫ k').left = (l ≫ l').left) (x : G.obj (op B')) :
    G.map k.op (G.map k'.op x) = G.map l.op (G.map l'.op x) := by
  rw [map_op_map_op_apply, map_op_map_op_apply]
  exact map_op_apply_eq_of_left_eq _ _ h x

lemma OverTotal.ext' {T : C} {a b : G.OverTotal T} (h₁ : a.1 = b.1)
    (h₂ : G.map (Over.homMk (𝟙 T) (by simp [h₁]) : Over.mk b.1 ⟶ Over.mk a.1).op a.2 = b.2) : a = b := by
  obtain ⟨t, x⟩ := a
  obtain ⟨t', y⟩ := b
  obtain rfl : t = t' := h₁
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  dsimp only at h₂
  rw [← h₂]
  symm
  exact map_op_apply_eq_self _ (by simp) x

variable (G)

def overTotal : Cᵒᵖ ⥤ Type (max w v) where
  obj T := G.OverTotal T.unop
  map {T T'} φ := TypeCat.ofHom fun a =>
    ⟨φ.unop ≫ a.1, G.map (Over.homMk φ.unop rfl : Over.mk (φ.unop ≫ a.1) ⟶ Over.mk a.1).op a.2⟩
  map_id T := TypeCat.homEquiv.injective (funext fun a =>
    OverTotal.ext' (by simp) (map_op_map_op_apply_eq_self _ _ (by simp) _))
  map_comp {T T' T''} φ ψ := TypeCat.homEquiv.injective (funext fun a =>
    OverTotal.ext' (by simp) (map_op_map_op_apply_eq _ _ _ _ (by simp) _))

@[simp] lemma overTotal_map_fst {T T' : Cᵒᵖ} (φ : T ⟶ T') (a : G.overTotal.obj T) :
    (G.overTotal.map φ a).1 = φ.unop ≫ a.1 := rfl

variable {G}

def OverTotal.toFibre (T : Over S) (b : G.OverTotal T.left) (hb : b.1 = T.hom) : G.obj (op T) :=
  G.map (Over.homMk (𝟙 T.left) (by simpa using hb) : T ⟶ Over.mk b.1).op b.2

lemma OverTotal.toFibre_congr (T : Over S) {b b' : G.OverTotal T.left} (h : b = b') (hb : b.1 = T.hom)
    (hb' : b'.1 = T.hom) : OverTotal.toFibre T b hb = OverTotal.toFibre T b' hb' := by
  subst h; rfl

def OverTotal.ofFibre (T : Over S) (x : G.obj (op T)) : G.OverTotal T.left :=
  ⟨T.hom, G.map (Over.homMk (𝟙 T.left) (by simp) : Over.mk T.hom ⟶ T).op x⟩

@[simp] lemma OverTotal.ofFibre_fst (T : Over S) (x : G.obj (op T)) : (OverTotal.ofFibre T x).1 = T.hom := rfl

lemma OverTotal.toFibre_ofFibre (T : Over S) (x : G.obj (op T)) :
    OverTotal.toFibre T (OverTotal.ofFibre T x) rfl = x :=
  map_op_map_op_apply_eq_self _ _ (by simp) x

lemma OverTotal.ofFibre_toFibre (T : Over S) (b : G.OverTotal T.left) (hb : b.1 = T.hom) :
    OverTotal.ofFibre T (OverTotal.toFibre T b hb) = b :=
  OverTotal.ext' (by simpa using hb.symm) (map_op_map_op_map_op_apply_eq_self _ _ _ (by simp) _)

lemma OverTotal.toFibre_naturality {T T' : Over S} (φ : T ⟶ T') (b : G.OverTotal T'.left) (hb : b.1 = T'.hom)
    (hb' : (G.overTotal.map φ.left.op b).1 = T.hom) :
    OverTotal.toFibre T (G.overTotal.map φ.left.op b) hb' = G.map φ.op (OverTotal.toFibre T' b hb) :=
  map_op_map_op_apply_eq _ _ _ _ (by simp) _

namespace RepresentableBy

variable {Y : C} (e : G.overTotal.RepresentableBy Y)

def overTotalBase : Y ⟶ S := (e.homEquiv (𝟙 Y)).1

lemma overTotal_homEquiv_fst {T : C} (k : T ⟶ Y) : (e.homEquiv k).1 = k ≫ e.overTotalBase := by
  have h := e.homEquiv_comp k (𝟙 Y)
  rw [comp_id] at h
  rw [h]
  rfl

noncomputable def ofOverTotal : G.RepresentableBy (Over.mk e.overTotalBase) where
  homEquiv {T} :=
    { toFun := fun g => OverTotal.toFibre T (e.homEquiv g.left)
        (by rw [overTotal_homEquiv_fst]; exact Over.w g)
      invFun := fun x => Over.homMk (e.homEquiv.symm (OverTotal.ofFibre T x)) (by
        have h := e.overTotal_homEquiv_fst (e.homEquiv.symm (OverTotal.ofFibre T x))
        rw [Equiv.apply_symm_apply, OverTotal.ofFibre_fst] at h
        exact h.symm)
      left_inv := fun g => by
        apply Over.OverMorphism.ext
        simp only [Over.homMk_left]
        apply e.homEquiv.injective
        rw [Equiv.apply_symm_apply, OverTotal.ofFibre_toFibre]
      right_inv := fun x =>
        (OverTotal.toFibre_congr T (e.homEquiv.apply_symm_apply (OverTotal.ofFibre T x)) _ rfl).trans
          (OverTotal.toFibre_ofFibre T x) }
  homEquiv_comp {T T'} φ g := by
    have hg : (e.homEquiv g.left).1 = T'.hom := by
      rw [overTotal_homEquiv_fst]; exact Over.w g
    have hφg : (e.homEquiv (φ ≫ g).left).1 = T.hom := by
      rw [overTotal_homEquiv_fst]; exact Over.w (φ ≫ g)
    have hb' : (G.overTotal.map φ.left.op (e.homEquiv g.left)).1 = T.hom := by
      rw [overTotal_map_fst, overTotal_homEquiv_fst, Quiver.Hom.unop_op, ← assoc]
      exact Over.w (φ ≫ g)
    calc OverTotal.toFibre T (e.homEquiv (φ ≫ g).left) hφg
        = OverTotal.toFibre T (G.overTotal.map φ.left.op (e.homEquiv g.left)) hb' :=
          OverTotal.toFibre_congr T (e.homEquiv_comp φ.left g.left) hφg hb'
      _ = G.map φ.op (OverTotal.toFibre T' (e.homEquiv g.left) hg) :=
          OverTotal.toFibre_naturality φ _ hg hb'

end RepresentableBy

end CategoryTheory.Functor


