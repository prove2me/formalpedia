-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
-- name    : AlgebraicGeometry_ModulesSectionsTensor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/d4fadaee-2a55-5c98-a22b-0ab3425a5fd2
-- title:
--   Sections of tensor products, tensor powers, and frames
-- statement:
--   Fix a scheme $X$ and work in $X$-modules, i.e. sheaves of $\mathcal O_X$-modules with the monoidal structure obtained by sheafifying the presheaf-level tensor product. For $L, M : X.\mathrm{Modules}$, `tensorSectionsHom L M` is the morphism of presheaves of $\mathcal O_X$-modules from $L^{\mathrm{val}} \otimes M^{\mathrm{val}}$ (objectwise tensor product $U \mapsto L(U) \otimes_{\Gamma(X,U)} M(U)$) to the presheaf underlying $L \otimes M$, namely the unit of the sheafification adjunction followed by the image of the comparison isomorphism `tensorIsoSheafify L M`. Applying its component at an open $U$ to a pure tensor gives `tensorSections s t : Γ(L ⊗ M, U)` for $s \in \Gamma(L,U)$, $t \in \Gamma(M,U)$. Accompanying lemmas record additivity in each argument, $\Gamma(X,U)$-homogeneity in each argument, vanishing when one argument is $0$, behaviour under negation and finite sums, the bundled bilinear map `tensorSectionsBilin L M U`, and compatibility with restriction along $V \to U$. Next, `unitSection U` is the section $1 \in \Gamma(X,U)$ viewed in the tensor unit, with $g \cdot 1 = g$ and hence $g \mapsto g \cdot 1$ bijective; `tensorPowSection s n : Γ(L.tensorPow n, U)` is defined by recursion, equal to `unitSection U` for $n = 0$ and to `tensorSections (tensorPowSection s n) s` for $n+1$, again compatible with restriction. Finally, `IsFrameOn s V`, for $s \in \Gamma(M,U)$ and $V$ open, asserts that for every open $W$ with $W \le U$ and $W \le V$ the map $\Gamma(X,W) \to \Gamma(M,W)$, $g \mapsto g \cdot s|_W$, is bijective. Its lemmas give the bijectivity, monotonicity in $V$, equivalence of `IsFrameOn s V` with `IsFrameOn s (V ⊓ U)`, stability under restricting $s$ along $U' \to U$ and under transport by an isomorphism $M \cong N$, the unique-solution and $g \cdot s|_W = 0 \iff g = 0$ reformulations, and the fact that `unitSection U` is a frame on every open.
--
--   **Relation to Mathlib.** Mathlib provides the monoidal structure on presheaves of modules and the $\Gamma(M, U)$ notation; the monoidal structure on sheaves of modules and the comparison isomorphism with the sheafified presheaf tensor product come from the project's own modules. The section-level operations `tensorSections`, `tensorPowSection` and the predicate `IsFrameOn` are the project's own.
--
--   **Where it is used.** These definitions supply the section-level vocabulary for tensor products and tensor powers of module sheaves on a scheme, together with the notion of a local generator (frame) trivialising a module sheaf over an open set, as used in the scheme-theoretic parts of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesSectionsTensor.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Hom

variable (L M : X.Modules)

def tensorSectionsHom : L.val ⊗ M.val ⟶
    (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).obj (L ⊗ M) :=
  (SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (L.val ⊗ M.val) ≫
    (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).map (tensorIsoSheafify L M).hom

end Hom

section Sections

variable {L M : X.Modules} {U : X.Opens}

def tensorSections (s : Γ(L, U)) (t : Γ(M, U)) : Γ(L ⊗ M, U) :=
  DFunLike.coe (α := ((L.val ⊗ M.val).obj (op U) :)) (β := fun _ => Γ(L ⊗ M, U))
    ((tensorSectionsHom L M).app (op U)).hom
    ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))

lemma tensorSections_def (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections s t = DFunLike.coe (α := ((L.val ⊗ M.val).obj (op U) :)) (β := fun _ => Γ(L ⊗ M, U))
      ((tensorSectionsHom L M).app (op U)).hom
      ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))) := rfl

lemma tensorSections_add_left (s s' : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (s + s') t = tensorSections s t + tensorSections s' t := by
  rw [tensorSections_def, tensorSections_def, tensorSections_def]
  erw [TensorProduct.add_tmul, map_add]
  rfl

lemma tensorSections_add_right (s : Γ(L, U)) (t t' : Γ(M, U)) :
    tensorSections s (t + t') = tensorSections s t + tensorSections s t' := by
  rw [tensorSections_def, tensorSections_def, tensorSections_def]
  erw [TensorProduct.tmul_add, map_add]
  rfl

lemma tensorSections_smul_left (g : Γ(X, U)) (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (g • s) t = g • tensorSections s t := by
  rw [tensorSections_def, tensorSections_def]
  letI : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
  erw [← TensorProduct.smul_tmul', LinearMap.map_smul]
  rfl

lemma tensorSections_smul_right (g : Γ(X, U)) (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections s (g • t) = g • tensorSections s t := by
  rw [tensorSections_def, tensorSections_def]
  letI : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
  erw [TensorProduct.tmul_smul, LinearMap.map_smul]
  rfl

@[simp] lemma tensorSections_zero_left (t : Γ(M, U)) : tensorSections (0 : Γ(L, U)) t = 0 := by
  rw [tensorSections_def]
  erw [TensorProduct.zero_tmul, map_zero]

@[simp] lemma tensorSections_zero_right (s : Γ(L, U)) : tensorSections s (0 : Γ(M, U)) = 0 := by
  rw [tensorSections_def]
  erw [TensorProduct.tmul_zero, map_zero]

lemma tensorSections_neg_left (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (-s) t = -tensorSections s t := by
  rw [eq_neg_iff_add_eq_zero, ← tensorSections_add_left, neg_add_cancel, tensorSections_zero_left]

lemma tensorSections_neg_right (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections s (-t) = -tensorSections s t := by
  rw [eq_neg_iff_add_eq_zero, ← tensorSections_add_right, neg_add_cancel, tensorSections_zero_right]

lemma tensorSections_sum_left {ι : Type*} (S : Finset ι) (s : ι → Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (∑ i ∈ S, s i) t = ∑ i ∈ S, tensorSections (s i) t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, tensorSections_add_left, ih]

lemma tensorSections_sum_right {ι : Type*} (S : Finset ι) (s : Γ(L, U)) (t : ι → Γ(M, U)) :
    tensorSections s (∑ i ∈ S, t i) = ∑ i ∈ S, tensorSections s (t i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, tensorSections_add_right, ih]

variable (L M U) in

def tensorSectionsBilin : Γ(L, U) →ₗ[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U) :=
  LinearMap.mk₂ Γ(X, U) tensorSections tensorSections_add_left tensorSections_smul_left
    tensorSections_add_right tensorSections_smul_right

@[simp] lemma tensorSectionsBilin_apply (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSectionsBilin L M U s t = tensorSections s t := rfl

lemma map_tensorSections {V : X.Opens} (i : V ⟶ U) (s : Γ(L, U)) (t : Γ(M, U)) :
    (L ⊗ M).presheaf.map i.op (tensorSections s t) =
      tensorSections (L.presheaf.map i.op s) (M.presheaf.map i.op t) := by
  rw [tensorSections_def, tensorSections_def]
  have h := PresheafOfModules.naturality_apply (tensorSectionsHom L M) i.op
    ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul] at h
  exact h.symm

lemma map_homOfLE_tensorSections {V : X.Opens} (h : V ≤ U) (s : Γ(L, U)) (t : Γ(M, U)) :
    (L ⊗ M).presheaf.map (homOfLE h).op (tensorSections s t) =
      tensorSections (L.presheaf.map (homOfLE h).op s) (M.presheaf.map (homOfLE h).op t) :=
  map_tensorSections (homOfLE h) s t

end Sections

section Pow

variable {L : X.Modules} {U : X.Opens}

variable (U) in

def unitSection : Γ(𝟙_ X.Modules, U) := (1 : Γ(X, U))

lemma unitSection_def : (unitSection U : Γ(𝟙_ X.Modules, U)) = (1 : Γ(X, U)) := rfl

@[simp] lemma map_unitSection {V : X.Opens} (i : V ⟶ U) :
    (𝟙_ X.Modules).presheaf.map i.op (unitSection U) = unitSection V :=
  (X.presheaf.map i.op).hom.map_one

lemma smul_unitSection (g : Γ(X, U)) : g • unitSection U = (g : Γ(X, U)) :=
  mul_one g

lemma smul_unitSection_bijective : Function.Bijective fun g : Γ(X, U) => g • unitSection U := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun x => (x : Γ(X, U)), fun g => ?_, fun x => ?_⟩
  · exact mul_one g
  · exact mul_one (show Γ(X, U) from x)

def tensorPowSection (s : Γ(L, U)) : (n : ℕ) → Γ(L.tensorPow n, U)
  | 0 => unitSection U
  | n + 1 => tensorSections (L := L.tensorPow n) (M := L) (tensorPowSection s n) s

@[simp] lemma tensorPowSection_zero (s : Γ(L, U)) : tensorPowSection s 0 = unitSection U := rfl

lemma tensorPowSection_succ (s : Γ(L, U)) (n : ℕ) :
    tensorPowSection s (n + 1) = tensorSections (L := L.tensorPow n) (M := L) (tensorPowSection s n) s := rfl

lemma tensorPowSection_one (s : Γ(L, U)) :
    tensorPowSection s 1 = tensorSections (L := 𝟙_ X.Modules) (M := L) (unitSection U) s := rfl

lemma map_tensorPowSection {V : X.Opens} (i : V ⟶ U) (s : Γ(L, U)) (n : ℕ) :
    (L.tensorPow n).presheaf.map i.op (tensorPowSection s n) =
      tensorPowSection (L.presheaf.map i.op s) n := by
  induction n with
  | zero => exact map_unitSection i
  | succ n ih =>
    rw [tensorPowSection_succ, tensorPowSection_succ, ← ih]
    exact map_tensorSections (L := L.tensorPow n) (M := L) i _ s

end Pow

section Frame

variable {M : X.Modules} {U : X.Opens}

def IsFrameOn (s : Γ(M, U)) (V : X.Opens) : Prop :=
  ∀ ⦃W : X.Opens⦄ (hWU : W ≤ U), W ≤ V →
    Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE hWU).op s : Γ(M, W))

namespace IsFrameOn

variable {s : Γ(M, U)} {V : X.Opens}

lemma bijective (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) :
    Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE hWU).op s : Γ(M, W)) :=
  h hWU hWV

lemma mono (h : IsFrameOn s V) {V' : X.Opens} (hV' : V' ≤ V) : IsFrameOn s V' :=
  fun _ hWU hWV' => h hWU (hWV'.trans hV')

lemma of_inf (h : IsFrameOn s (V ⊓ U)) : IsFrameOn s V :=
  fun _ hWU hWV => h hWU (le_inf hWV hWU)

lemma inf_iff : IsFrameOn s (V ⊓ U) ↔ IsFrameOn s V :=
  ⟨of_inf, fun h => h.mono inf_le_left⟩

lemma map (h : IsFrameOn s V) {U' : X.Opens} (i : U' ⟶ U) :
    IsFrameOn (M.presheaf.map i.op s) V := by
  intro W hWU' hWV
  have e : M.presheaf.map (homOfLE hWU').op (M.presheaf.map i.op s) =
      M.presheaf.map (homOfLE (hWU'.trans i.le)).op s := by
    rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
    rfl
  simp only [e]
  exact h (hWU'.trans i.le) hWV

lemma existsUnique (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) (x : Γ(M, W)) :
    ∃! g : Γ(X, W), g • M.presheaf.map (homOfLE hWU).op s = x :=
  (Function.bijective_iff_existsUnique _).1 (h hWU hWV) x

lemma smul_eq_zero_iff (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) (g : Γ(X, W)) :
    g • M.presheaf.map (homOfLE hWU).op s = 0 ↔ g = 0 := by
  constructor
  · intro hg
    apply (h hWU hWV).1
    change g • M.presheaf.map (homOfLE hWU).op s = (0 : Γ(X, W)) • M.presheaf.map (homOfLE hWU).op s
    rw [hg, zero_smul]
  · rintro rfl
    exact zero_smul _ _

end IsFrameOn

lemma isFrameOn_unitSection (V : X.Opens) : IsFrameOn (unitSection U) V := by
  intro W hWU _
  have e : (𝟙_ X.Modules).presheaf.map (homOfLE hWU).op (unitSection U) = unitSection W :=
    map_unitSection _
  simp only [e]
  exact smul_unitSection_bijective

lemma IsFrameOn.map_iso {N : X.Modules} {s : Γ(M, U)} {V : X.Opens} (h : IsFrameOn s V) (e : M ≅ N) :
    IsFrameOn (e.hom.app U s) V := by
  intro W hWU hWV
  have nat : N.presheaf.map (homOfLE hWU).op (e.hom.app U s) =
      e.hom.app W (M.presheaf.map (homOfLE hWU).op s) := by
    have := (e.hom.mapPresheaf).naturality (homOfLE hWU).op
    exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, U) → Γ(N, W))) this) s).symm
  simp only [nat]
  have hb : Function.Bijective (e.hom.app W : Γ(M, W) → Γ(N, W)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨e.inv.app W, fun x => ?_, fun y => ?_⟩
    · change (e.hom.app W ≫ e.inv.app W) x = x
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
    · change (e.inv.app W ≫ e.hom.app W) y = y
      rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl
  have : (fun g : Γ(X, W) => g • e.hom.app W (M.presheaf.map (homOfLE hWU).op s)) =
      (e.hom.app W) ∘ fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s := by
    funext g
    simp only [Function.comp_apply, Scheme.Modules.Hom.app_smul]
  rw [this]
  exact hb.comp (h hWU hWV)

end Frame

end AlgebraicGeometry.Scheme.Modules

end


