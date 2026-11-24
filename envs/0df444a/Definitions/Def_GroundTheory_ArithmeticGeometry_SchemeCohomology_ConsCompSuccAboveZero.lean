-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:22.398578+00:00
-- url     : https://prove2.me/theorems/b344696a-4764-4550-9d04-82c061db6d90
-- title:
--   Cons Comp Succ Above Zero
-- statement:
--   Definitions and structural lemmas for Cons Comp Succ Above Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
def inter (U : ι → Opens X) {n : ℕ} (i : Fin n → ι) : Opens X := ⨅ a, U (i a)
lemma inter_le_comp (U : ι → Opens X) {m n : ℕ} (i : Fin n → ι) (θ : Fin m → Fin n) :
    inter U i ≤ inter U (i ∘ θ) :=
  le_iInf fun a => iInf_le (fun b => U (i b)) (θ a)
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
abbrev Cochain (n : ℕ) : Type (max w u) := ∀ i : Fin (n + 1) → ι, P.obj (op (inter U i))
def res {V W : Opens X} (h : V ≤ W) : P.obj (op W) →+ P.obj (op V) :=
  (P.map (homOfLE h).op).hom
@[simp] lemma res_res {V W Z : Opens X} (h₁ : V ≤ W) (h₂ : W ≤ Z) (x : P.obj (op Z)) :
    res P h₁ (res P h₂ x) = res P (h₁.trans h₂) x := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl
@[simp] lemma res_refl {V : Opens X} (h : V ≤ V) (x : P.obj (op V)) : res P h x = x := by
  simp only [res]
  have : (homOfLE h).op = 𝟙 (op V) := rfl
  rw [this, CategoryTheory.Functor.map_id]
  rfl
def cochainMap {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) : Cochain P U m →+ Cochain P U n where
  toFun σ i := res P (inter_le_comp U i θ) (σ (i ∘ θ))
  map_zero' := by ext i; simp
  map_add' σ τ := by ext i; simp
noncomputable def cechCosimplicial : CosimplicialObject AddCommGrpCat.{max w u} where
  obj n := AddCommGrpCat.of (Cochain P U n.len)
  map θ := AddCommGrpCat.ofHom (cochainMap P U θ.toOrderHom)
  map_id n := by
    ext σ i
    simp only [cochainMap]
    exact res_refl P _ _
  map_comp θ θ' := by
    ext σ i
    simp [cochainMap]
    rfl
noncomputable def d (n : ℕ) : Cochain P U n →+ Cochain P U (n + 1) :=
  (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cechCosimplicial P U) n).hom
variable {P} in

def push {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (n : ℕ) :
    Cochain P U n →+ Cochain P' U n where
  toFun σ i := φ.app _ (σ i)
  map_zero' := by ext i; simp
  map_add' σ τ := by ext i; simp
def CechAcyclic : Prop :=
  ∀ (n : ℕ) (σ : Cochain P U (n + 1)), d P U (n + 1) σ = 0 → ∃ τ, d P U n τ = σ
def discPresheaf (A : X → AddCommGrpCat.{u}) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (∀ x : W.unop, A x.1)
  map h := AddCommGrpCat.ofHom
    { toFun := fun s x => s ⟨x.1, h.unop.le x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl
variable (A : X → AddCommGrpCat.{u})
def ev {W : Opens X} (x : X) (hx : x ∈ W) : (discPresheaf A).obj (op W) →+ A x :=
  Pi.evalAddMonoidHom (fun y : W => A y.1) ⟨x, hx⟩
lemma mem_inter_iff {n : ℕ} (i : Fin n → ι) (x : X) : x ∈ inter U i ↔ ∀ a, x ∈ U (i a) := by
  rw [inter, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  rfl
attribute [irreducible] inter
noncomputable def chosenIdx (x : X) (h : ∃ a, x ∈ U a) : ι := h.choose
lemma mem_chosenIdx (x : X) (h : ∃ a, x ∈ U a) : x ∈ U (chosenIdx U x h) := h.choose_spec
lemma exists_mem_of_mem_inter {m : ℕ} (j : Fin (m + 1) → ι) {x : X} (hx : x ∈ inter U j) :
    ∃ a, x ∈ U a :=
  ⟨j 0, (mem_inter_iff U j x).1 hx 0⟩
lemma mem_inter_cons {m : ℕ} (j : Fin (m + 1) → ι) {x : X} (hx : x ∈ inter U j) :
    x ∈ inter U (Fin.cons (chosenIdx U x (exists_mem_of_mem_inter U j hx)) j :
      Fin (m + 2) → ι) := by
  rw [mem_inter_iff]
  intro a
  cases a using Fin.cases with
  | zero => simpa using mem_chosenIdx U x _
  | succ a => simpa using (mem_inter_iff U j x).1 hx a
noncomputable def homotopy {n : ℕ} (σ : Cochain (discPresheaf A) U (n + 1)) :
    Cochain (discPresheaf A) U n :=
  fun j y => ev A y.1 (mem_inter_cons U j y.2)
    (σ (Fin.cons (chosenIdx U y.1 (exists_mem_of_mem_inter U j y.2)) j))
end GroundTheory.Arith.SchemeCoh


