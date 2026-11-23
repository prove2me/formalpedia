-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:18.544444+00:00
-- url     : https://prove2.me/theorems/da7f6432-92c6-4c0b-8621-88d98eb98806
-- title:
--   Cube Complex Acyclic Iff Quasi Iso Cech Aug
-- statement:
--   Definitions and structural lemmas for Cube Complex Acyclic Iff Quasi Iso Cech Aug, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
namespace GlobalTheory
namespace Cube
section Faces
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
def lowerFace (e : κ ↪o ι) (A : Cube.{v} ι R) : Cube.{v} κ R :=
  mk (fun s => A.obj (s.map e.toEmbedding)) (fun h => res A (Finset.map_subset_map.2 h))
    (fun _ _ => res_self A _ _) (fun _ _ _ => res_res A _ _ _)
def upperFace (e : κ ↪o ι) (i : ι) (A : Cube.{v} ι R) : Cube.{v} κ R :=
  mk (fun s => A.obj (insert i (s.map e.toEmbedding)))
    (fun h => res A (Finset.insert_subset_insert i (Finset.map_subset_map.2 h)))
    (fun _ _ => res_self A _ _) (fun _ _ _ => res_res A _ _ _)
variable (e : κ ↪o ι) (i : ι)
def faceMap (A : Cube.{v} ι R) : lowerFace e A ⟶ upperFace e i A :=
  homMk (fun s => res A (Finset.subset_insert i (s.map e.toEmbedding)))
    fun _ _ => (res_res A _ _ _).trans (res_res A _ _ _).symm
def lowerFaceMap {A B : Cube.{v} ι R} (φ : A ⟶ B) : lowerFace e A ⟶ lowerFace e B :=
  homMk (fun s => (φ.app (s.map e.toEmbedding)).hom) fun _ _ => app_res φ _ _
def upperFaceMap {A B : Cube.{v} ι R} (φ : A ⟶ B) : upperFace e i A ⟶ upperFace e i B :=
  homMk (fun s => (φ.app (insert i (s.map e.toEmbedding))).hom) fun _ _ => app_res φ _ _
@[reassoc]
theorem faceMap_naturality {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    lowerFaceMap e φ ≫ faceMap e i B = faceMap e i A ≫ upperFaceMap e i φ := by
  ext s x
  exact (app_res φ (Finset.subset_insert i (s.map e.toEmbedding)) x).symm
theorem cubeSign_map (s : Finset κ) (k : κ) :
    cubeSign (s.map e.toEmbedding) (e k) = cubeSign s k := by
  unfold cubeSign
  rw [Finset.filter_map, Finset.card_map]
  congr 2
  ext j
  simp
def upperSign (s : Finset κ) : ℤ :=
  (-1) ^ s.card * cubeSign (insert i (s.map e.toEmbedding)) i
@[simp]
theorem upperSign_mul_self (s : Finset κ) : upperSign e i s * upperSign e i s = 1 := by
  rw [upperSign, mul_mul_mul_comm, cubeSign_mul_self, ← mul_pow]; simp
@[simp]
theorem upperSign_smul_smul {M : Type*} [AddCommGroup M] (s : Finset κ) (x : M) :
    upperSign e i s • upperSign e i s • x = x := by
  rw [smul_smul, upperSign_mul_self, one_smul]
theorem totalD_map (A : Cube.{v} ι R) (x : ∀ t, A.obj t) (s : Finset κ) :
    totalD A x (s.map e.toEmbedding) =
      totalD (lowerFace e A) (fun s => x (s.map e.toEmbedding)) s := by
  rw [totalD_apply, Finset.sum_map]
  refine Eq.trans ?_ (totalD_apply (lowerFace e A) _ s).symm
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [res_congr A x (Finset.map_erase e.toEmbedding s k).symm _
    (Finset.map_subset_map.2 (Finset.erase_subset k s))]
  exact congrArg (· • _) (cubeSign_map e s k)
variable {e i}
theorem notMem_map_of_range_eq (he : Set.range e = {i}ᶜ) (s : Finset κ) :
    i ∉ s.map e.toEmbedding := by
  intro h
  obtain ⟨k, -, hk⟩ := Finset.mem_map.1 h
  have : i ∈ Set.range e := ⟨k, hk⟩
  simp [he] at this
theorem map_preimage_of_notMem (he : Set.range e = {i}ᶜ) {t : Finset ι} (ht : i ∉ t) :
    (t.preimage e e.injective.injOn).map e.toEmbedding = t := by
  ext j
  simp only [Finset.mem_map, Finset.mem_preimage]
  refine ⟨by rintro ⟨k, hk, rfl⟩; exact hk, fun hj => ?_⟩
  obtain ⟨k, rfl⟩ : j ∈ Set.range e := by
    rw [he]; rintro rfl; exact ht hj
  exact ⟨k, hj, rfl⟩
theorem preimage_insert_map (he : Set.range e = {i}ᶜ) (s : Finset κ) :
    (insert i (s.map e.toEmbedding)).preimage e e.injective.injOn = s := by
  ext k
  have : e k ≠ i := by
    have : e k ∈ Set.range e := ⟨k, rfl⟩
    simpa [he] using this
  simp [this]
theorem preimage_map_orderEmbedding (s : Finset κ) :
    (s.map e.toEmbedding).preimage e e.injective.injOn = s := by
  ext k
  simp
theorem exists_eq_map_or_eq_insert (he : Set.range e = {i}ᶜ) (t : Finset ι) :
    (∃ s : Finset κ, t = s.map e.toEmbedding) ∨
      ∃ s : Finset κ, t = insert i (s.map e.toEmbedding) := by
  by_cases ht : i ∈ t
  · exact Or.inr ⟨_, by rw [map_preimage_of_notMem he (Finset.notMem_erase i t),
      Finset.insert_erase ht]⟩
  · exact Or.inl ⟨_, (map_preimage_of_notMem he ht).symm⟩
theorem card_insert_map (he : Set.range e = {i}ᶜ) (s : Finset κ) :
    (insert i (s.map e.toEmbedding)).card = s.card + 1 := by
  rw [Finset.card_insert_of_notMem (notMem_map_of_range_eq he s), Finset.card_map]
theorem totalD_insert_map (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R) (x : ∀ t, A.obj t)
    (s : Finset κ) :
    upperSign e i s • totalD A x (insert i (s.map e.toEmbedding)) =
      totalD (upperFace e i A)
          (fun s => upperSign e i s • x (insert i (s.map e.toEmbedding))) s +
        (-1 : ℤ) ^ s.card • ((faceMap e i A).app s).hom (x (s.map e.toEmbedding)) := by
  have hi := notMem_map_of_range_eq he s
  rw [totalD_apply, Finset.sum_insert hi, Finset.sum_map, smul_add, add_comm,
    res_congr A x (Finset.erase_insert hi) _ (Finset.subset_insert _ _), Finset.smul_sum]
  refine congrArg₂ (· + ·) (Eq.trans (Finset.sum_congr rfl fun k hk => ?_)
    (totalD_apply (upperFace e i A) _ s).symm) ?_
  · have hki : e k ≠ i := fun h => hi (Finset.mem_map.2 ⟨k, hk, h⟩)
    have h1 : (insert i (s.map e.toEmbedding)).erase (e k) =
        insert i ((s.erase k).map e.toEmbedding) := by
      rw [Finset.erase_insert_of_ne hki.symm, Finset.map_erase]; rfl
    have h2 := cubeSign_mul_erase (t := insert i (s.map e.toEmbedding)) (i := i) (j := e k)
      (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨k, hk, rfl⟩)) hki.symm
    rw [h1, Finset.erase_insert hi, cubeSign_map] at h2
    have h3 : upperSign e i s * cubeSign (insert i (s.map e.toEmbedding)) (e k) =
        cubeSign s k * upperSign e i (s.erase k) := by
      rw [upperSign, upperSign, ← Finset.card_erase_add_one hk, pow_succ]
      have a1 := cubeSign_mul_self (insert i (s.map e.toEmbedding)) i
      have a2 := cubeSign_mul_self (insert i ((s.erase k).map e.toEmbedding)) i
      generalize cubeSign (insert i (s.map e.toEmbedding)) i = a at *
      generalize cubeSign (insert i ((s.erase k).map e.toEmbedding)) i = b at *
      generalize cubeSign (insert i (s.map e.toEmbedding)) (e k) = c at *
      generalize cubeSign s k = f at *
      generalize (-1 : ℤ) ^ (s.erase k).card = g
      linear_combination (-(g * a * b)) * h2 + (g * f * b) * a1 + (g * a * c) * a2
    refine Eq.trans (congrArg (fun y => upperSign e i s • cubeSign _ (e k) • y)
      (res_congr A x h1 _ (Finset.insert_subset_insert i
        (Finset.map_subset_map.2 (Finset.erase_subset k s))))) ?_
    rw [smul_smul, h3, ← smul_smul, ← map_zsmul]
    rfl
  · rw [upperSign, smul_smul, mul_assoc, cubeSign_mul_self, mul_one]
    rfl
end Faces
section Terms
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι}
variable (e) in

def termLower (A : Cube.{v} ι R) (p : ℕ) : Term A p →ₗ[R] Term (lowerFace e A) p :=
  LinearMap.pi fun s => LinearMap.proj (R := R)
    (φ := fun t : {t : Finset ι // t.card = p} => A.obj t.1)
    ⟨s.1.map e.toEmbedding, (Finset.card_map _).trans s.2⟩
theorem termLower_apply (A : Cube.{v} ι R) (p : ℕ) (x : Term A p)
    (s : {s : Finset κ // s.card = p}) :
    termLower e A p x s = x ⟨s.1.map e.toEmbedding, (Finset.card_map _).trans s.2⟩ := rfl
def termUpper (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R) (p : ℕ) :
    Term A (p + 1) →ₗ[R] Term (upperFace e i A) p :=
  LinearMap.pi fun s => upperSign e i s.1 • LinearMap.proj (R := R)
    (φ := fun t : {t : Finset ι // t.card = p + 1} => A.obj t.1)
    ⟨insert i (s.1.map e.toEmbedding), by rw [card_insert_map he, s.2]⟩
theorem termUpper_apply (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R) (p : ℕ) (x : Term A (p + 1))
    (s : {s : Finset κ // s.card = p}) :
    termUpper he A p x s = upperSign e i s.1 •
      x ⟨insert i (s.1.map e.toEmbedding), by rw [card_insert_map he, s.2]⟩ := rfl
variable (e i) in

noncomputable def termIncl (A : Cube.{v} ι R) (p : ℕ) :
    Term (upperFace e i A) p →ₗ[R] Term A (p + 1) :=
  LinearMap.pi fun t => if h : i ∈ t.1 then
    upperSign e i (t.1.preimage e e.injective.injOn) •
      (res A (s := insert i ((t.1.preimage e e.injective.injOn).map e.toEmbedding)) (t := t.1)
        (Finset.insert_subset h fun j hj => by
          obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hj
          exact Finset.mem_preimage.1 hk) ∘ₗ
        LinearMap.proj (R := R) (φ := fun s : Finset κ => (upperFace e i A).obj s)
          (t.1.preimage e e.injective.injOn) ∘ₗ extend (upperFace e i A) p)
    else 0
variable (e i) in

noncomputable def termSec (A : Cube.{v} ι R) (p : ℕ) :
    Term (lowerFace e A) p →ₗ[R] Term A p :=
  LinearMap.pi fun t => if i ∈ t.1 then 0 else
    res A (s := (t.1.preimage e e.injective.injOn).map e.toEmbedding) (t := t.1)
        (fun j hj => by
          obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hj
          exact Finset.mem_preimage.1 hk) ∘ₗ
        LinearMap.proj (R := R) (φ := fun s : Finset κ => (lowerFace e A).obj s)
          (t.1.preimage e e.injective.injOn) ∘ₗ extend (lowerFace e A) p
variable (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R)
theorem termIncl_apply_of_notMem {p : ℕ} (y : Term (upperFace e i A) p)
    (t : {t : Finset ι // t.card = p + 1}) (ht : i ∉ t.1) : termIncl e i A p y t = 0 := by
  rw [termIncl, LinearMap.pi_apply, dif_neg ht]; rfl
theorem termIncl_apply_insert {p : ℕ} (y : Term (upperFace e i A) p)
    (s : {s : Finset κ // s.card = p}) :
    termIncl e i A p y ⟨insert i (s.1.map e.toEmbedding), by rw [card_insert_map he, s.2]⟩ =
      upperSign e i s.1 • y s := by
  rw [termIncl, LinearMap.pi_apply, dif_pos (Finset.mem_insert_self _ _)]
  have key : ∀ (s' : Finset κ) (_ : s' = s.1) (h : insert i (s'.map e.toEmbedding) ⊆
      insert i (s.1.map e.toEmbedding)), upperSign e i s' • res A h
        (extend (upperFace e i A) p y s') = upperSign e i s.1 • y s := by
    rintro _ rfl h
    rw [extend_apply_of_eq _ y s.2]
    exact congrArg (upperSign e i s.1 • ·) (res_self A h _)
  exact key _ (preimage_insert_map he s.1) _
theorem termSec_apply_of_mem {p : ℕ} (y : Term (lowerFace e A) p)
    (t : {t : Finset ι // t.card = p}) (ht : i ∈ t.1) : termSec e i A p y t = 0 := by
  rw [termSec, LinearMap.pi_apply, if_pos ht]; rfl
include he in

theorem termSec_apply_map {p : ℕ} (y : Term (lowerFace e A) p)
    (s : {s : Finset κ // s.card = p}) :
    termSec e i A p y ⟨s.1.map e.toEmbedding, (Finset.card_map _).trans s.2⟩ = y s := by
  rw [termSec, LinearMap.pi_apply, if_neg (notMem_map_of_range_eq he s.1)]
  have key : ∀ (s' : Finset κ) (_ : s' = s.1) (h : s'.map e.toEmbedding ⊆
      s.1.map e.toEmbedding), res A h (extend (lowerFace e A) p y s') = y s := by
    rintro _ rfl h
    rw [extend_apply_of_eq _ y s.2]
    exact res_self A h _
  exact key _ (preimage_map_orderEmbedding s.1) _
@[simp]
theorem termUpper_termIncl {p : ℕ} (y : Term (upperFace e i A) p) :
    termUpper he A p (termIncl e i A p y) = y := by
  funext s
  rw [termUpper_apply, termIncl_apply_insert he]
  exact upperSign_smul_smul e i s.1 (y s)
include he in

theorem termLower_termIncl {p : ℕ} (y : Term (upperFace e i A) p) :
    termLower e A (p + 1) (termIncl e i A p y) = 0 :=
  funext fun s => termIncl_apply_of_notMem A y _ (notMem_map_of_range_eq he s.1)
include he in

theorem termLower_termSec {p : ℕ} (y : Term (lowerFace e A) p) :
    termLower e A p (termSec e i A p y) = y :=
  funext fun s => termSec_apply_map he A y s
@[simp]
theorem termUpper_termSec {p : ℕ} (y : Term (lowerFace e A) (p + 1)) :
    termUpper he A p (termSec e i A (p + 1) y) = 0 := by
  funext s
  rw [termUpper_apply, termSec_apply_of_mem A y _ (Finset.mem_insert_self _ _), smul_zero]
  rfl
theorem term_ext_faces {p : ℕ} {x y : Term A (p + 1)}
    (h₁ : termUpper he A p x = termUpper he A p y)
    (h₂ : termLower e A (p + 1) x = termLower e A (p + 1) y) : x = y := by
  funext ⟨t, ht⟩
  rcases exists_eq_map_or_eq_insert he t with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · exact congrFun h₂ ⟨s, (Finset.card_map _).symm.trans ht⟩
  · have hs : s.card = p := by rw [card_insert_map he] at ht; omega
    have h := congrArg (upperSign e i s • ·) (congrFun h₁ ⟨s, hs⟩)
    exact (upperSign_smul_smul e i s _).symm.trans (h.trans (upperSign_smul_smul e i s _))
include he in

theorem termLower_zero_injective : Function.Injective (termLower e A 0) := by
  intro x y h
  funext ⟨t, ht⟩
  rcases exists_eq_map_or_eq_insert he t with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · exact congrFun h ⟨s, (Finset.card_map _).symm.trans ht⟩
  · rw [card_insert_map he] at ht; omega
theorem termIncl_add_termSec {p : ℕ} (x : Term A (p + 1)) :
    termIncl e i A p (termUpper he A p x) + termSec e i A (p + 1) (termLower e A (p + 1) x) = x :=
  term_ext_faces he A (by simp) (by simp [termLower_termSec he, termLower_termIncl he])
include he in

theorem termSec_termLower_zero (x : Term A 0) : termSec e i A 0 (termLower e A 0 x) = x :=
  termLower_zero_injective he A (termLower_termSec he A _)
theorem termLower_d {p : ℕ} (x : Term A p) :
    termLower e A (p + 1) (d A p x) = d (lowerFace e A) p (termLower e A p x) := by
  funext s
  rw [termLower_apply, d_apply_eq_totalD A x _ (fun s => (extend_apply_of_eq A x s.2).symm),
    totalD_map]
  exact (d_apply_eq_totalD (lowerFace e A) (termLower e A p x)
    (fun s => extend A p x (s.map e.toEmbedding))
    (fun s => (extend_apply_of_eq A x ((Finset.card_map _).trans s.2)).symm) s).symm
theorem termUpper_d {p : ℕ} (x : Term A (p + 1)) :
    termUpper he A (p + 1) (d A (p + 1) x) = d (upperFace e i A) p (termUpper he A p x) +
      (-1 : ℤ) ^ (p + 1) • termMap (faceMap e i A) (p + 1) (termLower e A (p + 1) x) := by
  funext s
  rw [termUpper_apply, d_apply_eq_totalD A x _ (fun s => (extend_apply_of_eq A x s.2).symm),
    totalD_insert_map he]
  refine congrArg₂ (· + ·) (d_apply_eq_totalD _ _ _ (fun s => ?_) s).symm ?_
  · exact congrArg (upperSign e i s.1 • ·) (extend_apply_of_eq A x _).symm
  · rw [s.2, extend_apply_of_eq A x ((Finset.card_map _).trans s.2)]
    rfl
include he in

theorem d_termIncl {p : ℕ} (y : Term (upperFace e i A) p) :
    d A (p + 1) (termIncl e i A p y) = termIncl e i A (p + 1) (d (upperFace e i A) p y) :=
  term_ext_faces he A (by simp [termUpper_d, termLower_termIncl he])
    (by simp [termLower_d, termLower_termIncl he])
variable {A} {B : Cube.{v} ι R} (φ : A ⟶ B)
theorem termLower_termMap {p : ℕ} (x : Term A p) :
    termLower e B p (termMap φ p x) = termMap (lowerFaceMap e φ) p (termLower e A p x) := rfl
theorem termUpper_termMap {p : ℕ} (x : Term A (p + 1)) :
    termUpper he B p (termMap φ (p + 1) x) =
      termMap (upperFaceMap e i φ) p (termUpper he A p x) :=
  funext fun s => (map_zsmul (φ.app (insert i (s.1.map e.toEmbedding))).hom _ _).symm
include he in

theorem termMap_termIncl {p : ℕ} (y : Term (upperFace e i A) p) :
    termMap φ (p + 1) (termIncl e i A p y) =
      termIncl e i B p (termMap (upperFaceMap e i φ) p y) :=
  term_ext_faces he B (by simp [termUpper_termMap])
    (by simp [termLower_termMap, termLower_termIncl he])
end Terms
end Cube
section Shift
def succEmbedding : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
  ComplexShape.embeddingUp'Add 1 1
instance succEmbedding_isRelIff : succEmbedding.IsRelIff :=
  inferInstanceAs (ComplexShape.embeddingUp'Add (1 : ℕ) 1).IsRelIff
theorem succEmbedding_f (p : ℕ) : succEmbedding.f p = p + 1 := rfl
theorem succEmbedding_f_ne_zero (p : ℕ) : succEmbedding.f p ≠ 0 := Nat.succ_ne_zero p
variable {R : Type u} [Ring R]
noncomputable abbrev shiftSucc (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    CochainComplex (ModuleCat.{v} R) ℕ := K.extend succEmbedding
noncomputable abbrev shiftSuccXIso (K : CochainComplex (ModuleCat.{v} R) ℕ) (p : ℕ) :
    (shiftSucc K).X (p + 1) ≅ K.X p := K.extendXIso succEmbedding (succEmbedding_f p)
noncomputable abbrev shiftSuccHomologyIso (K : CochainComplex (ModuleCat.{v} R) ℕ) (p : ℕ) :
    (shiftSucc K).homology (p + 1) ≅ K.homology p :=
  K.extendHomologyIso succEmbedding (succEmbedding_f p)
theorem isZero_shiftSucc_X_zero (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    IsZero ((shiftSucc K).X 0) := K.isZero_extend_X _ 0 succEmbedding_f_ne_zero
theorem shiftSucc_d (K : CochainComplex (ModuleCat.{v} R) ℕ) (p : ℕ) :
    (shiftSucc K).d (p + 1) (p + 1 + 1) =
      (shiftSuccXIso K p).hom ≫ K.d p (p + 1) ≫ (shiftSuccXIso K (p + 1)).inv :=
  K.extend_d_eq _ (succEmbedding_f p) (succEmbedding_f (p + 1))
end Shift
section Cone
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι}
variable (e) in

def cubeLowerProj (A : Cube.{v} ι R) : cubeComplex A ⟶ cubeComplex (Cube.lowerFace e A) :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (Cube.termLower e A p)) fun p => by
    rw [cubeComplex_d, cubeComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => (Cube.termLower_d A x).symm)
@[reassoc]
theorem cubeLowerProj_naturality {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    cubeComplexMap φ ≫ cubeLowerProj e B =
      cubeLowerProj e A ≫ cubeComplexMap (Cube.lowerFaceMap e φ) := rfl
variable (e i) in

noncomputable def cubeInclX (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComplex (Cube.upperFace e i A)).X p ⟶ (cubeComplex A).X (p + 1) :=
  ModuleCat.ofHom (Cube.termIncl e i A p)
variable (e i) in

noncomputable def cubeSecX (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComplex (Cube.lowerFace e A)).X p ⟶ (cubeComplex A).X p :=
  ModuleCat.ofHom (Cube.termSec e i A p)
variable (e i) in

noncomputable def cubeUpperInclF (A : Cube.{v} ι R) : ∀ p : ℕ,
    (shiftSucc (cubeComplex (Cube.upperFace e i A))).X p ⟶ (cubeComplex A).X p
  | 0 => 0
  | p + 1 => (shiftSuccXIso _ p).hom ≫ cubeInclX e i A p
variable (he : Set.range e = {i}ᶜ)
noncomputable def cubeUpperIncl (A : Cube.{v} ι R) :
    shiftSucc (cubeComplex (Cube.upperFace e i A)) ⟶ cubeComplex A :=
  CochainComplex.ofHom (cubeUpperInclF e i A) fun p => by
    cases p with
    | zero => exact (isZero_shiftSucc_X_zero _).eq_of_src _ _
    | succ p =>
      change ((shiftSuccXIso _ p).hom ≫ cubeInclX e i A p) ≫ _ =
        _ ≫ (shiftSuccXIso _ (p + 1)).hom ≫ cubeInclX e i A (p + 1)
      rw [shiftSucc_d, Category.assoc, Category.assoc,
        Category.assoc, Iso.inv_hom_id_assoc, cubeComplex_d, cubeComplex_d]
      congr 1
      exact ModuleCat.hom_ext (LinearMap.ext fun x => Cube.d_termIncl he A x)
theorem cubeUpperIncl_f_succ (A : Cube.{v} ι R) (p : ℕ) :
    (cubeUpperIncl he A).f (p + 1) = (shiftSuccXIso _ p).hom ≫ cubeInclX e i A p := rfl
@[reassoc]
theorem cubeUpperIncl_naturality {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    extendMap (cubeComplexMap (Cube.upperFaceMap e i φ)) succEmbedding ≫ cubeUpperIncl he B =
      cubeUpperIncl he A ≫ cubeComplexMap φ := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  cases p with
  | zero => exact (isZero_shiftSucc_X_zero _).eq_of_src _ _
  | succ p =>
    rw [comp_f, comp_f, cubeUpperIncl_f_succ, cubeUpperIncl_f_succ,
      extendMap_f _ _ (succEmbedding_f p), Category.assoc, Category.assoc, Category.assoc,
      Iso.inv_hom_id_assoc]
    congr 1
    exact ModuleCat.hom_ext (LinearMap.ext fun x => (Cube.termMap_termIncl he φ x).symm)
noncomputable abbrev cubeFaceSequence (A : Cube.{v} ι R) :
    ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ) :=
  ShortComplex.mk (cubeUpperIncl he A) (cubeLowerProj e A) (by
    refine HomologicalComplex.hom_ext _ _ fun p => ?_
    cases p with
    | zero => exact (isZero_shiftSucc_X_zero _).eq_of_src _ _
    | succ p =>
      rw [comp_f, cubeUpperIncl_f_succ, Category.assoc, zero_f]
      have h : cubeInclX e i A p ≫ (cubeLowerProj e A).f (p + 1) = 0 :=
        ModuleCat.hom_ext (LinearMap.ext fun x => Cube.termLower_termIncl he A x)
      rw [h, comp_zero])
noncomputable def cubeFaceSequenceMap {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    cubeFaceSequence he A ⟶ cubeFaceSequence he B where
  τ₁ := extendMap (cubeComplexMap (Cube.upperFaceMap e i φ)) succEmbedding
  τ₂ := cubeComplexMap φ
  τ₃ := cubeComplexMap (Cube.lowerFaceMap e φ)
  comm₁₂ := cubeUpperIncl_naturality he φ
  comm₂₃ := cubeLowerProj_naturality φ
noncomputable def cubeFaceSplitting (A : Cube.{v} ι R) : ∀ p : ℕ,
    ((cubeFaceSequence he A).map (eval _ _ p)).Splitting
  | 0 =>
    { r := 0
      s := cubeSecX e i A 0
      f_r := (isZero_shiftSucc_X_zero _).eq_of_src _ _
      s_g := ModuleCat.hom_ext (LinearMap.ext fun x => Cube.termLower_termSec he A x)
      id := by
        rw [zero_comp, zero_add]
        exact ModuleCat.hom_ext (LinearMap.ext fun x => Cube.termSec_termLower_zero he A x) }
  | p + 1 =>
    { r := ModuleCat.ofHom (Cube.termUpper he A p) ≫
        (shiftSuccXIso (cubeComplex (Cube.upperFace e i A)) p).inv
      s := cubeSecX e i A (p + 1)
      f_r := by
        have h : ModuleCat.ofHom (Cube.termIncl e i A p) ≫
            ModuleCat.ofHom (Cube.termUpper he A p) =
            𝟙 ((cubeComplex (Cube.upperFace e i A)).X p) :=
          ModuleCat.hom_ext (LinearMap.ext fun x => Cube.termUpper_termIncl he A x)
        let j := shiftSuccXIso (cubeComplex (Cube.upperFace e i A)) p
        have h' := congrArg (fun f => j.hom ≫ f ≫ j.inv) h
        simp only [Category.id_comp, Iso.hom_inv_id] at h'
        exact h'
      s_g := ModuleCat.hom_ext (LinearMap.ext fun x => Cube.termLower_termSec he A x)
      id := by
        refine ModuleCat.hom_ext (LinearMap.ext fun x =>
          Eq.trans ?_ (Cube.termIncl_add_termSec he A x))
        let j := shiftSuccXIso (cubeComplex (Cube.upperFace e i A)) p
        have h : j.hom.hom (j.inv.hom (Cube.termUpper he A p x)) = Cube.termUpper he A p x :=
          congr(($(j.inv_hom_id)).hom (Cube.termUpper he A p x))
        exact congrArg (fun y => Cube.termIncl e i A p y +
          Cube.termSec e i A (p + 1) (Cube.termLower e A (p + 1) x)) h }
theorem cubeFaceSequence_shortExact (A : Cube.{v} ι R) : (cubeFaceSequence he A).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p =>
    (cubeFaceSplitting he A p).shortExact
end Cone
section FiveLemma
open ComposableArrows Abelian HomologySequence
variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
include hS₁ hS₂
end FiveLemma
section Corollaries
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι} (he : Set.range e = {i}ᶜ)
include he
end Corollaries
section DegreeZero
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
end DegreeZero
section Cech
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
def cechAugX (A : Cube.{v} ι R) : A.obj ∅ ⟶ (cechComplex A).X 0 := ModuleCat.ofHom (Cube.aug A)
noncomputable def cechAugHomology (A : Cube.{v} ι R) : A.obj ∅ ⟶ (cechComplex A).homology 0 :=
  (cechComplex A).liftCycles (cechAugX A) 1 (by simp) (by
      rw [cechComplex_d A 0]
      exact ModuleCat.hom_ext (LinearMap.ext (Cube.d_aug A))) ≫
    (cechComplex A).homologyπ 0
@[reassoc]
theorem cechAugHomology_naturality {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    φ.app ∅ ≫ cechAugHomology B = cechAugHomology A ≫ homologyMap (cechComplexMap φ) 0 := by
  rw [cechAugHomology, cechAugHomology, Category.assoc, homologyπ_naturality, ← Category.assoc,
    ← Category.assoc]
  congr 1
  rw [← cancel_mono ((cechComplex B).iCycles 0), Category.assoc, Category.assoc, liftCycles_i,
    cyclesMap_i, liftCycles_i_assoc]
  exact ModuleCat.hom_ext (LinearMap.ext fun a => (Cube.termMap_aug φ a).symm)
noncomputable def cechHomologySuccIso (A : Cube.{v} ι R) (p : ℕ) :
    (cechComplex A).homology (p + 1) ≅ (cubeComplex A).homology (p + 2) :=
  (cechComplex A).homologyIsoSc' p (p + 1) (p + 2) (by simp) (by simp) ≪≫
    ((cubeComplex A).homologyIsoSc' (p + 1) (p + 2) (p + 3) (by simp) (by simp)).symm
end Cech
section Main
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
abbrev otherDirections (i : ι) : {j : ι // j ≠ i} ↪o ι := OrderEmbedding.subtype _
theorem range_otherDirections (i : ι) : Set.range (otherDirections i) = {i}ᶜ := by
  ext j
  exact ⟨by rintro ⟨k, rfl⟩; exact k.2, fun h => ⟨⟨j, h⟩, rfl⟩⟩
example (A : Cube.{v} ι R) (i : ι) : (cubeFaceSequence (range_otherDirections i) A).ShortExact :=
  cubeFaceSequence_shortExact _ A
example {n : ℕ} (A : Cube.{v} (Fin (n + 1)) R) (i : Fin (n + 1)) :
    (cubeFaceSequence (e := Fin.succAboveOrderEmb i) (Fin.range_succAbove i) A).ShortExact :=
  cubeFaceSequence_shortExact _ A
end Main
end GlobalTheory


