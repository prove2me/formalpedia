-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.rpow_le_mul_card_rpow_mul_card_triangles_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:21:04.513359+00:00
-- url     : https://prove2.me/submissions/8bca5bce-33ed-4355-9799-3e979d56f1c9

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Pruning
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Embedding
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsMulticoloredSumFree_comp
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_triangles
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_rpow_le_mul_rpow_mul_card_triangles_rpow
attribute [local simp] ArithmeticTriangleRemovalInVectorSpaces.mem_triangles


section
public section
open Finset Function Submodule
namespace ArithmeticTriangleRemovalInVectorSpaces
variable {V : Type*}
private lemma lift_injective (p : ℕ) (a b : ZMod p) : Injective (lift (V := V) p a b) :=
  fun _ _ h ↦ congrArg Prod.fst h
variable [AddCommGroup V] {p : ℕ}
private lemma card_triangles_image_lift [DecidableEq V] (X Y Z : Finset V) :
    #(triangles (X.image (lift p 1 0)) (Y.image (lift p (-1) 1)) (Z.image (lift p 0 (-1)))) =
      #(triangles X Y Z) := by
  symm
  refine card_nbij' (fun (x, y, z) ↦ (lift p 1 0 x, lift p (-1) 1 y, lift p 0 (-1) z))
    (fun ((x, _), (y, _), (z, _)) ↦ (x, y, z)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ h
    simp only [mem_coe, mem_triangles, mem_image] at h ⊢
    obtain ⟨hx, hy, hz, h⟩ := h
    refine ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ⟨z, hz, rfl⟩, ?_⟩
    simp [lift, Prod.ext_iff, h]
  · rintro ⟨a, b, c⟩ h
    simp only [mem_coe, mem_triangles, mem_image] at h ⊢
    obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ⟨z, hz, rfl⟩, h⟩ := h
    simp only [lift, Prod.ext_iff, Prod.fst_add, Prod.fst_zero] at h ⊢
    obtain ⟨h, -⟩ := h
    exact ⟨hx, hy, hz, h⟩
  · rintro ⟨x, y, z⟩ -
    rfl
  · rintro ⟨a, b, c⟩ h
    simp only [mem_coe, mem_triangles, mem_image] at h
    obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ⟨z, hz, rfl⟩, -⟩ := h
    rfl
variable [Module (ZMod p) V]
private lemma linearIndependent_lift (x y : V) :
    LinearIndependent (ZMod p) ![lift p 1 0 x, lift p (-1) 1 y] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  simp only [lift, Prod.ext_iff, Prod.smul_mk, Prod.fst_add, Prod.snd_add, Prod.fst_zero,
    Prod.snd_zero, smul_eq_mul] at h
  grind
private lemma eq_of_lift_mem_span_left {x y x' : V}
    (h : lift p 1 0 x' ∈ span (ZMod p) {lift p 1 0 x, lift p (-1) 1 y}) : x' = x := by
  obtain ⟨s, t, h⟩ := mem_span_pair.1 h
  simp only [lift, Prod.ext_iff, Prod.smul_mk, Prod.fst_add, Prod.snd_add, smul_eq_mul] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  obtain rfl : t = 0 := by simpa using h₃
  obtain rfl : s = 1 := by simpa using h₂
  simpa using h₁.symm
private lemma eq_of_lift_mem_span_right {x y y' : V}
    (h : lift p (-1) 1 y' ∈ span (ZMod p) {lift p 1 0 x, lift p (-1) 1 y}) : y' = y := by
  obtain ⟨s, t, h⟩ := mem_span_pair.1 h
  simp only [lift, Prod.ext_iff, Prod.smul_mk, Prod.fst_add, Prod.snd_add, smul_eq_mul] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  obtain rfl : t = 1 := by simpa using h₃
  obtain rfl : s = 0 := by simpa using h₂
  simpa using h₁.symm
variable [DecidableEq V] {X Y Z : Finset V}
section GeneralPosition
variable {a b c a' b' c' : V × ZMod p × ZMod p}
private lemma linearIndependent_of_mem_triangles_image_lift
    (h : (a, b, c) ∈
      triangles (X.image (lift p 1 0)) (Y.image (lift p (-1) 1)) (Z.image (lift p 0 (-1)))) :
    LinearIndependent (ZMod p) ![a, b] := by
  simp only [mem_triangles, mem_image] at h
  obtain ⟨⟨x, -, rfl⟩, ⟨y, -, rfl⟩, -⟩ := h
  exact linearIndependent_lift x y
private lemma eq_of_mem_span_of_mem_triangles_image_lift
    (h : (a, b, c) ∈
      triangles (X.image (lift p 1 0)) (Y.image (lift p (-1) 1)) (Z.image (lift p 0 (-1))))
    (h' : (a', b', c') ∈
      triangles (X.image (lift p 1 0)) (Y.image (lift p (-1) 1)) (Z.image (lift p 0 (-1))))
    (ha : a' ∈ span (ZMod p) {a, b}) (hb : b' ∈ span (ZMod p) {a, b}) : a' = a ∧ b' = b := by
  simp only [mem_triangles, mem_image] at h h'
  obtain ⟨⟨x, -, rfl⟩, ⟨y, -, rfl⟩, -⟩ := h
  obtain ⟨⟨x', -, rfl⟩, ⟨y', -, rfl⟩, -⟩ := h'
  rw [eq_of_lift_mem_span_left ha, eq_of_lift_mem_span_right hb]
  exact ⟨rfl, rfl⟩
end GeneralPosition
variable [Fact p.Prime] [Fintype V] {ι : Type*} [Fintype ι] {x y z : ι → V}
end ArithmeticTriangleRemovalInVectorSpaces
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Function Submodule
open ArithmeticTriangleRemovalInVectorSpaces
variable {V : Type*}
variable [AddCommGroup V] {p : ℕ}
variable [Module (ZMod p) V]
variable [DecidableEq V] {X Y Z : Finset V}
variable [Fact p.Prime] [Fintype V] {ι : Type*} [Fintype ι] {x y z : ι → V}
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution (hx : Injective x) (hy : Injective y)
    (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z)
    (hsum : ∀ i, x i + y i + z i = 0) :
    (c p / (1 + c p) * Fintype.card ι / 2) ^ (1 + c p) ≤
      125 * p ^ 2 * (p ^ 2 * Fintype.card V) ^ (1 - c p) * #(triangles X Y Z) ^ c p := by
  have h := rpow_le_mul_rpow_mul_card_triangles_rpow (p := p)
    (fun _ _ _ ↦ linearIndependent_of_mem_triangles_image_lift)
    (fun _ _ _ h _ _ _ h' ↦ eq_of_mem_span_of_mem_triangles_image_lift h h')
    ((lift_injective _ _ _).comp hx) ((lift_injective _ _ _).comp hy)
    ((lift_injective _ _ _).comp hz) (fun i ↦ mem_image_of_mem _ (hxX i))
    (fun i ↦ mem_image_of_mem _ (hyY i)) (fun i ↦ mem_image_of_mem _ (hzZ i))
    (fun i ↦ by simp [lift, Prod.ext_iff, hsum i])
  rw [card_triangles_image_lift, Fintype.card_prod, Fintype.card_prod, ZMod.card] at h
  convert h using 4
  push_cast
  ring
end ArithmeticTriangleRemovalInVectorSpaces
