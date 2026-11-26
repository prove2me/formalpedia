-- Prove2me | Definitions.Def_Stanley_Convolution
-- name    : Stanley_Convolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:56:11.529977+00:00
-- url     : https://prove2.me/theorems/84f482f8-344f-514f-90b0-40fd6297efe1
-- title:
--   Convolution
-- statement:
--   Definitions and structural lemmas for Convolution, from Juan Pablo Traverso Gianini (jtraverso/stanley; ChromaticPolynomial/ adapted under Apache-2.0 from anlucia/ChromaticPolynomial by Angelo Lucia; see pinned LICENSE and THIRD_PARTY.md)'s pinned Stanley's acyclic orientations and chromatic reciprocity development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Convolution.lean

module
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
public import Definitions.Def_Stanley_SourceSum
public import Mathlib.Algebra.Polynomial.Roots
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Stanley
open SimpleGraph Finset Polynomial
universe u v w
variable {V : Type u} {α : Type v} {β : Type w} [Fintype V] (G : SimpleGraph V)
noncomputable def joinColor (s : Finset V)
    (A : (G.induce (s : Set V)).Coloring α)
    (B : (G.induce (s : Set V)ᶜ).Coloring β) : G.Coloring (α ⊕ β) := by
  classical
  refine Coloring.mk (fun v => if hv : v ∈ s then Sum.inl (A ⟨v, hv⟩)
    else Sum.inr (B ⟨v, hv⟩)) ?_
  intro u v h
  by_cases hu : u ∈ s <;> by_cases hv : v ∈ s
  · simpa [hu, hv] using A.valid (show (G.induce (s : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ from h)
  · simp [hu, hv]
  · simp [hu, hv]
  · simpa [hu, hv] using B.valid (show (G.induce (s : Set V)ᶜ).Adj ⟨u, hu⟩ ⟨v, hv⟩ from h)
noncomputable def colorSumEquiv :
    (Σ s : Finset V, (G.induce (s : Set V)).Coloring α ×
      (G.induce (s : Set V)ᶜ).Coloring β) ≃ G.Coloring (α ⊕ β) := by
  classical
  apply Equiv.ofBijective (fun x => joinColor G x.1 x.2.1 x.2.2)
  constructor
  · rintro ⟨s, A, B⟩ ⟨t, C, D⟩ h
    have hst : s = t := by
      ext v
      have hv := congrArg (fun c : G.Coloring (α ⊕ β) => (c v).isLeft) h
      simpa [joinColor, Coloring.mk, apply_dite Sum.isLeft] using hv
    subst t
    have hA : A = C := by
      ext v
      have hv := congrArg (fun c : G.Coloring (α ⊕ β) => c v.val) h
      simpa [joinColor, Coloring.mk, v.property] using hv
    have hB : B = D := by
      ext v
      have hv := congrArg (fun c : G.Coloring (α ⊕ β) => c v.val) h
      have hn : v.val ∉ s := v.property
      simpa [joinColor, Coloring.mk, hn] using hv
    cases hA
    cases hB
    rfl
  · intro c
    let s : Finset V := univ.filter (fun v => (c v).isLeft)
    have hl (v : (s : Set V)) : (c v.val).isLeft := (mem_filter.mp v.property).2
    have hr (v : ((s : Set V)ᶜ : Set V)) : (c v.val).isRight := by
      apply Sum.not_isLeft.mp
      intro h
      exact v.property (mem_filter.mpr ⟨mem_univ _, h⟩)
    let A : (G.induce (s : Set V)).Coloring α := Coloring.mk
      (fun v => (c v.val).getLeft (hl v)) (by
        intro u v h he
        apply c.valid (show G.Adj u.val v.val from h)
        change c u.val = c v.val
        rw [← Sum.inl_getLeft (c u.val) (hl u), ← Sum.inl_getLeft (c v.val) (hl v), he])
    let B : (G.induce (s : Set V)ᶜ).Coloring β := Coloring.mk
      (fun v => (c v.val).getRight (hr v)) (by
        intro u v h he
        apply c.valid (show G.Adj u.val v.val from h)
        change c u.val = c v.val
        rw [← Sum.inr_getRight (c u.val) (hr u), ← Sum.inr_getRight (c v.val) (hr v), he])
    refine ⟨⟨s, A, B⟩, ?_⟩
    ext v
    by_cases hv : v ∈ s
    · simp [joinColor, Coloring.mk, hv, A]
    · simp [joinColor, Coloring.mk, hv, B]
end Stanley


