-- Prove2me | Definitions.Def_OccupiedOverlap
-- name    : OccupiedOverlap
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:16.825973+00:00
-- url     : https://prove2.me/theorems/816d613f-037e-4c13-8067-68a5364bf872
-- statement:
--   This block builds the Specht module of a Young diagram μ and defines a proposition (not an established theorem) bounding overlaps between row and column isotypic components. Tabloids of μ are functions from cells to row indices of the form rowIndex∘p for a permutation p of the cells; permutations act on them, giving a permutation representation on complex functions of tabloids. The polytabloid is the column-group alternator, the signed sum over permutations preserving each column, applied to the delta function at the base tabloid. The Specht space is the span of its orbit, a subrepresentation, which is identified with a subspace hilbertSpace μ of a Euclidean space, carries a unitary action, and can be relabelled by any bijection from another finite set to the cells. A representation is unitary if it preserves inner products. For a board Fin m × Fin n and an occupied finite subset Ω, rowGroup and columnGroup are the permutations of Ω preserving each row or each column. InHook a h means every cell (i,j) of a has i<h or j<h. For isometries Iᵢ: V→W, Intertwines means equivariance, and CompleteCopies means the Iᵢ are equivariant, have mutually orthogonal images, and their images together span the range of every intertwiner V→W, so they are all multiplicity copies of one irreducible. allCopyOverlap of isometries Iᵢ and Jⱼ into X is the sum over i,j of the squared operator norm of Iᵢ*Jⱼ. OccupiedOverlapEndpoint asserts that there is a constant C>0 such that for all m, n, Ω, Young diagram a, bijection e: Ω≃cells of a, and h with 1≤h≤mn and InHook a h, and for all unitary irreducible representations ρ of the row group (dimension r) and τ of the column group (dimension c), with complete copy families I and J inside the Specht space of a, with the group actions acting via the relabelled Specht representation restricted to rows and columns, the all-copy overlap is at most exp(C((m+n+1)h² log(mn+2) + (mn−|Ω|))) times min(1, rc/dim of the Specht space of a).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OccupiedOverlap.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/OccupiedOverlap.lean; bytes 16..10678
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace CubeShuffle.Specht

open scoped BigOperators Classical

abbrev Cell (μ : YoungDiagram) := {x : ℕ × ℕ // x ∈ μ.cells}
def row {μ : YoungDiagram} (x : Cell μ) : ℕ := x.1.1
def col {μ : YoungDiagram} (x : Cell μ) : ℕ := x.1.2

lemma row_lt_colLen {μ : YoungDiagram} (x : Cell μ) : row x < μ.colLen (col x) :=
  YoungDiagram.mem_iff_lt_colLen.mp x.2
noncomputable def rowIndex {μ : YoungDiagram} (x : Cell μ) : Fin (μ.colLen 0) :=
  ⟨row x, (row_lt_colLen x).trans_le (μ.colLen_anti 0 (col x) (Nat.zero_le _))⟩

abbrev Tabloid (μ : YoungDiagram) :=
  {f : Cell μ → Fin (μ.colLen 0) // ∃ p : Equiv.Perm (Cell μ), f = rowIndex ∘ p}

noncomputable instance (μ : YoungDiagram) : Fintype (Tabloid μ) := Fintype.ofFinite _

noncomputable def baseTabloid (μ : YoungDiagram) : Tabloid μ := ⟨rowIndex, 1, rfl⟩

noncomputable def tabloidAct {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) :
    Equiv.Perm (Tabloid μ) where
  toFun f := ⟨fun x => f.1 (p⁻¹ x), by
    obtain ⟨q,hq⟩ := f.2
    refine ⟨q*p⁻¹, ?_⟩
    funext x
    simp only [hq,Function.comp_apply,Equiv.Perm.mul_apply]⟩
  invFun f := ⟨fun x => f.1 (p x), by
    obtain ⟨q,hq⟩ := f.2
    refine ⟨q*p, ?_⟩
    funext x
    simp only [hq,Function.comp_apply,Equiv.Perm.mul_apply]⟩
  left_inv f := by apply Subtype.ext; funext x; simp
  right_inv f := by apply Subtype.ext; funext x; simp

@[simp] lemma tabloidAct_apply {μ : YoungDiagram} (p : Equiv.Perm (Cell μ))
    (f : Tabloid μ) (x : Cell μ) : (tabloidAct p f).1 x = f.1 (p⁻¹ x) := rfl

@[simp] lemma tabloidAct_one (μ : YoungDiagram) : tabloidAct (1 : Equiv.Perm (Cell μ)) = 1 := by
  ext f x
  rfl

@[simp] lemma tabloidAct_mul {μ : YoungDiagram} (p q : Equiv.Perm (Cell μ)) :
    tabloidAct (p*q) = tabloidAct p * tabloidAct q := by
  ext f x
  simp only [tabloidAct_apply, mul_inv_rev,Equiv.Perm.mul_apply]

@[simp] lemma tabloidAct_inv {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) :
    tabloidAct p⁻¹ = (tabloidAct p)⁻¹ := by
  ext f x
  simp [tabloidAct,Equiv.Perm.inv_def]

noncomputable def tabloidRep (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (Tabloid μ → ℂ) where
  toFun p :=
    { toFun := fun v f => v (tabloidAct p⁻¹ f)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext v f; simp
  map_mul' p q := by
    ext v f
    simp only [mul_inv_rev,tabloidAct_mul,Equiv.Perm.mul_apply]
    rfl

@[simp] lemma tabloidRep_apply {μ : YoungDiagram} (p : Equiv.Perm (Cell μ))
    (v : Tabloid μ → ℂ) (f : Tabloid μ) : tabloidRep μ p v f = v (tabloidAct p⁻¹ f) := rfl

noncomputable def delta {μ : YoungDiagram} (f : Tabloid μ) : Tabloid μ → ℂ :=
  fun g => if g=f then 1 else 0

noncomputable def colGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (Cell μ)) where
  carrier := {p | ∀ x, col (p x) = col x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro p q hp hq x; exact (hp (q x)).trans (hq x)
  inv_mem' := by intro p hp x; simpa using (hp (p⁻¹ x)).symm

noncomputable def permSign {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) : ℂ :=
  ((Equiv.Perm.sign p : ℤ) : ℂ)
section Alternator
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

noncomputable def alternator (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) : Module.End ℂ V := by
  classical
  exact ∑ c : C, permSign (c : Equiv.Perm α) • ρ c

end Alternator

noncomputable def polytabloid (μ : YoungDiagram) : Tabloid μ → ℂ :=
  alternator (colGroup μ) (tabloidRep μ) (delta (baseTabloid μ))

noncomputable def space (μ : YoungDiagram) : Submodule ℂ (Tabloid μ → ℂ) :=
  Submodule.span ℂ (Set.range (fun p : Equiv.Perm (Cell μ) => tabloidRep μ p (polytabloid μ)))

lemma orbit_mem_space (μ : YoungDiagram) (p : Equiv.Perm (Cell μ)) :
    tabloidRep μ p (polytabloid μ) ∈ space μ := Submodule.subset_span ⟨p,rfl⟩

lemma action_mem_space (μ : YoungDiagram) (p : Equiv.Perm (Cell μ))
    (v : Tabloid μ → ℂ) (hv : v ∈ space μ) : tabloidRep μ p v ∈ space μ := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨q,rfl⟩ := hv
    change ((tabloidRep μ p)*(tabloidRep μ q)) (polytabloid μ) ∈ space μ
    rw [←map_mul]
    exact orbit_mem_space μ (p*q)
  | zero => simp
  | add v w hv hw ihv ihw => simpa using (space μ).add_mem ihv ihw
  | smul a v hv ih => simpa using (space μ).smul_mem a ih

noncomputable def subrepresentation (μ : YoungDiagram) : Subrepresentation (tabloidRep μ) :=
  ⟨space μ, fun p v hv => action_mem_space μ p v hv⟩

noncomputable def representation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (space μ) :=
  (subrepresentation μ).toRepresentation

end CubeShuffle.Specht

namespace CubeShuffle.PermutationHilbert

open scoped BigOperators ComplexConjugate Classical
open Complex

variable {X : Type*} [Fintype X]

abbrev H (X : Type*) [Fintype X] := EuclideanSpace ℂ X

end CubeShuffle.PermutationHilbert

namespace CubeShuffle.Specht

open scoped BigOperators Classical

noncomputable def hilbertEquiv (μ : YoungDiagram) :
    (Tabloid μ → ℂ) ≃ₗ[ℂ] PermutationHilbert.H (Tabloid μ) :=
  (WithLp.linearEquiv 2 ℂ (Tabloid μ → ℂ)).symm

noncomputable def hilbertSpace (μ : YoungDiagram) :
    Submodule ℂ (PermutationHilbert.H (Tabloid μ)) := (space μ).map (hilbertEquiv μ).toLinearMap

noncomputable def spaceHilbertEquiv (μ : YoungDiagram) : space μ ≃ₗ[ℂ] hilbertSpace μ :=
  (hilbertEquiv μ).submoduleMap (space μ)

noncomputable def unitaryRepresentation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (hilbertSpace μ) :=
  ((spaceHilbertEquiv μ).conjAlgEquiv ℂ).toMonoidHom.comp (representation μ)

variable {α ι : Type*} [Fintype α] [Fintype ι]

noncomputable def relabelledUnitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation ℂ (Equiv.Perm α) (hilbertSpace μ) :=
  (unitaryRepresentation μ).comp e.permCongrHom.toMonoidHom

end CubeShuffle.Specht

namespace CubeShuffle.UnitaryFinite

open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

def IsUnitary (ρ : Representation ℂ G V) : Prop :=
  ∀ g v w, inner ℂ (ρ g v) (ρ g w) = inner ℂ v w

end CubeShuffle.UnitaryFinite

noncomputable section

open scoped BigOperators Classical

namespace RowColumn
open CubeShuffle CubeShuffle.Specht CubeShuffle.UnitaryFinite

/-- Permutations preserving each fibre of a given line map. -/
def lineGroup {α β : Type*} (f : α → β) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ x, f (g x) = f x}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro a b ha hb x
    exact (ha (b x)).trans (hb x)
  inv_mem' := by
    intro a ha x
    simpa using (ha (a⁻¹ x)).symm

abbrev Board (m n : ℕ) := Fin m × Fin n
abbrev rowGroup {m n : ℕ} (Ω : Finset (Board m n)) :=
  lineGroup (fun x : Ω => x.1.1)
abbrev columnGroup {m n : ℕ} (Ω : Finset (Board m n)) :=
  lineGroup (fun x : Ω => x.1.2)

/-- Zero-based form of the manuscript's (h,h)-hook. -/
def InHook (a : YoungDiagram) (h : ℕ) : Prop :=
  ∀ c ∈ a.cells, c.1 < h ∨ c.2 < h

section Copies
variable {G V W : Type*} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- An actual equivariant inclusion, not an unspecified overlap matrix. -/
def Intertwines (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (I : V →ₗ[ℂ] W) : Prop :=
  ∀ g v, I (ρ g v) = τ g (I v)

/-- All orthogonal multiplicity copies of one irreducible type. The completeness
condition quantifies over genuine intertwiners, i.e. it is exactly the isotypic
space condition. -/
def CompleteCopies (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    {u : ℕ} (I : Fin u → V →ₗᵢ[ℂ] W) : Prop :=
  (∀ i, Intertwines ρ τ (I i).toLinearMap) ∧
  (∀ i j, i ≠ j → ∀ v w, inner ℂ (I i v) (I j w) = 0) ∧
  ∀ J : V →ₗ[ℂ] W, Intertwines ρ τ J →
    LinearMap.range J ≤ ⨆ i, LinearMap.range (I i).toLinearMap

end Copies

/-- The all-copy operator-overlap sum, with each squared operator norm. -/
def allCopyOverlap {V W X : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    {u v : ℕ} (I : Fin u → V →ₗᵢ[ℂ] X) (J : Fin v → W →ₗᵢ[ℂ] X) : ℝ :=
  ∑ i, ∑ j, ‖((I i).toContinuousLinearMap.adjoint).comp
    (J j).toContinuousLinearMap‖ ^ 2

/-- Exact occupied-board main. Carriers are in orthonormal coordinates; arbitrary
unitary irreducibles of the two actual line groups are quantified over (equivalently,
the tuples of line partitions in the manuscript). Labelling `e` chooses the action
of the Specht module on the occupied cells and forces |a| = |Ω|. -/
abbrev OccupiedOverlapEndpoint : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ) (Ω : Finset (Board m n))
    (a : YoungDiagram) (e : Ω ≃ Cell a) (h : ℕ),
    1 ≤ h → h ≤ m * n → InHook a h →
    ∀ (r c u v : ℕ)
      (ρ : Representation ℂ (rowGroup Ω) (EuclideanSpace ℂ (Fin r)))
      (τ : Representation ℂ (columnGroup Ω) (EuclideanSpace ℂ (Fin c))),
      Representation.IsIrreducible ρ → Representation.IsIrreducible τ →
      IsUnitary ρ → IsUnitary τ →
    ∀ (I : Fin u → EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] hilbertSpace a)
      (J : Fin v → EuclideanSpace ℂ (Fin c) →ₗᵢ[ℂ] hilbertSpace a),
      CompleteCopies (V := EuclideanSpace ℂ (Fin r)) (W := hilbertSpace a) ρ ((relabelledUnitary a e).comp (rowGroup Ω).subtype) I →
      CompleteCopies (V := EuclideanSpace ℂ (Fin c)) (W := hilbertSpace a) τ ((relabelledUnitary a e).comp (columnGroup Ω).subtype) J →
      allCopyOverlap (V := EuclideanSpace ℂ (Fin r)) (W := EuclideanSpace ℂ (Fin c))
        (X := hilbertSpace a) I J ≤
        Real.exp (C * (((m + n + 1 : ℕ) : ℝ) * (h : ℝ)^2 *
          Real.log ((m * n : ℕ) + 2) + (m * n - Ω.card : ℕ))) *
          min 1 ((r : ℝ) * c / Module.finrank ℂ (space a))

end RowColumn

end



end OAI


