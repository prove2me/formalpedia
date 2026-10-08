-- Prove2me | Definitions.Def_WeightedSweepMoments
-- name    : WeightedSweepMoments
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:31.303407+00:00
-- url     : https://prove2.me/theorems/df394271-a336-4176-8fae-58edcab8f099
-- statement:
--   For a Young diagram μ, a cell is a pair (row, column) in μ, and a tabloid is a function from the cells of μ to the row indices {0,…,colLen(0)−1} that has the form (row index of x) composed with some permutation of the cells, that is, a rearrangement of the cell-to-row labelling. A permutation p of the cells acts on tabloids by (p·f)(x)=f(p⁻¹x), and tabloidRep(μ) is the induced complex linear representation on functions from tabloids to ℂ, with (p·v)(f)=v(p⁻¹·f). The base tabloid is the row-index function itself, delta(f) is the indicator function of a tabloid f, and colGroup(μ) is the subgroup of permutations preserving every cell's column. The polytabloid is the alternator of the delta at the base tabloid, namely the sum over c in colGroup of sign(c) times c acting on it. The Specht space(μ) is the complex span of all permutation translates of the polytabloid; it is invariant under the action, so it carries a subrepresentation of the symmetric group on the cells, and its dimension is defined as a real number, dimension(μ)=finrank of space(μ). Transporting this space into the Euclidean space ℂ^{Tabloid μ} gives hilbertSpace(μ), with the transported representation called unitaryRepresentation; the source does not itself prove it is unitary. For a diagram of size N, a fixed label equivalence identifies cells with Fin N, and for N=2^d it identifies the cube Card d={0,1}^d (d-bit strings) with the cells, so cardRepresentation(d,μ) is a representation of permutations of the d-bit strings on hilbertSpace(μ). The shuffling process uses coin data: Coins(0) is a single point and Coins(d+1) is the set of Boolean functions on d-bit strings. For d+1 bits and a coin function ξ, pairSwitch(ξ) is the involution that replaces the first bit by its XOR with ξ applied to the remaining bits, rotate permutes the coordinates cyclically, one step is rotate composed after pairSwitch(ξ) (the identity when d=0), and run(d,t) composes t such steps for a sequence of t coin choices, with the latest step applied last. For a finite group representation on a finite-dimensional complex inner product space, sampleOperator averages the continuous linear operators ρ(P ω) over all ω in a finite sample space. Then fourierSweep(d,μ) is this average over all d-step coin sequences ω:Fin d→Coins(d) of cardRepresentation(d,μ) applied to run(d,d)(ω), an operator on hilbertSpace(μ). Finally, schattenMoment(A,p) is the sum, over the finrank-many singular values σᵢ of a linear map A on a finite-dimensional complex inner product space, of σᵢ^p, and schattenNorm(A,p) is that moment raised to the power 1/p. The block gives these definitions and a few supporting lemmas, such as closure of the Specht space under the action, and states no main theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/WeightedSweepMoments.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/WeightedSweepMoments.lean; bytes 16..10593
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

namespace CubeShuffle

open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

def Coins : ℕ → Type
  | 0 => Unit
  | d + 1 => Card d → Bool

instance (d : ℕ) : Fintype (Coins d) := by
  cases d <;> dsimp [Coins] <;> infer_instance

instance (d : ℕ) : Nonempty (Coins d) := by
  cases d <;> dsimp [Coins] <;> infer_instance

def switchFun {d : ℕ} (ξ : Card d → Bool) (x : Card (d + 1)) : Card (d + 1) :=
  Fin.cons (Bool.xor (x 0) (ξ (Fin.tail x))) (Fin.tail x)

theorem switchFun_involutive {d : ℕ} (ξ : Card d → Bool) :
    Function.Involutive (switchFun ξ) := by
  intro x
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [switchFun, Fin.cons_zero, Fin.tail_cons]
    cases x 0 <;> cases ξ (Fin.tail x) <;> rfl
  · simp [switchFun, Fin.tail]

def pairSwitch {d : ℕ} (ξ : Card d → Bool) : Equiv.Perm (Card (d + 1)) :=
  { toFun := switchFun ξ
    invFun := switchFun ξ
    left_inv := switchFun_involutive ξ
    right_inv := switchFun_involutive ξ }

def rotate (d : ℕ) : Equiv.Perm (Card d) where
  toFun x i := x (finRotate d i)
  invFun x i := x ((finRotate d).symm i)
  left_inv x := by funext i; simp only [Equiv.apply_symm_apply]
  right_inv x := by funext i; simp only [Equiv.symm_apply_apply]

def step : (d : ℕ) → Coins d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, ξ => rotate (d + 1) * pairSwitch ξ

def run (d : ℕ) : (t : ℕ) → (Fin t → Coins d) → Equiv.Perm (Card d)
  | 0, _ => 1
  | t + 1, ω => step d (ω (Fin.last t)) * run d t (fun i => ω i.castSucc)

lemma card_positions (d : ℕ) : Fintype.card (Card d) = 2 ^ d := by
  simp [Card]

end CubeShuffle

namespace CubeShuffle.Specht
open scoped BigOperators Classical

@[simp] lemma card_cell (μ : YoungDiagram) : Fintype.card (Cell μ) = μ.card := by
  simp [Cell, YoungDiagram.card]

abbrev Shapes (N : ℕ) := {μ : YoungDiagram // μ.card = N}

noncomputable def labels {N : ℕ} (μ : Shapes N) : Cell μ.1 ≃ Fin N :=
  (Fintype.equivFin (Cell μ.1)).trans (finCongr ((card_cell μ.1).trans μ.2))

noncomputable def cardLabels (d : ℕ) (μ : Shapes (2^d)) : Card d ≃ Cell μ.1 :=
  ((Fintype.equivFin (Card d)).trans (finCongr (card_positions d))).trans (labels μ).symm

noncomputable def cardRepresentation (d : ℕ) (μ : Shapes (2^d)) :
    Representation ℂ (Equiv.Perm (Card d)) (hilbertSpace μ.1) :=
  relabelledUnitary μ.1 (cardLabels d μ)

end CubeShuffle.Specht

namespace CubeShuffle.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def continuousRepresentation (ρ : Representation ℂ G V) : G →* (V →L[ℂ] V) where
  toFun g := (ρ g).toContinuousLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

end CubeShuffle.UnitaryFinite


namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def sampleOperator (ρ : Representation ℂ G V) (P : Ω → G) : V →L[ℂ] V :=
  (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,continuousRepresentation ρ (P ω)

end CubeShuffle.UnitaryFinite

noncomputable section
open scoped BigOperators Classical

namespace CubeShuffle.WeightedSweep
open Specht UnitaryFinite

def dimension (μ : YoungDiagram) : ℝ := Module.finrank ℂ (space μ)
def fourierSweep (d : ℕ) (μ : Shapes (2^d)) :
    hilbertSpace μ.1 →L[ℂ] hilbertSpace μ.1 :=
  sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d d)
def schattenMoment {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (A : V →L[ℂ] V) (p : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℂ V), (A.toLinearMap.singularValues i) ^ p

def schattenNorm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (A : V →L[ℂ] V) (p : ℝ) : ℝ :=
  schattenMoment A p ^ (1 / p)

end CubeShuffle.WeightedSweep

end

noncomputable section
open scoped BigOperators Classical

namespace CubeShuffle.WeightedSweep
open Specht UnitaryFinite



end CubeShuffle.WeightedSweep
end
end OAI


