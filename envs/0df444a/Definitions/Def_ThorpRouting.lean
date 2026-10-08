-- Prove2me | Definitions.Def_ThorpRouting
-- name    : ThorpRouting
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:30.298077+00:00
-- url     : https://prove2.me/theorems/4b698431-be46-4c26-8fd9-75cb30c53934
-- statement:
--   This file contains nine independent blocks that share one hypercube routing model, and each ends in a defined proposition MainStatement asserting the existence of constants (a defined proposition, not an established theorem). Common setup: Card(d) is the set of d-bit strings. For a coin function ξ on Card(d), pairSwitch(ξ) is the involutive permutation of Card(d+1) that XORs the first bit with ξ of the remaining bits. A depth-(d+1) butterfly consists of a coin function on Card(d) and two depth-d butterflies indexed by the first bit; butterflyPerm composes pairSwitch with the lift that applies the chosen child permutation to the tail bits, and decodeButterfly reads a butterfly from a Boolean assignment on the switch index set SwitchIndex(d). palindromePerm on BenesCoins(d) is a butterfly permutation times the inverse of a second, independent one. finiteMean is the uniform average over a finite type, and tupleProbability(P,x,y) is the probability over uniform ω that P(ω) sends every x_i to y_i. For a Young diagram μ, tabloids, the polytabloid and the Specht space are built over ℂ with the column-group alternator; relabelling by a bijection e from Card(d) to the cells of μ gives a unitary representation, sampleOperator averages it over a random permutation, and sweepOperator is this average for the butterfly permutation or, if rev is true, its inverse. Writing k = |μ| minus the first row length, levelScale(n,k) = k(1+log(n/k)), and D for the dimension of the Specht space, the blocks state the following. Adaptive: there are positive constants such that, with h = levelScale(2^d,k) and F = TT* for T = sweepOperator, ‖F‖ ≤ e^{-ch}, trace(F⁴) ≤ e^{-c' log D + Ch}, and ‖T‖ ≤ e^{-c₀(log D + h)}. Casimir: palindromic row moments of order 1+1/64, raised to the power 64/65, are at most e^{C·levelScale(2^d,k)} for k-tuples; for k>0 the averaged palindromic operator K has norm at most e^{-a·levelScale}, and D times the real part of trace(K⁶⁵) is at most e^{C·levelScale}; and for some l>0, a random walk whose steps are a coordinate rotation followed by a pairSwitch, run for l·d steps, has total variation distance to the uniform law on permutations of Card(d) tending to 0 from any starting permutation. Dense: for each density ρ>0 and ε>0 there is c>0 such that, whenever r/2^d = ρ and x is an r-tuple of distinct vertices, the fraction of palindromic coin settings whose palindromeCost plus log₂((2^d)_r/2^{dr}) exceeds r(H(ρ)+entropyCorrection(ρ)+ε) is at most e^{-cr}, where H(ρ) is a supremum over admissible cycle-length laws and allocations. Contact: for 1≤k<2^d, ‖T‖² ≤ min(1,(C*dk/2^d)^{k/2}), T=0 if k=1, and ‖T‖² ≤ C^k(1+d)^{Ck}(k/2^d)^{k/2}. Harmonic: bounds on ‖K‖ in terms of e^{-cL}, the dimension of the Specht space of the diagram with first row removed, and D, together with bounds on tuple moments and traces of a reflected sweep kernel. Smoothing: some power u of the reflected sweep kernel on l-tuples is entrywise at most e^{Cl}/(2^d)_l, with a trace bound e^{C2^d} for full tuples. Tail: for some 1<p≤2, p-th moment density bounds on that kernel hold and ‖T‖² ≤ e^{Ck} times the tail-diagram dimension to the power -(p-1)/p. HighTail: for some b,δ,C>0, the base-2 logarithm of the average of 2^{b·highCost} (the cost above the part from heights below J) is at most Ck·2^{-bJ} for J large, and the base-2 logarithm of the average of 2^{b·palindromeCost} is at most Ck(k/2^d)^δ, with a related bound when the coin bits are partly fixed. SparseSaving: if d^{3/4} ≤ log(2^d/k), then ‖T‖² ≤ e^{Ck}(k/2^d)^{k/4}, and for d large enough, ‖T‖² ≤ (k/2^d)^{k/4}.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThorpRouting.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThorpRouting.lean; bytes 16..97159
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

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

def Butterfly : ℕ → Type
  | 0 => Unit
  | d + 1 => (Card d → Bool) × (Bool → Butterfly d)

def childLift {d : ℕ} (p : Bool → Equiv.Perm (Card d)) : Equiv.Perm (Card (d + 1)) where
  toFun x := Fin.cons (x 0) (p (x 0) (Fin.tail x))
  invFun x := Fin.cons (x 0) ((p (x 0)).symm (Fin.tail x))
  left_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.symm_apply_apply, Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail]

def butterflyPerm : (d : ℕ) → Butterfly d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, b => pairSwitch b.1 * childLift (fun ε => butterflyPerm d (b.2 ε))

def SwitchIndex : ℕ → Type
  | 0 => Empty
  | d + 1 => Sum (Card d) (Bool × SwitchIndex d)

instance (d : ℕ) : Fintype (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih => exact inferInstanceAs (Fintype (Sum (Card d) (Bool × SwitchIndex d)))

instance (d : ℕ) : DecidableEq (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ d ih => exact inferInstanceAs (DecidableEq (Sum (Card d) (Bool × SwitchIndex d)))

def decodeButterfly : (d : ℕ) → (SwitchIndex d → Bool) → Butterfly d
  | 0, _ => ()
  | d + 1, ω => (fun y => ω (Sum.inl y), fun ε =>
      decodeButterfly d (fun i => ω (Sum.inr (ε,i))))

end Thorp

namespace Thorp.Specht
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

noncomputable def delta {μ : YoungDiagram} (f : Tabloid μ) : Tabloid μ → ℂ :=
  fun g => if g=f then 1 else 0

noncomputable def colGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (Cell μ)) where
  carrier := {p | ∀ x, col (p x) = col x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro p q hp hq x; exact (hp (q x)).trans (hq x)
  inv_mem' := by intro p hp x; simpa using (hp (p⁻¹ x)).symm

noncomputable def permSign {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) : ℂ :=
  ((Equiv.Perm.sign p : ℤ) : ℂ)


section
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

noncomputable def alternator (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) : Module.End ℂ V := by
  classical
  exact ∑ c : C, permSign (c : Equiv.Perm α) • ρ c

end

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

end Thorp.Specht

namespace Thorp.PermutationHilbert
open scoped BigOperators ComplexConjugate Classical
open Complex
variable {X : Type*} [Fintype X]

abbrev H (X : Type*) [Fintype X] := EuclideanSpace ℂ X

end Thorp.PermutationHilbert

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def hilbertEquiv (μ : YoungDiagram) :
    (Tabloid μ → ℂ) ≃ₗ[ℂ] PermutationHilbert.H (Tabloid μ) :=
  (WithLp.linearEquiv 2 ℂ (Tabloid μ → ℂ)).symm

noncomputable def hilbertSpace (μ : YoungDiagram) :
    Submodule ℂ (PermutationHilbert.H (Tabloid μ)) := (space μ).map (hilbertEquiv μ).toLinearMap

end Thorp.Specht

namespace Thorp.UnitaryFinite

section
open scoped BigOperators ComplexConjugate Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def continuousRepresentation (ρ : Representation ℂ G V) : G →* (V →L[ℂ] V) where
  toFun g := (ρ g).toContinuousLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

end
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def sampleOperator (ρ : Representation ℂ G V) (P : Ω → G) : V →L[ℂ] V :=
  (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,continuousRepresentation ρ (P ω)

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def spaceHilbertEquiv (μ : YoungDiagram) : space μ ≃ₗ[ℂ] hilbertSpace μ :=
  (hilbertEquiv μ).submoduleMap (space μ)

noncomputable def unitaryRepresentation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (hilbertSpace μ) :=
  ((spaceHilbertEquiv μ).conjAlgEquiv ℂ).toMonoidHom.comp (representation μ)

variable {α ι : Type*} [Fintype α] [Fintype ι]

noncomputable def relabelledUnitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation ℂ (Equiv.Perm α) (hilbertSpace μ) :=
  (unitaryRepresentation μ).comp e.permCongrHom.toMonoidHom

end Thorp.Specht

namespace Thorp.SparseContact
open scoped BigOperators

noncomputable def sweepOperator (d : ℕ) (μ : YoungDiagram)
    (e : Card d ≃ Specht.Cell μ) (reverse : Bool) :
    Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ :=
  UnitaryFinite.sampleOperator (V := Specht.hilbertSpace μ) (Specht.relabelledUnitary μ e)
    (fun ω : SwitchIndex d → Bool => if reverse then
      (butterflyPerm d (decodeButterfly d ω))⁻¹ else butterflyPerm d (decodeButterfly d ω))

end Thorp.SparseContact

namespace Thorp.Casimir
open scoped BigOperators Classical
open Filter

noncomputable def levelScale (n k : ℕ) : ℝ :=
  (k:ℝ) * (1 + Real.log ((n:ℝ)/(k:ℝ)))

end Thorp.Casimir

namespace Thorp.AdaptiveBounds
open scoped BigOperators Classical
open Casimir

noncomputable def positiveSquare {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (T : V →L[ℂ] V) : V →L[ℂ] V :=
  T * T.adjoint

noncomputable def F (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (rev : Bool) : Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ :=
  positiveSquare (V := Specht.hilbertSpace μ) (SparseContact.sweepOperator d μ e rev)

noncomputable def fourthTrace (d : ℕ) (μ : YoungDiagram)
    (e : Card d ≃ Specht.Cell μ) (rev : Bool) : ℝ :=
  (LinearMap.trace ℂ (Specht.hilbertSpace μ) ((F d μ e rev)^4).toLinearMap).re

def MainStatement : Prop :=
  ∃ c c' C c₀ : ℝ, 0<c ∧ 0<c' ∧ 0<C ∧ 0<c₀ ∧
    ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool),
      let h := levelScale (2^d) (μ.card-μ.rowLen 0)
      let D : ℝ := Module.finrank ℂ (Specht.space μ)
      ‖F d μ e rev‖ ≤ Real.exp (-c*h) ∧
      fourthTrace d μ e rev ≤ Real.exp (-c'*Real.log D+C*h) ∧
      ‖SparseContact.sweepOperator d μ e rev‖ ≤ Real.exp (-c₀*(Real.log D+h))

end Thorp.AdaptiveBounds

end ThorpNine.Adaptive


namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

def Coins : ℕ → Type
  | 0 => Unit
  | d + 1 => Card d → Bool

instance (d : ℕ) : Fintype (Coins d) := by
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

noncomputable def law (d t : ℕ) (g : Equiv.Perm (Card d)) : ℝ :=
  (Fintype.card {ω : Fin t → Coins d // run d t ω = g} : ℝ) /
    (Fintype.card (Fin t → Coins d) : ℝ)

def Butterfly : ℕ → Type
  | 0 => Unit
  | d + 1 => (Card d → Bool) × (Bool → Butterfly d)

def childLift {d : ℕ} (p : Bool → Equiv.Perm (Card d)) : Equiv.Perm (Card (d + 1)) where
  toFun x := Fin.cons (x 0) (p (x 0) (Fin.tail x))
  invFun x := Fin.cons (x 0) ((p (x 0)).symm (Fin.tail x))
  left_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.symm_apply_apply, Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail]

def butterflyPerm : (d : ℕ) → Butterfly d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, b => pairSwitch b.1 * childLift (fun ε => butterflyPerm d (b.2 ε))

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

def SwitchIndex : ℕ → Type
  | 0 => Empty
  | d + 1 => Sum (Card d) (Bool × SwitchIndex d)

instance (d : ℕ) : Fintype (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih => exact inferInstanceAs (Fintype (Sum (Card d) (Bool × SwitchIndex d)))

instance (d : ℕ) : DecidableEq (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ d ih => exact inferInstanceAs (DecidableEq (Sum (Card d) (Bool × SwitchIndex d)))

def decodeButterfly : (d : ℕ) → (SwitchIndex d → Bool) → Butterfly d
  | 0, _ => ()
  | d + 1, ω => (fun y => ω (Sum.inl y), fun ε =>
      decodeButterfly d (fun i => ω (Sum.inr (ε,i))))

end Thorp

namespace Thorp.PairRouting
open scoped BigOperators
open Filter
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

noncomputable def tupleProbability {Ω β : Type*} [Fintype Ω] [DecidableEq β]
    (P : Ω → Equiv.Perm β) (x y : ι → β) : ℝ := by
  classical
  exact finiteMean (fun ω => if ∀ i, P ω (x i) = y i then 1 else 0)

end Thorp.PairRouting

namespace Thorp
open scoped BigOperators
open Filter

abbrev BenesCoins (d : ℕ) := (SwitchIndex d → Bool) × (SwitchIndex d → Bool)

def palindromePerm (d : ℕ) (ω : BenesCoins d) : Equiv.Perm (Card d) :=
  butterflyPerm d (decodeButterfly d ω.1) * (butterflyPerm d (decodeButterfly d ω.2)).symm

noncomputable def palindromeRowMoment (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (a : ℝ) : ℝ :=
  finiteMean (fun f : ι ↪ Card d =>
    ((Fintype.card (ι ↪ Card d):ℝ)*PairRouting.tupleProbability (palindromePerm d) e f)^(1+a))

end Thorp

namespace Thorp.Specht
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

noncomputable def delta {μ : YoungDiagram} (f : Tabloid μ) : Tabloid μ → ℂ :=
  fun g => if g=f then 1 else 0

noncomputable def colGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (Cell μ)) where
  carrier := {p | ∀ x, col (p x) = col x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro p q hp hq x; exact (hp (q x)).trans (hq x)
  inv_mem' := by intro p hp x; simpa using (hp (p⁻¹ x)).symm

noncomputable def permSign {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) : ℂ :=
  ((Equiv.Perm.sign p : ℤ) : ℂ)


section
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

noncomputable def alternator (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) : Module.End ℂ V := by
  classical
  exact ∑ c : C, permSign (c : Equiv.Perm α) • ρ c

end

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

end Thorp.Specht

namespace Thorp.PermutationHilbert
open scoped BigOperators ComplexConjugate Classical
open Complex
variable {X : Type*} [Fintype X]

abbrev H (X : Type*) [Fintype X] := EuclideanSpace ℂ X

end Thorp.PermutationHilbert

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def hilbertEquiv (μ : YoungDiagram) :
    (Tabloid μ → ℂ) ≃ₗ[ℂ] PermutationHilbert.H (Tabloid μ) :=
  (WithLp.linearEquiv 2 ℂ (Tabloid μ → ℂ)).symm

noncomputable def hilbertSpace (μ : YoungDiagram) :
    Submodule ℂ (PermutationHilbert.H (Tabloid μ)) := (space μ).map (hilbertEquiv μ).toLinearMap

end Thorp.Specht

namespace Thorp.UnitaryFinite

section
open scoped BigOperators ComplexConjugate Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def continuousRepresentation (ρ : Representation ℂ G V) : G →* (V →L[ℂ] V) where
  toFun g := (ρ g).toContinuousLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

end
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def sampleOperator (ρ : Representation ℂ G V) (P : Ω → G) : V →L[ℂ] V :=
  (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,continuousRepresentation ρ (P ω)

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def spaceHilbertEquiv (μ : YoungDiagram) : space μ ≃ₗ[ℂ] hilbertSpace μ :=
  (hilbertEquiv μ).submoduleMap (space μ)

noncomputable def unitaryRepresentation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (hilbertSpace μ) :=
  ((spaceHilbertEquiv μ).conjAlgEquiv ℂ).toMonoidHom.comp (representation μ)

variable {α ι : Type*} [Fintype α] [Fintype ι]

noncomputable def relabelledUnitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation ℂ (Equiv.Perm α) (hilbertSpace μ) :=
  (unitaryRepresentation μ).comp e.permCongrHom.toMonoidHom

end Thorp.Specht

namespace Thorp.CasimirBounds
open scoped BigOperators Classical
open Filter

noncomputable def levelScale (n k : ℕ) : ℝ :=
  (k:ℝ) * (1 + Real.log ((n:ℝ)/(k:ℝ)))

noncomputable def K (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) :
    Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ :=
  UnitaryFinite.sampleOperator (V := Specht.hilbertSpace μ)
    (Specht.relabelledUnitary μ e) (palindromePerm d)

noncomputable def traceMoment (d : ℕ) (μ : YoungDiagram)
    (e : Card d ≃ Specht.Cell μ) (r : ℕ) : ℝ :=
  (LinearMap.trace ℂ (Specht.hilbertSpace μ) ((K d μ e)^r).toLinearMap).re

noncomputable def fromDistance (d t : ℕ) (σ : Equiv.Perm (Card d)) : ℝ :=
  (1/2:ℝ) * ∑ g : Equiv.Perm (Card d),
    |law d t (g*σ⁻¹) - 1/(Nat.factorial (2^d):ℝ)|

def MainStatement : Prop :=
  ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    (∀ d k : ℕ, 1 ≤ k → k ≤ 2^d → ∀ x : Fin k ↪ Card d,
      (palindromeRowMoment d x (1/64))^(64/65:ℝ) ≤
        Real.exp (C*levelScale (2^d) k)) ∧
    (∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ),
      0 < μ.card-μ.rowLen 0 →
        ‖K d μ e‖ ≤ Real.exp (-a*levelScale (2^d) (μ.card-μ.rowLen 0)) ∧
        (Module.finrank ℂ (Specht.space μ):ℝ) * traceMoment d μ e 65 ≤
          Real.exp (C*levelScale (2^d) (μ.card-μ.rowLen 0))) ∧
    (∃ l : ℕ, 0 < l ∧ ∀ starts : (d : ℕ) → Equiv.Perm (Card d),
      Tendsto (fun d => fromDistance d (l*d) (starts d)) atTop (nhds 0))

end Thorp.CasimirBounds

end ThorpNine.Casimir


namespace ThorpNine.Dense

namespace Thorp
open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

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

def Butterfly : ℕ → Type
  | 0 => Unit
  | d + 1 => (Card d → Bool) × (Bool → Butterfly d)

def childLift {d : ℕ} (p : Bool → Equiv.Perm (Card d)) : Equiv.Perm (Card (d + 1)) where
  toFun x := Fin.cons (x 0) (p (x 0) (Fin.tail x))
  invFun x := Fin.cons (x 0) ((p (x 0)).symm (Fin.tail x))
  left_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.symm_apply_apply, Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail]

def butterflyPerm : (d : ℕ) → Butterfly d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, b => pairSwitch b.1 * childLift (fun ε => butterflyPerm d (b.2 ε))

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

def SwitchIndex : ℕ → Type
  | 0 => Empty
  | d + 1 => Sum (Card d) (Bool × SwitchIndex d)

instance (d : ℕ) : Fintype (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih => exact inferInstanceAs (Fintype (Sum (Card d) (Bool × SwitchIndex d)))

instance (d : ℕ) : DecidableEq (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ d ih => exact inferInstanceAs (DecidableEq (Sum (Card d) (Bool × SwitchIndex d)))

def decodeButterfly : (d : ℕ) → (SwitchIndex d → Bool) → Butterfly d
  | 0, _ => ()
  | d + 1, ω => (fun y => ω (Sum.inl y), fun ε =>
      decodeButterfly d (fun i => ω (Sum.inr (ε,i))))

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def orbitSet (p : Equiv.Perm α) (x : α) : Finset α :=
  Finset.univ.filter (p.SameCycle x)

end Thorp

namespace Thorp.RoutingNetwork
open scoped BigOperators
open Filter
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
variable {A : ℕ}

abbrev SelectedCycle (p : Equiv.Perm (α)) (S : Finset (α)) :=
  {C : Finset (α) // (∃ x, C = orbitSet p x) ∧ C ⊆ S}

noncomputable instance (p : Equiv.Perm (α)) (S : Finset (α)) :
    Fintype (SelectedCycle p S) := Fintype.ofFinite _

end Thorp.RoutingNetwork

namespace Thorp
open scoped BigOperators
open Filter

section
variable {β : Type*} [Fintype β] [DecidableEq β]

def pairLayer (ξ : β → Bool) : Equiv.Perm (Bool × β) where
  toFun x := (Bool.xor x.1 (ξ x.2),x.2)
  invFun x := (Bool.xor x.1 (ξ x.2),x.2)
  left_inv x := by
    rcases x with ⟨b,x⟩
    change (Bool.xor (Bool.xor b (ξ x)) (ξ x),x) = (b,x)
    cases b <;> cases ξ x <;> rfl
  right_inv x := by
    rcases x with ⟨b,x⟩
    change (Bool.xor (Bool.xor b (ξ x)) (ξ x),x) = (b,x)
    cases b <;> cases ξ x <;> rfl

end

def coinStepEquiv (d : ℕ) : (SwitchIndex (d+1) → Bool) ≃
    ((SwitchIndex d → Bool) × (SwitchIndex d → Bool)) × (Card d → Bool) where
  toFun ω := ((fun i => ω (Sum.inr (false,i)),fun i => ω (Sum.inr (true,i))),
    fun x => ω (Sum.inl x))
  invFun ω := Sum.elim ω.2 (fun bi => if bi.1 then ω.1.2 bi.2 else ω.1.1 bi.2)
  left_inv ω := by
    funext i
    cases i with
    | inl x => rfl
    | inr bi => cases bi with | mk b i => cases b <;> rfl
  right_inv ω := by
    rcases ω with ⟨⟨ω₀,ω₁⟩,ξ⟩
    rfl

def headTailEquiv (d : ℕ) : Card (d+1) ≃ Bool × Card d :=
  (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).symm

end Thorp

namespace Thorp.CycleColoring
open scoped BigOperators
open Filter
variable {α : Type*} [Fintype α] [DecidableEq α]

def alternatingPerm (p : Equiv.Perm α) : Equiv.Perm (Bool × α) where
  toFun x := if x.1 then (false,p x.2) else (true,x.2)
  invFun x := if x.1 then (false,x.2) else (true,p.symm x.2)
  left_inv x := by rcases x with ⟨b,x⟩; cases b <;> simp
  right_inv x := by rcases x with ⟨b,x⟩; cases b <;> simp

end Thorp.CycleColoring

namespace Thorp.PairRouting
open scoped BigOperators
open Filter
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

def required (x : ι → Bool × α) (c : ι → Bool) (i : ι) : Bool := Bool.xor (x i).1 (c i)

def Compatible (x : ι → Bool × α) (c : ι → Bool) : Prop :=
  ∀ i j, (x i).2 = (x j).2 → required x c i = required x c j

def colors (x : ι → Bool × α) (ξ : α → Bool) (i : ι) : Bool :=
  Bool.xor (x i).1 (ξ (x i).2)

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma required_colors (x : ι → Bool × α) (ξ : α → Bool) (i : ι) :
    required x (colors x ξ) i = ξ (x i).2 := by
  simp only [required,colors]
  cases (x i).1 <;> cases ξ (x i).2 <;> rfl

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma colors_compatible (x : ι → Bool × α) (ξ : α → Bool) : Compatible x (colors x ξ) := by
  intro i j he
  simp only [required_colors,he]

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma Compatible.tail_injective {x : ι ↪ Bool × α} {c : ι → Bool} (hc : Compatible x c) (b : Bool) :
    Function.Injective (fun i : {i : ι // c i = b} => (x i.val).2) := by
  intro i j he
  apply Subtype.ext
  apply x.injective
  apply Prod.ext
  · have hh := hc i j he
    simp only [required,i.property,j.property] at hh
    cases h₀ : (x i.val).1 <;> cases h₁ : (x j.val).1 <;> cases b <;> simp_all
  · exact he

def childEmbedding (x : ι ↪ Bool × α) (c : ι → Bool) (hc : Compatible x c) (b : Bool) :
    {i : ι // c i = b} ↪ α := ⟨fun i => (x i.val).2,hc.tail_injective b⟩

noncomputable def labelSet (e : ι ↪ Bool × α) : Finset (Bool × α) := Finset.univ.image e

def alternatingProjection (p : Bool → Equiv.Perm α) : Equiv.Perm α := (p false).symm * p true

noncomputable def alternatingCycles (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) : ℕ :=
  Fintype.card (RoutingNetwork.SelectedCycle
    (CycleColoring.alternatingPerm (alternatingProjection p)) (labelSet e))

def switchedEmbedding (e : ι ↪ Bool × α) (ξ : α → Bool) : ι ↪ Bool × α :=
  e.trans (pairLayer ξ).toEmbedding

end Thorp.PairRouting

namespace Thorp
open scoped BigOperators
open Filter

abbrev BenesCoins (d : ℕ) := (SwitchIndex d → Bool) × (SwitchIndex d → Bool)

def palindromePerm (d : ℕ) (ω : BenesCoins d) : Equiv.Perm (Card d) :=
  butterflyPerm d (decodeButterfly d ω.1) * (butterflyPerm d (decodeButterfly d ω.2)).symm

def sandwichShuffle {A B C D E F : Type*} :
    ((A × B) × C) × ((D × E) × F) ≃ ((A × D) × (B × E)) × (F × C) where
  toFun x := (((x.1.1.1,x.2.1.1),(x.1.1.2,x.2.1.2)),(x.2.2,x.1.2))
  invFun x := (((x.1.1.1,x.1.2.1),x.2.2),((x.1.1.2,x.1.2.2),x.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def benesStepEquiv (d : ℕ) : BenesCoins (d+1) ≃
    (BenesCoins d × BenesCoins d) × ((Card d → Bool) × (Card d → Bool)) :=
  (Equiv.prodCongr (coinStepEquiv d) (coinStepEquiv d)).trans sandwichShuffle

noncomputable def palindromeCost : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, ω =>
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) +
        palindromeCost d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeCost d (PairRouting.childEmbedding x c hc true) σ.1.2

end Thorp

namespace Thorp.DenseTruncation
open scoped BigOperators

def AdmissibleCycleLaw (j : ℕ) (p : ℕ → ℝ) : Prop :=
  (∀ l, 0 ≤ p l) ∧ HasSum p 1 ∧
    ∀ l, p l ≤ ((l + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j - 1)

noncomputable def h (j : ℕ) : ℝ :=
  sSup {z : ℝ | ∃ p : ℕ → ℝ, AdmissibleCycleLaw j p ∧
    z = ∑' l : ℕ, p l / ((l + 1 : ℕ) : ℝ)}

def AdmissibleAllocation (ρ : ℝ) (x : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
    (∑' j : ℕ, x j / (2 : ℝ) ^ (j + 1)) ≤ ρ

noncomputable def H (ρ : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ x : ℕ → ℝ, AdmissibleAllocation ρ x ∧
    z = (1 / 2 : ℝ) * ∑' j : ℕ, h (j + 1) * x j}

noncomputable def entropyCorrection (ρ : ℝ) : ℝ :=
  (-ρ - (1 - ρ) * Real.log (1 - ρ)) / (ρ * Real.log 2)

noncomputable def densityExponent (d r : ℕ) (x : Fin r ↪ Card d)
    (ω : BenesCoins d) : ℝ :=
  palindromeCost d x ω +
    Real.log (((2 ^ d).descFactorial r : ℝ) / ((2 : ℝ) ^ d) ^ r) / Real.log 2

def MainStatement : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧ ∀ d r : ℕ, 1 ≤ d → 1 ≤ r →
      (r : ℝ) / (2 : ℝ) ^ d = ρ → ∀ x : Fin r ↪ Card d,
      finiteMean (fun ω : BenesCoins d =>
        if (r : ℝ) * (H ρ + entropyCorrection ρ + ε) < densityExponent d r x ω
        then (1 : ℝ) else 0) ≤ Real.exp (-c * r)

end Thorp.DenseTruncation

end ThorpNine.Dense


namespace ThorpNine.Contact

namespace Thorp
open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

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

def Butterfly : ℕ → Type
  | 0 => Unit
  | d + 1 => (Card d → Bool) × (Bool → Butterfly d)

def childLift {d : ℕ} (p : Bool → Equiv.Perm (Card d)) : Equiv.Perm (Card (d + 1)) where
  toFun x := Fin.cons (x 0) (p (x 0) (Fin.tail x))
  invFun x := Fin.cons (x 0) ((p (x 0)).symm (Fin.tail x))
  left_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.symm_apply_apply, Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail]

def butterflyPerm : (d : ℕ) → Butterfly d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, b => pairSwitch b.1 * childLift (fun ε => butterflyPerm d (b.2 ε))

def SwitchIndex : ℕ → Type
  | 0 => Empty
  | d + 1 => Sum (Card d) (Bool × SwitchIndex d)

instance (d : ℕ) : Fintype (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih => exact inferInstanceAs (Fintype (Sum (Card d) (Bool × SwitchIndex d)))

instance (d : ℕ) : DecidableEq (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ d ih => exact inferInstanceAs (DecidableEq (Sum (Card d) (Bool × SwitchIndex d)))

def decodeButterfly : (d : ℕ) → (SwitchIndex d → Bool) → Butterfly d
  | 0, _ => ()
  | d + 1, ω => (fun y => ω (Sum.inl y), fun ε =>
      decodeButterfly d (fun i => ω (Sum.inr (ε,i))))

end Thorp

namespace Thorp.Specht
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

noncomputable def delta {μ : YoungDiagram} (f : Tabloid μ) : Tabloid μ → ℂ :=
  fun g => if g=f then 1 else 0

noncomputable def colGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (Cell μ)) where
  carrier := {p | ∀ x, col (p x) = col x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro p q hp hq x; exact (hp (q x)).trans (hq x)
  inv_mem' := by intro p hp x; simpa using (hp (p⁻¹ x)).symm

noncomputable def permSign {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) : ℂ :=
  ((Equiv.Perm.sign p : ℤ) : ℂ)


section
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

noncomputable def alternator (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) : Module.End ℂ V := by
  classical
  exact ∑ c : C, permSign (c : Equiv.Perm α) • ρ c

end

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

end Thorp.Specht

namespace Thorp.PermutationHilbert
open scoped BigOperators ComplexConjugate Classical
open Complex
variable {X : Type*} [Fintype X]

abbrev H (X : Type*) [Fintype X] := EuclideanSpace ℂ X

end Thorp.PermutationHilbert

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def hilbertEquiv (μ : YoungDiagram) :
    (Tabloid μ → ℂ) ≃ₗ[ℂ] PermutationHilbert.H (Tabloid μ) :=
  (WithLp.linearEquiv 2 ℂ (Tabloid μ → ℂ)).symm

noncomputable def hilbertSpace (μ : YoungDiagram) :
    Submodule ℂ (PermutationHilbert.H (Tabloid μ)) := (space μ).map (hilbertEquiv μ).toLinearMap

end Thorp.Specht

namespace Thorp.UnitaryFinite

section
open scoped BigOperators ComplexConjugate Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def continuousRepresentation (ρ : Representation ℂ G V) : G →* (V →L[ℂ] V) where
  toFun g := (ρ g).toContinuousLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

end
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def sampleOperator (ρ : Representation ℂ G V) (P : Ω → G) : V →L[ℂ] V :=
  (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,continuousRepresentation ρ (P ω)

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def spaceHilbertEquiv (μ : YoungDiagram) : space μ ≃ₗ[ℂ] hilbertSpace μ :=
  (hilbertEquiv μ).submoduleMap (space μ)

noncomputable def unitaryRepresentation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (hilbertSpace μ) :=
  ((spaceHilbertEquiv μ).conjAlgEquiv ℂ).toMonoidHom.comp (representation μ)

variable {α ι : Type*} [Fintype α] [Fintype ι]

noncomputable def relabelledUnitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation ℂ (Equiv.Perm α) (hilbertSpace μ) :=
  (unitaryRepresentation μ).comp e.permCongrHom.toMonoidHom

end Thorp.Specht

namespace Thorp.SparseContact
open scoped BigOperators

noncomputable def sweepOperator (d : ℕ) (μ : YoungDiagram)
    (e : Card d ≃ Specht.Cell μ) (reverse : Bool) :
    Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ :=
  UnitaryFinite.sampleOperator (V := Specht.hilbertSpace μ) (Specht.relabelledUnitary μ e)
    (fun ω : SwitchIndex d → Bool => if reverse then
      (butterflyPerm d (decodeButterfly d ω))⁻¹ else butterflyPerm d (decodeButterfly d ω))

def MainStatement : Prop :=
  ∃ Cstar C : ℝ, 0 < Cstar ∧ 0 < C ∧
    ∀ (d : ℕ), 1 ≤ d → ∀ (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ),
      let k := μ.card - μ.rowLen 0
      1 ≤ k → k < 2^d → ∀ reverse : Bool,
        ‖sweepOperator d μ e reverse‖^2 ≤
          min 1 ((Cstar * d * k / (2:ℝ)^d) ^ ((k:ℝ)/2)) ∧
        (k = 1 → sweepOperator d μ e reverse = 0) ∧
        ‖sweepOperator d μ e reverse‖^2 ≤
          C^k * (1+(d:ℝ))^(C*k) * ((k:ℝ)/(2:ℝ)^d)^((k:ℝ)/2)

end Thorp.SparseContact

end ThorpNine.Contact


namespace ThorpNine.Harmonic

namespace Thorp
open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

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

def Butterfly : ℕ → Type
  | 0 => Unit
  | d + 1 => (Card d → Bool) × (Bool → Butterfly d)

def childLift {d : ℕ} (p : Bool → Equiv.Perm (Card d)) : Equiv.Perm (Card (d + 1)) where
  toFun x := Fin.cons (x 0) (p (x 0) (Fin.tail x))
  invFun x := Fin.cons (x 0) ((p (x 0)).symm (Fin.tail x))
  left_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.symm_apply_apply, Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail]

def butterflyPerm : (d : ℕ) → Butterfly d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, b => pairSwitch b.1 * childLift (fun ε => butterflyPerm d (b.2 ε))

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

def SwitchIndex : ℕ → Type
  | 0 => Empty
  | d + 1 => Sum (Card d) (Bool × SwitchIndex d)

instance (d : ℕ) : Fintype (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih => exact inferInstanceAs (Fintype (Sum (Card d) (Bool × SwitchIndex d)))

instance (d : ℕ) : DecidableEq (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ d ih => exact inferInstanceAs (DecidableEq (Sum (Card d) (Bool × SwitchIndex d)))

def decodeButterfly : (d : ℕ) → (SwitchIndex d → Bool) → Butterfly d
  | 0, _ => ()
  | d + 1, ω => (fun y => ω (Sum.inl y), fun ε =>
      decodeButterfly d (fun i => ω (Sum.inr (ε,i))))

end Thorp

namespace Thorp.PairRouting
open scoped BigOperators
open Filter
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

noncomputable def tupleProbability {Ω β : Type*} [Fintype Ω] [DecidableEq β]
    (P : Ω → Equiv.Perm β) (x y : ι → β) : ℝ := by
  classical
  exact finiteMean (fun ω => if ∀ i, P ω (x i) = y i then 1 else 0)

end Thorp.PairRouting

namespace Thorp
open scoped BigOperators
open Filter

abbrev BenesCoins (d : ℕ) := (SwitchIndex d → Bool) × (SwitchIndex d → Bool)

def palindromePerm (d : ℕ) (ω : BenesCoins d) : Equiv.Perm (Card d) :=
  butterflyPerm d (decodeButterfly d ω.1) * (butterflyPerm d (decodeButterfly d ω.2)).symm

end Thorp

namespace Thorp.Specht
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

noncomputable def delta {μ : YoungDiagram} (f : Tabloid μ) : Tabloid μ → ℂ :=
  fun g => if g=f then 1 else 0

noncomputable def colGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (Cell μ)) where
  carrier := {p | ∀ x, col (p x) = col x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro p q hp hq x; exact (hp (q x)).trans (hq x)
  inv_mem' := by intro p hp x; simpa using (hp (p⁻¹ x)).symm

noncomputable def permSign {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) : ℂ :=
  ((Equiv.Perm.sign p : ℤ) : ℂ)


section
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

noncomputable def alternator (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) : Module.End ℂ V := by
  classical
  exact ∑ c : C, permSign (c : Equiv.Perm α) • ρ c

end

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

end Thorp.Specht

namespace Thorp.PermutationHilbert
open scoped BigOperators ComplexConjugate Classical
open Complex
variable {X : Type*} [Fintype X]

abbrev H (X : Type*) [Fintype X] := EuclideanSpace ℂ X

end Thorp.PermutationHilbert

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def hilbertEquiv (μ : YoungDiagram) :
    (Tabloid μ → ℂ) ≃ₗ[ℂ] PermutationHilbert.H (Tabloid μ) :=
  (WithLp.linearEquiv 2 ℂ (Tabloid μ → ℂ)).symm

noncomputable def hilbertSpace (μ : YoungDiagram) :
    Submodule ℂ (PermutationHilbert.H (Tabloid μ)) := (space μ).map (hilbertEquiv μ).toLinearMap

end Thorp.Specht

namespace Thorp.UnitaryFinite

section
open scoped BigOperators ComplexConjugate Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def continuousRepresentation (ρ : Representation ℂ G V) : G →* (V →L[ℂ] V) where
  toFun g := (ρ g).toContinuousLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

end
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def sampleOperator (ρ : Representation ℂ G V) (P : Ω → G) : V →L[ℂ] V :=
  (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,continuousRepresentation ρ (P ω)

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def spaceHilbertEquiv (μ : YoungDiagram) : space μ ≃ₗ[ℂ] hilbertSpace μ :=
  (hilbertEquiv μ).submoduleMap (space μ)

noncomputable def unitaryRepresentation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (hilbertSpace μ) :=
  ((spaceHilbertEquiv μ).conjAlgEquiv ℂ).toMonoidHom.comp (representation μ)

variable {α ι : Type*} [Fintype α] [Fintype ι]

noncomputable def relabelledUnitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation ℂ (Equiv.Perm α) (hilbertSpace μ) :=
  (unitaryRepresentation μ).comp e.permCongrHom.toMonoidHom

end Thorp.Specht

namespace Thorp.SparseContact
open scoped BigOperators

noncomputable def sweepOperator (d : ℕ) (μ : YoungDiagram)
    (e : Card d ≃ Specht.Cell μ) (reverse : Bool) :
    Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ :=
  UnitaryFinite.sampleOperator (V := Specht.hilbertSpace μ) (Specht.relabelledUnitary μ e)
    (fun ω : SwitchIndex d → Bool => if reverse then
      (butterflyPerm d (decodeButterfly d ω))⁻¹ else butterflyPerm d (decodeButterfly d ω))

end Thorp.SparseContact

namespace Thorp.StrongSmoothing

def coordinateRelabel (d : ℕ) (order : Equiv.Perm (Fin d)) : Equiv.Perm (Card d) where
  toFun x := fun i => x (order.symm i)
  invFun x := fun i => x (order i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

def sweep (d : ℕ) (order : Equiv.Perm (Fin d)) (ω : SwitchIndex d → Bool) :
    Equiv.Perm (Card d) :=
  coordinateRelabel d order * butterflyPerm d (decodeButterfly d ω) *
    (coordinateRelabel d order)⁻¹

abbrev Tuples (d l : ℕ) := Fin l ↪ Card d

noncomputable def sweepKernel (d l : ℕ) (order : Equiv.Perm (Fin d)) :
    Matrix (Tuples d l) (Tuples d l) ℝ :=
  fun x y => PairRouting.tupleProbability (sweep d order) x y

noncomputable def reflectedKernel (d l : ℕ) (order : Equiv.Perm (Fin d)) (orientation : Bool) :
    Matrix (Tuples d l) (Tuples d l) ℝ :=
  let A := sweepKernel d l order
  if orientation then A * A.transpose else A.transpose * A

end Thorp.StrongSmoothing

namespace Thorp.StrongTail
open scoped BigOperators Classical
open Specht

def tailDiagram (μ : YoungDiagram) : YoungDiagram :=
  YoungDiagram.ofRowLens μ.rowLens.tail μ.rowLens_sorted.pairwise.tail.sortedGE

end Thorp.StrongTail

namespace Thorp.Casimir
open scoped BigOperators Classical
open Filter

noncomputable def levelScale (n k : ℕ) : ℝ :=
  (k:ℝ) * (1 + Real.log ((n:ℝ)/(k:ℝ)))

noncomputable def K (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) :
    Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ :=
  UnitaryFinite.sampleOperator (V := Specht.hilbertSpace μ)
    (Specht.relabelledUnitary μ e) (palindromePerm d)

end Thorp.Casimir

namespace Thorp.HarmonicBounds
open scoped BigOperators Classical
open _root_.OAI.ThorpNine.Harmonic.Thorp.Casimir StrongSmoothing

abbrev tail (μ : YoungDiagram) := StrongTail.tailDiagram μ

noncomputable def W (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) : ℝ := ‖K d μ e‖

noncomputable def tupleTrace (d k : ℕ) (order : Equiv.Perm (Fin d)) (rev : Bool) (p : ℕ) : ℝ :=
  Matrix.trace ((reflectedKernel d k order rev)^p)

def MainStatement : Prop :=
  ∃ c C ζ δ cTail c₁ c₂ : ℝ, ∃ p₀ : ℕ,
    0<c ∧ 0<C ∧ 0<ζ ∧ 0<δ ∧ δ<1 ∧ 0<cTail ∧ 0<c₁ ∧ 0<c₂ ∧ 0<p₀ ∧
    (∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ),
      0<μ.card-μ.rowLen 0 →
      let L := levelScale (2^d) (μ.card-μ.rowLen 0)
      let f : ℝ := Module.finrank ℂ (Specht.space (tail μ))
      let D : ℝ := Module.finrank ℂ (Specht.space μ)
      W d μ e ≤ Real.exp (-c*L) ∧
      W d μ e ≤ Real.exp (C*L)*f^(-ζ) ∧
      (∀ rev : Bool, ‖SparseContact.sweepOperator d μ e rev‖ ≤
        Real.exp (-cTail*(L+Real.log f))) ∧
      W d μ e ≤ Real.exp (-c₁*L)*D^(-c₂)) ∧
    (∀ d k : ℕ, 1≤k → k≤2^d → ∀ (order : Equiv.Perm (Fin d)) (rev : Bool),
      (∀ x : Tuples d k,
        finiteMean (fun y => ((Fintype.card (Tuples d k):ℝ)*
          reflectedKernel d k order rev x y)^(1+δ)) ≤
        Real.exp (C*levelScale (2^d) k)) ∧
      tupleTrace d k order rev p₀ ≤ Real.exp (C*levelScale (2^d) k))

end Thorp.HarmonicBounds

end ThorpNine.Harmonic


namespace ThorpNine.Smoothing

namespace Thorp
open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

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

def Butterfly : ℕ → Type
  | 0 => Unit
  | d + 1 => (Card d → Bool) × (Bool → Butterfly d)

def childLift {d : ℕ} (p : Bool → Equiv.Perm (Card d)) : Equiv.Perm (Card (d + 1)) where
  toFun x := Fin.cons (x 0) (p (x 0) (Fin.tail x))
  invFun x := Fin.cons (x 0) ((p (x 0)).symm (Fin.tail x))
  left_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.symm_apply_apply, Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail]

def butterflyPerm : (d : ℕ) → Butterfly d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, b => pairSwitch b.1 * childLift (fun ε => butterflyPerm d (b.2 ε))

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

def SwitchIndex : ℕ → Type
  | 0 => Empty
  | d + 1 => Sum (Card d) (Bool × SwitchIndex d)

instance (d : ℕ) : Fintype (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih => exact inferInstanceAs (Fintype (Sum (Card d) (Bool × SwitchIndex d)))

instance (d : ℕ) : DecidableEq (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ d ih => exact inferInstanceAs (DecidableEq (Sum (Card d) (Bool × SwitchIndex d)))

def decodeButterfly : (d : ℕ) → (SwitchIndex d → Bool) → Butterfly d
  | 0, _ => ()
  | d + 1, ω => (fun y => ω (Sum.inl y), fun ε =>
      decodeButterfly d (fun i => ω (Sum.inr (ε,i))))

end Thorp

namespace Thorp.PairRouting
open scoped BigOperators
open Filter
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

noncomputable def tupleProbability {Ω β : Type*} [Fintype Ω] [DecidableEq β]
    (P : Ω → Equiv.Perm β) (x y : ι → β) : ℝ := by
  classical
  exact finiteMean (fun ω => if ∀ i, P ω (x i) = y i then 1 else 0)

end Thorp.PairRouting

namespace Thorp.StrongSmoothing

def coordinateRelabel (d : ℕ) (order : Equiv.Perm (Fin d)) : Equiv.Perm (Card d) where
  toFun x := fun i => x (order.symm i)
  invFun x := fun i => x (order i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

def sweep (d : ℕ) (order : Equiv.Perm (Fin d)) (ω : SwitchIndex d → Bool) :
    Equiv.Perm (Card d) :=
  coordinateRelabel d order * butterflyPerm d (decodeButterfly d ω) *
    (coordinateRelabel d order)⁻¹

abbrev Tuples (d l : ℕ) := Fin l ↪ Card d

noncomputable def sweepKernel (d l : ℕ) (order : Equiv.Perm (Fin d)) :
    Matrix (Tuples d l) (Tuples d l) ℝ :=
  fun x y => PairRouting.tupleProbability (sweep d order) x y

noncomputable def reflectedKernel (d l : ℕ) (order : Equiv.Perm (Fin d)) (orientation : Bool) :
    Matrix (Tuples d l) (Tuples d l) ℝ :=
  let A := sweepKernel d l order
  if orientation then A * A.transpose else A.transpose * A

noncomputable def regularAbsoluteEvenTrace (d : ℕ) (order : Equiv.Perm (Fin d)) (u : ℕ) : ℝ :=
  Matrix.trace ((reflectedKernel d (2^d) order false)^u)

def MainStatement : Prop :=
  ∃ u : ℕ, 1 ≤ u ∧ ∃ C : ℝ,
    (∀ d l : ℕ, l ≤ 2^d → ∀ order : Equiv.Perm (Fin d), ∀ orientation : Bool,
      ∀ x y : Tuples d l,
        ((reflectedKernel d l order orientation)^u) x y ≤
          Real.exp (C*l)/((2^d).descFactorial l:ℝ)) ∧
    (∀ d : ℕ, ∀ order : Equiv.Perm (Fin d),
      regularAbsoluteEvenTrace d order u ≤ Real.exp (C*(2:ℝ)^d))

end Thorp.StrongSmoothing

end ThorpNine.Smoothing


namespace ThorpNine.Tail

namespace Thorp
open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

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

def Butterfly : ℕ → Type
  | 0 => Unit
  | d + 1 => (Card d → Bool) × (Bool → Butterfly d)

def childLift {d : ℕ} (p : Bool → Equiv.Perm (Card d)) : Equiv.Perm (Card (d + 1)) where
  toFun x := Fin.cons (x 0) (p (x 0) (Fin.tail x))
  invFun x := Fin.cons (x 0) ((p (x 0)).symm (Fin.tail x))
  left_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.symm_apply_apply, Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail]

def butterflyPerm : (d : ℕ) → Butterfly d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, b => pairSwitch b.1 * childLift (fun ε => butterflyPerm d (b.2 ε))

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

def SwitchIndex : ℕ → Type
  | 0 => Empty
  | d + 1 => Sum (Card d) (Bool × SwitchIndex d)

instance (d : ℕ) : Fintype (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih => exact inferInstanceAs (Fintype (Sum (Card d) (Bool × SwitchIndex d)))

instance (d : ℕ) : DecidableEq (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ d ih => exact inferInstanceAs (DecidableEq (Sum (Card d) (Bool × SwitchIndex d)))

def decodeButterfly : (d : ℕ) → (SwitchIndex d → Bool) → Butterfly d
  | 0, _ => ()
  | d + 1, ω => (fun y => ω (Sum.inl y), fun ε =>
      decodeButterfly d (fun i => ω (Sum.inr (ε,i))))

end Thorp

namespace Thorp.PairRouting
open scoped BigOperators
open Filter
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

noncomputable def tupleProbability {Ω β : Type*} [Fintype Ω] [DecidableEq β]
    (P : Ω → Equiv.Perm β) (x y : ι → β) : ℝ := by
  classical
  exact finiteMean (fun ω => if ∀ i, P ω (x i) = y i then 1 else 0)

end Thorp.PairRouting

namespace Thorp.Specht
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

noncomputable def delta {μ : YoungDiagram} (f : Tabloid μ) : Tabloid μ → ℂ :=
  fun g => if g=f then 1 else 0

noncomputable def colGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (Cell μ)) where
  carrier := {p | ∀ x, col (p x) = col x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro p q hp hq x; exact (hp (q x)).trans (hq x)
  inv_mem' := by intro p hp x; simpa using (hp (p⁻¹ x)).symm

noncomputable def permSign {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) : ℂ :=
  ((Equiv.Perm.sign p : ℤ) : ℂ)


section
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

noncomputable def alternator (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) : Module.End ℂ V := by
  classical
  exact ∑ c : C, permSign (c : Equiv.Perm α) • ρ c

end

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

end Thorp.Specht

namespace Thorp.PermutationHilbert
open scoped BigOperators ComplexConjugate Classical
open Complex
variable {X : Type*} [Fintype X]

abbrev H (X : Type*) [Fintype X] := EuclideanSpace ℂ X

end Thorp.PermutationHilbert

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def hilbertEquiv (μ : YoungDiagram) :
    (Tabloid μ → ℂ) ≃ₗ[ℂ] PermutationHilbert.H (Tabloid μ) :=
  (WithLp.linearEquiv 2 ℂ (Tabloid μ → ℂ)).symm

noncomputable def hilbertSpace (μ : YoungDiagram) :
    Submodule ℂ (PermutationHilbert.H (Tabloid μ)) := (space μ).map (hilbertEquiv μ).toLinearMap

end Thorp.Specht

namespace Thorp.UnitaryFinite

section
open scoped BigOperators ComplexConjugate Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def continuousRepresentation (ρ : Representation ℂ G V) : G →* (V →L[ℂ] V) where
  toFun g := (ρ g).toContinuousLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

end
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def sampleOperator (ρ : Representation ℂ G V) (P : Ω → G) : V →L[ℂ] V :=
  (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,continuousRepresentation ρ (P ω)

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def spaceHilbertEquiv (μ : YoungDiagram) : space μ ≃ₗ[ℂ] hilbertSpace μ :=
  (hilbertEquiv μ).submoduleMap (space μ)

noncomputable def unitaryRepresentation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (hilbertSpace μ) :=
  ((spaceHilbertEquiv μ).conjAlgEquiv ℂ).toMonoidHom.comp (representation μ)

variable {α ι : Type*} [Fintype α] [Fintype ι]

noncomputable def relabelledUnitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation ℂ (Equiv.Perm α) (hilbertSpace μ) :=
  (unitaryRepresentation μ).comp e.permCongrHom.toMonoidHom

end Thorp.Specht

namespace Thorp.SparseContact
open scoped BigOperators

noncomputable def sweepOperator (d : ℕ) (μ : YoungDiagram)
    (e : Card d ≃ Specht.Cell μ) (reverse : Bool) :
    Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ :=
  UnitaryFinite.sampleOperator (V := Specht.hilbertSpace μ) (Specht.relabelledUnitary μ e)
    (fun ω : SwitchIndex d → Bool => if reverse then
      (butterflyPerm d (decodeButterfly d ω))⁻¹ else butterflyPerm d (decodeButterfly d ω))

end Thorp.SparseContact

namespace Thorp.StrongSmoothing

def coordinateRelabel (d : ℕ) (order : Equiv.Perm (Fin d)) : Equiv.Perm (Card d) where
  toFun x := fun i => x (order.symm i)
  invFun x := fun i => x (order i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

def sweep (d : ℕ) (order : Equiv.Perm (Fin d)) (ω : SwitchIndex d → Bool) :
    Equiv.Perm (Card d) :=
  coordinateRelabel d order * butterflyPerm d (decodeButterfly d ω) *
    (coordinateRelabel d order)⁻¹

abbrev Tuples (d l : ℕ) := Fin l ↪ Card d

noncomputable def sweepKernel (d l : ℕ) (order : Equiv.Perm (Fin d)) :
    Matrix (Tuples d l) (Tuples d l) ℝ :=
  fun x y => PairRouting.tupleProbability (sweep d order) x y

noncomputable def reflectedKernel (d l : ℕ) (order : Equiv.Perm (Fin d)) (orientation : Bool) :
    Matrix (Tuples d l) (Tuples d l) ℝ :=
  let A := sweepKernel d l order
  if orientation then A * A.transpose else A.transpose * A

end Thorp.StrongSmoothing

namespace Thorp.StrongTail
open scoped BigOperators Classical
open Specht

def tailDiagram (μ : YoungDiagram) : YoungDiagram :=
  YoungDiagram.ofRowLens μ.rowLens.tail μ.rowLens_sorted.pairwise.tail.sortedGE

end Thorp.StrongTail

namespace Thorp.StrongTail
open scoped BigOperators Classical
open StrongSmoothing

def DensityAt (p C : ℝ) : Prop :=
  ∀ (d l : ℕ), l ≤ 2^d → ∀ (order : Equiv.Perm (Fin d)) (rev : Bool)
    (x : StrongSmoothing.Tuples d l),
    let H := StrongSmoothing.reflectedKernel d l order rev
    (Thorp.finiteMean (fun y => ((Fintype.card (StrongSmoothing.Tuples d l):ℝ)*H x y)^p)
      ≤ Real.exp (C*l)) ∧
    (Thorp.finiteMean (fun y => ((Fintype.card (StrongSmoothing.Tuples d l):ℝ)*H y x)^p)
      ≤ Real.exp (C*l)) ∧
    (((2:ℝ)^d)^l)⁻¹ * (∑ y, ((((2:ℝ)^d)^l)*H x y)^p) ≤ Real.exp (C*l) ∧
    (((2:ℝ)^d)^l)⁻¹ * (∑ y, ((((2:ℝ)^d)^l)*H y x)^p) ≤ Real.exp (C*l)

end Thorp.StrongTail

namespace Thorp.StrongTail
open scoped BigOperators Classical
open Specht UnitaryFinite

def MainStatement : Prop :=
  ∃ p Cdensity C : ℝ, 1 < p ∧ p ≤ 2 ∧ DensityAt p Cdensity ∧
    ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool),
      ‖SparseContact.sweepOperator d μ e rev‖^2 ≤
       Real.exp (C*(μ.card-μ.rowLen 0 : ℕ)) *
       (Module.finrank ℂ (Specht.space (tailDiagram μ)):ℝ)^(-((p-1)/p))

end Thorp.StrongTail

end ThorpNine.Tail


namespace ThorpNine.HighTail

namespace Thorp
open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

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

def Butterfly : ℕ → Type
  | 0 => Unit
  | d + 1 => (Card d → Bool) × (Bool → Butterfly d)

def childLift {d : ℕ} (p : Bool → Equiv.Perm (Card d)) : Equiv.Perm (Card (d + 1)) where
  toFun x := Fin.cons (x 0) (p (x 0) (Fin.tail x))
  invFun x := Fin.cons (x 0) ((p (x 0)).symm (Fin.tail x))
  left_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.symm_apply_apply, Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail]

def butterflyPerm : (d : ℕ) → Butterfly d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, b => pairSwitch b.1 * childLift (fun ε => butterflyPerm d (b.2 ε))

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

def SwitchIndex : ℕ → Type
  | 0 => Empty
  | d + 1 => Sum (Card d) (Bool × SwitchIndex d)

instance (d : ℕ) : Fintype (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih => exact inferInstanceAs (Fintype (Sum (Card d) (Bool × SwitchIndex d)))

instance (d : ℕ) : DecidableEq (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ d ih => exact inferInstanceAs (DecidableEq (Sum (Card d) (Bool × SwitchIndex d)))

def decodeButterfly : (d : ℕ) → (SwitchIndex d → Bool) → Butterfly d
  | 0, _ => ()
  | d + 1, ω => (fun y => ω (Sum.inl y), fun ε =>
      decodeButterfly d (fun i => ω (Sum.inr (ε,i))))

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def orbitSet (p : Equiv.Perm α) (x : α) : Finset α :=
  Finset.univ.filter (p.SameCycle x)

end Thorp

namespace Thorp.RoutingNetwork
open scoped BigOperators
open Filter
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
variable {A : ℕ}

abbrev SelectedCycle (p : Equiv.Perm (α)) (S : Finset (α)) :=
  {C : Finset (α) // (∃ x, C = orbitSet p x) ∧ C ⊆ S}

noncomputable instance (p : Equiv.Perm (α)) (S : Finset (α)) :
    Fintype (SelectedCycle p S) := Fintype.ofFinite _

end Thorp.RoutingNetwork

namespace Thorp
open scoped BigOperators
open Filter

def cardSplit : (r s : ℕ) → Card (s+r) ≃ Card r × Card s
  | 0, s =>
    { toFun := fun x => ((fun i => Fin.elim0 i), x)
      invFun := fun x => x.2
      left_inv := fun _ => rfl
      right_inv := fun x => by
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl }
  | r+1, s =>
    { toFun := fun x => (Fin.cons (x 0) ((cardSplit r s (Fin.tail x)).1),
        (cardSplit r s (Fin.tail x)).2)
      invFun := fun x => Fin.cons (x.1 0) ((cardSplit r s).symm (Fin.tail x.1,x.2))
      left_inv := by
        intro x
        simp only [Fin.cons_zero, Fin.tail_cons, Prod.mk.eta, Equiv.symm_apply_apply, Fin.cons_self_tail]
      right_inv := by
        intro x
        simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail] }

def assembleBits : (r s : ℕ) → (Card r × SwitchIndex s → Bool) →
    (Card s × SwitchIndex r → Bool) → SwitchIndex (s+r) → Bool
  | 0, _, lo, _, i => lo ((fun j => Fin.elim0 j), i)
  | r+1, s, _, hi, Sum.inl y => hi ((cardSplit r s y).2,Sum.inl (cardSplit r s y).1)
  | r+1, s, lo, hi, Sum.inr (b,i) => assembleBits r s
      (fun j => lo (Fin.cons b j.1,j.2)) (fun j => hi (j.1,Sum.inr (b,j.2))) i


section
variable {β : Type*} [Fintype β] [DecidableEq β]

def pairLayer (ξ : β → Bool) : Equiv.Perm (Bool × β) where
  toFun x := (Bool.xor x.1 (ξ x.2),x.2)
  invFun x := (Bool.xor x.1 (ξ x.2),x.2)
  left_inv x := by
    rcases x with ⟨b,x⟩
    change (Bool.xor (Bool.xor b (ξ x)) (ξ x),x) = (b,x)
    cases b <;> cases ξ x <;> rfl
  right_inv x := by
    rcases x with ⟨b,x⟩
    change (Bool.xor (Bool.xor b (ξ x)) (ξ x),x) = (b,x)
    cases b <;> cases ξ x <;> rfl

end

def coinStepEquiv (d : ℕ) : (SwitchIndex (d+1) → Bool) ≃
    ((SwitchIndex d → Bool) × (SwitchIndex d → Bool)) × (Card d → Bool) where
  toFun ω := ((fun i => ω (Sum.inr (false,i)),fun i => ω (Sum.inr (true,i))),
    fun x => ω (Sum.inl x))
  invFun ω := Sum.elim ω.2 (fun bi => if bi.1 then ω.1.2 bi.2 else ω.1.1 bi.2)
  left_inv ω := by
    funext i
    cases i with
    | inl x => rfl
    | inr bi => cases bi with | mk b i => cases b <;> rfl
  right_inv ω := by
    rcases ω with ⟨⟨ω₀,ω₁⟩,ξ⟩
    rfl

def headTailEquiv (d : ℕ) : Card (d+1) ≃ Bool × Card d :=
  (Fin.consEquiv (fun _ : Fin (d+1) => Bool)).symm

end Thorp

namespace Thorp.CycleColoring
open scoped BigOperators
open Filter
variable {α : Type*} [Fintype α] [DecidableEq α]

def alternatingPerm (p : Equiv.Perm α) : Equiv.Perm (Bool × α) where
  toFun x := if x.1 then (false,p x.2) else (true,x.2)
  invFun x := if x.1 then (false,x.2) else (true,p.symm x.2)
  left_inv x := by rcases x with ⟨b,x⟩; cases b <;> simp
  right_inv x := by rcases x with ⟨b,x⟩; cases b <;> simp

end Thorp.CycleColoring

namespace Thorp.PairRouting
open scoped BigOperators
open Filter
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

def required (x : ι → Bool × α) (c : ι → Bool) (i : ι) : Bool := Bool.xor (x i).1 (c i)

def Compatible (x : ι → Bool × α) (c : ι → Bool) : Prop :=
  ∀ i j, (x i).2 = (x j).2 → required x c i = required x c j

def colors (x : ι → Bool × α) (ξ : α → Bool) (i : ι) : Bool :=
  Bool.xor (x i).1 (ξ (x i).2)

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma required_colors (x : ι → Bool × α) (ξ : α → Bool) (i : ι) :
    required x (colors x ξ) i = ξ (x i).2 := by
  simp only [required,colors]
  cases (x i).1 <;> cases ξ (x i).2 <;> rfl

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma colors_compatible (x : ι → Bool × α) (ξ : α → Bool) : Compatible x (colors x ξ) := by
  intro i j he
  simp only [required_colors,he]

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma Compatible.tail_injective {x : ι ↪ Bool × α} {c : ι → Bool} (hc : Compatible x c) (b : Bool) :
    Function.Injective (fun i : {i : ι // c i = b} => (x i.val).2) := by
  intro i j he
  apply Subtype.ext
  apply x.injective
  apply Prod.ext
  · have hh := hc i j he
    simp only [required,i.property,j.property] at hh
    cases h₀ : (x i.val).1 <;> cases h₁ : (x j.val).1 <;> cases b <;> simp_all
  · exact he

def childEmbedding (x : ι ↪ Bool × α) (c : ι → Bool) (hc : Compatible x c) (b : Bool) :
    {i : ι // c i = b} ↪ α := ⟨fun i => (x i.val).2,hc.tail_injective b⟩

noncomputable def labelSet (e : ι ↪ Bool × α) : Finset (Bool × α) := Finset.univ.image e

def alternatingProjection (p : Bool → Equiv.Perm α) : Equiv.Perm α := (p false).symm * p true

noncomputable def alternatingCycles (e : ι ↪ Bool × α) (p : Bool → Equiv.Perm α) : ℕ :=
  Fintype.card (RoutingNetwork.SelectedCycle
    (CycleColoring.alternatingPerm (alternatingProjection p)) (labelSet e))

def switchedEmbedding (e : ι ↪ Bool × α) (ξ : α → Bool) : ι ↪ Bool × α :=
  e.trans (pairLayer ξ).toEmbedding

end Thorp.PairRouting

namespace Thorp

section
open scoped BigOperators
open Filter

abbrev BenesCoins (d : ℕ) := (SwitchIndex d → Bool) × (SwitchIndex d → Bool)

def palindromePerm (d : ℕ) (ω : BenesCoins d) : Equiv.Perm (Card d) :=
  butterflyPerm d (decodeButterfly d ω.1) * (butterflyPerm d (decodeButterfly d ω.2)).symm

def sandwichShuffle {A B C D E F : Type*} :
    ((A × B) × C) × ((D × E) × F) ≃ ((A × D) × (B × E)) × (F × C) where
  toFun x := (((x.1.1.1,x.2.1.1),(x.1.1.2,x.2.1.2)),(x.2.2,x.1.2))
  invFun x := (((x.1.1.1,x.1.2.1),x.2.2),((x.1.1.2,x.1.2.2),x.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def benesStepEquiv (d : ℕ) : BenesCoins (d+1) ≃
    (BenesCoins d × BenesCoins d) × ((Card d → Bool) × (Card d → Bool)) :=
  (Equiv.prodCongr (coinStepEquiv d) (coinStepEquiv d)).trans sandwichShuffle

noncomputable def palindromeCost : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, ω =>
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) +
        palindromeCost d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeCost d (PairRouting.childEmbedding x c hc true) σ.1.2

end

noncomputable def palindromeLowCost (H : ℕ) : (d : ℕ) → {ι : Type*} → [Fintype ι] →
    (ι ↪ Card d) → BenesCoins d → ℕ
  | 0, _, _, _, _ => 0
  | d+1, _, _, e, ω =>
      let σ := benesStepEquiv d ω
      let x := e.trans (headTailEquiv d).toEmbedding
      let c := PairRouting.colors x σ.2.1
      let hc := PairRouting.colors_compatible x σ.2.1
      (if d+1 ≤ H then PairRouting.alternatingCycles (PairRouting.switchedEmbedding x σ.2.1)
          (fun b => palindromePerm d (if b then σ.1.2 else σ.1.1)) else 0) +
        palindromeLowCost H d (PairRouting.childEmbedding x c hc false) σ.1.1 +
        palindromeLowCost H d (PairRouting.childEmbedding x c hc true) σ.1.2

end Thorp

namespace Thorp.HighHeight
open scoped BigOperators Classical

noncomputable def highCost (J d : ℕ) {ι : Type*} [Fintype ι]
    (x : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  palindromeCost d x ω-palindromeLowCost (J-1) d x ω

def MainStatement : Prop :=
  ∃ b δ C : ℝ, 0<b ∧ 0<δ ∧ 0<C ∧ ∃ J₀ : ℕ, 1≤J₀ ∧
    (∀ d k : ℕ, ∀ x : Fin k ↪ Card d, ∀ J : ℕ, J₀≤J →
      Real.log (finiteMean (fun ω : BenesCoins d => ((2:ℝ)^b)^(highCost J d x ω)))/Real.log 2 ≤
        C*k*(2:ℝ)^(-b*J)) ∧
    (∀ d k : ℕ, ∀ x : Fin k ↪ Card d,
      Real.log (finiteMean (fun ω : BenesCoins d => ((2:ℝ)^b)^(palindromeCost d x ω)))/Real.log 2 ≤
        C*k*((k:ℝ)/(2:ℝ)^d)^δ) ∧
    (∀ r s k : ℕ, ∀ x : Fin k ↪ Card (s+r), ∀ J : ℕ, J₀≤J → 2*s<J →
      ∀ (X : SwitchIndex (s+r) → Bool) (lo : Card r × SwitchIndex s → Bool),
      Real.log (finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
        ((2:ℝ)^b)^(highCost J (s+r) x (assembleBits r s lo hi,X))))/Real.log 2 ≤
          C*k*(2:ℝ)^(-b*J))

end Thorp.HighHeight

end ThorpNine.HighTail


namespace ThorpNine.SparseSaving

namespace Thorp
open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

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

def Butterfly : ℕ → Type
  | 0 => Unit
  | d + 1 => (Card d → Bool) × (Bool → Butterfly d)

def childLift {d : ℕ} (p : Bool → Equiv.Perm (Card d)) : Equiv.Perm (Card (d + 1)) where
  toFun x := Fin.cons (x 0) (p (x 0) (Fin.tail x))
  invFun x := Fin.cons (x 0) ((p (x 0)).symm (Fin.tail x))
  left_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.symm_apply_apply, Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail]

def butterflyPerm : (d : ℕ) → Butterfly d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, b => pairSwitch b.1 * childLift (fun ε => butterflyPerm d (b.2 ε))

def SwitchIndex : ℕ → Type
  | 0 => Empty
  | d + 1 => Sum (Card d) (Bool × SwitchIndex d)

instance (d : ℕ) : Fintype (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih => exact inferInstanceAs (Fintype (Sum (Card d) (Bool × SwitchIndex d)))

instance (d : ℕ) : DecidableEq (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ d ih => exact inferInstanceAs (DecidableEq (Sum (Card d) (Bool × SwitchIndex d)))

def decodeButterfly : (d : ℕ) → (SwitchIndex d → Bool) → Butterfly d
  | 0, _ => ()
  | d + 1, ω => (fun y => ω (Sum.inl y), fun ε =>
      decodeButterfly d (fun i => ω (Sum.inr (ε,i))))

end Thorp

namespace Thorp.Specht
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

noncomputable def delta {μ : YoungDiagram} (f : Tabloid μ) : Tabloid μ → ℂ :=
  fun g => if g=f then 1 else 0

noncomputable def colGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (Cell μ)) where
  carrier := {p | ∀ x, col (p x) = col x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro p q hp hq x; exact (hp (q x)).trans (hq x)
  inv_mem' := by intro p hp x; simpa using (hp (p⁻¹ x)).symm

noncomputable def permSign {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) : ℂ :=
  ((Equiv.Perm.sign p : ℤ) : ℂ)


section
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

noncomputable def alternator (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) : Module.End ℂ V := by
  classical
  exact ∑ c : C, permSign (c : Equiv.Perm α) • ρ c

end

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

end Thorp.Specht

namespace Thorp.PermutationHilbert
open scoped BigOperators ComplexConjugate Classical
open Complex
variable {X : Type*} [Fintype X]

abbrev H (X : Type*) [Fintype X] := EuclideanSpace ℂ X

end Thorp.PermutationHilbert

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def hilbertEquiv (μ : YoungDiagram) :
    (Tabloid μ → ℂ) ≃ₗ[ℂ] PermutationHilbert.H (Tabloid μ) :=
  (WithLp.linearEquiv 2 ℂ (Tabloid μ → ℂ)).symm

noncomputable def hilbertSpace (μ : YoungDiagram) :
    Submodule ℂ (PermutationHilbert.H (Tabloid μ)) := (space μ).map (hilbertEquiv μ).toLinearMap

end Thorp.Specht

namespace Thorp.UnitaryFinite

section
open scoped BigOperators ComplexConjugate Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def continuousRepresentation (ρ : Representation ℂ G V) : G →* (V →L[ℂ] V) where
  toFun g := (ρ g).toContinuousLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

end
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def sampleOperator (ρ : Representation ℂ G V) (P : Ω → G) : V →L[ℂ] V :=
  (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,continuousRepresentation ρ (P ω)

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def spaceHilbertEquiv (μ : YoungDiagram) : space μ ≃ₗ[ℂ] hilbertSpace μ :=
  (hilbertEquiv μ).submoduleMap (space μ)

noncomputable def unitaryRepresentation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (hilbertSpace μ) :=
  ((spaceHilbertEquiv μ).conjAlgEquiv ℂ).toMonoidHom.comp (representation μ)

variable {α ι : Type*} [Fintype α] [Fintype ι]

noncomputable def relabelledUnitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation ℂ (Equiv.Perm α) (hilbertSpace μ) :=
  (unitaryRepresentation μ).comp e.permCongrHom.toMonoidHom

end Thorp.Specht

namespace Thorp.SparseContact
open scoped BigOperators

noncomputable def sweepOperator (d : ℕ) (μ : YoungDiagram)
    (e : Card d ≃ Specht.Cell μ) (reverse : Bool) :
    Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ :=
  UnitaryFinite.sampleOperator (V := Specht.hilbertSpace μ) (Specht.relabelledUnitary μ e)
    (fun ω : SwitchIndex d → Bool => if reverse then
      (butterflyPerm d (decodeButterfly d ω))⁻¹ else butterflyPerm d (decodeButterfly d ω))

end Thorp.SparseContact

namespace Thorp.SparseRegime

def MainStatement : Prop :=
  ∃ (C : ℝ) (d₀ : ℕ), 0 < C ∧ 0 < d₀ ∧
    ∀ (d : ℕ) (μ : YoungDiagram) (e : Thorp.Card d ≃ Thorp.Specht.Cell μ),
      let k := μ.card - μ.rowLen 0
      1 ≤ k → k < 2^d → (d:ℝ)^((3:ℝ)/4) ≤ Real.log ((2:ℝ)^d/k) →
      ∀ rev : Bool,
        ‖Thorp.SparseContact.sweepOperator d μ e rev‖^2 ≤
          Real.exp (C*k)*((k:ℝ)/(2:ℝ)^d)^((k:ℝ)/4) ∧
        (d₀ ≤ d → ‖Thorp.SparseContact.sweepOperator d μ e rev‖^2 ≤
          ((k:ℝ)/(2:ℝ)^d)^((k:ℝ)/4))

end Thorp.SparseRegime

end ThorpNine.SparseSaving



end OAI


