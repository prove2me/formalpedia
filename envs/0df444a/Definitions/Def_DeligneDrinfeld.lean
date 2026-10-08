-- Prove2me | Definitions.Def_DeligneDrinfeld
-- name    : DeligneDrinfeld
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:07.343539+00:00
-- url     : https://prove2.me/theorems/e3945b57-957e-4bf8-81bb-1e9d94055b8a
-- statement:
--   Let L be the free Lie algebra over ℚ on x and y, and write p(a,b) for substitution into a Lie polynomial p. The four-strand infinitesimal braid algebra T₄ is the free Lie algebra on symmetric chords tᵢⱼ, with tᵢᵢ=0, modulo [tᵢⱼ,tₖₗ]=0 for four distinct indices and [tᵢⱼ,tᵢₖ+tⱼₖ]=0 for three distinct indices, all indexed by 0,1,2,3. The solution space W is the rational vector subspace of L consisting of p satisfying p(x,y)+p(y,x)=0, p(x,y)+p(y,−x−y)+p(−x−y,x)=0, and the pentagon identity p(t₀₁,t₁₂+t₁₃)+p(t₀₂+t₁₂,t₂₃)=p(t₁₂,t₂₃)+p(t₀₁+t₀₂,t₁₃+t₂₃)+p(t₀₁,t₁₂) in T₄; closure under vector-space operations is established. The tangent Lie algebra consists of pairs (a,u) in L×L with bracket [(a,u),(b,v)]=([a,b],[u,b]+[a,v]). Substituting (x,0) and (y,[y,p]) into q and taking its second component defines Dₚq, and the Ihara operation is {p,q}=Dₚq−D_qp+[p,q]. For any natural-number weights on free generators, a weighted Lie word is a generator or an iterated bracket, with bracket weights added; the weight-n piece is the rational span of words of weight n. Give x and y weight 1, obtaining Lₙ, and put Wₙ=W∩Lₙ. Let F be the free rational Lie algebra on generators indexed by k≥0, with generator k of weight 2k+3, and let Fₙ be its weight-n piece. A linear equivalence e:F→W is graded when e(a) belongs to Lₙ exactly when a belongs to Fₙ, for every n and a. The completions are the products ∏ₙFₙ and ∏ₙWₙ, with the factor topologies induced from discrete free Lie algebras. A graded e and its inverse act componentwise on these products. MainStatement is the defined proposition that such a graded e exists, carries the free Lie bracket to the Ihara operation, and induces mutually inverse continuous maps between the completions. It additionally requires preservation of the completed bracket degree by degree: for every completed a,b and n≥0, e(Σᵢ₌₀ⁿ[aᵢ,bₙ₋ᵢ])=Σᵢ₌₀ⁿ{e(aᵢ),e(bₙ₋ᵢ)}.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DeligneDrinfeld.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DeligneDrinfeld.lean; bytes 16..7213
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
namespace DeligneDrinfeld

abbrev L := FreeLieAlgebra ℚ Bool
def x : L := FreeLieAlgebra.of ℚ false
def y : L := FreeLieAlgebra.of ℚ true

def eval {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) : L →ₗ⁅ℚ⁆ M :=
  FreeLieAlgebra.lift ℚ (fun i => if i then b else a)

abbrev Edge := {p : Fin 4 × Fin 4 // p.1 < p.2}
abbrev BraidFree := FreeLieAlgebra ℚ Edge

def chord (i j : Fin 4) : BraidFree :=
  if h : i < j then FreeLieAlgebra.of ℚ ⟨(i, j), h⟩
  else if h : j < i then FreeLieAlgebra.of ℚ ⟨(j, i), h⟩ else 0

def braidRelations : Set BraidFree :=
  {z | (∃ i j k l : Fin 4,
    i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      z = ⁅chord i j, chord k l⁆) ∨
    (∃ i j k : Fin 4, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      z = ⁅chord i j, chord i k + chord j k⁆)}

def braidIdeal : LieIdeal ℚ BraidFree :=
  LieSubmodule.lieSpan ℚ BraidFree braidRelations

abbrev T4 := BraidFree ⧸ braidIdeal
def t (i j : Fin 4) : T4 := LieSubmodule.Quotient.mk (chord i j)

def IsSolution (p : L) : Prop :=
  p + eval y x p = 0 ∧
  p + eval y (-x-y) p + eval (-x-y) x p = 0 ∧
  eval (t 0 1) (t 1 2 + t 1 3) p + eval (t 0 2 + t 1 2) (t 2 3) p =
    eval (t 1 2) (t 2 3) p + eval (t 0 1 + t 0 2) (t 1 3 + t 2 3) p +
      eval (t 0 1) (t 1 2) p

def W : Submodule ℚ L where
  carrier := {p | IsSolution p}
  zero_mem' := by simp [IsSolution]
  add_mem' := by
    intro p q hp hq
    rcases hp with ⟨hp1, hp2, hp3⟩
    rcases hq with ⟨hq1, hq2, hq3⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [map_add]
      calc
        _ = (p + eval y x p) + (q + eval y x q) := by abel
        _ = 0 := by rw [hp1, hq1, add_zero]
    · simp only [map_add]
      calc
        _ = (p + eval y (-x-y) p + eval (-x-y) x p) +
            (q + eval y (-x-y) q + eval (-x-y) x q) := by abel
        _ = 0 := by rw [hp2, hq2, add_zero]
    · simp only [map_add]
      calc
        _ = (eval (t 0 1) (t 1 2 + t 1 3) p + eval (t 0 2 + t 1 2) (t 2 3) p) +
            (eval (t 0 1) (t 1 2 + t 1 3) q + eval (t 0 2 + t 1 2) (t 2 3) q) := by abel
        _ = _ := by rw [hp3, hq3]; abel
  smul_mem' := by
    intro a p hp
    rcases hp with ⟨hp1, hp2, hp3⟩
    change IsSolution (a • p)
    simp only [IsSolution, map_smul]
    constructor
    · simpa only [smul_add, smul_zero] using congrArg (a • ·) hp1
    constructor
    · simpa only [smul_add, smul_zero] using congrArg (a • ·) hp2
    · simpa only [smul_add] using congrArg (a • ·) hp3

structure Tangent where
  base : L
  velocity : L

def Tangent.equiv : Tangent ≃ L × L where
  toFun z := (z.base, z.velocity)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup Tangent := Tangent.equiv.addCommGroup
instance : Module ℚ Tangent := Tangent.equiv.addEquiv.module ℚ
instance : Bracket Tangent Tangent :=
  ⟨fun a b => ⟨⁅a.base, b.base⁆,
    ⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆⟩⟩

instance : LieRing Tangent where
  add_lie a b c := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact add_lie a.base b.base c.base
    · change ⁅a.velocity + b.velocity, c.base⁆ + ⁅a.base + b.base, c.velocity⁆ =
        (⁅a.velocity, c.base⁆ + ⁅a.base, c.velocity⁆) +
          (⁅b.velocity, c.base⁆ + ⁅b.base, c.velocity⁆)
      simp only [add_lie]
      abel
  lie_add a b c := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact lie_add a.base b.base c.base
    · change ⁅a.velocity, b.base + c.base⁆ + ⁅a.base, b.velocity + c.velocity⁆ =
        (⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆) +
          (⁅a.velocity, c.base⁆ + ⁅a.base, c.velocity⁆)
      simp only [lie_add]
      abel
  lie_self a := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact lie_self a.base
    · change ⁅a.velocity, a.base⁆ + ⁅a.base, a.velocity⁆ = 0
      rw [← lie_skew a.velocity a.base]
      exact neg_add_cancel _
  leibniz_lie a b c := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact leibniz_lie a.base b.base c.base
    · change ⁅a.velocity, ⁅b.base, c.base⁆⁆ +
          ⁅a.base, ⁅b.velocity, c.base⁆ + ⁅b.base, c.velocity⁆⁆ =
        (⁅⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆, c.base⁆ +
          ⁅⁅a.base, b.base⁆, c.velocity⁆) +
        (⁅b.velocity, ⁅a.base, c.base⁆⁆ +
          ⁅b.base, ⁅a.velocity, c.base⁆ + ⁅a.base, c.velocity⁆⁆)
      simp only [lie_add, add_lie, lie_lie]
      abel

instance : LieAlgebra ℚ Tangent where
  lie_smul scalar left right := by
    apply Tangent.equiv.injective
    apply Prod.ext
    · exact lie_smul scalar left.base right.base
    · change ⁅left.velocity, scalar • right.base⁆ + ⁅left.base, scalar • right.velocity⁆ =
        scalar • (⁅left.velocity, right.base⁆ + ⁅left.base, right.velocity⁆)
      simp only [lie_smul, smul_add]

def tangentLift (p : L) : L →ₗ⁅ℚ⁆ Tangent :=
  FreeLieAlgebra.lift ℚ (fun i => if i then ⟨y, ⁅y,p⁆⟩ else ⟨x, 0⟩)

def D (p q : L) : L := (tangentLift p q).velocity

def ihara (p q : L) : L := D p q - D q p + ⁅p,q⁆

inductive WeightedWord {α : Type*} (wt : α → ℕ) : ℕ → FreeLieAlgebra ℚ α → Prop
  | generator (a : α) : WeightedWord wt (wt a) (FreeLieAlgebra.of ℚ a)
  | bracket {n m a b} : WeightedWord wt n a → WeightedWord wt m b →
      WeightedWord wt (n+m) ⁅a,b⁆

def weightPiece {α : Type*} (wt : α → ℕ) (n : ℕ) : Submodule ℚ (FreeLieAlgebra ℚ α) :=
  Submodule.span ℚ {p | WeightedWord wt n p}

abbrev OddFree := FreeLieAlgebra ℚ ℕ
def oddWeight (k : ℕ) : ℕ := 2*k+3
abbrev Fn (n : ℕ) := weightPiece oddWeight n
abbrev Ln (n : ℕ) := weightPiece (fun _ : Bool => 1) n
abbrev Wn (n : ℕ) : Submodule ℚ L := W ⊓ Ln n

def Graded (e : OddFree ≃ₗ[ℚ] W) : Prop :=
  ∀ n a, (e a : L) ∈ Ln n ↔ a ∈ Fn n

abbrev OddCompletion := (n : ℕ) → Fn n
abbrev WCompletion := (n : ℕ) → Wn n

instance : TopologicalSpace L := ⊥
instance : TopologicalSpace OddFree := ⊥

def completed (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) : OddCompletion → WCompletion :=
  fun a n => ⟨e (a n), (e (a n)).property, (h n (a n)).2 (a n).property⟩

def completedInv (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) : WCompletion → OddCompletion :=
  fun a n => ⟨e.symm ⟨a n, (a n).property.1⟩,
    (h n (e.symm ⟨a n, (a n).property.1⟩)).1 (by
      rw [LinearEquiv.apply_symm_apply]
      exact (a n).property.2)⟩

def MainStatement : Prop :=
  ∃ (e : OddFree ≃ₗ[ℚ] W) (h : Graded e),
    (∀ a b, (e ⁅a,b⁆ : L) = ihara (e a) (e b)) ∧
    Function.LeftInverse (completedInv e h) (completed e h) ∧
    Function.RightInverse (completedInv e h) (completed e h) ∧
    Continuous (completed e h) ∧ Continuous (completedInv e h) ∧
    (∀ (a b : OddCompletion) n,
      (e (∑ i ∈ Finset.range (n+1), ⁅(a i : OddFree), (b (n-i) : OddFree)⁆) : L) =
      ∑ i ∈ Finset.range (n+1),
        ihara (completed e h a i) (completed e h b (n-i)))



end DeligneDrinfeld
end
end OAI


