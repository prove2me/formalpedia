-- Prove2me | Definitions.Def_UltimateL_Constructible
-- name    : UltimateL_Constructible
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T21:31:56.525646+00:00
-- url     : https://prove2.me/theorems/1299bbba-dc5a-4c2a-9341-a2231b71c965
-- title:
--   The constructible hierarchy, L, L(A,ℝ), and Θ^{L(A,ℝ)}
-- statement:
--   The **definable power set** of a set $a$ consists of the subsets of $a$ carved out over $(a,\in)$ by a first-order formula with finitely many parameters from $a$. Iterating this through the ordinals above a starting set $X$ (level $0$ is $X$, successors take definable subsets, nonzero limits take unions) gives the **constructible hierarchy above $X$**, whose union is the class $L[X]$. Gödel's **constructible universe** is $L=L[\varnothing]$, and a set is **constructible** if it lies in $L$. The **transitive closure** of a set is defined by recursion on rank. The inner model $L(A,\mathbb R)$ is the constructible closure above the transitive closure of $\{A\}\cup\mathbb R$ — equivalently, the least inner model of ZF containing $A$ and every real (reals are coded as elements of Baire space $\omega^\omega$, following the platform convention). Finally, $\Theta^{L(A,\mathbb R)}$ (Woodin's Definition 7.6) is the supremum of the ordinals that are surjective images of the reals under a function belonging to $L(A,\mathbb R)$.
-- source:
--   W. Hugh Woodin, In Search of Ultimate-L, BSL 23(1) (2017) 1-109, doi:10.1017/bsl.2016.34, Definition 7.6 (Θ^{L(A,ℝ)}) and §7 (L(A,ℝ)); the constructible hierarchy follows the platform's ContinuumHypothesis.Constructible (after Marks, Set Theory, Def. 20.2); L(A,ℝ) is standard (Kanamori, The Higher Infinite, 2nd ed., Springer 2003, §28).

import Mathlib
import Definitions.Def_OmegaLogic_Semantics
import Definitions.Def_OmegaLogic_Provability

namespace UltimateL

universe u

open ZFSet OmegaLogic

/-- The definable power set of `a`: the subsets of `a` carved out over `(a, ∈)` by a
first-order formula with finitely many parameters from `a`. -/
noncomputable def definableSubsets (a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun b =>
    ∃ (n : ℕ) (φ : setLang.Formula (Fin (n + 1))) (p : Fin n → (a : Set ZFSet.{u})),
      ∀ x : (a : Set ZFSet.{u}), x.1 ∈ b ↔ φ.Realize (Fin.cons x p)) (ZFSet.powerset a)

/-- The constructible hierarchy above a starting set `X`: level `0` is `X`, successor levels
take definable subsets, and nonzero limit levels take unions. -/
noncomputable def constructibleAbove (X : ZFSet.{u}) (α : Ordinal.{u}) : ZFSet.{u} :=
  Ordinal.limitRecOn α X (fun _ a => definableSubsets a)
    (fun β _ previous => ZFSet.iUnion (fun i : β.ToType =>
      previous i.toOrd.val i.toOrd.property))

/-- The class `L[X]` of sets constructible above `X`. -/
def Lof (X : ZFSet.{u}) : Set ZFSet.{u} := {x | ∃ α : Ordinal.{u}, x ∈ constructibleAbove X α}

/-- Gödel's constructible universe `L = L[∅]`. -/
def L : Set ZFSet.{u} := Lof ∅

/-- `x` is constructible: `x ∈ L`. -/
def IsConstructible (x : ZFSet.{u}) : Prop := x ∈ L

/-- The transitive closure of a set. -/
noncomputable def transitiveClosure (x : ZFSet.{u}) : ZFSet.{u} :=
  x ∪ ZFSet.iUnion (fun y : {y : ZFSet.{u} // y ∈ x} => transitiveClosure y.1)
termination_by x.rank
decreasing_by exact ZFSet.rank_lt_of_mem y.2

/-- The set of (codes of) all reals, i.e. all elements of Baire space `ω^ω`. -/
noncomputable def realsSet : ZFSet.{u} :=
  ZFSet.range (fun x : ULift.{u} (ℕ → ℕ) => OmegaLogic.realCode x.down)

/-- The inner model `L(A, ℝ)`: the constructible closure above the transitive closure of
`{A} ∪ ℝ`, i.e. the least inner model of ZF containing `A` and every real. -/
noncomputable def LAR (A : Set (ℕ → ℕ)) : Set ZFSet.{u} :=
  Lof (transitiveClosure ({OmegaLogic.realsIn (Set.univ : Set ZFSet.{u}) A} ∪ realsSet))

/-- `Θ^{L(A, ℝ)}` (Woodin, Definition 7.6): the supremum of the ordinals `α` that are
surjective images of the reals under a function belonging to `L(A, ℝ)`. -/
noncomputable def ThetaLAR (A : Set (ℕ → ℕ)) : Ordinal.{u} :=
  sSup {α : Ordinal.{u} | ∃ f : ZFSet.{u}, f ∈ LAR A ∧
    IsFunc realsSet α.toZFSet f ∧ ∀ β < α, ∃ r ∈ realsSet, pair r β.toZFSet ∈ f}

end UltimateL


