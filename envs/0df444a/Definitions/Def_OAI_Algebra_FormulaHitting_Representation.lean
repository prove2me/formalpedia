-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_Representation
-- name    : OAI_Algebra_FormulaHitting_Representation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T08:58:17.586978+00:00
-- url     : https://prove2.me/theorems/ae37de42-97e0-41e7-a627-8eb133c19190
-- title:
--   Acyclic weighted automata and their construction from noncommutative formulas
-- statement:
--   Fix $n\in\mathbb{N}$. A word is a finite list $w=w_1w_2\cdots w_m$ of letters $w_r\in\{0,\dots,n-1\}$, with length $|w|=m$; $\varepsilon$ denotes the empty word. A noncommutative formula over a semiring $F$ in variables $x_0,\dots,x_{n-1}$ is built from scalars $a\in F$, variables $x_i$, sums $f+g$ and products $f\cdot g$. Its size counts each leaf as $1$ and each $+$ or $\cdot$ node as $1$ plus the sizes of its two parts. Its coefficient series $w\mapsto f_w\in F$ assigns $a$ to $\varepsilon$ for a scalar $a$ (and $0$ to other words), the indicator of the one-letter word $i$ to $x_i$, adds termwise for sums, and takes the convolution
--   $$
--   (f\cdot g)_w=\sum_{uv=w}f_u\,g_v
--   $$
--   over all ways of cutting $w$ into a prefix $u$ and a suffix $v$ for products.
--
--   Let $F$ be a commutative semiring. The file defines the following.
--
--   1. **Automaton value.** For a finite state set $Q$, matrices $B_0,\dots,B_{n-1}\in F^{Q\times Q}$ and vectors $u,v\in F^Q$, the value on a word $w=w_1\cdots w_m$ is
--   $$
--   u^{\mathsf T}B_{w_1}B_{w_2}\cdots B_{w_m}\,v .
--   $$
--   The word matrix is the product $B_{w_1}\cdots B_{w_m}$.
--   2. **Acyclic representation.** This consists of a finite state set $Q$ with decidable equality, vectors $u,v\in F^Q$, transition matrices $B_i\in F^{Q\times Q}$, and a rank function $\rho:Q\to\mathbb{N}$ with $\rho(a)<|Q|$ for all $a$, such that $(B_i)_{ab}=0$ whenever $\rho(b)\le\rho(a)$. So every transition strictly increases the rank. Its value is the word series $w\mapsto u^{\mathsf T}B_w v$.
--   3. **Constructions.**
--      - *Scalar $a$*: one state with $u=a$, $v=1$, $B_i=0$.
--      - *Variable $x_i$*: two states $0\to1$, a transition of weight $1$ on letter $i$ only, $u=e_0$, $v=e_1$.
--      - *Sum $R+S$*: the disjoint union of the state sets, block-diagonal transitions, and concatenated $u,v$.
--      - *Product $R\cdot S$*: the disjoint union, with $u=(u_R,0)$, $v=\bigl((u_S^{\mathsf T}v_S)\,v_R,\ v_S\bigr)$ and block transitions
--   $$
--   \begin{pmatrix}A_i & v_R\,(u_S^{\mathsf T}B_i)\\ 0 & B_i\end{pmatrix},
--   $$
--   where $A_i$ and $B_i$ are the transitions of $R$ and $S$. This block matrix is the product transition.
--
--      The rank on a disjoint union is $\rho_R$ on $R$'s states and $|Q_R|+\rho_S$ on $S$'s states. The state counts are $1$, $2$, $|Q_R|+|Q_S|$ and $|Q_R|+|Q_S|$ respectively.
--   4. **Representation of a formula.** Defined by structural recursion, using the four constructions above.
--
--   This is the classical translation of noncommutative formulas into small acyclic (upper-triangular) automata, whose values can then be studied by linear algebra.
--
--   **Formalization Note** `AcyclicRepresentation F n` is a structure whose state type is a field `State : Type`, with `Fintype` and `DecidableEq` instances. Here $(B_i)_{ab}$ is `B i a b`, and `vecMulVec` is the outer product. The constructions are `scalar`, `ofVariable`, `add` and `mul`, and the state counts are recorded as simplification lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Representation.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Representation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FormulaHitting mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FormulaHitting
import Definitions.Def_OAI_Algebra_FormulaHitting_Wronskian
import Definitions.Def_OAI_Algebra_FormulaHitting_NumeratorRows
import Definitions.Def_OAI_Algebra_FormulaHitting_OrderBasis
import Definitions.Def_OAI_Algebra_FormulaHitting_Multiplicity
import Definitions.Def_OAI_Algebra_FormulaHitting_Formula

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace NCHitting

open Matrix

def automatonValue {F I : Type*} {n : ℕ} [Semiring F] [Fintype I]
    (B : Fin n → Matrix I I F) (u v : I → F) : Word n → F
  | [] => u ⬝ᵥ v
  | i :: w => automatonValue B (u ᵥ* B i) v w

def wordMatrix {F I : Type*} {n : ℕ} [Semiring F] [Fintype I] [DecidableEq I]
    (B : Fin n → Matrix I I F) (w : Word n) : Matrix I I F :=
  (w.map B).prod

def productTransition {F I J : Type*} {n : ℕ}
    [Semiring F] [Fintype J]
    (A : Fin n → Matrix I I F) (B : Fin n → Matrix J J F)
    (v : I → F) (u' : J → F) (i : Fin n) : Matrix (I ⊕ J) (I ⊕ J) F :=
  fromBlocks (A i) (vecMulVec v (u' ᵥ* B i)) 0 (B i)

structure AcyclicRepresentation (F : Type*) (n : ℕ) [CommSemiring F] where
  State : Type
  [fintype : Fintype State]
  [decidableEq : DecidableEq State]
  u : State → F
  v : State → F
  B : Fin n → Matrix State State F
  rank : State → ℕ
  rank_lt : ∀ a, rank a < Fintype.card State
  upper : ∀ i a b, rank b ≤ rank a → B i a b = 0

attribute [instance] AcyclicRepresentation.fintype AcyclicRepresentation.decidableEq

namespace AcyclicRepresentation

variable {F : Type*} {n : ℕ} [CommSemiring F]

def value (R : AcyclicRepresentation F n) : WordSeries F n :=
  automatonValue R.B R.u R.v

def sumRank (R S : AcyclicRepresentation F n) : R.State ⊕ S.State → ℕ :=
  Sum.elim R.rank (fun a => Fintype.card R.State + S.rank a)

theorem sumRank_lt (R S : AcyclicRepresentation F n) (a : R.State ⊕ S.State) :
    sumRank R S a < Fintype.card (R.State ⊕ S.State) := by
  cases a with
  | inl a =>
    have h := R.rank_lt a
    simp only [sumRank, Sum.elim_inl, Fintype.card_sum]
    omega
  | inr a =>
    have h := S.rank_lt a
    simp only [sumRank, Sum.elim_inr, Fintype.card_sum]
    omega

theorem block_upper (R S : AcyclicRepresentation F n)
    (C : Fin n → Matrix R.State S.State F) (i : Fin n)
    (a b : R.State ⊕ S.State) (h : sumRank R S b ≤ sumRank R S a) :
    fromBlocks (R.B i) (C i) 0 (S.B i) a b = 0 := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact R.upper i a b h
    | inr b =>
      have ha := R.rank_lt a
      simp only [sumRank, Sum.elim_inl, Sum.elim_inr] at h
      omega
  | inr a =>
    cases b with
    | inl b => rfl
    | inr b =>
      apply S.upper i a b
      simp only [sumRank, Sum.elim_inr] at h
      omega

def add (R S : AcyclicRepresentation F n) : AcyclicRepresentation F n where
  State := R.State ⊕ S.State
  fintype := inferInstance
  decidableEq := inferInstance
  u := Sum.elim R.u S.u
  v := Sum.elim R.v S.v
  B i := fromBlocks (R.B i) 0 0 (S.B i)
  rank := sumRank R S
  rank_lt := sumRank_lt R S
  upper := block_upper R S (fun _ => 0)

def mul (R S : AcyclicRepresentation F n) : AcyclicRepresentation F n where
  State := R.State ⊕ S.State
  fintype := inferInstance
  decidableEq := inferInstance
  u := Sum.elim R.u 0
  v := Sum.elim ((S.u ⬝ᵥ S.v) • R.v) S.v
  B := productTransition R.B S.B R.v S.u
  rank := sumRank R S
  rank_lt := sumRank_lt R S
  upper := block_upper R S (fun i => vecMulVec R.v (S.u ᵥ* S.B i))

def scalar (a : F) : AcyclicRepresentation F n where
  State := Unit
  fintype := inferInstance
  decidableEq := inferInstance
  u _ := a
  v _ := 1
  B _ := 0
  rank _ := 0
  rank_lt _ := by simp
  upper _ _ _ _ := rfl

def ofVariable (i : Fin n) : AcyclicRepresentation F n where
  State := Fin 2
  fintype := inferInstance
  decidableEq := inferInstance
  u a := if a = 0 then 1 else 0
  v a := if a = 1 then 1 else 0
  B j a b := if a = 0 ∧ b = 1 ∧ j = i then 1 else 0
  rank a := a.val
  rank_lt a := by simp <;> exact Nat.le_of_lt_succ a.isLt
  upper j a b h := by
    by_cases hab : a = 0 ∧ b = 1 ∧ j = i
    · rcases hab with ⟨rfl, rfl, _⟩
      simp at h
    · simp [hab]

@[simp] theorem scalar_card (a : F) : Fintype.card (scalar (n := n) a).State = 1 := rfl

@[simp] theorem variable_card (i : Fin n) :
    Fintype.card (ofVariable (F := F) i).State = 2 := rfl

@[simp] theorem add_card (R S : AcyclicRepresentation F n) :
    Fintype.card (R.add S).State = Fintype.card R.State + Fintype.card S.State :=
  Fintype.card_sum

@[simp] theorem mul_card (R S : AcyclicRepresentation F n) :
    Fintype.card (R.mul S).State = Fintype.card R.State + Fintype.card S.State :=
  Fintype.card_sum

end AcyclicRepresentation

noncomputable def Formula.representation {F : Type*} {n : ℕ} [CommSemiring F] :
    Formula F n → AcyclicRepresentation F n
  | .scalar a => .scalar a
  | .var i => .ofVariable i
  | .add f g => f.representation.add g.representation
  | .mul f g => f.representation.mul g.representation

end NCHitting

end OAI


