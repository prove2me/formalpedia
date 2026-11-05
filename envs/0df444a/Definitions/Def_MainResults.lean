-- Prove2me | Definitions.Def_MainResults
-- name    : MainResults
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:55:07.403249+00:00
-- url     : https://prove2.me/theorems/344aa353-4a6b-40b8-a59f-a8788d644940
-- title:
--   CNF formulas, finite-alphabet machines, ETH and the uniform counting bound
-- statement:
--   For each natural number $n$, a literal is a pair $(i,b)$ with $i$ one of the $n$ variable indices and $b$ a Boolean, and a CNF formula is a finite ordered list of finite ordered lists of literals. A formula is a $k$-CNF here when every clause has length at most $k$ and the outer list has no repeated clauses; clauses are compared as literal lists, so literal repetition within a clause, tautological clauses, empty clauses, and distinct permutations of the same literals are permitted. Satisfiability means that some Boolean assignment to all $n$ variables gives at least one literal its specified Boolean value in every clause. A missing literal slot is encoded as $0$, and $(i,b)$ as $2i+1+\operatorname{toNat}(b)$, where false and true have values $0$ and $1$. The clause encoding consists of $n$ true bits followed by a false bit, then exactly $k$ slots per clause, each represented by $w(n)=\operatorname{Nat.log2}(2n)+1$ bits in increasing bit-position order; missing slots are zero-padded, and literals after position $k-1$ are ignored by the encoding itself. There is no separate clause-count field. A Boolean-input/Boolean-output machine $M$ of Mathlib's type $\operatorname{TM2ComputableAux}$ decides $k$-SAT within $t$ when, for every natural $n$ and every formula satisfying this $k$-CNF condition, there exists a Boolean $b$ such that $b$ is true exactly when the formula is satisfiable and the library predicate $\operatorname{TM2OutputsInTime}$ holds for the encoded input, successful singleton output $[b]$, and time bound $t(n)$; input and output bits are transported using $M$'s inverse alphabet maps. $\operatorname{InTime}(k,\delta)$, for a nonnegative real $\delta$, means there exist such a machine $M$ and a natural constant $c$, every alphabet $M.\mathrm{tm}.\Gamma(i)$ being finite, that decide all these formulas within $\lfloor c2^{\delta n}\rfloor_+$, where the subscript denotes the natural-number floor. The extended nonnegative real $s(k)$ is the infimum of all nonnegative rates $\delta$ satisfying this condition, with infimum of an empty set equal to infinity; ETH means $0<s(3)$, and ETHIsFalse means its negation. AllOccur means that every one of the $n$ variables appears in at least one literal. The natural number numSat counts all satisfying Boolean assignments to the $n$ variables, and binary$(n,c)$ is exactly the lowest $n+1$ bits of $c$, in increasing bit-position order. The counting input prefixes the clause encoding with $k$ true bits and a false bit. With $\lg x=\log_2 x$, define $E_m(k,m)=km/\sqrt{\lg m}$, $E_n(k,n)=k^2n\lg(\lg n)/\sqrt{\lg n}$, and $T(C,k,m,n)=\lfloor2^{C\min(E_m(k,m),E_n(k,n))}\rfloor_+$. CountsWithin asserts the same library output-in-time predicate for this counting input, successful output binary$(n,\operatorname{numSat}(\varphi))$, and the supplied natural time bound. MainTheorem asserts the uniform-machine counting statement specified in its separate read-back. These definitions themselves permit zero parameters: the empty formula is satisfied by every assignment, an empty clause makes a formula unsatisfiable, AllOccur is vacuous for $n=0$, $w(0)=1$, and the real logarithm, square root, and division in the time expressions are Lean's total operations even outside their usual positive domains.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/MainResults.lean

import Mathlib
set_option autoImplicit false
namespace MainResults
open Turing
open scoped NNReal ENNReal
abbrev Lit (n : ℕ) : Type := Fin n × Bool
abbrev CNF (n : ℕ) : Type := List (List (Lit n))
def IsKCNF (k : ℕ) {n : ℕ} (φ : CNF n) : Prop := (∀ C ∈ φ, C.length ≤ k) ∧ φ.Nodup
def slot {n : ℕ} : Option (Lit n) → ℕ
  | none => 0
  | some l => 2 * l.1.val + 1 + l.2.toNat
def Satisfiable {n : ℕ} (φ : CNF n) : Prop := ∃ a : Fin n → Bool, ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2
def encClauses (k : ℕ) {n : ℕ} (φ : CNF n) : List Bool :=
  List.replicate n true ++ false :: φ.flatMap fun C => (List.range k).flatMap fun j =>
    (List.range (Nat.log2 (2 * n) + 1)).map (slot C[j]?).testBit
def DecidesKSat (k : ℕ) (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), IsKCNF k φ → ∃ b : Bool, (b = true ↔ Satisfiable φ) ∧
    Nonempty (TM2OutputsInTime M.tm ((encClauses k φ).map M.inputAlphabet.invFun)
      (some ([b].map M.outputAlphabet.invFun)) (t n))
def InTime (k : ℕ) (δ : ℝ≥0) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    DecidesKSat k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊
noncomputable def s (k : ℕ) : ℝ≥0∞ := ⨅ (δ : ℝ≥0) (_ : InTime k δ), (δ : ℝ≥0∞)
def ETH : Prop := 0 < s 3
def ETHIsFalse : Prop := ¬ ETH
def AllOccur {n : ℕ} (φ : CNF n) : Prop := ∀ i : Fin n, ∃ C ∈ φ, ∃ l ∈ C, l.1 = i
def numSat {n : ℕ} (φ : CNF n) : ℕ :=
  (Finset.univ.filter fun a : Fin n → Bool => ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2).card
def binary (n c : ℕ) : List Bool := (List.range (n + 1)).map c.testBit
def encInput (k : ℕ) {n : ℕ} (φ : CNF n) : List Bool :=
  List.replicate k true ++ false :: encClauses k φ
noncomputable def lg (x : ℝ) : ℝ := Real.logb 2 x
noncomputable def expM (k m : ℕ) : ℝ := (k : ℝ) * m / Real.sqrt (lg m)
noncomputable def expN (k n : ℕ) : ℝ := (k : ℝ) ^ 2 * n * lg (lg n) / Real.sqrt (lg n)
noncomputable def timeMin (C k m n : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ ((C : ℝ) * min (expM k m) (expN k n))⌋₊
def CountsWithin (M : TM2ComputableAux Bool Bool) (k : ℕ) {n : ℕ} (φ : CNF n) (t : ℕ) : Prop :=
  Nonempty (TM2OutputsInTime M.tm ((encInput k φ).map M.inputAlphabet.invFun)
    (some ((binary n (numSat φ)).map M.outputAlphabet.invFun)) t)
def MainTheorem : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → IsKCNF k φ → 2 ≤ φ.length → 4 ≤ n → AllOccur φ →
      CountsWithin M k φ (timeMin C k φ.length n)
end MainResults


