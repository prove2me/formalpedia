-- Prove2me | Definitions.Def_TwoMasterRoommates_Capped_Supplement_Hardness
-- name    : TwoMasterRoommates_Capped_Supplement_Hardness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:33:05.510141+00:00
-- url     : https://prove2.me/theorems/51373ea0-6611-48a4-9490-49e7f1c24a7b
-- title:
--   Flat/strict domain, reward alphabets, reward-threshold languages, PTAS, and bounded-occurrence formulas
-- statement:
--   Instances are the mission's two-master instances with integer ranks. The flat/strict domain of Theorem D.1 consists of the instances with an even number $n$ of agents, no caps, a constant master $a$ (every $A$ observer is indifferent among all other agents), an injective master $b$ (every $B$ observer follows one strict whole order), and $b(x)<b(y)$ whenever $x\in A$ and $y\in B$. Either class may be empty. Rewards $w$ are integers on unordered pairs, independent of the preferences; they never remove a pair from the matching domain or from the blocking test.
--
--   The signed alphabet requires, on every pair of distinct agents, $w(AA)=0$, $w(AB)\in\{-3,0\}$ and $w(BB)\in\{-3,1,4\}$. The nonnegative alphabets are $\{0,3,4,7\}$ and $\{0,21,22,23,31\}$. For an alphabet, the reward-threshold language consists of the binary codes of a domain instance, its rewards in the alphabet and an integer threshold $T$ such that some weakly stable perfect matching $M$ has
--
--   $$w(M)\ge T.$$
--
--   Strings that are not such codes are outside the language. A stable-output reduction family supplies, for every NP language over any finite nonempty alphabet, a polynomial-time many-one reduction to the language whose every output is the code of a domain instance, with rewards in the alphabet, that has a weakly stable perfect matching. A deterministic PTAS gives, for each rational $\varepsilon>0$, a polynomial-time computable map that, on every domain instance with rewards in $\{0,21,22,23,31\}$ that has a weakly stable perfect matching, returns the code of a weakly stable perfect matching $M$ with $w(M)\ge(1-\varepsilon)w(M')$ for every weakly stable perfect matching $M'$.
--
--   A formula has $n$ variables and a list of labelled clauses, each a list of literals. It is valid for Lemma D.5 when $n\ge1$, every clause has at most three literals, and each variable has at most five literal occurrences over all clauses. For an assignment $\tau$, $\mathrm{unsat}(\tau)$ counts the clauses with no true literal, $u^*$ is its minimum over all assignments, $K=321n+22m$ and $N=28n+2m$, where $m$ is the number of clauses.
--
--   These are the objects of Theorems D.1 and D.6 and Lemma D.5. P, NP, polynomial-time computability and NP-completeness are those of the published Cook framework.
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 23 (PDF p. 24), Theorem D.1 and §D.1; p. 25 (PDF p. 26), proof of D.1 (NP membership, alphabet shift) and Lemma D.5; p. 27 (PDF p. 28), Theorem D.6

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Instance
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_TwoMasterRoommates_Capped_Supplement_Common

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped.Supplement

open TwoMasterRoommates.Capped

/-- The preference domain of Theorem D.1: an even complete population, no caps, every `A`
observer indifferent among all other agents (its whole master `a` is constant), every `B`
observer following one whole strict master `b`, and all `A` identities before all `B` identities
in `b`. Either class may be empty. -/
def FlatStrict {n : ℕ} (I : Instance ℤ n) : Prop :=
  Even n ∧ (∀ v, I.κ v = ⊤) ∧ (∀ x y, I.a x = I.a y) ∧ Function.Injective I.b ∧
    ∀ x y, I.isA x = true → I.isA y = false → I.b x < I.b y

/-- A restriction on the rewards of an instance (a reward alphabet). -/
abbrev RewardRule : Type := ∀ n : ℕ, Instance ℤ n → (Sym2 (Fin n) → ℤ) → Prop

/-- The signed alphabet of Theorem D.1: `w(AA) = 0`, `w(AB) ∈ {−3, 0}`, `w(BB) ∈ {−3, 1, 4}`
on every pair of distinct agents. -/
def signedRule : RewardRule := fun n I w => ∀ x y : Fin n, x ≠ y →
  (I.isA x = true → I.isA y = true → w s(x, y) = 0) ∧
  (I.isA x = true → I.isA y = false → w s(x, y) = -3 ∨ w s(x, y) = 0) ∧
  (I.isA x = false → I.isA y = false →
    w s(x, y) = -3 ∨ w s(x, y) = 1 ∨ w s(x, y) = 4)

/-- Every reward of a pair of distinct agents lies in the fixed set `S`. -/
def setRule (S : Finset ℤ) : RewardRule := fun n _ w => ∀ x y : Fin n, x ≠ y → w s(x, y) ∈ S

/-- The nonnegative alphabet `{0, 3, 4, 7}` of Theorem D.1. -/
def alphabetD1 : Finset ℤ := {0, 3, 4, 7}

/-- The nonnegative alphabet `{0, 21, 22, 23, 31}` of Lemma D.5 and Theorem D.6. -/
def alphabetD6 : Finset ℤ := {0, 21, 22, 23, 31}

/-- Binary code of an optimisation input: `n`, the class flags, the masters `a` and `b`, and the
rewards on all pairs `{i, j}`, `i < j`. Caps are not encoded (they are `⊤` in the domain). -/
def encI {n : ℕ} (I : Instance ℤ n) (w : Sym2 (Fin n) → ℤ) : List Bool :=
  encNat n ++ List.ofFn I.isA ++ (List.ofFn I.a).flatMap encInt ++
    (List.ofFn I.b).flatMap encInt ++ encWeights encInt w

/-- Binary code of a decision input: the optimisation input followed by the threshold `T`. -/
def encD {n : ℕ} (I : Instance ℤ n) (w : Sym2 (Fin n) → ℤ) (T : ℤ) : List Bool :=
  encI I w ++ encInt T

/-- The reward-threshold language for a reward alphabet: the codes of domain instances with
rewards in the alphabet and a threshold `T` such that some weakly stable perfect matching has
total reward at least `T`. A string that is not such a code (malformed, out of the domain, or out
of the alphabet) is not in the language. -/
def ThreshLang (rule : RewardRule) : CookPvsNP.Lang Bool :=
  { x | ∃ (n : ℕ) (I : Instance ℤ n) (w : Sym2 (Fin n) → ℤ) (T : ℤ),
      x = encD I w T ∧ FlatStrict I ∧ rule n I w ∧
        ∃ M, IsSolution I M ∧ T ≤ edgeSum w M }

/-- Every NP language reduces to `ThreshLang rule` by a polynomial-time many-one reduction all
of whose outputs are codes of domain instances, with rewards in the alphabet, that have a weakly
stable perfect matching. -/
def StableOutputReductions (rule : RewardRule) : Prop :=
  ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
    L' ∈ CookPvsNP.NP Sym' →
    ∃ f : List Sym' → List Bool, CookPvsNP.PolyTimeComputable f ∧
      (∀ x, x ∈ L' ↔ f x ∈ ThreshLang rule) ∧
      ∀ x, ∃ (n : ℕ) (I : Instance ℤ n) (w : Sym2 (Fin n) → ℤ) (T : ℤ),
        f x = encD I w T ∧ FlatStrict I ∧ rule n I w ∧ ∃ M, IsSolution I M

/-- A deterministic PTAS for maximum-reward weakly stable matching on domain instances with
rewards in `{0, 21, 22, 23, 31}` that admit a weakly stable perfect matching: for every rational
`ε > 0` a polynomial-time computable map returns the code of a weakly stable perfect matching
whose reward is at least `(1 − ε)` times the reward of every weakly stable perfect matching. -/
def HasPTAS : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
    ∀ (n : ℕ) (I : Instance ℤ n) (w : Sym2 (Fin n) → ℤ),
      FlatStrict I → setRule alphabetD6 n I w → (∃ M, IsSolution I M) →
      ∃ M, IsSolution I M ∧ f (encI I w) = encM M ∧
        ∀ M', IsSolution I M' → (1 - ε) * ((edgeSum w M' : ℤ) : ℚ) ≤ ((edgeSum w M : ℤ) : ℚ)

/-! ### Bounded-occurrence formulas (Lemma D.5) -/

/-- A CNF formula on variables `Fin n` with a list of labelled clauses; a literal `(b, i)` is
`x_i` when `b = true` and `¬x_i` when `b = false`. -/
structure Formula where
  n : ℕ
  clauses : List (List (Bool × Fin n))

namespace Formula

/-- The input class of Lemma D.5: at least one variable, every clause of size at most three,
and at most five literal occurrences of each variable over all clauses. -/
def Valid5 (φ : Formula) : Prop :=
  1 ≤ φ.n ∧ (∀ C ∈ φ.clauses, C.length ≤ 3) ∧
    ∀ i : Fin φ.n, (φ.clauses.map fun C => C.countP fun l => decide (l.2 = i)).sum ≤ 5

/-- The number of clauses (with their labels) with no true literal under `τ`. -/
def unsat (φ : Formula) (τ : Fin φ.n → Bool) : ℕ :=
  φ.clauses.countP fun C => C.all fun l => τ l.2 != l.1

/-- `u*`: the minimum number of unsatisfied clauses over all assignments. -/
def ustar (φ : Formula) : ℕ := Finset.univ.inf' Finset.univ_nonempty φ.unsat

/-- Binary code of a formula. -/
def enc (φ : Formula) : List Bool :=
  encNat φ.n ++ encList (encList fun l : Bool × Fin φ.n => l.1 :: encNat l.2.val) φ.clauses

/-- Binary code of an assignment: its values `τ 0, …, τ (n-1)`. -/
def encA (φ : Formula) (τ : Fin φ.n → Bool) : List Bool := List.ofFn τ

/-- The baseline `K = 321 n + 22 m` of Lemma D.5. -/
def K (φ : Formula) : ℤ := 321 * φ.n + 22 * φ.clauses.length

/-- The number of agents `N = 28 n + 2 m` of Lemma D.5. -/
def agents (φ : Formula) : ℕ := 28 * φ.n + 2 * φ.clauses.length

end Formula

end TwoMasterRoommates.Capped.Supplement


