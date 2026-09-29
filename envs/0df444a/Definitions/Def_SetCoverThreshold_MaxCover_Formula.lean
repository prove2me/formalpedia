-- Prove2me | Definitions.Def_SetCoverThreshold_MaxCover_Formula
-- name    : SetCoverThreshold_MaxCover_Formula
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:00:37.098575+00:00
-- url     : https://prove2.me/theorems/7ad4ebaa-1d43-4d33-ac3e-5e26c8ec0ac0
-- title:
--   MAX 3SAT-B and MAX 3SAT-5 formulas, satisfiable fractions, gap NP-hardness, and Theorem 2.1.1 as a hypothesis
-- statement:
--   This file fixes the formula layer of Feige's reduction (J. ACM 45(4), 1998, §2.1, pp. 639–640). Formulas are CNF formulas in the sense of Cook's P versus NP statement: a formula is a list of clauses, a clause a list of literals, and a literal a variable $x_v$ ($v\in\mathbb N$) with a sign.
--
--   1. **3CNF-B formulas.** The paper's MAX 3SAT-B input reads: "A CNF formula with $n$ variables in which every clause contains at most three literals (a literal is a Boolean variable in either positive or negated form), and every variable appears in a bounded number of clauses." A formula $F$ is *3CNF-B* for the bound $B$ if every clause has at most three literals and every variable appears in at most $B$ clauses.
--   2. **3CNF-5 formulas.** The MAX 3SAT-5 input reads: "A CNF formula with $n$ variables and $5n/3$ clauses, in which every clause contains exactly three literals, every variable appears in exactly five clauses, and a variable does not appear in a clause more than once." A formula is *3CNF-5* if every clause has exactly three literals over three distinct variables and every variable that occurs appears in exactly five clauses. The count of $5n/3$ clauses follows from these conditions by double counting, so it is not a separate condition.
--   3. **Satisfiable fraction.** "At most a $\theta$-fraction of the clauses can be satisfied simultaneously" means that under every truth assignment $\tau$ the number of clauses containing a true literal is at most $\theta\,|F|$:
--   $$\forall \tau,\qquad \#\{C\in F : C \text{ contains a literal true under } \tau\} \le \theta\,|F|.$$
--   4. **Gap NP-hardness.** "It is NP-hard to distinguish between Yes and No instances" means: for every NP language $L'$ over a finite nonempty alphabet there is a map $f$ from strings to instances, computable in polynomial time together with the encoding of its output, sending members of $L'$ to Yes instances and non-members to No instances.
--   5. **Theorem 2.1.1 (cited, p. 639), as a named hypothesis.** The paper cites: "It is MAX-SNP hard to approximate MAX 3SAT-B: for some $\epsilon > 0$, it is NP-hard to distinguish between satisfiable 3CNF-B formulas, and 3CNF-B formulas in which at most an $(1 - \epsilon)$-fraction of the clauses can be satisfied simultaneously." The proposition `Thm211` says exactly this, for some bound $B$ and some $\varepsilon>0$, with formulas encoded by Cook's CNF encoding.
--   6. **Indexed 3CNF-5 formulas.** A `Formula5` is a 3CNF-5 formula with $M$ clauses indexed by $0,\dots,M-1$ and the three literals of each clause indexed by positions $0,1,2$; it carries the 3CNF-5 conditions as fields. Its variable at position $p$ of clause $c$, the notion of a local assignment of a clause's three positions satisfying it, and its conversion to a CNF formula are defined here.
--
--   These are the objects every later statement of the mission quantifies over; the cited Theorem 2.1.1 enters the goal theorem only through `Thm211`.
--
--   **Formalization Note** "At most three literals" is read literally, so the empty clause is a 3CNF-B clause; this makes `Thm211` a weaker (hence safer) hypothesis than a one-to-three reading. Clauses are counted with multiplicity. The CNF encoding writes variable indices in unary. The "no" formulas of `Thm211` are required to have at least one clause: the empty formula is satisfiable and satisfies every fraction bound, so without this requirement it would lie in both classes and the constant reduction to the empty formula would witness the gap.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), pp. 639–640, Section 2.1 (MAX 3SAT-B, Theorem 2.1.1, MAX 3SAT-5)

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace SetCoverThreshold.MaxCover

open CookPvsNP

/-- **MAX 3SAT-B instances** (Feige 1998, p. 639, §2.1 "Input"): every clause of the CNF formula
`F` contains at most three literals, and every variable appears in at most `B` clauses. -/
def Is3CNFB (B : ℕ) (F : CNF) : Prop :=
  (∀ C ∈ F, C.length ≤ 3) ∧
    ∀ v : ℕ, (F.filter (fun C => decide (∃ l ∈ C, l.2 = v))).length ≤ B

/-- **MAX 3SAT-5 instances** (Feige 1998, p. 640, §2.1 "Input"): every clause contains exactly
three literals, a variable does not appear in a clause more than once, and every variable that
occurs in `F` appears in exactly five clauses. -/
def Is3CNF5 (F : CNF) : Prop :=
  (∀ C ∈ F, C.length = 3 ∧ (C.map Prod.snd).Nodup) ∧
    ∀ v : ℕ, (∃ C ∈ F, ∃ l ∈ C, l.2 = v) →
      (F.filter (fun C => decide (∃ l ∈ C, l.2 = v))).length = 5

/-- **At most a `θ`-fraction of the clauses can be satisfied simultaneously**: under every
assignment `τ` of truth values to the variables, the number of clauses of `F` containing a true
literal is at most `θ · |F|` (clauses counted with multiplicity). -/
def AtMostFracSat (θ : ℝ) (F : CNF) : Prop :=
  ∀ τ : ℕ → Bool, ((F.filter (fun C => decide (∃ l ∈ C, τ l.2 = l.1))).length : ℝ) ≤ θ * F.length

/-- **Gap (promise) NP-hardness**: "it is NP-hard to distinguish between `Yes` and `No`
instances". Every NP language `L'` over any finite nonempty alphabet is mapped by a function `f`
(whose composition with the encoding `enc` is polynomial-time computable) to `Yes`-instances on
members of `L'` and to `No`-instances on non-members. -/
def GapNPHard {α Sym : Type} (enc : α → List Sym) (Yes No : α → Prop) : Prop :=
  ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : Lang Sym'), L' ∈ NP Sym' →
    ∃ f : List Sym' → α, PolyTimeComputable (fun x => enc (f x)) ∧
      ∀ x, (x ∈ L' → Yes (f x)) ∧ (x ∉ L' → No (f x))

/-- **Theorem 2.1.1 (cited, p. 639), as a named hypothesis.** For some bound `B` and some
`ε > 0` it is NP-hard to distinguish satisfiable 3CNF-B formulas from 3CNF-B formulas in which at
most a `(1 − ε)`-fraction of the clauses can be satisfied simultaneously. The latter formulas have
at least one clause: the empty formula is satisfiable, so without `F ≠ []` it would be a member of
both classes and the constant reduction `x ↦ []` would witness the gap. -/
def Thm211 : Prop :=
  ∃ (B : ℕ) (ε : ℝ), 0 < ε ∧
    GapNPHard encodeCNF (fun F => Is3CNFB B F ∧ F.Satisfiable)
      (fun F => Is3CNFB B F ∧ F ≠ [] ∧ AtMostFracSat (1 - ε) F)

/-- A **3CNF-5 formula** with its clauses indexed: `M` clauses, clause `c` having literals
`clause c 0, clause c 1, clause c 2` over three distinct variables, and every variable that occurs
occurring in exactly five clauses. -/
structure Formula5 where
  /-- The number of clauses. -/
  M : ℕ
  /-- The three literals of each clause. -/
  clause : Fin M → Fin 3 → Literal
  /-- A variable does not appear in a clause more than once. -/
  distinct_vars : ∀ c, Function.Injective (fun p => (clause c p).2)
  /-- Every variable that occurs appears in exactly five clauses. -/
  five : ∀ v : ℕ, (∃ c p, (clause c p).2 = v) →
    (Finset.univ.filter (fun c => ∃ p, (clause c p).2 = v)).card = 5

namespace Formula5

/-- The variable at position `p` of clause `c`. -/
def var (φ : Formula5) (c : Fin φ.M) (p : Fin 3) : ℕ := (φ.clause c p).2

/-- A local assignment `b` of the three positions of clause `c` satisfies that clause. -/
def LocalSat (φ : Formula5) (c : Fin φ.M) (b : Fin 3 → Bool) : Prop :=
  ∃ p, b p = (φ.clause c p).1

instance (φ : Formula5) (c : Fin φ.M) : DecidablePred (φ.LocalSat c) := by
  intro b; unfold LocalSat; infer_instance

/-- The formula as a `CookPvsNP.CNF`: the list of its clauses, each the list of its three
literals. -/
def toCNF (φ : Formula5) : CNF := List.ofFn (fun c => List.ofFn (φ.clause c))

end Formula5

end SetCoverThreshold.MaxCover


