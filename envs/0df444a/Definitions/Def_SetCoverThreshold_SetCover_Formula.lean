-- Prove2me | Definitions.Def_SetCoverThreshold_SetCover_Formula
-- name    : SetCoverThreshold_SetCover_Formula
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:52:40.562505+00:00
-- url     : https://prove2.me/theorems/84663f41-a721-404e-b793-b8bc5e3de3e7
-- title:
--   3CNF-B and 3CNF-5 formulas, the satisfiable fraction, and Theorem 2.1.1 as a hypothesis
-- statement:
--   Formulas are CNF formulas over variables $x_0,x_1,\dots$; a literal is $x_v$ or $\neg x_v$, a clause is a disjunction of literals, and an assignment $\tau$ satisfies a clause when it makes one of its literals true.
--
--   1. **3CNF-B** (p. 639, MAX 3SAT-B): every clause has at most three literals and every variable appears in at most $B$ clauses.
--   2. **At most a $\theta$-fraction satisfiable**: the formula $F$ has at least one clause, and every assignment satisfies at most $\theta\cdot|F|$ of its clauses.
--   3. **3CNF-5** (p. 640, MAX 3SAT-5): "A CNF formula with n variables and 5n/3 clauses, in which every clause contains exactly three literals, every variable appears in exactly five clauses, and a variable does not appear in a clause more than once." A 3CNF-5 formula $\varphi$ is given by its number of variables $n$, its number of clauses $M\ge 1$, and for each clause $c$ and position $p\in\{0,1,2\}$ a literal on a variable $x_{v(c,p)}$; the three variables of a clause are distinct, and each variable appears in exactly five clauses (so $3M=5n$).
--   4. **Theorem 2.1.1** (p. 639; Arora et al. 1992, Papadimitriou–Yannakakis 1991), recorded as a proposition to be assumed: "It is MAX-SNP hard to approximate MAX 3SAT-B: for some ε > 0, it is NP-hard to distinguish between satisfiable 3CNF-B formulas, and 3CNF-B formulas in which at most an (1 − ε)-fraction of the clauses can be satisfied simultaneously." In symbols: there are $B\in\mathbb N$ and $\varepsilon>0$ such that it is NP-hard to distinguish satisfiable 3CNF-B formulas from 3CNF-B formulas in which at most a $(1-\varepsilon)$-fraction of the clauses can be satisfied simultaneously, formulas being encoded as in `CookPvsNP_defs`.
--
--   These are the inputs of the multi-prover proof system of Section 2; every statement of Sections 2–4 is about a 3CNF-5 formula.
--
--   **Formalization Note** "At most a $\theta$-fraction" requires a nonempty formula: without it the empty formula would be both satisfiable and a no-instance, and Theorem 2.1.1 would hold trivially by mapping every input to it. A 3CNF-5 formula is a structure on the variables $0,\dots,n-1$ (every one of them occurs), converted to a `CookPvsNP.CNF` by `toCNF`. "At most three literals" admits clauses with fewer (even zero) literals.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 639, Section 2.1 (MAX 3SAT-B) and Theorem 2.1.1; p. 640, Section 2.1 (MAX 3SAT-5)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity

namespace SetCoverThreshold.SetCover

open CookPvsNP

/-- `F` is a 3CNF-B formula (Feige 1998, p. 639, MAX 3SAT-B): every clause has at most three
literals, and every variable occurs in at most `B` clauses. -/
def Is3CNFB (B : ℕ) (F : CNF) : Prop :=
  (∀ C ∈ F, C.length ≤ 3) ∧
    ∀ v : ℕ, (F.filter (fun C => decide (∃ ℓ ∈ C, ℓ.2 = v))).length ≤ B

/-- "At most a `θ`-fraction of the clauses of `F` can be satisfied simultaneously": `F` has at
least one clause, and every assignment satisfies at most `θ · |F|` clauses. -/
def AtMostFracSat (θ : ℝ) (F : CNF) : Prop :=
  0 < F.length ∧
    ∀ τ : ℕ → Bool,
      ((F.filter (fun C => decide (∃ ℓ ∈ C, τ ℓ.2 = ℓ.1))).length : ℝ) ≤ θ * F.length

/-- A 3CNF-5 formula (Feige 1998, p. 640, MAX 3SAT-5) on the variables `0, …, n-1` with `M ≥ 1`
clauses. Clause `c` is `clause c 0 ∨ clause c 1 ∨ clause c 2`; a literal `(b, v)` is the variable
`x_v` if `b = true` and `¬x_v` if `b = false`. Every clause has exactly three literals on three
distinct variables, and every variable appears in exactly five clauses. -/
structure Formula5 where
  /-- number of variables -/
  n : ℕ
  /-- number of clauses -/
  M : ℕ
  M_pos : 0 < M
  /-- the three literals of each clause -/
  clause : Fin M → Fin 3 → Bool × Fin n
  /-- a variable does not appear in a clause more than once -/
  distinct : ∀ c, Function.Injective (fun p => (clause c p).2)
  /-- every variable appears in exactly five clauses -/
  five : ∀ v : Fin n,
    (Finset.univ.filter (fun cp : Fin M × Fin 3 => (clause cp.1 cp.2).2 = v)).card = 5

namespace Formula5

variable (φ : Formula5)

/-- The variable at position `p` of clause `c`. -/
def var (c : Fin φ.M) (p : Fin 3) : Fin φ.n := (φ.clause c p).2

/-- The three bits `b` (the values of the three variables of clause `c`, in position order)
satisfy clause `c`. -/
def ClauseSatBy (c : Fin φ.M) (b : Fin 3 → Bool) : Prop := ∃ p, b p = (φ.clause c p).1

instance (c : Fin φ.M) (b : Fin 3 → Bool) : Decidable (φ.ClauseSatBy c b) := by
  unfold ClauseSatBy; infer_instance

/-- The formula as a `CookPvsNP.CNF` (variable `x_v` becomes the natural number `v`). -/
def toCNF : CNF :=
  List.ofFn fun c : Fin φ.M => List.ofFn fun p : Fin 3 => ((φ.clause c p).1, ((φ.clause c p).2 : ℕ))

end Formula5

/-- Theorem 2.1.1 of Feige 1998 (p. 639; Arora et al. 1992, Papadimitriou–Yannakakis 1991), taken
as a hypothesis: for some bound `B` and some `ε > 0` it is NP-hard to distinguish satisfiable
3CNF-B formulas from 3CNF-B formulas in which at most a `(1 - ε)`-fraction of the clauses can be
satisfied simultaneously. -/
def Thm211 : Prop :=
  ∃ (B : ℕ) (ε : ℝ), 0 < ε ∧
    GapNPHard encodeCNF (fun F => Is3CNFB B F ∧ F.Satisfiable)
      (fun F => Is3CNFB B F ∧ AtMostFracSat (1 - ε) F)

end SetCoverThreshold.SetCover


