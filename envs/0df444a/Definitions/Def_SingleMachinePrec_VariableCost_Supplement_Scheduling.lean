-- Prove2me | Definitions.Def_SingleMachinePrec_VariableCost_Supplement_Scheduling
-- name    : SingleMachinePrec_VariableCost_Supplement_Scheduling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:45:40.851384+00:00
-- url     : https://prove2.me/theorems/92a38556-8ab5-4b98-8909-d46494aa70d4
-- title:
--   Integer scheduling inputs, feasible orders, $\sum w_jC_j$, and polynomial-time (randomized) approximation algorithms
-- statement:
--   An instance of $1|\mathrm{prec}|\sum w_jC_j$ (p. 653) consists of $n$ jobs $0,\dots,n-1$, nonnegative integer processing times $p_j$ and weights $w_j$, and the precedence relation $P$, given by its $n\times n$ Boolean matrix; the precedence constraints are required to form a partial order (reflexive, antisymmetric, transitive). The **input code** of an instance writes $n$ in unary, every $p_j$ and $w_j$ in self-delimiting binary, and then the matrix row by row.
--
--   A schedule is a **processing order** $\sigma$: a list containing every job exactly once. It is **feasible** when $(i,j)\in P$, $i\neq j$, implies that $i$ comes before $j$ in $\sigma$. The completion time $C_j(\sigma)$ is the total processing time of $j$ and of the jobs before it, and the cost of $\sigma$ is
--   $$\operatorname{cost}(\sigma)=\sum_{j} w_j\,C_j(\sigma),$$
--   the full objective, including its fixed part.
--
--   Given a class of inputs (an input may carry more data than the instance, such as a realizer) and a ratio $\alpha$, an **$\alpha$-approximation algorithm** maps the code of every input of the class to the code of a feasible order $\sigma$ with $\operatorname{cost}(\sigma)\le\alpha\cdot\operatorname{cost}(\tau)$ for every feasible order $\tau$. It runs in **polynomial time** if it is computed by one multi-stack Turing machine within a polynomial in the length of the input code.
--
--   A **randomized polynomial-time $\alpha$-approximation algorithm** consists of two polynomial-time machines: the first computes from the input code a number $N\ge1$; a seed $s$ is drawn uniformly from $\{0,\dots,N-1\}$; the second maps the input code followed by the binary code of $s$ to the code of a feasible order $\sigma_s$. Every outcome must be feasible and the expected cost must satisfy
--   $$\frac1N\sum_{s<N}\operatorname{cost}(\sigma_s)\le\alpha\cdot\operatorname{cost}(\tau)\quad\text{for every feasible }\tau .$$
--
--   These notions are the conclusions of the paper's algorithmic theorems (§§3–6).
--
--   **Formalization Note** Machines are the published `QAlgorithms.Complexity.PolyTimeComputable` (Mathlib's `TM2ComputableInPolyTime` on `List Bool`). Inserting idle time never helps, so idle-free orders suffice. `toInstance` gives the published real-valued `SingleMachinePrec.VariableCost.Instance` carried by an integer input. The comparison with every feasible order replaces $\mathrm{OPT}$ and avoids a minimum over a possibly empty set.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 653, §1 (the problem 1|prec|∑w_jC_j); pp. 657–661, Theorems 3.2–6.5 (polynomial-time and randomized approximation algorithms)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_SingleMachinePrec_VariableCost_VertexCoverGraph

set_option autoImplicit false

namespace SingleMachinePrec.VariableCost.Supplement

open QAlgorithms.Complexity

/-! ### Binary codes -/

/-- Self-delimiting binary code of a natural number: each bit `b` of its binary expansion
(least significant first) is written as the pair `true, b`, and the word ends with `false`.
Its length is `2 · (number of binary digits) + 1`, so numbers are written in binary. -/
def encBin (m : ℕ) : Str :=
  (Nat.bits m).flatMap (fun b => [true, b]) ++ [false]

/-- Code of a list: its length in unary (`encNat`), followed by the codes of its entries. -/
def encList {α : Type} (f : α → Str) (l : List α) : Str :=
  encNat l.length ++ l.flatMap f

/-! ### Scheduling instances with integer data -/

/-- An instance of `1|prec|∑ w_j C_j` as an algorithm receives it (p. 653): `n` jobs
`0, …, n-1`, nonnegative integer processing times `p j` and weights `w j`, and the precedence
relation given by its `n × n` Boolean matrix (`prec i j = true` means `(i, j) ∈ P`). -/
structure SchedInput where
  n : ℕ
  p : Fin n → ℕ
  w : Fin n → ℕ
  prec : Fin n → Fin n → Bool

namespace SchedInput

/-- The precedence relation `P` of the instance, as a proposition. -/
def Prec (x : SchedInput) (i j : Fin x.n) : Prop := x.prec i j = true

/-- The precedence constraints form a partial order (reflexive, antisymmetric, transitive), as
required on p. 653. -/
def IsPoset (x : SchedInput) : Prop := IsPartialOrder (Fin x.n) x.Prec

/-- The input code: `n` in unary, then `p_0, …, p_{n-1}` and `w_0, …, w_{n-1}` in binary, then
the `n²` entries of the precedence matrix row by row. -/
def enc (x : SchedInput) : Str :=
  encNat x.n ++ (List.finRange x.n).flatMap (fun j => encBin (x.p j)) ++
    (List.finRange x.n).flatMap (fun j => encBin (x.w j)) ++
    (List.finRange x.n).flatMap (fun i => (List.finRange x.n).map (fun j => x.prec i j))

/-- A (non-preemptive, idle-free) schedule is a processing order `σ` of the jobs: a list
containing every job exactly once. It is feasible when `(i, j) ∈ P`, `i ≠ j` implies that `i`
comes before `j`. -/
def Feasible (x : SchedInput) (σ : List (Fin x.n)) : Prop :=
  σ.Nodup ∧ σ.length = x.n ∧ ∀ i j, x.Prec i j → i ≠ j → σ.idxOf i < σ.idxOf j

/-- Completion time `C_j` of job `j` in the order `σ`: the total processing time of `j` and of
the jobs before it. -/
def completion (x : SchedInput) (σ : List (Fin x.n)) (j : Fin x.n) : ℕ :=
  ((σ.take (σ.idxOf j + 1)).map x.p).sum

/-- The objective `∑_j w_j C_j` of the order `σ` (the full weighted completion time,
including its fixed part). -/
def cost (x : SchedInput) (σ : List (Fin x.n)) : ℕ :=
  ∑ j, x.w j * x.completion σ j

/-- The published real-valued instance (`SingleMachinePrec.VariableCost.Instance`) carried by
this integer input. -/
def toInstance (x : SchedInput) (h : x.IsPoset) : SingleMachinePrec.VariableCost.Instance (Fin x.n) where
  P := x.Prec
  isPartialOrder := h
  p := fun j => (x.p j : ℝ)
  w := fun j => (x.w j : ℝ)
  p_nonneg := fun _ => Nat.cast_nonneg _
  w_nonneg := fun _ => Nat.cast_nonneg _

end SchedInput

/-- The output code of a processing order: its length in unary, then the job indices in
binary. -/
def encSchedule {n : ℕ} (σ : List (Fin n)) : Str :=
  encList (fun j : Fin n => encBin j.val) σ

/-! ### Approximation algorithms -/

/-- `A` is an `α`-approximation algorithm on the inputs `a : I` satisfying `Cls`: on the code
`enc a` it outputs the code of a feasible order `σ` of the instance `inst a` whose cost is at
most `α a` times the cost of every feasible order (hence at most `α a · OPT`). -/
def IsApproxOn {I : Type} (enc : I → Str) (inst : I → SchedInput) (Cls : I → Prop)
    (α : I → ℝ) (A : Str → Str) : Prop :=
  ∀ a, Cls a → ∃ σ : List (Fin (inst a).n), A (enc a) = encSchedule σ ∧ (inst a).Feasible σ ∧
    ∀ τ : List (Fin (inst a).n), (inst a).Feasible τ →
      ((inst a).cost σ : ℝ) ≤ α a * ((inst a).cost τ : ℝ)

/-- A deterministic polynomial-time `α`-approximation algorithm: one multi-stack Turing machine,
running in time polynomial in the length of the input code, that is an `α`-approximation
algorithm on the inputs of class `Cls`. -/
def HasPolyTimeApprox {I : Type} (enc : I → Str) (inst : I → SchedInput) (Cls : I → Prop)
    (α : I → ℝ) : Prop :=
  ∃ A : Str → Str, PolyTimeComputable A ∧ IsApproxOn enc inst Cls α A

/-- A randomized polynomial-time `α`-approximation algorithm. Polynomial-time machine `R`
computes from the input code a range `N ≥ 1`; a seed `s` is drawn uniformly from
`{0, …, N-1}`; polynomial-time machine `A` maps the input code followed by `encBin s` to the
code of a feasible order `σ s`. Every outcome is feasible, and the expected cost
`(1/N) ∑_{s<N} cost (σ s)` is at most `α a` times the cost of every feasible order. -/
def HasPolyTimeRandApprox {I : Type} (enc : I → Str) (inst : I → SchedInput) (Cls : I → Prop)
    (α : I → ℝ) : Prop :=
  ∃ R A : Str → Str, PolyTimeComputable R ∧ PolyTimeComputable A ∧
    ∀ a, Cls a → ∃ N : ℕ, 0 < N ∧ R (enc a) = encBin N ∧
      ∃ σ : ℕ → List (Fin (inst a).n),
        (∀ s < N, A (enc a ++ encBin s) = encSchedule (σ s) ∧ (inst a).Feasible (σ s)) ∧
        ∀ τ : List (Fin (inst a).n), (inst a).Feasible τ →
          ∑ s ∈ Finset.range N, ((inst a).cost (σ s) : ℝ) ≤ α a * N * ((inst a).cost τ : ℝ)

end SingleMachinePrec.VariableCost.Supplement


