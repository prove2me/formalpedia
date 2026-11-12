-- Prove2me | Definitions.Def_PQNormIPM1352_Main_Prog
-- name    : PQNormIPM1352_Main_Prog
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:54.165501+00:00
-- url     : https://prove2.me/theorems/62df5fa4-a863-441f-9601-71d9ead015ca
-- title:
--   Cost model: real-RAM programs, their interpreter, and the SDD-solver oracle with the contract of Theorem 2
-- statement:
--   The paper states running times without fixing a machine model. The mission fixes a **randomized real-RAM**:
--
--   1. A **program** is a finite tree of primitive operations on an abstract carrier of real values: loading a rational constant; $a+b$, $a-b$, $a\times b$, $a/b$ and the real power $a^b$; the natural logarithm; the comparison $a \le b$; one unit of index work (`tick`; every loop iteration executes one); a counting loop that returns $\lceil x\rceil$ (or $0$ for $x \le 0$) after $\lceil x\rceil + 1$ steps; and two oracle calls, `build` and `apply`. Programs are written for an arbitrary carrier type, so real values can only be combined through these primitives. There is no floor, norm, supremum, argmin or matrix-inverse primitive.
--   2. The **interpreter** runs a program over $\mathbb R$ and charges one unit per primitive, $\lceil x\rceil + 1$ per counting loop, $1 + |L| + c_{\text{build}}$ per call `build(N, L, δ)` and $1 + N + |b| + c_{\text{apply}}$ per call `apply(h, b)`. It returns the probability distribution of the pair (result, total cost). The **expected cost** is $\mathbb E[\text{cost}]$.
--   3. An **SDD-solver oracle** (`STSolve`) maps an $N\times N$ matrix $L$ and an accuracy $\delta$ to a random outcome $(P, c_{\text{build}}, c_{\text{apply}})$: a linear operator $P$ (applied as $b\mapsto Pb$), the build cost, and the cost of each application.
--   4. The **contract of Theorem 2** with constants $c_0, k_0$: for every positive definite SDD $L \in \mathbb R^{N\times N}$ with $s_L$ non-zero entries and every $0 < \delta < 1$, every outcome satisfies
--   $$P = P^\top,\qquad (1-\delta)L^{-1} \preceq P \preceq (1+\delta)L^{-1},\qquad c_{\text{apply}} \le c_0\,(s_L+1)\,\log(N+s_L+2)^{k_0}\,\big(1 + \log(1/\delta)\big),$$
--   and the expected build cost is at most $c_0\,(s_L+1)\,\log(N+s_L+2)^{k_0}$.
--
--   Theorem 2 (nearly-linear-time Laplacian solvers, cited from the literature) is the statement that some oracle meets this contract; the mission uses it as a hypothesis on the oracle.
--
--   **Formalization Note** The program syntax is a free-monad tree; costs are computed by the interpreter, never annotated by the algorithm author. A program can perform bookkeeping on natural-number indices inside its control flow; the mission's algorithms do all index work inside charged loops (one charged unit per iteration) and sort with a charged merge sort, so this convention charges $O(1)$ per array access and per index operation, as in a RAM. The order $\preceq$ is the Loewner order, written as positive semidefiniteness of the differences. The exact-inverse oracle ($P = L^{-1}$, costs $\mathrm{nnz}(L)+1$) meets the contract with $c_0 = 1$, $k_0 = 0$, so the contract is satisfiable.
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Theorem 2, p. 4 (solver contract, eq. (10) on p. 15); §2.1, p. 3 (Õ hides polylog(m, n, s)); cost model fixed by the mission

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_MatrixClasses

/-!
# The cost model: programs over an abstract real carrier, their interpreter, and the SDD-solver
# oracle with the contract of Theorem 2

Pirazzini–Spielman, STOC 2027 submission #1352. The paper fixes no machine model; this file
fixes a randomized real-RAM. A program is a tree (`Prog R α`) whose nodes are primitive
operations; it is written polymorphically in the carrier `R` of real values, so a program can
combine reals **only** through the primitive nodes (there is no other operation on `R`). Every
executed node is charged by the interpreter `run`, which instantiates `R := ℝ`:

* `const c`, `bin op a b` (`+ − × ÷` and `a ^ b`, real power), `log a`, `le a b` (comparison):
  one unit each;
* `tick`: one unit of index work (loop control, index arithmetic, array access); the loop
  combinator `forLoop` executes one `tick` per iteration;
* `count x`: counting `t = 0, 1, …` until `t ≥ x` — returns `⌈x⌉₊` (`Nat.ceil`, `0` for `x ≤ 0`)
  and costs `⌈x⌉₊ + 1` (there is no floor or ceiling primitive);
* `build N L δ`: one call `STSolve(L, δ)` of the SDD-solver oracle on the `N × N` matrix given by
  the entry list `L` (duplicate positions are summed); it returns a handle and costs
  `1 + |L| + buildCost`, where `buildCost` is part of the oracle's random outcome;
* `apply h b`: one application `solveL(b) = P b` of a built operator; costs
  `1 + N + |b| + applyCost`.

There is no norm, supremum, argmin or matrix-inverse primitive. The oracle is the only source of
randomness; the interpreter returns a probability distribution (`PMF`) over pairs
(result, total cost).

Theorem 2 (p. 4) enters as the predicate `SatisfiesContract`: a solver all of whose outcomes are
symmetric operators `P` with `(1 − δ)L⁻¹ ⪯ P ⪯ (1 + δ)L⁻¹`, with expected build cost
`≤ c₀ (s_L + 1) log(N + s_L + 2)^{k₀}` and application cost
`≤ c₀ (s_L + 1) log(N + s_L + 2)^{k₀} (1 + log(1/δ))`, for every positive definite SDD `L` with
`s_L` non-zero entries and every `0 < δ < 1`.
-/

open Matrix
open scoped ENNReal

namespace PQNormIPM1352.Main

/-- Binary real primitives: `+`, `−`, `×`, `÷`, and the real power `a ^ b`. -/
inductive BinOp
  | add
  | sub
  | mul
  | div
  | rpow
  deriving DecidableEq

/-- Programs over the real carrier `R` returning a value of type `α` (a free-monad syntax tree).
Each constructor is one primitive whose result is passed to the continuation. -/
inductive Prog (R : Type) (α : Type) : Type
  | ret : α → Prog R α
  | const : ℚ → (R → Prog R α) → Prog R α
  | bin : BinOp → R → R → (R → Prog R α) → Prog R α
  | log : R → (R → Prog R α) → Prog R α
  | le : R → R → (Bool → Prog R α) → Prog R α
  | tick : Prog R α → Prog R α
  | count : R → (ℕ → Prog R α) → Prog R α
  | build : ℕ → List (ℕ × ℕ × R) → R → (ℕ → Prog R α) → Prog R α
  | apply : ℕ → List R → (List R → Prog R α) → Prog R α

namespace Prog

variable {R α β : Type}

/-- Sequential composition of programs. -/
def bind : Prog R α → (α → Prog R β) → Prog R β
  | ret a, f => f a
  | const c k, f => const c fun r => bind (k r) f
  | bin o a b k, f => bin o a b fun r => bind (k r) f
  | log a k, f => log a fun r => bind (k r) f
  | le a b k, f => le a b fun r => bind (k r) f
  | tick k, f => tick (bind k f)
  | count x k, f => count x fun t => bind (k t) f
  | build N L δ k, f => build N L δ fun h => bind (k h) f
  | apply h b k, f => apply h b fun r => bind (k r) f

instance : Monad (Prog R) where
  pure := ret
  bind := bind

/-- The primitive `bin o a b` returning its result. -/
def op (o : BinOp) (a b : R) : Prog R R := bin o a b ret

/-- Load the rational constant `c`. -/
def cst (c : ℚ) : Prog R R := const c ret

/-- One charged unit of index work. -/
def step : Prog R Unit := tick (ret ())

/-- The comparison `a ≤ b`. -/
def leq (a b : R) : Prog R Bool := le a b ret

/-- Counting loop: returns `⌈x⌉₊` at cost `⌈x⌉₊ + 1`. -/
def countUp (x : R) : Prog R ℕ := count x ret

/-- Build a solver for the `N × N` matrix with entry list `L` and accuracy `δ`; returns a handle. -/
def solverBuild (N : ℕ) (L : List (ℕ × ℕ × R)) (δ : R) : Prog R ℕ := build N L δ ret

/-- Apply the operator with handle `h` to the vector `b`. -/
def solverApply (h : ℕ) (b : List R) : Prog R (List R) := apply h b ret

/-- The loop `for k = 0, …, n − 1` threading a state; one `tick` is executed per iteration. -/
def forLoop {σ : Type} (n : ℕ) (init : σ) (body : ℕ → σ → Prog R σ) : Prog R σ :=
  (List.range n).foldlM (fun st k => bind step fun _ => body k st) init

end Prog

/-- Arithmetic expressions over `R`. `Ex.eval` compiles an expression to primitives: every
constant and every operation node is one primitive (no sharing), a variable is a register read. -/
inductive Ex (R : Type)
  | var : R → Ex R
  | lit : ℚ → Ex R
  | add : Ex R → Ex R → Ex R
  | sub : Ex R → Ex R → Ex R
  | mul : Ex R → Ex R → Ex R
  | div : Ex R → Ex R → Ex R
  | pow : Ex R → Ex R → Ex R
  | log : Ex R → Ex R

namespace Ex

variable {R : Type}

/-- Compile an expression to a program (each node is one charged primitive). -/
def eval : Ex R → Prog R R
  | var r => Prog.ret r
  | lit c => Prog.cst c
  | add a b => Prog.bind a.eval fun x => Prog.bind b.eval fun y => Prog.op .add x y
  | sub a b => Prog.bind a.eval fun x => Prog.bind b.eval fun y => Prog.op .sub x y
  | mul a b => Prog.bind a.eval fun x => Prog.bind b.eval fun y => Prog.op .mul x y
  | div a b => Prog.bind a.eval fun x => Prog.bind b.eval fun y => Prog.op .div x y
  | pow a b => Prog.bind a.eval fun x => Prog.bind b.eval fun y => Prog.op .rpow x y
  | log a => Prog.bind a.eval fun x => Prog.log x Prog.ret

instance : Add (Ex R) := ⟨add⟩
instance : Sub (Ex R) := ⟨sub⟩
instance : Mul (Ex R) := ⟨mul⟩
instance : Div (Ex R) := ⟨div⟩
instance : HPow (Ex R) (Ex R) (Ex R) := ⟨pow⟩
instance {k : ℕ} [k.AtLeastTwo] : OfNat (Ex R) k := ⟨lit k⟩
instance : One (Ex R) := ⟨lit 1⟩
instance : Zero (Ex R) := ⟨lit 0⟩
instance : Neg (Ex R) := ⟨fun a => sub (lit 0) a⟩

end Ex

/-! ## Semantics over `ℝ` -/

/-- The meaning of a binary primitive on `ℝ` (Lean's total conventions `a / 0 = 0` and real power;
the programs of this mission only use them on inputs where they are the usual operations). -/
noncomputable def BinOp.denote : BinOp → ℝ → ℝ → ℝ
  | .add => fun a b => a + b
  | .sub => fun a b => a - b
  | .mul => fun a b => a * b
  | .div => fun a b => a / b
  | .rpow => fun a b => a ^ b

/-- One outcome of a solver build: the linear operator `P` it implements, the cost of the build,
and the cost of each later application `b ↦ P b`. -/
structure SolverOutcome (N : ℕ) where
  P : Matrix (Fin N) (Fin N) ℝ
  buildCost : ℕ
  applyCost : ℕ

/-- An SDD-solver oracle (`STSolve` of Theorem 2): on an `N × N` matrix `L` and accuracy `δ` it
returns a random outcome. -/
structure Solver where
  build : (N : ℕ) → Matrix (Fin N) (Fin N) ℝ → ℝ → PMF (SolverOutcome N)

/-- The matrix of an entry list (entries outside `N × N` are ignored, duplicates are summed). -/
noncomputable def entriesMatrix (N : ℕ) (L : List (ℕ × ℕ × ℝ)) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ((L.filter fun e => e.1 = (i : ℕ) ∧ e.2.1 = (j : ℕ)).map fun e => e.2.2).sum

/-- A list read as a vector of `ℝᴺ` (missing entries are `0`). -/
def listVec (N : ℕ) (b : List ℝ) : Fin N → ℝ := fun i => b.getD i 0

/-- The operators built so far, indexed by their handles. -/
abbrev Store := List (Σ N : ℕ, SolverOutcome N)

/-- Add `c` to the cost component of a distribution of (result, cost) pairs. -/
noncomputable def charge {α : Type} (c : ℕ) (μ : PMF (α × ℕ)) : PMF (α × ℕ) :=
  μ.map fun r => (r.1, r.2 + c)

open Classical in
/-- The interpreter: the distribution of (result, total cost) of a program over `ℝ`, given the
solver oracle and the store of operators already built. -/
noncomputable def runFrom (S : Solver) {α : Type} : Prog ℝ α → Store → PMF (α × ℕ)
  | .ret a, _ => PMF.pure (a, 0)
  | .const c k, st => charge 1 (runFrom S (k (c : ℝ)) st)
  | .bin o a b k, st => charge 1 (runFrom S (k (o.denote a b)) st)
  | .log a k, st => charge 1 (runFrom S (k (Real.log a)) st)
  | .le a b k, st => charge 1 (runFrom S (k (decide (a ≤ b))) st)
  | .tick k, st => charge 1 (runFrom S k st)
  | .count x k, st => charge (⌈x⌉₊ + 1) (runFrom S (k ⌈x⌉₊) st)
  | .build N L δ k, st =>
      (S.build N (entriesMatrix N L) δ).bind fun o =>
        charge (1 + L.length + o.buildCost) (runFrom S (k st.length) (st ++ [⟨N, o⟩]))
  | .apply h b k, st =>
      match st[h]? with
      | none => charge (1 + b.length) (runFrom S (k []) st)
      | some ⟨N, o⟩ =>
          charge (1 + N + b.length + o.applyCost)
            (runFrom S (k (List.ofFn fun i => (o.P *ᵥ listVec N b) i)) st)

/-- The distribution of (result, cost) of a complete run (empty store). -/
noncomputable def run (S : Solver) {α : Type} (P : Prog ℝ α) : PMF (α × ℕ) := runFrom S P []

/-- The expected cost of a program: `E[cost] = ∑ Pr[(r, c)] · c`, in `ℝ≥0∞`. -/
noncomputable def expectedCost (S : Solver) {α : Type} (P : Prog ℝ α) : ℝ≥0∞ :=
  ∑' r : α × ℕ, run S P r * (r.2 : ℝ≥0∞)

/-- The solver contract of Theorem 2 (p. 4) with constants `c₀, k₀`: for every positive definite
SDD matrix `L ∈ ℝ^{N×N}` with `s_L = nnz L` non-zero entries and every `0 < δ < 1`,
1. every outcome is a symmetric `P` with `(1 − δ)L⁻¹ ⪯ P ⪯ (1 + δ)L⁻¹` (Loewner order), whose
   application cost is `≤ c₀ (s_L + 1) log(N + s_L + 2)^{k₀} (1 + log(1/δ))`;
2. the expected build cost is `≤ c₀ (s_L + 1) log(N + s_L + 2)^{k₀}`. -/
def SatisfiesContract (S : Solver) (c₀ k₀ : ℕ) : Prop :=
  ∀ (N : ℕ) (L : Matrix (Fin N) (Fin N) ℝ) (δ : ℝ), L.PosDef → IsSDD L → 0 < δ → δ < 1 →
    (∀ o ∈ (S.build N L δ).support,
        o.Pᵀ = o.P ∧ (o.P - (1 - δ) • L⁻¹).PosSemidef ∧ ((1 + δ) • L⁻¹ - o.P).PosSemidef ∧
        (o.applyCost : ℝ) ≤
          c₀ * (nnz L + 1) * Real.log (N + nnz L + 2) ^ k₀ * (1 + Real.log (1 / δ))) ∧
    ∑' o : SolverOutcome N, S.build N L δ o * (o.buildCost : ℝ≥0∞) ≤
      ENNReal.ofReal (c₀ * (nnz L + 1) * Real.log (N + nnz L + 2) ^ k₀)

end PQNormIPM1352.Main


