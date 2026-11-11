-- Prove2me | Definitions.Def_ComplexityUnpred_Catalytic_FastCatTape
-- name    : ComplexityUnpred_Catalytic_FastCatTape
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:01:56.563886+00:00
-- url     : https://prove2.me/theorems/423ba840-addd-49e1-899b-4362b8104a54
-- title:
--   Catalytic logspace machines, logspace-computable functions and FastCatTape (Definitions 2.6, 2.9, 4.1)
-- statement:
--   A **catalytic machine** (published model `CatalyticMatching.General.Machine`) has a read-only input tape, a write-only output tape, a binary read-write work tape, and a binary read-write **catalytic tape** initialised to an arbitrary string $\tau$. It is a **catalytic logspace machine with catalytic space $p(n)$** ($p$ a polynomial) if there is $C\ge1$ such that for every input $x$ and **every** $\tau\in\{0,1\}^{p(|x|)}$ the run halts with $\tau$ restored on the catalytic tape, having visited at most $C\,(\lfloor\log_2(|x|+2)\rfloor+1)$ work cells. $\mathrm{time}(M(x,\tau))$ is the number of steps before it halts.
--
--   For a catalytic logspace machine $M$ with catalytic space $p$ and $p_M:\mathbb N\to\mathbb N$, **FastCatTape$(M,p_M)$** is the search problem: input $x\in\{0,1\}^*$; output $\tau\in\{0,1\}^{p(|x|)}$ with $\mathrm{time}(M(x,\tau))\le p_M(|x|)$.
--
--   A function $f:\{0,1\}^*\to\mathbb N$ is **logspace computable** if a machine of the same model with an empty catalytic tape halts on every $x$ with the binary code of $f(x)$ on its output tape, visiting at most $C(\lfloor\log_2(|x|+2)\rfloor+1)$ work cells; $f:\mathbb N\to\mathbb N$ is logspace computable if $x\mapsto f(|x|)$ is. A function is **polynomially bounded** if $f(N)\le N^k+k$ (resp. $f(x)\le|x|^k+k$) for some $k$.
--
--   FastCatTape is the problem whose deterministic polynomial-time solution would derandomize the ZPP simulation of catalytic logspace of Buhrman et al.
--
--   **Formalization Note** `IsCatalyticLogspace M C p` reuses the published `RestoredOutput` with the trivial output relation. `HaltsWithin M x τ T` ("the run has halted after $T$ steps") is $\mathrm{time}(M(x,\tau))\le T$, since a halted configuration is a fixed point of the published `step`. Binary output is `Nat.bits` (least significant bit first). The paper fixes no model for "logspace-computable"; this is the ordinary logspace transducer.
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, pp. 20–21, Definitions 2.6, 2.9; p. 29, Definition 4.1

import Mathlib
import Definitions.Def_CatalyticMatching_General_CatalyticSpace
import Definitions.Def_TetrisHard_Rows_Search

namespace ComplexityUnpred.Catalytic

open CatalyticMatching.General

/-! Agarwala, Dorfman, *The Complexity of Unpredictability*, arXiv:2611.05956v1: catalytic
machines (Definitions 2.6, 2.9, pp. 20–21) and **Definition 4.1** (FastCatTape, p. 29), on the
published catalytic machine `CatalyticMatching.General.Machine` (finite binary transition
table; read-only input with endmarkers; append-only output; semi-infinite binary work tape whose
visited cells are counted; catalytic tape = the supplied string `τ`, of fixed length).

"Logarithmic space" is `C · logBudget(L) = C · (⌊log₂(L + 2)⌋ + 1)` visited work cells on inputs
of length `L`, as in the published `InCL`; "polynomially bounded" is `f(N) ≤ N^k + k`. -/

/-- `f : ℕ → ℕ` is polynomially bounded: `f(N) ≤ N^k + k` for some `k`. -/
def PolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ k : ℕ, ∀ N, f N ≤ N ^ k + k

/-- `f : {0,1}* → ℕ` is polynomially bounded in the input length: `f(x) ≤ |x|^k + k`. -/
def PolyBoundedStr (f : List Bool → ℕ) : Prop :=
  ∃ k : ℕ, ∀ x : List Bool, f x ≤ x.length ^ k + k

/-- `f : {0,1}* → ℕ` is logspace computable: one machine of the published model, run with an
empty catalytic tape (so an ordinary logspace transducer), halts on every input `x` with the
binary code of `f(x)` (least significant bit first, `Nat.bits`) on its output tape, having
visited at most `C · logBudget(|x|)` work cells. -/
def LogspaceComputable (f : List Bool → ℕ) : Prop :=
  ∃ (M : Machine) (C : ℕ), 1 ≤ C ∧ ∀ x : List Bool, ∃ t c, M.run x [] t = some c ∧
    c.state = none ∧ c.output = Nat.bits (f x) ∧ M.workBound x [] t (C * logBudget x.length)

/-- `f : ℕ → ℕ` is logspace computable: `N ↦ f(N)` is computed in space `O(log N)` from any input
of length `N` (in particular from `1^N`), in the sense of `LogspaceComputable`. -/
def LogspaceComputableNat (f : ℕ → ℕ) : Prop :=
  LogspaceComputable (fun x => f x.length)

/-- `M` is a catalytic logspace machine with catalytic space `p(|x|)` and work-space constant
`C` (Definitions 2.6–2.9 without the output requirement): on every input `x` and **every**
initial catalytic tape `τ ∈ {0,1}^{p(|x|)}` it halts, with `τ` restored, having visited at most
`C · logBudget(|x|)` work cells. -/
def IsCatalyticLogspace (M : Machine) (C : ℕ) (p : Polynomial ℕ) : Prop :=
  1 ≤ C ∧ ∀ x τ : List Bool, τ.length = p.eval x.length →
    ∃ t, RestoredOutput M (fun _ _ => True) C x τ t

/-- `time(M(x, τ)) ≤ T`: the run of `M` on input `x` with catalytic tape `τ` has halted after
`T` steps. (A halted configuration is a fixed point of `Machine.step`, so this holds for every
`T` at least the halting time and for no smaller `T`.) -/
def HaltsWithin (M : Machine) (x τ : List Bool) (T : ℕ) : Prop :=
  ∃ c, M.run x τ T = some c ∧ c.state = none

/-- **Definition 4.1** (p. 29), `FastCatTape(M, p_M)` for a catalytic machine `M` with catalytic
space `q(n) = p(n)`: input `x ∈ {0,1}*`; output `τ ∈ {0,1}^{q(|x|)}` with
`time(M(x, τ)) ≤ p_M(|x|)`. Every string is a valid instance. -/
def FastCatTape (M : Machine) (p : Polynomial ℕ) (pM : ℕ → ℕ) :
    TetrisHard.Rows.SearchProblem where
  valid _ := True
  answer x τ := τ.length = p.eval x.length ∧ HaltsWithin M x τ (pM x.length)

end ComplexityUnpred.Catalytic


