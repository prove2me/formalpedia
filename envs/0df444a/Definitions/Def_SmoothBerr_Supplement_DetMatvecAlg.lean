-- Prove2me | Definitions.Def_SmoothBerr_Supplement_DetMatvecAlg
-- name    : SmoothBerr_Supplement_DetMatvecAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:52:53.315315+00:00
-- url     : https://prove2.me/theorems/f85ec3ec-3968-49e8-9de0-5fded089b919
-- title:
--   Deterministic adaptive matvec algorithm $\Phi$, its transcript and $t_\Phi(A,b)$
-- statement:
--   A **deterministic matvec algorithm** $\Phi$ for $n\times n$ systems accesses the matrix $A$ only through queries $x\mapsto Ax$ and $y\mapsto A^\top y$. Given the right-hand side $b$ and the transcript of earlier queries and answers, it either halts or chooses the kind and the vector of its next query; when it halts it returns a vector $\Phi(A,b)$ computed from $b$ and the final transcript.
--
--   The **transcript** after $i$ steps lists the queries with their answers. The algorithm **halts within $t$ matvecs** on $(A,b)$ if it has stopped after at most $t$ queries, and
--   $$
--   t_\Phi(A,b)\in\mathbb N\cup\{\infty\}
--   $$
--   is the number of matvecs it computes before halting ($\infty$ if it never halts). The structure also records when an algorithm uses only queries $x\mapsto Ax$.
--
--   These objects state the deterministic lower bounds (Theorems 2.2, 4.3, 4.4, 6.2, 6.4, 6.7) and the deterministic upper bound of Theorem 2.3.
--
--   **Formalization Note** The algorithm is information-based: the next-query and output maps are arbitrary functions, with no computability or measurability requirement, as in the paper. The run is computed round by round; after halting the transcript no longer changes, so the output read after any round past the halting time is $\Phi(A,b)$.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), §2, p.2 (matvec model); §6, pp.16–18 (Φ(A, b), transcripts T_i, t_Φ(A, b))

import Mathlib

open Matrix

namespace SmoothBerr.Supplement

/-- The two kinds of matvec query: `x ↦ A x` (`mulA`) and `y ↦ Aᵀ y` (`mulAT`). -/
inductive Side
  | mulA
  | mulAT
  deriving DecidableEq

/-- The answer to a query of kind `s` with vector `v` against the matrix `A`. -/
def Side.apply {n : ℕ} : Side → Matrix (Fin n) (Fin n) ℝ → (Fin n → ℝ) → (Fin n → ℝ)
  | .mulA, A, v => A *ᵥ v
  | .mulAT, A, v => Aᵀ *ᵥ v

/-- One transcript entry: the kind of query, the query vector and the answer. -/
abbrev Entry (n : ℕ) : Type := Side × (Fin n → ℝ) × (Fin n → ℝ)

/-- A **deterministic adaptive matvec algorithm** for `n × n` systems (Dereziński, Mahoney, Meyer,
Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript
of 3 Nov 2026, sha256 9575cd20…, §2, p.2: the algorithm accesses `A` "only through implicit
queries of the form x ↦ Ax and x ↦ A^⊤x"; §6, pp.16–18: `Φ(A, b)`, its transcript
`T_i = (b, (x_1, y_1), …, (x_i, y_i))` and `t_Φ(A, b)`).

From the right-hand side `b` and the transcript so far, `next` either halts (`none`) or submits
the next query (its kind and vector); `output` maps `b` and the final transcript to the returned
vector `x̃`.

**Formalization Note** The algorithm is information-based: `next` and `output` are arbitrary
functions (no computability or measurability), as in the paper. The dimension `n` is fixed and
known to the algorithm. -/
structure DetMatvecAlg (n : ℕ) where
  /-- Halt (`none`) or the next query, from `b` and the transcript so far. -/
  next : (Fin n → ℝ) → List (Entry n) → Option (Side × (Fin n → ℝ))
  /-- The returned vector, from `b` and the final transcript. -/
  output : (Fin n → ℝ) → List (Entry n) → (Fin n → ℝ)

namespace DetMatvecAlg

variable {n : ℕ}

/-- The transcript of the run of `Φ` on `(A, b)` after `k` rounds: each round either appends the
next query with its answer, or (once `Φ` has halted) leaves the transcript unchanged. -/
def trace (Φ : DetMatvecAlg n) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ℕ → List (Entry n)
  | 0 => []
  | k + 1 =>
    match Φ.next b (Φ.trace A b k) with
    | none => Φ.trace A b k
    | some q => Φ.trace A b k ++ [(q.1, q.2, q.1.apply A q.2)]

/-- `Φ` halts on `(A, b)` after computing at most `t` matvecs. -/
def HaltsWithin (Φ : DetMatvecAlg n) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (t : ℕ) :
    Prop :=
  Φ.next b (Φ.trace A b t) = none

/-- The vector returned by `Φ` on `(A, b)` from its transcript after `k` rounds; once `Φ` has
halted within `k` matvecs this is `Φ(A, b)`. -/
def outputAt (Φ : DetMatvecAlg n) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (k : ℕ) :
    Fin n → ℝ :=
  Φ.output b (Φ.trace A b k)

/-- `t_Φ(A, b) ∈ ℕ∞`: the number of matvecs `Φ` computes on `(A, b)` before halting, `⊤` if it
never halts (§6, p.16). -/
noncomputable def numMatvecs (Φ : DetMatvecAlg n) (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : Φ.HaltsWithin A b k), (k : ℕ∞)

/-- `Φ` only queries `x ↦ A x`, never `y ↦ Aᵀ y` ("deterministic matvecs with A", Theorem 2.3). -/
def OnlyMulA (Φ : DetMatvecAlg n) : Prop :=
  ∀ (b : Fin n → ℝ) (T : List (Entry n)) (s : Side) (v : Fin n → ℝ),
    Φ.next b T = some (s, v) → s = Side.mulA

end DetMatvecAlg

end SmoothBerr.Supplement


