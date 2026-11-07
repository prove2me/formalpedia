-- Prove2me | Definitions.Def_SmoothBerr_PairedMatvecAlg
-- name    : SmoothBerr_PairedMatvecAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:00.993695+00:00
-- url     : https://prove2.me/theorems/b0c4c9f9-00b2-4427-84cd-58e6dde142c7
-- title:
--   Randomized adaptive paired matrix-vector product algorithm
-- statement:
--   In the **matrix-vector product (matvec) model** an algorithm may access an $n\times n$ matrix $M$ only through products $x\mapsto Mx$ and $x\mapsto M^\top x$. A **paired matvec algorithm** with $t$ steps does both at every step: at step $k=1,\dots,t$ it submits a left query $u_k$ and a right query $v_k$ and receives
--   $$
--   (u_k,v_k)\ \longrightarrow\ \text{oracle}\ \longrightarrow\ (M^\top u_k,\ Mv_k).
--   $$
--   The algorithm receives an input $x$ (for instance a right-hand side $b$) and a random seed $\omega$. The queries are **adaptive**: $(u_k,v_k)$ is a function of $x$, $\omega$ and the answers $(M^\top u_i,Mv_i)_{i<k}$ to the earlier queries. After $t$ steps the algorithm returns an output computed from $x$, $\omega$ and all $t$ answers. The **transcript** of a run is
--   $$
--   \mathcal T_t=(u_i,\ M^\top u_i,\ v_i,\ Mv_i)_{i=1}^t .
--   $$
--   The run depends on $M$ only through the answers, which is what makes this a model of computation for lower bounds.
--
--   The structure also carries the run (`answersUpTo`, `answers`), the queries, the transcript and the output (`run`) of the algorithm against a given matrix.
--
--   **Formalization Note** The algorithm performs exactly $t$ paired steps; an algorithm using at most $t$ steps is one that ignores its last answers. For each fixed input, the query maps and the output map are required to be measurable jointly in the seed and the answers, which is what "with probability" presupposes. Steps are indexed from $0$ to $t-1$.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), §5, p.9 (paired matvec algorithm, (u_t, v_t) → oracle → (A^⊤u_t, Av_t)); §2, p.2 (matrix-vector product model); Theorem 5.1, p.9 (transcript T_t)

import Mathlib

open MeasureTheory Matrix

namespace SmoothBerr

/-- One answer of the paired matvec oracle: the pair `(Mᵀu, Mv)` for a query `(u, v)`. -/
abbrev Answer (n : ℕ) : Type := (Fin n → ℝ) × (Fin n → ℝ)

/-- One entry `(u_i, Mᵀu_i, v_i, Mv_i)` of a transcript of paired matvecs. -/
abbrev TranscriptEntry (n : ℕ) : Type := (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)

/-- A **randomized adaptive paired matvec algorithm** with `t` steps (Dereziński, Mahoney, Meyer,
Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*,
manuscript of 3 Nov 2026, sha256 9575cd20…, §5, p.9: "a paired matvec algorithm, which at every
timestep computes a matvec with both A and A^⊤: (u_t, v_t) → oracle → (A^⊤u_t, Av_t)"; §2, p.2:
the matrix-vector product model, where an algorithm interacts with the input matrix "only through
implicit queries of the form x ↦ Ax and x ↦ A^⊤x").

The algorithm receives an input `x : ι` (the right-hand side `b`, or nothing) and a random seed
`ω : Ω`. At step `k` (`0 ≤ k < t`) it submits a left query `u_k` and a right query `v_k`, chosen
as a function of the input, the seed and the answers `(Mᵀu_i, Mv_i)` to the earlier queries
`i < k`; after `t` steps it returns `output x ω (answers)`. The matrix `M` is accessed only
through the answers (see `answersUpTo`).

**Formalization Note** The algorithm performs exactly `t` paired steps; an algorithm with at
most `t` steps is one that ignores its remaining answers. The seed is drawn from a probability
measure on `Ω` chosen together with the algorithm and independent of the matrix. For each fixed
input, the query and output maps are measurable jointly in the seed and the answers (the
measurability that "with probability" presupposes); no measurability in the input is required. -/
structure PairedMatvecAlg (n t : ℕ) (ι Ω β : Type*) [MeasurableSpace Ω] [MeasurableSpace β] where
  /-- The `k`-th query `(u_k, v_k)` from the input, the seed and the `k` earlier answers. -/
  query : (k : Fin t) → ι → Ω → (Fin k → Answer n) → Answer n
  /-- The output, from the input, the seed and all `t` answers. -/
  output : ι → Ω → (Fin t → Answer n) → β
  /-- Each query map is jointly measurable in the seed and the earlier answers. -/
  measurable_query : ∀ (k : Fin t) (x : ι),
    Measurable fun p : Ω × (Fin k → Answer n) => query k x p.1 p.2
  /-- The output map is jointly measurable in the seed and the answers. -/
  measurable_output : ∀ x : ι, Measurable fun p : Ω × (Fin t → Answer n) => output x p.1 p.2

namespace PairedMatvecAlg

variable {n t : ℕ} {ι Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]

/-- The answers `(Mᵀu_i, Mv_i)_{i<k}` to the first `k` queries of a run of `alg` against the
matrix `M` on input `x` with seed `ω`; query `i` is computed from the answers before `i`. -/
noncomputable def answersUpTo (alg : PairedMatvecAlg n t ι Ω β) (M : Matrix (Fin n) (Fin n) ℝ)
    (x : ι) (ω : Ω) : (k : ℕ) → k ≤ t → (Fin k → Answer n)
  | 0, _ => Fin.elim0
  | k + 1, h =>
    let prev := answersUpTo alg M x ω k (Nat.le_of_succ_le h)
    let q := alg.query ⟨k, h⟩ x ω prev
    Fin.snoc (α := fun _ => Answer n) prev (Mᵀ *ᵥ q.1, M *ᵥ q.2)

/-- The `t` answers of a full run of `alg` against `M` on input `x` with seed `ω`. -/
noncomputable def answers (alg : PairedMatvecAlg n t ι Ω β) (M : Matrix (Fin n) (Fin n) ℝ)
    (x : ι) (ω : Ω) : Fin t → Answer n :=
  answersUpTo alg M x ω t le_rfl

/-- The queries `(u_k, v_k)_{k<t}` submitted during the run of `alg` against `M`. -/
noncomputable def queries (alg : PairedMatvecAlg n t ι Ω β) (M : Matrix (Fin n) (Fin n) ℝ)
    (x : ι) (ω : Ω) : Fin t → Answer n :=
  fun k => alg.query k x ω (answersUpTo alg M x ω k k.2.le)

/-- The transcript `T_t = (u_i, Mᵀu_i, v_i, Mv_i)_{i<t}` of the run of `alg` against `M`
(manuscript of 3 Nov 2026, Theorem 5.1, p.9). -/
noncomputable def transcript (alg : PairedMatvecAlg n t ι Ω β) (M : Matrix (Fin n) (Fin n) ℝ)
    (x : ι) (ω : Ω) : Fin t → TranscriptEntry n :=
  fun k => ((queries alg M x ω k).1, Mᵀ *ᵥ (queries alg M x ω k).1,
    (queries alg M x ω k).2, M *ᵥ (queries alg M x ω k).2)

/-- The output of the run of `alg` against `M` on input `x` with seed `ω`. -/
noncomputable def run (alg : PairedMatvecAlg n t ι Ω β) (M : Matrix (Fin n) (Fin n) ℝ)
    (x : ι) (ω : Ω) : β :=
  alg.output x ω (answers alg M x ω)

end PairedMatvecAlg

end SmoothBerr


