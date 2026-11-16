-- Prove2me | Definitions.Def_SmoothBerr_Supplement_RandMatvecAlg
-- name    : SmoothBerr_Supplement_RandMatvecAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:55:41.676924+00:00
-- url     : https://prove2.me/theorems/8a8edaf6-a3ee-4573-b096-2cce78c92829
-- title:
--   Randomized adaptive matvec algorithm with $t$ matvecs
-- statement:
--   A **randomized adaptive matvec algorithm with $t$ matvecs** receives the right-hand side $b$ and a random seed $\omega$ drawn from a probability law $\mu$. At each step $k=0,\dots,t-1$ it submits one vector $v_k$, chosen from $b$, $\omega$ and the earlier answers $Av_0,\dots,Av_{k-1}$, and receives $Av_k$. After $t$ steps it returns a vector computed from $b$, $\omega$ and all answers.
--
--   This is the algorithm class of the lower bounds for symmetric and positive definite systems (Theorems 2.3 and 9.2).
--
--   **Formalization Note** Exactly $t$ single matvecs (an algorithm with fewer ignores its last answers). Only $v\mapsto Av$ is queried, since $A^\top v=Av$ on the symmetric inputs considered. For each fixed $b$ the query and output maps are measurable jointly in the seed and the answers, which is what a success probability presupposes. It is the single-matvec counterpart of the published paired model `SmoothBerr.PairedMatvecAlg`, in which each step costs two matvecs.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), §2, p.2; Imported Theorem 9.1 and Theorem 9.2, p.24

import Mathlib

open MeasureTheory Matrix

namespace SmoothBerr.Supplement

/-- A **randomized adaptive matvec algorithm with `t` matvecs** for `n × n` systems (Dereziński,
Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive
perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, §2, p.2; Imported Theorem 9.1 and
Theorem 9.2, p.24: "a (possibly randomized) algorithm that is given a vector b, computes t matvecs
with any symmetric matrix A").

The algorithm receives the right-hand side `b` and a random seed `ω : Ω`. At step `k`
(`0 ≤ k < t`) it submits one vector `v_k`, a function of `b`, `ω` and the answers `A v_i` to the
earlier queries `i < k`, and receives `A v_k`; after `t` steps it returns
`output b ω (answers)`.

**Formalization Note** Exactly `t` single matvecs (an algorithm with fewer ignores its last
answers). Only `v ↦ A v` is queried: on the symmetric inputs of Theorems 2.3 and 9.2,
`Aᵀ v = A v`. The seed law is a probability measure on `Ω` chosen with the algorithm. For each fixed
`b`, queries and output are measurable jointly in the seed and the answers. This is the
single-matvec counterpart of the published `SmoothBerr.PairedMatvecAlg` (where each step is two
matvecs). -/
structure RandMatvecAlg (n t : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- The `k`-th query vector from `b`, the seed and the `k` earlier answers. -/
  query : (k : Fin t) → (Fin n → ℝ) → Ω → (Fin k → (Fin n → ℝ)) → (Fin n → ℝ)
  /-- The returned vector from `b`, the seed and all `t` answers. -/
  output : (Fin n → ℝ) → Ω → (Fin t → (Fin n → ℝ)) → (Fin n → ℝ)
  /-- Each query map is jointly measurable in the seed and the earlier answers. -/
  measurable_query : ∀ (k : Fin t) (b : Fin n → ℝ),
    Measurable fun p : Ω × (Fin k → (Fin n → ℝ)) => query k b p.1 p.2
  /-- The output map is jointly measurable in the seed and the answers. -/
  measurable_output : ∀ b : Fin n → ℝ,
    Measurable fun p : Ω × (Fin t → (Fin n → ℝ)) => output b p.1 p.2

namespace RandMatvecAlg

variable {n t : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The answers `A v_0, …, A v_{k−1}` of the first `k` steps of a run against `A` on `b` with
seed `ω`. -/
def answersUpTo (alg : RandMatvecAlg n t Ω) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (ω : Ω) : (k : ℕ) → k ≤ t → (Fin k → (Fin n → ℝ))
  | 0, _ => Fin.elim0
  | k + 1, h =>
    let prev := answersUpTo alg A b ω k (Nat.le_of_succ_le h)
    Fin.snoc (α := fun _ => Fin n → ℝ) prev (A *ᵥ alg.query ⟨k, h⟩ b ω prev)

/-- The vector returned by the run of `alg` against `A` on `b` with seed `ω`. -/
def run (alg : RandMatvecAlg n t Ω) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (ω : Ω) :
    Fin n → ℝ :=
  alg.output b ω (answersUpTo alg A b ω t le_rfl)

end RandMatvecAlg

end SmoothBerr.Supplement


