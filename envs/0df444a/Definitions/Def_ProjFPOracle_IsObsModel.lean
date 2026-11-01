-- Prove2me | Definitions.Def_ProjFPOracle_IsObsModel
-- name    : ProjFPOracle_IsObsModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:42.379119+00:00
-- url     : https://prove2.me/theorems/e4467b9c-2341-47bf-8a1f-f8694f9f7874
-- title:
--   The i.i.d. unbiased observation model in projected coordinates
-- statement:
--   The data of the problem are i.i.d. random pairs $(L_i,b_i)$, $i=1,2,\dots$, of operators and vectors that are unbiased for $(L,b)$:
--   $$
--   \mathbb E[L_i]=L,\qquad \mathbb E[b_i]=b .
--   $$
--   The algorithm and all the bounds use them only through the projected observations
--   $$
--   A_i:=\Phi_d L_i\Phi_d^*\in\mathbb R^{d\times d},\qquad h_i:=\Phi_d b_i\in\mathbb R^d .
--   $$
--   This definition states the model directly for these: on a probability space $(\Omega,\mathbb P)$,
--
--   1. the pairs $(A_i,h_i)$, $i\ge1$, are mutually independent and identically distributed random elements of $\mathbb R^{d\times d}\times\mathbb R^d$ (within a pair, $A_i$ and $h_i$ may be dependent);
--   2. every entry of $A_i$ and of $h_i$ is square-integrable;
--   3. $\mathbb E[A_i]=M$ and $\mathbb E[h_i]=m$ entrywise.
--
--   The mission uses it with $M=\Phi_dL\Phi_d^*$ and $m=\Phi_d b$; any paper instance $(L_i,b_i)$ produces such pairs.
--
--   **Formalization Note** The observations form an infinite sequence indexed from $1$ (index $0$ is unused); an estimate from $n$ samples uses the first $n$. Matrices are passed to Mathlib's independence and identical-distribution predicates as their entry functions. Square-integrability is implied by the paper's second-moment bounds (11) and makes those bounds and the covariances meaningful.
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, §2.1, p.7, Eq. (10), and §3.1, p.12, Eq. (25)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ProjFPOracle

/-- **The i.i.d. unbiased observation model, in projected coordinates** (Mou, Pananjady &
Wainwright, *Optimal Oracle Inequalities for Projected Fixed-Point Equations*,
arXiv:2012.05299v1, Eq. (10), p.7, and Eq. (25), p.12): "we observe i.i.d. random pairs
`(L_i, b_i)` for `i = 1, …, n` that are unbiased estimates of the pair `(L, b)`", and the
algorithm sees them only through `A_i := Φ_d L_i Φ_d^* ∈ ℝ^{d×d}` and `h_i := Φ_d b_i ∈ ℝ^d`.

`IsObsModel P A h M m` says that, on the probability space `(Ω, P)`, the pairs
`(A_i, h_i)`, `i = 1, 2, …`, are independent and identically distributed random elements of
`ℝ^{d×d} × ℝ^d`, every entry is square-integrable, and `E[A_i] = M`, `E[h_i] = m` entrywise. The
mission uses it with `M = Φ_d L Φ_d^*` and `m = Φ_d b`.

**Formalization Note** The observations form an infinite sequence indexed from `1`; an estimate
from `n` samples uses the first `n` of them, and index `0` is not used. Independence and identical
distribution are of the *pairs* `(A_i, h_i)`: `A_i` and `h_i` may be dependent. A matrix is passed
to `iIndepFun`/`IdentDistrib` as its entry function `Matrix.of.symm (A i ω) : Fin d → Fin d → ℝ`
(Mathlib has no measurable structure on `Matrix`). Square-integrability (`MemLp · 2`) makes the
second moments of Assumption 1(W) and the covariances meaningful; the paper's bound (11) implies
it. -/
structure IsObsModel {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (h : ℕ → Ω → Fin d → ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (m : Fin d → ℝ) : Prop where
  /-- `P` is a probability measure. -/
  isProbability : IsProbabilityMeasure P
  /-- Each observation is a random variable. -/
  measurable_A : ∀ i, 1 ≤ i → Measurable fun ω => Matrix.of.symm (A i ω)
  measurable_h : ∀ i, 1 ≤ i → Measurable (h i)
  /-- The pairs `(A_i, h_i)`, `i = 1, 2, …`, are mutually independent. -/
  indep : iIndepFun (fun (i : ℕ) ω => (Matrix.of.symm (A (i + 1) ω), h (i + 1) ω)) P
  /-- The pairs `(A_i, h_i)`, `i ≥ 1`, are identically distributed. -/
  identDistrib : ∀ i, 1 ≤ i →
    IdentDistrib (fun ω => (Matrix.of.symm (A i ω), h i ω))
      (fun ω => (Matrix.of.symm (A 1 ω), h 1 ω)) P P
  /-- Every entry is square-integrable. -/
  memLp_A : ∀ i, 1 ≤ i → ∀ j k, MemLp (fun ω => A i ω j k) 2 P
  memLp_h : ∀ i, 1 ≤ i → ∀ j, MemLp (fun ω => h i ω j) 2 P
  /-- Unbiasedness, Eq. (10): `E[A_i] = M` and `E[h_i] = m`, entrywise. -/
  mean_A : ∀ i, 1 ≤ i → ∀ j k, ∫ ω, A i ω j k ∂P = M j k
  mean_h : ∀ i, 1 ≤ i → ∀ j, ∫ ω, h i ω j ∂P = m j

end ProjFPOracle


