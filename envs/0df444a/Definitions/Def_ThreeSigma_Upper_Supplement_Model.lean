-- Prove2me | Definitions.Def_ThreeSigma_Upper_Supplement_Model
-- name    : ThreeSigma_Upper_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:15:09.623748+00:00
-- url     : https://prove2.me/theorems/a5958f72-4376-48ba-ad0b-bbbdbc79d943
-- title:
--   Sign-vector averages, Hadamard matrices, disc(A), $D_n^\pm$ and the matrix $[H\mid R]$
-- statement:
--   Fix $\delta:=2^{-22}$. For a finite index set $\iota$, let $\{-1,1\}^\iota$ be the set of sign vectors and, for $\varepsilon$ uniform on it, write
--   $$\mathbb E[f(\varepsilon)]=2^{-|\iota|}\sum_{x\in\{-1,1\}^\iota}f(x),\qquad \mathbb P[P(\varepsilon)]=2^{-|\iota|}\,\#\{x\in\{-1,1\}^\iota: P(x)\}.$$
--   A **Hadamard matrix** of order $n$ is $H\in\{-1,1\}^{n\times n}$ with $H^\top H=nI_n$. For $A\in\mathbb R^{d\times n}$, the **discrepancy** is
--   $$\operatorname{disc}(A)=\min_{x\in\{-1,1\}^n}\|Ax\|_\infty,\qquad D_n^\pm=\max_{A\in\{-1,1\}^{n\times n}}\frac{\operatorname{disc}(A)}{\sqrt n}.$$
--   Given a matrix $H_0$ of order $n$, a set $S$ of column indices and a sign matrix $R\in\{-1,1\}^{n\times S}$, the matrix $A=[H\mid R]$ of Theorem 1.1 has entry $R_{ij}$ in the columns $j\in S$ and $(H_0)_{ij}$ elsewhere.
--
--   These are the objects of the lower bound (§1–§2): the random-sign averages used in Lemmas 2.1–2.3 and the Claim, and the discrepancy quantities of Theorem 1.1.
--
--   **Formalization Note** Sign vectors are real-valued functions with every value $\pm1$. The sup norm on $\mathbb R^d$ is Mathlib's norm on `Fin d → ℝ` (zero when $d=0$). The minimum and maximum are infima/suprema over finite nonempty sets. The replaced columns stay in place instead of being moved to the right; the discrepancy does not depend on column order. At $n=0$ the division by $\sqrt n$ is Lean's total division and gives $0$.
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), §1 (definitions of disc, D_n^±, Hadamard matrix) p. 1; δ and Theorem 1.1's A = [H | R] p. 2 and p. 4, p. 1–4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf (SHA-256 3be06ff7fede4a6b259a8de8615176523f985a50a464328e2179c71e52153940)

import Mathlib

namespace ThreeSigma.Upper.Supplement

/-- δ := 2^{-22}, fixed throughout §2 (p. 2). -/
noncomputable def delta : ℝ := 1 / 2 ^ 22

/-- The sign vectors {−1,1}^ι, as real-valued functions on the finite index type ι. -/
noncomputable def signVectors (ι : Type*) [Fintype ι] [DecidableEq ι] : Finset (ι → ℝ) :=
  Fintype.piFinset fun _ => ({-1, 1} : Finset ℝ)

/-- 𝔼[f(ε)] for ε uniform on {−1,1}^ι: the average of f over all 2^|ι| sign vectors. -/
noncomputable def uniformAvg {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ) : ℝ :=
  (∑ x ∈ signVectors ι, f x) / ((signVectors ι).card : ℝ)

open Classical in
/-- ℙ[P(ε)] for ε uniform on {−1,1}^ι: the fraction of sign vectors satisfying P. -/
noncomputable def uniformProb {ι : Type*} [Fintype ι] [DecidableEq ι] (P : (ι → ℝ) → Prop) : ℝ :=
  (((signVectors ι).filter P).card : ℝ) / ((signVectors ι).card : ℝ)

/-- A Hadamard matrix of order n: entries in {−1,1} and HᵀH = n·I (p. 1). -/
def IsHadamard {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧ H.transpose * H = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- disc(A) := min over x ∈ {−1,1}^n of ‖Ax‖∞ (p. 1). The norm on `Fin d → ℝ` is the sup
norm max_i |(Ax)_i| (zero when d = 0); the infimum is over a finite nonempty set. -/
noncomputable def disc {d n : ℕ} (A : Fin d → Fin n → ℝ) : ℝ :=
  ⨅ x : {x // x ∈ signVectors (Fin n)}, ‖(fun i => ∑ j, A i j * (x : Fin n → ℝ) j : Fin d → ℝ)‖

/-- D_n^± := max over A ∈ {−1,1}^{n×n} of disc(A)/√n (p. 1); the supremum is over a finite
nonempty set. -/
noncomputable def Dpm (n : ℕ) : ℝ :=
  ⨆ A : {A : Fin n → Fin n → ℝ // ∀ i j, A i j = 1 ∨ A i j = -1}, disc A.1 / Real.sqrt n

/-- The matrix A = [H | R] of Theorem 1.1: the columns of H0 in S are replaced by the
entries of the random sign matrix R; the other columns are those of H0 (p. 2, p. 4). -/
noncomputable def replaceCols {n : ℕ} (H0 : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (R : Fin n × {j // j ∈ S} → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if h : j ∈ S then R (i, ⟨j, h⟩) else H0 i j

end ThreeSigma.Upper.Supplement


