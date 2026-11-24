-- Prove2me | Definitions.Def_SparseLpLq_SmallP_Supplement_Constants
-- name    : SparseLpLq_SmallP_Supplement_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:08:39.932359+00:00
-- url     : https://prove2.me/theorems/f090deda-6fe8-4643-a1bc-7c110593979e
-- title:
--   (2.6)–(2.9), pp. 9–10 (corrected: λ* in r replaced by λ̂) — λ*, the corrected λ̂ and r, r̃, the p = 0 optimal value s, and the threshold p*
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $\sigma\ge0$. These are the constants of Theorem 2.3.
--
--   1. $\lambda^*$ is the smallest nonzero eigenvalue of $A^\top A$ (as printed in (2.6)). The corrected constant is
--   $$\hat\lambda:=\min\big\{\lambda_{\min}(A_{\mathcal I}^\top A_{\mathcal I}) : \emptyset\ne\mathcal I\subseteq\{1,\dots,n\},\ \operatorname{rank}A_{\mathcal I}=|\mathcal I|\big\},$$
--   the least eigenvalue of $A_{\mathcal I}^\top A_{\mathcal I}$ minimized over the nonempty column subsets $\mathcal I$ for which $A_{\mathcal I}$ has full column rank, and
--   $$r:=\frac{\sigma+\|b\|_2}{\sqrt{\hat\lambda}}. \tag{2.6, corrected}$$
--   When $A$ has full column rank, $\hat\lambda=\lambda^*$ and $r$ is the printed constant.
--   2. With $\mathrm{EXT}(\cdot)$ the set of extreme points and $\mathbb P_j$ the closed orthants (2.2),
--   $$\tilde r:=\min\Big\{|x_i| : x\in\bigcup_{j=1}^{2^n}\mathrm{EXT}\big(\mathbb P_j\cap\mathrm{FEA}(A,b,\sigma,1)\big),\ x_i\neq0,\ 1\le i\le n\Big\}. \tag{2.7}$$
--   3. $s$ is the optimal objective value of problem (1.4) with $p=0$, the least $\|x\|_0$ over $\mathrm{FEA}(A,b,\sigma,1)$.
--   4. The threshold
--   $$p^*:=\min\Big\{1,\ \frac{\ln(s+1)-\ln s}{\ln r-\ln\tilde r}\Big\}. \tag{2.9}$$
--
--   Under the paper's blanket assumptions ($\mathrm{FEA}(A,b,\sigma,1)\neq\emptyset$, $\|b\|_1>\sigma$) one has $A\ne0$, $s\ge1$ and $r\ge\tilde r>0$.
--
--   **Formalization Note** The paper's step (2.8) uses $\lambda_{\min}(A_{\mathcal I}^\top A_{\mathcal I})\ge\lambda^*$ for every full-column-rank $A_{\mathcal I}$, which is false when $A$ has dependent columns; with the printed $\lambda^*$ Theorem 2.3 fails (counterexample in the theorem item). The constant $r$ is therefore built from $\hat\lambda$ (`lamHat`), exactly the bound that step needs; the printed $\lambda^*$ is kept as `lamStar`. $\hat\lambda$, $\lambda^*$, $\tilde r$ and $s$ are written as infima (`sInf`) of sets that are finite and nonempty under the blanket assumptions, so each infimum is a minimum. When $r=\tilde r$ the quotient in (2.9) has a positive numerator and a zero denominator; it is read as $+\infty$, so $p^*=1$ (the proof on p. 10 treats this case as (2.10) holding for every $p\in(0,1)$); without this convention Lean's $x/0=0$ would give $p^*=0$. Orthants are indexed by sign patterns, as in the base mission.
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 9, (2.6)–(2.7); p. 10, (2.9) and Theorem 2.3 (definition of s); p. 7, EXT

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting

open scoped ENNReal Matrix Topology

namespace SparseLpLq.SmallP.Supplement

open SparseLpLq.SmallP

/-! ### Constants of Theorem 2.3 (pp. 9–10) -/

/-- `λ*` of (2.6) as printed: the smallest nonzero eigenvalue of `AᵀA` (the infimum of the finite
set of nonzero points of the spectrum of the symmetric matrix `AᵀA`). Kept for reference: with it
Theorem 2.3 is false (see `DISPROOF.md`); `rConst` uses the corrected `lamHat`. -/
noncomputable def lamStar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sInf {μ : ℝ | μ ∈ spectrum ℝ (Aᵀ * A) ∧ μ ≠ 0}

/-- Corrected constant `λ̂ := min {λ_min(A_ℐᵀA_ℐ) : ∅ ≠ ℐ ⊆ {1,…,n}, A_ℐ has full column rank}`:
the smallest of the least eigenvalues of `A_ℐᵀA_ℐ` over the nonempty column subsets `ℐ` with
`rank A_ℐ = |ℐ|`. The proof of (2.8) on p. 9 needs `λ_min(A_ℐᵀA_ℐ) ≥ λ*` for every such `ℐ`, which
fails for the printed `λ*` (smallest nonzero eigenvalue of `AᵀA`) when `A` has dependent columns
(see `DISPROOF.md`); `λ̂` is exactly the quantity that step uses. When `A` has full column rank,
`λ̂ = λ*` (Cauchy interlacing, with equality at `ℐ = {1,…,n}`). -/
noncomputable def lamHat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sInf {μ : ℝ | ∃ I : Finset (Fin n), I.Nonempty ∧
    (Matrix.of (fun i (j : I) => A i j)).rank = I.card ∧
    μ = sInf (spectrum ℝ ((Matrix.of (fun i (j : I) => A i j))ᵀ * Matrix.of (fun i (j : I) => A i j)))}

/-- `r := (σ + ‖b‖₂)/√λ̂`: the constant (2.6) with the printed `λ*` replaced by the corrected `λ̂`
(`lamHat`), so that (2.8) `‖x*‖_∞ ≤ r` holds for every `x* ∈ SOL(A,b,σ,p,1)`, `0 ≤ p < 1`. -/
noncomputable def rConst {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ) : ℝ :=
  (σ + qNorm 2 b) / Real.sqrt (lamHat A)

/-- `r̃` of (2.7): the smallest nonzero `|xᵢ|` over all extreme points `x` of all the pieces
`ℙ_j ∩ FEA(A,b,σ,1)` (`EXT` is `Set.extremePoints ℝ`; orthants are indexed by sign patterns). -/
noncomputable def rTilde {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ) : ℝ :=
  sInf {t : ℝ | ∃ (s : Fin n → Bool) (x : Fin n → ℝ) (i : Fin n),
    x ∈ Set.extremePoints ℝ (orthant s ∩ FEA A b σ 1) ∧ x i ≠ 0 ∧ t = |x i|}

/-- `s`: the optimal objective value of problem (1.4) with `p = 0`, i.e. the least `‖x‖₀` over
`FEA(A,b,σ,1)` (an infimum of a nonempty set of natural numbers when the feasible set is
nonempty, hence attained). -/
noncomputable def sOpt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ) : ℝ :=
  sInf (lpObj 0 '' FEA A b σ 1)

/-- `p* := min{1, (ln(s+1) − ln s)/(ln r − ln r̃)}` of (2.9). When `r = r̃` the quotient has a
zero denominator and a positive numerator; it is read as `+∞`, so `p* = 1` (the proof on p. 10
treats this case as (2.10) holding for every `p ∈ (0,1)`). -/
noncomputable def pStar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ) : ℝ :=
  if rConst A b σ = rTilde A b σ then 1
  else min 1 ((Real.log (sOpt A b σ + 1) - Real.log (sOpt A b σ)) /
    (Real.log (rConst A b σ) - Real.log (rTilde A b σ)))

end SparseLpLq.SmallP.Supplement


