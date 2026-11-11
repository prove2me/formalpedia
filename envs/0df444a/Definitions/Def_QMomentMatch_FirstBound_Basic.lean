-- Prove2me | Definitions.Def_QMomentMatch_FirstBound_Basic
-- name    : QMomentMatch_FirstBound_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T18:59:04.954799+00:00
-- url     : https://prove2.me/theorems/630a06d4-4796-42f2-9c04-f83b4297d100
-- title:
--   Frequency statistics, moments, mean-one normalization (4), proportional moments (7), product laws and piecewise-$C^1$ paths
-- statement:
--   This file fixes the probabilistic vocabulary of the paper. Throughout, $A\ge 1$ is an integer and $S=\{0\}\cup[A]=\{0,1,\dots,A\}$ is the set of possible multiplicities.
--
--   1. A **probability vector** on a finite set $\Omega$ is $p:\Omega\to\mathbb R$ with $p(a)\ge 0$ for all $a$ and $\sum_a p(a)=1$.
--   2. The **$j$-th moment** of a law $p$ on $S$ is $\mathbb E[Z^j]=\sum_{s=0}^{A}p(s)\,s^j$.
--   3. **Positive frequency statistics supported on $[A]$** are a law $X$ on $\{1,\dots,A\}$; it is written as a law on $S$ with $\Pr[X=0]=0$.
--   4. The associated **mean-one frequency statistics** $Z$ of $X$ (eq. (4)), with $\mu=\mathbb E[X]$:
--   $$\Pr[Z=a]=\frac{\Pr[X=a]}{\mu}\quad(a\in[A]),\qquad \Pr[Z=0]=1-\frac1\mu .$$
--   5. The **proportional-moment condition** (7) for an integer $r$: for every $1\le j\le r-1$,
--   $$\frac{\mathbb E[X_1]}{\mathbb E[X_0]}=\frac{\mathbb E[X_1^j]}{\mathbb E[X_0^j]} .$$
--   6. The **product expectation** $\mathbb E_{z\sim\pi^{\otimes n}}[g(z)]=\sum_{z\in S^n}\big(\prod_{i}\pi(z_i)\big)g(z)$.
--   7. For $w\in S^{m-1}$ and $s\in S$, $(w,s)\in S^m$ is $w$ with $s$ appended as last coordinate.
--   8. A **continuous, piecewise $C^1$ path of probability distributions** on a finite set $S$ is $u\mapsto\pi_u$ such that every $\pi_u$, $u\in[0,1]$, is a probability vector, each coordinate $u\mapsto\pi_u(s)$ is continuous on $[0,1]$, and there is a partition $0=t_0<t_1<\dots<t_k=1$ such that each coordinate is continuously differentiable on every closed piece $[t_i,t_{i+1}]$ (one-sided derivatives at the ends).
--
--   These are the objects of §2.1–2.2 and §3.2 that every statement of the mission is phrased in.
--
--   **Formalization Note** $S$ is `Fin (A + 1)`, the element `s` standing for the integer `(s : ℕ)`. Since $\Pr[X=a]\ge 0$ is supported on $a\ge1$, $\mu\ge 1$, so the divisions in (4) and (7) never divide by zero for positive frequency statistics. A path is a function `ℝ → S → ℝ`; only its values on $[0,1]$ matter.
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), §2.1 eq. (4) p. 12, §2.2 p. 13, Theorem 2.5 eq. (7) p. 14, §3.2 pp. 18–19

import Mathlib

/-!
# Frequency statistics, moments, product laws and probability paths

Kayal, Magniez, Sen, Szabó, *Quantum Query Lower Bounds from Classical Moment Matching*,
STOC 2027 submission #564, §2.1–§2.2 (pp. 12–13) and §3.2 (pp. 18–20).

Conventions. The multiplicity set `S = {0} ∪ [A] = {0, 1, …, A}` is `Fin (A + 1)`, the element
`s` standing for the integer `(s : ℕ)`. A law on `S` is a vector `p : Fin (A + 1) → ℝ`.
-/

namespace QMomentMatch.FirstBound

/-- A probability vector on a finite set: nonnegative entries summing to one. -/
def IsProbVec {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- The `j`-th moment `E[Z^j] = ∑_{s=0}^{A} p(s) s^j` of a law `p` on `S = {0,…,A}`. -/
noncomputable def moment {A : ℕ} (p : Fin (A + 1) → ℝ) (j : ℕ) : ℝ :=
  ∑ s : Fin (A + 1), p s * ((s : ℕ) : ℝ) ^ j

/-- p. 12: "positive frequency statistics `X` supported on `[A]`": a probability distribution on
`{1,…,A}`, written as a law on `{0,…,A}` with no mass at `0`. -/
def IsPosFreqStat {A : ℕ} (X : Fin (A + 1) → ℝ) : Prop :=
  IsProbVec X ∧ X 0 = 0

/-- p. 12, eq. (4), and p. 13: the associated mean-one frequency statistics `Z`:
`Pr[Z = a] = Pr[X = a]/μ` for `a ∈ [A]` and `Pr[Z = 0] = 1 − 1/μ`, where `μ = E[X]`. -/
noncomputable def meanOne {A : ℕ} (X : Fin (A + 1) → ℝ) : Fin (A + 1) → ℝ :=
  fun s => if (s : ℕ) = 0 then 1 - 1 / moment X 1 else X s / moment X 1

/-- p. 14, eq. (7): `E[X₁]/E[X₀] = E[X₁²]/E[X₀²] = ⋯ = E[X₁^{r−1}]/E[X₀^{r−1}]`. -/
def PropMoments {A : ℕ} (X₀ X₁ : Fin (A + 1) → ℝ) (r : ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ r - 1 → moment X₁ 1 / moment X₀ 1 = moment X₁ j / moment X₀ j

/-- The expectation `E_{z ∼ π^{⊗n}}[g(z)] = ∑_{z ∈ S^n} (∏_i π(z_i)) g(z)` under the product of
`n` copies of a law `π` on `S`. -/
noncomputable def prodExp {A n : ℕ} (π : Fin (A + 1) → ℝ) (g : (Fin n → Fin (A + 1)) → ℝ) : ℝ :=
  ∑ z : Fin n → Fin (A + 1), (∏ i, π (z i)) * g z

/-- p. 18: the vector `(w, s) ∈ S^m` obtained by appending `s` to `w ∈ S^{m−1}` as last
coordinate. -/
def appendLast {α : Type*} {m : ℕ} (w : Fin (m - 1) → α) (s : α) : Fin m → α :=
  fun i => if h : (i : ℕ) < m - 1 then w ⟨i, h⟩ else s

/-- p. 18 (Lemma 3.7): a continuous, piecewise `C¹` path `(π_u)_{0 ≤ u ≤ 1}` of probability
distributions on `S`: every `π_u` with `u ∈ [0,1]` is a probability vector, each coordinate is
continuous on `[0,1]`, and there is a partition `0 = t₀ < t₁ < ⋯ < t_k = 1` such that each
coordinate is `C¹` on every closed piece `[t_i, t_{i+1}]` (one-sided derivatives at the ends). -/
def IsPiecewiseC1ProbPath {S : Type*} [Fintype S] (π : ℝ → S → ℝ) : Prop :=
  (∀ u ∈ Set.Icc (0 : ℝ) 1, IsProbVec (π u)) ∧
  (∀ s, ContinuousOn (fun u => π u s) (Set.Icc 0 1)) ∧
  ∃ (k : ℕ) (t : Fin (k + 1) → ℝ), t 0 = 0 ∧ t (Fin.last k) = 1 ∧ StrictMono t ∧
    ∀ i : Fin k, ∀ s, ContDiffOn ℝ 1 (fun u => π u s) (Set.Icc (t i.castSucc) (t i.succ))

end QMomentMatch.FirstBound


