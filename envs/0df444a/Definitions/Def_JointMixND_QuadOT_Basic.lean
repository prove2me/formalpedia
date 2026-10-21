-- Prove2me | Definitions.Def_JointMixND_QuadOT_Basic
-- name    : JointMixND_QuadOT_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:33.149819+00:00
-- url     : https://prove2.me/theorems/77c781e4-e218-40f4-9e89-6ea316d0ebe1
-- title:
--   Defs. 1(i), 1(vi), 2, pp. 4, 6, 9, 27 — couplings of F, joint mix, NCD, correlation matrix P*_n, exchangeability, n-complete mixability, symmetrization
-- statement:
--   Throughout, $n$ is the number of components, $[n]=\{1,\dots,n\}$, and $F$ is a distribution on $\mathbb R$. A random vector $\mathbf X=(X_1,\dots,X_n)$ is represented by its law $P$, a probability measure on $\mathbb R^n$; every notion below depends on $\mathbf X$ only through $P$.
--
--   1. **Coupling of $F$.** $P$ is a probability measure on $\mathbb R^n$ each of whose one-dimensional marginals equals $F$, i.e. $X_i\sim F$ for every $i\in[n]$.
--   2. **Joint mix** (Definition 1(vi)). $\mathbf X$ is a joint mix (JM) if $\sum_{i=1}^n X_i=c$ almost surely for some constant $c\in\mathbb R$.
--   3. **Negative correlation dependence** (Definition 1(i)). $\mathbf X$ is NCD if $\operatorname{Cov}(X_i,X_j)\le 0$ for all $i,j\in[n]$ with $i\neq j$.
--   4. **Correlation matrix $P^*_n$.** For a vector with identical marginals $F$, "correlation matrix $P^*_n$" (the matrix with diagonal $1$ and off-diagonal entries $-1/(n-1)$) is expressed through covariances:
--   $$\operatorname{Cov}(X_i,X_j)=-\frac{\operatorname{Var}(F)}{n-1}\qquad (i\neq j).$$
--   5. **Exchangeability** (p. 6). $\mathbf X$ is exchangeable if $\mathbf X\overset{d}{=}\mathbf X_\pi$ for every permutation $\pi$ of $[n]$, where $\mathbf X_\pi=(X_{\pi(1)},\dots,X_{\pi(n)})$.
--   6. **$n$-complete mixability** (Definition 2). $F$ is $n$-completely mixable if the $n$-tuple $(F,\dots,F)$ is jointly mixable, i.e. some joint mix has all marginals equal to $F$.
--   7. **Symmetrization.** If $\Pi$ is uniform on the permutation group $\mathfrak S_n$ and independent of $\mathbf X\sim P$, the law of $\mathbf X^\Pi=(X_{\Pi(1)},\dots,X_{\Pi(n)})$ is
--   $$\frac1{n!}\sum_{\pi\in\mathfrak S_n}\operatorname{law}(\mathbf X_\pi).$$
--
--   These are the objects in which the paper's §4 results on the multi-marginal problem are stated: the minimizers of the quadratic problems are characterized as NCD joint mixes with correlation matrix $P^*_n$.
--
--   **Formalization Note** Components are 0-based: the paper's $X_i$ is the coordinate `x (i-1)` of a point `x : Fin n → ℝ`. Random vectors are represented by their laws `P : Measure (Fin n → ℝ)`. "Correlation matrix $P^*_n$" is written in covariance form `Cov(X_i,X_j) = -Var(F)/(n-1)`, which agrees with the correlation form whenever $\operatorname{Var}(F)>0$ and stays meaningful when $\operatorname{Var}(F)=0$ (Theorem 4 allows it). `IsCoupling` includes that `P` is a probability measure. Covariances and variances are Mathlib's `covariance` and `variance`; theorems using them carry the finite second moment of $F$ explicitly.
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 4, Definitions 1(i), 1(vi) and 2; p. 6 (exchangeability); p. 9 (P*_n); p. 27, Proof of Proposition 5 (X^Π)

import Mathlib

namespace JointMixND.QuadOT

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- `P` is the law of a random vector `(X_1, …, X_n)` with `X_i ∼ F` for every `i`
(components are 0-based: the paper's `X_i` is the coordinate `x (i-1)`). -/
def IsCoupling {n : ℕ} (F : Measure ℝ) (P : Measure (Fin n → ℝ)) : Prop :=
  IsProbabilityMeasure P ∧ ∀ i : Fin n, P.map (fun x => x i) = F

/-- Definition 1(vi), p. 4: `X` is a joint mix if `∑_{i=1}^n X_i = c` a.s. for some constant `c ∈ ℝ`. -/
def IsJointMix {n : ℕ} (P : Measure (Fin n → ℝ)) : Prop :=
  ∃ c : ℝ, ∀ᵐ x ∂P, ∑ i, x i = c

/-- Definition 1(i), p. 4: `X` is negative correlation dependent (NCD) if
`Cov(X_i, X_j) ≤ 0` for all `i ≠ j`. -/
def IsNCD {n : ℕ} (P : Measure (Fin n → ℝ)) : Prop :=
  ∀ i j : Fin n, i ≠ j → covariance (fun x => x i) (fun x => x j) P ≤ 0

/-- "Correlation matrix `P*_n`" (p. 9) for a law with identical marginals `F`, in covariance form:
every off-diagonal covariance equals `-Var(F)/(n-1)` (the diagonal is `Var(F)` automatically). -/
def HasCorrPstar {n : ℕ} (F : Measure ℝ) (P : Measure (Fin n → ℝ)) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    covariance (fun x => x i) (fun x => x j) P = -(variance id F) / ((n : ℝ) - 1)

/-- p. 6: `X` is exchangeable if `X =d X_π` for every permutation `π`, where
`X_π = (X_{π(1)}, …, X_{π(n)})`, i.e. the vector `x ∘ π`. -/
def IsExchangeable {n : ℕ} (P : Measure (Fin n → ℝ)) : Prop :=
  ∀ π : Equiv.Perm (Fin n), P.map (fun x => x ∘ π) = P

/-- Definition 2, p. 4: `F` is `n`-completely mixable if some random vector with all
marginals `F` is a joint mix. -/
def CompletelyMixable (n : ℕ) (F : Measure ℝ) : Prop :=
  ∃ P : Measure (Fin n → ℝ), IsCoupling F P ∧ IsJointMix P

/-- The law of `X^Π = (X_{Π(1)}, …, X_{Π(n)})`, where `Π` is uniform on the permutations of `[n]`
and independent of `X ∼ P` (proofs of Proposition 5 and Theorem 4, p. 27). -/
noncomputable def symmetrize {n : ℕ} (P : Measure (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  ((Nat.factorial n : ℝ≥0∞)⁻¹) • ∑ π : Equiv.Perm (Fin n), P.map (fun x => x ∘ π)

end JointMixND.QuadOT


