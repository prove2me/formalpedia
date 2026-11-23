-- Prove2me | Definitions.Def_ConformalRiskControl_Basic
-- name    : ConformalRiskControl_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T20:12:10.12617+00:00
-- url     : https://prove2.me/theorems/ee1baacc-133a-468b-aebf-fa52088edcc7
-- title:
--   Conformal risk control: exchangeable monotone losses and the calibrated parameter $\hat\lambda$
-- statement:
--   Objects of Sections 1.1, 2, 4 and Appendix A of Angelopoulos, Bates, Fisch, Lei and Schuster, *Conformal Risk Control* (arXiv:2208.02814v4).
--
--   1. **Parameter set and losses.** The parameter set is a nonempty compact set $\Lambda\subset\mathbb{R}$ with $\lambda_{\max}=\sup\Lambda\in\Lambda$. A loss is a function $L:\Lambda\to\mathbb{R}$. It is *right-continuous* if at every $\lambda\in\Lambda$ it is continuous within $\Lambda\cap[\lambda,\infty)$. It satisfies eq. (5) if $\sup_{\lambda\in\Lambda}L(\lambda)\le B$ and $L(\lambda_{\max})\le\alpha$.
--   2. **Exchangeable and i.i.d. random losses.** Random losses $L_1,\dots,L_m$ on a probability space are *exchangeable* if every $L_i(\lambda)$ is a random variable and the joint law of $(L_1,\dots,L_m)$, as random elements of $\mathbb{R}^\Lambda$ with the product $\sigma$-algebra, is invariant under every permutation of the indices. They are *i.i.d.* if they are independent and identically distributed as random elements of $\mathbb{R}^\Lambda$.
--   3. **Expectation.** For a random variable $X\le B$ almost surely, $\mathbb{E}[X]=B-\mathbb{E}[B-X]\in[-\infty,B]$, where $\mathbb{E}[B-X]\in[0,\infty]$ is a (lower) Lebesgue integral of a nonnegative function. This is the usual expectation, and equals $-\infty$ when $\mathbb{E}[X^-]=\infty$.
--   4. **Conformal risk control (eq. 4).** With $\hat R_n(\lambda)=\frac1n\sum_{i=1}^nL_i(\lambda)$,
--   $$\hat\lambda=\inf\Big\{\lambda\in\Lambda:\ \tfrac{n}{n+1}\hat R_n(\lambda)+\tfrac{B}{n+1}\le\alpha\Big\},$$
--   and $\hat\lambda=\lambda_{\max}$ when the set is empty. The same convention (infimum of the empty set is $\lambda_{\max}$) is used for every parameter below.
--   5. **Jump function (Section 2.2).** $J(l,\lambda)=\lim_{\epsilon\to0^+}l(\lambda-\epsilon)-l(\lambda)$.
--   6. **Monotonization.** $\tilde f(\lambda)=\sup_{\lambda'\in\Lambda,\,\lambda'\ge\lambda}f(\lambda')$ (Corollary 1 and Appendix A). Appendix A sets $\hat R_n^{\uparrow}=\widetilde{\hat R_n}$ and $\hat\lambda_n^{\uparrow}=\inf\{\lambda\in\Lambda:\hat R_n^{\uparrow}(\lambda)\le\alpha\}$.
--   7. **Covariate shift (Section 4.1).** With weights $w(x)\ge0$, $\hat\lambda(x)=\inf\{\lambda\in\Lambda:\ (\sum_{i=1}^nw(X_i)L_i(\lambda)+w(x)B)/(\sum_{i=1}^nw(X_i)+w(x))\le\alpha\}$. The total variation distance is $\mathrm{TV}(\mu,\nu)=\sup_A|\mu(A)-\nu(A)|$ over measurable sets $A$.
--   8. **Quantiles (Section 4.2).** $\mathrm{Quantile}_\beta(X)=\inf\{x:\mathbb{P}(X\le x)\ge\beta\}$, and $\hat\lambda_\beta=\inf\{\lambda\in\Lambda:\frac1{n+1}\sum_{i=1}^n\mathbb{1}\{L_i(\lambda)>\alpha\}+\frac1{n+1}\le1-\beta\}$.
--   9. **U-risk (Section 4.5).** For $k$-subsets $S\subset\{1,\dots,n+k\}$ with losses $L_S$,
--   $$\hat\lambda_k=\inf\Big\{\lambda\in\Lambda:\ \frac{k!\,n!}{(n+k)!}\sum_{S\subset\{1,\dots,n\},|S|=k}L_S(\lambda)+B\Big(1-\frac{(n!)^2}{(n+k)!\,(n-k)!}\Big)\le\alpha\Big\}.$$
--   The family $(L_S)$ is exchangeable if its joint law is invariant under every relabelling $\sigma$ of $\{1,\dots,n+k\}$, acting by $L_S\mapsto L_{\sigma(S)}$.
--
--   **Formalization Note** Losses are functions $\mathbb{R}\to\mathbb{R}$ of which only the values on $\Lambda$ are used; exchangeability and independence concern the restrictions to $\Lambda$. The paper does not give a topology for $\Lambda$. Compactness is assumed so that every infimum above lies in $\Lambda$, as the proofs require. The expectation is written as $B-\mathbb{E}[B-X]$ in the extended reals because the losses of Theorem 1 are only bounded above. Losses are indexed from $0$: the calibration losses are $L_0,\dots,L_{n-1}$ and the test loss is $L_n$.
-- source:
--   Angelopoulos, Bates, Fisch, Lei and Schuster, Conformal Risk Control, arXiv:2208.02814v4, Section 1.1 (eq. (4), p. 2), Section 2 (eq. (5), Theorem 1, jump function, Corollary 1, pp. 3-5), Section 4.1-4.2 and 4.5 (pp. 10-12), Appendix A (p. 15)

import Mathlib

/-!
Angelopoulos, Bates, Fisch, Lei and Schuster, *Conformal Risk Control*, arXiv:2208.02814v4:
the parameter set, random loss functions, exchangeability, the conformal risk control parameter
`λ̂` of eq. (4), the jump function of Section 2.2, and the modified parameters of Corollary 1,
Section 4 (Propositions 2, 3, 4, 7) and Appendix A (Theorem A.1).
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace ConformalRiskControl

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Section 1.1, p. 2: `f` is right-continuous on the parameter set `Λ ⊆ ℝ`, i.e. at every
`x ∈ Λ` it is continuous within `Λ ∩ [x, ∞)`. -/
def IsRightContOn (Λ : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ Λ, ContinuousWithinAt f (Λ ∩ Set.Ici x) x

/-- Eq. (5), p. 3: `L(λ_max) ≤ α` and `sup_{λ ∈ Λ} L(λ) ≤ B`, with `λ_max = sup Λ`. -/
def LossBounds (Λ : Set ℝ) (B α : ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ x ∈ Λ, f x ≤ B) ∧ f (sSup Λ) ≤ α

/-- Section 1.1, p. 2: the random functions `L_i : Λ → ℝ` form an exchangeable collection:
each `L_i(λ)` is a random variable, and the joint law of `(L_i)_i`, as random elements of
`Λ → ℝ` with the product σ-algebra, is invariant under every permutation of the indices. -/
def IsExchangeable {ι : Type*} (P : Measure Ω) (Λ : Set ℝ) (L : ι → Ω → ℝ → ℝ) : Prop :=
  (∀ i, ∀ x ∈ Λ, Measurable fun ω => L i ω x) ∧
    ∀ σ : Equiv.Perm ι,
      P.map (fun ω i (x : Λ) => L (σ i) ω x) = P.map (fun ω i (x : Λ) => L i ω x)

/-- Theorem 2, p. 4 and Theorem A.1, p. 15: the random functions `L_i : Λ → ℝ` are i.i.d. as
random elements of `Λ → ℝ` with the product σ-algebra. -/
def IsIID {ι : Type*} (P : Measure Ω) (Λ : Set ℝ) (L : ι → Ω → ℝ → ℝ) : Prop :=
  (∀ i, ∀ x ∈ Λ, Measurable fun ω => L i ω x) ∧
    iIndepFun (fun i ω (x : Λ) => L i ω x) P ∧
    ∀ i j, IdentDistrib (fun ω (x : Λ) => L i ω x) (fun ω (x : Λ) => L j ω x) P P

/-- The expectation `E[X] ∈ [-∞, B]` of a random variable bounded above by `B`, written as
`B - E[B - X]` with `E[B - X] ∈ [0, ∞]` a lower Lebesgue integral. For `X ≤ B` almost surely and
`P` a probability measure it is the usual expectation, and equals `-∞` when `E[X⁻] = ∞`; it does
not depend on the choice of the upper bound `B`. -/
def upperExp (P : Measure Ω) (B : ℝ) (X : Ω → ℝ) : EReal :=
  (B : EReal) - ((∫⁻ ω, ENNReal.ofReal (B - X ω) ∂P : ENNReal) : EReal)

/-- Section 1.1, p. 2: the empirical risk `R̂_m(λ) = (L_1(λ) + ⋯ + L_m(λ)) / m`. -/
def empRisk {m : ℕ} (Ls : Fin m → ℝ → ℝ) (x : ℝ) : ℝ :=
  (∑ i, Ls i x) / m

open Classical in
/-- Eq. (4), p. 2: the infimum of a set of parameters, with the convention that the infimum of
the empty set is `λ_max = sup Λ`. -/
def infOrMax (Λ S : Set ℝ) : ℝ :=
  if S.Nonempty then sInf S else sSup Λ

/-- Eq. (4), p. 2: the conformal risk control parameter
`λ̂ = inf {λ ∈ Λ : n/(n+1) · R̂_n(λ) + B/(n+1) ≤ α}`, equal to `λ_max` when the set is empty;
`Ls` are the calibration losses `L_1, …, L_n`. -/
def lhat (Λ : Set ℝ) (B α : ℝ) {n : ℕ} (Ls : Fin n → ℝ → ℝ) : ℝ :=
  infOrMax Λ {x ∈ Λ | (n : ℝ) / (n + 1) * empRisk Ls x + B / (n + 1) ≤ α}

/-- Section 2.2, p. 4: the jump function `J(l, λ) = lim_{ε → 0⁺} l(λ - ε) - l(λ)`. -/
def jump (l : ℝ → ℝ) (x : ℝ) : ℝ :=
  Function.leftLim l x - l x

/-- Corollary 1, p. 5 and Appendix A, p. 15: the monotonization `sup_{λ' ∈ Λ, λ' ≥ λ} f(λ')`. -/
def supRight (Λ : Set ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨆ t : {t : ℝ // t ∈ Λ ∧ x ≤ t}, f t

/-- Section 4.1, p. 10: the weighted parameter under covariate shift,
`λ̂(x) = inf {λ : (∑_i w(X_i) L_i(λ) + w(x) B) / (∑_i w(X_i) + w(x)) ≤ α}`, equal to `max Λ`
when the set is empty; `Ls` and `Xs` are the calibration losses and covariates. -/
def weightedLhat {X : Type*} (Λ : Set ℝ) (B α : ℝ) (w : X → ℝ) {n : ℕ}
    (Ls : Fin n → ℝ → ℝ) (Xs : Fin n → X) (x : X) : ℝ :=
  infOrMax Λ {t ∈ Λ | (∑ i, w (Xs i) * Ls i t + w x * B) / (∑ i, w (Xs i) + w x) ≤ α}

/-- Section 4.1, p. 10: total variation distance `TV(μ, ν) = sup_A |μ(A) - ν(A)|` over
measurable sets `A`. -/
def tvDist {Z : Type*} [MeasurableSpace Z] (μ ν : Measure Z) : ℝ :=
  sSup {r | ∃ A : Set Z, MeasurableSet A ∧ r = |(μ A).toReal - (ν A).toReal|}

/-- Section 4.2, p. 11: `Quantile_β(X) = inf {x : P(X ≤ x) ≥ β}`. -/
def quantile (P : Measure Ω) (X : Ω → ℝ) (β : ℝ) : ℝ :=
  sInf {x : ℝ | β ≤ (P {ω | X ω ≤ x}).toReal}

open Classical in
/-- Section 4.2, p. 11: `λ̂_β = inf {λ ∈ Λ : (1/(n+1)) ∑_{i ≤ n} 1{L_i(λ) > α} + 1/(n+1) ≤ 1 - β}`,
equal to `λ_max` when the set is empty. -/
def lhatQuantile (Λ : Set ℝ) (α β : ℝ) {n : ℕ} (Ls : Fin n → ℝ → ℝ) : ℝ :=
  infOrMax Λ {x ∈ Λ |
    1 / ((n : ℝ) + 1) * ∑ i, (if α < Ls i x then (1 : ℝ) else 0) + 1 / ((n : ℝ) + 1) ≤ 1 - β}

/-- Section 4.5, p. 12: the `k`-subsets `S ⊆ {1, …, n+k}` are indexed by finsets of `Fin (n+k)`;
the calibration subsets are those contained in the first `n` indices. -/
def calibSubsets (n k : ℕ) : Finset (Finset (Fin (n + k))) :=
  (Finset.univ.filter fun i : Fin (n + k) => i.val < n).powersetCard k

/-- Section 4.5, p. 12: the test subset `{n+1, …, n+k}`, i.e. the last `k` indices. -/
def testSubset (n k : ℕ) : Finset (Fin (n + k)) :=
  Finset.univ.filter fun i : Fin (n + k) => n ≤ i.val

/-- Eq. (16), p. 12: `λ̂_k = inf {λ : k! n!/(n+k)! ∑_{S ⊆ {1..n}, |S| = k} L_S(λ)
+ B (1 - (n!)² / ((n+k)! (n-k)!)) ≤ α}`, equal to `λ_max` when the set is empty. -/
def lhatU (Λ : Set ℝ) (B α : ℝ) (n k : ℕ) (L : Finset (Fin (n + k)) → ℝ → ℝ) : ℝ :=
  infOrMax Λ {x ∈ Λ |
    ((k.factorial * n.factorial : ℕ) : ℝ) / ((n + k).factorial : ℝ) *
        ∑ S ∈ calibSubsets n k, L S x +
      B * (1 - ((n.factorial ^ 2 : ℕ) : ℝ) / (((n + k).factorial * (n - k).factorial : ℕ) : ℝ))
      ≤ α}

/-- Section 4.5, p. 12: the collection `(L_S)_{|S| = k}` is exchangeable under relabelling of the
`n + k` data points: each `L_S(λ)` is a random variable, and for every permutation `σ` of
`{1, …, n+k}` the joint law of `(L_{σ(S)})_S` equals that of `(L_S)_S`. -/
def IsExchangeableU (P : Measure Ω) (Λ : Set ℝ) (n k : ℕ)
    (L : Finset (Fin (n + k)) → Ω → ℝ → ℝ) : Prop :=
  (∀ S : Finset (Fin (n + k)), S.card = k → ∀ x ∈ Λ, Measurable fun ω => L S ω x) ∧
    ∀ σ : Equiv.Perm (Fin (n + k)),
      P.map (fun ω (S : {S : Finset (Fin (n + k)) // S.card = k}) (x : Λ) =>
          L (S.1.map σ.toEmbedding) ω x) =
        P.map (fun ω (S : {S : Finset (Fin (n + k)) // S.card = k}) (x : Λ) => L S.1 ω x)

/-- Appendix A, p. 15 (unnumbered displays before Theorem A.1):`λ̂⁺_n = inf {λ ∈ Λ : R̂⁺_n(λ) ≤ α}` with the monotonized
empirical risk `R̂⁺_n(λ) = sup_{t ≥ λ} R̂_n(t)`, equal to `λ_max` when the set is empty. -/
def lhatPlus (Λ : Set ℝ) (α : ℝ) {n : ℕ} (Ls : Fin n → ℝ → ℝ) : ℝ :=
  infOrMax Λ {x ∈ Λ | supRight Λ (empRisk Ls) x ≤ α}

end ConformalRiskControl


