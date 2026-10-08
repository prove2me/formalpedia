-- Prove2me | Definitions.Def_ProgHedging_Convex_Problem
-- name    : ProgHedging_Convex_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:45.202996+00:00
-- url     : https://prove2.me/theorems/433970d4-489e-42f1-a4c2-bcc8622c6782
-- title:
--   The scenario model: weights, decision periods, scenario bundles, subproblems, standing assumptions, and the operators J, K and sets 𝒩, ℳ, 𝒞 (pp. 2–11)
-- statement:
--   **Scenarios and subproblems.** Let $S$ be a finite set of *scenarios* with weights $p_s>0$, $\sum_{s\in S}p_s=1$. For each scenario $s$ there is a *scenario subproblem*
--
--   $$
--   (P_s)\qquad \text{minimize } f_s(x) \text{ over all } x\in C_s\subset\mathbb R^n .
--   $$
--
--   **Standing assumptions** (§3): every $C_s$ is nonempty and closed, every $f_s:\mathbb R^n\to\mathbb R$ is locally Lipschitz continuous, and every level set $\{x\in C_s \mid f_s(x)\le\alpha\}$, $\alpha\in\mathbb R$, is bounded. The **convex case** is the case where every $f_s$ and every $C_s$ is convex.
--
--   **Periods and bundles.** A decision vector is split into stages, $x=(x_1,\dots,x_T)\in\mathbb R^{n_1}\times\dots\times\mathbb R^{n_T}$, $n_1+\dots+n_T=n$. A **policy** is a map $X:S\to\mathbb R^n$, $X(s)=(X_1(s),\dots,X_T(s))$; the space of policies is $\mathcal E$. For each time $t$ the scenarios are partitioned into *bundles* $A\in\mathcal A_t$ (scenarios indistinguishable at time $t$). With the inner product and norm
--
--   $$
--   \langle X,Y\rangle=\sum_{s\in S}p_s\,X(s)\cdot Y(s),\qquad \|X\|=\langle X,X\rangle^{1/2},
--   $$
--
--   the **aggregation operator** $J:X\mapsto\hat X$ replaces $X_t(s)$ by the conditional expectation $\hat X_t(s)=\sum_{s'\in A}p_{s'}X_t(s')/\sum_{s'\in A}p_{s'}$ over the bundle $A\in\mathcal A_t$ containing $s$, and $K=I-J$. The **implementable** policies form $\mathcal N=\{X \mid X_t \text{ constant on each } A\in\mathcal A_t\}$, the **price systems** form $\mathcal M=\{W\mid JW=0\}$, and the **admissible** policies form $\mathcal C=\{X\mid X(s)\in C_s\ \forall s\}$. The objective of the full problem is $F(X)=\sum_s p_s f_s(X(s))$, and the objective of the modified subproblem $(\hat P_s(\hat x,w,r))$ is
--
--   $$
--   \tilde f_s(x)=f_s(x)+x\cdot w+\tfrac12 r\,|x-\hat x|^2,\qquad r>0 .
--   $$
--
--   This is the data of the progressive hedging algorithm; the problem to be solved is (P): minimize $F(X)$ over $X\in\mathcal C\cap\mathcal N$.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The stages are encoded by a monotone map `period : Fin n → Fin T` sending each coordinate to its stage (so $n_t$ may be $0$), and $\mathcal A_t$ by a `Setoid S` whose classes are the bundles; no refinement between periods is assumed, as in the paper. $J$ is written coordinatewise, using the bundle of $s$ at the period of the coordinate; its denominator is positive. The standing assumptions are fields of the structure. Mathlib's norm on policies (`S → EuclideanSpace`) is the sup norm and is not used for any quantitative statement; $\langle\cdot,\cdot\rangle$ and $\|\cdot\|$ above are `ip` and `pnorm`.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), pp. 2–11, (1.1)–(1.9), (2.2)–(2.7), (3.1), (3.4)

import Mathlib

open scoped RealInnerProductSpace

namespace ProgHedging.Convex

/-- Rockafellar–Wets (WP-87-119), §§1–3: finite scenario set `S` with weights `p` (p. 3), decision
vector `x = (x₁,…,x_T)` with coordinate `j` in period `period j` (1.1), bundle partitions `𝒜_t`
(p. 2), scenario subproblems `(P_s)`: minimize `f s` over `C s` (p. 2), and the standing assumptions
of §3 (p. 10): `C s` nonempty and closed, `f s` locally Lipschitz with bounded level sets (3.1). -/
structure Problem (S : Type*) [Fintype S] (n T : ℕ) where
  p : S → ℝ
  p_pos : ∀ s, 0 < p s
  p_sum : ∑ s, p s = 1
  period : Fin n → Fin T
  period_mono : Monotone period
  bundle : Fin T → Setoid S
  C : S → Set (EuclideanSpace ℝ (Fin n))
  f : S → EuclideanSpace ℝ (Fin n) → ℝ
  C_nonempty : ∀ s, (C s).Nonempty
  C_closed : ∀ s, IsClosed (C s)
  f_locallyLipschitz : ∀ s, LocallyLipschitz (f s)
  levelSet_bounded : ∀ s (α : ℝ), Bornology.IsBounded {x | x ∈ C s ∧ f s x ≤ α}

/-- p. 2: a policy assigns to each scenario `s` a decision vector `X(s) ∈ Rⁿ`; the space `ℰ`. -/
abbrev Policy (S : Type*) (n : ℕ) := S → EuclideanSpace ℝ (Fin n)

/-- (2.2), p. 6: `⟨X, Y⟩ = Σ_s p_s X(s)·Y(s)`. -/
noncomputable def Problem.ip {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (X Y : Policy S n) : ℝ :=
  ∑ s, pr.p s * ⟪X s, Y s⟫

/-- (2.3), p. 6: `‖X‖ = (E{|X(s)|²})^{1/2}`. -/
noncomputable def Problem.pnorm {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (X : Policy S n) : ℝ :=
  Real.sqrt (pr.ip X X)

/-- (1.6)–(1.8), p. 4: `X̂ = J X`, `X̂_t(s) = Σ_{s'∈A} p_{s'} X_t(s') / Σ_{s'∈A} p_{s'}` for the bundle
`A ∈ 𝒜_t` containing `s`, coordinate by coordinate. -/
noncomputable def Problem.J {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (X : Policy S n) : Policy S n := by
  classical
  exact fun s => (WithLp.equiv 2 (Fin n → ℝ)).symm fun j =>
    (∑ s' ∈ Finset.univ.filter (fun s' => (pr.bundle (pr.period j)).r s' s), pr.p s' * X s' j) /
      (∑ s' ∈ Finset.univ.filter (fun s' => (pr.bundle (pr.period j)).r s' s), pr.p s')

/-- (2.4), p. 7: `K = I − J`. -/
noncomputable def Problem.K {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (X : Policy S n) : Policy S n :=
  X - pr.J X

/-- (1.3), p. 2: implementable policies, `X_t` constant on each bundle `A ∈ 𝒜_t`. -/
def Problem.N {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) : Set (Policy S n) :=
  {X | ∀ j s s', (pr.bundle (pr.period j)).r s s' → X s j = X s' j}

/-- (2.5), p. 7: `ℳ = 𝒩^⊥ = {W | J W = 0}`. -/
noncomputable def Problem.M {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) :
    Set (Policy S n) :=
  {W | pr.J W = 0}

/-- (1.4), p. 2: admissible policies, `X(s) ∈ C_s` for all `s`. -/
def Problem.adm {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) : Set (Policy S n) :=
  {X | ∀ s, X s ∈ pr.C s}

/-- (1.9) = (2.7), pp. 4, 7: `F(X) = Σ_s p_s f_s(X(s))`. -/
def Problem.F {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (X : Policy S n) : ℝ :=
  ∑ s, pr.p s * pr.f s (X s)

/-- p. 10: the convex case, every `f_s` and every `C_s` convex. -/
def Problem.ConvexCase {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) : Prop :=
  ∀ s, Convex ℝ (pr.C s) ∧ ConvexOn ℝ Set.univ (pr.f s)

/-- (3.4), p. 11: the objective of the modified subproblem `(P̂_s(x̂, w, r))`,
`f_s(x) + x·w + ½ r |x − x̂|²`; `(P^ν_s)` is the case `x̂ = X̂^ν(s)`, `w = W^ν(s)`. -/
noncomputable def Problem.subObj {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (s : S)
    (xhat w : EuclideanSpace ℝ (Fin n)) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  pr.f s x + ⟪x, w⟫ + r / 2 * ‖x - xhat‖ ^ 2

end ProgHedging.Convex


