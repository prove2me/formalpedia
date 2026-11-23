-- Prove2me | Definitions.Def_WiesemannRMDP_SRect_Supplement_Inference
-- name    : WiesemannRMDP_SRect_Supplement_Inference
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:51:04.477739+00:00
-- url     : https://prove2.me/theorems/aed6db47-b539-4f93-a88d-80524f339cff
-- title:
--   Observation history (30), log-likelihood (33), MLE, (A1)–(A3′), chain (45) with (C1)–(C4), Σ (48d), ϕ_n (37) and Ξ_n (36)
-- statement:
--   The statistical objects of §5 and Appendices B–C, built on the robust MDP model of the base mission: $\Xi_0$ is the parameter set $\Xi$ of (3b) and $p^\xi(\cdot\mid s,a)=k_{sa}+K_{sa}\xi$ the affine kernel of (3a). A true parameter $\xi^0$ and a known stationary randomized policy $\pi_0$ are fixed.
--
--   1. **Observation (30).** A process $(s_t,a_t)_{t\ge1}$ of state-action pairs on a probability space $(\Omega,\mathcal F,\mathbb P)$ is an observation process if each event $\{(s_t,a_t)=x\}$ is measurable and every finite path has probability (32) with $\xi=\xi^0$:
--   $$\mathbb P\big((s_1,a_1,\dots,s_n,a_n) = h\big) = p_0(s_1)\,\pi_0(a_n\mid s_n)\prod_{t=1}^{n-1}\pi_0(a_t\mid s_t)\,p^{\xi^0}(s_{t+1}\mid s_t,a_t).$$
--   2. **Counts.** $n_{sas'}$ is the number of $t\in\{1,\dots,n-1\}$ with $(s_t,a_t,s_{t+1})=(s,a,s')$, and $N:=\{(s,a,s') : n_{sas'}>0\}$.
--   3. **Log-likelihood (33).** With $\log 0 := -\infty$,
--   $$\ell_n(\xi) := \sum_{t=1}^{n-1}\log p^\xi(s_{t+1}\mid s_t,a_t)+\zeta,\qquad \zeta := \log p_0(s_1)+\sum_{t=1}^{n}\log\pi_0(a_t\mid s_t),$$
--   a function $\Xi_0\to\mathbb R\cup\{-\infty\}$. A sequence of **maximum likelihood estimators** is any sequence $\xi^n$ with $\xi^n\in\Xi_0$ maximizing $\ell_n$ over $\Xi_0$, almost surely for each $n$. The likelihood-ratio statistic is $2[\ell_n(\xi^n)-\ell_n(\xi^0)]$ with $\ell_n(\xi^n)=\max_{\Xi_0}\ell_n$.
--   4. **Assumptions.** (A1) $\xi^0\in\operatorname{int}\Xi_0$. (A2) The Markov chain on $\mathcal S$ with kernel $\widehat P(\pi_0;\xi)$ of (7a) is irreducible for some $\xi\in\Xi_0$. Let $\kappa$ be the rank of the matrix whose rows are $[K_{sa}]^\top_{s'\cdot}$ (row $s'$ of $K_{sa}$) for all $(s,a,s')$ with $\pi_0(a\mid s)>0$. (A3) $\kappa>0$. (A3′) $\kappa=q$ (full column rank).
--   5. **State-action chain (45).** $\mathcal X:=\{(s,a):\pi_0(a\mid s)>0\}$, $\Theta:=\operatorname{int}\Xi_0$ and $p_{xy}(\theta):=p^\theta(s'\mid s,a)\,\pi_0(a'\mid s')$ for $x=(s,a)$, $y=(s',a')$. Billingsley's conditions are: (C1) each $p_{xy}$ is $C^3$ on $\Theta$; (C2) $D(\theta):=\{(x,y):p_{xy}(\theta)>0\}$ is the same set for all $\theta\in\Theta$; (C3) the Jacobian $(\partial p_{xy}/\partial\theta_u)\in\mathbb R^{|\mathcal X|^2\times q}$ has rank $q$ on $\Theta$; (C4) the chain $(p_{xy}(\theta))$ is irreducible for every $\theta\in\Theta$.
--   6. **Return times and $\Sigma$ (48d).** $\mu_s$ is the expected return time of $s$ in the chain $\widehat P(\pi_0;\xi^0)$, $N_0:=\{(s,a,s'):[k_{sa}\ K_{sa}]^\top_{s'\cdot}\neq0\}$ and
--   $$\Sigma := \sum_{(s,a,s')\in N_0}\frac{\pi_0(a\mid s)}{\mu_s\,p^{\xi^0}(s'\mid s,a)}\big([K_{sa}]^\top_{s'\cdot}\big)^\top[K_{sa}]^\top_{s'\cdot}.$$
--   7. **Quadratic approximation (36)–(37).** For $\delta\ge0$ and a centre $\xi^n$,
--   $$\phi_n(\xi) := [\nabla_\xi\ell_n(\xi^n)]^\top(\xi-\xi^n) - \tfrac12(\xi-\xi^n)^\top[\nabla^2_\xi\ell_n(\xi^n)](\xi-\xi^n)+\delta,$$
--   with $[\nabla_\xi\ell_n(\xi^n)]^\top := \sum_{N} \frac{n_{sas'}}{p^{\xi^n}(s'\mid s,a)}[K_{sa}]^\top_{s'\cdot}$ (37b) and $\nabla^2_\xi\ell_n(\xi^n):=\sum_N\frac{n_{sas'}}{[p^{\xi^n}(s'\mid s,a)]^2}([K_{sa}]^\top_{s'\cdot})^\top[K_{sa}]^\top_{s'\cdot}$ (37c), and $\Xi_n:=\Xi_0\cap\{\xi:\phi_n(\xi)\ge0\}$.
--
--   These are the objects of Theorems 5.3 and 5.5 and of the supporting Lemmas B.2, C.1 and C.2.
--
--   **Formalization Note** The observation $(s_1,a_1,\dots,s_n,a_n)$ is $X\,0,\dots,X\,(n-1)$ (time starts at $0$ in Lean). Any probability space carrying a process with the laws (32) is allowed; the paper uses the canonical one. $\log$ is extended-real valued with $\log x=-\infty$ for $x\le0$ (only $x=0$ occurs on $\Xi_0$); Mathlib's $\log 0 = 0$ is not used. The likelihood-ratio statistic is converted to a real number, which is the paper's value almost surely. The matrix (37c) is defined by the printed sum; it is positive semidefinite (minus the Hessian of $\ell_n$). The gradient (37b), the matrix (37c), $\phi_n$ and $\Xi_n$ take their centre $\xi^n$ as an argument. $\mu_s$ enters $\Sigma$ as a real number; it is finite under (A1)–(A2) by Lemma C.1. The Jacobian of (C3) is the Fréchet derivative applied to the coordinate vectors.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), §5 pp. 28–29 ((30), Ω, F, P), (A1) p. 29, (32), (33), (33'), N and n_sas' p. 31, (A2), (A3), δ p. 32, (36), (37a)–(37c), (A3') p. 34, (45a)–(45c) pp. 46–47, (C1)–(C4) p. 46, µ_s p. 49, (48d) p. 50

import Mathlib
import Definitions.Def_WiesemannRMDP_SRect_Model
import Definitions.Def_WiesemannRMDP_SRect_Supplement_Chains

open MeasureTheory FoundationsML.ReinforcementLearning Matrix

namespace WiesemannRMDP.SRect.Supplement

open WiesemannRMDP.SRect

variable {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act] [DecidableEq Act]
  {q L : ℕ}

/-! Objects of §5 and Appendices B–C of Wiesemann, Kuhn & Rustem, *Robust Markov Decision
Processes*, Optimization Online 2610, revision of February 9, 2012, built on the base model
`WiesemannRMDP.SRect.Model`: the structural set `Ξ0` is `M.Xi` and `p^ξ(·|s, a)` is
`M.pXi ξ s a`. The observation `(s₁, a₁, …, s_n, a_n)` of (30) is the first `n` values
`X 0, …, X (n - 1)` of a process `X : ℕ → Ω → S × A`; Lean's time index starts at `0`. -/

/-- The probability (32), p. 31, of observing the state-action sequence
`h 0, …, h n` (of length `n + 1`) under the policy `π0` and the kernel `p^ξ`:
`p₀(s₁) π₀(a₁|s₁) ∏_{t} p^ξ(s_{t+1}|s_t, a_t) π₀(a_{t+1}|s_{t+1})`. -/
noncomputable def pathProb (M : Model St Act q L) (π0 : St → Act → ℝ) (ξ : Fin q → ℝ)
    {n : ℕ} (h : Fin (n + 1) → St × Act) : ℝ :=
  M.p0 (h 0).1 * π0 (h 0).1 (h 0).2 *
    ∏ i : Fin n, (M.pXi ξ (h i.castSucc).1 (h i.castSucc).2 (h i.succ).1 *
      π0 (h i.succ).1 (h i.succ).2)

/-- The observation process of §5 (pp. 28–29): `X t = (s_{t+1}, a_{t+1})` is the state-action
Markov chain of the MDP run under the stationary policy `π0` and the true kernel `p^{ξ0}`, from
the initial law `p₀`. Every event `{X t = x}` is measurable, and every finite path
`(h 0, …, h n)` has probability (32) with `ξ = ξ0`.

**Formalization Note.** The paper takes the canonical space `Ω = (S × A)^∞` with the product
σ-field and the measure induced by `π0` and `P0` ([2, Theorem 4.11.2]); here any probability space
carrying a process with these finite-dimensional laws is allowed. All statements built on it are
about the laws of the observations, so the two readings are equivalent. -/
def IsObservationProcess {Ω : Type*} [MeasurableSpace Ω] (M : Model St Act q L)
    (π0 : St → Act → ℝ) (ξ0 : Fin q → ℝ) (P : Measure Ω) (X : ℕ → Ω → St × Act) : Prop :=
  (∀ (t : ℕ) (x : St × Act), MeasurableSet {ω | X t ω = x}) ∧
  ∀ (n : ℕ) (h : Fin (n + 1) → St × Act),
    P {ω | ∀ i : Fin (n + 1), X i ω = h i} = ENNReal.ofReal (pathProb M π0 ξ0 h)

/-- The transition count `n_{sas'}` of the length-`n` observation (p. 31): the number of
`t ∈ {1, …, n − 1}` with `(s_t, a_t, s_{t+1}) = (s, a, s')`. -/
def transCount {Ω : Type*} (X : ℕ → Ω → St × Act) (n : ℕ) (ω : Ω) (s : St) (a : Act)
    (s' : St) : ℕ :=
  ((Finset.range (n - 1)).filter fun t => X t ω = (s, a) ∧ (X (t + 1) ω).1 = s').card

/-- The set `N := {(s, a, s') : n_{sas'} > 0}` of observed transitions (p. 31). Triples are
written `(s, a, s')`. -/
noncomputable def observedSet {Ω : Type*} (X : ℕ → Ω → St × Act) (n : ℕ) (ω : Ω) :
    Finset (St × Act × St) :=
  Finset.univ.filter fun t => 0 < transCount X n ω t.1 t.2.1 t.2.2

/-- The logarithm with the paper's convention `log(0) := −∞` (p. 31), as an extended real.

**Formalization Note.** Mathlib's `Real.log 0 = 0` is not used at `0`. Negative arguments also
give `−∞`; they do not occur, since the log-likelihood is only evaluated on `Ξ0`, where every
`p^ξ(s'|s, a)` is a probability. -/
noncomputable def logE (x : ℝ) : EReal :=
  if 0 < x then ((Real.log x : ℝ) : EReal) else ⊥

/-- The log-likelihood (33), p. 31, of the length-`n` observation:
`ℓ_n(ξ) := ∑_{t=1}^{n−1} log p^ξ(s_{t+1}|s_t, a_t) + ζ`, with
`ζ := log p₀(s₁) + ∑_{t=1}^{n} log π₀(a_t|s_t)` and `log 0 = −∞`. It takes values in
`ℝ ∪ {−∞}`, and is meaningful for `ξ ∈ Ξ0`. -/
noncomputable def logLik {Ω : Type*} (M : Model St Act q L) (π0 : St → Act → ℝ)
    (X : ℕ → Ω → St × Act) (n : ℕ) (ω : Ω) (ξ : Fin q → ℝ) : EReal :=
  (∑ t ∈ Finset.range (n - 1), logE (M.pXi ξ (X t ω).1 (X t ω).2 (X (t + 1) ω).1)) +
    (logE (M.p0 (X 0 ω).1) + ∑ t ∈ Finset.range n, logE (π0 (X t ω).1 (X t ω).2))

/-- The maximum `ℓ_n(ξ_n) = max_{ξ ∈ Ξ0} ℓ_n(ξ)` of the log-likelihood over `Ξ0` (p. 31), written
as the supremum over `Ξ0` in `EReal`. -/
noncomputable def maxLogLik {Ω : Type*} (M : Model St Act q L) (π0 : St → Act → ℝ)
    (X : ℕ → Ω → St × Act) (n : ℕ) (ω : Ω) : EReal :=
  ⨆ ξ ∈ M.Xi, logLik M π0 X n ω ξ

/-- The likelihood-ratio statistic `2 [ℓ_n(ξ_n) − ℓ_n(ξ0)]` of (35), p. 32.

**Formalization Note.** Both log-likelihoods are converted to real numbers. Almost surely they are
finite (the observed path has positive probability under `ξ0`, so `ℓ_n(ξ0) > −∞`, and
`ℓ_n ≤ ζ < ∞`), and then the value is the paper's; on the null event where one of them is
infinite, `EReal.toReal` gives `0`, an arbitrary value which does not affect the law. -/
noncomputable def lrStat {Ω : Type*} (M : Model St Act q L) (π0 : St → Act → ℝ)
    (X : ℕ → Ω → St × Act) (ξ0 : Fin q → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  2 * ((maxLogLik M π0 X n ω).toReal - (logLik M π0 X n ω ξ0).toReal)

/-- A sequence of maximum likelihood estimators (p. 31): for every observation length `n`,
almost surely, `ξ_n ∈ Ξ0` maximizes `ℓ_n` over `Ξ0`. No measurability of `ξ_n` and no particular
selection among several maximizers is required. -/
def IsMLESeq {Ω : Type*} [MeasurableSpace Ω] (M : Model St Act q L) (π0 : St → Act → ℝ)
    (X : ℕ → Ω → St × Act) (P : Measure Ω) (ξhat : ℕ → Ω → Fin q → ℝ) : Prop :=
  ∀ n : ℕ, ∀ᵐ ω ∂P, ξhat n ω ∈ M.Xi ∧
    ∀ ξ ∈ M.Xi, logLik M π0 X n ω ξ ≤ logLik M π0 X n ω (ξhat n ω)

/-- Assumption (A1), p. 29: `ξ0 ∈ int Ξ0`. -/
def A1 (M : Model St Act q L) (ξ0 : Fin q → ℝ) : Prop :=
  ξ0 ∈ interior M.Xi

/-- Assumption (A2), p. 32: the Markov chain with state set `S` and transition kernel
`P̂(π0; ξ)` of (7a) is irreducible for some `ξ ∈ Ξ0`. -/
def A2 (M : Model St Act q L) (π0 : St → Act → ℝ) : Prop :=
  ∃ ξ ∈ M.Xi, IsIrreducible (M.Phat π0 ξ)

/-- The matrix of (A3) and (A3'), pp. 32 and 34: its rows are `[K_{sa}]ᵀ_{s'·}` (row `s'` of
`K_{sa}`) for the triples `(s, a, s')` with `π0(a|s) > 0`. -/
def rowMatrix (M : Model St Act q L) (π0 : St → Act → ℝ) :
    Matrix {t : St × Act × St // 0 < π0 t.1 t.2.1} (Fin q) ℝ :=
  Matrix.of fun t u => M.K t.1.1 t.1.2.1 t.1.2.2 u

/-- The rank `κ` of the matrix of (A3), p. 32. -/
noncomputable def kappa (M : Model St Act q L) (π0 : St → Act → ℝ) : ℕ :=
  (rowMatrix M π0).rank

/-- Assumption (A3), p. 32: the matrix with rows `[K_{sa}]ᵀ_{s'·}`, `π0(a|s) > 0`, has rank
`κ > 0`. -/
def A3 (M : Model St Act q L) (π0 : St → Act → ℝ) : Prop :=
  0 < kappa M π0

/-- Assumption (A3'), p. 34: the same matrix has full column rank (rank `q`). -/
def A3' (M : Model St Act q L) (π0 : St → Act → ℝ) : Prop :=
  kappa M π0 = q

/-- The state set `X := {(s, a) ∈ S × A : π0(a|s) > 0}` of the state-action chain (45a),
p. 46. -/
abbrev SAState (π0 : St → Act → ℝ) := {x : St × Act // 0 < π0 x.1 x.2}

/-- The transition probabilities (45c), p. 47, of the state-action chain:
`p_{xy}(θ) := p^θ(s'|s, a) π0(a'|s')` for `x = (s, a)`, `y = (s', a')` in `X`. -/
noncomputable def saKernel (M : Model St Act q L) (π0 : St → Act → ℝ) (θ : Fin q → ℝ) :
    Matrix (SAState π0) (SAState π0) ℝ :=
  Matrix.of fun x y => M.pXi θ x.1.1 x.1.2 y.1.1 * π0 y.1.1 y.1.2

/-- The Jacobian matrix `J(θ) ∈ ℝ^{|X|² × q}` of the kernel `θ ↦ (p_{xy}(θ))_{x,y}` of (45c)
(condition (C3), p. 46, and proof of Lemma B.2, p. 47): `J_{xy,u} := ∂p_{xy}(θ)/∂θ_u`. -/
noncomputable def saJacobian (M : Model St Act q L) (π0 : St → Act → ℝ) (θ : Fin q → ℝ) :
    Matrix (SAState π0 × SAState π0) (Fin q) ℝ :=
  Matrix.of fun xy u => fderiv ℝ (fun θ' => saKernel M π0 θ' xy.1 xy.2) θ (Pi.single u 1)

/-- Conditions (C1)–(C4) of Theorem B.1 (p. 46) for the state-action chain (45), with parameter
set `Θ := int Ξ0` (45b) and parameter dimension `U := q`:

* (C1) each `θ ↦ p_{xy}(θ)` has continuous partial derivatives of third order throughout `Θ`;
* (C2) `D(θ) := {(x, y) : p_{xy}(θ) > 0}` is the same set `D` for all `θ ∈ Θ`;
* (C3) the Jacobian of `(p_{xy}(θ))_{x,y}` has rank `q` throughout `Θ`;
* (C4) for each `θ ∈ Θ` the chain with transition probabilities `p_{xy}(θ)` is irreducible. -/
def BillingsleyConditions (M : Model St Act q L) (π0 : St → Act → ℝ) : Prop :=
  (∀ x y : SAState π0, ContDiffOn ℝ 3 (fun θ => saKernel M π0 θ x y) (interior M.Xi)) ∧
  (∃ D : Set (SAState π0 × SAState π0), ∀ θ ∈ interior M.Xi,
      {xy : SAState π0 × SAState π0 | 0 < saKernel M π0 θ xy.1 xy.2} = D) ∧
  (∀ θ ∈ interior M.Xi, (saJacobian M π0 θ).rank = q) ∧
  (∀ θ ∈ interior M.Xi, IsIrreducible (saKernel M π0 θ))

/-- The expected return time `µ_s` of the state `s` under the policy `π0` (Appendix C, p. 49): the
expected return time of `s` in the Markov chain with state set `S` and kernel `P̂(π0; ξ0)` of
(7a). -/
noncomputable def returnTime (M : Model St Act q L) (π0 : St → Act → ℝ) (ξ0 : Fin q → ℝ)
    (s : St) : ENNReal :=
  expectedReturnTime (M.Phat π0 ξ0) s

/-- The index set `N0 := {(s, a, s') : [k_{sa} K_{sa}]ᵀ_{s'·} ≠ 0}` of (48d), p. 50: the triples
whose row `s'` of the `S × (1 + q)` matrix `[k_{sa} K_{sa}]` is nonzero. -/
noncomputable def N0 (M : Model St Act q L) : Finset (St × Act × St) :=
  Finset.univ.filter fun t => M.k t.1 t.2.1 t.2.2 ≠ 0 ∨ ∃ u : Fin q, M.K t.1 t.2.1 t.2.2 u ≠ 0

/-- The matrix `Σ` of (48d), p. 50:
`Σ := ∑_{(s,a,s') ∈ N0} π0(a|s) / (µ_s p^{ξ0}(s'|s, a)) · ([K_{sa}]ᵀ_{s'·})ᵀ [K_{sa}]ᵀ_{s'·}`.

**Formalization Note.** `µ_s` enters through `ENNReal.toReal`; it is finite under (A1)–(A2)
(Lemma C.1). -/
noncomputable def sigmaMat (M : Model St Act q L) (π0 : St → Act → ℝ) (ξ0 : Fin q → ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun u v => ∑ t ∈ N0 M,
    π0 t.1 t.2.1 / ((returnTime M π0 ξ0 t.1).toReal * M.pXi ξ0 t.1 t.2.1 t.2.2) *
      (M.K t.1 t.2.1 t.2.2 u * M.K t.1 t.2.1 t.2.2 v)

/-- The gradient (37b), p. 34, of the log-likelihood at a point `ξc` (the paper evaluates it at
`ξc = ξ_n`): `∇_ξ ℓ_n(ξc) = ∑_{(s,a,s') ∈ N} n_{sas'} / p^{ξc}(s'|s, a) · [K_{sa}]ᵀ_{s'·}`. -/
noncomputable def scoreVec {Ω : Type*} (M : Model St Act q L) (X : ℕ → Ω → St × Act) (n : ℕ)
    (ω : Ω) (ξc : Fin q → ℝ) : Fin q → ℝ :=
  fun u => ∑ t ∈ observedSet X n ω,
    (transCount X n ω t.1 t.2.1 t.2.2 : ℝ) / M.pXi ξc t.1 t.2.1 t.2.2 * M.K t.1 t.2.1 t.2.2 u

/-- The matrix (37c), p. 34, written `∇²_ξ ℓ_n(ξ_n)` in the paper, at a point `ξc`:
`∑_{(s,a,s') ∈ N} n_{sas'} / [p^{ξc}(s'|s, a)]² · ([K_{sa}]ᵀ_{s'·})ᵀ [K_{sa}]ᵀ_{s'·}`.

**Formalization Note.** This is the sum (37c) as printed. It is positive semidefinite: it is
*minus* the Hessian of `ℓ_n` at `ξc`, and the minus sign in (37a) makes `ϕ_n` concave. -/
noncomputable def infoMat {Ω : Type*} (M : Model St Act q L) (X : ℕ → Ω → St × Act) (n : ℕ)
    (ω : Ω) (ξc : Fin q → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun u v => ∑ t ∈ observedSet X n ω,
    (transCount X n ω t.1 t.2.1 t.2.2 : ℝ) / (M.pXi ξc t.1 t.2.1 t.2.2) ^ 2 *
      (M.K t.1 t.2.1 t.2.2 u * M.K t.1 t.2.1 t.2.2 v)

/-- The quadratic function (37a), p. 34, centred at `ξc` (the paper's `ξc = ξ_n`):
`ϕ_n(ξ) := [∇_ξ ℓ_n(ξc)]ᵀ (ξ − ξc) − ½ (ξ − ξc)ᵀ [∇²_ξ ℓ_n(ξc)] (ξ − ξc) + δ`. -/
noncomputable def phiN {Ω : Type*} (M : Model St Act q L) (X : ℕ → Ω → St × Act) (δ : ℝ)
    (n : ℕ) (ω : Ω) (ξc ξ : Fin q → ℝ) : ℝ :=
  scoreVec M X n ω ξc ⬝ᵥ (ξ - ξc) -
    1 / 2 * ((ξ - ξc) ⬝ᵥ (infoMat M X n ω ξc *ᵥ (ξ - ξc))) + δ

/-- The approximate confidence set (36), p. 34: `Ξ_n := Ξ0 ∩ {ξ ∈ ℝ^q : ϕ_n(ξ) ≥ 0}`, with
`ϕ_n` centred at `ξc` (the paper's `ξc = ξ_n`). -/
def XiN {Ω : Type*} (M : Model St Act q L) (X : ℕ → Ω → St × Act) (δ : ℝ) (n : ℕ) (ω : Ω)
    (ξc : Fin q → ℝ) : Set (Fin q → ℝ) :=
  M.Xi ∩ {ξ | 0 ≤ phiN M X δ n ω ξc ξ}

end WiesemannRMDP.SRect.Supplement


