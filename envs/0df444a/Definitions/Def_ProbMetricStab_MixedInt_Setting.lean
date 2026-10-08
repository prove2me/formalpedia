-- Prove2me | Definitions.Def_ProbMetricStab_MixedInt_Setting
-- name    : ProbMetricStab_MixedInt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:52.043248+00:00
-- url     : https://prove2.me/theorems/bd6e89c8-98b5-4516-830a-f3d8524c71a5
-- title:
--   §1, p. 3, and §3.2, pp. 14–17 — program (9), value function Φ of (10), (B1)–(B3), 𝒫_p, 𝒫_{p,K}, ℱ_{1,lg}(P), d_{1,phk}, α_{phk}
-- statement:
--   This module fixes the mixed-integer two-stage stochastic program of §3.2 and the probability metrics attached to it.
--
--   1. **Value function** (10). For recourse costs $q\in\mathbb R^{\hat m}$, $\bar q\in\mathbb R^{\bar m}$ and $(r,\hat m)$-, $(r,\bar m)$-matrices $W$, $\bar W$,
--   $$
--   \Phi(t)=\min\{qy+\bar q\bar y:\ Wy+\bar W\bar y=t,\ y\in\mathbb Z^{\hat m}_+,\ \bar y\in\mathbb R^{\bar m}_+\}\qquad(t\in\mathbb R^r),
--   $$
--   and $\mathcal T=\{t\in\mathbb R^r: t=Wy+\bar W\bar y,\ y\in\mathbb Z^{\hat m}_+,\ \bar y\in\mathbb R^{\bar m}_+\}$ is the set of right-hand sides for which the second stage is feasible; $\operatorname{pos}\bar W=\{\bar W\bar y:\bar y\in\mathbb R^{\bar m}_+\}$.
--   2. **Program** (9): $\min\{cx+\int_\Xi\Phi(h(\xi)-T(\xi)x)\mu(d\xi): x\in X\}$ with $c\in\mathbb R^m$, $X\subseteq\mathbb R^m$, $\Xi\subseteq\mathbb R^s$, and $h(\xi)\in\mathbb R^r$, the $(r,m)$-matrix $T(\xi)$ affine in $\xi$. Its integrand is $f_0(\xi,x)=cx+\Phi(h(\xi)-T(\xi)x)$.
--   3. **Conditions.** (B1) $W$ and $\bar W$ have only rational elements. (B2) $h(\xi)-T(\xi)x\in\mathcal T$ for each $(\xi,x)\in\Xi\times X$ (relatively complete recourse). (B3) there is $u\in\mathbb R^r$ with $W'u\le q$ and $\bar W'u\le\bar q$ (dual feasibility).
--   4. **Polyhedra.** A polyhedron is an intersection of finitely many closed half-spaces; a polyhedron with at most $k$ faces is $\{\xi:\langle a_i,\xi\rangle\le b_i,\ i=1,\dots,k\}$.
--   5. **Moment classes.** $\mathcal P_p(\Xi)=\{\nu\in\mathcal P(\Xi):\int_\Xi\|\xi\|^p\nu(d\xi)<\infty\}$ and $\mathcal P_{p,K}(\Xi)=\{\nu\in\mathcal P_p(\Xi):\int_\Xi\|\xi\|^p\nu(d\xi)\le K\}$.
--   6. **Metrics.** $\mathcal F_{1,lg}(P)$ is the set of $f:P\to\mathbb R$ with $|f(\xi)-f(\tilde\xi)|\le\|\xi-\tilde\xi\|$ and $|f(\xi)|\le\max\{1,\|\xi\|\}$ on $P$, and
--   $$
--   d_{1,phk}(\mu,\nu)=\sup\Big\{\Big|\int_P f(\xi)(\mu-\nu)(d\xi)\Big|: f\in\mathcal F_{1,lg}(P),\ P \text{ a polyhedron with at most } k \text{ faces}\Big\},\qquad \alpha_{phk}(\mu,\nu)=\sup\{|\mu(P)-\nu(P)|: P \text{ a polyhedron with at most } k \text{ faces}\}.
--   $$
--
--   $d_{1,phk}$ is the canonical metric of Theorem 3.6, and the polyhedral discrepancy $\alpha_{phk}$ that of Corollary 3.7.
--
--   **Formalization Note** $\Phi$ is an extended-real infimum, $+\infty$ when the feasible set is empty; the paper's "min" (attained under (B1)–(B3)) is read as an infimum. Nonnegative integer vectors are $\hat m$-tuples of natural numbers, and $W$, $\bar W$ are real matrices, with (B1) stated as rationality of every entry. $T(\xi)$ is a linear map $\mathbb R^m\to\mathbb R^r$ depending affinely on $\xi$, so $\|T(\xi)\|$ is the operator norm. "Polyhedron with at most $k$ faces" is read as the intersection of $k$ closed half-spaces (rows with $a_i=0$ allowed, hence "at most"); since $k$ is existential in Theorem 3.6 and Corollary 3.7, this reading and the facet-count reading give the same theorems. A function on $P$ is represented by a function on $\mathbb R^s$ whose values off $P$ are ignored; $\int_P$ is the Bochner integral over $P$, and $\mathcal F_1(P)$ is the class $\mathcal F_p$ of p. 3 with $p=1$, i.e. the 1-Lipschitz functions. The suprema are taken in $[0,\infty]$. The paper's indices $1,\dots,k$ are $0,\dots,k-1$.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 3 (ℱ_p, 𝒫_p), p. 14 ((9), (10), (B1)–(B3), 𝒯), p. 15 (Lemma 3.5: pos W̄; Theorem 3.6: 𝒫_{p,K}, d_{1,phk}, ℱ_{1,lg}; proof: f₀), p. 17 (Corollary 3.7: α_{phk})

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_ProbMetricStab_MixedInt_ObjectiveStability

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ProbMetricStab.MixedInt

/-! Rachev & Römisch, *Quantitative stability in stochastic programming: The method of probability
metrics*, preprint, §1 (p. 3) and §3.2 (pp. 14–17): the mixed-integer two-stage program (9)–(10),
conditions (B1)–(B3), the moment classes `𝒫_p(Ξ)`, `𝒫_{p,K}(Ξ)`, and the polyhedral metrics
`d_{1,phk}` and `α_{phk}`. -/

/-- The polyhedra with at most `k` faces, read as intersections of `k` closed half-spaces
`{ξ : ⟨a_i, ξ⟩ ≤ b_i}`, `i = 1, …, k` (a row with `a_i = 0` may be void, hence "at most"). -/
def PolyAtMost (s k : ℕ) : Set (Set (EuclideanSpace ℝ (Fin s))) :=
  {P | ∃ (a : Fin k → EuclideanSpace ℝ (Fin s)) (b : Fin k → ℝ),
    P = {ξ | ∀ i, inner ℝ (a i) ξ ≤ b i}}

/-- A polyhedron in `ℝ^s`: an intersection of finitely many closed half-spaces. -/
def IsPolyhedron {s : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin s))) : Prop :=
  ∃ k : ℕ, Ξ ∈ PolyAtMost s k

/-- Second-stage (recourse) data of (10): costs `q ∈ ℝ^{m̂}`, `q̄ ∈ ℝ^{m̄}` and the `(r, m̂)`- and
`(r, m̄)`-matrices `W`, `W̄`. -/
structure Recourse (r mh mb : ℕ) where
  q : Fin mh → ℝ
  qb : Fin mb → ℝ
  W : Matrix (Fin r) (Fin mh) ℝ
  Wb : Matrix (Fin r) (Fin mb) ℝ

namespace Recourse

variable {r mh mb : ℕ} (R : Recourse r mh mb)

/-- The mixed-integer value function (10):
`Φ(t) = min { q y + q̄ ȳ : W y + W̄ ȳ = t, y ∈ ℤ₊^{m̂}, ȳ ∈ ℝ₊^{m̄} }`, read as an `EReal` infimum
(`+∞` when the feasible set is empty). Nonnegative integer vectors are `Fin m̂ → ℕ`. -/
noncomputable def Phi (t : EuclideanSpace ℝ (Fin r)) : EReal :=
  ⨅ (y : Fin mh → ℕ) (yb : Fin mb → ℝ) (_ : 0 ≤ yb)
    (_ : WithLp.toLp 2 (R.W *ᵥ (fun i => (y i : ℝ)) + R.Wb *ᵥ yb) = t),
    ((R.q ⬝ᵥ (fun i => (y i : ℝ)) + R.qb ⬝ᵥ yb : ℝ) : EReal)

/-- `𝒯 = { t ∈ ℝ^r : t = W y + W̄ ȳ, y ∈ ℤ₊^{m̂}, ȳ ∈ ℝ₊^{m̄} }` (B2). -/
def Tset : Set (EuclideanSpace ℝ (Fin r)) :=
  {t | ∃ (y : Fin mh → ℕ) (yb : Fin mb → ℝ), 0 ≤ yb ∧
    WithLp.toLp 2 (R.W *ᵥ (fun i => (y i : ℝ)) + R.Wb *ᵥ yb) = t}

/-- `pos W̄ = { W̄ ȳ : ȳ ∈ ℝ₊^{m̄} }`. -/
def posWb : Set (EuclideanSpace ℝ (Fin r)) :=
  {t | ∃ yb : Fin mb → ℝ, 0 ≤ yb ∧ WithLp.toLp 2 (R.Wb *ᵥ yb) = t}

/-- (B1): the matrices `W` and `W̄` have only rational elements. -/
def B1 : Prop :=
  (∀ i j, ∃ a : ℚ, R.W i j = (a : ℝ)) ∧ (∀ i j, ∃ a : ℚ, R.Wb i j = (a : ℝ))

/-- (B3), dual feasibility: there is `u ∈ ℝ^r` with `W'u ≤ q` and `W̄'u ≤ q̄` (componentwise). -/
def B3 : Prop :=
  ∃ u : Fin r → ℝ, R.Wᵀ *ᵥ u ≤ R.q ∧ R.Wbᵀ *ᵥ u ≤ R.qb

end Recourse

/-- The mixed-integer two-stage program (9): first-stage cost `c ∈ ℝ^m`, closed constraint set
`X ⊆ ℝ^m`, support polyhedron `Ξ ⊆ ℝ^s`, recourse data, and the right-hand side `h(ξ) ∈ ℝ^r` and
technology matrix `T(ξ)` (an `(r, m)`-matrix, i.e. a linear map `ℝ^m → ℝ^r`), both affine in `ξ`. -/
structure MIProgram (m s r mh mb : ℕ) where
  c : EuclideanSpace ℝ (Fin m)
  X : Set (EuclideanSpace ℝ (Fin m))
  Ξ : Set (EuclideanSpace ℝ (Fin s))
  recourse : Recourse r mh mb
  h : EuclideanSpace ℝ (Fin s) →ᵃ[ℝ] EuclideanSpace ℝ (Fin r)
  T : EuclideanSpace ℝ (Fin s) →ᵃ[ℝ] (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin r))

namespace MIProgram

variable {m s r mh mb : ℕ} (P : MIProgram m s r mh mb)

/-- The integrand `f₀(ξ, x) = c x + Φ(h(ξ) − T(ξ) x)` (proof of Theorem 3.6, p. 15). -/
noncomputable def f0 (ξ : EuclideanSpace ℝ (Fin s)) (x : EuclideanSpace ℝ (Fin m)) : EReal :=
  ((inner ℝ P.c x : ℝ) : EReal) + P.recourse.Phi (P.h ξ - P.T ξ x)

/-- (B2), relatively complete recourse: `h(ξ) − T(ξ) x ∈ 𝒯` for each `(ξ, x) ∈ Ξ × X`. -/
def B2 : Prop :=
  ∀ ξ ∈ P.Ξ, ∀ x ∈ P.X, P.h ξ - P.T ξ x ∈ P.recourse.Tset

end MIProgram

variable {s : ℕ}

/-- `𝒫_p(Ξ) = { ν ∈ 𝒫(Ξ) : ∫_Ξ ‖ξ‖^p ν(dξ) < ∞ }` (p. 3). -/
def Pp (Ξ : Set (EuclideanSpace ℝ (Fin s))) (p : ℝ) : Set (Measure (EuclideanSpace ℝ (Fin s))) :=
  {ν | ν ∈ ProbOn Ξ ∧ ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ p) ∂ν < ∞}

/-- `𝒫_{p,K}(Ξ) = { ν ∈ 𝒫_p(Ξ) : ∫_Ξ ‖ξ‖^p ν(dξ) ≤ K }` (Theorem 3.6, p. 15). -/
def PpK (Ξ : Set (EuclideanSpace ℝ (Fin s))) (p K : ℝ) : Set (Measure (EuclideanSpace ℝ (Fin s))) :=
  {ν | ν ∈ Pp Ξ p ∧ ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ p) ∂ν ≤ ENNReal.ofReal K}

/-- `ℱ_{1,lg}(P) = { f ∈ ℱ_1(P) : |f(ξ)| ≤ max{1, ‖ξ‖} for each ξ ∈ P }` (Theorem 3.6, p. 15), where
`ℱ_1(P)` (p. 3, `p = 1`) is the class of functions with `|f(ξ) − f(ξ̃)| ≤ ‖ξ − ξ̃‖` on `P`. A function
on `P` is represented by any function on `ℝ^s`; only its values on `P` matter. -/
def F1lg (P : Set (EuclideanSpace ℝ (Fin s))) : Set (EuclideanSpace ℝ (Fin s) → ℝ) :=
  {f | LipschitzOnWith 1 f P ∧ ∀ ξ ∈ P, |f ξ| ≤ max 1 ‖ξ‖}

/-- `d_{1,phk}(μ, ν) = sup { |∫_P f(ξ)(μ − ν)(dξ)| : f ∈ ℱ_{1,lg}(P), P a polyhedron with at most
k faces }` (Theorem 3.6, p. 15), valued in `ℝ≥0∞`. -/
noncomputable def d1phk (k : ℕ) (μ ν : Measure (EuclideanSpace ℝ (Fin s))) : ℝ≥0∞ :=
  ⨆ (P ∈ PolyAtMost s k) (f ∈ F1lg P), ‖(∫ ξ in P, f ξ ∂μ) - ∫ ξ in P, f ξ ∂ν‖ₑ

/-- `α_{phk}(μ, ν) = sup { |μ(P) − ν(P)| : P a polyhedron with at most k faces }` (Corollary 3.7,
p. 17), the polyhedral discrepancy, valued in `ℝ≥0∞`. -/
noncomputable def alphaPhk (k : ℕ) (μ ν : Measure (EuclideanSpace ℝ (Fin s))) : ℝ≥0∞ :=
  ⨆ P ∈ PolyAtMost s k, ‖(μ P).toReal - (ν P).toReal‖ₑ

end ProbMetricStab.MixedInt


