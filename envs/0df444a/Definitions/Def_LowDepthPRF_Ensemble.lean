-- Prove2me | Definitions.Def_LowDepthPRF_Ensemble
-- name    : LowDepthPRF_Ensemble
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:41.148347+00:00
-- url     : https://prove2.me/theorems/ebde268b-25e2-4c19-8094-88ae4df4ae29
-- title:
--   Ensembles, efficiency, $\mathsf{NC}^1$, negligible functions, PRFs and WPRFs, key-uniformity
-- statement:
--   A function $f$ is **polynomially bounded** if $f(n)\le p(n)$ for a polynomial $p$ and all $n$ (Definition 3.14). A function $\epsilon$ is **negligible** if for every $c>0$ there is $n_c$ with $\epsilon(n)<n^{-c}$ for all $n\ge n_c$ (Definition 3.15).
--
--   A **function family ensemble** (Definition 3.16) is $\{F_\lambda\}_{\lambda\in\mathbb N}$ with $F_\lambda=\{F_k:\{0,1\}^{p_0(\lambda)}\to\{0,1\}^{p_1(\lambda)},\ k\in\{0,1\}^{p_2(\lambda)}\}$, where $p_0,p_1,p_2$ are positive and polynomially bounded. It is a **$(t,d)$-ensemble** if $F_\lambda$ is a $(t(\lambda),d(\lambda))$-function family for every $\lambda$, **efficient** if this holds for polynomials $t,d$, and **in $\mathsf{NC}^1$** if it is a $(\mathrm{poly}(\lambda),O(\log\lambda))$-ensemble.
--
--   An efficient ensemble is a **PRF** (Definition 3.17) if for all polynomials $q,t$ there is a negligible $\epsilon$ such that $F_\lambda$ is $(q(\lambda),t(\lambda),\epsilon(\lambda))$-strong pseudorandom for every $\lambda$. It is a **WPRF** (Definition 3.18) under the same condition with weak pseudorandomness. It is **key-uniform** (Definition 4.1) if every $F_\lambda$ is a $1$-wise independent hashing.
--
--   These are the objects in the statement of the main result.
--
--   **Formalization Note**
--   1. Polynomials are `Polynomial ℕ` evaluated at $\lambda$.
--   2. Positivity of the lengths is required for $\lambda\ge1$, because the constructions of §4 have key length $\lambda$.
--   3. $O(\log\lambda)$ means $\le C\log_2\lambda$ for all $\lambda\ge\lambda_0$.
--   4. "Computable in depth $d(\lambda)$" is `DepthEventually`: for all large $\lambda$, one circuit of polynomial size and depth at most $d(\lambda)$.
--   5. The predicates also come in versions for sequences of families that are not packaged as an `Ensemble`, which are used for the construction of §4.
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Definitions 3.14–3.18, pp.13–14 (pdf 15–16); Definition 4.1, p.15 (pdf 17)

import Mathlib
import Definitions.Def_LowDepthPRF_Pseudorandom

namespace LowDepthPRF

/-!
# Asymptotics: function family ensembles, efficiency, NC¹, PRFs and WPRFs

Ding, Jain, Komargodski, *Pseudorandom Functions in NC¹ from LWE/LPN/CDH*, arXiv:2608.25213
(sha256 89a55849…), Definitions 3.14–3.18, pp.13–14, and Definition 4.1, p.15.

**Formalization Note.**
* "Polynomial" means a polynomial with natural coefficients evaluated at `λ`
  (`Polynomial ℕ`); `f` is polynomially bounded if `f(n) ≤ p(n)` for all `n` (Def 3.14).
* Negligible (Def 3.15): for every real `c > 0` there is `n_c` with `ε(n) < n^{-c}` for all
  `n ≥ n_c` (real power).
* An ensemble (Def 3.16) has input, output and key lengths `p₀, p₁, p₂` and families
  `F_λ = {F_k : {0,1}^{p₀(λ)} → {0,1}^{p₁(λ)}, k ∈ {0,1}^{p₂(λ)}}`. `Ensemble.Valid` asks the
  lengths to be polynomially bounded and positive for every `λ ≥ 1` (at `λ = 0` the
  constructions of §4 have key length `0`).
* A `(t, d)`-ensemble has, for every `λ`, one circuit for `F_λ` of size `≤ t(λ)` and depth
  `≤ d(λ)` (Def 3.1). Efficient: polynomials `t`, `d`. In NC¹: a `(poly(λ), O(log λ))`-ensemble,
  where `O(log λ)` means `≤ C·log₂ λ` for all `λ ≥ λ₀`.
* `DepthEventually F d`: polynomial size and depth `≤ d(λ)` by one circuit, for all large `λ`;
  it is the reading of "computable in depth `d(λ)`" (an asymptotic statement), used together with
  efficiency, which already gives polynomial size at every `λ`.
* PRF / WPRF (Defs 3.17, 3.18): efficient, and for all polynomials `q, t` there is a negligible
  `ε` with `F_λ` `(q(λ), t(λ), ε(λ))`-strong (resp. weak) pseudorandom for **every** `λ`.
* Key-uniform (Def 4.1): every `G_λ` is a 1-wise independent hashing.
* The predicates on raw families (`EfficientFam`, `DepthEventually`, `InNC1Fam`) are used for
  the construction of §4, whose families are not packaged as an `Ensemble`.
-/

/-- Definition 3.14: polynomially bounded. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n

/-- Definition 3.15: negligible. -/
def Negligible (ε : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ nc : ℕ, ∀ n ≥ nc, ε n < (n : ℝ) ^ (-c)

/-- Definition 3.16: a function family ensemble `{F_λ}` with input, output, key lengths
`p₀(λ), p₁(λ), p₂(λ)`. -/
structure Ensemble where
  /-- Input length. -/
  p0 : ℕ → ℕ
  /-- Output length. -/
  p1 : ℕ → ℕ
  /-- Key length. -/
  p2 : ℕ → ℕ
  /-- The family at security parameter `λ`. -/
  F : (lam : ℕ) → FunFam (Fin (p2 lam) → Bool) (p0 lam) (p1 lam)

/-- Efficient (Def 3.16) for a raw sequence of families: polynomials `t, d` with `F_λ` a
`(t(λ), d(λ))`-function family for every `λ`. -/
def EfficientFam {kl a b : ℕ → ℕ} (F : (lam : ℕ) → FunFam (Fin (kl lam) → Bool) (a lam) (b lam)) :
    Prop :=
  ∃ t d : Polynomial ℕ, ∀ lam, IsSizeDepth (F lam) ((t.eval lam : ℕ) : ℝ) ((d.eval lam : ℕ) : ℝ)

/-- Computable in depth `d(λ)`: for all large `λ`, one circuit of polynomial size and depth at most
`d(λ)`. -/
def DepthEventually {kl a b : ℕ → ℕ}
    (F : (lam : ℕ) → FunFam (Fin (kl lam) → Bool) (a lam) (b lam)) (d : ℕ → ℝ) : Prop :=
  ∃ t : Polynomial ℕ, ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, IsSizeDepth (F lam) ((t.eval lam : ℕ) : ℝ) (d lam)

/-- In NC¹ (Def 3.16): a `(poly(λ), O(log λ))`-function family ensemble. -/
def InNC1Fam {kl a b : ℕ → ℕ} (F : (lam : ℕ) → FunFam (Fin (kl lam) → Bool) (a lam) (b lam)) :
    Prop :=
  ∃ t : Polynomial ℕ, ∃ d : ℕ → ℝ, (∀ lam, IsSizeDepth (F lam) ((t.eval lam : ℕ) : ℝ) (d lam)) ∧
    ∃ C : ℝ, ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, d lam ≤ C * Real.logb 2 lam

namespace Ensemble

/-- The lengths are positive (for `λ ≥ 1`) and polynomially bounded (Def 3.16). -/
def Valid (E : Ensemble) : Prop :=
  PolyBounded E.p0 ∧ PolyBounded E.p1 ∧ PolyBounded E.p2 ∧
    ∀ lam ≥ 1, 0 < E.p0 lam ∧ 0 < E.p1 lam ∧ 0 < E.p2 lam

/-- Efficient (Def 3.16). -/
def Efficient (E : Ensemble) : Prop := EfficientFam E.F

/-- In NC¹ (Def 3.16). -/
def InNC1 (E : Ensemble) : Prop := InNC1Fam E.F

/-- Definition 3.17: a (polynomially secure) PRF. -/
def IsPRF (E : Ensemble) : Prop :=
  E.Valid ∧ E.Efficient ∧
    ∀ q t : Polynomial ℕ, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ lam, StrongPR (E.F lam) (q.eval lam) ((t.eval lam : ℕ) : ℝ) (ε lam)

/-- Definition 3.18: a (polynomially secure) WPRF. -/
def IsWPRF (E : Ensemble) : Prop :=
  E.Valid ∧ E.Efficient ∧
    ∀ q t : Polynomial ℕ, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ lam, WeakPR (E.F lam) (q.eval lam) ((t.eval lam : ℕ) : ℝ) (ε lam)

/-- Definition 4.1: key-uniform — every `F_λ` is a 1-wise independent hashing. -/
def KeyUniform (E : Ensemble) : Prop := ∀ lam, NWiseIndep (E.F lam) 1

end Ensemble

end LowDepthPRF


