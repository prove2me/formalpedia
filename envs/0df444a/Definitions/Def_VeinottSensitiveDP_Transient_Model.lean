-- Prove2me | Definitions.Def_VeinottSensitiveDP_Transient_Model
-- name    : VeinottSensitiveDP_Transient_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:47:57.128032+00:00
-- url     : https://prove2.me/theorems/01e460ad-5e63-4ea5-92f3-ef5bce1b2971
-- title:
--   §2 model: rewards r(s,a), nonnegative weights p(t|s,a), decision rules F, policies, Pᴺ(π), transient policies, V(π), v(g,π*), row-sum norm
-- statement:
--   This file sets up the model of §2 of Veinott (1969), "Maximal expected reward: discrete parameter".
--
--   **The program.** There are finitely many states $1,\dots,S$ (a nonempty finite set). In state $s$ a finite nonempty set $A_s$ of actions is available. Taking action $a$ in state $s$ earns the reward $r(s,a)\in\mathbb R$ (of either sign), and $p(t\mid s,a)\ge 0$ is the transition weight from $s$ to $t$. In the probabilistic reading $p(t\mid s,a)$ is a transition probability and $1-\sum_t p(t\mid s,a)$ the probability of stopping; in §2 Veinott drops the assumption that the row sums are at most one and keeps only nonnegativity, and so does this file.
--
--   **Decision rules and policies.** $F=\times_{s=1}^S A_s$ is the finite set of decision rules $f$, each choosing an action $f(s)\in A_s$ in every state. For $f\in F$, $r(f)$ is the column vector with $s$th component $r(s,f(s))$ and $P(f)$ the $S\times S$ matrix with $st$th element $p(t\mid s,f(s))$. A **policy** is a sequence $\pi=(f_1,f_2,\dots)$ of elements of $F$. Special policies are the **stationary** policy $f^\infty=(f,f,\dots)$, the policy $(g,\pi)=(g,f_1,f_2,\dots)$, and the **periodic** policy ${}^N\pi=(\pi^N,\pi^N,\dots)$ that repeats the first $N\ge 1$ components $\pi^N$ of $\pi$.
--
--   **Transience and total reward.** Let $P^0(\pi)=I$ and $P^N(\pi)=P(f_1)\cdots P(f_N)$. A policy $\pi$ is **transient** if $\sum_{N=0}^\infty P^N(\pi)$ converges. For a transient $\pi$ the vector of expected total returns is
--
--   $$V(\pi)=\sum_{N=0}^\infty P^N(\pi)\,r(f_{N+1}),$$
--
--   which converges absolutely. For a decision rule $g$ and a policy $\pi^*$, $v(g,\pi^*)=V(g,\pi^*)-V(\pi^*)$ is the change in return from using $g$ first and then following $\pi^*$.
--
--   **Norm.** For an $S\times S$ matrix $B=(b_{ij})$, $\|B\|=\max_i\sum_j|b_{ij}|$ is the maximum absolute row sum.
--
--   Vectors in $\mathbb R^S$ are compared coordinatewise; Veinott's $x>y$ means $x\ge y$ and $x\ne y$, and the statements of the mission write this out.
--
--   **Formalization Note.** States form a type `St` with `[Fintype St] [DecidableEq St]` (and `[Nonempty St]` where the norm is used); actions are a family of types `A : St → Type`, so $F$ is the dependent function type `(s : St) → A s`. A program is a structure `Program St A` with fields `r`, `p` and the nonnegativity proof. Policies are `ℕ → F`, indexed from $0$: `π 0` is $f_1$, so $P^N(\pi)$ is `PN N π` $=P(\pi\,0)\cdots P(\pi\,(N-1))$ and the $N$th summand of $V(\pi)$ is $P^N(\pi)\,r(\pi\,N)$. Transience is `Summable` in the entrywise topology. $V$ is a `tsum`, which equals the series for transient $\pi$ and is an uninformative default otherwise; every theorem that uses $V$ supplies the transience it needs. The norm is defined explicitly and is not Mathlib's default matrix norm.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, pp. 1636–1637, §2 (Preliminaries; (1); v(g, π*) of Lemma 1)

import Mathlib

namespace VeinottSensitiveDP.Transient

open Matrix

/-- Veinott's dynamic program of §2 (Veinott, *Discrete Dynamic Programming with Sensitive
Discount Optimality Criteria*, Ann. Math. Statist. 40(5):1635–1660 (1969),
DOI 10.1214/aoms/1177697379, p. 1636, §2 "Preliminaries").

The states `1, …, S` form a finite type `St`; in state `s` the finite set of possible actions is
`A s`. Taking action `a` in state `s` earns the reward `r s a = r(s, a)` (any sign), and
`p s a t = p(t | s, a)` is the transition weight from `s` to `t`.

**Formalization Note.** Following p. 1636 ("we shall drop the assumption that the row sums of
P(·) be one or less; however, we retain the hypothesis that P(·) is nonnegative"), the only
condition on the weights is nonnegativity; no row-sum bound is imposed. -/
structure Program (St : Type) (A : St → Type) where
  /-- The reward `r(s, a)`. -/
  r : (s : St) → A s → ℝ
  /-- The transition weight `p(t | s, a)`, written `p s a t`. -/
  p : (s : St) → A s → St → ℝ
  /-- `P(·)` is nonnegative. -/
  p_nonneg : ∀ s a t, 0 ≤ p s a t

/-- The set `F = ×_{s=1}^S A_s` of decision rules (p. 1636): a decision rule picks an action
`f s ∈ A s` in every state. -/
abbrev DecisionRule (St : Type) (A : St → Type) : Type := (s : St) → A s

/-- A policy `π = (f₁, f₂, ⋯)` with `f_N ∈ F` (p. 1636).

**Formalization Note.** Policies are indexed from `0`: `π 0` is Veinott's `f₁`, and in general
`π N` is `f_{N+1}`. -/
abbrev Policy (St : Type) (A : St → Type) : Type := ℕ → DecisionRule St A

variable {St : Type} {A : St → Type}

/-- The stationary policy `f^∞ = (f, f, ⋯)` (p. 1636). -/
def stationary (f : DecisionRule St A) : Policy St A := fun _ => f

/-- The policy `(g, π) = (g, f₁, f₂, ⋯)`: use `g` first, then follow `π` (p. 1637). -/
def cons (g : DecisionRule St A) (π : Policy St A) : Policy St A
  | 0 => g
  | n + 1 => π n

/-- The periodic policy `ᴺπ = (πᴺ, πᴺ, ⋯)` (p. 1636), which repeats the first `N` components
`πᴺ = (f₁, …, f_N)` of `π`. It is meant for `N ≥ 1`. -/
def periodicOf (N : ℕ) (π : Policy St A) : Policy St A := fun k => π (k % N)

/-- A policy is **periodic** if it is `ᴺπ'` for some `N ≥ 1` and some policy `π'` (p. 1636). -/
def IsPeriodic (π : Policy St A) : Prop := ∃ N : ℕ, 1 ≤ N ∧ ∃ π' : Policy St A, π = periodicOf N π'

/-- The norm `‖B‖ ≡ maxᵢ Σⱼ |bᵢⱼ|` of an `S × S` matrix (p. 1636): the maximum absolute row sum.

**Formalization Note.** This is defined explicitly; it is not Mathlib's default (entrywise
sup) matrix norm. -/
def rowSumNorm [Fintype St] [Nonempty St] (B : Matrix St St ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => ∑ j, |B i j|

namespace Program

variable [Fintype St] [DecidableEq St] (D : Program St A)

/-- `r(f)`, the `S × 1` vector whose `s`th component is `r(s, f(s))` (p. 1636). -/
def rvec (f : DecisionRule St A) : St → ℝ := fun s => D.r s (f s)

/-- `P(f)`, the `S × S` matrix whose `st`th element is `p(t | s, f(s))` (p. 1636). -/
def Pmat (f : DecisionRule St A) : Matrix St St ℝ := Matrix.of fun s t => D.p s (f s) t

/-- `Pᴺ(π) = P(f₁) ⋯ P(f_N)`, with `P⁰(π) = I` (p. 1636): the ordered product of the first
`N` transition matrices of `π`. With `π 0 = f₁`, `PN (N + 1) π = PN N π * P(π N)`. -/
def PN : ℕ → Policy St A → Matrix St St ℝ
  | 0, _ => 1
  | N + 1, π => PN N π * D.Pmat (π N)

/-- A policy `π` is **transient** if `Σ_{N=0}^∞ Pᴺ(π)` converges (p. 1636).

**Formalization Note.** Convergence is `Summable` in `Matrix St St ℝ` with its entrywise
topology; since every `Pᴺ(π)` is entrywise nonnegative this is absolute convergence. -/
def IsTransient (π : Policy St A) : Prop := Summable fun N => D.PN N π

/-- The vector of expected total returns (1), p. 1636:
`V(π) ≡ Σ_{N=0}^∞ Pᴺ(π) r(f_{N+1})`.

**Formalization Note.** With `π N = f_{N+1}` the `N`th summand is `Pᴺ(π) r(π N)`. The sum is
Lean's `tsum`; it is the genuine (absolutely convergent) series when `π` is transient, and an
uninformative default (`0` in each non-summable coordinate) otherwise, so every statement about
`V` supplies the transience it needs. -/
noncomputable def V (π : Policy St A) : St → ℝ := ∑' N, D.PN N π *ᵥ D.rvec (π N)

/-- `v(g, π*) ≡ V(g, π*) − V(π*)` (p. 1637, Lemma 1): the gain from using `g` first and then
following `π*`, relative to following `π*` from the start. -/
noncomputable def v (g : DecisionRule St A) (πs : Policy St A) : St → ℝ :=
  D.V (cons g πs) - D.V πs

end Program

end VeinottSensitiveDP.Transient


