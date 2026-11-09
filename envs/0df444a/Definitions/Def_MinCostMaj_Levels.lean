-- Prove2me | Definitions.Def_MinCostMaj_Levels
-- name    : MinCostMaj_Levels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:05:02.509452+00:00
-- url     : https://prove2.me/theorems/b8da614d-94ac-4662-9484-938dc9c0b857
-- title:
--   Threshold conflicts, good levels and the level procedure
-- statement:
--   Fix a variable $v$ with potato $S=A^J_v$ and LP marginals $\lambda_v$, a probability vector on $S$; write $\lambda_v(B)=\sum_{b\in B}\lambda_v(b)$. Let $(t_i)_{i\ge1}$ be the threshold sequence.
--
--   1. **Threshold conflict** (Definition 5.1): $v\mapsto a$ conflicts with $t_i$ if there is $B\subseteq S$ with $a\notin B$ and $\lambda_v(B)<t_i\le\lambda_v(B\cup\{a\})$.
--   2. **Good level** (Definition 5.2): level $i$ is good for $v$ if no $a\in S$ has $\lambda_v(a)<t_i$ and conflicts with one of $t_1,\dots,t_i$.
--   3. $\ell(v,a)=i$ iff $\lambda_v(a)\in(2^{-i},2^{-(i-1)}]$.
--   4. **Level procedure**: start with $L=1$; while $L$ is not good, choose a witness $a$ (with $\lambda_v(a)<t_L$ and a conflict with one of $t_1,\dots,t_L$) of minimal $\lambda_v(a)$ and set $L:=\ell(v,a)+1$. The final value is the level $L(v)$.
--   5. **Truncated potato**: $A^I_v=\{a\in S:\lambda_v(a)\ge t_{L(v)}\}$.
--
--   The truncated potatoes define the random subinstance whose solutions the algorithm returns.
--
--   **Formalization Note** All notions are defined from $(S,\lambda_v,t)$ for one variable. The step uses the minimal marginal value directly ($\ell$ depends only on it). $L(v)$ is the first good iterate of the step from $1$; if no iterate were good the value would be $0$, which Lemma "Termination" excludes. $\ell$ of a nonpositive number is $0$ instead of $\infty$; witnesses always have positive marginal, so this case is never used.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Definitions 5.1 and 5.2, and the level procedure, p.11 (PDF p.12)

import Mathlib

namespace MinCostMaj

variable {D : Type*} [DecidableEq D]

/-- `λᵥ(B) = Σ_{b∈B} λᵥ(b)` (§5, p.10). -/
def lamSet (lam : D → ℝ) (B : Finset D) : ℝ := ∑ b ∈ B, lam b

/-- `λ` is a probability vector on the potato `S = A^J_v` (nonnegative, zero off `S`, total mass
`1`); the LP marginals of a feasible BLP solution are such vectors (Figure 3, p.20). -/
def IsProbVec (S : Finset D) (lam : D → ℝ) : Prop :=
  (∀ a, 0 ≤ lam a) ∧ (∀ a, a ∉ S → lam a = 0) ∧ ∑ a ∈ S, lam a = 1

/-- **Threshold conflict** (Definition 5.1, p.11).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Definition 5.1, p.11: "The assignment v ↦ a conflicts with ti if
there is B ⊆ A^J_v, a ∉ B, such that λv(B) < ti ≤ λv(B ∪ {a})."

`S = A^J_v`, `lam = λᵥ`, `t i = tᵢ`.

**Formalization Note.** All of §5's level notions concern one variable at a time and are defined
from `(S, λᵥ, t)` alone. Thresholds are `t : ℕ → ℝ` with `t i` the paper's `tᵢ` for `i ≥ 1`;
`t 0` is never used. -/
def Conflicts (S : Finset D) (lam : D → ℝ) (t : ℕ → ℝ) (i : ℕ) (a : D) : Prop :=
  ∃ B ⊆ S, a ∉ B ∧ lamSet lam B < t i ∧ t i ≤ lamSet lam (insert a B)

/-- **Good level** (Definition 5.2, p.11): "A level i is good for v if there is no a ∈ A^J_v such
that λv(a) < ti and v ↦ a conflicts with one of t1, . . . , ti." -/
def IsGood (S : Finset D) (lam : D → ℝ) (t : ℕ → ℝ) (i : ℕ) : Prop :=
  ¬ ∃ a ∈ S, lam a < t i ∧ ∃ j, 1 ≤ j ∧ j ≤ i ∧ Conflicts S lam t j a

/-- **The level of a value**, `ℓ(v, a) = i ⟺ λᵥ(a) ∈ (2^{−i}, 2^{−(i−1)}]` (p.11): the least `i`
with `2^{−i} < λᵥ(a)`.

**Formalization Note.** For `x ∈ (0, 1]` this is the `i ≥ 1` with `x ∈ (2^{−i}, 2^{−(i−1)}]`. The
paper sets `ℓ = ∞` when `λᵥ(a) = 0`; here the set is empty and the value is `0`, but this case is
never used: a witness of Step 2 conflicts with a threshold, so its marginal is positive. -/
noncomputable def ell (x : ℝ) : ℕ := sInf {i : ℕ | ((1 : ℝ) / 2) ^ i < x}

open Classical in
/-- The witnesses of Step 2 at the current level `L` (p.11): values `a ∈ A^J_v` with
`λᵥ(a) < t_L` that conflict with one of `t₁, …, t_L`. Level `L` is good iff there are none. -/
noncomputable def witnesses (S : Finset D) (lam : D → ℝ) (t : ℕ → ℝ) (L : ℕ) : Finset D :=
  S.filter (fun a => lam a < t L ∧ ∃ j, 1 ≤ j ∧ j ≤ L ∧ Conflicts S lam t j a)

/-- **One step of the level procedure** (p.11, Step 2): if level `L` is not good, choose a witness
`a` of minimal `λᵥ(a)` and set `L := ℓ(v, a) + 1`; a good level is left unchanged.

**Formalization Note.** `ℓ(v, a)` depends only on `λᵥ(a)`, so the choice among minimal witnesses
does not matter; the step uses the minimal marginal value directly. -/
noncomputable def step (S : Finset D) (lam : D → ℝ) (t : ℕ → ℝ) (L : ℕ) : ℕ :=
  if h : (witnesses S lam t L).Nonempty then ell ((witnesses S lam t L).inf' h lam) + 1 else L

open Classical in
/-- **The level `L(v)` of a variable** (p.11, Steps 1–3): start at `L = 1` and apply Step 2 while
`L` is not good; `L(v)` is the first good level reached.

**Formalization Note.** Defined as the first good iterate `step^[n] 1`; if no iterate were good the
value would be `0` (never a level). Lemma "Termination" shows this case does not occur. -/
noncomputable def level (S : Finset D) (lam : D → ℝ) (t : ℕ → ℝ) : ℕ :=
  if h : ∃ n, IsGood S lam t ((step S lam t)^[n] 1) then (step S lam t)^[Nat.find h] 1 else 0

open Classical in
/-- **The truncated potato** (p.11): `A^I_v := {a ∈ A^J_v : λv(a) ≥ t_{L(v)}}`. -/
noncomputable def truncPot (S : Finset D) (lam : D → ℝ) (t : ℕ → ℝ) : Finset D :=
  S.filter (fun a => t (level S lam t) ≤ lam a)

end MinCostMaj


