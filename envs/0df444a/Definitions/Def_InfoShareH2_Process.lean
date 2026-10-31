-- Prove2me | Definitions.Def_InfoShareH2_Process
-- name    : InfoShareH2_Process
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:05.543356+00:00
-- url     : https://prove2.me/theorems/4c873f83-2c0a-47b7-a9d5-3f2ffb121171
-- title:
--   Gaussian white noise, the order process in $L^2$, linear pasts and invertibility
-- statement:
--   This module supplies the stochastic layer used by Propositions 4 and 5.
--
--   1. **Gaussian white noise** (Assumption 1(a)): $(\epsilon_t)_{t\in\mathbb Z}$ is an i.i.d. sequence of $N(0,\sigma_\epsilon^2)$ random variables.
--   2. **The order process** (5): $O_t=d+\sum_{n\ge0}\tilde\psi_n\epsilon_{t-n}$, an element of $L^2(\Omega)$ when $\sum\tilde\psi_n^2<\infty$.
--   3. **Linear past** (Definition 1): $M_X(t)=\overline{\operatorname{sp}}\{1,X_t,X_{t-1},\dots\}$, the closed linear span in $L^2(\Omega)$.
--   4. **Invertibility** (Definition 2): a process $X$ is invertible with respect to $(\epsilon_t)$ if $M_X(t)=M_\epsilon(t)$ for every $t$.
--
--   **Formalization Note** Random variables are identified with their classes in $L^2(\Omega)$; a function that is not square integrable is sent to $0$, which never happens for the Gaussian variables and constants used here. The series (5) converges unconditionally in $L^2$ and is written as an unordered sum.
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, Assumption 1(a) and (5) p.10, Definition 1 p.13, Definition 2 p.14

import Mathlib

open Filter Topology MeasureTheory ProbabilityTheory

set_option autoImplicit false

namespace InfoShareH2

variable {Ω : Type} [MeasurableSpace Ω]

open Classical in
/-- **A random variable as an element of `L²(Ω)`.**

**Formalization Note** `toL2 P f` is the class of `f` in `L²(P)` when `f ∈ L²(P)`, and `0`
otherwise. It is applied only to Gaussian variables and constants, which lie in `L²`. -/
noncomputable def toL2 (P : Measure Ω) (f : Ω → ℝ) : Lp ℝ 2 P :=
  if h : MemLp f 2 P then h.toLp f else 0

/-- **Gaussian white noise** (Assumption 1(a), p.10): `{ε_t}_{t ∈ ℤ}` is an i.i.d. sequence of
`N(0, σ_ε²)` random variables. -/
def IsGaussianWhiteNoise (P : Measure Ω) (σε : ℝ) (ε : ℤ → Ω → ℝ) : Prop :=
  (∀ t, Measurable (ε t)) ∧ iIndepFun ε P ∧
    ∀ t, P.map (ε t) = gaussianReal 0 (σε ^ 2).toNNReal

/-- **The order process** (5), p.10: `O_t = d + ∑_{n≥0} ψ̃_n ε_{t−n}`, as an element of `L²(P)`.

**Formalization Note** For `∑ ψ̃_n² < ∞` the series of orthogonal terms converges unconditionally
in `L²`, so it is a `tsum` in `Lp ℝ 2 P`. -/
noncomputable def orderL2 (P : Measure Ω) (ψ : ℕ → ℝ) (d : ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) :
    Lp ℝ 2 P :=
  toL2 P (fun _ => d) + ∑' n : ℕ, ψ n • toL2 P (ε (t - n))

/-- **Linear past** (Definition 1, p.13): `M_X(t) := sp{1, X_t, X_{t−1}, …}`, the closed linear
span in `L²(P)` (the Hilbert space with the covariance inner product). -/
noncomputable def linPast (P : Measure Ω) (X : ℤ → Lp ℝ 2 P) (t : ℤ) : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ (insert (toL2 P (fun _ => (1 : ℝ))) (Set.range fun k : ℕ => X (t - k)))).topologicalClosure

/-- **Invertibility** (Definition 2, p.14): `X` is invertible with respect to the white noise
`{ε_t}` if `M_X(t) = M_ε(t)` (for every `t`). -/
def IsInvertibleWRT (P : Measure Ω) (X : ℤ → Lp ℝ 2 P) (ε : ℤ → Ω → ℝ) : Prop :=
  ∀ t, linPast P X t = linPast P (fun s => toL2 P (ε s)) t

end InfoShareH2


