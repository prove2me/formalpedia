-- Prove2me | Definitions.Def_MPECRelax_ScholtesConv_MPEC
-- name    : MPECRelax_ScholtesConv_MPEC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:59.16699+00:00
-- url     : https://prove2.me/theorems/bc328739-f9cf-4a64-aa1a-0ba3a83a9710
-- title:
--   (1), Definitions 2.3, 2.4: the MPEC, its index sets, weak and C-stationarity, TNLP(x*) and MPEC-MFCQ
-- statement:
--   This file sets up the mathematical program with equilibrium (complementarity) constraints (1) and the MPEC-tailored notions of §2.2.
--
--   The **MPEC** (1) is
--   $$\min f(x)\quad\text{s.t.}\quad g_i(x)\le0\ (i=1,\dots,m),\ \ h_i(x)=0\ (i=1,\dots,p),\ \ G_i(x)\ge0,\ H_i(x)\ge0,\ G_i(x)H_i(x)=0\ (i=1,\dots,l),$$
--   with data $f,g_i,h_i,G_i,H_i:\mathbb R^n\to\mathbb R$; the paper assumes them continuously differentiable (predicate $C^1$). Its feasible set is $X$. For a point $x^*$ the paper's index sets are
--   $$I_g=\{i\mid g_i(x^*)=0\},\quad I_{0+}=\{i\mid G_i(x^*)=0<H_i(x^*)\},\quad I_{00}=\{i\mid G_i(x^*)=H_i(x^*)=0\},\quad I_{+0}=\{i\mid G_i(x^*)>0=H_i(x^*)\}.$$
--
--   1. (**Definition 2.3(a)**) A feasible $x^*$ is **weakly stationary** if there are $\lambda\in\mathbb R^m$, $\mu\in\mathbb R^p$, $\gamma,\nu\in\mathbb R^l$ with
--   $$\nabla f(x^*)+\sum_{i=1}^m\lambda_i\nabla g_i(x^*)+\sum_{i=1}^p\mu_i\nabla h_i(x^*)-\sum_{i=1}^l\gamma_i\nabla G_i(x^*)-\sum_{i=1}^l\nu_i\nabla H_i(x^*)=0,$$
--   $\lambda\ge0$, $\lambda_ig_i(x^*)=0$ ($i=1,\dots,m$), $\gamma_i=0$ ($i\in I_{+0}$), $\nu_i=0$ ($i\in I_{0+}$).
--   2. (**Definition 2.3(b)**) $x^*$ is **C-stationary** if it is feasible and there are multipliers as in (a) which in addition satisfy $\gamma_i\nu_i\ge0$ for all $i\in I_{00}$.
--   3. The **tightened nonlinear program** TNLP$(x^*)$ has the constraints $g_i\le0$, $h_i=0$, and $G_i=0,\ H_i\ge0$ ($i\in I_{0+}$), $G_i\ge0,\ H_i=0$ ($i\in I_{+0}$), $G_i=H_i=0$ ($i\in I_{00}$).
--   4. (**Definition 2.4**) **MPEC-MFCQ** holds at $x^*$ if standard MFCQ holds at $x^*$ for TNLP$(x^*)$.
--
--   These are the stationarity concept and the constraint qualification in Theorem 3.1.
--
--   **Formalization Note** Indices are `Fin m`, `Fin p`, `Fin l` (0-based). Definition 2.3(a) is printed with two misprints ("$\mu_ih_i(x^*)$" and "$\lambda_ig_i(x^*)=0$ $(i=1,\dots,l)$"); the definition uses the evident $\mu_i\nabla h_i(x^*)$ and $i=1,\dots,m$. Both stationarity notions include feasibility of $x^*$, and C-stationarity uses one multiplier tuple for the weak-stationarity conditions and the sign condition. TNLP$(x^*)$ is an NLP whose constraints are indexed by subtypes ($I_{0+}$, $I_{+0}$, $I_{0+}\cup I_{00}$, $I_{+0}\cup I_{00}$), so a constraint exists exactly for the indices listed; absent constraints are not padded with zero functions. Its inequality constraints are written $-H_i\le0$, $-G_i\le0$. The $C^1$ assumption is a separate predicate carried as a hypothesis by every theorem.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, pp. 1, 5–6, (1), index sets (p. 5), Definition 2.3, TNLP(x*), Definition 2.4 (p. 6)

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP

open Filter Topology
open scoped RealInnerProductSpace

namespace MPECRelax.ScholtesConv

/-- The MPEC (1): minimize `f` subject to `g i ≤ 0`, `h i = 0`, `G i ≥ 0`, `H i ≥ 0`,
`G i * H i = 0`. -/
structure MPEC (n m p l : ℕ) where
  f : E n → ℝ
  g : Fin m → E n → ℝ
  h : Fin p → E n → ℝ
  G : Fin l → E n → ℝ
  H : Fin l → E n → ℝ

namespace MPEC

variable {n m p l : ℕ}

/-- Standing assumption (p. 1): `f, g_i, h_i, G_i, H_i` are continuously differentiable. -/
def IsC1 (P : MPEC n m p l) : Prop :=
  ContDiff ℝ 1 P.f ∧ (∀ i, ContDiff ℝ 1 (P.g i)) ∧ (∀ i, ContDiff ℝ 1 (P.h i)) ∧
    (∀ i, ContDiff ℝ 1 (P.G i)) ∧ ∀ i, ContDiff ℝ 1 (P.H i)

/-- `x` lies in the feasible set `X` of the MPEC (1). -/
def Feasible (P : MPEC n m p l) (x : E n) : Prop :=
  (∀ i, P.g i x ≤ 0) ∧ (∀ i, P.h i x = 0) ∧
    ∀ i, 0 ≤ P.G i x ∧ 0 ≤ P.H i x ∧ P.G i x * P.H i x = 0

/-- `I_g = {i | g_i(x) = 0}` (p. 5). -/
def Ig (P : MPEC n m p l) (x : E n) : Set (Fin m) := {i | P.g i x = 0}

/-- `I_{0+} = {i | G_i(x) = 0, H_i(x) > 0}` (p. 5). -/
def I0p (P : MPEC n m p l) (x : E n) : Set (Fin l) := {i | P.G i x = 0 ∧ 0 < P.H i x}

/-- `I_{00} = {i | G_i(x) = 0, H_i(x) = 0}` (p. 5). -/
def I00 (P : MPEC n m p l) (x : E n) : Set (Fin l) := {i | P.G i x = 0 ∧ P.H i x = 0}

/-- `I_{+0} = {i | G_i(x) > 0, H_i(x) = 0}` (p. 5). -/
def Ip0 (P : MPEC n m p l) (x : E n) : Set (Fin l) := {i | 0 < P.G i x ∧ P.H i x = 0}

/-- The weak-stationarity conditions of Definition 2.3(a) for given multipliers, with the
misprints of the page corrected (`μ_i ∇h_i`, and `λ_i g_i(x) = 0` for `i = 1, …, m`):
`∇f + ∑ λ_i ∇g_i + ∑ μ_i ∇h_i − ∑ γ_i ∇G_i − ∑ ν_i ∇H_i = 0`, `λ ≥ 0`, `λ_i g_i(x) = 0`,
`γ_i = 0` on `I_{+0}`, `ν_i = 0` on `I_{0+}`. -/
def WeakStatMult (P : MPEC n m p l) (x : E n) (lam : Fin m → ℝ) (mu : Fin p → ℝ)
    (γ ν : Fin l → ℝ) : Prop :=
  gradient P.f x + ∑ i, lam i • gradient (P.g i) x + ∑ i, mu i • gradient (P.h i) x
      - ∑ i, γ i • gradient (P.G i) x - ∑ i, ν i • gradient (P.H i) x = 0 ∧
    (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * P.g i x = 0) ∧
    (∀ i ∈ P.Ip0 x, γ i = 0) ∧ (∀ i ∈ P.I0p x, ν i = 0)

/-- Definition 2.3(a): `x` is feasible for (1) and weakly stationary. -/
def IsWeaklyStationary (P : MPEC n m p l) (x : E n) : Prop :=
  P.Feasible x ∧ ∃ lam mu γ ν, P.WeakStatMult x lam mu γ ν

/-- Definition 2.3(b): `x` is feasible for (1) and C-stationary: there are weak-stationarity
multipliers which in addition satisfy `γ_i ν_i ≥ 0` for all `i ∈ I_{00}`. -/
def IsCStationary (P : MPEC n m p l) (x : E n) : Prop :=
  P.Feasible x ∧ ∃ lam mu γ ν, P.WeakStatMult x lam mu γ ν ∧ ∀ i ∈ P.I00 x, 0 ≤ γ i * ν i

/-- The tightened nonlinear program TNLP(x*) (p. 6) as an NLP. Inequality constraints:
`g_i ≤ 0` (all `i`), `−H_i ≤ 0` (`i ∈ I_{0+}`), `−G_i ≤ 0` (`i ∈ I_{+0}`). Equality
constraints: `h_j = 0` (all `j`), `G_i = 0` (`i ∈ I_{0+} ∪ I_{00}`), `H_i = 0`
(`i ∈ I_{+0} ∪ I_{00}`). The index sets are those of `xs`; a constraint exists only for the
indices the paper lists. -/
def TNLP (P : MPEC n m p l) (xs : E n) :
    NLP n (Fin m ⊕ ↥(P.I0p xs) ⊕ ↥(P.Ip0 xs))
      (Fin p ⊕ ↥(P.I0p xs ∪ P.I00 xs) ⊕ ↥(P.Ip0 xs ∪ P.I00 xs)) where
  f := P.f
  g := Sum.elim P.g (Sum.elim (fun i x => -P.H i x) (fun i x => -P.G i x))
  h := Sum.elim P.h (Sum.elim (fun i => P.G i) (fun i => P.H i))

/-- Definition 2.4: MPEC-MFCQ holds at `xs` if standard MFCQ holds at `xs` for TNLP(xs). -/
def MPEC_MFCQ (P : MPEC n m p l) (xs : E n) : Prop :=
  (P.TNLP xs).IsMFCQ xs

end MPEC

end MPECRelax.ScholtesConv


