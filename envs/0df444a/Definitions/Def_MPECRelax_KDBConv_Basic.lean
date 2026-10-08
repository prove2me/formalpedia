-- Prove2me | Definitions.Def_MPECRelax_KDBConv_Basic
-- name    : MPECRelax_KDBConv_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:11.546359+00:00
-- url     : https://prove2.me/theorems/6ab0b88b-bdd2-4987-83cf-47f6c5552028
-- title:
--   (1), (2), Definitions 2.1, 2.3, 2.4, R^KDB(t), (10): the MPEC, NLPs, CPLD, KKT points, weak and M-stationarity, TNLP(x*), MPEC-CPLD, the Kadrani et al. relaxation
-- statement:
--   This file sets up the objects of Hoheisel, Kanzow and Schwartz's convergence analysis of the relaxation method of Kadrani, Dussault and Benchakroun for mathematical programs with complementarity constraints.
--
--   **Nonlinear programs.** A nonlinear program (2) on $\mathbb R^n$ is
--   $$\min f(x)\quad\text{s.t.}\quad g_i(x)\le 0\ (i\in\iota),\qquad h_j(x)=0\ (j\in\kappa),$$
--   with finitely many constraints. Its active set at $x$ is $I_g(x)=\{i \mid g_i(x)=0\}$.
--
--   1. *Positive-linear dependence* (Definition 2.1): for $I_1\subseteq\iota$, $I_2\subseteq\kappa$, the gradients $\{\nabla g_i(x)\mid i\in I_1\}\cup\{\nabla h_j(x)\mid j\in I_2\}$ are positive-linearly dependent if there are scalars $\alpha_i\ge 0$ ($i\in I_1$) and $\beta_j$ ($j\in I_2$), not all zero, with $\sum_{i\in I_1}\alpha_i\nabla g_i(x)+\sum_{j\in I_2}\beta_j\nabla h_j(x)=0$.
--   2. *CPLD* (p. 4) holds at a feasible $x^*$ if for all $I_1\subseteq I_g(x^*)$ and $I_2\subseteq\kappa$ whose gradients are positive-linearly dependent at $x^*$, there is a neighbourhood $N(x^*)$ on which the gradients $\{\nabla g_i(x)\mid i\in I_1\}\cup\{\nabla h_j(x)\mid j\in I_2\}$ are linearly dependent for every $x\in N(x^*)$.
--   3. *KKT multipliers and stationary points* (p. 5): $(\lambda,\mu)$ are KKT multipliers at $x$ if $\lambda\ge 0$, $\lambda_i g_i(x)=0$ for all $i$, and $\nabla f(x)+\sum_i\lambda_i\nabla g_i(x)+\sum_j\mu_j\nabla h_j(x)=0$. A *stationary point* is a feasible $x$ admitting KKT multipliers (the $x$-part of a KKT point).
--
--   **The MPEC (1).** Given $f,g_i,h_i,G_i,H_i:\mathbb R^n\to\mathbb R$ ($i\le m$, $i\le p$, $i\le l$ respectively), the MPEC is
--   $$\min f(x)\ \text{ s.t. }\ g(x)\le 0,\ h(x)=0,\ G(x)\ge 0,\ H(x)\ge 0,\ G_i(x)H_i(x)=0\ (i=1,\dots,l),$$
--   with feasible set $X$. The data are assumed continuously differentiable (standing assumption, p. 1). At a feasible $x^*$ the index sets are $I_g=\{i\mid g_i(x^*)=0\}$, $I_{0+}=\{i\mid G_i(x^*)=0<H_i(x^*)\}$, $I_{00}=\{i\mid G_i(x^*)=H_i(x^*)=0\}$, $I_{+0}=\{i\mid G_i(x^*)>0=H_i(x^*)\}$.
--
--   4. *Weak stationarity* (Definition 2.3(a)): $x^*\in X$ and there are $\lambda\in\mathbb R^m$, $\mu\in\mathbb R^p$, $\gamma,\nu\in\mathbb R^l$ with
--   $$\nabla f(x^*)+\sum_{i=1}^m\lambda_i\nabla g_i(x^*)+\sum_{i=1}^p\mu_i\nabla h_i(x^*)-\sum_{i=1}^l\gamma_i\nabla G_i(x^*)-\sum_{i=1}^l\nu_i\nabla H_i(x^*)=0,$$
--   $\lambda\ge0$, $\lambda_ig_i(x^*)=0$ ($i=1,\dots,m$), $\gamma_i=0$ ($i\in I_{+0}$), $\nu_i=0$ ($i\in I_{0+}$).
--   5. *M-stationarity* (Definition 2.3(c)): the same multipliers can be chosen so that, in addition, for every $i\in I_{00}$ either $\gamma_i>0$ and $\nu_i>0$, or $\gamma_i\nu_i=0$.
--   6. *The tightened program* TNLP$(x^*)$ (p. 6): minimize $f$ subject to $g\le 0$, $h=0$, $G_i=0\le H_i$ ($i\in I_{0+}$), $G_i\ge 0=H_i$ ($i\in I_{+0}$), $G_i=H_i=0$ ($i\in I_{00}$). *MPEC-CPLD* (Definition 2.4) holds at $x^*$ if standard CPLD holds for TNLP$(x^*)$ at $x^*$.
--
--   **The relaxation of Kadrani et al.** (p. 14). For $t>0$ the relaxed program $R^{KDB}(t)$ is
--   $$\min f(x)\ \text{ s.t. }\ g(x)\le 0,\ h(x)=0,\ G_i(x)\ge -t,\ H_i(x)\ge -t,\ (G_i(x)-t)(H_i(x)-t)\le 0\ (i=1,\dots,l).$$
--   For $x$ and $t$ the index sets (10) used in the convergence proof are $I_G(x,t)=\{i\mid G_i(x)+t=0\}$, $I_H(x,t)=\{i\mid H_i(x)+t=0\}$, $I^{0*}_\Phi(x,t)=\{i\mid (G_i(x)-t)(H_i(x)-t)=0,\ G_i(x)-t=0\}$, $I^{*0}_\Phi(x,t)=\{i\mid (G_i(x)-t)(H_i(x)-t)=0,\ H_i(x)-t=0\}$. Given multipliers $\gamma_i$ of the product constraints, the proof of Theorem 3.5 puts
--   $$\eta^G_i:=-\gamma_i(H_i(x)-t),\qquad \eta^H_i:=-\gamma_i(G_i(x)-t).$$
--
--   These objects are the vocabulary of every statement of the mission: the goal (Theorem 3.5) assumes KKT points of $R^{KDB}(t_k)$ and MPEC-CPLD, and concludes M-stationarity.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $\nabla$ is Mathlib's `gradient`; the C¹ standing assumption is the separate predicate `MPEC.IsC1`, carried as a hypothesis by the theorems (without it `gradient` is $0$ at nondifferentiable points). Indices are 0-based (`Fin m`, `Fin p`, `Fin l`); $m,p,l$ may be $0$. Sets of gradients are indexed families: linear (in)dependence is `LinearIndependent ℝ` of a family indexed by a disjoint union of subtypes, so a repeated gradient counts as dependent. In positive-linear dependence "not all of them being zero" is read as "not all of the $\alpha_i$ and $\beta_j$ are zero", and coefficients outside $I_1$, $I_2$ are set to $0$. The neighbourhood in CPLD is `∀ᶠ y in 𝓝 x`. Definition 2.3 is encoded with its two misprints corrected ($\mu_i\nabla h_i$ instead of $\mu_ih_i$; $\lambda_ig_i(x^*)=0$ for $i=1,\dots,m$), and the M-condition uses the same multipliers as weak stationarity; both stationarity notions include feasibility. TNLP$(x^*)$ is an NLP whose constraints are indexed by subtypes, so it has exactly the constraints the paper lists: inequalities $g_i\le0$, $-H_i\le 0$ ($i\in I_{0+}$), $-G_i\le 0$ ($i\in I_{+0}$) and equalities $h_j=0$, $G_i=0$ ($i\in I_{0+}\cup I_{00}$), $H_i=0$ ($i\in I_{+0}\cup I_{00}$). $R^{KDB}(t)$ is an NLP with inequality index `Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l` (in this order: $g_i\le 0$, $-(G_i+t)\le0$, $-(H_i+t)\le 0$, $(G_i-t)(H_i-t)\le 0$); `kdbLam`, `kdbAlpha`, `kdbBeta`, `kdbGamma` read off the four blocks $\lambda,\alpha,\beta,\gamma$ of a multiplier vector.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, pp. 1–7 and 14–15: (1), (2), Definition 2.1, CPLD (p. 4), KKT points (p. 5), index sets (p. 5), Definitions 2.3, 2.4, TNLP(x*) (p. 6), R^KDB(t) and (10) (p. 14), η^{G,k}, η^{H,k} (p. 15)

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP

namespace MPECRelax.KDBConv

open Filter Topology

/-- A standard nonlinear program (2): minimize `f` subject to `g i x ≤ 0` (`i : ι`) and
`h j x = 0` (`j : κ`). -/
structure NLP (n : ℕ) (ι κ : Type) where
  f : MPECRelax.ScholtesConv.E n → ℝ
  g : ι → MPECRelax.ScholtesConv.E n → ℝ
  h : κ → MPECRelax.ScholtesConv.E n → ℝ

namespace NLP

variable {n : ℕ} {ι κ : Type}

/-- `x` is feasible for the NLP (2). -/
def Feasible (P : NLP n ι κ) (x : MPECRelax.ScholtesConv.E n) : Prop :=
  (∀ i, P.g i x ≤ 0) ∧ ∀ j, P.h j x = 0

/-- The active inequality constraints `I_g = {i | g_i(x) = 0}` (p. 3). -/
def activeSet (P : NLP n ι κ) (x : MPECRelax.ScholtesConv.E n) : Set ι := {i | P.g i x = 0}

/-- Definition 2.1: the family `{∇g_i(x) | i ∈ I₁} ∪ {∇h_j(x) | j ∈ I₂}` is
positive-linearly dependent: there are scalars `α_i ≥ 0` (`i ∈ I₁`) and `β_j` (`j ∈ I₂`),
not all zero, with `∑ α_i ∇g_i(x) + ∑ β_j ∇h_j(x) = 0`. Coefficients outside `I₁`, `I₂`
are zero. -/
def PosLinDep [Fintype ι] [Fintype κ] (P : NLP n ι κ) (x : MPECRelax.ScholtesConv.E n) (I₁ : Set ι) (I₂ : Set κ) :
    Prop :=
  ∃ (α : ι → ℝ) (β : κ → ℝ), (∀ i ∈ I₁, 0 ≤ α i) ∧ (∀ i ∉ I₁, α i = 0) ∧
    (∀ j ∉ I₂, β j = 0) ∧ ((∃ i, α i ≠ 0) ∨ (∃ j, β j ≠ 0)) ∧
    ∑ i, α i • gradient (P.g i) x + ∑ j, β j • gradient (P.h j) x = 0

/-- CPLD (p. 4): for all `I₁ ⊆ I_g(x)` and `I₂` such that the gradients indexed by
`I₁`, `I₂` are positive-linearly dependent at `x`, there is a neighbourhood of `x` on which
the family `{∇g_i(y) | i ∈ I₁} ∪ {∇h_j(y) | j ∈ I₂}` (indexed by `I₁ ⊕ I₂`) is linearly
dependent. -/
def IsCPLD [Fintype ι] [Fintype κ] (P : NLP n ι κ) (x : MPECRelax.ScholtesConv.E n) : Prop :=
  ∀ (I₁ : Set ι) (I₂ : Set κ), I₁ ⊆ P.activeSet x → P.PosLinDep x I₁ I₂ →
    ∀ᶠ y in 𝓝 x, ¬ LinearIndependent ℝ
      (Sum.elim (fun i : ↥I₁ => gradient (P.g i.1) y) (fun j : ↥I₂ => gradient (P.h j.1) y))

/-- `(lam, mu)` are KKT multipliers of the NLP at `x` (p. 5): `lam ≥ 0`,
`lam_i g_i(x) = 0` for all `i`, and `∇f(x) + ∑ lam_i ∇g_i(x) + ∑ mu_j ∇h_j(x) = 0`. -/
def KKTMult [Fintype ι] [Fintype κ] (P : NLP n ι κ) (x : MPECRelax.ScholtesConv.E n) (lam : ι → ℝ) (mu : κ → ℝ) :
    Prop :=
  (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * P.g i x = 0) ∧
    gradient P.f x + ∑ i, lam i • gradient (P.g i) x + ∑ j, mu j • gradient (P.h j) x = 0

/-- `x` is a stationary point of the NLP: the `x`-part of a KKT point (p. 5), i.e. `x` is
feasible and admits KKT multipliers. -/
def IsKKTPoint [Fintype ι] [Fintype κ] (P : NLP n ι κ) (x : MPECRelax.ScholtesConv.E n) : Prop :=
  P.Feasible x ∧ ∃ (lam : ι → ℝ) (mu : κ → ℝ), P.KKTMult x lam mu

end NLP

/-- The MPEC (1): minimize `f` subject to `g_i ≤ 0` (`i < m`), `h_i = 0` (`i < p`),
`G_i ≥ 0`, `H_i ≥ 0`, `G_i H_i = 0` (`i < l`). -/
structure MPEC (n m p l : ℕ) where
  f : MPECRelax.ScholtesConv.E n → ℝ
  g : Fin m → MPECRelax.ScholtesConv.E n → ℝ
  h : Fin p → MPECRelax.ScholtesConv.E n → ℝ
  G : Fin l → MPECRelax.ScholtesConv.E n → ℝ
  H : Fin l → MPECRelax.ScholtesConv.E n → ℝ

namespace MPEC

variable {n m p l : ℕ}

/-- Standing assumption (p. 1): all data are continuously differentiable. -/
def IsC1 (P : MPEC n m p l) : Prop :=
  ContDiff ℝ 1 P.f ∧ (∀ i, ContDiff ℝ 1 (P.g i)) ∧ (∀ i, ContDiff ℝ 1 (P.h i)) ∧
    (∀ i, ContDiff ℝ 1 (P.G i)) ∧ ∀ i, ContDiff ℝ 1 (P.H i)

/-- `x ∈ X`, the feasible set of the MPEC (1). -/
def Feasible (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Prop :=
  (∀ i, P.g i x ≤ 0) ∧ (∀ i, P.h i x = 0) ∧
    ∀ i, 0 ≤ P.G i x ∧ 0 ≤ P.H i x ∧ P.G i x * P.H i x = 0

/-- `I_g = {i | g_i(x) = 0}` (p. 5). -/
def Ig (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Set (Fin m) := {i | P.g i x = 0}

/-- `I_0+ = {i | G_i(x) = 0, H_i(x) > 0}` (p. 5). -/
def I0p (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Set (Fin l) := {i | P.G i x = 0 ∧ 0 < P.H i x}

/-- `I_00 = {i | G_i(x) = 0, H_i(x) = 0}` (p. 5). -/
def I00 (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Set (Fin l) := {i | P.G i x = 0 ∧ P.H i x = 0}

/-- `I_+0 = {i | G_i(x) > 0, H_i(x) = 0}` (p. 5). -/
def Ip0 (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Set (Fin l) := {i | 0 < P.G i x ∧ P.H i x = 0}

/-- The weak-stationarity conditions of Definition 2.3(a) for given multipliers
`λ ∈ ℝ^m`, `µ ∈ ℝ^p`, `γ, ν ∈ ℝ^l` (the two misprints of the paper corrected:
`µ_i ∇h_i(x)` in the sum, and `λ_i g_i(x) = 0` for `i = 1, …, m`):
`∇f + ∑ λ_i ∇g_i + ∑ µ_i ∇h_i − ∑ γ_i ∇G_i − ∑ ν_i ∇H_i = 0`, `λ ≥ 0`, `λ_i g_i(x) = 0`,
`γ_i = 0` on `I_+0`, `ν_i = 0` on `I_0+`. -/
def WeakStatMult (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) (lam : Fin m → ℝ) (mu : Fin p → ℝ)
    (γ ν : Fin l → ℝ) : Prop :=
  gradient P.f x + ∑ i, lam i • gradient (P.g i) x + ∑ i, mu i • gradient (P.h i) x
      - ∑ i, γ i • gradient (P.G i) x - ∑ i, ν i • gradient (P.H i) x = 0 ∧
    (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * P.g i x = 0) ∧
    (∀ i ∈ P.Ip0 x, γ i = 0) ∧ (∀ i ∈ P.I0p x, ν i = 0)

/-- Definition 2.3(a): `x` is feasible and weakly stationary. -/
def IsWeaklyStationary (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Prop :=
  P.Feasible x ∧ ∃ lam mu γ ν, P.WeakStatMult x lam mu γ ν

/-- Definition 2.3(c): `x` is feasible and M-stationary: one multiplier tuple satisfies
the weak-stationarity conditions and, for every `i ∈ I_00`, either `γ_i > 0` and `ν_i > 0`,
or `γ_i ν_i = 0`. -/
def IsMStationary (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Prop :=
  P.Feasible x ∧ ∃ lam mu γ ν, P.WeakStatMult x lam mu γ ν ∧
    ∀ i ∈ P.I00 x, (0 < γ i ∧ 0 < ν i) ∨ γ i * ν i = 0

/-- The tightened program TNLP(x*) (p. 6), as an NLP whose constraints are exactly those
listed in the paper (subtype index sets, no padding): inequalities `g_i ≤ 0` (all `i`),
`-H_i ≤ 0` (`i ∈ I_0+`), `-G_i ≤ 0` (`i ∈ I_+0`); equalities `h_j = 0` (all `j`),
`G_i = 0` (`i ∈ I_0+ ∪ I_00`), `H_i = 0` (`i ∈ I_+0 ∪ I_00`). -/
def TNLP (P : MPEC n m p l) (xs : MPECRelax.ScholtesConv.E n) :
    NLP n (Fin m ⊕ ↥(P.I0p xs) ⊕ ↥(P.Ip0 xs))
      (Fin p ⊕ ↥(P.I0p xs ∪ P.I00 xs) ⊕ ↥(P.Ip0 xs ∪ P.I00 xs)) where
  f := P.f
  g := Sum.elim P.g (Sum.elim (fun i x => -P.H i x) (fun i x => -P.G i x))
  h := Sum.elim P.h (Sum.elim (fun i => P.G i) (fun i => P.H i))

open Classical in
/-- Definition 2.4: MPEC-CPLD holds at `xs` if standard CPLD holds for TNLP(xs) at `xs`. -/
def MPEC_CPLD (P : MPEC n m p l) (xs : MPECRelax.ScholtesConv.E n) : Prop := (P.TNLP xs).IsCPLD xs

/-- The relaxed program R^KDB(t) of Kadrani, Dussault and Benchakroun (p. 14) as an NLP:
inequalities `g_i ≤ 0` (index `inl i`), `-(G_i + t) ≤ 0` (`inr (inl i)`),
`-(H_i + t) ≤ 0` (`inr (inr (inl i))`), `(G_i − t)(H_i − t) ≤ 0` (`inr (inr (inr i))`);
equalities `h_j = 0`. Its feasible set is `X^KDB(t)`. -/
def RKDB (P : MPEC n m p l) (t : ℝ) : NLP n (Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l) (Fin p) where
  f := P.f
  g := Sum.elim P.g (Sum.elim (fun i x => -(P.G i x + t))
         (Sum.elim (fun i x => -(P.H i x + t)) (fun i x => (P.G i x - t) * (P.H i x - t))))
  h := P.h

/-- (10), p. 14: `I_G(x, t) = {i | G_i(x) + t = 0}`. -/
def IGt (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) (t : ℝ) : Set (Fin l) := {i | P.G i x + t = 0}

/-- (10), p. 14: `I_H(x, t) = {i | H_i(x) + t = 0}`. -/
def IHt (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) (t : ℝ) : Set (Fin l) := {i | P.H i x + t = 0}

/-- (10), p. 14: `I^{0*}_Φ(x, t) = {i ∈ I_Φ(x, t) | G_i(x) − t = 0}`, where
`I_Φ(x, t) = {i | (G_i(x) − t)(H_i(x) − t) = 0}`. -/
def IPhi0s (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) (t : ℝ) : Set (Fin l) :=
  {i | (P.G i x - t) * (P.H i x - t) = 0 ∧ P.G i x - t = 0}

/-- (10), p. 14: `I^{*0}_Φ(x, t) = {i ∈ I_Φ(x, t) | H_i(x) − t = 0}`. -/
def IPhis0 (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) (t : ℝ) : Set (Fin l) :=
  {i | (P.G i x - t) * (P.H i x - t) = 0 ∧ P.H i x - t = 0}

/-- The multiplier `λ_i` of `g_i ≤ 0` in a multiplier vector of R^KDB(t). -/
def kdbLam (Λ : Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l → ℝ) : Fin m → ℝ := fun i => Λ (Sum.inl i)

/-- The multiplier `α_i` of `G_i ≥ −t` in a multiplier vector of R^KDB(t). -/
def kdbAlpha (Λ : Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l → ℝ) : Fin l → ℝ :=
  fun i => Λ (Sum.inr (Sum.inl i))

/-- The multiplier `β_i` of `H_i ≥ −t` in a multiplier vector of R^KDB(t). -/
def kdbBeta (Λ : Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l → ℝ) : Fin l → ℝ :=
  fun i => Λ (Sum.inr (Sum.inr (Sum.inl i)))

/-- The multiplier `γ_i` of `(G_i − t)(H_i − t) ≤ 0` in a multiplier vector of R^KDB(t). -/
def kdbGamma (Λ : Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l → ℝ) : Fin l → ℝ :=
  fun i => Λ (Sum.inr (Sum.inr (Sum.inr i)))

/-- Proof of Theorem 3.5, p. 15: `η^G_i := −γ_i (H_i(x) − t)`. -/
def etaG (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) (t : ℝ) (γ : Fin l → ℝ) : Fin l → ℝ :=
  fun i => -(γ i * (P.H i x - t))

/-- Proof of Theorem 3.5, p. 15: `η^H_i := −γ_i (G_i(x) − t)`. -/
def etaH (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) (t : ℝ) (γ : Fin l → ℝ) : Fin l → ℝ :=
  fun i => -(γ i * (P.G i x - t))

end MPEC

end MPECRelax.KDBConv


