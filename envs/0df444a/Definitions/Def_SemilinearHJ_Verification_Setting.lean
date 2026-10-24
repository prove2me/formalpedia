-- Prove2me | Definitions.Def_SemilinearHJ_Verification_Setting
-- name    : SemilinearHJ_Verification_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:11.944606+00:00
-- url     : https://prove2.me/theorems/47e06022-cb5a-4626-9082-42be1c6dcfbc
-- title:
--   §2.1, §3, §4, pp. 4–5, 7–9, 11–12 — polytope X, TX(x), B_r, running cost (3.1), paths Φ_T, path cost (2.2), (SP), (TP), C(x0, x), Hamiltonian (3.4), ‖Ψ‖∞, a.e. conditions (3.9)/(3.10), Definitions 1–2
-- statement:
--   This file sets up the state-constrained control problem with semilinear running costs of Sandholm, Tran and Arigapudi.
--
--   **State space.** $X\subset\mathbb R^n$ is a polytope, the convex hull of finitely many points (at least one). Its dimension $m$ is the dimension of its affine hull, whose direction subspace is the tangent space $TX$; $X^\circ$ is the relative interior of $X$. The tangent cone of $X$ at $x$ is
--   $$TX(x)=\{t(y-x):\ y\in X,\ t\ge 0\}.$$
--   The norm $|u|=\sum_{i=1}^n|u_i|$ is the $\ell^1$ norm, and for $r>0$, $B_r=\{u\in TX:\ |u|\le r\}$.
--
--   **Running cost and paths.** Given $\Psi:X\to\mathbb R^n_+$ and $r>0$, the running cost (3.1) is
--   $$L(x,v)=\begin{cases}\sum_{i=1}^n\Psi_i(x)[v_i]_+ & \text{if } v\in TX(x)\cap B_r,\\ +\infty&\text{otherwise,}\end{cases}$$
--   with $[a]_+=\max(a,0)$. $\Phi_T$ is the set of Lipschitz continuous paths $\phi:[0,T]\to X$ ($T\ge0$), and the path cost (2.2) is $c(\phi)=\int_0^T L(\phi(t),\dot\phi(t))\,dt\in[0,+\infty]$.
--
--   **Value functions.** For sets $X_0, Y\subseteq X$,
--   $$V(x)=\inf\{c(\phi):\ \phi\in\Phi_T,\ T\ge 0,\ \phi(0)\in X_0,\ \phi(T)=x\}\quad\text{(SP)},$$
--   $$W(x)=\inf\{c(\phi):\ \phi\in\Phi_T,\ T\ge 0,\ \phi(0)=x,\ \phi(T)\in Y\}\quad\text{(TP)},$$
--   and $C(x_0,x)=\inf\{c(\phi):\ \phi\in\Phi_T,\ T\ge0,\ \phi(0)=x_0,\ \phi(T)=x\}$; all three take values in $[0,+\infty]$, with $\inf\emptyset=+\infty$.
--
--   **Hamiltonian.** $H(x,u)=\max_{v\in TX\cap B_r}\big(\langle u,v\rangle-\langle\Psi(x),[v]_+\rangle\big)$ (3.4), and $\|\Psi\|_\infty=\max_{x\in X}|\Psi(x)|$.
--
--   **Almost-everywhere subsolutions.** $DV(x)=w$ means $w\in TX$ and $V$ is differentiable at $x$ relative to $X$ with derivative $z\mapsto\langle w,z\rangle$. Condition (3.9) (first line) says that for almost every $x\in X^\circ$ (with respect to $m$-dimensional Hausdorff measure) $H(x,DV(x))\le 0$; (3.10) (first line) says $H(x,-DW(x))\le0$ for almost every $x\in X^\circ$.
--
--   **Viscosity solutions of (4.1)** (Definitions 1–2). A function $V$ continuous on $X$ with $V=0$ on $X_0$ is a viscosity subsolution if $H(x_0,D\varphi(x_0))\le0$ whenever $\varphi$ is $C^\infty$ and $V-\varphi$ has a local maximum (relative to $X$) at $x_0\in X^\circ\setminus X_0$; a viscosity supersolution if $H(x_0,D\varphi(x_0))\ge0$ whenever $V-\varphi$ has a local minimum at $x_0\in X\setminus X_0$; a viscosity solution if both; and a maximal viscosity solution if moreover $V\ge\hat V$ on $X$ for every viscosity solution $\hat V$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The ambient space is `EuclideanSpace ℝ (Fin n)`; the paper's $|\cdot|$ is the separate $\ell^1$ function `l1`. Costs and value functions are `ℝ≥0∞`-valued, so an infimum over no path is $+\infty$, not a junk $0$. $\dot\phi$ is `derivWithin φ (Icc 0 T)` (it exists a.e., $\phi$ being Lipschitz) and the integral is the lower Lebesgue integral. $H$ is a real `sSup` over the image of the compact nonempty set $B_r$ (it contains $0$) under a continuous function, so it is a genuine maximum. "Almost every $x\in X^\circ$" uses `μH[m]` with $m=\dim TX$, restricted to `intrinsicInterior ℝ X`, so it is not vacuous when $m<n$. Test functions are $C^\infty$ on all of $\mathbb R^n$ (`ContDiff ℝ ∞`), and $D\varphi(x_0)$ is `gradient ϕ x0`; $H$ only sees its component in $TX$. Functions defined on $X$ are Lean functions on $\mathbb R^n$ whose values off $X$ are never used.
-- source:
--   Sandholm, Tran & Arigapudi, Hamilton-Jacobi Equations with Semilinear Costs and State Constraints, with Applications to Large Deviations in Games, author's manuscript (July 4, 2018; Math. Oper. Res. doi:10.1287/moor.2020.1114), pp. 4–5, 7–9, 11–12, §2.1, §3, §4, Equations (2.2), (SP), (TP), (3.1), (3.3)–(3.4), (3.9)–(3.10), (4.1), Definitions 1–2

import Mathlib

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory ContDiff

/-- The ambient space `ℝⁿ`, with its Euclidean structure (the paper's norm `|·|` is the separate
`ℓ¹` function `l1` below). -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `X ⊆ ℝⁿ` is a polytope: the convex hull of a finite nonempty set of points (§2.1, p. 4). Its
dimension `m` is `Module.finrank ℝ (vectorSpan ℝ X)`, unrestricted. -/
def IsPolytope {n : ℕ} (X : Set (E n)) : Prop :=
  ∃ S : Finset (E n), S.Nonempty ∧ X = convexHull ℝ (S : Set (E n))

/-- The paper's norm `|v| = ∑ᵢ |vᵢ|`, the `ℓ¹` norm on `ℝⁿ` (p. 5). -/
def l1 {n : ℕ} (v : E n) : ℝ := ∑ i, |v i|

/-- The tangent cone `TX(x) = {t (y - x) : y ∈ X, t ≥ 0}` (p. 4). -/
def tanCone {n : ℕ} (X : Set (E n)) (x : E n) : Set (E n) :=
  {v | ∃ y ∈ X, ∃ t : ℝ, 0 ≤ t ∧ v = t • (y - x)}

/-- `B_r = {u ∈ TX : |u| ≤ r}`, where `TX = vectorSpan ℝ X` is the direction of the affine hull
of `X` (p. 5). -/
def ballR {n : ℕ} (X : Set (E n)) (r : ℝ) : Set (E n) :=
  {u | u ∈ vectorSpan ℝ X ∧ l1 u ≤ r}

open Classical in
/-- The running cost (3.1): `L(x, v) = ∑ᵢ Ψᵢ(x) [vᵢ]₊` if `v ∈ TX(x) ∩ B_r`, and `+∞` otherwise
(p. 7). -/
noncomputable def runCost {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (x v : E n) : ℝ≥0∞ :=
  if v ∈ tanCone X x ∧ v ∈ ballR X r then ENNReal.ofReal (∑ i, Ψ x i * max (v i) 0) else ⊤

/-- `φ ∈ Φ_T`: `T ≥ 0` and `φ` restricted to `[0, T]` is a Lipschitz continuous path into `X`
(p. 4). Values of `φ` outside `[0, T]` play no role. -/
def IsPath {n : ℕ} (X : Set (E n)) (T : ℝ) (φ : ℝ → E n) : Prop :=
  0 ≤ T ∧ (∃ K : NNReal, LipschitzOnWith K φ (Set.Icc 0 T)) ∧ Set.MapsTo φ (Set.Icc 0 T) X

/-- The path cost (2.2) with running cost (3.1): `c(φ) = ∫₀ᵀ L(φ(t), φ̇(t)) dt` (p. 5), as a lower
integral in `[0, +∞]`; `φ̇` is the derivative of `φ` within `[0, T]` (it exists for almost every
`t`, `φ` being Lipschitz). -/
noncomputable def pathCost {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (T : ℝ)
    (φ : ℝ → E n) : ℝ≥0∞ :=
  ∫⁻ t in Set.Icc 0 T, runCost X Ψ r (φ t) (derivWithin φ (Set.Icc 0 T) t)

/-- `C(x₀, x) = inf {c(φ) : φ ∈ Φ_T for some T ≥ 0, φ(0) = x₀, φ(T) = x}` (p. 12). -/
noncomputable def minCost {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (x0 x : E n) : ℝ≥0∞ :=
  ⨅ (T : ℝ) (φ : ℝ → E n) (_ : IsPath X T φ ∧ φ 0 = x0 ∧ φ T = x), pathCost X Ψ r T φ

/-- The value function of the source problem (SP) for `X₀`:
`V(x) = inf {c(φ) : φ ∈ Φ_T for some T ≥ 0, φ(0) ∈ X₀, φ(T) = x}` (p. 5). -/
noncomputable def srcVal {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (X0 : Set (E n))
    (x : E n) : ℝ≥0∞ :=
  ⨅ (T : ℝ) (φ : ℝ → E n) (_ : IsPath X T φ ∧ φ 0 ∈ X0 ∧ φ T = x), pathCost X Ψ r T φ

/-- The value function of the target problem (TP) for `Y`:
`W(x) = inf {c(φ) : φ ∈ Φ_T for some T ≥ 0, φ(0) = x, φ(T) ∈ Y}` (p. 5). -/
noncomputable def tgtVal {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (Y : Set (E n))
    (x : E n) : ℝ≥0∞ :=
  ⨅ (T : ℝ) (φ : ℝ → E n) (_ : IsPath X T φ ∧ φ 0 = x ∧ φ T ∈ Y), pathCost X Ψ r T φ

/-- The maximized Hamiltonian (3.4): `H(x, u) = max_{v ∈ TX ∩ B_r} (⟨u, v⟩ - ⟨Ψ(x), [v]₊⟩)`
(pp. 7–8). `B_r` is compact and contains `0`, so the supremum is attained. -/
noncomputable def ham {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (x u : E n) : ℝ :=
  sSup ((fun v => inner ℝ u v - ∑ i, Ψ x i * max (v i) 0) '' ballR X r)

/-- `‖Ψ‖∞ = max_{x ∈ X} |Ψ(x)|`, with `|·|` the `ℓ¹` norm (p. 8). -/
noncomputable def psiNorm {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) : ℝ :=
  sSup ((fun x => l1 (Ψ x)) '' X)

/-- The `m`-dimensional Hausdorff measure, `m = dim X`, restricted to the relative interior `X°`:
the measure behind "for almost all `x ∈ X°`" in (3.9), (3.10). -/
noncomputable def interiorMeasure {n : ℕ} (X : Set (E n)) : MeasureTheory.Measure (E n) :=
  (μH[(Module.finrank ℝ (vectorSpan ℝ X) : ℝ)]).restrict (intrinsicInterior ℝ X)

/-- `DV(x) = w`: `w ∈ TX` and `V` has the derivative `z ↦ ⟨w, z⟩` at `x` relative to `X` (p. 4 and
p. 13, where `DV(x) ∈ L(TX, ℝ)` is identified with the unique such `w ∈ TX`). -/
def relGrad {n : ℕ} (X : Set (E n)) (V : E n → ℝ) (x w : E n) : Prop :=
  w ∈ vectorSpan ℝ X ∧ HasFDerivWithinAt V (innerSL ℝ w) X x

/-- First line of (3.9): `H(x, DV(x)) ≤ 0` for almost all `x ∈ X°` (p. 9). -/
def AESubsol {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (V : E n → ℝ) : Prop :=
  ∀ᵐ x ∂(interiorMeasure X), ∃ w, relGrad X V x w ∧ ham X Ψ r x w ≤ 0

/-- First line of (3.10): `H(x, -DW(x)) ≤ 0` for almost all `x ∈ X°` (p. 9). -/
def AESubsolNeg {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (W : E n → ℝ) : Prop :=
  ∀ᵐ x ∂(interiorMeasure X), ∃ w, relGrad X W x w ∧ ham X Ψ r x (-w) ≤ 0

/-- Definition 1 (p. 11), subsolution part: `V ∈ C(X)`, `V = 0` on `X₀`, and for every test
function `ϕ ∈ C^∞` such that `V - ϕ` has a (local, relative to `X`) maximum at
`x₀ ∈ X° ∖ X₀`, `H(x₀, Dϕ(x₀)) ≤ 0`. -/
def IsViscSub {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (X0 : Set (E n))
    (V : E n → ℝ) : Prop :=
  ContinuousOn V X ∧ (∀ x ∈ X0, V x = 0) ∧
    ∀ ϕ : E n → ℝ, ContDiff ℝ ∞ ϕ → ∀ x0 ∈ intrinsicInterior ℝ X \ X0,
      IsLocalMaxOn (fun x => V x - ϕ x) X x0 → ham X Ψ r x0 (gradient ϕ x0) ≤ 0

/-- Definition 1 (p. 11), supersolution part: `V ∈ C(X)`, `V = 0` on `X₀`, and for every test
function `ϕ ∈ C^∞` such that `V - ϕ` has a (local, relative to `X`) minimum at `x₀ ∈ X ∖ X₀`,
`H(x₀, Dϕ(x₀)) ≥ 0`. -/
def IsViscSuper {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (X0 : Set (E n))
    (V : E n → ℝ) : Prop :=
  ContinuousOn V X ∧ (∀ x ∈ X0, V x = 0) ∧
    ∀ ϕ : E n → ℝ, ContDiff ℝ ∞ ϕ → ∀ x0 ∈ X \ X0,
      IsLocalMinOn (fun x => V x - ϕ x) X x0 → 0 ≤ ham X Ψ r x0 (gradient ϕ x0)

/-- Definition 1 (p. 11): a viscosity solution of (4.1). -/
def IsViscSol {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (X0 : Set (E n))
    (V : E n → ℝ) : Prop :=
  IsViscSub X Ψ r X0 V ∧ IsViscSuper X Ψ r X0 V

/-- Definition 2 (p. 12): a maximal viscosity solution of (4.1). -/
def IsMaxViscSol {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (X0 : Set (E n))
    (V : E n → ℝ) : Prop :=
  IsViscSol X Ψ r X0 V ∧ ∀ V' : E n → ℝ, IsViscSol X Ψ r X0 V' → ∀ x ∈ X, V' x ≤ V x

end SemilinearHJ.Verification


