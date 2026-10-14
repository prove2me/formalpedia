-- Prove2me | Definitions.Def_LambdaVaRAmb_Comono_Setting
-- name    : LambdaVaRAmb_Comono_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:16.141977+00:00
-- url     : https://prove2.me/theorems/0a3db5a4-ddc2-4ad3-bf2c-27e9038d9306
-- title:
--   pp. 5–7, 21, 39 — capacities, ΛVaR (1), ℋ_I, comonotonic same-sign allocations 𝔸⁺ₙ(X), the comonotonic inf-convolution ⊞, atomless capacities, 𝔽ₙ
-- statement:
--   This file fixes the model of §2 and §6 of Liu and Schied, *Lambda Value-at-Risk under ambiguity and risk sharing*.
--
--   **Random variables.** $(\Omega,\mathcal F)$ is a measurable space and $\mathcal X$ is a set of real random variables that the paper leaves unspecified, asking only that it have "good enough properties, such as $\mathcal X=\mathcal X_0$ or $\mathcal X_1$" ($\mathcal X_0$: bounded random variables; $\mathcal X_1$: all random variables). Here $\mathcal X$ is any set of functions $\Omega\to\mathbb R$ such that
--
--   1. every $X\in\mathcal X$ is $\mathcal F$-measurable;
--   2. every bounded measurable $X$ lies in $\mathcal X$;
--   3. $(X-c)\mathbb 1_A+d\in\mathcal X$ for $X\in\mathcal X$, $A\in\mathcal F$ and $c,d\in\mathbb R$;
--   4. $f(X)\in\mathcal X$ for $X\in\mathcal X$ and every increasing, $1$-Lipschitz $f:\mathbb R\to\mathbb R$ with $f(0)=0$.
--
--   Both $\mathcal X_0$ and $\mathcal X_1$ satisfy these conditions.
--
--   **Capacities.** A capacity is a set function $w:\mathcal F\to[0,1]$ that is increasing ($A\subseteq B\Rightarrow w(A)\le w(B)$) with $w(\emptyset)=0$ and $w(\Omega)=1$. It is continuous if $w(A_n)\to0$ whenever $A_n\downarrow\emptyset$. It is atomless if there is a bounded random variable $Y$ such that $x\mapsto w(Y>x)$ is continuous on $\mathbb R$.
--
--   **Lambda functions and ΛVaR.** $\mathcal H$ is the set of functions $\Lambda:\mathbb R\to(0,1)$ and $\mathcal H_I$ its increasing (non-decreasing) members. For a capacity $w$, $\Lambda:\mathbb R\to\mathbb R$ and a random variable $X$,
--   $$\Lambda\mathrm{VaR}^w(X)=\inf\{x\in\mathbb R: w(X>x)\le\Lambda(x)\}\in[-\infty,\infty],\qquad \inf\emptyset=\infty .$$
--
--   **Comonotonic allocations.** For $n$ agents, $\mathbb A_n(X)$ is the set of $(X_1,\dots,X_n)\in\mathcal X^n$ with $X_1+\dots+X_n=X$. The tuple is comonotonic if there are increasing $f_1,\dots,f_n$ with $f_i(X_1+\dots+X_n)=X_i$ for all $i$, and the components have the same sign if no two of them take strictly opposite signs at any state. $\mathbb A_n^+(X)$ is the set of comonotonic same-sign allocations, and for $\rho_1,\dots,\rho_n$ with values in $[-\infty,\infty]$
--   $$\boxplus_{i=1}^n\rho_i(X)=\inf\Big\{\sum_{i=1}^n\rho_i(X_i):(X_1,\dots,X_n)\in\mathbb A_n^+(X)\Big\}.$$
--   An optimal allocation is an element of $\mathbb A_n^+(X)$ attaining this infimum.
--
--   **Splits of the identity.** $\mathbb F_n$ is the set of $(f_1,\dots,f_n)$ with $f_1+\dots+f_n=\mathrm{id}$ and each $f_i$ increasing, continuous and with $f_i(0)=0$. For $f:\mathbb R\to\mathbb R$ and $z\in[-\infty,\infty]$, $f(z)$ means $f(z)$ for real $z$, $\inf_x f(x)$ for $z=-\infty$ and $\sup_x f(x)$ for $z=+\infty$ (the limits of an increasing $f$).
--
--   These are the objects of Theorem 4 (comonotonic risk sharing) and of its proof.
--
--   **Formalization Note** Set functions are `Set Ω → ℝ`, and the capacity axioms are imposed on measurable sets only; values on non-measurable sets are never read, because every event used is $\{X>x\}$ with $X$ measurable. ΛVaR is an infimum in `EReal`, so it is $+\infty$ on an empty set and $-\infty$ when the set is unbounded below, as in the paper. "Increasing" is `Monotone`. Allocations are indexed by `Fin n` and the sum constraint is pointwise. The conditions on $\mathcal X$ are the disclosed reading of "good enough properties": they are what the proof of Theorem 4 uses (bounded test variables, splits $f(X)$). "sign$(X_i)$ are the same" is read weakly as $X_i(\omega)X_j(\omega)\ge0$ for all $i,j,\omega$: the literal reading with sign$(0)=+1$ would exclude Theorem 4's own optimal allocation $(X,0,\dots,0)$ whenever $X$ takes a negative value. The extension of $f$ to $\pm\infty$ is the convention needed to read the paper's $f_i\big((\Lambda_i\circ f_i)\mathrm{VaR}^{w_i}(X)\big)$ when that ΛVaR is infinite.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, pp. 5–7 (§2, (1)), p. 21 (§6, footnote 2), p. 39 (proof of Theorem 4, 𝔽ₙ)

import Mathlib
import Definitions.Def_LambdaVaRAmb_InfConv_Setting
import Definitions.Def_LambdaVaRAmb_Robust_Setting

namespace LambdaVaRAmb.Comono

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Footnote 2, p. 21: `X₁, …, Xₙ` are comonotonic if there exist increasing `f₁, …, fₙ` with
`fᵢ(X₁ + ⋯ + Xₙ) = Xᵢ` for all `i`. -/
def IsComonotonic {n : ℕ} (Xs : Fin n → Ω → ℝ) : Prop :=
  ∃ f : Fin n → ℝ → ℝ, (∀ i, Monotone (f i)) ∧ ∀ i ω, f i (∑ j, Xs j ω) = Xs i ω

/-- p. 21, "sign(Xᵢ) are the same", in the weak reading: no two components have strictly
opposite signs at any `ω` (see the Formalization Note). -/
def SameSign {n : ℕ} (Xs : Fin n → Ω → ℝ) : Prop := ∀ i j ω, 0 ≤ Xs i ω * Xs j ω

/-- p. 21: `𝔸⁺ₙ(X)`, comonotonic allocations with components of the same sign. -/
def ComonoAllocations (dom : Set (Ω → ℝ)) (n : ℕ) (X : Ω → ℝ) : Set (Fin n → Ω → ℝ) :=
  {Xs | Xs ∈ LambdaVaRAmb.InfConv.Allocations dom n X ∧ IsComonotonic Xs ∧ SameSign Xs}

/-- p. 21: `⊞ᵢ ρᵢ(X) = inf {Σᵢ ρᵢ(Xᵢ) : (X₁, …, Xₙ) ∈ 𝔸⁺ₙ(X)}`, in `EReal`. -/
noncomputable def comonoInfConv (dom : Set (Ω → ℝ)) {n : ℕ} (ρ : Fin n → (Ω → ℝ) → EReal)
    (X : Ω → ℝ) : EReal :=
  ⨅ Xs ∈ ComonoAllocations dom n X, ∑ i, ρ i (Xs i)

/-- p. 21: `(X₁*, …, Xₙ*) ∈ 𝔸⁺ₙ(X)` is an optimal (comonotonic) allocation of `X` for
`ρ₁, …, ρₙ` if it is a minimizer of the infimum defining `⊞ᵢ ρᵢ(X)`. -/
def IsComonoOptimal (dom : Set (Ω → ℝ)) {n : ℕ} (ρ : Fin n → (Ω → ℝ) → EReal)
    (X : Ω → ℝ) (Xs : Fin n → Ω → ℝ) : Prop :=
  Xs ∈ ComonoAllocations dom n X ∧ ∑ i, ρ i (Xs i) = comonoInfConv dom ρ X

/-- p. 21: `w` is atomless if some bounded random variable `Y` has `x ↦ w(Y > x)` continuous
on `ℝ`. -/
def IsAtomlessCapacity (w : Set Ω → ℝ) : Prop :=
  ∃ Y : Ω → ℝ, Measurable Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
    Continuous (fun x : ℝ => w {ω | x < Y ω})

/-- Proof of Theorem 4, p. 39: `𝔽ₙ = {(f₁, …, fₙ) : f₁ + ⋯ + fₙ = id, all fᵢ increasing and
continuous, fᵢ(0) = 0}`. -/
def splitsFn (n : ℕ) : Set (Fin n → ℝ → ℝ) :=
  {f | (∀ x, ∑ i, f i x = x) ∧ ∀ i, Monotone (f i) ∧ Continuous (f i) ∧ f i 0 = 0}

/-- Proof of Theorem 4, pp. 39–40: a function `f : ℝ → ℝ` applied to a value in `[-∞, ∞]`, as
the page does in `fᵢ((Λᵢ ∘ fᵢ)VaR^{wᵢ}(X))`: at a real point it is `f`, at `-∞` it is
`inf_x f(x)` and at `+∞` it is `sup_x f(x)` (the limits of an increasing `f`). -/
noncomputable def extendEReal (f : ℝ → ℝ) (z : EReal) : EReal :=
  if z = ⊥ then ⨅ x, (f x : EReal)
  else if z = ⊤ then ⨆ x, (f x : EReal)
  else (f z.toReal : EReal)

end LambdaVaRAmb.Comono


