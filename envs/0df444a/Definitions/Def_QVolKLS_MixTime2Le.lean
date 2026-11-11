-- Prove2me | Definitions.Def_QVolKLS_MixTime2Le
-- name    : QVolKLS_MixTime2Le
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:38:31.399115+00:00
-- url     : https://prove2.me/theorems/85743a16-6fe9-477a-aac2-bce8ffdf5d82
-- title:
--   Finite reversible chains, the discriminant $D_\pi\oplus0$, the warm-start mixing time $\tau_{\mathrm{mix},2}$, exact block-encodings
-- statement:
--   Let $\Omega$ be a finite feasible set of register labels and $\pi$ a law positive on $\Omega$ and zero elsewhere. A **finite reversible chain** on $\Omega$ is a stochastic matrix $P(x,y)$, $x,y\in\Omega$, with stationary law $\pi$ and detailed balance $\pi(x)P(x,y)=\pi(y)P(y,x)$.
--
--   1. $P$ is **positive** if its spectrum lies in $[0,1]$, i.e. $\langle f,Pf\rangle_\pi=\sum_{x,y}\pi(x)f(x)P(x,y)f(y)\ge0$ for all real $f$.
--   2. $P$ is **ergodic** if $\ker(I-P)=\mathrm{span}\{1\}$: every $f$ with $Pf=f$ is constant.
--   3. The **discriminant** is $D_\pi(y,x)=\sqrt{\pi(x)/\pi(y)}\,P(x,y)$; $D_\pi\oplus0$ extends it by zero to all register labels.
--   4. The total variation distance is $d_{\mathrm{TV}}(\mu,\nu)=\sup_A|\mu(A)-\nu(A)|$, and $\tau_{\mathrm{mix},2}(\eta,\pi;P)\le t$ means: for every start $\nu$ with $d\nu/d\pi\le2$ there is $j\le t$ with $d_{\mathrm{TV}}(\nu P^j,\pi)\le\eta$. This is the paper's
--   $$
--   \tau_{\mathrm{mix},2}(\eta,\pi;P)=\sup_{\nu:\,d\nu/d\pi\le 2}\ \inf\{t\in\mathbb N: d_{\mathrm{TV}}(\nu P^t,\pi)\le\eta\}\le t .
--   $$
--   5. A unitary $U$ on $b+s$ qubits is an exact $(1,b,0)$-**block-encoding** of an operator $A$ on $s$ qubits if $(\langle0^b|\otimes I)U(|0^b\rangle\otimes I)=A$.
--
--   These are the hypotheses of the input-dependent reflection theorem (Theorem 3.3).
--
--   **Formalization Note** `IsReversibleChainOn`, `IsPositiveChain`, `IsErgodicChain`, `distAfter`, `finTV`, `MixTime2Le`, `discriminantExt`, `IsZeroExtBlockEncoding`. The mixing condition is unfolded, so no convention for an empty infimum enters.
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §2, p.21 (block-encoding); §2.3, pp.22–23 ((12), τ_mix, τ_mix,2); §3.2, p.27; §5.2, p.39, (39)

import Definitions.Def_QVolKLS_fourthMomentNorm

set_option autoImplicit false

namespace QVolKLS

open QAlgorithms

/-!
# Finite reversible chains, the discriminant, warm-start mixing, zero-extended block-encodings

R. Zhang, *Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation*,
arXiv:2610.04987 (held version, sha256 eee7a45e…): §2, p.21 (block-encodings), §2.3, p.22
(reversible, positive, ergodic; the discriminant `D_π = J_π P J_π†`, (12)), §2.3, p.23 (total
variation, `τ_mix`, `τ_mix,2`), §3.2, p.27 (the chain on a feasible subset `Ω` of the register, and
the block-encoding of `D_π ⊕ 0`), §5.2, p.39, (39) (`D_π(y, x) = √(π(x)/π(y)) P(x, y)`).

**Formalization Note.**
* The chain lives on a feasible finite set `Ω` of register labels; `P x y` is the transition
  probability from `x` to `y` for `x, y ∈ Ω` (values off `Ω` are never used). The law `π` is positive
  on `Ω`, zero off `Ω`, and sums to `1`.
* Reversible: `π(x)P(x, y) = π(y)P(y, x)`. Then `P` is self-adjoint on `L²(π)`, and **positive**
  (spectrum in `[0, 1]`) is the quadratic-form condition `⟨f, Pf⟩_π ≥ 0` for real `f` (the spectrum
  of a stochastic matrix already lies in `[−1, 1]`). **Ergodic** (`ker(I − P) = span{1}`) is: every
  real `f` with `Pf = f` on `Ω` is constant on `Ω` (complex `f` reduce to real and imaginary parts).
* `distAfter Ω P ν j` is `νP^j`. `finTV μ ν = sup_A |μ(A) − ν(A)|` over all subsets `A`.
* `MixTime2Le Ω η π P t` is `τ_mix,2(η, π; P) ≤ t`, unfolded from p.23: for every start `ν` with
  `dν/dπ ≤ 2` (i.e. `ν ≤ 2π` pointwise) some `j ≤ t` has `d_TV(νP^j, π) ≤ η`. This is the value of
  the `inf`/`sup` in `ℕ ∪ {∞}`; no `sInf ∅ = 0` convention enters.
* `discriminantExt Ω π P` is `D_π ⊕ 0`: `D_π(y, x)` on `Ω × Ω`, zero elsewhere.
* `IsZeroExtBlockEncoding U A`: `U` is unitary on `b + s` qubits (ancilla `b` wires first) and
  `(⟨0^b| ⊗ I) U (|0^b⟩ ⊗ I) = A` exactly: a `(1, b, 0)`-block-encoding (p.21).
-/

/-- A finite reversible Markov chain `P` on the feasible set `Ω` with stationary law `π`. -/
structure IsReversibleChainOn {ι : Type*} [Fintype ι] (Ω : Finset ι) (P : ι → ι → ℝ)
    (π : ι → ℝ) : Prop where
  /-- `π` is positive on `Ω`. -/
  law_pos : ∀ x ∈ Ω, 0 < π x
  /-- `π` vanishes off `Ω`. -/
  law_zero : ∀ x, x ∉ Ω → π x = 0
  /-- `π` is a probability law. -/
  law_sum : ∑ x, π x = 1
  /-- Transition probabilities are nonnegative. -/
  nonneg : ∀ x ∈ Ω, ∀ y ∈ Ω, 0 ≤ P x y
  /-- Each row on `Ω` sums to `1`. -/
  stochastic : ∀ x ∈ Ω, ∑ y ∈ Ω, P x y = 1
  /-- `π` is stationary: `πP = π`. -/
  stationary : ∀ y ∈ Ω, ∑ x ∈ Ω, π x * P x y = π y
  /-- Detailed balance: `π(x)P(x, y) = π(y)P(y, x)`. -/
  reversible : ∀ x ∈ Ω, ∀ y ∈ Ω, π x * P x y = π y * P y x

/-- Zhang, §2.3, p.22: `P` is **positive** (spectrum in `[0, 1]`): `⟨f, Pf⟩_π ≥ 0` for all real
`f` on `Ω`. -/
def IsPositiveChain {ι : Type*} (Ω : Finset ι) (P : ι → ι → ℝ) (π : ι → ℝ) : Prop :=
  ∀ f : ι → ℝ, 0 ≤ ∑ x ∈ Ω, ∑ y ∈ Ω, π x * f x * P x y * f y

/-- Zhang, §2.3, p.22: `P` is **ergodic** (`ker(I − P) = span{1}`): a real `f` with `Pf = f` on `Ω`
is constant on `Ω`. -/
def IsErgodicChain {ι : Type*} (Ω : Finset ι) (P : ι → ι → ℝ) : Prop :=
  ∀ f : ι → ℝ, (∀ x ∈ Ω, ∑ y ∈ Ω, P x y * f y = f x) → ∀ x ∈ Ω, ∀ y ∈ Ω, f x = f y

/-- The law `νP^j` after `j` steps of the chain on `Ω` from the start `ν` (supported on `Ω`). -/
noncomputable def distAfter {ι : Type*} [DecidableEq ι] (Ω : Finset ι) (P : ι → ι → ℝ) (ν : ι → ℝ) :
    ℕ → ι → ℝ
  | 0 => ν
  | j + 1 => fun y =>
      if y ∈ Ω then ∑ x ∈ Ω, distAfter Ω P ν j x * P x y else 0

/-- Zhang, §2.3, p.23: total variation `d_TV(µ, ν) = sup_A |µ(A) − ν(A)|` on a finite set. -/
noncomputable def finTV {ι : Type*} (μ ν : ι → ℝ) : ℝ :=
  ⨆ A : Finset ι, |∑ x ∈ A, (μ x - ν x)|

/-- Zhang, §2.3, p.23: `τ_mix,2(η, π; P) ≤ t`: from every two-warm start `ν` (`dν/dπ ≤ 2`) the
chain reaches total variation `≤ η` from `π` within `t` steps. -/
def MixTime2Le {ι : Type*} [Fintype ι] [DecidableEq ι] (Ω : Finset ι) (η : ℝ) (π : ι → ℝ) (P : ι → ι → ℝ)
    (t : ℕ) : Prop :=
  ∀ ν : ι → ℝ, (∀ x, 0 ≤ ν x) → ∑ x, ν x = 1 → (∀ x, ν x ≤ 2 * π x) →
    ∃ j ≤ t, finTV (distAfter Ω P ν j) π ≤ η

/-- Zhang, (12) and (39): the zero-extended **discriminant** `D_π ⊕ 0`,
`D_π(y, x) = √(π(x)/π(y)) P(x, y)` for `x, y ∈ Ω`, and `0` elsewhere. -/
noncomputable def discriminantExt {ι : Type*} (Ω : Finset ι) (π : ι → ℝ) (P : ι → ι → ℝ) :
    Matrix ι ι ℂ :=
  haveI := Classical.decEq ι
  Matrix.of fun y x =>
    if x ∈ Ω ∧ y ∈ Ω then ((Real.sqrt (π x / π y) * P x y : ℝ) : ℂ) else 0

/-- Zhang, §2, p.21: `U` is an exact `(1, b, 0)`-block-encoding of `A` (ancilla wires first):
`U` is unitary and `(⟨0^b| ⊗ I) U (|0^b⟩ ⊗ I) = A`. -/
def IsZeroExtBlockEncoding {b s : ℕ} (U : Matrix (Qubits (b + s)) (Qubits (b + s)) ℂ)
    (A : Matrix (Qubits s) (Qubits s) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (Qubits (b + s)) ℂ ∧
    ∀ y x : Qubits s, U (joinReg (fun _ => false) y) (joinReg (fun _ => false) x) = A y x

end QVolKLS


