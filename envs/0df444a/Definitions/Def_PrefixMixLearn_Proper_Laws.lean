-- Prove2me | Definitions.Def_PrefixMixLearn_Proper_Laws
-- name    : PrefixMixLearn_Proper_Laws
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:44:47.176723+00:00
-- url     : https://prove2.me/theorems/638604e4-8438-491b-8bab-76a261228b7e
-- title:
--   Laws on $\{0,1\}^T$, products $Q_\mu$, classes $\mathcal P_{\alpha,T}$, $\mathcal M_{2,\alpha,T}$, total variation, $\mathrm{OPT}_\alpha$, $\mathrm{OPT}^{(2)}_\alpha$, prefix masses
-- statement:
--   Fix an integer $T\ge 1$ and write $X_T=\{0,1\}^T$. A **law** on a finite set is a nonnegative function summing to one; a finite **signed measure** is any real function. For $\mu\in[0,1]^T$ the **product law** is $Q_\mu=\bigotimes_{i=1}^T\mathrm{Ber}(\mu_i)$, i.e. $Q_\mu(x)=\prod_i \mu_i^{x_i}(1-\mu_i)^{1-x_i}$, and the **two-product mixture** with weight $w$ is $(1-w)Q_\nu+wQ_\mu$. **Total variation** is $d_{TV}(R,S)=\tfrac12\sum_x|R(x)-S(x)|$.
--
--   For $0<\alpha<1/2$ the balanced classes are
--   $$\mathcal P_{\alpha,T}=\{Q_\mu:\mu\in[\alpha,1-\alpha]^T\},\qquad \mathcal M_{2,\alpha,T}=\{(1-w)Q_\nu+wQ_\mu: w\in[0,1],\ \mu,\nu\in[\alpha,1-\alpha]^T\},$$
--   (repeated components and $w\in\{0,1\}$ allowed) and the benchmarks are $\mathrm{OPT}_\alpha(P)=\min_{Q\in\mathcal P_{\alpha,T}}d_{TV}(P,Q)$ and $\mathrm{OPT}^{(2)}_\alpha(P)=\min_{M\in\mathcal M_{2,\alpha,T}}d_{TV}(P,M)$. Also $u=\alpha(1-\alpha)$.
--
--   For a (signed) $R$ and $x\in X_T$, the **prefix mass** $R[x_{\le t}]$ is the total mass of the points agreeing with $x$ on the first $t$ coordinates ($t=0$: total mass), and the next-bit ratio at coordinate $i$ is $R[x_{<i}1]/R[x_{<i}]$; for a full-support law it is $R(X_i=1\mid x_{<i})$. $R(S)$ is the mass of a set, and the probability of an event of $n$ independent draws from $R$ is the sum of $\prod_k R(x_k)$ over the tuples in the event.
--
--   **Formalization Note.** `Cube T = Fin T → Bool`, coordinate `i : Fin T` is the paper's $i.\mathrm{val}+1$. Laws are real functions with `IsLaw`. `OPT`, `OPT2` are infima (`sInf`) over the images; the classes are nonempty for $\alpha\le 1/2$ and distances are $\ge 0$, so these are the paper's minima (which exist by compactness). `condOne R x i` is the ratio $R[x_{<i}1]/R[x_{<i}]$ and returns $0$ if the parent mass is $0$; every statement using it has full support or a positivity guarantee.
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 3–4 (PDF 5–6), §2 and (2.1)–(2.2); p. 13 (PDF 15); p. 22 (PDF 24)

import Mathlib

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace PrefixMixLearn.Proper

/-!
# Laws on `{0,1}^T`, product laws, the balanced classes and the benchmarks

Saravanan, *Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional
Samples*, STOC 2027 submission (manuscript sha256 9c359910…), §2, pp. 3–4 (PDF 5–6), (2.1)–(2.2);
Appendix A preamble, p. 13 (PDF 15); Appendix C preamble, p. 22 (PDF 24).

* `Cube T = Fin T → Bool` is `X_T = {0,1}^T`; coordinate `i : Fin T` is the paper's coordinate
  `i.val + 1`.
* A law (or a finite signed measure) on a finite set is a real function; `IsLaw` says it is a
  probability law, `FullSupport` that every point has positive mass.
* `prodLaw μ = Q_μ = ⊗ Ber(μ_i)`; `mixLaw w ν μ = (1 − w) Q_ν + w Q_μ`.
* `tv R S = ½ Σ |R − S|`.
* `InBox α μ` : `μ ∈ [α, 1 − α]^T`. `PClass α T = P_{α,T}`, `M2Class α T = M_{2,α,T}` (weights
  `w ∈ [0,1]`, repeated components allowed).
* `OPT α P`, `OPT2 α P`: the infima of `tv P ·` over the two classes. The classes are nonempty
  for `α ≤ 1/2` and `tv ≥ 0`, so these infima are the paper's minima (which exist by compactness).
* `prefMass R x t = R[x_{≤t}]`, the mass of the cylinder of the first `t` bits of `x`
  (`t = 0` gives the total mass); `condOne R x i = R[x_{<i}1] / R[x_{<i}]`, the next-bit
  conditional mean `R(1 | x_{<i})` (a signed ratio for a signed `R`).
* `massOf R S = R(S)`; `iidProb R n E` is the probability of `E` under `n` independent draws
  from `R`.
-/

/-- The cube `X_T = {0,1}^T`. -/
abbrev Cube (T : ℕ) := Fin T → Bool

/-- `R` is a probability law on the finite set `Ω`. -/
def IsLaw {Ω : Type*} [Fintype Ω] (R : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ R x) ∧ ∑ x, R x = 1

/-- `R` has full support. -/
def FullSupport {Ω : Type*} [Fintype Ω] (R : Ω → ℝ) : Prop := ∀ x, 0 < R x

/-- Total variation `d_TV(R, S) = ½ Σ_x |R(x) − S(x)|`. -/
def tv {Ω : Type*} [Fintype Ω] (R S : Ω → ℝ) : ℝ := (1 / 2) * ∑ x, |R x - S x|

/-- The mass `R(S)` of a set. -/
def massOf {Ω : Type*} [Fintype Ω] (R : Ω → ℝ) (S : Set Ω) : ℝ :=
  ∑ x, if x ∈ S then R x else 0

/-- The product law `Q_μ = ⊗_{i} Ber(μ_i)`. -/
def prodLaw {T : ℕ} (μ : Fin T → ℝ) : Cube T → ℝ :=
  fun x => ∏ i, if x i then μ i else 1 - μ i

/-- The two-product mixture `(1 − w) Q_ν + w Q_μ`. -/
def mixLaw {T : ℕ} (w : ℝ) (ν μ : Fin T → ℝ) : Cube T → ℝ :=
  fun x => (1 - w) * prodLaw ν x + w * prodLaw μ x

/-- The uniform product `Q_{(1/2,…,1/2)}`. -/
def uniformLaw (T : ℕ) : Cube T → ℝ := prodLaw (fun _ => (1 / 2 : ℝ))

/-- `μ ∈ [α, 1 − α]^T`. -/
def InBox {T : ℕ} (α : ℝ) (μ : Fin T → ℝ) : Prop := ∀ i, α ≤ μ i ∧ μ i ≤ 1 - α

/-- `u = α(1 − α)`. -/
def uOf (α : ℝ) : ℝ := α * (1 - α)

/-- The balanced product class `P_{α,T} = {Q_μ : μ ∈ [α, 1 − α]^T}`. -/
def PClass (α : ℝ) (T : ℕ) : Set (Cube T → ℝ) :=
  {Q | ∃ μ : Fin T → ℝ, InBox α μ ∧ Q = prodLaw μ}

/-- The balanced two-product class
`M_{2,α,T} = {(1 − w)Q_ν + wQ_μ : w ∈ [0,1], μ, ν ∈ [α, 1 − α]^T}`. -/
def M2Class (α : ℝ) (T : ℕ) : Set (Cube T → ℝ) :=
  {M | ∃ (w : ℝ) (ν μ : Fin T → ℝ), 0 ≤ w ∧ w ≤ 1 ∧ InBox α ν ∧ InBox α μ ∧ M = mixLaw w ν μ}

/-- `OPT_α(P) = min_{Q ∈ P_{α,T}} d_TV(P, Q)` (2.1), as an infimum. -/
def OPT (α : ℝ) {T : ℕ} (P : Cube T → ℝ) : ℝ := sInf ((fun Q => tv P Q) '' PClass α T)

/-- `OPT^(2)_α(P) = min_{M ∈ M_{2,α,T}} d_TV(P, M)` (2.2), as an infimum. -/
def OPT2 (α : ℝ) {T : ℕ} (P : Cube T → ℝ) : ℝ := sInf ((fun M => tv P M) '' M2Class α T)

/-- The prefix mass `R[x_{≤t}]`: the total mass of the points agreeing with `x` on its first `t`
coordinates. `t = 0` gives the total mass; `t ≥ T` gives `R(x)`. -/
def prefMass {T : ℕ} (R : Cube T → ℝ) (x : Cube T) (t : ℕ) : ℝ :=
  ∑ y, if (∀ i : Fin T, i.val < t → y i = x i) then R y else 0

/-- The child-to-parent ratio `R[x_{<i}1] / R[x_{<i}]` at coordinate `i` (paper index `i.val + 1`):
for a law with `R[x_{<i}] > 0` this is the next-bit mean `R(X_i = 1 | x_{<i})`. -/
def condOne {T : ℕ} (R : Cube T → ℝ) (x : Cube T) (i : Fin T) : ℝ :=
  prefMass R (Function.update x i true) (i.val + 1) / prefMass R x i.val

/-- The Euclidean norm `‖v‖₂` of a real vector. -/
def l2 {T : ℕ} (v : Fin T → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- The probability of an event `E` of `n` independent draws from the law `R`. -/
def iidProb {Ω : Type*} [Fintype Ω] (R : Ω → ℝ) (n : ℕ) (E : (Fin n → Ω) → Prop) : ℝ :=
  ∑ xs : Fin n → Ω, if E xs then ∏ k, R (xs k) else 0

end PrefixMixLearn.Proper


