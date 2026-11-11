-- Prove2me | Definitions.Def_ProdMixedTomo_Goodness
-- name    : ProdMixedTomo_Goodness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:46.655318+00:00
-- url     : https://prove2.me/theorems/43202cd3-4539-4b04-8255-0fff3bbd8306
-- title:
--   $(K,\epsilon)$-good sets: Definition 4.11 and Equations (2)–(5)
-- statement:
--   A list $T=(X_1,\dots,X_N)$ of points of $\{0,1\}^n$ is **$(K,\epsilon)$-good** for $\mathrm{Bern}(\mu)$ if for every $\mu'\in[0,1]^n$ with $\mu'_i\ge\mu_i/3$, and every $w\in\Gamma_N$ with $w\le w(T)$ and $\|w\|_1\le\epsilon$:
--   $$
--   \begin{aligned}
--   &\|\mu(T)-\mu\|_\mu\le K\epsilon L(1/\epsilon), &(2)\\
--   &\Bigl\|\mathbb E_{X\sim T}(X-\mu(T))(X-\mu(T))^\top-\mathbb E_{X\sim\mathrm{Bern}(\mu)}(X-\mu)(X-\mu)^\top\Bigr\|_{\mu'}\le K\epsilon L(1/\epsilon)^2, &(3)\\
--   &\Bigl\|\sum_iw_i(X_i-\mu)\Bigr\|_\mu\le K\epsilon L(1/\epsilon), &(4)\\
--   &\Bigl\|\sum_iw_i(X_i-\mu)(X_i-\mu)^\top\Bigr\|_{\mu'}\le K\epsilon L(1/\epsilon)^2, &(5)
--   \end{aligned}
--   $$
--   with $L(t)=\max\{1,\log t\}$. This is the paper's $\epsilon$-goodness with its four $\lesssim$ made explicit by the constant $K$.
--
--   **Formalization Note** (2) and (4) do not involve $\mu'$ and are stated outside the $\mu'$ quantifier, which is the same condition when $\mu\in[0,1]^n$ (then $\mu'=\mu$ is admissible). Each equation is also a separate definition, used by Lemmas 4.15, 4.17, 4.19.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Definition 4.11, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_ProdMixedTomo_Rates
import Definitions.Def_ProdMixedTomo_TestNorms
import Definitions.Def_ProdMixedTomo_Weights

namespace ProdMixedTomo

/-!
# `(K, ϵ)`-good sets (Definition 4.11, Equations (2)–(5))

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Definition 4.11, p.26
(PDF p.28): a set `T` of points is `ϵ`-good with respect to a binary product distribution `π` with
mean `μ` if for all `μ' ∈ [0,1]ⁿ` with `μ'ᵢ ≥ μᵢ/3`:
(2) `‖μ(T) − μ‖_μ ≲ ϵ log 1/ϵ`;
(3) `‖E_{X∼T}(X − μ(T))(X − μ(T))ᵀ − E_{X∼π}(X − μ)(X − μ)ᵀ‖_{μ'} ≲ ϵ log²(1/ϵ)`;
and for all `w ≤ w(T)` with `‖w‖₁ ≤ ϵ`:
(4) `‖Σᵢ wᵢ(Xᵢ − μ)‖_μ ≲ ϵ log 1/ϵ`;
(5) `‖Σ_{i∈T} wᵢ(Xᵢ − μ)(Xᵢ − μ)ᵀ‖_{μ'} ≲ ϵ log²(1/ϵ)`.

**Formalization Note.** The four `≲` inside the definition are replaced by one explicit constant
`K` ("`(K, ϵ)`-good"); the lemmas quantify over `K` as their statements require. `log(1/ϵ)` is
`max{1, log(1/ϵ)}` (p.13). The weights `w` in (4)–(5) range over `Γ_N` (nonnegative, as in §4.1).
Equations (2) and (4) do not involve `μ'`, so they are stated outside the `μ'` quantifier; for
`μ ∈ [0,1]ⁿ` (the only case used) the set of `μ'` is nonempty (it contains `μ`), so this is the
same condition.
-/

/-- The `μ'` of Definition 4.11: `μ' ∈ [0,1]ⁿ` with `μ'ᵢ ≥ μᵢ/3`. -/
def MuPrime {n : ℕ} (μ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {μ' | ∀ i, 0 ≤ μ' i ∧ μ' i ≤ 1 ∧ μ i / 3 ≤ μ' i}

/-- The weights of (4)–(5): `w ∈ Γ_N`, `w ≤ w(T)`, `‖w‖₁ ≤ ϵ`. -/
noncomputable def SmallW (N : ℕ) (ϵ : ℝ) : Set (Fin N → ℝ) :=
  {w | w ∈ Gamma N ∧ (∀ i, w i ≤ wAll N i) ∧ ∑ i, w i ≤ ϵ}

/-- Equation (2) with constant `K`. -/
def Eq2 {n N : ℕ} (K ϵ : ℝ) (μ : Fin n → ℝ) (X : Fin N → Fin n → ℝ) : Prop :=
  vnorm μ (empMean X - μ) ≤ K * ϵ * logPlus (1 / ϵ)

/-- Equation (3) with constant `K`, for every `μ'`. -/
def Eq3 {n N : ℕ} (K ϵ : ℝ) (μ : Fin n → ℝ) (X : Fin N → Fin n → ℝ) : Prop :=
  ∀ μ' ∈ MuPrime μ, mnorm μ' (empCov X - popCov μ) ≤ K * ϵ * logPlus (1 / ϵ) ^ 2

/-- Equation (4) with constant `K`. -/
def Eq4 {n N : ℕ} (K ϵ : ℝ) (μ : Fin n → ℝ) (X : Fin N → Fin n → ℝ) : Prop :=
  ∀ w ∈ SmallW N ϵ, vnorm μ (∑ i, w i • (X i - μ)) ≤ K * ϵ * logPlus (1 / ϵ)

/-- Equation (5) with constant `K`, for every `μ'`. -/
def Eq5 {n N : ℕ} (K ϵ : ℝ) (μ : Fin n → ℝ) (X : Fin N → Fin n → ℝ) : Prop :=
  ∀ μ' ∈ MuPrime μ, ∀ w ∈ SmallW N ϵ,
    mnorm μ' (∑ i, w i • Matrix.vecMulVec (X i - μ) (X i - μ)) ≤ K * ϵ * logPlus (1 / ϵ) ^ 2

/-- `X` is a `(K, ϵ)`-good set of points for `Bern(μ)` (Definition 4.11). -/
def IsGood {n N : ℕ} (K ϵ : ℝ) (μ : Fin n → ℝ) (X : Fin N → Fin n → ℝ) : Prop :=
  Eq2 K ϵ μ X ∧ Eq3 K ϵ μ X ∧ Eq4 K ϵ μ X ∧ Eq5 K ϵ μ X

end ProdMixedTomo


