-- Prove2me | Definitions.Def_GoodProphets_lpObj
-- name    : GoodProphets_lpObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:29.736333+00:00
-- url     : https://prove2.me/theorems/8907d164-5626-4fc1-bdcf-548bb3a21046
-- title:
--   The objective $f_{\vec N}(\vec x)$, its domain, $\arg\min_{\vec x\ge\vec y}f_{\vec N}$, $\mathrm{OPT}(\vec N)$ and boundedness
-- statement:
--   Fix an instance. For $\vec N\in\mathbb R^k$ and a type-action array $\vec x$, the **objective** is
--   $$
--   f_{\vec N}(\vec x)=\inf\Big\{\vec c_1\cdot\vec x+\vec c_2\cdot\vec z\ :\ \vec z\ge0,\ A\vec x-D\vec z\le\vec B\sum_\theta N_\theta\Big\},
--   $$
--   evaluated on the **domain** $\{\vec x:\sum_jx_{\theta j}=N_\theta\ \forall\theta\}$. The module also defines:
--
--   1. the feasible set $\{\vec x\ge\vec y:\sum_jx_{\theta j}=N_\theta\}$ of $\min_{\vec x\ge\vec y}f_{\vec N}(\vec x)$;
--   2. $\vec x\in\arg\min_{\vec x\ge\vec y}f_{\vec N}$, meaning that $\vec x$ is feasible and no feasible point has a smaller objective;
--   3. the optimal value $\min_{\vec x\ge\vec y}f_{\vec N}(\vec x)$, which is the problem $\mathrm{OPT}^t$ when $\vec y=\vec x^{\mathrm{ALG}}(t-1)$;
--   4. the clairvoyant optimum $\mathrm{OPT}(\vec N)=\min_{\vec x\ge0}f_{\vec N}(\vec x)$;
--   5. **boundedness** of the instance: for every $\vec N\ge0$ and every $\vec x$ in the domain, the inner minimization over $\vec z$ is bounded below, so $f_{\vec N}(\vec x)$ is a real number.
--
--   These are the optimization problems that every statement of the mission refers to: $\mathrm{OPT}^t$, $\mathrm{DLP}$, $\mathrm{EDLP}(t)$, $\mathrm{TDLP}(t)$ and the benchmark $\mathrm{OPT}(\vec N)$.
--
--   **Formalization Note** The minimum is Mathlib's real infimum `sInf`. It equals the paper's minimum when the instance is bounded, and the inner program is always feasible because $D$ has a positive entry in every row. $\mathrm{OPT}(\vec N)$ is taken over real (fractional) $\vec x\ge0$, the paper's convention (p.10: $L=\mathbb E[\mathrm{OPT}^T-\mathrm{OPT}^1]$ "since $\vec x^{\mathrm{ALG}}(0)=\vec 0$").
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), §2, pp.7–8 (objective, Performance Benchmark), §3, p.10 (OPTᵗ, DLP)

import Mathlib
import Definitions.Def_GoodProphets_Instance

namespace GoodProphets

/-- The feasible values `c⃗₁·x + c⃗₂·z` of the inner minimization over `z` in the objective
`f_N(x)` of Banerjee & Freund, *Good prophets know when the end is near*, Management Science
(2024), doi:10.1287/mnsc.2023.04307 (author manuscript), §2, p.7: all `z ≥ 0` with
`A x − D z ≤ B⃗ ∑_θ N_θ`. -/
def innerValues {k ℓ r m : ℕ} (I : Instance k ℓ r m) (N : Fin k → ℝ)
    (x : Fin k → Fin ℓ → ℝ) : Set ℝ :=
  {v | ∃ z : Fin m → ℝ, (∀ q, 0 ≤ z q) ∧
      (∀ i, ∑ θ, ∑ j, I.A i θ j * x θ j - ∑ q, I.D i q * z q ≤ I.B i * ∑ θ, N θ) ∧
      v = ∑ θ, ∑ j, I.c1 θ j * x θ j + ∑ q, I.c2 q * z q}

/-- The objective `f_N(x) = min_z {c⃗₁·x + c⃗₂·z : z ≥ 0, A x − D z ≤ B⃗ ∑_θ N_θ}`
(doi:10.1287/mnsc.2023.04307, author manuscript, §2, p.7, "Objective Function").

**Formalization Note** The minimum is the real infimum `sInf` of `innerValues`. It is the paper's
minimum when the inner linear program is bounded below (`Bounded`); the inner program is always
feasible because `D ≥ 0` has a positive entry in every row. The constraint `∑ⱼ x_θj = N_θ` of the
paper's display is kept separately as the domain `Dom N`: `f_N(x)` is only ever evaluated on it. -/
noncomputable def lpObj {k ℓ r m : ℕ} (I : Instance k ℓ r m) (N : Fin k → ℝ)
    (x : Fin k → Fin ℓ → ℝ) : ℝ :=
  sInf (innerValues I N x)

/-- The domain `{x : ∑ⱼ x_θj = N_θ ∀θ}` of `f_N` (doi:10.1287/mnsc.2023.04307, p.7; Proposition 1
(i), p.8). -/
def Dom {k ℓ : ℕ} (N : Fin k → ℝ) : Set (Fin k → Fin ℓ → ℝ) :=
  {x | ∀ θ, ∑ j, x θ j = N θ}

/-- The feasible set `{x ≥ y : ∑ⱼ x_θj = N_θ}` of `min_{x ≥ y} f_N(x)` (doi:10.1287/mnsc.2023.04307,
Proposition 1 (ii), p.8; (OPTᵗ), p.10). -/
def Feas {k ℓ : ℕ} (N : Fin k → ℝ) (y : Fin k → Fin ℓ → ℝ) : Set (Fin k → Fin ℓ → ℝ) :=
  {x | (∀ θ j, y θ j ≤ x θ j) ∧ x ∈ Dom N}

/-- `x ∈ arg min_{x ≥ y} f_N(x)` (doi:10.1287/mnsc.2023.04307, Proposition 1 (ii), p.8). -/
def IsOptIn {k ℓ r m : ℕ} (I : Instance k ℓ r m) (N : Fin k → ℝ) (y x : Fin k → Fin ℓ → ℝ) :
    Prop :=
  x ∈ Feas N y ∧ ∀ x' ∈ Feas N y, lpObj I N x ≤ lpObj I N x'

/-- The optimal value `min_{x ≥ y} f_N(x)` of the problem (OPTᵗ) with `y = x^ALG(t−1)`
(doi:10.1287/mnsc.2023.04307, p.10). -/
noncomputable def optVal {k ℓ r m : ℕ} (I : Instance k ℓ r m) (N : Fin k → ℝ)
    (y : Fin k → Fin ℓ → ℝ) : ℝ :=
  sInf (lpObj I N '' Feas N y)

/-- The clairvoyant optimum `OPT(N) = min_x f_N(x)` (doi:10.1287/mnsc.2023.04307, §2, p.8,
"Performance Benchmark").

**Formalization Note** The minimum is over real (fractional) `x ≥ 0` with `∑ⱼ x_θj = N_θ`, the
paper's convention (p.10: `L = E[OPTᵀ − OPT¹]` "since `x^ALG(0) = 0`", and `OPT¹` has the
constraint `x ≥ x^ALG(0)`). -/
noncomputable def OPT {k ℓ r m : ℕ} (I : Instance k ℓ r m) (N : Fin k → ℝ) : ℝ :=
  optVal I N 0

/-- The inner linear program of `f_N(x)` is bounded below for every `N ≥ 0` and every `x` with
`∑ⱼ x_θj = N_θ`, so that `f_N(x)` is a real number, as the paper treats it throughout
(doi:10.1287/mnsc.2023.04307, §2, pp.7–8). -/
def Instance.Bounded {k ℓ r m : ℕ} (I : Instance k ℓ r m) : Prop :=
  ∀ N : Fin k → ℝ, (∀ θ, 0 ≤ N θ) → ∀ x ∈ (Dom N : Set (Fin k → Fin ℓ → ℝ)),
    BddBelow (innerValues I N x)

end GoodProphets


