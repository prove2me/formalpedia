-- Prove2me | Definitions.Def_InfoShareH2_Model
-- name    : InfoShareH2_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:06.839031+00:00
-- url     : https://prove2.me/theorems/7eed85d8-8068-4df5-a6e3-b389a38df0ae
-- title:
--   Policies $\tilde\Psi$, inventory variance $\sigma_I^2$, forecast errors $\sigma^2_{S|FI},\sigma^2_{S|NS}$, Assumption 2 and the frontiers $\Sigma^2_{FI},\Sigma^2_{NS}$
-- statement:
--   This module fixes the optimization problems (25) and (26) of the paper.
--
--   A retailer facing i.i.d. demand $D_t=d+\epsilon_t$ with $\operatorname{Var}\epsilon_t=\sigma_\epsilon^2$ places orders $O_t=d+\sum_{n\ge0}\tilde\psi_n\epsilon_{t-n}$. The **ordering policy** is the real sequence $\tilde\psi=(\tilde\psi_n)_{n\ge0}$, and the admissible policies form the set (6)
--
--   $$\tilde\Psi=\Bigl\{\tilde\psi:\ \sum_{n\ge0}\tilde\psi_n=1,\ \sum_{n\ge0}\tilde\psi_n^2<\infty,\ \sum_{n\ge1}\Bigl(\sum_{k=0}^{n-1}\tilde\psi_k-1\Bigr)^2<\infty\Bigr\}.$$
--
--   The **z-transform** is $\tilde\psi(z)=\sum_n\tilde\psi_nz^n$ for $|z|<1$, and its **boundary value** $\tilde\psi(e^{-i\lambda})$ is the radial limit $\lim_{r\uparrow1}\tilde\psi(re^{-i\lambda})$, which exists for almost every $\lambda$.
--
--   1. The retailer's **inventory variance** (8) is $\sigma_I^2(\tilde\psi)=\sigma_\epsilon^2\bigl(1+\sum_{n\ge1}(\sum_{k<n}\tilde\psi_k-1)^2\bigr)$.
--   2. The supplier's one-step **forecast error under full sharing** (25) is $\sigma^2_{S|FI}(\tilde\psi)=\sigma_\epsilon^2\tilde\psi_0^2$.
--   3. The **forecast error under no sharing** (26) is Kolmogorov's expression
--   $$\sigma^2_{S|NS}(\tilde\psi)=\sigma_\epsilon^2\exp\Bigl(\frac1{2\pi}\int_{-\pi}^{\pi}\log\bigl(\tilde\psi(e^{-i\lambda})\tilde\psi(e^{i\lambda})\bigr)\,d\lambda\Bigr).$$
--   4. The function $\Theta(z)=\frac1{2\pi}\int_{-\pi}^{\pi}\frac{e^{i\lambda}+z}{e^{i\lambda}-z}\log|\tilde\psi(e^{-i\lambda})|\,d\lambda$ on the unit disk has Taylor coefficients $\theta_n$; **Assumption 2** is $(\theta_n)_{n\ge0}\in\ell^2$.
--   5. The **frontiers** are
--   $$\Sigma^2_{FI}(\sigma)=\inf\{\sigma_I^2(\tilde\psi):\tilde\psi\in\tilde\Psi,\ \sigma^2_{S|FI}(\tilde\psi)\le\sigma^2\},$$
--   $$\Sigma^2_{NS}(\sigma)=\inf\{\sigma_I^2(\tilde\psi):\tilde\psi\in\tilde\Psi \text{ satisfying Assumption 2},\ \sigma^2_{S|NS}(\tilde\psi)\le\sigma^2\}.$$
--
--   These objects carry the whole goal of the mission (Theorem 2) and its full-sharing counterpart (Theorem 1).
--
--   **Formalization Note** Coefficients are real. "$\sum\tilde\psi_n=1$" is convergence of the partial sums, not absolute summability. The series in (8) is reindexed from $n\ge1$ to $n\ge0$. For real coefficients $\tilde\psi(e^{i\lambda})$ is the conjugate of $\tilde\psi(e^{-i\lambda})$, so the integrand of (26) is written $\log|\tilde\psi(e^{-i\lambda})|^2$. The Taylor coefficients are $\Theta^{(n)}(0)/n!$. The infima are real `sInf`s of the sets of attained values; for $\sigma_\epsilon>0$ these sets are bounded below by $\sigma_\epsilon^2$.
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, (6) p.10, (8) p.11, (25) p.19, (26)–(27) p.20, p.22 (radial limits), p.27 (Θ, Assumption 2)

import Mathlib

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **z-transform of a coefficient sequence** (27), p.20 and p.22.
Caldentey–Giloni–Hurvich–Zhang, *Information Design and Sharing in Supply Chains*,
SSRN 4319721 (v. 2024-01-20), (27), p.20: `ψ̃(z) = ∑_{n ≥ 0} ψ̃_n zⁿ`, `z ∈ D`.

**Formalization Note** The series is a Lean `tsum`; it is used only for `‖z‖ < 1` and
square-summable coefficients, where it converges absolutely. -/
noncomputable def zTransform (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n, a n * z ^ n

/-- **Radial limit at `e^{−iλ}`** (p.22). SSRN 4319721 (v. 2024-01-20), §5, p.22: "for each
`z = e^{−iλ}` on `T`, the function value of `ψ̃(z)` is defined by its radial limit `ψ̃(rz)` where
`r ∈ ℝ` and `r ↑ 1`".

`radialLim f λ` is `lim_{r ↑ 1} f(r e^{−iλ})`.

**Formalization Note** It is written with `limUnder` along `𝓝[<] 1`. Where the limit does not
exist, `limUnder` returns an unspecified value. For a function in `H²` that happens only on a
Lebesgue-null set of `λ` (p.22), so no integral over `λ` depends on it. -/
noncomputable def radialLim (f : ℂ → ℂ) (lam : ℝ) : ℂ :=
  limUnder (𝓝[<] (1 : ℝ)) (fun r : ℝ => f ((r : ℂ) * exp (-(lam : ℂ) * I)))

/-- **Boundary value `ψ̃(e^{−iλ})` of a coefficient sequence** (p.22): the radial limit of its
z-transform at `e^{−iλ}`. -/
noncomputable def boundary (a : ℕ → ℂ) (lam : ℝ) : ℂ :=
  radialLim (zTransform a) lam

/-- **Real coefficients as complex coefficients.** The orders are real (Assumption 1(b), §9.3),
so a policy is `ψ : ℕ → ℝ`; `ofRealSeq ψ` is the same sequence in `ℂ`. -/
def ofRealSeq (ψ : ℕ → ℝ) : ℕ → ℂ := fun n => (ψ n : ℂ)

/-- **Partial sums** `∑_{n < N} ψ_n`. -/
def partialSum (ψ : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, ψ n

/-- **The admissible policies `Ψ̃`** (6), Assumption 1(b), p.10:
`Ψ̃ = {ψ̃ : ∑_{n≥0} ψ̃_n = 1, ∑_{n≥0} ψ̃_n² < ∞, ∑_{n≥1} (∑_{k=0}^{n−1} ψ̃_k − 1)² < ∞}`.

**Formalization Note** Coefficients are real (the orders are real random variables).
"`∑ ψ̃_n = 1`" is the convergence of the partial sums to `1`, not `HasSum` (which in `ℝ` would
force absolute summability; `ψ̃` is only square summable). The third series is reindexed:
term `n ≥ 1` of the source is term `n − 1 ≥ 0` here, `(partialSum ψ (n+1) − 1)²`. -/
def PsiTilde : Set (ℕ → ℝ) :=
  {ψ | Tendsto (partialSum ψ) atTop (𝓝 1) ∧ Summable (fun n => ψ n ^ 2) ∧
    Summable (fun n => (partialSum ψ (n + 1) - 1) ^ 2)}

/-- **Retailer's inventory variance** (8), p.11:
`σ²_I(ψ̃) = σ_ε² (1 + ∑_{n≥1} (∑_{k=0}^{n−1} ψ̃_k − 1)²)`.

**Formalization Note** A real `tsum`, reindexed from `n ≥ 1` to `n ≥ 0`. On `Ψ̃` the series is
summable (third condition of (6)), so the `tsum` is the true sum there. -/
noncomputable def invVar (σε : ℝ) (ψ : ℕ → ℝ) : ℝ :=
  σε ^ 2 * (1 + ∑' n, (partialSum ψ (n + 1) - 1) ^ 2)

/-- **Supplier's MSFE under full information sharing** (25), p.19: `σ²_S|FI(ψ̃) = σ_ε² ψ̃_0²`. -/
def fsVar (σε : ℝ) (ψ : ℕ → ℝ) : ℝ := σε ^ 2 * ψ 0 ^ 2

/-- **Supplier's MSFE under no information sharing** (26), p.20 (Kolmogorov's expression):
`σ²_S|NS(ψ̃) = σ_ε² exp((1/2π) ∫_{−π}^{π} log(ψ̃(e^{−iλ}) ψ̃(e^{iλ})) dλ)`.

**Formalization Note** For real coefficients `ψ̃(e^{iλ})` is the complex conjugate of
`ψ̃(e^{−iλ})`, so the integrand is `log ‖ψ̃(e^{−iλ})‖²`, written with the radial-limit boundary
function `boundary`. `Real.log 0 = 0` and the value `0` of a non-integrable integral do not fire on
`Ψ̃`: every `ψ̃ ∈ Ψ̃` is a nonzero element of `H²`, for which `log |ψ̃|` is integrable on the
circle (Lemma 2). -/
noncomputable def nsVar (σε : ℝ) (ψ : ℕ → ℝ) : ℝ :=
  σε ^ 2 * Real.exp ((1 / (2 * Real.pi)) *
    ∫ lam in (-Real.pi)..Real.pi, Real.log (‖boundary (ofRealSeq ψ) lam‖ ^ 2))

/-- **The exponent `Θ` of the outer factor** (p.27):
`Θ(z) = (1/2π) ∫_{−π}^{π} (e^{iλ} + z)/(e^{iλ} − z) log |ψ̃(e^{−iλ})| dλ`, `z ∈ D`.

**Formalization Note** Printed orientation (`log|ψ̃(e^{−iλ})|` against the kernel in `e^{iλ}`);
for real coefficients it coincides with the orientation of (29). Used only for `‖z‖ < 1`. -/
noncomputable def Theta (ψ : ℕ → ℝ) (z : ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ lam in (-Real.pi)..Real.pi,
    (exp ((lam : ℂ) * I) + z) / (exp ((lam : ℂ) * I) - z) *
      (Real.log ‖boundary (ofRealSeq ψ) lam‖ : ℂ)

/-- **Taylor coefficient at `0`**: `f^{(n)}(0) / n!`. -/
noncomputable def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- **`θ_n`, the Taylor coefficients of `Θ`** (p.27: "`Θ(z) = ∑_{k≥0} θ_k z^k` for `z ∈ D`"). -/
noncomputable def thetaCoeff (ψ : ℕ → ℝ) (n : ℕ) : ℂ :=
  taylorCoeff (Theta ψ) n

/-- **Assumption 2** (p.27): "The coefficients in the Taylor expansion of `Θ(z)` satisfy
`{θ_n}_{n≥0} ∈ ℓ²`". -/
def Assumption2 (ψ : ℕ → ℝ) : Prop :=
  Summable (fun n => ‖thetaCoeff ψ n‖ ^ 2)

/-- **Full-information frontier** (25), p.19:
`Σ²_FI(σ) := inf_{ψ̃ ∈ Ψ̃} σ²_I(ψ̃)` subject to `σ_ε² ψ̃_0² ≤ σ²`.

**Formalization Note** A real `sInf` of the set of attained values. For `σ_ε > 0` the set is
nonempty (`ψ̃ = (1, 0, 0, …)` is feasible for `σ ≥ σ_ε`, and `(σ/σ_ε, 1 − σ/σ_ε, 0, …)` for
`0 ≤ σ ≤ σ_ε`) and bounded below by `σ_ε²`. -/
noncomputable def SigmaFIsq (σε σ : ℝ) : ℝ :=
  sInf {v | ∃ ψ ∈ PsiTilde, fsVar σε ψ ≤ σ ^ 2 ∧ v = invVar σε ψ}

/-- **No-sharing frontier** (26), p.20:
`Σ²_NS(σ) := inf_{ψ̃ ∈ Ψ̃} σ²_I(ψ̃)` subject to `σ²_S|NS(ψ̃) ≤ σ²`, with the infimum over the
policies satisfying Assumption 2 (p.28: "we solve the optimization problem (26) … with respect to
all functions in `H²` that satisfy Assumption 2").

**Formalization Note** A real `sInf`: the infimum is not attained for `σ < σ_ε/2` (p.21). For
`σ_ε > 0` and `σ > 0` the set is nonempty and bounded below by `σ_ε²`. -/
noncomputable def SigmaNSsq (σε σ : ℝ) : ℝ :=
  sInf {v | ∃ ψ ∈ PsiTilde, Assumption2 ψ ∧ nsVar σε ψ ≤ σ ^ 2 ∧ v = invVar σε ψ}

end InfoShareH2


