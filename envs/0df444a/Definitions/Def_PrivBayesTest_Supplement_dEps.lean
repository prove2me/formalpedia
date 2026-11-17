-- Prove2me | Definitions.Def_PrivBayesTest_Supplement_dEps
-- name    : PrivBayesTest_Supplement_dEps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:10:58.14841+00:00
-- url     : https://prove2.me/theorems/c7799368-5d33-43cf-afb0-7fe0afcfc9df
-- title:
--   The divergence $I_\theta$, community profiles $\theta_i$, and the private Chernoff–Hellinger quantities $c_\varepsilon$, $d_\varepsilon$, $C_\varepsilon$, $D_\varepsilon$
-- statement:
--   For a scalar $\theta>0$ and $x\ge0$ let $I_\theta(x)=x\log(x/\theta)-x+\theta$ (with $0\log0=0$), and let $I_0(0)=0$ and $I_0(x)=+\infty$ for $x>0$. For nonnegative vectors $\theta,r\in\mathbb R_+^k$ let
--
--   $$I_\theta(r)=\sum_{\ell=1}^k I_{\theta_\ell}(r_\ell)\in[0,+\infty],$$
--
--   which generalizes the Kullback–Leibler divergence to nonnegative measures on $[k]$. For a prior $p$ and a connection matrix $Q$, the **community profile** $\theta_i$ is the $i$-th column of $\mathrm{diag}(p)Q$, that is $\theta_{i,\ell}=p_\ell Q_{\ell i}$. With $\tilde\alpha=\min(\alpha,1-\alpha)$ and $\|r-s\|_1=\sum_\ell|r_\ell-s_\ell|$,
--
--   $$c_\varepsilon(i,j)=\sup_{\alpha\in(0,1)}\inf_{r,s\ge0}\big\{\alpha I_{\theta_i}(r)+(1-\alpha)I_{\theta_j}(s)+\tilde\alpha\varepsilon\|r-s\|_1\big\},$$
--
--   $$d_\varepsilon(i\to j)=\sup_{\alpha\in(0,1)}\inf_{r,s\ge0}\big\{\alpha I_{\theta_i}(r)+(1-\alpha)I_{\theta_j}(s)+\alpha\varepsilon\|r-s\|_1\big\},$$
--
--   and $C_\varepsilon=\min_{i\ne j}c_\varepsilon(i,j)$, $D_\varepsilon=\min_{i\ne j}d_\varepsilon(i\to j)$, the minima over ordered pairs of distinct communities. The infima range over all nonnegative vectors $r,s\in\mathbb R_+^k$, not only probability vectors; $d_\varepsilon$ is not symmetric in $i,j$.
--
--   These quantities are the conjectured threshold ($C_\varepsilon$) and the proved threshold ($D_\varepsilon$) for private exact recovery in Theorems 1.7 and 4.8.
--
--   **Formalization Note** All values are in $[0,+\infty]$ (`ℝ≥0∞`). The norm is $\ell_1$, not total variation (footnote 1, p.7). The minima over the finitely many ordered pairs are written as infima.
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), θ_i, I_θ, c_ε, C_ε, d_ε, D_ε, §1.3.2, p.7; d_ε, D_ε, §4.1, p.16; scalar I_θ and its convention at θ = 0, §4.2.3, p.20

import Mathlib

open scoped ENNReal

namespace PrivBayesTest

namespace Supplement

/-- The scalar divergence `I_θ(x)` (Jacobsen, *Optimal Error Exponents for Private Bayesian
Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), §4.2.3, p.20,
PDF p.20): for `θ > 0`, `I_θ(x) = x log(x/θ) − x + θ` (with `0 log 0 = 0`, so `I_θ(0) = θ`), and
`I_0(x) = +∞` for `x > 0`, `I_0(0) = 0`.

**Formalization Note** Values in `[0, +∞]` (`ℝ≥0∞`). For `θ > 0` and `x ≥ 0` the real number
`x log(x/θ) − x + θ` is nonnegative, so `ENNReal.ofReal` loses nothing; Lean's `Real.log 0 = 0`
gives exactly the convention `0 log 0 = 0`. Only `x ≥ 0` and `θ ≥ 0` occur; `θ ≤ 0` is treated as
the case `θ = 0`. -/
noncomputable def poisDiv (θ x : ℝ) : ℝ≥0∞ :=
  if 0 < θ then ENNReal.ofReal (x * Real.log (x / θ) - x + θ)
  else if x = 0 then 0 else ⊤

/-- The divergence `I_θ(r) = ∑_ℓ (r_ℓ log(r_ℓ/θ_ℓ) − r_ℓ + θ_ℓ)` between nonnegative measures on
`[k]` (Jacobsen, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.7, and its
coordinatewise form `I_θ(x) = ∑_ℓ I_{θ_ℓ}(x_ℓ)`, p.20), valued in `[0, +∞]`. -/
noncomputable def measDiv {k : ℕ} (θ r : Fin k → ℝ) : ℝ≥0∞ :=
  ∑ ℓ, poisDiv (θ ℓ) (r ℓ)

/-- The **community profile** `θ_i` (Jacobsen, STOC 2027 submission (manuscript sha256
abff2fdd…124ef), p.7): the `i`-th column of `diag(p) Q`, i.e. `θ_{i,ℓ} = p_ℓ Q_{ℓ,i}`. -/
def profile {k : ℕ} (p : Fin k → ℝ) (Q : Matrix (Fin k) (Fin k) ℝ) (i : Fin k) : Fin k → ℝ :=
  fun ℓ => p ℓ * Q ℓ i

/-- The common shape of `c_ε` and `d_ε` (Jacobsen, STOC 2027 submission (manuscript sha256
abff2fdd…124ef), p.7): for a weight `w : (0,1) → ℝ` on the ℓ₁ term,

`sup_{α ∈ (0,1)} inf_{r, s ∈ ℝ₊ᵏ} { α I_θ(r) + (1 − α) I_θ'(s) + w(α) ε ‖r − s‖₁ }`.

**Formalization Note** `‖r − s‖₁ = ∑_ℓ |r_ℓ − s_ℓ|` is the ℓ₁ norm (not total variation, which
is half of it; footnote 1, p.7). `r, s` range over all nonnegative vectors, not only probability
vectors. Values in `[0, +∞]`; `ENNReal.ofReal α * ⊤ = ⊤` for `α > 0`. The infimum is over a
nonempty set (`r = s = 0`) and the supremum over the nonempty interval `(0, 1)`. -/
noncomputable def privCH {k : ℕ} (w : ℝ → ℝ) (θ θ' : Fin k → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ⨆ α ∈ Set.Ioo (0 : ℝ) 1, ⨅ (r : Fin k → ℝ) (_ : 0 ≤ r) (s : Fin k → ℝ) (_ : 0 ≤ s),
    ENNReal.ofReal α * measDiv θ r + ENNReal.ofReal (1 - α) * measDiv θ' s +
      ENNReal.ofReal (w α * ε * ∑ ℓ, |r ℓ - s ℓ|)

/-- The **private Chernoff–Hellinger divergence** `c_ε(i, j)` (Jacobsen, STOC 2027 submission
(manuscript sha256 abff2fdd…124ef), p.7 and p.20):

`c_ε(i, j) = sup_{α ∈ (0,1)} inf_{r, s ≥ 0} { α I_{θ_i}(r) + (1 − α) I_{θ_j}(s) + α̃ ε ‖r − s‖₁ }`
with `α̃ = min(α, 1 − α)`. -/
noncomputable def cEps {k : ℕ} (p : Fin k → ℝ) (Q : Matrix (Fin k) (Fin k) ℝ) (ε : ℝ)
    (i j : Fin k) : ℝ≥0∞ :=
  privCH (fun α => min α (1 - α)) (profile p Q i) (profile p Q j) ε

/-- `d_ε(i → j)` (Jacobsen, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.7, p.16
and p.20): `c_ε(i, j)` with `α` in place of `α̃`,

`d_ε(i → j) = sup_{α ∈ (0,1)} inf_{r, s ≥ 0} { α I_{θ_i}(r) + (1 − α) I_{θ_j}(s) + α ε ‖r − s‖₁ }`.
It is not symmetric in `i, j`. -/
noncomputable def dEps {k : ℕ} (p : Fin k → ℝ) (Q : Matrix (Fin k) (Fin k) ℝ) (ε : ℝ)
    (i j : Fin k) : ℝ≥0∞ :=
  privCH (fun α => α) (profile p Q i) (profile p Q j) ε

/-- `C_ε = min_{i ≠ j} c_ε(i, j)` (Jacobsen, STOC 2027 submission (manuscript sha256
abff2fdd…124ef), p.7, p.20).

**Formalization Note** The minimum over the finitely many ordered pairs `i ≠ j` is written as an
infimum; for `k ≥ 2` it is attained. -/
noncomputable def CEps {k : ℕ} (p : Fin k → ℝ) (Q : Matrix (Fin k) (Fin k) ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (i : Fin k) (j : Fin k) (_ : i ≠ j), cEps p Q ε i j

/-- `D_ε = min_{i ≠ j} d_ε(i → j)`, the minimum over ordered pairs (Jacobsen, STOC 2027 submission
(manuscript sha256 abff2fdd…124ef), p.7, p.16, p.20).

**Formalization Note** As for `CEps`, an infimum over the finitely many ordered pairs `i ≠ j`. -/
noncomputable def DEps {k : ℕ} (p : Fin k → ℝ) (Q : Matrix (Fin k) (Fin k) ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (i : Fin k) (j : Fin k) (_ : i ≠ j), dEps p Q ε i j

end Supplement

end PrivBayesTest


