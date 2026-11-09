-- Prove2me | Definitions.Def_LinearChoresCLS_Remainders
-- name    : LinearChoresCLS_Remainders
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:56:50.401245+00:00
-- url     : https://prove2.me/theorems/8e765760-89f5-4223-b08b-a771f5995971
-- title:
--   The chain quantities $\Delta_{(j,j'),k}$, $P_{(j,j')}$ and the remainders $R_{(j,j')}$, $R_{\mathrm{lin}}$, $R_{\mathrm{norm}}$
-- statement:
--   For a chain $(j,j')$: $\Delta_{(j,j'),0}=\log(p_j(x)/p_{j'}(x))$ and $\Delta_{(j,j'),k+1}=\log(p^+_{(j,j'),k}/p^-_{(j,j'),k})$; the absolute-value terms are $P_{(j,j')}=-\frac12\sum_{k<L}B_{(j,j'),k}|\Delta_{(j,j'),k}|$. With $s_k=2\log q_k$ and $w=w_{jj'}$, the chain remainder is $R_{(j,j')}=\tilde R_{(j,j')}+\hat R_{(j,j')}$,
--   $$
--   \tilde R_{(j,j')}=-\frac w2\Delta_{(j,j'),L}^2+\frac w2\sum_{k<L}s_k^2+\sum_{k<L}\Big(\frac{B_{(j,j'),k}}2-ws_k\Big)|\Delta_{(j,j'),k}|,\qquad \hat R_{(j,j')}=\frac w2\big(\Delta_{(j,j'),0}^2-t^2(x_j-x_{j'})^2\big).
--   $$
--   The linear and normalization remainders are
--   $$
--   R_{\mathrm{lin}}(x)=\sum_{j=1}^n\frac\alpha t c_j\big(\log(1+tx_j)-tx_j\big),\qquad R_{\mathrm{norm}}(x)=(n+1)\log\frac{T(x)}{n+1}.
--   $$
--
--   These remainders appear in Theorems 6.9, 6.10 and 6.12 and add up to the total remainder of Lemma 7.6.
--
--   **Formalization Note** All remainders are the paper's explicit formulas, so the identities (6.11), (6.16) and $\Psi(\tilde p)=\Psi(p)+R_{\mathrm{norm}}$ are genuine claims rather than definitions.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), pp.17, 23–24, 27, 29, 47

import Mathlib
import Definitions.Def_LinearChoresCLS_PriceFamily

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

variable {n : ℕ}

/-- The chain quantities `Δ_{(j,j′),k}(x)` (arXiv:2611.06589, held version sha256 85d34a9e…,
§6.1, p.17, and §6.3, p.21): `Δ_{(j,j′),0} := log(p_j(x)/p_{j′}(x))` and
`Δ_{(j,j′),k+1} := log(p^+_{(j,j′),k}/p^−_{(j,j′),k})`, the log ratio of the outputs of layer `k`. -/
noncomputable def chainDelta (t : ℝ) (π : Pair n) (x : Fin n → ℝ) : ℕ → ℝ
  | 0 => Real.log (basicPrice t x π.1.1 / basicPrice t x π.1.2)
  | k + 1 =>
    let o := layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k
    Real.log (o.1 / o.2)

/-- The absolute-value terms of chain `(j, j′)`:
`P_{(j,j′)} := −½ ∑_{k=0}^{L−1} B_{(j,j′),k} |Δ_{(j,j′),k}|` (arXiv:2611.06589, (6.10), p.23). -/
noncomputable def chainAbs (P : Quadratic n) (t : ℝ) (L : ℕ) (π : Pair n) (x : Fin n → ℝ) : ℝ :=
  -(1 / 2) * ∑ k ∈ range L, gadgetEarn P t π k * |chainDelta t π x k|

/-- The chain remainder `R_{(j,j′)} := R̃_{(j,j′)} + R̂_{(j,j′)}` (arXiv:2611.06589, p.24), with
`s_k = 2 log q_k` (6.9),
`R̃_{(j,j′)} := −(w/2) Δ_L² + (w/2) ∑_{k<L} s_k² + ∑_{k<L} (B_{(j,j′),k}/2 − w s_k) |Δ_k|` and
`R̂_{(j,j′)} := (w/2)(Δ_0² − t²(x_j − x_{j′})²)` (p.47), `w = w_{jj′}`.

**Formalization Note.** Both parts are the paper's explicit formulas, so the identity (6.11) of
Theorem 6.9 is a genuine claim (it rests on the telescoping (6.6) through the max–min rule). -/
noncomputable def chainRem (P : Quadratic n) (t : ℝ) (L : ℕ) (π : Pair n) (x : Fin n → ℝ) : ℝ :=
  let w := pairWeight P π
  (-(w / 2) * chainDelta t π x L ^ 2 + w / 2 * ∑ k ∈ range L, (2 * Real.log (qPar t k)) ^ 2 +
    ∑ k ∈ range L, (gadgetEarn P t π k / 2 - w * (2 * Real.log (qPar t k))) *
      |chainDelta t π x k|) +
  w / 2 * (chainDelta t π x 0 ^ 2 - t ^ 2 * (xExt x π.1.1 - xExt x π.1.2) ^ 2)

/-- The linear remainder `R_lin(x) := ∑_{j=1}^n (α/t) c_j (log(1 + t x_j) − t x_j)`
(arXiv:2611.06589, p.27), with `α = λt²` (5.5). -/
noncomputable def Rlin (P : Quadratic n) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j, alpha P t / t * (P.c j : ℝ) * (Real.log (1 + t * x j) - t * x j)

/-- The normalization remainder `R_norm(x) := (n + 1) log(T(x)/(n + 1))` (arXiv:2611.06589,
(6.20), p.29). -/
noncomputable def Rnorm (P : Quadratic n) (t : ℝ) (L : ℕ) (x : Fin n → ℝ) : ℝ :=
  (n + 1) * Real.log (totalPay P t L x / (n + 1))

end LinearChoresCLS


