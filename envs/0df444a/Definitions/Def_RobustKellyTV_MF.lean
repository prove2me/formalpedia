-- Prove2me | Definitions.Def_RobustKellyTV_MF
-- name    : RobustKellyTV_MF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:55.21317+00:00
-- url     : https://prove2.me/theorems/3e1387c3-cbc7-4e6f-9e38-3286db095eaf
-- title:
--   The learn-an-event process $M^{\mathrm F}$
-- statement:
--   Let $m_j=2^j$ for $j\ge 0$ and let $\bar S_m$ be the empirical distribution after $m$ observations. At time $m_j$ select
--
--   $$\widehat A_j=\{i:\bar S_{m_j,i}>P_i\},\quad q_j=P(\widehat A_j)+\epsilon_0,\quad \widehat\Delta_j=(D_{\mathrm{TV}}(\bar S_{m_j},P)-\epsilon_0)_+,\quad \lambda_j=4\widehat\Delta_j .$$
--
--   Account $j$ starts at one, bets during observations $m_j+1,\dots,2m_j$, then freezes: with $\nu_j(n)=((n\wedge 2m_j)-m_j)_+$,
--
--   $$W^{(j)}_n=1\ (n\le m_j),\qquad W^{(j)}_n=\exp\Big(\lambda_j\sum_{t=m_j+1}^{n\wedge 2m_j}(\mathbf 1\{X_t\in\widehat A_j\}-q_j)-\frac{\nu_j(n)\lambda_j^2}{8}\Big)\ (n>m_j).$$
--
--   With initial capital $w_j=1/[(j+1)(j+2)]$, the process is
--
--   $$M^{\mathrm F}_n=\sum_{j=0}^\infty w_jW^{(j)}_n .$$
--
--   The weights sum to one, so $M^{\mathrm F}_0=1$, and the process does not depend on the level $\alpha$.
--
--   **Formalization Note** The series is a `tsum`; for fixed $n$ all but finitely many accounts equal one, so it is summable (checked separately). The block sum runs over coordinates $m_j,\dots,(n\wedge2m_j)-1$.
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §3.2 eqs. (25)–(27) p.11, p.12

import Mathlib
import Definitions.Def_RobustKellyTV_Mck

namespace RobustKellyTV

variable {d : ℕ}

/-- The selected event `Â_j = {i : S̄_{m_j,i} > Pᵢ}`, `m_j = 2^j` (arXiv:2611.02130v1, eq. (25),
p.11). It is computed from the first `m_j` observations (coordinates `0, …, m_j − 1`). -/
noncomputable def selEvent (σ : Setting d) (x : ℕ → Fin d) (j : ℕ) : Finset (Fin d) :=
  Finset.univ.filter (fun i => σ.P i < empirical x (2 ^ j) i)

/-- `q_j = P(Â_j) + ϵ0` (arXiv:2611.02130v1, eq. (25), p.11). -/
noncomputable def qSel (σ : Setting d) (x : ℕ → Fin d) (j : ℕ) : ℝ :=
  ∑ i ∈ selEvent σ x j, σ.P i + σ.ε₀

/-- The estimated excess `∆̂_j = (D_TV(S̄_{m_j}, P) − ϵ0)₊` (arXiv:2611.02130v1, eq. (25), p.11). -/
noncomputable def gapHat (σ : Setting d) (x : ℕ → Fin d) (j : ℕ) : ℝ :=
  max (tv (empirical x (2 ^ j)) σ.P - σ.ε₀) 0

/-- The betting intensity `λ_j = 4 ∆̂_j` (arXiv:2611.02130v1, eq. (25), p.11); `λ_j = 0` when the
estimated excess is zero ("the account does not bet"). -/
noncomputable def betSize (σ : Setting d) (x : ℕ → Fin d) (j : ℕ) : ℝ :=
  4 * gapHat σ x j

/-- The number of bets placed by account `j` up to time `n`, `ν_j(n) = ((n ∧ 2m_j) − m_j)₊`
(arXiv:2611.02130v1, p.11); natural-number subtraction is the positive part. -/
def nBets (j n : ℕ) : ℕ :=
  min n (2 * 2 ^ j) - 2 ^ j

/-- The wealth of account `j` (arXiv:2611.02130v1, eq. (26), p.11):
`W^{(j)}_n = 1` for `n ≤ m_j`, and for `n > m_j`
`W^{(j)}_n = exp(λ_j Σ_{t=m_j+1}^{n∧2m_j} (1{X_t ∈ Â_j} − q_j) − ν_j(n) λ_j² / 8)`.

**Formalization Note.** Observation `X_t` is coordinate `t − 1`, so the sum over
`t = m_j + 1, …, n ∧ 2m_j` is over coordinates `Finset.Ico m_j (n ∧ 2m_j)`. -/
noncomputable def account (σ : Setting d) (j n : ℕ) (x : ℕ → Fin d) : ℝ :=
  if n ≤ 2 ^ j then 1 else
    Real.exp (betSize σ x j *
        ∑ t ∈ Finset.Ico (2 ^ j) (min n (2 * 2 ^ j)),
          ((if x t ∈ selEvent σ x j then (1 : ℝ) else 0) - qSel σ x j) -
      (nBets j n : ℝ) * betSize σ x j ^ 2 / 8)

/-- The initial capital `w_j = 1 / [(j + 1)(j + 2)]` of account `j` (arXiv:2611.02130v1, p.11). -/
noncomputable def weight (j : ℕ) : ℝ :=
  1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))

/-- The learned-event process `M^F_n = Σ_{j=0}^∞ w_j W^{(j)}_n` (arXiv:2611.02130v1, eq. (27), p.11).

**Formalization Note.** A `tsum`: for fixed `n`, `W^{(j)}_n = 1` whenever `2^j ≥ n`, so the series is
`Σ w_j` plus finitely many other terms and is summable (checked in the verification file), and
`M^F_0 = Σ_j w_j = 1`. -/
noncomputable def MF (σ : Setting d) (n : ℕ) (x : ℕ → Fin d) : ℝ :=
  ∑' j, weight j * account σ j n x

end RobustKellyTV


