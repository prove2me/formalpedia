-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_Market
-- name    : BauerleRiederMDP_Indifference_Market
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:13.71236+00:00
-- url     : https://prove2.me/theorems/a11dd66a-db75-4e87-ba6c-b40068fcd81d
-- title:
--   The market data of §4.9: four-state returns, Assumption (FM), exponential utility
-- statement:
--   The market of Section 4.9 has a bond with zero interest, a traded risky asset and a non-traded risky asset. On the sample space $\Omega=\{\omega_1,\omega_2,\omega_3,\omega_4\}$ the relative price changes are
--   $$
--   \tilde R(\omega_1)=\tilde R(\omega_2)=u,\quad \tilde R(\omega_3)=\tilde R(\omega_4)=d,\qquad \hat R(\omega_1)=\hat R(\omega_3)=\hat u,\quad \hat R(\omega_2)=\hat R(\omega_4)=\hat d,
--   $$
--   and $\mathbb P(\{\omega_k\})=p_k>0$ with $p_1+p_2+p_3+p_4=1$. Assumption (FM) is $0<d<1<u$ and $\hat d<\hat u$. The investor has the utility $U(x)=-e^{-\gamma x}$ with $\gamma>0$.
--
--   These parameters determine both the one-period market and, through i.i.d. copies of $(\tilde R,\hat R)$, the multiperiod market. The incompleteness of the market comes from the asset $\hat S$, which cannot be traded.
--
--   **Formalization Note** The point $\omega_k$ is the element $k-1$ of `Fin 4`. The structure carries exactly the assumptions of the one-period market of p.135, so $\hat d$ may be negative. The multiperiod model of p.138 also has $\mathcal Z=\mathbb R_+\times\mathbb R_+$, i.e. $0\le\hat d$; the statements about that model take it as a hypothesis.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.9, p.135, Assumption (FM)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.Indifference

/-- The market data of §4.9 (Bäuerle & Rieder, Markov Decision Processes with Applications to
Finance (2011), §4.9, p.135, PDF 149 and p.138, PDF 152): the bond has zero interest (`i ≡ 0`), the
relative price changes `(R̃, R̂)` of the traded and the non-traded asset take the four values
`(u, û), (u, d̂), (d, û), (d, d̂)` on `Ω = {ω₁, ω₂, ω₃, ω₄}` with probabilities `p_k > 0`, Assumption
(FM) `0 < d < 1 < u`, `d̂ < û` holds, and the investor has the exponential utility
`U(x) = -e^{-γx}`, `γ > 0`.

**Formalization Note.** `ω_k` is the element `k - 1` of `Fin 4`, so `p 0, …, p 3` are the book's
`p₁, …, p₄`. The structure carries exactly the assumptions of the one-period market (p.135), so
`d̂` may be negative here. The multiperiod model of p.138 also puts the relative price changes in
`𝒵 := ℝ₊ × ℝ₊`, i.e. `0 ≤ d̂`; the statements about that model carry `0 ≤ M.dhat` as a hypothesis. -/
structure Market where
  /-- The up factor `u` of the traded asset. -/
  u : ℝ
  /-- The down factor `d` of the traded asset. -/
  d : ℝ
  /-- The up factor `û` of the non-traded asset. -/
  uhat : ℝ
  /-- The down factor `d̂` of the non-traded asset. -/
  dhat : ℝ
  /-- The risk aversion `γ`. -/
  γ : ℝ
  /-- The probabilities `p_k := ℙ({ω_k})`. -/
  p : Fin 4 → ℝ
  d_pos : 0 < d
  d_lt_one : d < 1
  one_lt_u : 1 < u
  dhat_lt_uhat : dhat < uhat
  γ_pos : 0 < γ
  p_pos : ∀ k, 0 < p k
  p_sum : ∑ k, p k = 1

namespace Market

/-- The relative price change `R̃` of the traded asset: `R̃(ω₁) = R̃(ω₂) = u`, `R̃(ω₃) = R̃(ω₄) = d`
(p.135, PDF 149). -/
def Rt (M : Market) : Fin 4 → ℝ := ![M.u, M.u, M.d, M.d]

/-- The relative price change `R̂` of the non-traded asset: `R̂(ω₁) = R̂(ω₃) = û`,
`R̂(ω₂) = R̂(ω₄) = d̂` (p.135, PDF 149). -/
def Rh (M : Market) : Fin 4 → ℝ := ![M.uhat, M.dhat, M.uhat, M.dhat]

/-- The probability measure `ℙ` on `Ω`, with `ℙ({ω_k}) = p_k` (p.135, PDF 149). -/
noncomputable def P (M : Market) : Measure (Fin 4) :=
  ∑ k, ENNReal.ofReal (M.p k) • Measure.dirac k

instance (M : Market) : IsProbabilityMeasure M.P := ⟨by
  have h : ∑ k, ENNReal.ofReal (M.p k) = ENNReal.ofReal (∑ k, M.p k) :=
    (ENNReal.ofReal_sum_of_nonneg fun k _ => (M.p_pos k).le).symm
  simp [P, Measure.finsetSum_apply, h, M.p_sum]⟩

end Market

end BauerleRiederMDP.Indifference


