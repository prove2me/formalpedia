-- Prove2me | Definitions.Def_FixedPriceTrade_Supplement_rFam
-- name    : FixedPriceTrade_Supplement_rFam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:16:16.227063+00:00
-- url     : https://prove2.me/theorems/4e08a3c5-3742-4dcd-bf55-4256ffc216a3
-- title:
--   The two-unit curve family $\mathfrak F$, $R_{\mathrm f}$ and $r_{\mathrm{fam}}=\inf_{\mathfrak F}R_{\mathrm f}$
-- statement:
--   For $0<t_f<1$, $t_f\le p_f\le1$ and $\xi_0>0$ put
--   $$
--   m_f=\frac{2t_f}{1+t_f},\quad N_f=\frac2{1+t_f},\quad c_f=\frac{p_f-t_f}2,\quad \delta_f=\frac{p_f+t_f}2,\quad e_f=\frac{1+t_f}2,\quad v_f=1-e_f,\quad a_f=\frac{c_f}{t_fp_f},\quad h_f=\frac{v_f}{\xi_0},
--   $$
--   and require $\xi_0\ge c_f$. The **closed curve class** $\mathfrak F$ consists of the positive, concave, Lipschitz functions $P$ on $[c_f,\xi_0]$ with
--   $$
--   P(c_f)=p_f,\qquad P(\xi_0)=1,\qquad P(\xi)\le\min\{\xi+\delta_f,\ h_f\xi+e_f\}.
--   $$
--   For $P\in\mathfrak F$ define
--   $$
--   T_f=\int_{c_f}^{\xi_0}P^{-2}\,d\xi,\quad Q_f=\int_{c_f}^{\xi_0}\xi\Big(\frac{P'}{P}\Big)^2d\xi,\quad M_f=N_f(a_f+T_f-\xi_0),\quad G_f=2+2m_fa_f-N_f\log p_f-N_fQ_f,\quad R_f=\frac{M_f+2}{M_f+G_f},
--   $$
--   and $r_{\mathrm{fam}}=\inf R_f$ over all feasible triples and curves.
--
--   The family describes limiting two-unit instances (the second buyer's body is the single value $a_f$); $R_f$ is their welfare ratio, and $r_{\mathrm{fam}}\approx0.729080$ is the conjectured optimal two-unit guarantee.
--
--   **Formalization Note** $P$ is a function on $\mathbb R$ of which only the values on $[c_f,\xi_0]$ matter; the degenerate interval $c_f=\xi_0$ (forcing $p_f=1$) is included. $P'$ is Lean's `deriv P`, which equals the almost-everywhere derivative of the Lipschitz $P$ on the interval. $r_{\mathrm{fam}}$ is an infimum over a nonempty set; its attainment is Proposition 13.2 of the paper, not part of the definition.
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 2683234615efe3b875b8a3f0cde6b0637c6b82cf550767823ebc24d5cd1bca0e), §13.4, (63)–(65), p.29; Proposition 13.2 (definition of r_fam), p.29 (PDF p.29)

import Mathlib

set_option autoImplicit false

namespace FixedPriceTrade.Supplement

open MeasureTheory Set

/-- `m_f = 2t_f/(1 + t_f)` ((63), p.29). -/
noncomputable def mF (t : ℝ) : ℝ := 2 * t / (1 + t)
/-- `N_f = 2/(1 + t_f)` ((63)). -/
noncomputable def NF (t : ℝ) : ℝ := 2 / (1 + t)
/-- `c_f = (p_f − t_f)/2` ((63)). -/
noncomputable def cF (t p : ℝ) : ℝ := (p - t) / 2
/-- `δ_f = (p_f + t_f)/2` ((63)). -/
noncomputable def deltaF (t p : ℝ) : ℝ := (p + t) / 2
/-- `e_f = (1 + t_f)/2` ((63)). -/
noncomputable def eF (t : ℝ) : ℝ := (1 + t) / 2
/-- `v_f = 1 − e_f` ((63)). -/
noncomputable def vF (t : ℝ) : ℝ := 1 - eF t
/-- `a_f = c_f/(t_f p_f)` ((63)). -/
noncomputable def aF (t p : ℝ) : ℝ := cF t p / (t * p)
/-- `h_f = v_f/ξ₀` ((63)). -/
noncomputable def hF (t ξ0 : ℝ) : ℝ := vF t / ξ0

/-- The parameter range of (63)–(64), p.29: `0 < t_f < 1`, `t_f ≤ p_f ≤ 1`, `ξ₀ > 0`, `ξ₀ ≥ c_f`. -/
def IsFamilyTriple (t p ξ0 : ℝ) : Prop :=
  0 < t ∧ t < 1 ∧ t ≤ p ∧ p ≤ 1 ∧ 0 < ξ0 ∧ cF t p ≤ ξ0

/-- **The closed curve class `F`** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee of
Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), (64), p.29: positive,
concave, Lipschitz `P` on `[c_f, ξ₀]` with `P(c_f) = p_f`, `P(ξ₀) = 1` and
`P(ξ) ≤ U_f(ξ) = min{ξ + δ_f, h_f ξ + e_f}`.

**Formalization Note.** `P` is a function on `ℝ`; only its values on `[c_f, ξ₀]` enter. A triple is
feasible when this class is nonempty; `c_f = ξ₀` (the degenerate interval, forcing `p_f = 1`) is
included. -/
def InCurveClass (t p ξ0 : ℝ) (P : ℝ → ℝ) : Prop :=
  (∀ ξ ∈ Icc (cF t p) ξ0, 0 < P ξ) ∧ ConcaveOn ℝ (Icc (cF t p) ξ0) P ∧
    (∃ K : NNReal, LipschitzOnWith K P (Icc (cF t p) ξ0)) ∧
    P (cF t p) = p ∧ P ξ0 = 1 ∧
    ∀ ξ ∈ Icc (cF t p) ξ0, P ξ ≤ min (ξ + deltaF t p) (hF t ξ0 * ξ + eF t)

/-- `T_f = ∫_{c_f}^{ξ₀} P^{−2} dξ` ((65), p.29). -/
noncomputable def TF (t p ξ0 : ℝ) (P : ℝ → ℝ) : ℝ := ∫ ξ in cF t p..ξ0, (P ξ ^ 2)⁻¹

/-- `Q_f = ∫_{c_f}^{ξ₀} ξ (P′/P)² dξ` ((65), p.29).

**Formalization Note.** `P′` is Lean's `deriv P`. A Lipschitz `P` is differentiable almost
everywhere on `[c_f, ξ₀]`, and `deriv P` agrees with the a.e. derivative there (at interior points
it only reads values of `P` inside the interval), so the integral is the paper's. -/
noncomputable def QF (t p ξ0 : ℝ) (P : ℝ → ℝ) : ℝ := ∫ ξ in cF t p..ξ0, ξ * (deriv P ξ / P ξ) ^ 2

/-- `M_f = N_f(a_f + T_f − ξ₀)` ((65)). -/
noncomputable def MF (t p ξ0 : ℝ) (P : ℝ → ℝ) : ℝ := NF t * (aF t p + TF t p ξ0 P - ξ0)

/-- `G_f = 2 + 2m_f a_f − N_f log p_f − N_f Q_f` ((65)); `p_f ≥ t_f > 0`, so the logarithm is genuine. -/
noncomputable def GF (t p ξ0 : ℝ) (P : ℝ → ℝ) : ℝ :=
  2 + 2 * mF t * aF t p - NF t * Real.log p - NF t * QF t p ξ0 P

/-- `R_f = (M_f + 2)/(M_f + G_f)` ((65), p.29). -/
noncomputable def RF (t p ξ0 : ℝ) (P : ℝ → ℝ) : ℝ := (MF t p ξ0 P + 2) / (MF t p ξ0 P + GF t p ξ0 P)

/-- **The family value** `r_fam = inf_F R_f` (Proposition 13.2, p.29): the infimum of `R_f` over
feasible triples `(t_f, p_f, ξ₀)` and curves `P ∈ F`.

**Formalization Note.** Defined as `sInf`; the set is nonempty (the degenerate triple
`(1/2, 1, 1/4)` with `P ≡ 1` is feasible) and Appendix D (p.49) shows `R_f > 18227/25000` on `F`. Attainment is
Proposition 13.2, not part of the definition. -/
noncomputable def rFam : ℝ :=
  sInf {r : ℝ | ∃ t p ξ0 : ℝ, ∃ P : ℝ → ℝ, IsFamilyTriple t p ξ0 ∧ InCurveClass t p ξ0 P ∧
    RF t p ξ0 P = r}

end FixedPriceTrade.Supplement


