-- Prove2me | Definitions.Def_Random2SATWindow_CriticalLaw_Strata
-- name    : Random2SATWindow_CriticalLaw_Strata
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:41:27.946961+00:00
-- url     : https://prove2.me/theorems/92036f79-8bde-476e-9930-89279b91ef06
-- title:
--   The cubic constants $s_r$, the decorations $a_j,b_j$, the Airy quotients $R_q$, the strata limits $\pi_q$ and the series $f=\sum_q\pi_q$
-- statement:
--   * (82) $s_r=\dfrac1{(2r)!}\displaystyle\sum_M\frac1{\prod_{i,j}m_{ij}!}$, the sum over $2r\times2r$ nonnegative integer matrices $M$ with $\sum_j(m_{ij}+m_{ji})=3$ for every $i$, every row and column nonzero, and strongly connected as a directed multigraph on $[2r]$ (`IsCubicSCMatrix`, `kernelConst r`). The degree condition forces $m_{ij}\le3$, so entries range over `Fin 4`. Check: $s_1=1/2$, $s_2=17/8$.
--   * (84) $a_j=[v^j]\exp\big(-\tfrac12\sum_{r\ge1}s_rv^r\big)$, $b_j=[v^j]\exp\big(-\sum_{r\ge1}s_rv^r\big)$ (`aCoef`, `bCoef`). Check: $(a_0,a_1,a_2)=(1,-\tfrac14,-\tfrac{33}{32})$, $(b_0,b_1,b_2)=(1,-\tfrac12,-2)$.
--   * (120) $N_j(\zeta)=4^{-j}a_jA_{1/2-3j}(2^{-2/3}\zeta)$, $D_j(\zeta)=2^{-j}b_jA_{1-3j}(\zeta)$.
--   * (121) $R_0=N_0/D_0$, $R_q=\frac1{D_0}\big(N_q-\sum_{j=1}^qD_jR_{q-j}\big)$ (`Rq`), $\hat Q_q(\theta)=R_q(-i2^{1/3}\theta)$ (`Qhat`).
--   * (126) $\pi_q(x)=\dfrac{2^{-1/6}\sqrt\pi\,e^{-x^3/6}}{2\pi}\displaystyle\int_{\mathbb R}e^{-i2^{-2/3}x\theta}\hat Q_q(\theta)\,d\theta$ (`piQC q x`, complex; `piPrefactor`, `piIntegrand`); `piQ q x` is its real part.
--   * Theorem 3.1: `fProfile x` $=\sum_{q\ge0}\pi_q(x)$, the series (not the limit; that the satisfiability probabilities converge to it is the theorem).
--   * Unfolding (121) (cf. (54)): $R_q=\sum(-1)^kN_{j_0}D_{j_1}\cdots D_{j_k}/D_0^{k+1}$ over $j_0\ge0$ and compositions $(j_1,\dots,j_k)$ of $q-j_0$ (`RqTerm`, integrand `piTermIntegrand`).
--   * (145) $C_0=\sqrt{\pi/2}\,A_{1/2}(2^{-2/3}a'_1)/(-a'_1\,\mathrm{Ai}(a'_1))$ as a function of $a'_1$ (`rightTailConst`), with $\mathrm{Ai}=A_0$ by (31).
--
--   **Formalization Note.** The checks above were done by exact enumeration of (82) and of the recurrences under (84), outside the mission; they agree with the paper's table, as do $N_1=-\frac1{16}A_{-5/2}(2^{-2/3}\zeta)$, $D_1=-\frac14A_{-2}(\zeta)$, $N_2=-\frac{33}{512}A_{-11/2}$, $D_2=-\frac12A_{-5}$. Quadrature of (126) from these definitions gives $\pi_0(0)\approx0.802463$.
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), (82) printed p. 36 (PDF 38); (84) printed p. 37 (PDF 39); (120)–(121) printed pp. 47–48 (PDF 49–50); (126) printed p. 49 (PDF 51); Theorem 3.1 printed p. 9 (PDF 11); (145) printed p. 57 (PDF 59)

import Mathlib
import Definitions.Def_Random2SATWindow_CriticalLaw_Airy
import Definitions.Def_Random2SATWindow_CriticalLaw_Hadamard

set_option autoImplicit false

open scoped BigOperators
open Complex MeasureTheory

namespace Random2SATWindow.CriticalLaw

/-! # The cubic constants `s_r`, the decorations `a_j, b_j`, the Airy quotients `R_q` and the
strata limits `π_q`

Ravelomanana, *Inside the Critical Window of Random 2-SAT*, STOC 2027 submission (manuscript
sha256 eef2fa67…), (82) printed p. 36 (PDF 38); (84) printed p. 37 (PDF 39); (120)–(121)
printed pp. 47–48 (PDF 49–50); (126) printed p. 49 (PDF 51); Theorem 3.1 printed p. 9 (PDF 11);
(145) printed p. 57 (PDF 59). -/

/-- The conditions on a `2r × 2r` nonnegative integer matrix `M` in (82): every vertex `i` has
total degree `Σ_j (m_ij + m_ji) = 3`, every row and column is nonzero, and `M` is strongly
connected as a directed multigraph on `[2r]` (`i → j` when `m_ij > 0`). -/
def IsCubicSCMatrix {r : ℕ} (M : Fin (2 * r) → Fin (2 * r) → Fin 4) : Prop :=
  (∀ i, ∑ j, ((M i j : ℕ) + (M j i : ℕ)) = 3) ∧ (∀ i, ∃ j, 0 < (M i j : ℕ)) ∧
    (∀ j, ∃ i, 0 < (M i j : ℕ)) ∧
    ∀ i j, Relation.ReflTransGen (fun a b => 0 < (M a b : ℕ)) i j

open Classical in
/-- The cubic-kernel constant (82): `s_r = (1/(2r)!) Σ_M 1/∏_{i,j} m_ij!`, the sum over the
`2r × 2r` nonnegative integer matrices of `IsCubicSCMatrix`. Entries are at most `3` under the
degree condition, so the matrices are enumerated with entries in `Fin 4`. -/
noncomputable def kernelConst (r : ℕ) : ℚ :=
  ((2 * r).factorial : ℚ)⁻¹ *
    ∑ M ∈ (Finset.univ : Finset (Fin (2 * r) → Fin (2 * r) → Fin 4)).filter IsCubicSCMatrix,
      (∏ i, ∏ j, (((M i j : ℕ).factorial : ℚ)))⁻¹

/-- `Σ_{r ≥ 1} s_r v^r`. -/
noncomputable def kernelSeries : PowerSeries ℚ :=
  PowerSeries.mk fun r => if r = 0 then 0 else kernelConst r

/-- `a_j = [v^j] exp(-½ Σ_{r ≥ 1} s_r v^r)` (84). -/
noncomputable def aCoef (j : ℕ) : ℚ :=
  PowerSeries.coeff j (expOf (-((1 / 2 : ℚ) • kernelSeries)))

/-- `b_j = [v^j] exp(-Σ_{r ≥ 1} s_r v^r)` (84). -/
noncomputable def bCoef (j : ℕ) : ℚ :=
  PowerSeries.coeff j (expOf (-kernelSeries))

/-- `N_j(ζ) = 4^{-j} a_j A_{1/2-3j}(2^{-2/3} ζ)` (120). -/
noncomputable def Nj (j : ℕ) (ζ : ℂ) : ℂ :=
  ((4 : ℂ) ^ j)⁻¹ * (aCoef j : ℂ) * airyA (1 / 2 - 3 * j) (((2 : ℝ) ^ (-(2 / 3 : ℝ)) : ℝ) * ζ)

/-- `D_j(ζ) = 2^{-j} b_j A_{1-3j}(ζ)` (120). -/
noncomputable def Dj (j : ℕ) (ζ : ℂ) : ℂ :=
  ((2 : ℂ) ^ j)⁻¹ * (bCoef j : ℂ) * airyA (1 - 3 * j) ζ

/-- The Airy quotients (121): `R_0 = N_0/D_0` and
`R_q = (1/D_0) (N_q - Σ_{j=1}^q D_j R_{q-j})` (the sum is written over `i = q - j < q`). -/
noncomputable def Rq (q : ℕ) (ζ : ℂ) : ℂ :=
  (Nj q ζ - ∑ i : Fin q, Dj (q - i) ζ * Rq i ζ) / Dj 0 ζ
decreasing_by exact i.isLt

/-- `Q̂_q(θ) = R_q(-i 2^{1/3} θ)` (121). -/
noncomputable def Qhat (q : ℕ) (θ : ℝ) : ℂ :=
  Rq q (-Complex.I * ((2 : ℝ) ^ (1 / 3 : ℝ) * θ : ℝ))

/-- The constant `2^{-1/6} √π e^{-x³/6} / (2π)` in front of (126). -/
noncomputable def piPrefactor (x : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(1 / 6 : ℝ)) * Real.sqrt Real.pi * Real.exp (-x ^ 3 / 6) / (2 * Real.pi)

/-- The integrand of (126): `θ ↦ e^{-i 2^{-2/3} x θ} Q̂_q(θ)`. -/
noncomputable def piIntegrand (q : ℕ) (x θ : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * x * θ : ℝ)) * Qhat q θ

/-- The strata limits (126):
`π_q(x) = (2^{-1/6} √π e^{-x³/6} / (2π)) ∫_ℝ e^{-i 2^{-2/3} x θ} Q̂_q(θ) dθ`
(as a complex number; Theorem 5.1 asserts it is real and in `[0, 1]`). -/
noncomputable def piQC (q : ℕ) (x : ℝ) : ℂ :=
  (piPrefactor x : ℂ) * ∫ θ : ℝ, piIntegrand q x θ

/-- The real part of `π_q(x)`. -/
noncomputable def piQ (q : ℕ) (x : ℝ) : ℝ := (piQC q x).re

/-- The explicit Airy series of Theorem 3.1, `f(x) = Σ_{q ≥ 0} π_q(x)` (the series, not the limit:
that the satisfiability probabilities converge to it is the content of Theorem 3.1). -/
noncomputable def fProfile (x : ℝ) : ℝ := ∑' q : ℕ, piQ q x

/-! ### The finite expansion of `R_q` into Airy monomials (cf. (54))

Unfolding (121), `R_q = Σ (-1)^k N_{j_0} D_{j_1} ⋯ D_{j_k} / D_0^{k+1}`, the sum over
`j_0 ≥ 0` and `j_1, …, j_k ≥ 1` with `j_0 + j_1 + ⋯ + j_k = q`; `(j_1, …, j_k)` is a composition
of `q - j_0`. -/

/-- One Airy monomial `(-1)^k N_{j_0}(ζ) D_{j_1}(ζ) ⋯ D_{j_k}(ζ) / D_0(ζ)^{k+1}`, where
`(j_1, …, j_k)` is the composition `c` of `q - j_0`. -/
noncomputable def RqTerm (q : ℕ) (j0 : Fin (q + 1)) (c : Composition (q - j0)) (ζ : ℂ) : ℂ :=
  (-1 : ℂ) ^ c.length * Nj j0 ζ * (c.blocks.map fun b => Dj b ζ).prod / Dj 0 ζ ^ (c.length + 1)

/-- The integrand of the monomial `RqTerm` in (126). -/
noncomputable def piTermIntegrand (q : ℕ) (j0 : Fin (q + 1)) (c : Composition (q - j0))
    (x θ : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * x * θ : ℝ)) *
    RqTerm q j0 c (-Complex.I * ((2 : ℝ) ^ (1 / 3 : ℝ) * θ : ℝ))

/-- The right-tail constant (145), `C_0 = √(π/2) A_{1/2}(2^{-2/3} a'_1) / (-a'_1 Ai(a'_1))`, as a
function of the zero `a'_1` of `Ai′`; `Ai = A_0` by (31). -/
noncomputable def rightTailConst (a1 : ℝ) : ℂ :=
  (Real.sqrt (Real.pi / 2) : ℂ) * airyA (1 / 2) (((2 : ℝ) ^ (-(2 / 3 : ℝ)) * a1 : ℝ)) /
    (-(a1 : ℂ) * airyA 0 (a1 : ℂ))

end Random2SATWindow.CriticalLaw


