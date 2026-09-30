-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_AuxiliaryParameters
-- name    : WeierstrassEllipticZeta_AuxiliaryParameters
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T15:02:21.920744+00:00
-- url     : https://prove2.me/theorems/256f6590-bee5-4018-b43a-8d6cca380f72
-- title:
--   Rounded auxiliary parameters and their geometric bounds on shifted grids
-- statement:
--   For a nonnegative integer $N$, define
--
--   $$m=\lfloor N/\log N\rfloor,\qquad
--   \ell=\lfloor\sqrt{N\log N}\rfloor,\qquad
--   s=\lfloor N^{3/16}\rfloor,\qquad
--   q=\lfloor N^{5/8}\log N/64\rfloor,\qquad
--   R=N^{49/72}.$$
--
--   Only sufficiently large $N$ enter the estimates. The formal definitions use nonnegative integer floors, which agree with the displayed floors there. The constant $1/64$ is one explicit small choice for the source's freely chosen grid constant.
--
--   The five displayed quantities define the numerical parameter functions. The grid-data predicate below is a separate proposition; its truth is not built into these definitions.
--
--   Write $\Omega$ for the period lattice and put
--
--   $$U=|u_1|+|u_2|+|\omega|+1,\qquad r=4qU,$$
--
--   $$\Gamma_N=\{a_1u_1+a_2u_2+a_3\omega+u_1/2:
--   0\le a_1,a_2<s,\ 0\le a_3<q,\ a_i\in\mathbb Z\},$$
--
--   $$\Gamma_N^{(3)}=\{a_1u_1+a_2u_2+a_3\omega+u_1/2:
--   0\le a_1,a_2<3s,\ 0\le a_3<3q,\ a_i\in\mathbb Z\}.$$
--
--   The grid parameter data assert that, for every fixed $B>0$, all sufficiently large $N$ satisfy
--
--   $$m,\ell,q\ge1,\qquad 2\le s\le q,$$
--
--   $$8(m+1)|\Gamma_N|\le(m+1)(\ell+1)^2,\qquad
--   \frac{N^2}{512}\le(m+1)|\Gamma_N|\le\frac{N^2}{32},$$
--
--   $$m\log N\le N,\qquad \ell s^2\le m,\qquad R\ge1,\qquad r>0,$$
--
--   $$z\in\Gamma_N^{(3)}\ \Longrightarrow\ z\notin\Omega\ \text{and}\ |z|+1\le r,$$
--
--   $$\frac{2r}{R}\le N^{-1/36},\qquad B\ell R^2\le N^2.$$
--
--   Here the grids are the actual finite sets, so their cardinalities count distinct points. All shifted points are regular, including shifts whose unshifted point lies in the lattice. The counts allow vanishing conditions on the entire shifted grid; the data do not assert that an auxiliary function satisfying those conditions has already been constructed. Basic sigma factors, arithmetic coordinate presentations, coefficient envelopes, and the zero estimate are separate obligations.
-- source:
--   Definitions supporting Senthil Kumar K (2026), Section 5 parameter choice before Lemma 7, Lemma 8 counts, and equations (30)-(32). The fixed constant 1/64 and radius 4q(|u1|+|u2|+|omega|+1) are explicit choices with slack; the predicate states the precise supporting estimates, rather than a new source assertion. https://doi.org/10.1017/S001309152610145X

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids

noncomputable section

namespace WeierstrassEllipticZeta

/-- Degree in the ordinary variable in the Section 5 auxiliary polynomial. -/
def auxiliaryL0 (N : ℕ) : ℕ := ⌊(N : ℝ) / Real.log N⌋₊

/-- The common degree in the elliptic and zeta variables. -/
def auxiliaryL (N : ℕ) : ℕ := ⌊Real.sqrt ((N : ℝ) * Real.log N)⌋₊

/-- The first two side lengths of the auxiliary grid. -/
def auxiliaryS (N : ℕ) : ℕ := ⌊(N : ℝ) ^ (3 / 16 : ℝ)⌋₊

/-- The period side length, with the admissible fixed constant `1/64`. -/
def auxiliaryS3 (N : ℕ) : ℕ := ⌊(N : ℝ) ^ (5 / 8 : ℝ) * Real.log N / 64⌋₊

/-- The outer interpolation radius in Section 5, equation (32). -/
def auxiliaryRadius (N : ℕ) : ℝ := (N : ℝ) ^ (49 / 72 : ℝ)

/-- Numerical dimension, zero-count, radius and growth estimates on the actual
shifted grids. Construction of the analytic functions is a separate obligation. -/
def AuxiliaryGridParameterData (L : PeriodPair) (ω u₁ u₂ : ℂ) : Prop :=
  ∀ B : ℝ, 0 < B → ∀ᶠ N : ℕ in Filter.atTop,
    let m := auxiliaryL0 N
    let l := auxiliaryL N
    let s := auxiliaryS N
    let q := auxiliaryS3 N
    let R := auxiliaryRadius N
    let U := ‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1
    let r := 4 * q * U
    let Γ := shiftedAuxiliaryGrid u₁ u₂ ω ![s, s, q]
    let Γ₃ := shiftedAuxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q]
    1 ≤ m ∧ 1 ≤ l ∧ 2 ≤ s ∧ 1 ≤ q ∧ s ≤ q ∧
    8 * ((m + 1) * Γ.card) ≤ (m + 1) * (l + 1) ^ 2 ∧
    (N : ℝ) ^ 2 / 512 ≤ (m + 1 : ℝ) * Γ.card ∧
    (m + 1 : ℝ) * Γ.card ≤ (N : ℝ) ^ 2 / 32 ∧
    (m : ℝ) * Real.log N ≤ N ∧ l * s ^ 2 ≤ m ∧
    1 ≤ R ∧ 0 < r ∧
    (∀ z ∈ Γ₃, z ∉ L.lattice ∧ ‖z‖ + 1 ≤ r) ∧
    2 * r / R ≤ (N : ℝ) ^ (-1 / 36 : ℝ) ∧
    B * l * R ^ 2 ≤ (N : ℝ) ^ 2

end WeierstrassEllipticZeta


