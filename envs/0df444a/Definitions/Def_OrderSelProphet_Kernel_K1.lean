-- Prove2me | Definitions.Def_OrderSelProphet_Kernel_K1
-- name    : OrderSelProphet_Kernel_K1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:58:04.366206+00:00
-- url     : https://prove2.me/theorems/413ed05e-f7e1-42d5-a1df-4e52ac161616
-- title:
--   The kernel $K_1$ of (66)–(68) with the 69 integers of Table 5, and $\Gamma_1=74500001/10^8$ (69)
-- statement:
--   With $\Delta=2/5$, row cells $I_i=[i\Delta,(i+1)\Delta)$ ($0\le i<16$), column cells $J_j=[j\Delta,(j+1)\Delta)$ ($0\le j<25$), $E_{ij}$ the $16\times25$ matrix units, $\vartheta=999999999/10^9$ and row groups $\mathcal I_1=\{1,2,3,4\}$, $\mathcal I_2=\{5,6,7\}$, $\mathcal I_3=\{8,\dots,15\}$, the cell perturbation is (66)
--   $$\delta=\frac{\vartheta}{10^{21}}\sum_{g=1}^3\sum_{i\in\mathcal I_g}\sum_{j=1}^{23}N_{g,j}\,(E_{ij}+E_{0,24}-E_{i,24}-E_{0,j}),$$
--   with the integers $N_{g,j}$ of Table 5 (listed verbatim in `tableN1`, `tableN2`, `tableN3`). With $\omega_j=e^{-j\Delta}-e^{-(j+1)\Delta}$ and $w_{ij}=\delta_{ij}/(\Delta\omega_j)$,
--   $$p_0(a,r)=e^{-r}\mathbf 1\{a<r\},\qquad p_1(a,r)=e^{-r}\Big[\mathbf 1\{a<r\}+\sum_{i=0}^{15}\sum_{j=0}^{24}w_{ij}\mathbf 1\{a\in I_i\}\mathbf 1\{r\in J_j\}\Big]\ (67).$$
--   The kernel (68): $K_1(t_r,u_a)=e^a\int_0^rp_1(a,v)dv$ for $a,r\ge0$, i.e. $K_1(t,u)=\frac1{1-u}\int_0^{r(t)}p_1(-\log(1-u),v)dv$ for $t,u\in[0,1)$; $K_1(1,u)=1$ for $u<1$; $K_1(t,1)=t$; $0$ outside $[0,1]^2$ (unused). Finally $\Gamma_1=74500001/100000000$ (69).
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), §6.2–6.3, eqs. (66)–(69), pp. 29–30; Table 5, p. 49

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Coordinates

set_option autoImplicit false

open MeasureTheory Set

namespace OrderSelProphet.Kernel

/-! # The kernel K1 and the ratio Γ1

Peng and Tang (2026), arXiv:2610.34892, §6.2–6.3, eqs. (66)–(69), pp. 29–30, with the 69 integers
of Table 5, p. 49. -/

/-- Column `N_{1,j}`, `j = 1, …, 23`, of Table 5 (p. 49), in the order `j = 1, 2, …, 23`. -/
def tableN1 : List ℤ :=
  [139368429085091008, 5953487440217, 3990741975321,
   2675074343691, -1179057110689020928, 543811243036226816,
   187787420768742656, 596185967112761600, 423259029123334464,
   -691811398605077888, -184413906041231008, 34902452349492964,
   -37556789677386504, -47401672754419120, -96227740933766672,
   275400707757524384, 130717989035219808, 77567271414955840,
   -56519617666625056, -44238050328599312, -29653651932793608,
   -19877437328715028, -13324244705254784]

/-- Column `N_{2,j}`, `j = 1, …, 23`, of Table 5 (p. 49), in the order `j = 1, 2, …, 23`. -/
def tableN2 : List ℤ :=
  [253843311272096320, 1791759853683, 1201052547606,
   805089599003, 2698338485333, 1808750378235,
   1212441636912, -1832980005978172416, -313737654730343936,
   898120583974625280, 390602254327415360, 306734431836344000,
   263005582702171680, 173208685273138400, 168402329898501888,
   10295857615769126, -98670230297316768, -71065873407713880,
   -50315851097015144, -38428024022805248, -25759074832025444,
   -16129817091862610, -11156299818298360]

/-- Column `N_{3,j}`, `j = 1, …, 23`, of Table 5 (p. 49), in the order `j = 1, 2, …, 23`. -/
def tableN3 : List ℤ :=
  [32389009049152552, 71119674367, 47672943393,
   31956129611, 107104171361, 71794073076,
   48125006371, 51614650583, 34598334963,
   23191957399, 15546034017, 10420818254,
   6985283324, 11457312846336316, 22884320211898852,
   -114815326321236128, -10429295523610740, 172273975475231,
   54605577509679488, 42002973082326256, -12472760155322594,
   -12759564154888524, -7869831686836923]

/-- The integer `N_{g,j}` of Table 5 for `g ∈ {1,2,3}` and `j ∈ {1, …, 23}` (`0` elsewhere). -/
def tableN (g j : ℕ) : ℤ :=
  (match g with
    | 1 => tableN1
    | 2 => tableN2
    | 3 => tableN3
    | _ => []).getD (j - 1) 0

/-- The row groups `𝓘_1 = {1,2,3,4}`, `𝓘_2 = {5,6,7}`, `𝓘_3 = {8, …, 15}` (p. 30). -/
def rowGroup (g : ℕ) : Finset ℕ :=
  match g with
    | 1 => {1, 2, 3, 4}
    | 2 => {5, 6, 7}
    | 3 => Finset.Icc 8 15
    | _ => ∅

/-- `ϑ = 999999999 / 10⁹` (p. 30). -/
def theta : ℚ := 999999999 / 10 ^ 9

/-- The matrix unit `E_{ab}` of the `16 × 25` cell grid, as a function of the entry `(i,j)`. -/
def matUnit (a b i j : ℕ) : ℚ :=
  if i = a ∧ j = b then 1 else 0

/-- The exact cell-mass perturbation (eq. (66), p. 30):
`δ = ϑ/10²¹ ∑_{g=1}^3 ∑_{i ∈ 𝓘_g} ∑_{j=1}^{23} N_{g,j} (E_{ij} + E_{0,24} - E_{i,24} - E_{0,j})`,
entry `δ_{ij}`, `0 ≤ i < 16`, `0 ≤ j < 25`. -/
def deltaCell (i j : ℕ) : ℚ :=
  theta / 10 ^ 21 * ∑ g ∈ Finset.Icc 1 3, ∑ i' ∈ rowGroup g, ∑ j' ∈ Finset.Icc 1 23,
    (tableN g j' : ℚ) * (matUnit i' j' i j + matUnit 0 24 i j - matUnit i' 24 i j - matUnit 0 j' i j)

/-- The cell width `Δ = 2/5` (p. 29). -/
noncomputable def cellWidth : ℝ := 2 / 5

/-- `x` lies in the cell `[k Δ, (k+1) Δ)` (the row cells `I_i` and the column cells `J_j`, p. 29). -/
def inCell (k : ℕ) (x : ℝ) : Prop :=
  (k : ℝ) * cellWidth ≤ x ∧ x < ((k : ℝ) + 1) * cellWidth

/-- `ω_j = e^{-jΔ} - e^{-(j+1)Δ}` (p. 30). -/
noncomputable def omega (j : ℕ) : ℝ :=
  Real.exp (-((j : ℝ) * cellWidth)) - Real.exp (-(((j : ℝ) + 1) * cellWidth))

/-- `w_{ij} = δ_{ij} / (Δ ω_j)` (p. 30). -/
noncomputable def wCell (i j : ℕ) : ℝ :=
  (deltaCell i j : ℝ) / (cellWidth * omega j)

/-- The baseline joint density in exponential coordinates (p. 29): `p0(a,r) = e^{-r} 1{a < r}`. -/
noncomputable def p0 (a r : ℝ) : ℝ := by
  classical
  exact Real.exp (-r) * (if a < r then 1 else 0)

/-- The perturbed density (eq. (67), p. 30):
`p1(a,r) = e^{-r} [1{a < r} + ∑_{i=0}^{15} ∑_{j=0}^{24} w_{ij} 1{a ∈ I_i} 1{r ∈ J_j}]`. -/
noncomputable def p1 (a r : ℝ) : ℝ := by
  classical
  exact Real.exp (-r) * ((if a < r then 1 else 0) +
    ∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 25,
      wCell i j * (if inCell i a then 1 else 0) * (if inCell j r then 1 else 0))

/-- The kernel `K1` (eq. (68), p. 30), written `K1 t u`: for `t, u ∈ [0,1)`,
`K1(t_r, u_a) = e^a ∫_0^r p1(a,v) dv` with `a = -log(1-u)` (so `u = u_a`) and `r = r(t)` (so
`t = t_r`); `K1(1,u) = 1` for `u < 1`; `K1(t,1) = t`. Outside `[0,1]²` it is `0` (unused). -/
noncomputable def K1 (t u : ℝ) : ℝ := by
  classical
  exact if t ∈ Icc (0 : ℝ) 1 ∧ u ∈ Icc (0 : ℝ) 1 then
      (if u = 1 then t
       else if t = 1 then 1
       else Real.exp (-Real.log (1 - u)) * ∫ v in (0 : ℝ)..rOfT t, p1 (-Real.log (1 - u)) v)
    else 0

/-- The certified ratio (eq. (69), p. 30): `Γ1 = 74500001 / 100000000 = 0.74500001`. -/
noncomputable def Gamma1 : ℝ := 74500001 / 100000000

end OrderSelProphet.Kernel


