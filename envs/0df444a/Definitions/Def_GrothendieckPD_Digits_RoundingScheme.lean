-- Prove2me | Definitions.Def_GrothendieckPD_Digits_RoundingScheme
-- name    : GrothendieckPD_Digits_RoundingScheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:53.540264+00:00
-- url     : https://prove2.me/theorems/a25e195e-3df8-43fb-8108-524d29bd40bb
-- title:
--   §4.2: the explicit 32-function rounding scheme $\mu=\sum_i\lambda_i\delta_{(f_i,g_i)}$ and its coefficients $c_m$
-- statement:
--   All data are exact and are taken from §4.2, Table 1 (p. 15) and the table on p. 48.
--
--   1. **Correlated graded Gaussians (4.2).** For the odd polynomial $P_i(t)=\sum_{m\ge1}p_mt^m$ of row $i$ of Table 1 (with $\sum_m|p_m|\le1$),
--   $$W=\sum_{m}\sqrt{|p_m|}\,X^{(m)}_1+\sqrt{1-\textstyle\sum_m|p_m|}\,X_2,\qquad W'=\sum_m\operatorname{sign}(p_m)\sqrt{|p_m|}\,X^{(m)}_1+\sqrt{1-\textstyle\sum_m|p_m|}\,X_3 .$$
--   2. **Graph threshold (4.5)–(4.6).** $F(w,x_4,x_5,x_6)=\operatorname{sign}\bigl(w+\sum_{j=4}^6r(x_j)\bigr)$ with $r(s)=-0.002608895910895478\psi_1(s)-0.0999107408341197\psi_3(s)-0.020910560460516325\psi_5(s)-0.005853637316670958\psi_7(s)+0.0057627068821593744\psi_9(s)+0.0013019893459673402\psi_{11}(s)-0.0019418422133255495\psi_{13}(s)+0.0006843699264111792\psi_{15}(s)$.
--   3. **Bivariate threshold.** $R(x,y)$ is the polynomial of Eq. (4.7). For $k=0,\dots,2047$, the real roots in $x$ of $R(x,(2k+1)/512)$ are listed in increasing order, rounded to the nearest multiple of $10^{-12}$, corrected by $\pm10^{-12}$ at the 34 positions $(k,a,\pm1)$ of p. 48, and relisted in increasing order as $r_{k,1},r_{k,2},\dots$. Then $F_*(x,y)=1+2\sum_{a:\,r_{k,a}\le x}(-1)^a$ for $k/256\le y<(k+1)/256$, $F_*(x,y)=-\operatorname{sign}(x)$ for $y\ge8$, and $F_*(x,y)=-F_*(-x,-y)$ for $y<0$.
--   4. **The pairs.** For $i=17,\dots,31$: $f_i=\operatorname{sign}W$, $g_i=\operatorname{sign}W'$. For $i=0,\dots,13,15,16$: $f_i=F(W,X_4,X_5,X_6)$, $g_i=F(W',-X_4,-X_5,-X_6)$. For $i=14$: $f_{14}=F_*(X^{(3)}_1,X^{(5)}_1)$, $g_{14}=F_*(-X^{(3)}_1,X^{(5)}_1)$.
--   5. **Coefficients.** $[t^m]H_i=c_m(f_i,g_i)$ on the graded space, and
--   $$c_m=c_m(\mu)=[t^m]H=\sum_{i=0}^{31}\lambda_i\,[t^m]H_i,$$
--   with the weights $\lambda_i$ of Table 1 (exact fractions, e.g. $\lambda_0=60643327718562175000/25000000000000000247431$).
--
--   This is the Krivine rounding scheme whose value certifies the upper bound $K_G<1.779893$ (Theorem 4.2).
--
--   **Formalization Note** $\operatorname{sign}(0)=1$, the convention of the proof of Lemma 3.3; it only matters on null sets. Rounding uses Mathlib's `round` (ties upward); the source states that rounding is unique. The weights satisfy $\sum_i\lambda_i=1$, $\lambda_i>0$, and $\sum_m|p_m|\le1$ for $i\ne14$ (Eq. 4.4), checked in exact arithmetic.
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, §4.2 pp. 12–14 (Eq. 4.2–4.7, definition of F_*, H_i, c_m), Table 1 p. 15, staircase corrections pp. 47–48

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_GradedSpace
open MeasureTheory ProbabilityTheory

namespace GrothendieckPD.Digits

/-- The sign function used by the rounding functions, with the convention `sign(0) = 1`
(the convention stated in the proof of Lemma 3.3, p. 8; the value at `0` only matters on a
null set). -/
noncomputable def sgn (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

/-- The weights `λ_i`, `i = 0, …, 31`, of Table 1 (p. 15), as exact fractions. -/
noncomputable def lam : ℕ → ℝ
  | 0 => 60643327718562175000 / 25000000000000000247431
  | 1 => 175365095292992000 / 25000000000000000247431
  | 2 => 4573126272489115 / 1219512195121951231582
  | 3 => 248005501245969575 / 25000000000000000247431
  | 4 => 1746960750902429000 / 25000000000000000247431
  | 5 => 3119884864162846250 / 25000000000000000247431
  | 6 => 1167759537924566000 / 25000000000000000247431
  | 7 => 10622692935124497500 / 25000000000000000247431
  | 8 => 4510989226396620750 / 25000000000000000247431
  | 9 => 225271185467334750 / 25000000000000000247431
  | 10 => 2590644248486109750 / 25000000000000000247431
  | 11 => 159466984575209675 / 25000000000000000247431
  | 12 => 1252554238454943650 / 25000000000000000247431
  | 13 => 349449731405024675 / 25000000000000000247431
  | 14 => 892199070421725000 / 25000000000000000247431
  | 15 => 18675444698504427500000 / 25000000000000000247431
  | 16 => 5572553297529536750000 / 25000000000000000247431
  | 17 => 661943041586152825000 / 25000000000000000247431
  | 18 => 166403349365097000 / 25000000000000000247431
  | 19 => 24994962065681940 / 25000000000000000247431
  | 20 => 9752885915637175 / 25000000000000000247431
  | 21 => 30936434154596385 / 25000000000000000247431
  | 22 => 27931141611749985 / 25000000000000000247431
  | 23 => 23042926715956245 / 50000000000000000494862
  | 24 => 120200964730604775 / 25000000000000000247431
  | 25 => 1360595407560664500 / 25000000000000000247431
  | 26 => 213458751479788850 / 25000000000000000247431
  | 27 => 8400770105211650 / 25000000000000000247431
  | 28 => 15098122612496557 / 50000000000000000494862
  | 29 => 63773334657951175 / 50000000000000000494862
  | 30 => 149703036787065950 / 25000000000000000247431
  | 31 => 97307307105401800 / 25000000000000000247431
  | _ => 0

/-- The coefficient `p_m` of `t^m` in the correlation polynomial `P_i` of Table 1 (p. 15), as an
exact fraction; zero at every other degree. Row 14 has no polynomial (all entries `0`). -/
noncomputable def pcoef : ℕ → ℕ → ℝ
  | 0, 1 => 946 / 1000
  | 0, 3 => -54 / 1000
  | 1, 3 => -1
  | 2, 1 => 5 / 100
  | 2, 3 => -95 / 100
  | 3, 1 => 7500000000000001 / 100000000000000001
  | 3, 3 => -92500000000000000 / 100000000000000001
  | 4, 1 => 1 / 10
  | 4, 3 => -9 / 10
  | 5, 1 => 2 / 10
  | 5, 3 => -8 / 10
  | 6, 1 => 225 / 1000
  | 6, 3 => -775 / 1000
  | 7, 1 => 35000000000000003 / 100000000000000000
  | 7, 3 => -6499999999999999 / 10000000000000000
  | 8, 1 => 2006830122278547 / 40000000000000000
  | 8, 3 => -7540766094444311 / 10000000000000000
  | 8, 5 => 4893815937465127 / 25000000000000000
  | 9, 1 => 1741176476977869 / 100000000000000013
  | 9, 3 => -92295288728215510 / 100000000000000013
  | 9, 5 => 5963534794806634 / 100000000000000013
  | 10, 1 => 3393956633363427 / 100000000000000000
  | 10, 3 => -655490081870693 / 1000000000000000
  | 10, 5 => 3105703517956727 / 10000000000000000
  | 11, 1 => -36112846919679523 / 10000000000000000103
  | 11, 3 => -9881992863232164000 / 10000000000000000103
  | 11, 5 => -81894289848156580 / 10000000000000000103
  | 12, 1 => 4901570661097 / 5000000000000000
  | 12, 3 => -5234190673248801 / 10000000000000000
  | 12, 5 => 951201237085801 / 2000000000000000
  | 13, 1 => 280336034129396 / 312500000000000021
  | 13, 3 => -140417768196820875 / 312500000000000021
  | 13, 5 => 171801895769049750 / 312500000000000021
  | 15, 1 => 45146000000000005 / 50000000000000002
  | 15, 3 => -4853999999999997 / 50000000000000002
  | 16, 1 => 22573500000000000 / 25000000000000001
  | 16, 3 => -2426500000000001 / 25000000000000001
  | 17, 1 => 8859999999999999 / 10000000000000000
  | 17, 3 => -1140000000000001 / 10000000000000000
  | 18, 1 => 240000000000000000 / 250000000000000009
  | 18, 3 => -10000000000000009 / 250000000000000009
  | 19, 1 => 1 / 10
  | 19, 13 => -9 / 10
  | 20, 1 => 525 / 1000
  | 20, 13 => -475 / 1000
  | 21, 1 => 5499999999999999 / 10000000000000000
  | 21, 13 => -45000000000000007 / 100000000000000000
  | 22, 1 => 17500000000000000 / 25000000000000001
  | 22, 13 => -7500000000000001 / 25000000000000001
  | 23, 1 => 725 / 1000
  | 23, 13 => -275 / 1000
  | 24, 1 => 7999999999999999 / 10000000000000000
  | 24, 13 => -20000000000000007 / 100000000000000000
  | 25, 1 => 9249999999999999 / 10000000000000000
  | 25, 13 => -7500000000000007 / 100000000000000000
  | 26, 1 => 237500000000000000 / 250000000000000011
  | 26, 13 => -12500000000000011 / 250000000000000011
  | 27, 1 => 1 / 10
  | 27, 15 => 9 / 10
  | 28, 1 => 375 / 1000
  | 28, 15 => 625 / 1000
  | 29, 1 => 4 / 10
  | 29, 15 => 6 / 10
  | 30, 1 => 6749999999999999 / 10000000000000000
  | 30, 15 => 32500000000000007 / 100000000000000000
  | 31, 1 => 17500000000000000 / 25000000000000001
  | 31, 15 => 7500000000000001 / 25000000000000001
  | _, _ => 0

/-- The degrees that occur in Table 1: `1 ≤ m ≤ 15` (every `p_m` with `m > 15` is zero). -/
def tableDegrees : Finset ℕ := Finset.Icc 1 15

/-- The grade-`m` variable `X_1^{(m)}` (for `m ≥ 1`). -/
def gradeVar (m : ℕ) : GVar := (m.toPNat', 1)

/-- The grade-1 variable `X_j`. -/
def g1 (j : ℕ) : GVar := (1, j)

/-- `W_{P_i}(X) = ∑_{m≥1} √|p_m| X_1^{(m)} + √(1 - ∑_{m≥1} |p_m|) X_2` (Eq. 4.2, p. 12). -/
noncomputable def Wfun (i : ℕ) (x : GPoint) : ℝ :=
  ∑ m ∈ tableDegrees, Real.sqrt |pcoef i m| * x (gradeVar m) +
    Real.sqrt (1 - ∑ m ∈ tableDegrees, |pcoef i m|) * x (g1 2)

/-- `W'_{P_i}(X) = ∑_{m≥1} sign(p_m) √|p_m| X_1^{(m)} + √(1 - ∑_{m≥1} |p_m|) X_3` (Eq. 4.2). -/
noncomputable def Wfun' (i : ℕ) (x : GPoint) : ℝ :=
  ∑ m ∈ tableDegrees, sgn (pcoef i m) * Real.sqrt |pcoef i m| * x (gradeVar m) +
    Real.sqrt (1 - ∑ m ∈ tableDegrees, |pcoef i m|) * x (g1 3)

/-- `r(s)` of Eq. (4.6), p. 12. -/
noncomputable def rfun (s : ℝ) : ℝ :=
  -0.002608895910895478 * psi 1 s - 0.0999107408341197 * psi 3 s
  - 0.020910560460516325 * psi 5 s - 0.005853637316670958 * psi 7 s
  + 0.0057627068821593744 * psi 9 s + 0.0013019893459673402 * psi 11 s
  - 0.0019418422133255495 * psi 13 s + 0.0006843699264111792 * psi 15 s

/-- `F(w, x₄, x₅, x₆) = sign(w + ∑_{j=4}^{6} r(x_j))` (Eq. 4.5, p. 12). -/
noncomputable def Fgraph (w x4 x5 x6 : ℝ) : ℝ :=
  sgn (w + (rfun x4 + rfun x5 + rfun x6))

/-- `ψ_k` as a real polynomial: `He_k / √(k!)`. -/
noncomputable def psiPoly (k : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / Real.sqrt (k.factorial : ℝ)) *
    (Polynomial.hermite k).map (Int.castRingHom ℝ)

/-- `R(·, y)` of Eq. (4.7), p. 13, as a polynomial in `x` for fixed `y`. -/
noncomputable def Rpoly (y : ℝ) : Polynomial ℝ :=
  Polynomial.C (-0.072399902677 * psi 1 y + 0.073767456734 * psi 3 y)
  + Polynomial.C (-0.71483345535) * psiPoly 1
  + Polynomial.C (0.008648628127 * psi 2 y) * psiPoly 1
  + Polynomial.C (0.043678832526 * psi 1 y) * psiPoly 2
  + Polynomial.C (-0.004614640469 * psi 3 y) * psiPoly 2
  + Polynomial.C 0.036990218101 * psiPoly 3
  + Polynomial.C (0.001978721807 * psi 2 y) * psiPoly 3
  + Polynomial.C (0.036193792294 * psi 1 y) * psiPoly 4
  + Polynomial.C 0.131004390897 * psiPoly 5
  + Polynomial.C (-0.011093407361) * psiPoly 7

/-- `R(x, y)` of Eq. (4.7). -/
noncomputable def Rfun (x y : ℝ) : ℝ := (Rpoly y).eval x

/-- The 34 corrections `(k, a, ±1)` of the table on p. 48: add (`+1`) or subtract (`-1`)
`10^{-12}` to the `a`-th rounded root (`a` counted from 1) for strip `k`. -/
def staircaseCorrections : List (ℕ × ℕ × ℤ) :=
  [(44, 1, -1), (64, 5, 1), (181, 5, -1), (286, 1, -1), (305, 5, 1), (342, 1, 1),
   (369, 1, -1), (402, 2, -1), (449, 1, -1),
   (487, 1, -1), (619, 5, -1), (626, 1, -1), (669, 1, 1), (684, 4, 1), (715, 3, 1),
   (739, 1, -1), (862, 5, 1), (902, 5, 1),
   (948, 5, 1), (984, 2, 1), (1019, 1, -1), (1019, 5, -1), (1030, 2, 1), (1053, 2, 1),
   (1055, 1, -1), (1113, 1, -1), (1125, 1, -1),
   (1261, 3, 1), (1281, 3, 1), (1309, 2, -1), (1319, 2, -1), (1412, 1, 1), (1417, 2, -1),
   (1677, 1, 1)]

/-- The total correction (in units of `10^{-12}`) prescribed for the `a`-th root of strip `k`. -/
def correctionAt (k a : ℕ) : ℤ :=
  ((staircaseCorrections.filter fun c => c.1 = k ∧ c.2.1 = a).map fun c => c.2.2).sum

/-- The real roots in `x` of `R(x, (2k+1)/512)`, in increasing order, each rounded to the nearest
multiple of `10^{-12}` (p. 13; p. 47). -/
noncomputable def roundedRoots (k : ℕ) : List ℝ :=
  ((Rpoly ((2 * k + 1 : ℝ) / 512)).roots.sort (· ≤ ·)).map
    fun r => (round (r * 10 ^ 12) : ℝ) / 10 ^ 12

/-- The breakpoints `r_{k,1}, r_{k,2}, …` of strip `k`: the rounded roots after the corrections of
p. 48, listed in increasing order (p. 13, p. 47). -/
noncomputable def breakpoints (k : ℕ) : List ℝ :=
  (((roundedRoots k).mapIdx fun idx r => r + (correctionAt k (idx + 1) : ℝ) / 10 ^ 12 :
    List ℝ) : Multiset ℝ).sort (· ≤ ·)

/-- `1 + 2 ∑_{a : r_{k,a} ≤ x} (-1)^a` (the definition of `F_*` on strip `k`, p. 13). -/
noncomputable def stairValue (k : ℕ) (x : ℝ) : ℝ :=
  1 + 2 * ((breakpoints k).mapIdx fun idx r => if r ≤ x then (-1 : ℝ) ^ (idx + 1) else 0).sum

/-- `F_*` for `y ≥ 0`: the strip value for `k/256 ≤ y < (k+1)/256`, `0 ≤ k < 2048`, and
`-sign(x)` for `y ≥ 8` (p. 13). -/
noncomputable def FstarNonneg (x y : ℝ) : ℝ :=
  if 8 ≤ y then -sgn x else stairValue ⌊256 * y⌋₊ x

/-- The bivariate threshold `F_*(x, y)` of p. 13, with `F_*(x, y) = -F_*(-x, -y)` for `y < 0`. -/
noncomputable def Fstar (x y : ℝ) : ℝ :=
  if 0 ≤ y then FstarNonneg x y else -FstarNonneg (-x) (-y)

/-- The rounding function `f_i` of §4.2 (pp. 12–13): graded linear threshold for `i = 17, …, 31`,
graph threshold for `i = 0, …, 13, 15, 16`, bivariate threshold for `i = 14`. -/
noncomputable def roundF (i : ℕ) (x : GPoint) : ℝ :=
  if i = 14 then Fstar (x (gradeVar 3)) (x (gradeVar 5))
  else if 17 ≤ i then sgn (Wfun i x)
  else Fgraph (Wfun i x) (x (g1 4)) (x (g1 5)) (x (g1 6))

/-- The rounding function `g_i` of §4.2 (pp. 12–13). -/
noncomputable def roundG (i : ℕ) (x : GPoint) : ℝ :=
  if i = 14 then Fstar (-x (gradeVar 3)) (x (gradeVar 5))
  else if 17 ≤ i then sgn (Wfun' i x)
  else Fgraph (Wfun' i x) (-x (g1 4)) (-x (g1 5)) (-x (g1 6))

/-- `[t^m] H_i = c_m(f_i, g_i)`, the `m`-th coefficient of `H_i = H_{f_i, g_i}` (p. 14). -/
noncomputable def Hcoef (i m : ℕ) : ℝ :=
  gradedInner m (roundF i) (roundG i)

/-- `c_m = c_m(µ) = [t^m] H = ∑_{i=0}^{31} λ_i [t^m] H_i` for the mixture `µ = ∑_i λ_i δ_{(f_i, g_i)}`
(p. 14). -/
noncomputable def cMix (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range 32, lam i * Hcoef i m

end GrothendieckPD.Digits


