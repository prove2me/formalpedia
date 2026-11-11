-- Prove2me | Definitions.Def_ImprovedSteinerForest_Main_Certificate
-- name    : ImprovedSteinerForest_Main_Certificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:26:46.268198+00:00
-- url     : https://prove2.me/theorems/79bf73d5-b0ac-4448-a2f9-1322690d002c
-- title:
--   The exact rational certificate of §8 and Appendix F: parameters, score functions of Appendix D, θ_v of (B.7), the 72 weights and the expanded coefficients
-- statement:
--   The data of the final weighted sum (§8, Appendix F). Parameters: $g=1943/1000$, $\varepsilon=6005367/10^8$, $\eta=10^{-6}$ (§3.3), $b=2611195029/10^{10}$, $\underline a=2798113337/10^{10}$, $\overline a=2798113338/10^{10}$ (8.2), $r^*=4857374427850411096559/2500000000000000000000$, $\overline{\lambda}_c=b^2/2-\underline a+b$, and the saving profile with $a$ replaced by $\underline a$:
--   $$\underline\omega(n)=d_1(4-n)_++d_2\bigl[(8-n)_+-3(4-n)_+\bigr],\quad d_1=\underline a-b,\ d_2=\underline a-b-b^2/4.$$
--
--   - $\theta_1=1$, $\theta_2=2/3$, $\theta_3=3/5$, $\theta_v=\min_{2\le r\le v}\max\{\rho_r,\ v/(2^{v-r}(3r-2)-1)\}$ for $v\ge4$ (B.7), with $\rho_r=\frac{2d-1}{d^2+d-1}+\frac{(d-1)^2}{(d+1)(d^2+d-1)^2}$, $d=2r-2$ (B.5).
--   - For a menu $(u,v)$ and a reference rule $D\in\{M,H,S_{d_0}\}$: the functions $\ell_f,\ell_p$ (Lemma D.3), $\ell_0$ (D.2), $\lambda(n,j)$ (D.1), $\ell_s$ (D.4), $\ell_S$ (D.5); the good-block scores $\zeta^M$ (p. 57), $\zeta^H$ (D.3), $\zeta^S$ (D.6); the bad-block bounds $\beta_1^M,\beta_1^H$ (D.7) and $\beta_1^S$ (D.8); $\lambda_D$ and $\beta_1(\infty)$ (Lemma 7.2); and the remainder $\beta(n)$ with charge $\kappa$, (7.1) for $n<162$ and (7.2) for $n\ge 162$.
--   - The weights: budget, size, growth, rounding and pair rows $w_b,w_s,w_g,w_r,w_p$ and the 67 menu rows $(D_i,u_i,v_i,\kappa_i,\omega_i)$ of Appendix F.2, each numerator divided by $10^{14}$; $\nu=w_p+\sum_i\omega_i$.
--   - The expanded coefficients of Appendix F.1: $c_e,c_z,c_h$, the good-block coefficients $c^G_{n,j}$ (F.1), the bad-block coefficients $c^B_n$ (F.2), and the right-hand coefficient $2(1+\varepsilon)(w_g+w_r)+\eta w_r+g\nu-2\varepsilon w_b+4w_s$.
--
--   **Formalization Note.** All quantities are real numbers; sizes $n$, $j$, ranks $r$ and menu parameters are natural numbers, and every difference such as $2r+2-n-k$ is taken in $\mathbb R$. `maxIcc lo hi f` is the maximum of `f` over the integers of `[lo, hi]` and `0` on an empty range; it is used only where the range is nonempty or `0` is itself a term of the maximum ((D.7) "omitting empty ranges"). The supremum in (7.1) is `sSup` of the image of $[2,\infty)$; it is finite since every charge in the table is at least one. $\lambda(n,j)$ is evaluated with $d=n-2j$ as an integer.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Improved Steiner Forest Approximation via Cut Spaces, STOC 2027 submission (manuscript sha256 b2bf022d…0444), p. 18, §3.3; p. 32, Eq. (6.5); pp. 37, Eqs. (7.1)–(7.2) and Lemma 7.2; p. 39, §8.1 and Eq. (8.2); p. 51, Eq. (B.5); p. 54, Eq. (B.7); pp. 57–62, App. D, Eqs. (D.1)–(D.8); pp. 64–67, App. F

import Mathlib
set_option autoImplicit false

namespace ImprovedSteinerForest.Main

namespace Certificate

/-- `(x)₊ = max(x, 0)` (p. 13). -/
noncomputable def pos (x : ℝ) : ℝ := max x 0

open scoped Classical in
/-- `max_{lo ≤ r ≤ hi} f(r)` over the integers of `[lo, hi]`; `0` for an empty range (only used
where the range is nonempty or `0` is itself a term of the maximum). -/
noncomputable def maxIcc (lo hi : ℕ) (f : ℕ → ℝ) : ℝ :=
  if h : (Finset.Icc lo hi).Nonempty then (Finset.Icc lo hi).sup' h f else 0

/-- The algorithm's growth-ratio parameter `g = 1943/1000` (§3.3, p. 18). -/
noncomputable def g : ℝ := 1943 / 1000
/-- The budget earning rate `ε = 6005367/10⁸` (§3.3, p. 18). -/
noncomputable def ε : ℝ := 6005367 / 10 ^ 8
/-- The rounding accuracy `η = 10⁻⁶` (§3.3, p. 18). -/
noncomputable def η : ℝ := 1 / 10 ^ 6
/-- The analysis gain parameter `b = 2611195029/10¹⁰` (§8.1, p. 39). -/
noncomputable def b : ℝ := 2611195029 / 10 ^ 10
/-- Lower end `a̲ = 2798113337/10¹⁰` of the logarithm interval (8.2), p. 39. -/
noncomputable def aLo : ℝ := 2798113337 / 10 ^ 10
/-- Upper end `ā = 2798113338/10¹⁰` of the logarithm interval (8.2), p. 39. -/
noncomputable def aHi : ℝ := 2798113338 / 10 ^ 10
/-- `r* = 4857374427850411096559/2500000000000000000000` (Theorem 1.1, (8.1)). -/
noncomputable def rStar : ℝ := 4857374427850411096559 / 2500000000000000000000

/-- `λ̄_c = b²/2 − a̲ + b` (§8.1, p. 39). -/
noncomputable def lamcBar : ℝ := b ^ 2 / 2 - aLo + b

/-- The saving profile `ω̲(n) = d₁(4 − n)₊ + d₂[(8 − n)₊ − 3(4 − n)₊]` of (6.5) with `a` replaced
by `a̲`: `d₁ = a̲ − b`, `d₂ = a̲ − b − b²/4` ((4.2), §8.1). -/
noncomputable def omegaLo (n : ℕ) : ℝ :=
  (aLo - b) * pos (4 - n) + (aLo - b - b ^ 2 / 4) * (pos (8 - n) - 3 * pos (4 - n))

/-- The hit probability `ρ_r` of (B.5), p. 51, with `d = 2r − 2`:
`ρ_r = (2d − 1)/(d² + d − 1) + (d − 1)²/((d + 1)(d² + d − 1)²)`. -/
noncomputable def rho (r : ℕ) : ℝ :=
  let d : ℝ := 2 * r - 2
  (2 * d - 1) / (d ^ 2 + d - 1) + (d - 1) ^ 2 / ((d + 1) * (d ^ 2 + d - 1) ^ 2)

/-- The coefficients `θ_v` of Theorem 5.2 and (B.7), p. 54: `θ₁ = 1`, `θ₂ = 2/3`, `θ₃ = 3/5`, and
`θ_v = min_{2 ≤ r ≤ v} max{ρ_r, v/(2^{v−r}(3r − 2) − 1)}` for `v ≥ 4`. -/
noncomputable def theta (v : ℕ) : ℝ :=
  if _h1 : v ≤ 1 then 1 else if _h2 : v = 2 then 2 / 3 else if _h3 : v = 3 then 3 / 5 else
    (Finset.Icc 2 v).inf' ⟨2, by simp; omega⟩
      (fun r => max (rho r) ((v : ℝ) / (2 ^ (v - r) * (3 * (r : ℝ) - 2) - 1)))

/-- The reference rules of §7.1 (p. 36): `M` merges later moats, `H` retains an earlier phase with
bounded rank, `S d₀` bounds the rank at the base with parameter `d₀`. -/
inductive Rule
  | M
  | H
  | S (d0 : ℕ)

/-- `ℓ_f(n, k) = max_{1 ≤ r ≤ min(v, n−1)} {min(n, 2r) − g(2r + 2 − n − k)₊}` (Lemma D.3, p. 57). -/
noncomputable def ellF (v n k : ℕ) : ℝ :=
  maxIcc 1 (min v (n - 1)) (fun r => min (n : ℝ) (2 * r) - g * pos (2 * r + 2 - n - k))

/-- `ℓ_p(n, k)` (Lemma D.3, p. 57): `n − g(n − k)` for `n ≤ v + 1`, else
`min(n, 2v) − g(2v + 2 − n − k)₊`. -/
noncomputable def ellP (v n k : ℕ) : ℝ :=
  if n ≤ v + 1 then (n : ℝ) - g * ((n : ℝ) - k)
  else min (n : ℝ) (2 * v) - g * pos (2 * v + 2 - n - k)

/-- `ℓ₀(n, k)` of (D.2), p. 59: `2 − g(2 − k)` at `n = 2`, `3 − g(1 − k)` at `n = 3`,
`min(n, 2v)` for `n ≥ 4`. -/
noncomputable def ell0 (v n k : ℕ) : ℝ :=
  if n = 2 then 2 - g * (2 - k) else if n = 3 then 3 - g * (1 - k) else min (n : ℝ) (2 * v)

/-- `λ(n, j)` of (D.1), p. 58, with `d = n − 2j`: `2 − 2g` if `d = 0`, `min(n, 2d)` if `d > 0` is
even, `min(n, 2d + 1 − g)` if `d` is odd. -/
noncomputable def lam (n j : ℕ) : ℝ :=
  let d : ℤ := (n : ℤ) - 2 * j
  if d = 0 then 2 - 2 * g
  else if d % 2 = 0 then min (n : ℝ) (2 * d) else min (n : ℝ) (2 * d + 1 - g)

/-- `ℓ_s(n, k) = max_{1 ≤ r ≤ min(v, n−1)} {min(n, 2r) − g(4r − 4d₀ − n − k)₊}` (D.4), p. 60. -/
noncomputable def ellS (v d0 n k : ℕ) : ℝ :=
  maxIcc 1 (min v (n - 1)) (fun r => min (n : ℝ) (2 * r) - g * pos (4 * r - 4 * d0 - n - k))

/-- `ℓ_S(n, k)` of (D.5), p. 60: `ℓ₀(n, k)` for `n = 2, 3`; for `4 ≤ n < 2v + 2` the maximum of
`ℓ_f(n, k)`, `ℓ_s(n, k)`, `ℓ_S(n − 1, k)` and, when `n ≤ 2v`,
`min{n, 2v, λ(n, max(1, n − v)) + gk}`; `2v` for `n ≥ 2v + 2`. -/
noncomputable def ellBigS (v d0 : ℕ) : ℕ → ℕ → ℝ
  | n, k =>
    if _h : n ≤ 3 then ell0 v n k
    else if 2 * v + 2 ≤ n then 2 * v
    else
      let base := max (max (ellF v n k) (ellS v d0 n k)) (ellBigS v d0 (n - 1) k)
      if n ≤ 2 * v then
        max base (min (min (n : ℝ) (2 * v)) (lam n (max 1 (n - v)) + g * k))
      else base
  termination_by n => n
  decreasing_by omega

/-- The good-block score `ζ^M(n, j)` of rule `M` with menu `(u, v)` (p. 57). -/
noncomputable def zetaM (u v n j : ℕ) : ℝ :=
  if j ≤ u ∧ n - j ≤ v then g - 1
  else if j ≤ u then g * pos (2 * v + 2 - n) / n - min 1 (2 * v / (n : ℝ))
  else - ellF v n 0 / n

/-- The good-block score `ζ(n, j)` of a reference rule with menu `(u, v)`: `ζ^M` (p. 57), `ζ^H`
(D.3), p. 59, and `ζ^S` (D.6), p. 61. -/
noncomputable def zeta : Rule → ℕ → ℕ → ℕ → ℕ → ℝ
  | .M, u, v, n, j => zetaM u v n j
  | .H, u, v, n, j =>
    if j ≤ u then zetaM u v n j
    else if n - j ≤ v then - max 0 (lam n j) / n
    else - min 1 (2 * v / (n : ℝ))
  | .S d0, u, v, n, j =>
    if j ≤ u ∧ n - j ≤ v then g - 1
    else if n - j ≤ v ∧ (n : ℤ) - 2 * j ≤ d0 then - max 0 (lam n j) / n
    else - (1 / (n : ℝ)) *
      (if n - j ≤ v then max (max (ellF v n 0) (ellS v d0 n 0)) (lam n j)
       else max (ellF v n 0) (ellS v d0 n 0))

/-- The bad-block bound `β₁(n)` for `h_B = 1`: `β₁^M` (D.7), `β₁^H` (D.7 with `ℓ_f` replaced by
`ℓ₀` for references whose bases are still in the future), p. 61, and `β₁^S` (D.8), p. 62. -/
noncomputable def beta1 : Rule → ℕ → ℕ → ℝ
  | .M, v, n =>
    max (max (max 0 (ellF v n 0)) (if 3 ≤ n then ellF v (n - 1) 1 else 0))
      (max (maxIcc 2 (min (2 * v + 1) (n - 2)) (fun a => ellP v a 0 + ellF v (n - a) 0))
           (maxIcc 2 (min (2 * v + 1) (n - 1)) (fun a => ellP v a 1 + ellF v (n + 1 - a) 1)))
  | .H, v, n =>
    max (max (max 0 (ell0 v n 0)) (if 3 ≤ n then ell0 v (n - 1) 1 else 0))
      (max (maxIcc 2 (min (2 * v + 1) (n - 2)) (fun a => ellP v a 0 + ell0 v (n - a) 0))
           (maxIcc 2 (min (2 * v + 1) (n - 1)) (fun a => ellP v a 1 + ell0 v (n + 1 - a) 1)))
  | .S d0, v, n =>
    if n ≤ 2 then 0 else max (max 0 (ellBigS v d0 n 0)) (2 - g + ellBigS v d0 (n - 1) 1)

/-- `λ_D` of Lemma 7.2 (p. 37): `2v` for `M`, `H`; `2` for `S d₀`. -/
noncomputable def lamD : Rule → ℕ → ℝ
  | .M, v => 2 * v
  | .H, v => 2 * v
  | .S _, _ => 2

/-- The constant tail `β₁(∞)` of Lemma 7.2 (p. 37): `4v` for `M`, `H`; `2v + 2 − g` for `S d₀`. -/
noncomputable def beta1Inf : Rule → ℕ → ℝ
  | .M, v => 4 * v
  | .H, v => 4 * v
  | .S _, v => 2 * v + 2 - g

/-- The common bad-block remainder `β(n)` with charge `κ` ((7.1)–(7.2), p. 37): for `n < 162`,
`max{β₁(n) − κ, sup_{s ≥ 2} (min(n + s, λ_D s + 2v) − κ s)}` (supremum over real `s ≥ 2`); for
`n ≥ 162`, `max{β₁(∞) − κ, 2λ_D + 2v − 2κ}` if `κ ≥ λ_D`, else
`((λ_D − κ)n + 2v(κ − 1))/(λ_D − 1)`. -/
noncomputable def beta (D : Rule) (v : ℕ) (κ : ℝ) (n : ℕ) : ℝ :=
  if n < 162 then
    max (beta1 D v n - κ)
      (sSup ((fun s : ℝ => min ((n : ℝ) + s) (lamD D v * s + 2 * v) - κ * s) '' Set.Ici 2))
  else if lamD D v ≤ κ then max (beta1Inf D v - κ) (2 * lamD D v + 2 * v - 2 * κ)
  else ((lamD D v - κ) * n + 2 * v * (κ - 1)) / (lamD D v - 1)

/-- A menu row of the certificate (Appendix F.2, pp. 66–67): reference rule, menu `(u, v)`, charge
`κ` and integer numerator of its weight (the weight is numerator/10¹⁴). -/
structure MenuRow where
  rule : Rule
  u : ℕ
  v : ℕ
  κ : ℚ
  num : ℕ

/-- The 67 menu rows with positive weight (Appendix F.2, pp. 66–67), in the printed order. -/
def menuRows : List MenuRow := [
  ⟨(.S 0), 2, 3, 2443/500, 3257149833165⟩,
  ⟨.M, 2, 4, 6, 779592687948⟩,
  ⟨(.S 0), 2, 4, 2443/500, 737007490120⟩,
  ⟨(.S 1), 2, 4, 2443/500, 259864229316⟩,
  ⟨(.S 2), 2, 5, 2443/500, 459645259587⟩,
  ⟨(.S 0), 3, 5, 2443/500, 1264108183923⟩,
  ⟨.M, 4, 6, 12, 794077884077⟩,
  ⟨(.S 1), 4, 6, 2443/500, 210136120854⟩,
  ⟨(.S 2), 2, 7, 2443/500, 116693004759⟩,
  ⟨(.S 2), 3, 7, 2443/500, 576712256713⟩,
  ⟨(.S 2), 4, 7, 2443/500, 330128386124⟩,
  ⟨.M, 5, 7, 14, 459343356407⟩,
  ⟨(.S 2), 4, 8, 2443/500, 214010527648⟩,
  ⟨.M, 6, 8, 4, 638769180115⟩,
  ⟨(.S 2), 3, 9, 2443/500, 13131545615⟩,
  ⟨(.S 3), 4, 9, 2443/500, 297950451440⟩,
  ⟨(.S 2), 5, 9, 2443/500, 557030319422⟩,
  ⟨(.S 4), 4, 10, 2443/500, 173221577138⟩,
  ⟨(.S 2), 6, 10, 2443/500, 563960188063⟩,
  ⟨.M, 7, 11, 4, 513618217482⟩,
  ⟨(.S 4), 6, 12, 2443/500, 268417529059⟩,
  ⟨.M, 8, 12, 4, 217192821512⟩,
  ⟨(.S 4), 5, 13, 2443/500, 122850247901⟩,
  ⟨(.S 4), 6, 13, 2443/500, 160224903884⟩,
  ⟨(.S 4), 7, 13, 2443/500, 271714158417⟩,
  ⟨.M, 8, 14, 28, 530935087600⟩,
  ⟨.H, 7, 15, 2, 35227127437⟩,
  ⟨.H, 7, 16, 2, 73750760262⟩,
  ⟨.H, 8, 16, 2, 65239992505⟩,
  ⟨.M, 9, 16, 4, 254915460028⟩,
  ⟨.M, 9, 17, 4, 207761217565⟩,
  ⟨.H, 7, 18, 36, 158105554446⟩,
  ⟨.H, 8, 18, 2, 121158925331⟩,
  ⟨.H, 8, 19, 2, 51631032087⟩,
  ⟨.M, 9, 19, 8, 286356768640⟩,
  ⟨.H, 8, 21, 42, 60483358316⟩,
  ⟨.H, 9, 21, 2, 46918576955⟩,
  ⟨.M, 10, 21, 4, 146894733624⟩,
  ⟨.M, 10, 22, 8, 108626696489⟩,
  ⟨.H, 8, 23, 2, 107449657571⟩,
  ⟨.H, 9, 23, 2, 115291532830⟩,
  ⟨.M, 10, 24, 8, 151239860661⟩,
  ⟨.M, 10, 26, 4, 152196274512⟩,
  ⟨.M, 10, 28, 8, 127543865742⟩,
  ⟨.H, 9, 30, 2, 57481177530⟩,
  ⟨.M, 10, 30, 8, 592712934885⟩,
  ⟨.M, 10, 31, 31, 220187046243⟩,
  ⟨.M, 11, 31, 4, 344580054669⟩,
  ⟨.H, 9, 32, 8, 304648792852⟩,
  ⟨.M, 11, 32, 4, 68696355310⟩,
  ⟨.M, 11, 33, 4, 588710342347⟩,
  ⟨(.S 33), 9, 34, 4, 455387100910⟩,
  ⟨.M, 11, 34, 4, 301788607039⟩,
  ⟨.M, 12, 34, 4, 49789989582⟩,
  ⟨.M, 12, 36, 4, 598543369416⟩,
  ⟨(.S 36), 4, 37, 4, 835134200434⟩,
  ⟨.H, 5, 37, 2, 1465227438494⟩,
  ⟨(.S 36), 6, 37, 4, 1332897560938⟩,
  ⟨.H, 7, 37, 4, 1438836675954⟩,
  ⟨.H, 8, 37, 2, 747894487712⟩,
  ⟨.H, 8, 37, 74, 379120643391⟩,
  ⟨.H, 9, 37, 8, 295446998191⟩,
  ⟨.M, 12, 37, 111/2, 404840074282⟩,
  ⟨(.S 37), 2, 38, 4, 1160876167981⟩,
  ⟨(.S 37), 3, 38, 4, 716982805488⟩,
  ⟨(.S 37), 4, 38, 4, 139721768312⟩,
  ⟨.M, 13, 39, 4, 36110016658⟩]

/-- Weight of the budget row (8.8), F.2. -/
noncomputable def wb : ℝ := 97657180068683 / 10 ^ 14
/-- Weight of the size row (8.9), F.2. -/
noncomputable def ws : ℝ := 10000 / 10 ^ 14
/-- Weight of the growth row (8.5), F.2. -/
noncomputable def wg : ℝ := 4175683 / 10 ^ 14
/-- Weight of the rounding row (8.4), F.2. -/
noncomputable def wr : ℝ := 66198579034854 / 10 ^ 14
/-- Weight of the pair row (8.6), F.2. -/
noncomputable def wp : ℝ := 5207525337555 / 10 ^ 14

/-- Weight `ω_i` of a menu row. -/
noncomputable def MenuRow.w (i : MenuRow) : ℝ := (i.num : ℝ) / 10 ^ 14

/-- Total weight of the purchase rows `ν = w_p + Σ_i ω_i` (F.1, p. 65). -/
noncomputable def nu : ℝ := wp + (menuRows.map MenuRow.w).sum

/-- Coefficient of `e` in the weighted sum (F.1, p. 65). -/
noncomputable def cE : ℝ :=
  ws - (1 + 2 * ε) * wb + 2 * (1 + ε) * wg + (2 * (1 + ε) - aHi - η) * wr - wp
    - (menuRows.map (fun i => i.w / (i.u : ℝ))).sum

/-- Coefficient of `z` in the weighted sum (F.1, p. 65). -/
noncomputable def cZ : ℝ :=
  ws + wb - (aHi + η + lamcBar) * wr - (g + 1) * wp
    - (menuRows.map (fun i => (g + 1 / (i.u : ℝ)) * i.w)).sum

/-- Coefficient of `h` in the weighted sum (F.1, p. 65). -/
noncomputable def cH : ℝ :=
  ws + (aHi + η + lamcBar) * wr + (2 - g) * wp
    + (menuRows.map (fun i => (g * theta i.v - ((i.κ : ℝ) - 2) / (i.u : ℝ)) * i.w)).sum

/-- Coefficient `c^G_{n,j}` of the good-block count `x_{n,j}` (F.1), p. 65. -/
noncomputable def cG (n j : ℕ) : ℝ :=
  ws - 2 * ε * wb + (-aHi - η + b * (2 - 2 / (n : ℝ)) + omegaLo n / n) * wr
    + ((if n = 2 then g else 0) + (if n = 3 then g / 3 else 0) - 2 / (n : ℝ)) * wp
    + (menuRows.map (fun i => i.w / (i.u : ℝ) * zeta i.rule i.u i.v n j)).sum

/-- Coefficient `c^B_n` of the bad-block count `x̄_n` (F.2), p. 65. -/
noncomputable def cB (n : ℕ) : ℝ :=
  ws - 2 * ε * wb + (-aHi - η + b * (2 - 2 / (n : ℝ))) * wr
    + ((if n = 2 then g - 1 else 0) + (if n = 3 then 4 * (g - 1) / 3 else 0)
        + (if 4 ≤ n then (3 * g - 4) / n else 0)) * wp
    - (menuRows.map (fun i => i.w * beta i.rule i.v (i.κ : ℝ) n / ((i.u : ℝ) * n))).sum

/-- Coefficient of `opt` on the right-hand side of the weighted sum (F.1, p. 65):
`2(1 + ε)(w_g + w_r) + ηw_r + gν − 2εw_b + 4w_s`. -/
noncomputable def rhsCoeff : ℝ := 2 * (1 + ε) * (wg + wr) + η * wr + g * nu - 2 * ε * wb + 4 * ws

end Certificate

end ImprovedSteinerForest.Main


