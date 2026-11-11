-- Prove2me | Definitions.Def_RSBeyondJohnson_FirstOrder_Params
-- name    : RSBeyondJohnson_FirstOrder_Params
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:30:59.801203+00:00
-- url     : https://prove2.me/theorems/864044cf-3218-445e-aa94-95b2a01beee7
-- title:
--   Local rank $R_{\mathrm{loc}}$ (20) and the explicit parameters $m, B_\partial, B_{\mathrm{jet}}, B_Z$ above the curve (26)–(28)
-- statement:
--   For integers $m\ge1$, $B_\partial\ge0$ the **local rank bound** is
--   $$R_{\mathrm{loc}}(m,B_\partial)=\sum_{s=0}^{m-1}\Big[(s+1)(B_\partial+1)-(2s-m+1)_+(s+B_\partial-m+1)_+\Big],$$
--   and $N_{\mathrm{jet}}(t)=\min\{t,B_\partial\}+1$.
--
--   Given $0<\rho<a<1$ with $a>a_1(\rho)$ and $n\ge 2/\rho$, the paper fixes, depending only on $(\rho,a,n)$: $\rho_n=\rho-1/n$; $a_{\mathrm{cert}}=\min\{a,(1+a_1(\rho))/2\}$; $\lambda_\partial=(a_1(\rho)-\sqrt{\rho/2})/\rho$ if $\rho<\rho_c$ and $\lambda_\partial=3(1-a_{\mathrm{cert}})/(2(2-\rho))$ if $\rho\ge\rho_c$; the densities
--   $$\mathrm{Coef}(r,a,\lambda)=\frac{\lambda a^2}{2r}-\frac{a\lambda^2}{2}+\frac{r\lambda^3}{6},\qquad \mathrm{Rank}(\lambda)=\begin{cases}\lambda/2-\lambda^2/2+\lambda^3/3,&\lambda\le 1/2,\\ \lambda/4+1/24,&\lambda\ge1/2;\end{cases}$$
--   $\mathrm{Margin}_{\mathrm{int}}=\mathrm{Coef}-\mathrm{Rank}$, $\mathrm{Margin}^{(n)}_{\mathrm{int}}=\mathrm{Margin}_{\mathrm{int}}(\rho_n,a_{\mathrm{cert}},\lambda_\partial)$, $C_{\mathrm{rank}}=2\lambda_\partial+3$, and
--   $$m=\Big\lceil\frac{4C_{\mathrm{rank}}}{\mathrm{Margin}^{(n)}_{\mathrm{int}}}\Big\rceil,\ B_\partial=\lfloor\lambda_\partial m\rfloor,\ B_{\mathrm{jet}}=\lceil m a_{\mathrm{cert}}/\rho_n\rceil,\ \nu_{\mathrm{coef}}=\sum_{t=0}^{B_{\mathrm{jet}}}(\min\{t,B_\partial\}+1)(m a_{\mathrm{cert}}-\rho_n t)_+,$$
--   $$B_Z=\max\Big\{1,\Big\lfloor\frac{R_{\mathrm{loc}}(m,B_\partial)B_{\mathrm{jet}}}{\nu_{\mathrm{coef}}-R_{\mathrm{loc}}(m,B_\partial)}\Big\rfloor\Big\}.$$
--   These are the degree bounds of the interpolating polynomial: $B_\partial$ in $Y_1$, $B_{\mathrm{jet}}$ in $(Y_0,Y_1)$ jointly, $B_Z$ in the challenge.
--
--   **Formalization Note.** $R_{\mathrm{loc}}$ is computed in $\mathbb Z$; $(x)_+=\max\{0,x\}$. $m,B_\partial,B_{\mathrm{jet}},B_Z$ are natural numbers given by `Nat.ceil`/`Nat.floor` of the printed real expressions; Lemma 3.16 shows the denominators are positive in the stated range, so no default value of division is ever used there.
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 21, (20)–(21); p. 23, (26)–(28)

import Mathlib
import Definitions.Def_RSBeyondJohnson_FirstOrder_Curve

open Finset

namespace RSBeyondJohnson.FirstOrder

/-!
# The local rank `R_loc` (20) and the explicit parameters above the first-order curve (26)–(28)

Dao, Kominers, Thaler, *Reed–Solomon Codes Beyond Johnson*, STOC 2027 submission (manuscript of
November 2, 2026), §3.4, p. 21, (20)–(21), and §3.5, p. 23, (26)–(28).

All choices depend only on `(ρ, a, n)`. They are meaningful for `0 < ρ < a < 1`, `a > a₁(ρ)`,
`n ≥ 2/ρ` (Lemma 3.16 proves that `Margin^(n)_int`, the denominator of `m`, and
`ν_coef − R_loc`, the denominator of `B_Z`, are then positive). The positive part `(x)_+` is
`max 0 x`. `m`, `B∂`, `B_jet`, `B_Z` are natural numbers obtained by `Nat.ceil`/`Nat.floor` of
the printed real expressions, which are nonnegative in that range.
-/

/-- `R_loc(m, B∂) = ∑_{s=0}^{m−1} [(s + 1)(B∂ + 1) − (2s − m + 1)_+ (s + B∂ − m + 1)_+]`
((20), p. 21), computed in `ℤ`. -/
def rLoc (m Bd : ℕ) : ℤ :=
  ∑ s ∈ range m, (((s : ℤ) + 1) * ((Bd : ℤ) + 1) -
    max 0 (2 * (s : ℤ) - m + 1) * max 0 ((s : ℤ) + Bd - m + 1))

/-- `N_jet(t) = min{t, B∂} + 1` ((21), p. 21): the number of monomials `Y₀^a Y₁^b` with
`a + b = t` and `b ≤ B∂`. -/
def nJet (Bd t : ℕ) : ℕ := min t Bd + 1

/-- `Coef(r, a, λ) = λ a²/(2r) − a λ²/2 + r λ³/6` ((26), p. 23; the closed form of
`∫₀^∞ min{u, λ}(a − r u)_+ du`, valid for `0 < λ < a/r`). -/
noncomputable def coefDensity (r a lam : ℝ) : ℝ :=
  lam * a ^ 2 / (2 * r) - a * lam ^ 2 / 2 + r * lam ^ 3 / 6

/-- `Rank(λ) = λ/2 − λ²/2 + λ³/3` for `λ ≤ 1/2` and `λ/4 + 1/24` for `λ ≥ 1/2` ((26), p. 23;
the two formulas agree at `λ = 1/2`). -/
noncomputable def rankDensity (lam : ℝ) : ℝ :=
  if lam ≤ 1 / 2 then lam / 2 - lam ^ 2 / 2 + lam ^ 3 / 3 else lam / 4 + 1 / 24

/-- `Margin_int(r, a, λ) := Coef(r, a, λ) − Rank(λ)` (p. 23). -/
noncomputable def marginInt (r a lam : ℝ) : ℝ := coefDensity r a lam - rankDensity lam

/-- `ρ_n = ρ − 1/n` (p. 23). -/
noncomputable def rhoN (ρ : ℝ) (n : ℕ) : ℝ := ρ - 1 / (n : ℝ)

/-- The clipped agreement fraction `a_cert = min{a, (1 + a₁(ρ))/2}` (p. 23). -/
noncomputable def aCert (ρ a : ℝ) : ℝ := min a ((1 + a1 ρ) / 2)

/-- `λ∂ = (a₁(ρ) − √(ρ/2))/ρ` for `0 < ρ < ρ_c` and `3(1 − a_cert)/(2(2 − ρ))` for
`ρ_c ≤ ρ < 1` (p. 23). -/
noncomputable def lamD (ρ a : ℝ) : ℝ :=
  if ρ < rhoC then (a1 ρ - Real.sqrt (ρ / 2)) / ρ else 3 * (1 - aCert ρ a) / (2 * (2 - ρ))

/-- `Margin^(n)_int = Margin_int(ρ_n, a_cert, λ∂)` ((27), p. 23). -/
noncomputable def marginN (ρ a : ℝ) (n : ℕ) : ℝ := marginInt (rhoN ρ n) (aCert ρ a) (lamD ρ a)

/-- `C_rank = 2λ∂ + 3` ((28), p. 23). -/
noncomputable def cRank (ρ a : ℝ) : ℝ := 2 * lamD ρ a + 3

/-- `m = ⌈4 C_rank / Margin^(n)_int⌉` ((28)). -/
noncomputable def mParam (ρ a : ℝ) (n : ℕ) : ℕ := ⌈4 * cRank ρ a / marginN ρ a n⌉₊

/-- `B∂ = ⌊λ∂ m⌋` ((28)): the bound on the exponent of `Y₁`. -/
noncomputable def bDel (ρ a : ℝ) (n : ℕ) : ℕ := ⌊lamD ρ a * (mParam ρ a n : ℝ)⌋₊

/-- `B_jet = ⌈m a_cert / ρ_n⌉` ((28)): the bound on the total degree in `(Y₀, Y₁)`. -/
noncomputable def bJet (ρ a : ℝ) (n : ℕ) : ℕ := ⌈(mParam ρ a n : ℝ) * aCert ρ a / rhoN ρ n⌉₊

/-- `ν_coef = ∑_{t=0}^{B_jet} (min{t, B∂} + 1)(m a_cert − ρ_n t)_+` ((28)). -/
noncomputable def nuCoef (ρ a : ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ range (bJet ρ a n + 1), ((min t (bDel ρ a n) : ℕ) + 1 : ℝ) *
    max 0 ((mParam ρ a n : ℝ) * aCert ρ a - rhoN ρ n * (t : ℝ))

/-- `B_Z = max{1, ⌊R_loc(m, B∂) B_jet / (ν_coef − R_loc(m, B∂))⌋}` ((28)): the bound on the
degree in the challenge `Z`. -/
noncomputable def bZ (ρ a : ℝ) (n : ℕ) : ℕ :=
  max 1 ⌊((rLoc (mParam ρ a n) (bDel ρ a n) : ℤ) : ℝ) * (bJet ρ a n : ℝ) /
    (nuCoef ρ a n - ((rLoc (mParam ρ a n) (bDel ρ a n) : ℤ) : ℝ))⌋₊

end RSBeyondJohnson.FirstOrder


