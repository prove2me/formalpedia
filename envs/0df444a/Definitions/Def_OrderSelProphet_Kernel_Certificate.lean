-- Prove2me | Definitions.Def_OrderSelProphet_Kernel_Certificate
-- name    : OrderSelProphet_Kernel_Certificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:58:40.493066+00:00
-- url     : https://prove2.me/theorems/d6bb5430-2bcd-45b2-a5af-828a1da3e32a
-- title:
--   App. F: $D,Y,\sigma,k,R$, load (92), block masses (95), boxes $\Lambda(\mathcal R)$ (99), $\mathcal D_{\mathcal R}(r)$ (104), $V_\lambda$, $\Xi$ (108), $T_0$, and the constants (87), (131)
-- statement:
--   For a profile $\lambda$ (all at $\Gamma_1$, kernel $K_1$):
--   - $D(r)=D_{\Gamma_1}(r)$ (89); $Y(r)=y_{K_1,\lambda}(t_r)$, $\sigma(r)=S_{K_1,\lambda}(t_r)$ (90); $k(r)=e^r\frac{d}{dr}B(t_r)$ with $B=B_{K_1,\lambda}$, $R(r)=e^r(1-Y(r))$ (91).
--   - **Auxiliary load** (92): $\bar\ell_\lambda=\ell_{\Gamma_1}(K_1,\lambda)+\Gamma_1Y(0)\in[0,\infty]$.
--   - Blocks $(b_0,\dots,b_4)=(0,\tfrac25,2,\tfrac{16}5,\tfrac{32}5)$, $L_g=b_{g+1}-b_g$, $M_g=\int_{b_g}^{b_{g+1}}\lambda(u_a)da$, mass vector $x(\lambda)=(M_g/L_g)_{g=0}^3$ (94)–(95).
--   - A box $\mathcal R=\prod_g[\underline x_g,\overline x_g]$ with $0\le\underline x_g\le\overline x_g\le1$, and $\lambda\in\Lambda(\mathcal R)$ iff $x(\lambda)\in\mathcal R$ (99).
--   - $w_g(r)=e^r(p_1(a,r)-p_0(a,r))$ for $a\in[b_g,b_{g+1})$ (read at $a=b_g$); $\nu(r;x)=\sum_gw_g(r)L_gx_g$.
--   - $\underline M_{<p}=\sum_{g<p}L_g\underline x_g$, $\overline M_{<p}=\sum_{g<p}L_g\overline x_g$ (100); $h^-_{\mathcal R}(r)=\max\{\underline M_{<p},\underline M_{<p+1}+r-b_{p+1}\}$, $h^+_{\mathcal R}(r)=\min\{\overline M_{<p+1},\overline M_{<p}+r-b_p\}$ for $b_p\le r<b_{p+1}$, and $\underline M_{<4}$, $\overline M_{<4}+r-b_4$ for $r\ge b_4$ (102)–(103); $\mathcal D_{\mathcal R}(r)=\{(x,h):x\in\mathcal R,\ h^-_{\mathcal R}(r)\le h\le h^+_{\mathcal R}(r),\ 0\le h+\nu(r;x)\le r\}$ (104).
--   - $V_\lambda(a)=\int_a^\infty\frac{\sigma(r)}{\sigma(a)}\frac{(r-k(r))R(r)}{D(r)^2}dr$ (§F.5.1).
--   - $\chi(r)=r-h(r)$; $\rho_\lambda(x)=\inf\{a\ge0:1-e^{-\chi(a)}>x\}$ ($\inf\emptyset=\infty$), $\rho_\lambda(1)=\infty$; $\rho^*(r)=\rho_\lambda(Y(r))$; $\Xi(r)=e^r\int_r^{\rho^*(r)}(1-\lambda(u_a))e^{-a}da$, $\Xi_+=\max(\Xi,0)$ (108).
--   - $T_0(r)=\int_r^{10}v/D(v)^2dv$ (§F.5.3); `IsGridBilinear P r0 r1 h0 h1`: $P$ equals a bilinear polynomial on every closed cell of a finite grid covering $[r_0,r_1]\times[h_0,h_1]$.
--   - $U_{\rm cert}=999999999886/10^{12}$ (87), $U_{\max}=9007199253707871/9007199254740992$ (131).
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Appendix F, pp. 47–57: eqs. (87), (89)–(92), (94)–(104), (108), §F.5, (131)

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_K1

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-! # The objects of the certificate for (K1, Γ1)

Peng and Tang (2026), arXiv:2610.34892, Appendix F, pp. 47–57: the auxiliary load (92), the
exponential-coordinate quantities (89)–(91), the block masses (94)–(95), parameter boxes (99),
the state enclosures (101)–(104), the continuation integral (§F.5.1), the inverse correction
(108), `T0` (§F.5.3), and the constants `Ucert` (87) and `Umax` (131). Throughout, `lam` is a
profile. -/

/-- `D(r) = D_{Γ1}(r) = c_{Γ1} e^r + 1 + r` (eq. (89), p. 49). -/
noncomputable def Dc (r : ℝ) : ℝ :=
  DG Gamma1 r

/-- `Y(r) = y_{K1,λ}(t_r)` (eq. (90), p. 49). -/
noncomputable def Yc (lam : ℝ → ℝ) (r : ℝ) : ℝ :=
  yK K1 lam (tR r)

/-- `σ(r) = S_{K1,λ}(t_r)`, the survival factor at `Γ1` (eq. (90), p. 49). -/
noncomputable def sigmaC (lam : ℝ → ℝ) (r : ℝ) : ℝ :=
  SK Gamma1 K1 lam (tR r)

/-- The rescaled allocation rate (eq. (91), p. 50): `k(r) = e^r d/dr B(t_r)` with
`B = B_{K1,λ}` (defined for almost every `r > 0`; equal to `r B'(t_r)` there). -/
noncomputable def kRate (lam : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.exp r * deriv (fun s => allocK K1 lam (tR s)) r

/-- The rescaled threshold complement (eq. (91), p. 50): `R(r) = e^r (1 - Y(r))`. -/
noncomputable def Rc (lam : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.exp r * (1 - Yc lam r)

/-- The auxiliary load (eq. (92), p. 50): `ℓ̄_λ = ℓ_{Γ1}(K1, λ) + Γ1 Y(0)`. -/
noncomputable def auxLoad (lam : ℝ → ℝ) : ℝ≥0∞ :=
  loadK Gamma1 K1 lam + ENNReal.ofReal (Gamma1 * Yc lam 0)

/-- The block endpoints `(b0, b1, b2, b3, b4) = (0, 2/5, 2, 16/5, 32/5)` (eq. (94), p. 50). -/
noncomputable def blockEnd (p : ℕ) : ℝ :=
  match p with
    | 0 => 0
    | 1 => 2 / 5
    | 2 => 2
    | 3 => 16 / 5
    | _ => 32 / 5

/-- The block lengths `L_g = b_{g+1} - b_g` (eq. (95), p. 50). -/
noncomputable def blockLen (g : Fin 4) : ℝ :=
  blockEnd ((g : ℕ) + 1) - blockEnd (g : ℕ)

/-- The block mass `M_g = ∫_{b_g}^{b_{g+1}} λ(u_a) da` (eq. (95), p. 50). -/
noncomputable def blockMass (lam : ℝ → ℝ) (g : Fin 4) : ℝ :=
  ∫ a in blockEnd (g : ℕ)..blockEnd ((g : ℕ) + 1), lam (uA a)

/-- The mass vector `x(λ) = (M_g / L_g)_{g = 0..3} ∈ [0,1]⁴` (eq. (95), p. 50). -/
noncomputable def massVec (lam : ℝ → ℝ) (g : Fin 4) : ℝ :=
  blockMass lam g / blockLen g

/-- A closed parameter box `R = ∏_g [x̲_g, x̄_g]` (eq. (99), p. 51). -/
structure ParamBox where
  /-- lower corners `x̲_g` -/
  lo : Fin 4 → ℝ
  /-- upper corners `x̄_g` -/
  hi : Fin 4 → ℝ

/-- The box condition `0 ≤ x̲_g ≤ x̄_g ≤ 1` (eq. (99), p. 51). -/
def ParamBox.Valid (R : ParamBox) : Prop :=
  ∀ g, 0 ≤ R.lo g ∧ R.lo g ≤ R.hi g ∧ R.hi g ≤ 1

/-- `λ ∈ Λ(R)`: the mass vector of `λ` lies in the box (p. 51). -/
def InRegion (R : ParamBox) (lam : ℝ → ℝ) : Prop :=
  ∀ g, R.lo g ≤ massVec lam g ∧ massVec lam g ≤ R.hi g

/-- The correction coefficient of block `g` (p. 50): the common value `w_g(r)` of
`e^r (p1(a,r) - p0(a,r))` for `b_g ≤ a < b_{g+1}`, read at `a = b_g`. -/
noncomputable def wBlock (g : Fin 4) (r : ℝ) : ℝ :=
  Real.exp r * (p1 (blockEnd (g : ℕ)) r - p0 (blockEnd (g : ℕ)) r)

/-- The rate correction at a mass vector (eq. (98) and p. 51): `ν(r; x) = ∑_g w_g(r) L_g x_g`. -/
noncomputable def nuR (r : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ g, wBlock g r * blockLen g * x g

/-- The lower cumulative block-mass bound `M̲_{<p} = ∑_{g<p} L_g x̲_g` (eq. (100), p. 51). -/
noncomputable def massBelowLo (R : ParamBox) (p : ℕ) : ℝ :=
  ∑ g : Fin 4, if (g : ℕ) < p then blockLen g * R.lo g else 0

/-- The upper cumulative block-mass bound `M̄_{<p} = ∑_{g<p} L_g x̄_g` (eq. (100), p. 51). -/
noncomputable def massBelowHi (R : ParamBox) (p : ℕ) : ℝ :=
  ∑ g : Fin 4, if (g : ℕ) < p then blockLen g * R.hi g else 0

/-- The block `p` with `b_p ≤ r < b_{p+1}`, for `r < b_4` (`0` for `r < 0`, unused). -/
noncomputable def blockOf (r : ℝ) : ℕ := by
  classical
  exact if r < 2 / 5 then 0 else if r < 2 then 1 else if r < 16 / 5 then 2 else 3

/-- The lower state enclosure `h⁻_R(r)` (eq. (102) and (103), p. 51):
`max{M̲_{<p}, M̲_{<p+1} + r - b_{p+1}}` for `b_p ≤ r < b_{p+1}`, and `M̲_{<4}` for `r ≥ b_4`. -/
noncomputable def hLow (R : ParamBox) (r : ℝ) : ℝ := by
  classical
  exact if r < blockEnd 4 then
      max (massBelowLo R (blockOf r))
        (massBelowLo R (blockOf r + 1) + r - blockEnd (blockOf r + 1))
    else massBelowLo R 4

/-- The upper state enclosure `h⁺_R(r)` (eq. (102) and (103), p. 51):
`min{M̄_{<p+1}, M̄_{<p} + r - b_p}` for `b_p ≤ r < b_{p+1}`, and `M̄_{<4} + r - b_4` for
`r ≥ b_4`. -/
noncomputable def hHigh (R : ParamBox) (r : ℝ) : ℝ := by
  classical
  exact if r < blockEnd 4 then
      min (massBelowHi R (blockOf r + 1)) (massBelowHi R (blockOf r) + r - blockEnd (blockOf r))
    else massBelowHi R 4 + r - blockEnd 4

/-- The admissible set `D_R(r)` (eq. (104), p. 51): `(x, h)` with `x ∈ R`,
`h⁻_R(r) ≤ h ≤ h⁺_R(r)` and `0 ≤ h + ν(r; x) ≤ r`. -/
def Admissible (R : ParamBox) (r : ℝ) (x : Fin 4 → ℝ) (h : ℝ) : Prop :=
  (∀ g, R.lo g ≤ x g ∧ x g ≤ R.hi g) ∧ hLow R r ≤ h ∧ h ≤ hHigh R r ∧
    0 ≤ h + nuR r x ∧ h + nuR r x ≤ r

/-- The continuation integral of a profile (§F.5.1, p. 53):
`V_λ(a) = ∫_a^∞ σ(r)/σ(a) · (r - k(r)) R(r) / D(r)² dr`. -/
noncomputable def contV (lam : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ r in Ioi a, sigmaC lam r / sigmaC lam a * ((r - kRate lam r) * Rc lam r / Dc r ^ 2)

/-- The gap `χ(r) = r - h(r)` (§F.4, p. 52). -/
noncomputable def chiC (lam : ℝ → ℝ) (r : ℝ) : ℝ :=
  r - hExp lam r

/-- The generalized inverse of the loss-score map (§F.4, p. 52):
`ρ_λ(x) = inf {a ≥ 0 : 1 - e^{-χ(a)} > x}` for `0 ≤ x < 1` (with `inf ∅ = ∞`), and
`ρ_λ(1) = ∞`; values in `[0, ∞]`. -/
noncomputable def rhoInv (lam : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ := by
  classical
  exact if x < 1 then sInf {a : ℝ≥0∞ | a ≠ ⊤ ∧ x < 1 - Real.exp (-chiC lam a.toReal)} else ⊤

/-- The inverse coordinate `ρ*(r) = ρ_λ(Y(r))` (§F.4, p. 52). -/
noncomputable def rhoStar (lam : ℝ → ℝ) (r : ℝ) : ℝ≥0∞ :=
  rhoInv lam (Yc lam r)

/-- The inverse correction (eq. (108), p. 52): `Ξ(r) = e^r ∫_r^{ρ*(r)} (1 - λ(u_a)) e^{-a} da`
(an oriented integral; `∫_r^∞` when `ρ*(r) = ∞`). -/
noncomputable def XiC (lam : ℝ → ℝ) (r : ℝ) : ℝ := by
  classical
  exact Real.exp r *
    (if rhoStar lam r = ⊤ then ∫ a in Ioi r, (1 - lam (uA a)) * Real.exp (-a)
     else ∫ a in r..(rhoStar lam r).toReal, (1 - lam (uA a)) * Real.exp (-a))

/-- `Ξ₊(r) = max{Ξ(r), 0}` (p. 52). -/
noncomputable def XiPlus (lam : ℝ → ℝ) (r : ℝ) : ℝ :=
  max (XiC lam r) 0

/-- The i.i.d. continuation (§F.5.3, p. 55): `T0(r) = ∫_r^{10} v / D(v)² dv`. -/
noncomputable def T0 (r : ℝ) : ℝ :=
  ∫ v in r..10, v / Dc v ^ 2

/-- A function `P(r, h)` is **continuous piecewise bilinear on a finite grid** covering
`[r0, r1] × [h0, h1]` (§F.5.3, p. 55): there are strictly increasing finite grids `rg`, `hg`
whose ranges contain `[r0, r1]` and `[h0, h1]`, and on every closed grid cell `P` equals a
bilinear polynomial `c₀ + c₁ r + c₂ h + c₃ r h` (continuity on the grid follows). -/
def IsGridBilinear (P : ℝ → ℝ → ℝ) (r0 r1 h0 h1 : ℝ) : Prop :=
  ∃ (rg hg : List ℝ) (hr : rg ≠ []) (hh : hg ≠ []),
    rg.Pairwise (· < ·) ∧ hg.Pairwise (· < ·) ∧
    rg.head hr ≤ r0 ∧ r1 ≤ rg.getLast hr ∧ hg.head hh ≤ h0 ∧ h1 ≤ hg.getLast hh ∧
    ∀ (k m : ℕ) (hk : k + 1 < rg.length) (hm : m + 1 < hg.length),
      ∃ c : Fin 4 → ℝ, ∀ r ∈ Icc (rg[k]'(by omega)) (rg[k + 1]'hk),
        ∀ h ∈ Icc (hg[m]'(by omega)) (hg[m + 1]'hm), P r h = c 0 + c 1 * r + c 2 * h + c 3 * r * h

/-- `Ucert = 999999999886 / 10¹²` (eq. (87), p. 47). -/
noncomputable def Ucert : ℝ := 999999999886 / 10 ^ 12

/-- `Umax = 9007199253707871 / 9007199254740992` (eq. (131), p. 57). -/
noncomputable def Umax : ℝ := 9007199253707871 / 9007199254740992

end OrderSelProphet.Kernel


