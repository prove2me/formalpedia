-- Prove2me | Definitions.Def_EThetaPoula_Risk_Constants
-- name    : EThetaPoula_Risk_Constants
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:58.690981+00:00
-- url     : https://prove2.me/theorems/fe488642-1a0c-4bef-b98b-f4c848eff184
-- title:
--   The explicit constants of Lim–Neufeld–Sabanis–Zhang: (36), (46)–(49), (57), (60), (62), (63), (85), (110), (129), (130), (136)
-- statement:
--   The numeric inputs and the whole tower of explicit constants of the convergence analysis of e-TH$\varepsilon$O POULA.
--
--   The inputs are the dimension $d$, the exponents $q,r,\rho,\bar r$, the inverse temperature $\beta$, the constants $L_G,K_G,L_F,K_F,a,b$ of Assumptions 2–4, the contraction parameter $\epsilon$ of (48), and the moments $E_s:=E[(1+|X_0|)^s]$, $E[(1+2|X_0|)^{\rho-1}]$, $|h(0)|$, $\int V_2\,d\pi_\beta$, the $(4r+2)$-th moment of $\pi_\beta$ and $E[|\theta_0|^{4(2r+1)}]$.
--
--   The tower defines, in order: $a_F,R_F,b_F,a_h,b_h,L_h,K_H,R,L_R$ (Remarks 4.1, 4.2); $\lambda_{p,\max}$, $\lambda_{\max}=\lambda_{4r+2,\max}$ (36) and $\hat\lambda_{\max}$ (41); $M_0,\kappa,c_0,\mathring c_0$ (85); $M_1,\bar\kappa,c_4,M_2,\bar c_0$ (110); $M_3,\tilde\kappa,c_6,M_4,\tilde c_0$ (129); $\kappa^\sharp_2$, $c^\sharp_0$, $\mathring c_p$ (Lemma 6.1); $M_V,c_{V,1},c_{V,2}$ (Lemma 6.3); $\dot c_0,\dot c_1,\bar\phi,\dot c,\hat c$ (46)–(49); $\bar C_{0,1},\bar C_{1,1}$ (130); $\bar C_0,\bar C_1$ (136); $\bar C_4,\bar C_5$ (57); $C_3,C_4,C_5$ (60); $C_6,C_7,C_8$ (62); $C_9$ (63). Every later constant of the paper is a function of these inputs, and none depends on the stepsize $\lambda$, the iteration $n$ or the parameter $\varepsilon$ of the algorithm.
--
--   **Formalization Note** The tower is a family of pure real functions on the record `Params`, so that the probability setting stays separate; `Model.params` instantiates it at the actual laws. Natural division $(p+1)/2$ is the ceiling in $\binom{p}{\lceil p/2\rceil}$ (the paper's §1 convention $\lfloor a\rfloor+1$ would not give the central coefficient that p.38 needs). When $E_{2p\rho}=\infty$ the paper's $\lambda_{p,\max}$ is $0$, and the Lean value is also $0$. The cases $p=1$ of $M_1,c_4,c_6$ are stated as printed, separately from the general formula.
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, (36) p.18; Remarks 4.1, 4.2, pp.16–17; (41) p.23; Lemma 6.3 p.23; (46)–(49) pp.24–25; (57), (60) p.26; (62), (63) p.27; (85) p.33; (110) p.36; (129) p.39; (130) p.40; (136) p.42

import Mathlib

open MeasureTheory

namespace EThetaPoula.Risk

/-- The function `v_p̄(ν) := (1 + ν²)^{p̄/2}`, `ν ≥ 0`, of Lim, Neufeld, Sabanis, Zhang,
arXiv:2210.13193v3, §6.1, p.23.

**Formalization Note.** The exponent `p̄/2` is real, so this is `Real.rpow`; the base is at least
`1`, so no junk value arises. -/
noncomputable def vFun (p : ℕ) (ν : ℝ) : ℝ := (1 + ν ^ 2) ^ ((p : ℝ) / 2)

/-- The numeric inputs of the explicit constants of Lim, Neufeld, Sabanis, Zhang,
arXiv:2210.13193v3: the data `d, q, r, ρ` of §2.1 and §4.1, p.16, the inverse temperature `β`, the
constants `L_G, K_G, L_F, K_F, r̄, a, b` of Assumptions 2–4, p.16, the contraction parameter `ϵ` of
(48), p.24, and the moments that the formulas read.

* `mom s` is `E_s := E[(1 + |X₀|)^s]`, for real `s`.
* `momTwo` is `E[(1 + 2|X₀|)^{ρ−1}]`, which enters `L_h` (Remark 4.1, p.16).
* `h0` is `|h(0)|`, which enters `C̄₁` of (136), p.42.
* `gibbsV2` is `∫ V₂ dπ_β`, which enters `C₄` of (60), p.26.
* `gibbsMom` is `c_{Z∞,4r+2}`, the `(4r+2)`-th moment of `π_β` (Lemma 6.8, p.27).
* `thetaMom` is `E[|θ₀|^{4(2r+1)}]`, which enters `C₇` of (62), p.27.

**Formalization Note.** This record keeps the tower below a family of pure real functions,
separate from the probability setting; `Model.params` instantiates it at the actual laws. -/
structure Params where
  /-- dimension of the parameter space -/
  d : ℕ
  /-- the exponent `q` of Assumption 2 -/
  q : ℝ
  /-- the exponent `r` of (7) and Assumption 3 -/
  r : ℕ
  /-- the exponent `ρ` of Assumptions 1–3 -/
  ρ : ℝ
  /-- the inverse temperature `β` -/
  β : ℝ
  /-- the constant `L_G` of Assumption 2 -/
  LG : ℝ
  /-- the constant `K_G` of Assumption 2 -/
  KG : ℝ
  /-- the constant `L_F` of Assumption 3 -/
  LF : ℝ
  /-- the constant `K_F` of Assumption 3 -/
  KF : ℝ
  /-- the exponent `r̄` of Assumption 4 -/
  rbar : ℝ
  /-- the constant `a` of Assumption 4(iii) -/
  a : ℝ
  /-- the constant `b` of Assumption 4(iii) -/
  b : ℝ
  /-- the contraction parameter `ϵ` of (48), not the `ε` of the algorithm -/
  eps : ℝ
  /-- `s ↦ E[(1 + |X₀|)^s]` -/
  mom : ℝ → ℝ
  /-- `E[(1 + 2|X₀|)^{ρ−1}]` -/
  momTwo : ℝ
  /-- `|h(0)|` -/
  h0 : ℝ
  /-- `∫ V₂ dπ_β` -/
  gibbsV2 : ℝ
  /-- `c_{Z∞,4r+2}` -/
  gibbsMom : ℝ
  /-- `E[|θ₀|^{4(2r+1)}]` -/
  thetaMom : ℝ

namespace Params

variable (P : Params)

/-! ### Remarks 4.1, 4.2, pp.16–17, and (36), p.18 -/

/-- `E_{2pρ} = E[(1 + |X₀|)^{2pρ}]`. -/
noncomputable def E2p (p : ℕ) : ℝ := P.mom (2 * p * P.ρ)

/-- `a_F := a/2`. -/
noncomputable def aF : ℝ := P.a / 2

/-- `R_F := max{(4b/a)^{1/(2r−r̄)}, 2^{1/(2r)}}`. -/
noncomputable def RF : ℝ :=
  max ((4 * P.b / P.a) ^ (1 / (2 * (P.r : ℝ) - P.rbar))) ((2 : ℝ) ^ (1 / (2 * (P.r : ℝ))))

/-- `b_F := (a/2 + b) R_F^{r̄+2} + d K_F² E[(1 + |X₀|)^{2ρ}]/(2a)`. -/
noncomputable def bF : ℝ :=
  (P.a / 2 + P.b) * P.RF ^ (P.rbar + 2) + P.d * P.KF ^ 2 * P.mom (2 * P.ρ) / (2 * P.a)

/-- `a_h := 2^q K_G E[(1 + |X₀|)^ρ]`. -/
noncomputable def ah : ℝ := (2 : ℝ) ^ P.q * P.KG * P.mom P.ρ

/-- `b_h := 3 (2^{q+1} K_G E[(1 + |X₀|)^ρ]/min{1, a_F})^{q+2} + b_F`. -/
noncomputable def bh : ℝ :=
  3 * ((2 : ℝ) ^ (P.q + 1) * P.KG * P.mom P.ρ / min 1 P.aF) ^ (P.q + 2) + P.bF

/-- `L_h := max{L_G + L_F E[(1 + 2|X₀|)^{ρ−1}], 1}`. -/
noncomputable def Lh : ℝ := max (P.LG + P.LF * P.momTwo) 1

/-- `K_H := 2^{2r} K_G + 3 √(2d) K_F`. -/
noncomputable def KH : ℝ := (2 : ℝ) ^ (2 * P.r) * P.KG + 3 * √(2 * (P.d : ℝ)) * P.KF

/-- `R := max{1, (3^{q−1} L_G/a)^{1/(2r−q+1)}, (2b/a)^{1/(2r−r̄)}}`. -/
noncomputable def R : ℝ :=
  max 1 (max (((3 : ℝ) ^ (P.q - 1) * P.LG / P.a) ^ (1 / (2 * (P.r : ℝ) - P.q + 1)))
    ((2 * P.b / P.a) ^ (1 / (2 * (P.r : ℝ) - P.rbar))))

/-- `L_R := L_h (1 + 2R)^{2r}`. -/
noncomputable def LR : ℝ := P.Lh * (1 + 2 * P.R) ^ (2 * P.r)

/-- `λ_{p,max}` of (36), p.18. When `E_{2pρ} = +∞` the paper's fraction is `0`, hence
`λ_{p,max} = 0`; in Lean `mom` is then the Bochner junk `0`, the fraction is `x/0 = 0`, and the
value is the same. -/
noncomputable def lamMaxP (p : ℕ) : ℝ :=
  min 1 (min (1 / P.aF) (min (1 / P.aF ^ 2)
    (min ((P.aF / P.KF) ^ 2) ((P.aF / P.KF) ^ (2 / (2 * (p : ℝ) - 1))) /
      (16 * P.KF ^ 2 * (p : ℝ) ^ 2 * (2 * (p : ℝ) - 1) ^ 2 * P.E2p p ^ 2))))

/-- `λ_max := λ_{4r+2,max}` of (36), p.18. -/
noncomputable def lamMax : ℝ := P.lamMaxP (4 * P.r + 2)

/-- `λ̂_max := min{1, 1/a_F, 1/a_F², a_F²/(16 K_F⁴ (E[(1 + |X₀|)^{2ρ}])²)}` of (41), p.23. -/
noncomputable def lamHat : ℝ :=
  min 1 (min (1 / P.aF) (min (1 / P.aF ^ 2)
    (P.aF ^ 2 / (16 * P.KF ^ 4 * P.mom (2 * P.ρ) ^ 2))))

/-! ### (85), p.33 -/

/-- `2^{2r+1} K_G + 10 + 8K_F + 3K_F²`, the bracket of (85). -/
noncomputable def W0 : ℝ := (2 : ℝ) ^ (2 * P.r + 1) * P.KG + 10 + 8 * P.KF + 3 * P.KF ^ 2

/-- `M₀ := 2d E[(1 + |X₀|)^{2ρ}](2^{2r+1} K_G + 10 + 8K_F + 3K_F²)/min{1, a_F}`. -/
noncomputable def M0 : ℝ := 2 * P.d * P.mom (2 * P.ρ) * P.W0 / min 1 P.aF

/-- `κ := M₀^{2r}/(2(1 + M₀^{2r}))`. -/
noncomputable def kappa : ℝ := P.M0 ^ (2 * P.r) / (2 * (1 + P.M0 ^ (2 * P.r)))

/-- `c₀` of (85). -/
noncomputable def c0 : ℝ :=
  2 * P.d / P.β
    + P.d * P.mom (2 * P.ρ) *
        (2 * P.bF + (2 : ℝ) ^ (2 * P.r + 1) * P.KG + 8 + 8 * P.KF + 6 * P.KF ^ 2)
    + P.aF * P.kappa * P.M0 ^ 2
    + P.d * P.mom (2 * P.ρ) * P.W0 * P.M0 ^ (2 * P.r + 1)

/-- `c̊₀ := c₀(1 + 1/(a_F κ))`, Lemma 6.1(i), p.23. -/
noncomputable def c0ring : ℝ := P.c0 * (1 + 1 / (P.aF * P.kappa))

/-! ### (110) and the two displays before it, p.36 -/

/-- `M₁(p)`: `M₁(1)` from the display before (106) and, for `p ≥ 2`, (110). -/
noncomputable def M1 (p : ℕ) : ℝ :=
  if p = 1 then
    2 * P.d * ((2 : ℝ) ^ (2 * P.r + 3) * P.KG * P.mom (2 * P.ρ) + 4 * P.bF + 6) / min 1 P.aF
      + 64 * P.d * (2 + P.KF) ^ 2 * P.mom (2 * P.ρ) / min 1 P.aF
  else
    (2 * p * P.d * ((2 : ℝ) ^ (2 * P.r + 3) * P.KG * P.mom (2 * P.ρ) + 4 * P.bF + 6)
      + (P.d : ℝ) ^ p * (Nat.choose (2 * p) p : ℝ) * (2 * (p : ℝ) - 1) * (2 : ℝ) ^ (4 * p + 1)
        * (2 + P.KF) ^ (2 * p) * P.E2p p) / min 1 P.aF

/-- `κ̄(p) := (M₁(p))^{2r}/(4(1 + (M₁(p))^{2r}))` of (110). -/
noncomputable def kappaBar (p : ℕ) : ℝ :=
  P.M1 p ^ (2 * P.r) / (4 * (1 + P.M1 p ^ (2 * P.r)))

/-- `c₄(p)`: `c₄(1)` from the display before (106) and, for `p ≥ 2`, (110). -/
noncomputable def c4 (p : ℕ) : ℝ :=
  if p = 1 then
    P.d * P.mom (2 * P.ρ) * (2 + 4 * P.bF + (2 : ℝ) ^ (2 * P.r + 2) * P.KG)
      + 32 * P.d * (2 + P.KF) ^ 2 * P.mom (2 * P.ρ)
      + 2 * P.aF * P.M1 1 ^ (2 * P.r + 2) / (4 * (1 + P.M1 1 ^ (2 * P.r)))
      + P.d * P.mom (2 * P.ρ) * ((2 : ℝ) ^ (2 * P.r + 3) * P.KG + 4 * P.bF + 6)
          * P.M1 1 ^ (2 * P.r + 1)
      + 32 * P.d * (2 + P.KF) ^ 2 * P.mom (2 * P.ρ) * P.M1 1 ^ (2 * P.r + 1)
  else
    p * P.d * P.mom (2 * P.ρ) * (2 + 4 * P.bF + (2 : ℝ) ^ (2 * P.r + 2) * P.KG)
      + 2 * P.aF * P.kappaBar p * P.M1 p ^ (2 * p)
      + p * P.d * P.mom (2 * P.ρ) * ((2 : ℝ) ^ (2 * P.r + 3) * P.KG + 4 * P.bF + 6)
          * P.M1 p ^ (2 * P.r + 2 * p - 1)
      + (P.d : ℝ) ^ p * (Nat.choose (2 * p) p : ℝ) * (2 * (p : ℝ) - 1) * (2 : ℝ) ^ (4 * p)
          * (2 + P.KF) ^ (2 * p) * P.E2p p * (1 + P.M1 p ^ (2 * P.r + 2 * p - 1))

/-- `M₂(p) := (2^{2p−2} p (2p−1) d β⁻¹/(a_F κ̄(p)))^{1/2}` of (110). -/
noncomputable def M2 (p : ℕ) : ℝ :=
  √((2 : ℝ) ^ (2 * p - 2) * p * (2 * (p : ℝ) - 1) * P.d * P.β⁻¹ / (P.aF * P.kappaBar p))

/-- `c̄₀(p)` of (110), for `p ≥ 2`. -/
noncomputable def c0Bar (p : ℕ) : ℝ :=
  P.c4 p
    + (2 : ℝ) ^ (2 * p - 2) * p * (2 * (p : ℝ) - 1) * P.d * P.β⁻¹
        * (P.M2 p ^ (2 * (p - 1)) + P.c4 (p - 1))
    + (2 : ℝ) ^ (2 * p - 4) * (2 * (p : ℝ) * (2 * (p : ℝ) - 1)) ^ (p + 1) * (P.d * P.β⁻¹) ^ p

/-! ### (129), p.39 -/

/-- `2^{2r+1} K_G + 2b_F + 10 + 8K_F + 6K_F²`, the bracket of (129). -/
noncomputable def W : ℝ :=
  (2 : ℝ) ^ (2 * P.r + 1) * P.KG + 2 * P.bF + 10 + 8 * P.KF + 6 * P.KF ^ 2

/-- The binomial coefficient `C(p, ⌈p/2⌉)` of (129), with the ordinary ceiling
`⌈p/2⌉ = (p + 1)/2` (natural division).

**Formalization Note.** §1, p.3 sets `⌈a⌉ := ⌊a⌋ + 1`. Page 38 uses `C(p, ⌈p/2⌉)` as an upper bound
of every `C(p, k)`, which needs the central coefficient, so here the ordinary ceiling is the
reading. The two agree for odd `p`. -/
def choosePHalf (p : ℕ) : ℕ := Nat.choose p ((p + 1) / 2)

/-- `M₃(p)` of (129); `M₃(1) = 64 d E[(1 + |X₀|)^{2ρ}] W/min{1, a_F}` is its value at `p = 1`. -/
noncomputable def M3 (p : ℕ) : ℝ :=
  (P.d : ℝ) ^ p * (choosePHalf p : ℝ) * p * (4 : ℝ) ^ (p + 2) * P.E2p p * P.W ^ p / min 1 P.aF

/-- `κ̃(p) := (M₃(p))^{2r}/(4(1 + (M₃(p))^{2r}))` of (129). -/
noncomputable def kappaTilde (p : ℕ) : ℝ :=
  P.M3 p ^ (2 * P.r) / (4 * (1 + P.M3 p ^ (2 * P.r)))

/-- `c₅(1) := 16d E_{2ρ}(2^{2r+1}K_G + 2b_F + 8 + 8K_F + 6K_F²)
+ 4d E_{2ρ}(2^{2r+1}K_G + 10 + 8K_F + 3K_F²)`, p.39. -/
noncomputable def c5One : ℝ :=
  16 * P.d * P.mom (2 * P.ρ) *
      ((2 : ℝ) ^ (2 * P.r + 1) * P.KG + 2 * P.bF + 8 + 8 * P.KF + 6 * P.KF ^ 2)
    + 4 * P.d * P.mom (2 * P.ρ) * P.W0

/-- `c₆(p)`: `c₆(1)` from the text after (123), p.39, and, for `p ≥ 2`, (129). -/
noncomputable def c6 (p : ℕ) : ℝ :=
  if p = 1 then
    P.c5One + 2 * P.aF * P.kappaTilde 1 * P.M3 1 ^ 2
      + 64 * P.d * P.mom (2 * P.ρ) * P.W * P.M3 1 ^ (2 * P.r + 1)
  else
    (P.d : ℝ) ^ p * (choosePHalf p : ℝ) * p * (4 : ℝ) ^ (p + 2) * P.E2p p * P.W ^ p
      + 2 * P.aF * P.kappaTilde p * P.M3 p ^ (2 * p)
      + (P.d : ℝ) ^ p * (choosePHalf p : ℝ) * p * (4 : ℝ) ^ (p + 2) * P.E2p p * P.W ^ p
          * P.M3 p ^ (2 * p + 2 * P.r * p - 1)

/-- `M₄(p) := (2^{2p−2} p (2p−1) d β⁻¹/(a_F κ̃(p)))^{1/2}` of (129). -/
noncomputable def M4 (p : ℕ) : ℝ :=
  √((2 : ℝ) ^ (2 * p - 2) * p * (2 * (p : ℝ) - 1) * P.d * P.β⁻¹ / (P.aF * P.kappaTilde p))

/-- `c̃₀(p)` of (129), for `p ≥ 2`. -/
noncomputable def c0Tilde (p : ℕ) : ℝ :=
  P.c6 p
    + (2 : ℝ) ^ (2 * p - 2) * p * (2 * (p : ℝ) - 1) * P.d * P.β⁻¹
        * (P.M4 p ^ (2 * p - 2) + P.c6 (p - 1))
    + (2 : ℝ) ^ (2 * p - 4) * (2 * (p : ℝ) * (2 * (p : ℝ) - 1)) ^ (p + 1) * (P.d * P.β⁻¹) ^ p

/-! ### Lemma 6.1, p.23 -/

/-- `κ♯₂ := min{κ̄(2), κ̃(2)}`. -/
noncomputable def kappaSharp : ℝ := min (P.kappaBar 2) (P.kappaTilde 2)

/-- `c♯₀(p) := max{c̄₀(p), c̃₀(p)}`. -/
noncomputable def c0Sharp (p : ℕ) : ℝ := max (P.c0Bar p) (P.c0Tilde p)

/-- `c̊_p := c♯₀(p)(1 + 1/(a_F κ♯₂))`, for `p ≥ 2`. -/
noncomputable def cRing (p : ℕ) : ℝ := P.c0Sharp p * (1 + 1 / (P.aF * P.kappaSharp))

/-! ### Lemma 6.3, p.23, and Proposition 6.5, pp.24–25 -/

/-- `M_V(p̄) := (1/3 + 4b_h/(3a_h) + 4d/(3a_hβ) + 4(p̄−2)/(3a_hβ))^{1/2}`. -/
noncomputable def MV (p : ℕ) : ℝ :=
  √(1 / 3 + 4 * P.bh / (3 * P.ah) + 4 * P.d / (3 * P.ah * P.β)
    + 4 * ((p : ℝ) - 2) / (3 * P.ah * P.β))

/-- `c_{V,1}(p̄) := a_h p̄/4`. -/
noncomputable def cV1 (p : ℕ) : ℝ := P.ah * p / 4

/-- `c_{V,2}(p̄) := (3/4) a_h p̄ v_p̄(M_V(p̄))`. -/
noncomputable def cV2 (p : ℕ) : ℝ := 3 / 4 * P.ah * p * vFun p (P.MV p)

/-- `ċ₀ := 2(4c_{V,2}(2)(1 + c_{V,1}(2))/c_{V,1}(2) − 1)^{1/2}`, after (48), p.24. -/
noncomputable def c0Dot : ℝ := 2 * √(4 * P.cV2 2 * (1 + P.cV1 2) / P.cV1 2 - 1)

/-- `ċ₁ := 2(2c_{V,2}(2)/c_{V,1}(2) − 1)^{1/2}`, after (48), p.24. -/
noncomputable def c1Dot : ℝ := 2 * √(2 * P.cV2 2 / P.cV1 2 - 1)

/-- `φ̄` of (47), p.24. -/
noncomputable def phiBar : ℝ :=
  (√(8 * Real.pi / (P.β * P.LR)) * P.c0Dot *
    Real.exp ((P.c0Dot * √(P.β * P.LR / 8) + √(8 / (P.β * P.LR))) ^ 2))⁻¹

/-- The second argument of the minimum in (48), p.24:
`(4c_{V,2}(2) √(2βπ/L_R) ∫₀^{ċ₁} exp((s√(βL_R/8) + √(8/(βL_R)))²) ds)⁻¹`. -/
noncomputable def epsBound : ℝ :=
  (4 * P.cV2 2 * √(2 * P.β * Real.pi / P.LR) *
    ∫ s in (0 : ℝ)..P.c1Dot, Real.exp ((s * √(P.β * P.LR / 8) + √(8 / (P.β * P.LR))) ^ 2))⁻¹

/-- `ϵ` satisfies (48), p.24: `0 < ϵ ≤ 1 ∧ (…)⁻¹`. -/
def EpsAdmissible : Prop := 0 < P.eps ∧ P.eps ≤ min 1 P.epsBound

/-- `ċ := min{φ̄, c_{V,1}(2), 4c_{V,2}(2) ϵ c_{V,1}(2)}/2` of (46), p.24. -/
noncomputable def cDot : ℝ := min P.phiBar (min (P.cV1 2) (4 * P.cV2 2 * P.eps * P.cV1 2)) / 2

/-- `ĉ := 2(1 + ċ₀) exp(βL_R ċ₀²/8 + 2ċ₀)/ϵ` of (49), p.25. -/
noncomputable def cHat : ℝ :=
  2 * (1 + P.c0Dot) * Real.exp (P.β * P.LR * P.c0Dot ^ 2 / 8 + 2 * P.c0Dot) / P.eps

/-! ### (130), p.40, and (136), p.42 -/

/-- `C̄_{0,1} := 2^{8r+6} d⁴ (1 + K_F + K_G)⁴ E[(1 + |X₀|)^{4ρ}]` of (130). -/
noncomputable def C01 : ℝ :=
  (2 : ℝ) ^ (8 * P.r + 6) * (P.d : ℝ) ^ 4 * (1 + P.KF + P.KG) ^ 4 * P.mom (4 * P.ρ)

/-- `C̄_{1,1}` of (130). -/
noncomputable def C11 : ℝ :=
  (2 : ℝ) ^ (8 * P.r + 6) * (P.d : ℝ) ^ 4 * (1 + P.KF + P.KG) ^ 4 * P.mom (4 * P.ρ)
      * (1 + P.cRing (4 * P.r + 2))
    + 32 * P.d * (P.d + 2) * P.β⁻¹ ^ 2

/-- The bracket `2^{8r+5} d (K_G⁴ + K_F²) L_R⁻¹ + 2^{8r+3}(d²(1 + K_G + K_F)² + 4L_h² + 2K_H²)`
of (136). -/
noncomputable def Y : ℝ :=
  (2 : ℝ) ^ (8 * P.r + 5) * P.d * (P.KG ^ 4 + P.KF ^ 2) * P.LR⁻¹
    + (2 : ℝ) ^ (8 * P.r + 3) *
        ((P.d : ℝ) ^ 2 * (1 + P.KG + P.KF) ^ 2 + 4 * P.Lh ^ 2 + 2 * P.KH ^ 2)

/-- `C̄₀` of (136). -/
noncomputable def C0Bar : ℝ :=
  Real.exp (4 * P.LR) * P.Y * P.mom (4 * P.ρ)
    + Real.exp (4 * P.LR) * (3 : ℝ) ^ (4 * (P.r : ℝ) - 1 / 2) * P.Lh ^ 2 * P.LR⁻¹ * P.C01

/-- `C̄₁` of (136). -/
noncomputable def C1Bar : ℝ :=
  Real.exp (4 * P.LR) * P.Y * P.mom (4 * P.ρ) * (P.cRing (4 * P.r + 2) + 1)
    + Real.exp (4 * P.LR) * (3 : ℝ) ^ (4 * (P.r : ℝ) - 1 / 2) * P.Lh ^ 2 * P.LR⁻¹
        * (P.C11 + 2 * P.cRing (4 * P.r) + 1)
    + Real.exp (4 * P.LR) * (4 * P.d * P.LR⁻¹ + 4 * P.h0 ^ 2)

/-! ### (57), (60), p.26, and (62), (63), p.27 -/

/-- `min{ċ, a_F κ♯₂, a_h}`, which recurs in (56), (57), (60). -/
noncomputable def mMin : ℝ := min P.cDot (min (P.aF * P.kappaSharp) P.ah)

/-- `C̄₄` of (57). -/
noncomputable def C4Bar : ℝ :=
  √P.cHat * Real.exp (P.mMin / 8) * (1 + 8 / P.mMin) * (√P.C0Bar + 2 * √2)

/-- `C̄₅` of (57). -/
noncomputable def C5Bar : ℝ :=
  4 * (√P.cHat / P.cDot) * Real.exp (P.cDot / 4) *
    (√P.C1Bar + 1 + 2 * √2 + 2 * √(2 * P.cRing 2) + √(3 * vFun 4 (P.MV 4)))

/-- `C₃ := min{ċ, a_F κ♯₂, a_h}/8` of (60). -/
noncomputable def C3 : ℝ := P.mMin / 8

/-- `C₄` of (60). -/
noncomputable def C4 : ℝ :=
  (2 : ℝ) ^ (2 * (P.r : ℝ) + 1 / 2) * Real.exp (P.mMin / 8) *
    (√P.C0Bar + P.C4Bar + √(2 * P.cHat) * √(2 + P.gibbsV2))

/-- `C₅ := C̄₁^{1/2} + C̄₅` of (60). -/
noncomputable def C5 : ℝ := √P.C1Bar + P.C5Bar

/-- `C₆ := C₃` of (62). -/
noncomputable def C6 : ℝ := P.C3

/-- `C₇` of (62). -/
noncomputable def C7 : ℝ :=
  (2 : ℝ) ^ (2 * P.r) * P.KH * P.mom P.ρ *
    (P.C4 * (2 + √(P.cRing (2 * P.r + 1)) + √P.gibbsMom) + P.C5) * (P.thetaMom + 1)

/-- `C₈` of (62). -/
noncomputable def C8 : ℝ :=
  (2 : ℝ) ^ (2 * P.r) * P.KH * P.mom P.ρ * P.C5 *
    (1 + √(P.cRing (2 * P.r + 1)) + √P.gibbsMom)

/-- `C₉ ≡ C₉(β)` of (63), as a function of `β`. The inputs `L_h, a_h, b_h, d` do not involve
`β`, which is what makes the limit `C₉(β)/β → 0` of Lemma 6.9 meaningful. -/
noncomputable def C9Fn (β : ℝ) : ℝ :=
  (P.d : ℝ) / 2 * Real.log
      (P.Lh * (1 + 4 * max (√(P.bh / P.ah)) (√(2 * P.d / (β * P.Lh)))) ^ (2 * P.r)
          * Real.exp 1 / P.ah * (β * P.bh / P.d + 1))
    + Real.log 2

/-- `C₉ := C₉(β)` of (63). -/
noncomputable def C9 : ℝ := P.C9Fn P.β

end Params

end EThetaPoula.Risk


