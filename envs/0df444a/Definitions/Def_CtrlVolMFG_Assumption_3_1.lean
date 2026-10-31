-- Prove2me | Definitions.Def_CtrlVolMFG_Assumption_3_1
-- name    : CtrlVolMFG_Assumption_3_1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:22:29.129586+00:00
-- url     : https://prove2.me/theorems/cb2fe3d7-cce3-4f34-9234-c445fe6cbef7
-- title:
--   Assumptions 2.4, 2.5, 2.11, 2.12, 2.17, 2.19, 2.20 and 3.1
-- statement:
--   The standing assumptions of the paper, with the versions $D_mb$, $D_m\sigma$, $D_m\sigma^0$, $D_mL$, $D_mG$, $D_mH$ of the Lions derivatives.
--
--   1. **Assumption 2.17 (p.16).** $b,\sigma,\sigma^0$ are $C^1$ with bounded derivatives; $L$ is $C^1$ and $D_xL$, $D_aL$, $D_mL$ are Lipschitz in all arguments; $H$ is $C^1$ and $D_xH$, $D_yH$, $D_zH$, $D_{z^0}H$, $D_mH$ are Lipschitz; $G$ is $C^1$ and $D_xG$, $D_mG$ are Lipschitz.
--   2. **Assumption 2.19 (p.16).** There is $C_H>0$ with
--   $$\mathbb E\Big[-(D_xH(X,Y,Z,Z^0,\mathcal L(X))-D_xH(\bar X,\bar Y,\bar Z,\bar Z^0,\mathcal L(\bar X)))\cdot(X-\bar X)+(D_yH(\dots)-D_yH(\dots))\cdot(Y-\bar Y)+(D_zH(\dots)-D_zH(\dots))\cdot(Z-\bar Z)+(D_{z^0}H(\dots)-D_{z^0}H(\dots))\cdot(Z^0-\bar Z^0)\Big]\le-C_H\mathbb E|X-\bar X|^2$$
--   for all square-integrable random variables; $G$ is $C_G$-displacement monotone for some $C_G>0$; and $a\mapsto b(x,a,m)\cdot y+\sigma(x,a,m)\cdot z+\sigma^0(x,a,m)\cdot z^0+L(x,a,m)$ has a unique minimizer $\hat\alpha(x,y,z,z^0,m)$.
--   3. **Assumption 2.20 (p.17).** For fixed $(x,y,z,z^0)$, $m\mapsto D_xH,D_yH,D_zH,D_{z^0}H$ admit two Lions derivatives, bounded and Lipschitz in $m$ uniformly; for fixed $x$, $m\mapsto D_xG(x,m)$ likewise.
--   4. **Assumptions 2.4–2.5 (p.13).** $k=n$, $b=a$, $\sigma=\Sigma$, $\sigma^0=\Sigma^0$, $L=L_0(x,a)+F(x,m)$; $L_0$ is $C^1$ with Lipschitz $D_xL_0$, $D_aL_0$; $F,G$ are $C^1$ with Lipschitz $D_xF,D_mF,D_xG,D_mG$; there is $C_L>0$ with $(D_xL_0(x,a)-D_xL_0(\bar x,\bar a))\cdot(x-\bar x)+(D_aL_0(x,a)-D_aL_0(\bar x,\bar a))\cdot(a-\bar a)\ge C_L|a-\bar a|^2$, $F$ is $C_F$- and $G$ is $C_G$-displacement monotone, and $C_L+(C_G\wedge0)T+(C_F\wedge0)T^2/2>0$.
--   5. **Assumptions 2.11–2.12 (pp.14–15).** $b=B_0+B_1a+B_2x$, $\sigma=\Sigma_0+\Sigma_1a+\Sigma_2x$, $\sigma^0=\Sigma^0_0+\Sigma^0_1a+\Sigma^0_2x$; $L$, $G$ are $C^1$ with Lipschitz derivatives; $G$ is displacement monotone and (2.16) $\mathbb E[(D_xL(X,\alpha,\mathcal L(X))-D_xL(\bar X,\bar\alpha,\mathcal L(\bar X)))\cdot(X-\bar X)+(D_aL(\dots)-D_aL(\dots))\cdot(\alpha-\bar\alpha)]\ge C_L\mathbb E|\alpha-\bar\alpha|^2$.
--   6. **Assumption 3.1 (p.19).** Either 2.4 and 2.5, or 2.11 and 2.12, or 2.17 and 2.19 hold.
--
--   The extra conditions on $\hat\alpha$ in Theorem 2.23 (Lipschitz, two bounded Lipschitz Lions derivatives) are also recorded here.
--
--   **Formalization Note** "Displacement monotone" is $0$-displacement monotone. In (2.16) the page's $(X-X')$ is read as $(X-\bar X)$. The sentence of Assumption 2.20 on $D_yH$, $D_zH$, $D_{z^0}H$ is read as a condition on their two Lions derivatives. Expectations over random variables are integrals over couplings, required when the integrand is integrable.
-- source:
--   Jackson & Tangpi, Quantitative Convergence for Displacement Monotone Mean Field Games with Controlled Volatility, arXiv:2304.04543v2, Assumptions 2.4, 2.5 p.13; 2.11 p.14; 2.12 p.15; 2.17, 2.19 p.16; 2.20 p.17; Theorem 2.23 (1)–(2) p.18; Assumption 3.1 p.19

import Mathlib
import Definitions.Def_CtrlVolMFG_IsMFE

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CtrlVolMFG

variable {n k d : ℕ}

/-- Versions of the Lions derivatives of the data and of the Hamiltonian
(Jackson & Tangpi, arXiv:2304.04543v2, §2.3, p.11): `D_mb(x, a, m, p)`, `D_mσ`, `D_mσ⁰` (linear
maps `ℝⁿ → ℝⁿ`, `ℝⁿ → ℝ^{n×d}`, the paper's componentwise derivatives), and the vectors
`D_mL(x, a, m, p)`, `D_mG(x, m, p)`, `D_mH(x, y, z, z⁰, m, p) ∈ ℝⁿ`.

**Formalization Note** A Lions derivative is determined only `m`-almost everywhere in `p`, so the
versions are data; the assumptions below say they are Lions derivatives with the required
regularity. -/
structure Derivs (n k d : ℕ) where
  Dmb : Rn n → Rn k → P2 n → Rn n → (Rn n →L[ℝ] Rn n)
  Dmσ : Rn n → Rn k → P2 n → Rn n → (Rn n →L[ℝ] Mat n d)
  Dmσ0 : Rn n → Rn k → P2 n → Rn n → (Rn n →L[ℝ] Mat n d)
  DmL : Rn n → Rn k → P2 n → Rn n → Rn n
  DmG : Rn n → P2 n → Rn n → Rn n
  DmH : Rn n → Rn n → Mat n d → Mat n d → P2 n → Rn n → Rn n

/-- The versions `V` are Lions derivatives (in `m`, every other argument fixed) of `b`, `σ`,
`σ⁰`, `L` and `G` (§2.3, p.11). -/
def AreLions (D : Data n k d) (V : Derivs n k d) : Prop :=
  (∀ x a, DisplMonoMFG.WellPosed.HasLDeriv (D.b x a) (V.Dmb x a)) ∧
    (∀ x a, DisplMonoMFG.WellPosed.HasLDeriv (D.σ x a) (V.Dmσ x a)) ∧
    (∀ x a, DisplMonoMFG.WellPosed.HasLDeriv (D.σ0 x a) (V.Dmσ0 x a)) ∧
    (∀ x a, DisplMonoMFG.WellPosed.HasLDeriv (D.L x a)
      (fun m p => innerSL ℝ (V.DmL x a m p))) ∧
    ∀ x, DisplMonoMFG.WellPosed.HasLDeriv (D.G x) (fun m p => innerSL ℝ (V.DmG x m p))

/-! ### The general case, §2.5.3 -/

/-- Assumption 2.17 (arXiv:2304.04543v2, p.16): `b, σ, σ⁰` are `C¹` with bounded derivatives;
`L` is `C¹` and `D_xL, D_aL, D_mL` are Lipschitz in all arguments; the Hamiltonian `H` is `C¹` and
`D_xH, D_yH, D_zH, D_{z⁰}H, D_mH` are Lipschitz on `ℝⁿ × ℝⁿ × ℝ^{n×d} × ℝ^{n×d} × 𝒫₂(ℝⁿ)`; `G` is
`C¹` and `D_xG, D_mG` are Lipschitz in all arguments.

**Formalization Note** `C¹` is `IsC1` (§2.3): differentiable in the non-measure arguments jointly,
with jointly continuous derivative, and Lions differentiable in `m` with the version from `V`,
jointly continuous. "Bounded derivatives" of `b, σ, σ⁰` covers `D_{(x,a)}` and `D_m`. "Lipschitz in
all arguments" is Lipschitz in the non-measure arguments (including the point argument `p` of
`D_m`) and in `m` for `𝒲₂` (`LipXM`). -/
structure Assumption_2_17 (D : Data n k d) (V : Derivs n k d) : Prop where
  b_C1 : IsC1 (fun (q : Rn n × Rn k) m => D.b q.1 q.2 m) (fun q => V.Dmb q.1 q.2)
  σ_C1 : IsC1 (fun (q : Rn n × Rn k) m => D.σ q.1 q.2 m) (fun q => V.Dmσ q.1 q.2)
  σ0_C1 : IsC1 (fun (q : Rn n × Rn k) m => D.σ0 q.1 q.2 m) (fun q => V.Dmσ0 q.1 q.2)
  b_bdd : BddXM (fun (q : Rn n × Rn k) m => fderiv ℝ (fun q' : Rn n × Rn k => D.b q'.1 q'.2 m) q) ∧
    BddXM (fun (q : (Rn n × Rn k) × Rn n) m => V.Dmb q.1.1 q.1.2 m q.2)
  σ_bdd : BddXM (fun (q : Rn n × Rn k) m => fderiv ℝ (fun q' : Rn n × Rn k => D.σ q'.1 q'.2 m) q) ∧
    BddXM (fun (q : (Rn n × Rn k) × Rn n) m => V.Dmσ q.1.1 q.1.2 m q.2)
  σ0_bdd : BddXM (fun (q : Rn n × Rn k) m =>
      fderiv ℝ (fun q' : Rn n × Rn k => D.σ0 q'.1 q'.2 m) q) ∧
    BddXM (fun (q : (Rn n × Rn k) × Rn n) m => V.Dmσ0 q.1.1 q.1.2 m q.2)
  L_C1 : IsC1 (fun (q : Rn n × Rn k) m => D.L q.1 q.2 m)
    (fun q m p => innerSL ℝ (V.DmL q.1 q.2 m p))
  DxL_lip : LipXM (fun (q : Rn n × Rn k) m => D.DxL q.1 q.2 m)
  DaL_lip : LipXM (fun (q : Rn n × Rn k) m => D.DaL q.1 q.2 m)
  DmL_lip : LipXM (fun (q : (Rn n × Rn k) × Rn n) m => V.DmL q.1.1 q.1.2 m q.2)
  H_C1 : IsC1 (fun (q : Rn n × Rn n × Mat n d × Mat n d) m => D.H q.1 q.2.1 q.2.2.1 q.2.2.2 m)
    (fun q m p => innerSL ℝ (V.DmH q.1 q.2.1 q.2.2.1 q.2.2.2 m p))
  DxH_lip : LipXM (fun (q : Rn n × Rn n × Mat n d × Mat n d) m =>
    D.DxH q.1 q.2.1 q.2.2.1 q.2.2.2 m)
  DyH_lip : LipXM (fun (q : Rn n × Rn n × Mat n d × Mat n d) m =>
    D.DyH q.1 q.2.1 q.2.2.1 q.2.2.2 m)
  DzH_lip : LipXM (fun (q : Rn n × Rn n × Mat n d × Mat n d) m =>
    D.DzH q.1 q.2.1 q.2.2.1 q.2.2.2 m)
  Dz0H_lip : LipXM (fun (q : Rn n × Rn n × Mat n d × Mat n d) m =>
    D.Dz0H q.1 q.2.1 q.2.2.1 q.2.2.2 m)
  DmH_lip : LipXM (fun (q : (Rn n × Rn n × Mat n d × Mat n d) × Rn n) m =>
    V.DmH q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 m q.2)
  G_C1 : IsC1 D.G (fun x m p => innerSL ℝ (V.DmG x m p))
  DxG_lip : LipXM D.DxG
  DmG_lip : LipXM (fun (q : Rn n × Rn n) m => V.DmG q.1 m q.2)

/-- The left-hand integrand of (2.19), p.16, at `w = ((X, Y, Z, Z⁰), (X̄, Ȳ, Z̄, Z̄⁰))`, with
`μ = ℒ(X)` and `μ̄ = ℒ(X̄)`:
`−(D_xH(X, Y, Z, Z⁰, μ) − D_xH(X̄, Ȳ, Z̄, Z̄⁰, μ̄))·(X − X̄) + (D_yH(…) − D_yH(…))·(Y − Ȳ)
 + (D_zH(…) − D_zH(…))·(Z − Z̄) + (D_{z⁰}H(…) − D_{z⁰}H(…))·(Z⁰ − Z̄⁰)`. -/
noncomputable def monoH (D : Data n k d)
    (w : (Rn n × Rn n × Mat n d × Mat n d) × (Rn n × Rn n × Mat n d × Mat n d))
    (μ μ' : P2 n) : ℝ :=
  -inner ℝ (D.DxH w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2 μ -
      D.DxH w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2 μ') (w.1.1 - w.2.1) +
    inner ℝ (D.DyH w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2 μ -
      D.DyH w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2 μ') (w.1.2.1 - w.2.2.1) +
    inner ℝ (D.DzH w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2 μ -
      D.DzH w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2 μ') (w.1.2.2.1 - w.2.2.2.1) +
    inner ℝ (D.Dz0H w.1.1 w.1.2.1 w.1.2.2.1 w.1.2.2.2 μ -
      D.Dz0H w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2 μ') (w.1.2.2.2 - w.2.2.2.2)

/-- The displacement monotonicity (2.19) of the Hamiltonian with constant `C_H`
(arXiv:2304.04543v2, Assumption 2.19, p.16): for all square-integrable `X, X̄, Y, Ȳ` (`ℝⁿ`) and
`Z, Z̄, Z⁰, Z̄⁰` (`ℝ^{n×d}`) with joint law `π`,
`𝔼[monoH] ≤ −C_H 𝔼|X − X̄|²`, where `ℒ(X), ℒ(X̄)` are the marginals of `π`.

**Formalization Note** Random variables enter only through their joint law (all couplings occur
on an atomless space); the inequality is asked when the integrand is integrable (it always is
under Assumption 2.17). -/
def DisplMonoH (D : Data n k d) (CH : ℝ) : Prop :=
  ∀ π : Measure ((Rn n × Rn n × Mat n d × Mat n d) × (Rn n × Rn n × Mat n d × Mat n d)),
    IsL2Pair π →
    Integrable (fun w => monoH D w (toP2 (π.map fun w => w.1.1))
      (toP2 (π.map fun w => w.2.1))) π →
    ∫ w, monoH D w (toP2 (π.map fun w => w.1.1)) (toP2 (π.map fun w => w.2.1)) ∂π ≤
      -CH * ∫ w, ‖w.1.1 - w.2.1‖ ^ 2 ∂π

/-- Assumption 2.19 (arXiv:2304.04543v2, p.16): (2.19) holds for some `C_H > 0`; `G` is
`C_G`-displacement monotone for some `C_G > 0`; and for each `(x, y, z, z⁰, m)` the map (2.20)
`a ↦ b(x, a, m)·y + σ(x, a, m)·z + σ⁰(x, a, m)·z⁰ + L(x, a, m)` has a unique minimizer `α̂`. -/
def Assumption_2_19 (D : Data n k d) : Prop :=
  (∃ CH > 0, DisplMonoH D CH) ∧ (∃ CG > 0, IsDisplMono CG D.G) ∧
    ∀ x y z z0 m, ∃! a : Rn k, ∀ a', D.ham x a y z z0 m ≤ D.ham x a' y z z0 m

/-- Assumption 2.20 (arXiv:2304.04543v2, p.17): for each fixed `(x, y, z, z⁰)` the maps
`m ↦ D_xH, D_yH, D_zH, D_{z⁰}H (x, y, z, z⁰, m)` admit two Lions derivatives which are bounded and
Lipschitz in `m`, uniformly in `(x, y, z, z⁰)`; for each fixed `x`, `m ↦ D_xG(x, m)` admits two
such derivatives, uniformly in `x`.

**Formalization Note** The sentence "similarly, the functions `D_yH, D_zH, D_{z⁰}H` are bounded and
Lipschitz continuous, uniformly in `(x, y, z, z⁰)`" is read as a statement about their two Lions
derivatives (the reading that does not make `D_yH` itself bounded). -/
def Assumption_2_20 (D : Data n k d) : Prop :=
  TwoLionsUnif (fun (q : Rn n × Rn n × Mat n d × Mat n d) m =>
      D.DxH q.1 q.2.1 q.2.2.1 q.2.2.2 m) ∧
    TwoLionsUnif (fun (q : Rn n × Rn n × Mat n d × Mat n d) m =>
      D.DyH q.1 q.2.1 q.2.2.1 q.2.2.2 m) ∧
    TwoLionsUnif (fun (q : Rn n × Rn n × Mat n d × Mat n d) m =>
      D.DzH q.1 q.2.1 q.2.2.1 q.2.2.2 m) ∧
    TwoLionsUnif (fun (q : Rn n × Rn n × Mat n d × Mat n d) m =>
      D.Dz0H q.1 q.2.1 q.2.2.1 q.2.2.2 m) ∧
    TwoLionsUnif D.DxG

/-- The extra conditions on the optimizer in Theorem 2.23 and Proposition 3.16
(arXiv:2304.04543v2, pp.18, 35): (1) `α̂` is Lipschitz (in all arguments, `𝒲₂` in `m`); (2) for
each fixed `(x, y, z, z⁰)`, `m ↦ α̂(x, y, z, z⁰, m)` admits derivatives `D_mα̂`, `D_mmα̂` which are
bounded and Lipschitz continuous, uniformly in `(x, y, z, z⁰)`. -/
def AlphaHatReg (D : Data n k d) : Prop :=
  LipXM (fun (q : Rn n × Rn n × Mat n d × Mat n d) m =>
      D.alphaHat q.1 q.2.1 q.2.2.1 q.2.2.2 m) ∧
    TwoLionsUnif (fun (q : Rn n × Rn n × Mat n d × Mat n d) m =>
      D.alphaHat q.1 q.2.1 q.2.2.1 q.2.2.2 m)

/-! ### The constant volatility case, §2.5.1 -/

/-- The objects of the constant volatility case (2.10), p.13: `k = n`, matrices
`Σ, Σ⁰ ∈ ℝ^{n×d}`, the Lagrangian `L₀ : ℝⁿ × ℝⁿ → ℝ`, the coupling `F : ℝⁿ × 𝒫₂(ℝⁿ) → ℝ` and a
version `D_mF` of the Lions derivative of `F`. -/
structure ConstVol (n k d : ℕ) where
  hk : k = n
  Sig : Mat n d
  Sig0 : Mat n d
  L0 : Rn n → Rn k → ℝ
  F : Rn n → P2 n → ℝ
  DmF : Rn n → P2 n → Rn n → Rn n

/-- `D_xL₀(x, a)`. -/
noncomputable def ConstVol.DxL0 (c : ConstVol n k d) (x : Rn n) (a : Rn k) : Rn n :=
  gradient (fun x' => c.L0 x' a) x

/-- `D_aL₀(x, a)`. -/
noncomputable def ConstVol.DaL0 (c : ConstVol n k d) (x : Rn n) (a : Rn k) : Rn k :=
  gradient (fun a' => c.L0 x a') a

/-- Assumption 2.4 (arXiv:2304.04543v2, p.13): the data are of the form (2.10),
`b(x, a, m) = a`, `σ(x, a, m) = Σ`, `σ⁰(x, a, m) = Σ⁰`, `L(x, a, m) = L₀(x, a) + F(x, m)` (with
`k = n`); `L₀` is `C¹` and `D_xL₀, D_aL₀` are Lipschitz in all arguments; `F` and `G` are `C¹` and
`D_xF, D_mF, D_xG, D_mG` are Lipschitz in all arguments.

**Formalization Note** `b(x, a, m) = a` is written with the cast along `k = n`. -/
def Assumption_2_4 (D : Data n k d) (V : Derivs n k d) (c : ConstVol n k d) : Prop :=
  (∀ x a m, D.b x a m = c.hk ▸ a) ∧ (∀ x a m, D.σ x a m = c.Sig) ∧
    (∀ x a m, D.σ0 x a m = c.Sig0) ∧ (∀ x a m, D.L x a m = c.L0 x a + c.F x m) ∧
    ContDiff ℝ 1 (fun q : Rn n × Rn k => c.L0 q.1 q.2) ∧
    (∃ K : ℝ≥0, LipschitzWith K (fun q : Rn n × Rn k => c.DxL0 q.1 q.2)) ∧
    (∃ K : ℝ≥0, LipschitzWith K (fun q : Rn n × Rn k => c.DaL0 q.1 q.2)) ∧
    IsC1 c.F (fun x m p => innerSL ℝ (c.DmF x m p)) ∧ LipXM (Dx c.F) ∧
    LipXM (fun (q : Rn n × Rn n) m => c.DmF q.1 m q.2) ∧
    IsC1 D.G (fun x m p => innerSL ℝ (V.DmG x m p)) ∧ LipXM D.DxG ∧
    LipXM (fun (q : Rn n × Rn n) m => V.DmG q.1 m q.2)

/-- Assumption 2.5 (arXiv:2304.04543v2, p.13): there is `C_L > 0` with (2.12)
`(D_xL₀(x, a) − D_xL₀(x̄, ā))·(x − x̄) + (D_aL₀(x, a) − D_aL₀(x̄, ā))·(a − ā) ≥ C_L|a − ā|²` for all
`x, x̄, a, ā`; and there are (possibly negative) reals `C_F, C_G` such that `F` is
`C_F`-displacement monotone, `G` is `C_G`-displacement monotone and (2.13)
`C_L + (C_G ∧ 0)T + (C_F ∧ 0)T²/2 > 0`. -/
def Assumption_2_5 (D : Data n k d) (c : ConstVol n k d) (T : ℝ≥0) : Prop :=
  ∃ CL > 0,
    (∀ x x' a a', CL * ‖a - a'‖ ^ 2 ≤
      inner ℝ (c.DxL0 x a - c.DxL0 x' a') (x - x') + inner ℝ (c.DaL0 x a - c.DaL0 x' a') (a - a')) ∧
    ∃ CF CG : ℝ, IsDisplMono CF c.F ∧ IsDisplMono CG D.G ∧
      0 < CL + min CG 0 * T + min CF 0 * (T : ℝ) ^ 2 / 2

/-! ### The affine case, §2.5.2 -/

/-- The coefficients of the affine dynamics (2.15), p.14: `B₀ ∈ ℝⁿ`, `B₁ ∈ ℝ^{n×k}`,
`B₂ ∈ ℝ^{n×n}`, `Σ₀, Σ⁰₀ ∈ ℝ^{n×d}`, `Σ₁, Σ⁰₁ ∈ (ℝ^{n×d})ᵏ`, `Σ₂, Σ⁰₂ ∈ (ℝ^{n×d})ⁿ`, the last
four as the linear maps `a ↦ Σⱼ aʲΣ₁ʲ` etc. of p.14. -/
structure Affine (n k d : ℕ) where
  B0 : Rn n
  B1 : Rn k →L[ℝ] Rn n
  B2 : Rn n →L[ℝ] Rn n
  S0 : Mat n d
  S1 : Rn k →L[ℝ] Mat n d
  S2 : Rn n →L[ℝ] Mat n d
  S00 : Mat n d
  S01 : Rn k →L[ℝ] Mat n d
  S02 : Rn n →L[ℝ] Mat n d

/-- Assumption 2.11 (arXiv:2304.04543v2, p.14): the data are of the form (2.15),
`b = B₀ + B₁a + B₂x`, `σ = Σ₀ + Σ₁a + Σ₂x`, `σ⁰ = Σ⁰₀ + Σ⁰₁a + Σ⁰₂x`; `L` is `C¹` and
`D_xL, D_aL, D_mL` are Lipschitz in all arguments; `G` is `C¹` and `D_xG, D_mG` are Lipschitz in
all arguments. -/
def Assumption_2_11 (D : Data n k d) (V : Derivs n k d) (c : Affine n k d) : Prop :=
  (∀ x a m, D.b x a m = c.B0 + c.B1 a + c.B2 x) ∧
    (∀ x a m, D.σ x a m = c.S0 + c.S1 a + c.S2 x) ∧
    (∀ x a m, D.σ0 x a m = c.S00 + c.S01 a + c.S02 x) ∧
    IsC1 (fun (q : Rn n × Rn k) m => D.L q.1 q.2 m)
      (fun q m p => innerSL ℝ (V.DmL q.1 q.2 m p)) ∧
    LipXM (fun (q : Rn n × Rn k) m => D.DxL q.1 q.2 m) ∧
    LipXM (fun (q : Rn n × Rn k) m => D.DaL q.1 q.2 m) ∧
    LipXM (fun (q : (Rn n × Rn k) × Rn n) m => V.DmL q.1.1 q.1.2 m q.2) ∧
    IsC1 D.G (fun x m p => innerSL ℝ (V.DmG x m p)) ∧ LipXM D.DxG ∧
    LipXM (fun (q : Rn n × Rn n) m => V.DmG q.1 m q.2)

/-- The left-hand integrand of (2.16), p.15, at `w = ((X, α), (X̄, ᾱ))`, with `μ = ℒ(X)`,
`μ̄ = ℒ(X̄)`: `(D_xL(X, α, μ) − D_xL(X̄, ᾱ, μ̄))·(X − X̄) + (D_aL(X, α, μ) − D_aL(X̄, ᾱ, μ̄))·(α − ᾱ)`. -/
noncomputable def monoL (D : Data n k d) (w : (Rn n × Rn k) × (Rn n × Rn k)) (μ μ' : P2 n) : ℝ :=
  inner ℝ (D.DxL w.1.1 w.1.2 μ - D.DxL w.2.1 w.2.2 μ') (w.1.1 - w.2.1) +
    inner ℝ (D.DaL w.1.1 w.1.2 μ - D.DaL w.2.1 w.2.2 μ') (w.1.2 - w.2.2)

/-- Assumption 2.12 (arXiv:2304.04543v2, p.15): `G` is displacement monotone, and there is
`C_L > 0` with (2.16) `𝔼[monoL] ≥ C_L 𝔼|α − ᾱ|²` for all square-integrable `X, X̄` (`ℝⁿ`) and
`α, ᾱ` (`ℝᵏ`).

**Formalization Note** The page's `(X − X′)` is read as `(X − X̄)`. Random variables enter through
their joint law `π`, and the inequality is asked when the integrand is integrable. -/
def Assumption_2_12 (D : Data n k d) : Prop :=
  IsDisplMono 0 D.G ∧
    ∃ CL > 0, ∀ π : Measure ((Rn n × Rn k) × (Rn n × Rn k)), IsL2Pair π →
      Integrable (fun w => monoL D w (toP2 (π.map fun w => w.1.1))
        (toP2 (π.map fun w => w.2.1))) π →
      CL * ∫ w, ‖w.1.2 - w.2.2‖ ^ 2 ∂π ≤
        ∫ w, monoL D w (toP2 (π.map fun w => w.1.1)) (toP2 (π.map fun w => w.2.1)) ∂π

/-! ### Assumption 3.1 -/

/-- Assumption 3.1 (arXiv:2304.04543v2, p.19): either Assumptions 2.4 and 2.5 hold, or
Assumptions 2.11 and 2.12 hold, or Assumptions 2.17 and 2.19 hold. (Assumption 2.5 involves the
horizon `T` through (2.13).) -/
def Assumption_3_1 (D : Data n k d) (V : Derivs n k d) (T : ℝ≥0) : Prop :=
  (∃ c : ConstVol n k d, Assumption_2_4 D V c ∧ Assumption_2_5 D c T) ∨
    (∃ c : Affine n k d, Assumption_2_11 D V c ∧ Assumption_2_12 D) ∨
    (Assumption_2_17 D V ∧ Assumption_2_19 D)

end CtrlVolMFG


