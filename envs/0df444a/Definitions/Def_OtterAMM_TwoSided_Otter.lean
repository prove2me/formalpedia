-- Prove2me | Definitions.Def_OtterAMM_TwoSided_Otter
-- name    : OtterAMM_TwoSided_Otter
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:47:01.268838+00:00
-- url     : https://prove2.me/theorems/4ddee6c7-050b-4247-b624-0c800b2c5119
-- title:
--   The two-sided Otter mechanism of §3.2 (spot-eligible supplies $D_Y,D_X$, dominance (6), curves $\tilde F^M_Y,\tilde H^M_X$), its final pool input, and $\phi_Y,\phi_X$ of Lemma 17
-- statement:
--   Let $F$ be a pricing curve with $\sigma_0,\rho_0,H$. For a block with reports, the spot-eligible supplies are
--   $$D_Y=\sum_{i\in\mathcal Y}\tilde q_i\mathbf 1\{\tilde v_i\le\sigma_0\},\qquad D_X=\sum_{j\in\mathcal X}\tilde r_j\mathbf 1\{\tilde u_j\le\rho_0\}.$$
--   The profile is **sell-Y dominated** iff $D_Y\ge\rho_0D_X$ (6) (ties go to sell-Y), sell-X dominated otherwise.
--
--   **Otter** (with an admissible selection rule):
--
--   - *Sell-Y dominated*, $M:=\rho_0D_X$: every sell-X order with $\tilde u_j\le\rho_0$ gets $x_j=\tilde r_j$, $y_j=\rho_0\tilde r_j$ (7); one with $\tilde u_j>\rho_0$ gets $(0,0)$; all sell-Y reports run the one-sided VCG auction on
--   $$\tilde F^M_Y(y)=\begin{cases}\sigma_0y,&0\le y\le M,\\ D_X+F(y-M),&y\ge M.\end{cases}\qquad(8)$$
--   - *Sell-X dominated*, $M:=\sigma_0D_Y$: every sell-Y order with $\tilde v_i\le\sigma_0$ gets $y_i=\tilde q_i$, $x_i=\sigma_0\tilde q_i$; one with $\tilde v_i>\sigma_0$ gets $(0,0)$; all sell-X reports run the one-sided VCG auction with the roles of $X$ and $Y$ swapped ($x_j$ the sale, $y_j$ the compensation) on $\tilde H^M_X(x)=\rho_0x$ on $[0,M]$ and $D_Y+H(x-M)$ for $x\ge M$.
--
--   On ordered blocks Otter ignores the order. The **final pool input** is $p_e=Q_Y-M$ in a sell-Y dominated profile ($Q_Y$ the total $Y$ sold by sell-Y identities) and $p_e=F^{-1}(-(Q_X-M))$ in a sell-X dominated one ($Q_X$ the total $X$ sold by sell-X identities). For Lemma 17, with $O$ a finite set of sell-Y (resp. sell-X) reports and a fresh comparison seller,
--   $$\phi_Y(M;v,q)=W_{\tilde F^M_Y}(O\cup\{(v,q)\})-W_{\tilde F^M_Y}(O),\qquad \phi_X(M;u,r)=W_{\tilde H^M_X}(O\cup\{(u,r)\})-W_{\tilde H^M_X}(O).$$
--
--   **Formalization Note.** $\tilde F^M_Y$ is `spotExtend F σ0 M`, i.e. $\sigma_0M+F(y-M)$ beyond $M$; at $M=\rho_0D_X$ this is $D_X+F(y-M)$ because $\sigma_0\rho_0=1$ (likewise $\rho_0M=D_Y$ for $\tilde H^M_X$). The comparison seller of $\phi_Y,\phi_X$ is a label $i_0$ outside $O$ with ask $v$ and budget $q$.
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), pp. 11–12, §3.2, Eqs. (6)–(8) (PDF 13–14); p. 21, §6.2 (PDF 23); p. 22, Lemma 17 (PDF 24)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model
import Definitions.Def_OtterAMM_TwoSided_VCG

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- `D_Y := Σ_{i ∈ Y} q̃_i 1{ṽ_i ≤ σ0}`, the spot-eligible sell-Y supply of `S` (§3.2). -/
noncomputable def DY (C : PricingCurve) (S : Finset Ident) (rep : Ident → Report) : ℝ :=
  ∑ i ∈ sellYs S rep, if (rep i).ask ≤ C.σ0 then (rep i).budget else 0

/-- `D_X := Σ_{j ∈ X} r̃_j 1{ũ_j ≤ ρ0}`, the spot-eligible sell-X supply of `S` (§3.2). -/
noncomputable def DX (C : PricingCurve) (S : Finset Ident) (rep : Ident → Report) : ℝ :=
  ∑ j ∈ sellXs S rep, if (rep j).ask ≤ C.ρ0 then (rep j).budget else 0

/-- Eq. (6): the profile is sell-Y dominated iff `D_Y ≥ ρ0·D_X` (ties go to sell-Y); it is
sell-X dominated otherwise. -/
abbrev SellYDominated (C : PricingCurve) (S : Finset Ident) (rep : Ident → Report) : Prop :=
  C.ρ0 * DX C S rep ≤ DY C S rep

/-- Eq. (8): `F̃^M_Y(y) = σ0·y` on `[0, M]` and `σ0·M + F(y − M)` for `y ≥ M`. With
`M = ρ0·D_X` one has `σ0·M = D_X`, which is the printed form `D_X + F(y − M)`. -/
noncomputable def curveY (C : PricingCurve) (M : ℝ) : ℝ → ℝ := spotExtend C.F C.σ0 M

/-- `H̃^M_X(x) = ρ0·x` on `[0, M]` and `ρ0·M + H(x − M)` for `x ≥ M` (§3.2, p. 12). With
`M = σ0·D_Y` one has `ρ0·M = D_Y`, the printed form `D_Y + H(x − M)`. -/
noncomputable def curveX (C : PricingCurve) (M : ℝ) : ℝ → ℝ := spotExtend C.H C.ρ0 M

/-- The two-sided Otter mechanism of §3.2 (Eqs. (6)–(8)), with the one-sided VCG auction run
with the selection rule `sel`. Outcome pairs are `(x_i, y_i)`.
* Sell-Y dominated (`D_Y ≥ ρ0·D_X`), `M := ρ0·D_X`: a sell-X identity with `ũ_j ≤ ρ0` gets
  `x_j = r̃_j`, `y_j = ρ0·r̃_j` (Eq. (7)); one with `ũ_j > ρ0` gets `(0, 0)`; the sell-Y
  identities run the one-sided VCG auction on `F̃^M_Y`.
* Sell-X dominated, `M := σ0·D_Y`: a sell-Y identity with `ṽ_i ≤ σ0` gets `y_i = q̃_i`,
  `x_i = σ0·q̃_i`; one with `ṽ_i > σ0` gets `(0, 0)`; the sell-X identities run the one-sided
  VCG auction (roles of `X` and `Y` swapped: `x_j` = sale, `y_j` = compensation) on `H̃^M_X`.
Identities outside the block get `(0, 0)`. -/
noncomputable def otter (C : PricingCurve) (sel : SelRule) : UMechanism :=
  fun S rep i =>
    if i ∈ S then
      if SellYDominated C S rep then
        match (rep i).dir with
        | .sellY =>
            (vcgComp sel (curveY C (C.ρ0 * DX C S rep)) (sellYs S rep) (askOf rep) (budgetOf rep) i,
             vcgAlloc sel (curveY C (C.ρ0 * DX C S rep)) (sellYs S rep) (askOf rep) (budgetOf rep) i)
        | .sellX =>
            if (rep i).ask ≤ C.ρ0 then ((rep i).budget, C.ρ0 * (rep i).budget) else (0, 0)
      else
        match (rep i).dir with
        | .sellX =>
            (vcgAlloc sel (curveX C (C.σ0 * DY C S rep)) (sellXs S rep) (askOf rep) (budgetOf rep) i,
             vcgComp sel (curveX C (C.σ0 * DY C S rep)) (sellXs S rep) (askOf rep) (budgetOf rep) i)
        | .sellY =>
            if (rep i).ask ≤ C.σ0 then (C.σ0 * (rep i).budget, (rep i).budget) else (0, 0)
    else (0, 0)

/-- Otter on ordered blocks: it ignores the order (it reads only the set of identities). -/
noncomputable def otterMech (C : PricingCurve) (sel : SelRule) : Mechanism :=
  fun ℓ rep => otter C sel ℓ.toFinset rep

/-- The final signed pool input `p_e` (§6.2, p. 21): `Q_Y − M ≥ 0` in a sell-Y dominated profile
(`Q_Y` = aggregate `Y` spent by sell-Y identities, `M = ρ0·D_X`); in a sell-X dominated profile
the pool receives `Q_X − M` units of `X` (`M = σ0·D_Y`), i.e. `p_e = F⁻¹(−(Q_X − M)) ≤ 0`, with
`F⁻¹` the inverse of `F` on `(−b, +∞)`. -/
noncomputable def poolInput (C : PricingCurve) (sel : SelRule) (S : Finset Ident)
    (rep : Ident → Report) : ℝ :=
  if SellYDominated C S rep then
    (∑ i ∈ sellYs S rep, (otter C sel S rep i).2) - C.ρ0 * DX C S rep
  else
    Function.invFunOn C.F (Set.Ioi (-C.b))
      (-((∑ j ∈ sellXs S rep, (otter C sel S rep j).1) - C.σ0 * DY C S rep))

/-- Lemma 17: `ϕ_Y(M; v, q) := W_{F̃^M_Y}(O ∪ {(v, q)}) − W_{F̃^M_Y}(O)`, the comparison seller
being a fresh identity `i0` with ask `v` and budget `q`. -/
noncomputable def phiY (C : PricingCurve) (O : Finset Ident) (a q : Ident → ℝ) (i0 : Ident)
    (M v qq : ℝ) : ℝ :=
  W (curveY C M) (insert i0 O) (Function.update a i0 v) (Function.update q i0 qq) -
    W (curveY C M) O a q

/-- Lemma 17: `ϕ_X(M; u, r) := W_{H̃^M_X}(O ∪ {(u, r)}) − W_{H̃^M_X}(O)`. -/
noncomputable def phiX (C : PricingCurve) (O : Finset Ident) (a q : Ident → ℝ) (i0 : Ident)
    (M u r : ℝ) : ℝ :=
  W (curveX C M) (insert i0 O) (Function.update a i0 u) (Function.update q i0 r) -
    W (curveX C M) O a q

end OtterAMM.TwoSided


