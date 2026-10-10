-- Prove2me | Definitions.Def_MasterVisc_Comparison_Viscosity
-- name    : MasterVisc_Comparison_Viscosity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:28.651883+00:00
-- url     : https://prove2.me/theorems/67dab737-1142-4f1f-b316-d139dbc618aa
-- title:
--   Definition 4.2, (4.2), Definition 4.4, (4.4)–(4.6), Definition 3.3 — C_b^{1,1,1}, test sets 𝒜̲^L, 𝒜̄^L, viscosity solutions, paraboloids and semi-jets
-- statement:
--   This file defines the viscosity theory of Wu–Zhang for the master equation (3.1).
--
--   **Smooth objects (Definition 4.2).** Let $0\le t_1<t_2\le T$ and $\mathcal P\subset\mathcal P_2$ a set of semimartingale laws on $[t_1,t_2]$. A function $\varphi$ is in $C_b^{1,1,1}([t_1,t_2]\times\mathcal P)$ if there are $\partial_t\varphi$, $\partial_\mu\varphi(t,\mu,\omega)\in\mathbb R^d$ and $\partial_\omega\partial_\mu\varphi(t,\mu,\omega)\in\mathbb R^{d\times d}$ such that $\varphi,\partial_t\varphi$ are continuous on $[t_1,t_2]\times\mathcal P$, $\partial_\mu\varphi,\partial_\omega\partial_\mu\varphi$ are continuous on $[t_1,t_2]\times\mathcal P\times\Omega$ and $\mathcal F_s$-measurable in $\omega$, the functional Itô formula (2.25) holds on $[t_1,t_2]$ under every $\mathbb P\in\mathcal P$:
--   $$\varphi(s,\mathbb P)-\varphi(t_1,\mathbb P)=\int_{t_1}^s\partial_t\varphi(r,\mathbb P)\,dr+\mathbb E^{\mathbb P}\Big[\int_{t_1}^s\partial_\mu\varphi(r,\mathbb P,X)\cdot dX_r+\tfrac12\int_{t_1}^s\partial_\omega\partial_\mu\varphi(r,\mathbb P,X):d\langle X\rangle_r\Big],$$
--   $\partial_t\varphi$ is bounded, and $|\partial_\mu\varphi(t,\mu,\omega)|+|\partial_\omega\partial_\mu\varphi(t,\mu,\omega)|\le C[1+\|\omega\|]$ for $\mathbb P$-a.e. $\omega$ and all $\mathbb P\in\mathcal P$. The operator is $\mathbb L\varphi(t,\mu)=\partial_t\varphi(t,\mu)+G(t,\mu,\varphi(t,\mu),\partial_\mu\varphi(t,\mu,\cdot),\partial_\omega\partial_\mu\varphi(t,\mu,\cdot))$.
--
--   **Test sets (4.2).** For $V:\Theta\to\mathbb R$, $L>0$ and $(t,\mu)\in\Theta$, with $\mathcal P^{t,\mu}_{L,\delta}=[t,t+\delta]\times\mathcal P_L(t,\mu)$,
--   $$\underline{\mathcal A}^LV(t,\mu)=\bigcup_{0<\delta\le T-t}\Big\{\varphi\in C^{1,1,1}_b(\mathcal P^{t,\mu}_{L,\delta}):(\varphi-V)(t,\mu)=0,\ \inf_{\mathcal P^{t,\mu}_{L,\delta}}(\varphi-V)=0\Big\},$$
--   and $\overline{\mathcal A}^LV(t,\mu)$ is the same with $\sup$.
--
--   **Viscosity solutions (Definition 4.4).** $V\in C^0(\Theta)$ is an $L$-viscosity subsolution (supersolution) of (3.1) if $\mathbb L\varphi(t,\mu)\ge0$ ($\le0$) for all $(t,\mu)\in\Theta$ and all $\varphi\in\underline{\mathcal A}^LV(t,\mu)$ ($\overline{\mathcal A}^LV(t,\mu)$); an $L$-viscosity solution if both; a viscosity solution if it is an $L$-viscosity solution for some $L>0$. A viscosity sub- (super-)solution is an $L$-viscosity sub- (super-)solution for some $L>0$.
--
--   **Paraboloids and semi-jets (4.4)–(4.6).** For $\mathcal F_t$-measurable continuous $Z,\Gamma$ with $|Z(\omega)|+|\Gamma(\omega)|\le C[1+\|\omega\|]$,
--   $$\phi^{t,y,v,Z,\Gamma}(s,\mathbb P)=y+v[s-t]+\mathbb E^{\mathbb P}\Big[Z\cdot X_{t,s}+\tfrac12\Gamma:[X_{t,s}X_{t,s}^\top]\Big],$$
--   with $\partial_t\phi=v$, $\partial_\mu\phi(s,\mathbb P,\omega)=Z(\omega)+\Gamma^{\rm sym}(\omega)X_{t,s}(\omega)$, $\partial_\omega\partial_\mu\phi=\Gamma$, where $\Gamma^{\rm sym}=\tfrac12[\Gamma+\Gamma^\top]$. The superjet is $\overline{\mathcal J}^LV(t,\mu)=\{(v,Z,\Gamma):\phi^{t,V(t,\mu),v,Z,\Gamma}\in\overline{\mathcal A}^LV(t,\mu)\}$ and the subjet $\underline{\mathcal J}^LV(t,\mu)$ uses $\underline{\mathcal A}^L$.
--
--   **Classical solutions (Definition 3.3).** $\varphi$ is a classical subsolution (supersolution) if $\mathbb L\varphi\ge0$ ($\le0$) on all of $\Theta$. The class standing for $C_b^{1,1,1}(\Theta)$ consists of data continuous on $\Theta$ that lie in $C_b^{1,1,1}([t_1,t_2]\times\mathcal P_L(t_1,\mu))$ for all $t_1<t_2\le T$, $L>0$, $\mu\in\mathcal P_2$ (Remark 4.3(i)).
--
--   **Formalization Note.** A $C^{1,1,1}$ object is a record of four functions (the function and its three derivatives); the predicates say they are the derivatives. The Itô formula is required in drift form for every representation $(\tilde\Omega,\tilde B,\tilde b,\tilde\sigma,\tilde X)$ of $\mathbb P$ from $t_1$: $\mathbb E^{\tilde{\mathbb P}}\int_{t_1}^s[\partial_\mu\varphi\cdot\tilde b_r+\tfrac12\partial_\omega\partial_\mu\varphi:\tilde\sigma_r\tilde\sigma_r^\top]dr$; this is the same number as (2.25), because $dX=\tilde b\,dr+\tilde\sigma\,d\tilde B$, $d\langle X\rangle=\tilde\sigma\tilde\sigma^\top dr$, and the stochastic integral of the square-integrable integrand $\partial_\mu\varphi^\top\tilde\sigma$ has mean zero. "$\inf(\varphi-V)=0$" is encoded literally: $\varphi-V\ge0$ on the set and takes values below every $\varepsilon>0$ there. The data at $(t,\mu)$ are required to be the (common) values at $(t,\mathbb P)$, $\mathbb P\in\mathcal P_L(t,\mu)$ — the paper's identification of $(t,\mu)$ with $(t,\mathbb P)$ when $\mathbb P_{[0,t]}=\mu_{[0,t]}$ (§2.2, adaptedness). $\partial_\omega\partial_\mu\phi=\Gamma$ follows (4.8); $G$ sees $\Gamma$ only through $\Gamma^{\rm sym}$ (Remark 3.2). The class standing for $C_b^{1,1,1}(\Theta)$ is the tube class described above: it contains $C_b^{1,1,1}(\Theta)$ of Definition 2.8 by Remark 4.3(i), so statements assuming it are at least as strong as printed. Definition 4.2 does not print the $\mathcal F_s$-measurability of $\partial_\mu\varphi(s,\mathbb P,\cdot)$ and $\partial_\omega\partial_\mu\varphi(s,\mathbb P,\cdot)$; it is required because $G$ is only defined on $\mathcal F_t$-measurable arguments ((3.1)), so that $\mathbb L\varphi$ is meaningful, and the derivatives of Theorem 2.2 have it ($\psi$ is $\widehat{\mathcal F}_t$-measurable). The linear-growth bound is required at $(s,\mathbb P)$ for $\mathbb P$-a.e. $\omega$, i.e. with the same law in the derivative and in the null set; this is the form the Itô formula uses.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Definition 3.3 p. 948; Definition 4.2, Remark 4.3, (4.2), Definition 4.4 p. 959; (4.4)–(4.6) pp. 960–961; (2.25) p. 946

import Mathlib
import Definitions.Def_MasterVisc_Comparison_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators Matrix

namespace MasterVisc.Comparison

open EthierKurtz

/-- Candidate derivative data of a `C^{1,1,1}` object: the function `fn`, its time derivative `dt`, its
path derivative `dmu` (`∂_μ`) and `dwdmu` (`∂_ω∂_μ`). The predicates below say when they are the
derivatives. -/
structure C111Data (d : ℕ) (T : ℝ≥0) where
  /-- the function `V(t, μ)` -/
  fn : ℝ≥0 → Measure (Path d T) → ℝ
  /-- `∂_t V(t, μ)` -/
  dt : ℝ≥0 → Measure (Path d T) → ℝ
  /-- `∂_μ V(t, μ, ω)` -/
  dmu : ℝ≥0 → Measure (Path d T) → Path d T → SDEState d
  /-- `∂_ω ∂_μ V(t, μ, ω)` -/
  dwdmu : ℝ≥0 → Measure (Path d T) → Path d T → Matrix (Fin d) (Fin d) ℝ

variable {d : ℕ} {T : ℝ≥0}

/-- `Φ ∈ C_b^{1,1,1}([t₁, t₂] × 𝒫)` (Definition 4.2, p. 959), on `S = {(s, ℙ) : t₁ ≤ s ≤ t₂, ℙ ∈ 𝒫}`:
(a) `Φ.fn`, `Φ.dt` continuous on `S`; (b) `Φ.dmu`, `Φ.dwdmu` continuous on `S × Ω`; (c) `Φ.dmu(s, ℙ, ·)`,
`Φ.dwdmu(s, ℙ, ·)` are `F_s`-measurable; (d) the functional Itô formula (2.25) on `[t₁, t₂]` under every
`ℙ ∈ 𝒫`, in drift form, for every representation of `ℙ` as an Itô process from `t₁`;
(e) `Φ.dt` bounded on `S`; (f) `|∂_μΦ| + |∂_ω∂_μΦ| ≤ C[1 + ‖ω‖]` `ℙ`-a.e. for `(s, ℙ) ∈ S`. -/
def IsC111b (t₁ t₂ : ℝ≥0) (Pset : Measure (Path d T) → Prop) (Φ : C111Data d T) : Prop :=
  IsC0On (fun s P => t₁ ≤ s ∧ s ≤ t₂ ∧ Pset P) Φ.fn ∧
  IsC0On (fun s P => t₁ ≤ s ∧ s ≤ t₂ ∧ Pset P) Φ.dt ∧
  IsC0OnΩ (fun s P => t₁ ≤ s ∧ s ≤ t₂ ∧ Pset P) Φ.dmu Φ.dwdmu ∧
  (∀ s P, t₁ ≤ s → s ≤ t₂ → Pset P →
    Measurable[filt s] (Φ.dmu s P) ∧ ∀ i j, Measurable[filt s] (fun ω => Φ.dwdmu s P ω i j)) ∧
  (∀ P, Pset P → ∀ R : Rep d T, IsRepFrom t₁ P R → ∀ s, t₁ ≤ s → s ≤ t₂ →
    Φ.fn s P - Φ.fn t₁ P =
      (∫ r in (t₁ : ℝ)..(s : ℝ), Φ.dt r.toNNReal P) +
      ∫ ω, (∫ r in (t₁ : ℝ)..(s : ℝ),
        (inner ℝ (Φ.dmu r.toNNReal P (R.Y ω)) (R.b r.toNNReal ω) +
          fdot (Φ.dwdmu r.toNNReal P (R.Y ω))
            (R.σ r.toNNReal ω * (R.σ r.toNNReal ω)ᵀ) / 2)) ∂(R.P')) ∧
  (∃ C : ℝ, ∀ s P, t₁ ≤ s → s ≤ t₂ → Pset P → |Φ.dt s P| ≤ C) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ s P, t₁ ≤ s → s ≤ t₂ → Pset P →
    ∀ᵐ ω ∂P, ‖Φ.dmu s P ω‖ + Real.sqrt (frob2 (Φ.dwdmu s P ω)) ≤ C * (1 + ‖ω‖))

/-- The operator of (3.1): `𝕃Φ(t, μ) = ∂_tΦ(t, μ) + G(t, μ, Φ(t, μ), ∂_μΦ(t, μ, ·), ∂_ω∂_μΦ(t, μ, ·))`. -/
def Lop (G : Gen d T) (Φ : C111Data d T) (t : ℝ≥0) (μ : Measure (Path d T)) : ℝ :=
  Φ.dt t μ + G t μ (Φ.fn t μ) (Φ.dmu t μ) (Φ.dwdmu t μ)

/-- The data of `Φ` at `(t, μ)` are its (common) values at `(t, ℙ)`, `ℙ ∈ 𝒫_L(t, μ)`: the identification of
`(t, μ)` with `(t, ℙ)` for `ℙ_{[0,t]} = μ_{[0,t]}` (§2.2, adaptedness). -/
def IsAnchored (L : ℝ) (t : ℝ≥0) (μ : Measure (Path d T)) (Φ : C111Data d T) : Prop :=
  ∀ P, InPL L t μ P →
    Φ.fn t P = Φ.fn t μ ∧ Φ.dt t P = Φ.dt t μ ∧ Φ.dmu t P = Φ.dmu t μ ∧ Φ.dwdmu t P = Φ.dwdmu t μ

/-- `Φ ∈ 𝒜̲^L V(t, μ)` (4.2): for some `0 < δ ≤ T − t`, `Φ ∈ C_b^{1,1,1}([t, t+δ] × 𝒫_L(t, μ))`,
`(Φ − V)(t, μ) = 0`, and `inf_{(s,ℙ) ∈ [t,t+δ] × 𝒫_L(t,μ)} (Φ − V)(s, ℙ) = 0`. -/
def InAsub (L : ℝ) (V : ℝ≥0 → Measure (Path d T) → ℝ) (t : ℝ≥0) (μ : Measure (Path d T))
    (Φ : C111Data d T) : Prop :=
  ∃ δ : ℝ≥0, 0 < δ ∧ t + δ ≤ T ∧ IsC111b t (t + δ) (InPL L t μ) Φ ∧ IsAnchored L t μ Φ ∧
    Φ.fn t μ = V t μ ∧
    (∀ s P, t ≤ s → s ≤ t + δ → InPL L t μ P → 0 ≤ Φ.fn s P - V s P) ∧
    (∀ ε > 0, ∃ s P, t ≤ s ∧ s ≤ t + δ ∧ InPL L t μ P ∧ Φ.fn s P - V s P < ε)

/-- `Φ ∈ 𝒜̄^L V(t, μ)` (4.2): as `InAsub`, with `sup (Φ − V) = 0`. -/
def InAsup (L : ℝ) (V : ℝ≥0 → Measure (Path d T) → ℝ) (t : ℝ≥0) (μ : Measure (Path d T))
    (Φ : C111Data d T) : Prop :=
  ∃ δ : ℝ≥0, 0 < δ ∧ t + δ ≤ T ∧ IsC111b t (t + δ) (InPL L t μ) Φ ∧ IsAnchored L t μ Φ ∧
    Φ.fn t μ = V t μ ∧
    (∀ s P, t ≤ s → s ≤ t + δ → InPL L t μ P → Φ.fn s P - V s P ≤ 0) ∧
    (∀ ε > 0, ∃ s P, t ≤ s ∧ s ≤ t + δ ∧ InPL L t μ P ∧ -ε < Φ.fn s P - V s P)

/-- `V` is an `L`-viscosity subsolution of (3.1) (Definition 4.4(i)). -/
def IsLViscSub (L : ℝ) (G : Gen d T) (V : ℝ≥0 → Measure (Path d T) → ℝ) : Prop :=
  IsC0Θ V ∧ ∀ t μ Φ, t ≤ T → IsP2 μ → InAsub L V t μ Φ → 0 ≤ Lop G Φ t μ

/-- `V` is an `L`-viscosity supersolution of (3.1) (Definition 4.4(i)). -/
def IsLViscSuper (L : ℝ) (G : Gen d T) (V : ℝ≥0 → Measure (Path d T) → ℝ) : Prop :=
  IsC0Θ V ∧ ∀ t μ Φ, t ≤ T → IsP2 μ → InAsup L V t μ Φ → Lop G Φ t μ ≤ 0

/-- `V` is an `L`-viscosity solution of (3.1) (Definition 4.4(ii)). -/
def IsLViscSol (L : ℝ) (G : Gen d T) (V : ℝ≥0 → Measure (Path d T) → ℝ) : Prop :=
  IsLViscSub L G V ∧ IsLViscSuper L G V

/-- `V` is a viscosity solution: an `L`-viscosity solution for one `L > 0` (Definition 4.4(ii)). -/
def IsViscSol (G : Gen d T) (V : ℝ≥0 → Measure (Path d T) → ℝ) : Prop :=
  ∃ L > 0, IsLViscSol L G V

/-- `V` is a viscosity subsolution: an `L`-viscosity subsolution for some `L > 0`. -/
def IsViscSub (G : Gen d T) (V : ℝ≥0 → Measure (Path d T) → ℝ) : Prop :=
  ∃ L > 0, IsLViscSub L G V

/-- `V` is a viscosity supersolution: an `L`-viscosity supersolution for some `L > 0`. -/
def IsViscSuper (G : Gen d T) (V : ℝ≥0 → Measure (Path d T) → ℝ) : Prop :=
  ∃ L > 0, IsLViscSuper L G V

/-- The increment `X_{t,s} = X_s − X_t` (2.4). -/
def incr (t s : ℝ≥0) (ω : Path d T) : SDEState d := evalAt s ω - evalAt t ω

/-- `Γ^{sym} = ½[Γ + Γ^⊤]`. -/
noncomputable def symm (Γ : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ := (1 / 2 : ℝ) • (Γ + Γᵀ)

/-- The paraboloid (4.4), `φ^{t,y,v,Z,Γ}(s, ℙ) = y + v[s − t] + 𝔼^ℙ[Z · X_{t,s} + ½Γ : X_{t,s}X_{t,s}^⊤]`,
with its derivatives `∂_tφ = v`, `∂_μφ(s, ℙ, ω) = Z(ω) + Γ^{sym}(ω) X_{t,s}(ω)`, `∂_ω∂_μφ = Γ` (cf. (4.5), (4.8)). -/
noncomputable def paraboloid (t : ℝ≥0) (y v : ℝ) (Z : Path d T → SDEState d)
    (Γ : Path d T → Matrix (Fin d) (Fin d) ℝ) : C111Data d T where
  fn s P := y + v * ((s : ℝ) - (t : ℝ)) +
    ∫ ω, (inner ℝ (Z ω) (incr t s ω) +
      fdot (Γ ω) (Matrix.vecMulVec (fun i => incr t s ω i) (fun i => incr t s ω i)) / 2) ∂P
  dt _ _ := v
  dmu s _ ω := Z ω + WithLp.toLp 2 (symm (Γ ω) *ᵥ (fun i => incr t s ω i))
  dwdmu _ _ ω := Γ ω

/-- The arguments of the semi-jets: `F_t`-measurable continuous `Z, Γ` with
`|Z(ω)| + |Γ(ω)| ≤ C[1 + ‖ω‖]` (p. 960). -/
def IsJetArg (t : ℝ≥0) (Z : Path d T → SDEState d) (Γ : Path d T → Matrix (Fin d) (Fin d) ℝ) :
    Prop :=
  IsGenArg t Z Γ ∧ IsLinGrowth Z Γ

/-- `(v, Z, Γ) ∈ 𝒥̲^L V(t, μ)` (4.6). -/
def InJsub (L : ℝ) (V : ℝ≥0 → Measure (Path d T) → ℝ) (t : ℝ≥0) (μ : Measure (Path d T)) (v : ℝ)
    (Z : Path d T → SDEState d) (Γ : Path d T → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  IsJetArg t Z Γ ∧ InAsub L V t μ (paraboloid t (V t μ) v Z Γ)

/-- `(v, Z, Γ) ∈ 𝒥̄^L V(t, μ)` (4.6). -/
def InJsup (L : ℝ) (V : ℝ≥0 → Measure (Path d T) → ℝ) (t : ℝ≥0) (μ : Measure (Path d T)) (v : ℝ)
    (Z : Path d T → SDEState d) (Γ : Path d T → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  IsJetArg t Z Γ ∧ InAsup L V t μ (paraboloid t (V t μ) v Z Γ)

/-- Continuity of all four data on the slab `I × 𝒫₂` (derivatives jointly with `ω`), with
`F_s`-measurable path derivatives. -/
def IsSlabC0 (I : Set ℝ≥0) (Φ : C111Data d T) : Prop :=
  IsC0On (fun s P => s ∈ I ∧ IsP2 P) Φ.fn ∧
  IsC0On (fun s P => s ∈ I ∧ IsP2 P) Φ.dt ∧
  IsC0OnΩ (fun s P => s ∈ I ∧ IsP2 P) Φ.dmu Φ.dwdmu ∧
  ∀ s P, s ∈ I → IsP2 P →
    Measurable[filt s] (Φ.dmu s P) ∧ ∀ i j, Measurable[filt s] (fun ω => Φ.dwdmu s P ω i j)

/-- The class standing for `C_b^{1,1,1}(Θ)`: data continuous on `Θ`, and in
`C_b^{1,1,1}([t₁, t₂] × 𝒫_L(t₁, μ))` for all `t₁ < t₂ ≤ T`, `L > 0`, `μ ∈ 𝒫₂` (Remark 4.3(i)). -/
def IsC111bTubes (Φ : C111Data d T) : Prop :=
  IsSlabC0 (Set.Iic T) Φ ∧
  ∀ t₁ t₂ L μ, t₁ < t₂ → t₂ ≤ T → 0 < L → IsP2 μ → IsC111b t₁ t₂ (InPL L t₁ μ) Φ

/-- `Φ` is a classical subsolution of (3.1) (Definition 3.3): `𝕃Φ ≥ 0` on `Θ`. -/
def IsClassicalSub (G : Gen d T) (Φ : C111Data d T) : Prop :=
  ∀ t μ, t ≤ T → IsP2 μ → 0 ≤ Lop G Φ t μ

/-- `Φ` is a classical supersolution of (3.1) (Definition 3.3): `𝕃Φ ≤ 0` on `Θ`. -/
def IsClassicalSuper (G : Gen d T) (Φ : C111Data d T) : Prop :=
  ∀ t μ, t ≤ T → IsP2 μ → Lop G Φ t μ ≤ 0

end MasterVisc.Comparison


