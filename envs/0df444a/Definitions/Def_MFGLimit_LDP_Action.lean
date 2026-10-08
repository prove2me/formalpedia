-- Prove2me | Definitions.Def_MFGLimit_LDP_Action
-- name    : MFGLimit_LDP_Action
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:34.145086+00:00
-- url     : https://prove2.me/theorems/43b81549-1b67-4df0-8f0a-ac23d6270cfd
-- title:
--   Action functionals: I (3.11), I^φ (6.4), Ĩ^φ (6.6), I^φ for continuous φ (6.7), J^{σ₀} (6.9) and p. 14, J̃^{σ₀,μ₀} (6.11), H¹
-- statement:
--   The Dawson–Gärtner action functionals and the rate functions of §3.2 and §6.1.
--
--   A distribution-valued path $t\mapsto\nu_t$ on $[0,T]$ is **absolutely continuous** if for each compact $K\subset\mathbb R^d$ there are a neighbourhood $U_K$ of $0$ in $C_K(\mathbb R^d)$ (smooth functions supported in $K$) and an absolutely continuous $\delta_K:[0,T]\to\mathbb R$ with $|\langle\nu_t,f\rangle-\langle\nu_s,f\rangle|\le|\delta_K(t)-\delta_K(s)|$ for $s,t\in[0,T]$, $f\in U_K$. Its time derivative $\dot\nu_t$ is a distribution-valued function with $\langle\nu_t,h\rangle-\langle\nu_s,h\rangle=\int_s^t\langle\dot\nu_r,h\rangle dr$ for test functions $h\in C^\infty_c(\mathbb R^d)$. For $m\in\mathcal P^1(\mathbb R^d)$ the seminorm of a distribution $\gamma$ is
--   $$\|\gamma\|_m^2=\sup_{h\in C^\infty_c(\mathbb R^d),\ \langle m,|Dh|^2\rangle\ne0}\frac{\langle\gamma,h\rangle^2}{\langle m,|Dh|^2\rangle}.$$
--   With $\mathcal L_{t,m}h(x)=\frac12\mathrm{Tr}[\sigma\sigma^\top D^2h(x)]+Dh(x)\cdot\tilde b(t,x,m)$ (3.11)/(6.5) and $\mathcal L^*$ its formal adjoint:
--
--   1. $I(\nu)=\frac12\int_0^T\|\dot\nu_t-\mathcal L^*_{t,\nu_t}\nu_t\|^2_{\nu_t}dt$ if $\nu$ is absolutely continuous, $\infty$ otherwise (3.11);
--   2. for $\phi\in\mathcal H^1([0,T];\mathbb R^d)$, $I^\phi(\nu)=\frac12\int_0^T\|\dot\nu_t-\mathcal L^*_{t,\nu_t}\nu_t+\mathrm{div}(\nu_t\dot\phi_t)\|^2_{\nu_t}dt$ (or $\infty$) (6.4); $I^0=I^\phi$ for $\phi\equiv0$;
--   3. $\tilde I^\phi$ is (3.11) with $\tilde b$ replaced by $(t,x,m)\mapsto\tilde b(t,x+\phi_t,m\circ\tau^{-1}_{-\phi_t})$ (6.6);
--   4. for continuous $\phi$ with $\phi_0=0$, $I^\phi(\nu):=\tilde I^\phi((\nu_t\circ\tau^{-1}_{\phi_t})_t)$ (the extension through (6.7));
--   5. $J^{\sigma_0}(\nu)=\inf_{\phi\in\mathcal C^{d_0}_0}I^{\sigma_0\phi}(\nu)$ (6.9);
--   6. with $\Pi_{\sigma^{-1}\sigma_0}$ the orthogonal projection onto the image of $\sigma^{-1}\sigma_0$ and $\mathbb M^{\tilde b,\nu}_t=\sigma\Pi_{\sigma^{-1}\sigma_0}\sigma^{-1}\big(\mathbb M^\nu_t-\mathbb M^\nu_0-\int_0^t\langle\nu_s,\tilde b(s,\cdot,\nu_s)\rangle ds\big)$, the p. 14 form $J^{\sigma_0}(\nu)=\tilde I^{\mathbb M^{\tilde b,\nu}}((\nu_t\circ\tau^{-1}_{\mathbb M^{\tilde b,\nu}_t})_t)$;
--   7. $\tilde J^{\sigma_0,\mu_0}(\nu)=J^{\sigma_0}(\nu)+\mathcal R(\nu_0|\mu_0)$ (6.11), $\mathcal R$ the relative entropy (3.6).
--
--   $\mathcal H^1([0,T];\mathbb R^k)$ consists of absolutely continuous $\phi$ with square-integrable derivative, normed by $\|\phi\|_{\mathcal H^1}=(\int_0^T|\phi|^2)^{1/2}+(\int_0^T|\dot\phi|^2)^{1/2}$.
--
--   **Formalization Note** Test functions and distributions are Mathlib's `TestFunction` and `Distribution` on $\mathbb R^d$; $C_K$ carries Mathlib's topology on `ContDiffMapSupportedIn`. The action takes the infimum over all distributional time derivatives $\dot\nu$ (unique up to null sets of times), so no choice is made. Common-noise paths $\phi$ are $d_0$-dimensional, as $\sigma_0\phi$ requires. The (6.9) form `Jinf` and the p. 14 form `Jexplicit` are separate definitions, related only by Theorem 6.6. $\mathcal R$ is Mathlib's `klDiv` ($\infty$ unless absolutely continuous).
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, pp. 13–14, (3.11); pp. 25–28, (6.4), (6.6), (6.7), (6.9), (6.11), Theorem 6.6

import Mathlib
import Definitions.Def_MFGLimit_LDP_Model
import Definitions.Def_MFGLimit_LDP_PathSpace

open MeasureTheory Filter Topology Distributions
open scoped ENNReal NNReal

namespace MFGLimit.LDP

variable {d d₀ : ℕ} {T : ℝ≥0}

/-- The test functions `C_c^∞(ℝ^d)`. -/
abbrev TestFn (d : ℕ) := TestFunction (⊤ : TopologicalSpace.Opens (MFGLimit.Conc.E d)) ℝ (⊤ : ℕ∞)

/-- The Schwartz distributions `𝓓'(ℝ^d)` (continuous linear functionals on `C_c^∞(ℝ^d)`). -/
abbrev Distr (d : ℕ) := Distribution (⊤ : TopologicalSpace.Opens (MFGLimit.Conc.E d)) ℝ (⊤ : ℕ∞)

/-- §3.2, p. 13: the distribution-valued path `t ↦ ν_t` is absolutely continuous: for each compact
`K ⊂ ℝ^d` there are a neighbourhood `U_K` of `0` in `C_K(ℝ^d)` (smooth functions supported in `K`,
with their Fréchet topology) and an absolutely continuous `δ_K : [0, T] → ℝ` with
`|⟨ν_t, f⟩ − ⟨ν_s, f⟩| ≤ |δ_K(t) − δ_K(s)|` for all `s, t ∈ [0, T]`, `f ∈ U_K`. -/
def IsAbsContFlow (ν : Flow d T) : Prop :=
  ∀ K : TopologicalSpace.Compacts (MFGLimit.Conc.E d),
    ∃ U : Set (ContDiffMapSupportedIn (MFGLimit.Conc.E d) ℝ (⊤ : ℕ∞) K), U ∈ 𝓝 0 ∧
      ∃ δK : ℝ → ℝ, AbsolutelyContinuousOnInterval δK 0 T ∧
        ∀ s t : Set.Icc (0 : ℝ≥0) T, ∀ f ∈ U,
          |∫ x, f x ∂(ν t) - ∫ x, f x ∂(ν s)| ≤ |δK (t : ℝ) - δK (s : ℝ)|

/-- `γ = (γ_r)_{r ∈ [0, T]}` is a time derivative `ν̇` of the flow, in the distributional sense
(Dawson–Gärtner): for every test function `h`, `r ↦ ⟨γ_r, h⟩` is integrable on `[0, T]` and
`⟨ν_t, h⟩ − ⟨ν_s, h⟩ = ∫_s^t ⟨γ_r, h⟩ dr` for `0 ≤ s ≤ t ≤ T`. -/
def IsTimeDeriv (ν : Flow d T) (γ : ℝ → Distr d) : Prop :=
  ∀ h : TestFn d, IntervalIntegrable (fun r => γ r h) volume 0 T ∧
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      ∫ x, h x ∂(flowAt ν t) - ∫ x, h x ∂(flowAt ν s) = ∫ r in s..t, γ r h

/-- The seminorm `‖Λ‖²_m = sup { ⟨Λ, h⟩² / ⟨m, |Dh|²⟩ : h ∈ C_c^∞(ℝ^d), ⟨m, |Dh|²⟩ ≠ 0 }` (p. 13),
in `[0, ∞]`, of a functional `Λ` on test functions. -/
noncomputable def seminormSq (m : Measure (MFGLimit.Conc.E d)) (Λ : TestFn d → ℝ) : ℝ≥0∞ :=
  ⨆ (h : TestFn d) (_ : ∫ x, ‖gradient h x‖ ^ 2 ∂m ≠ 0),
    ENNReal.ofReal ((Λ h) ^ 2 / ∫ x, ‖gradient h x‖ ^ 2 ∂m)

/-- The generator `L h(x) = ½ Tr[σσᵀ D²h(x)] + Dh(x) · β(x)` for a drift field `β`. -/
noncomputable def gen (σ : Matrix (Fin d) (Fin d) ℝ) (β : MFGLimit.Conc.E d → MFGLimit.Conc.E d) (h : TestFn d) (x : MFGLimit.Conc.E d) :
    ℝ :=
  (1 / 2) * trMul (σ * σ.transpose) (hessE h x) + inner ℝ (gradient h x) (β x)

open Classical in
/-- The action functional with drift `β(r, x, m)` and an extra velocity `w_r`:
`½ ∫₀ᵀ ‖ν̇_r − L*_{r,ν_r} ν_r + div(ν_r w_r)‖²_{ν_r} dr` if `ν` is absolutely continuous, `∞` otherwise,
where `L_{r,m} h = ½ Tr[σσᵀ D²h] + Dh · β(r, ·, m)`, so that for a test function `h`
`⟨ν̇_r − L*_{r,ν_r} ν_r + div(ν_r w_r), h⟩ = ⟨ν̇_r, h⟩ − ⟨ν_r, L_{r,ν_r} h⟩ − ⟨ν_r, w_r · Dh⟩`. The
derivative `ν̇` is any distributional time derivative; the infimum over them is the value
(a.e. unique, Dawson–Gärtner [18, Lemma 4.2]). -/
noncomputable def action (σ : Matrix (Fin d) (Fin d) ℝ) (β : ℝ → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d)
    (w : ℝ → MFGLimit.Conc.E d) (ν : Flow d T) : ℝ≥0∞ :=
  if IsAbsContFlow ν then
    ⨅ (γ : ℝ → Distr d) (_ : IsTimeDeriv ν γ),
      (1 / 2 : ℝ≥0∞) * ∫⁻ r in Set.Icc (0 : ℝ) T, seminormSq (flowAt ν r) (fun h =>
        γ r h - (∫ x, gen σ (fun y => β r y (flowAt ν r)) h x ∂(flowAt ν r))
          - ∫ x, inner ℝ (w r) (gradient h x) ∂(flowAt ν r))
  else ⊤

/-- The rate function `I` of (3.11) for the drift `b̃`. -/
noncomputable def Iact (σ : Matrix (Fin d) (Fin d) ℝ) (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d)
    (ν : Flow d T) : ℝ≥0∞ :=
  action σ (fun r x m => btil r.toNNReal x m) (fun _ => 0) ν

/-- `I^φ` of (6.4), for `φ ∈ H¹([0, T]; ℝ^d)`: the extra term `+ div(ν_t φ̇_t)` with `φ̇` the
derivative of `φ` (defined a.e.). `I⁰ = I^φ` for `φ ≡ 0`. -/
noncomputable def IphiH1 (σ : Matrix (Fin d) (Fin d) ℝ)
    (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d) (φ : ℝ → MFGLimit.Conc.E d) (ν : Flow d T) : ℝ≥0∞ :=
  action σ (fun r x m => btil r.toNNReal x m) (fun r => deriv φ r) ν

/-- The shifted drift `(t, x, m) ↦ b̃(t, x + φ_t, m ∘ τ_{−φ_t}^{-1})`, `τ_{−y}(z) = z + y`. -/
noncomputable def shiftDrift (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d) (φ : ℝ → MFGLimit.Conc.E d) :
    ℝ → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d :=
  fun r x m => btil r.toNNReal (x + φ r) (m.map (fun z => z + φ r))

/-- `Ĩ^φ` of (6.6) (also p. 14): the action functional for the shifted drift. -/
noncomputable def Itil (σ : Matrix (Fin d) (Fin d) ℝ) (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d)
    (φ : ℝ → MFGLimit.Conc.E d) (ν : Flow d T) : ℝ≥0∞ :=
  action σ (shiftDrift btil φ) (fun _ => 0) ν

/-- `I^φ` for a continuous path `φ` with `φ_0 = 0`, defined through (6.7) (p. 27):
`I^φ(ν) := Ĩ^φ((ν_t ∘ τ_{φ_t}^{-1})_t)`. -/
noncomputable def Iphi (σ : Matrix (Fin d) (Fin d) ℝ) (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d)
    (φ : ℝ → MFGLimit.Conc.E d) (ν : Flow d T) : ℝ≥0∞ :=
  Itil σ btil φ (shiftFlow ν φ)

/-- `J^{σ₀}` of (6.9): `J^{σ₀}(ν) = inf_{φ ∈ C^{d₀}_0} I^{σ₀φ}(ν)` (common-noise paths are
`d₀`-dimensional). -/
noncomputable def Jinf (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d) (ν : Flow d T) : ℝ≥0∞ :=
  ⨅ φ : C0T d₀ T, Iphi σ btil (fun r => matVec σ₀ ((φ : CPath d₀ T).atR r)) ν

/-- `Π_{σ^{-1}σ₀}`: the orthogonal projection of `ℝ^d` onto the image of `σ^{-1}σ₀`. -/
noncomputable def projRange (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ) :
    MFGLimit.Conc.E d →L[ℝ] MFGLimit.Conc.E d :=
  (LinearMap.range (Matrix.toEuclideanLin (σ⁻¹ * σ₀))).starProjection

/-- `𝕄^{b̃,ν}_t = σ Π_{σ^{-1}σ₀} σ^{-1} (𝕄^ν_t − 𝕄^ν_0 − ∫₀ᵗ ⟨ν_s, b̃(s, ·, ν_s)⟩ ds)`
(p. 14 and Theorem 6.6). -/
noncomputable def Mbt (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d) (ν : Flow d T) (t : ℝ) : MFGLimit.Conc.E d :=
  matVec σ (projRange σ σ₀ (matVec σ⁻¹ (meanPath ν t - meanPath ν 0
    - ∫ s in Set.Icc (0 : ℝ) t, ∫ x, btil s.toNNReal x (flowAt ν s) ∂(flowAt ν s))))

/-- The rate functional of p. 14: `J^{σ₀}(ν) = Ĩ^{𝕄^{b̃,ν}}((ν_t ∘ τ^{-1}_{𝕄^{b̃,ν}_t})_t)`. -/
noncomputable def Jexplicit (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d) (ν : Flow d T) : ℝ≥0∞ :=
  Itil σ btil (Mbt σ σ₀ btil ν) (shiftFlow ν (Mbt σ σ₀ btil ν))

/-- `J̃^{σ₀,μ₀}(ν) = J^{σ₀}(ν) + R(ν_0 | μ₀)` (6.11), with `J^{σ₀}` from (6.9). -/
noncomputable def rateTilde (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d) (μ₀ : Measure (MFGLimit.Conc.E d)) (ν : PathP1 d T) : ℝ≥0∞ :=
  Jinf σ σ₀ btil ν.ν + InformationTheory.klDiv (ν.ν (t0 T)) μ₀

/-- `ν ↦ J^{σ₀}(ν) + R(ν_0 | μ₀)` with the p. 14 form of `J^{σ₀}` (rate of Theorem 3.10). -/
noncomputable def rateExplicit (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d) (μ₀ : Measure (MFGLimit.Conc.E d)) (ν : PathP1 d T) : ℝ≥0∞ :=
  Jexplicit σ σ₀ btil ν.ν + InformationTheory.klDiv (ν.ν (t0 T)) μ₀

/-- `φ ∈ H¹([0, T]; ℝ^k)`: absolutely continuous on `[0, T]` with square-integrable derivative. -/
def IsH1 (T : ℝ≥0) {k : ℕ} (φ : ℝ → MFGLimit.Conc.E k) : Prop :=
  AbsolutelyContinuousOnInterval φ 0 T ∧ ∫⁻ r in Set.Icc (0 : ℝ) T, ‖deriv φ r‖ₑ ^ 2 < ⊤

/-- `‖φ‖_{H¹} = (∫₀ᵀ |φ(t)|² dt)^{1/2} + (∫₀ᵀ |φ̇(t)|² dt)^{1/2}` (p. 26). -/
noncomputable def H1norm (T : ℝ≥0) {k : ℕ} (φ : ℝ → MFGLimit.Conc.E k) : ℝ :=
  Real.sqrt (∫ r in Set.Icc (0 : ℝ) T, ‖φ r‖ ^ 2) + Real.sqrt (∫ r in Set.Icc (0 : ℝ) T, ‖deriv φ r‖ ^ 2)

end MFGLimit.LDP


