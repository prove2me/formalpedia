-- Prove2me | Definitions.Def_ReflectedBSDE_StoppingControl_Control
-- name    : ReflectedBSDE_StoppingControl_Control
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:10:33.278252+00:00
-- url     : https://prove2.me/theorems/cb554e80-3832-477d-9e97-8102e89c6183
-- title:
--   §7 — conjugate $F$, domain $D^F_t$, admissible controls $\mathcal A$, affine coefficient $f^{\beta,\gamma}$, $\Gamma^{\beta,\gamma}_{t,s}$ and the payoff $\Phi(t,v,\beta,\gamma)$
-- statement:
--   In the setting of `ReflectedBSDE.StoppingControl.Setting`, let $f(\omega,t,y,z)$ be a coefficient. This file fixes the objects of §7.
--
--   1. The **conjugate function** $$F(\omega,t,\beta,\gamma)=\sup_{(y,z)\in\mathbb R\times\mathbb R^d}\big[f(\omega,t,y,z)-\beta y-\langle\gamma,z\rangle\big]\in(-\infty,+\infty],$$ and its **domain** $D^F_t(\omega)=\{(\beta,\gamma)\in\mathbb R\times\mathbb R^d: F(\omega,t,\beta,\gamma)<\infty\}$.
--   2. The class $\mathcal A$ of **admissible controls**: bounded progressively measurable $\mathbb R\times\mathbb R^d$-valued processes $(\beta_t,\gamma_t)_{0\le t\le T}$ with $$E\int_0^T F(t,\beta_t,\gamma_t)^2\,dt<\infty.$$
--   3. The **affine coefficient** $f^{\beta,\gamma}(t,y,z)=F(t,\beta_t,\gamma_t)+\beta_ty+\langle\gamma_t,z\rangle$.
--   4. The solution $\Gamma^{\beta,\gamma}_{t,s}$, $t\le s\le T$, of the linear SDE $d\Gamma_{t,s}=\Gamma_{t,s}(\beta_s\,ds+(\gamma_s,dB_s))$, $\Gamma_{t,t}=1$, written in closed form $$\Gamma^{\beta,\gamma}_{t,s}=\exp\Big(\int_t^s\beta_r\,dr+\int_t^s(\gamma_r,dB_r)-\tfrac12\int_t^s|\gamma_r|^2\,dr\Big).$$ The process $\Gamma_s=\Gamma_{0,s}$ is the one of Proposition 7.1.
--   5. The **payoff** of Proposition 7.1 for an affine coefficient $\delta_t+\beta_ty+\langle\gamma_t,z\rangle$ and a stopping time $v$, $$\Gamma_v\xi 1_{\{v=T\}}+\Gamma_vS_v1_{\{v<T\}}+\int_t^v\Gamma_s\delta_s\,ds,$$ and the payoff of Theorem 7.2, $$\Phi(t,v,\beta,\gamma)=\Gamma^{\beta,\gamma}_{t,v}\big[S_v1_{\{v<T\}}+\xi1_{\{v=T\}}\big]+\int_t^v\Gamma^{\beta,\gamma}_{t,s}F(s,\beta_s,\gamma_s)\,ds.$$
--
--   With a concave coefficient, $Y_t$ is the value of the stopping–control game whose payoff is $\Phi$ and whose controls range over $\mathcal A$.
--
--   **Formalization Note** $F$ is computed in the extended reals, so an unbounded supremum is $+\infty$ rather than a junk value. $F^2$ in the definition of $\mathcal A$ is computed in $[0,\infty]$ with $|{+\infty}|^2=+\infty$, so finiteness of the integral forces $F(t,\beta_t,\gamma_t)<\infty$ for $dt\times dP$-a.e. $(t,\omega)$; elsewhere $F$ enters $f^{\beta,\gamma}$ and $\Phi$ as a real number, the value on that null set being immaterial. "Bounded" means one constant $C$ with $|\beta_t(\omega)|+|\gamma_t(\omega)|\le C$ for all $t\le T$ and all $\omega$. $\Gamma$ is the Doléans-Dade exponential, which is the unique solution of the linear SDE by Itô's formula; the stochastic integral $\int_t^s(\gamma_r,dB_r)$ is $\sum_j(J_j(s)-J_j(t))$ for Itô integrals $J_j$ of $\gamma^j$ against $B^j$ with continuous paths (`IsContItoIntegral`), which the theorems take as given.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 724 (Proposition 7.1; F and D^F_t) and p. 725 (𝒜, f^{β,γ}, Theorem 7.2: Φ and Γ^{β,γ}), https://doi.org/10.1214/aop/1024404416

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_StoppingControl_Setting

namespace ReflectedBSDE.StoppingControl

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A control: a pair of processes `(β_t, γ_t)` valued in `ℝ × ℝ^d`. -/
abbrev Control (Ω : Type*) (d : ℕ) : Type _ :=
  (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → Fin d → ℝ)

/-- §7, p. 724: the conjugate function
`F(ω, t, β, γ) = sup_{(y, z) ∈ ℝ × ℝ^d} [f(ω, t, y, z) − βy − ⟨γ, z⟩]`, valued in `(−∞, +∞]`
(computed in `EReal`, so an unbounded supremum is `+∞`). -/
noncomputable def conj {d : ℕ} (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (ω : Ω) (t : ℝ≥0)
    (β : ℝ) (γ : Fin d → ℝ) : EReal :=
  ⨆ (y : ℝ) (z : Fin d → ℝ), ((f t ω y z - β * y - dot γ z : ℝ) : EReal)

/-- §7, p. 724: `D^F_t(ω) = {(β, γ) ∈ ℝ × ℝ^d : F(ω, t, β, γ) < ∞}`. -/
def conjDomain {d : ℕ} (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (ω : Ω) (t : ℝ≥0) :
    Set (ℝ × (Fin d → ℝ)) :=
  {p | conj f ω t p.1 p.2 < ⊤}

/-- §7, p. 725: the class `𝒜` of bounded progressively measurable `ℝ × ℝ^d`-valued processes
`(β_t, γ_t)` with `E ∫₀ᵀ F(t, β_t, γ_t)² dt < ∞`. Boundedness: one constant `C` with
`|β_t(ω)| + |γ_t(ω)| ≤ C` for all `t ∈ [0, T]` and all `ω`. The square of the extended real
`F` is taken in `ℝ≥0∞` with `|+∞|² = +∞`, so the finiteness of the integral forces
`F(t, β_t, γ_t) < ∞` for `dt × dP`-a.e. `(t, ω)`. -/
def admissible {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) : Set (Control Ω d) :=
  {c | IsStronglyProgressive 𝓕 c.1 ∧ IsStronglyProgressive 𝓕 c.2 ∧
    (∃ C : ℝ, ∀ t ≤ T, ∀ ω, |c.1 t ω| + eucNorm (c.2 t ω) ≤ C) ∧
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      EReal.abs (conj f ω s.toNNReal (c.1 s.toNNReal ω) (c.2 s.toNNReal ω)) ^ 2 ∂volume ∂P < ⊤}

/-- §7, p. 725: the affine coefficient
`f^{β,γ}(t, y, z) = F(t, β_t, γ_t) + β_t y + ⟨γ_t, z⟩` (with `F` read as a real number; on the
`dt × dP`-null set where `F(t, β_t, γ_t) = +∞` for `(β, γ) ∈ 𝒜` the value used is `0`). -/
noncomputable def affineCoeff {d : ℕ} (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (c : Control Ω d) :
    ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ :=
  fun t ω y z => (conj f ω t (c.1 t ω) (c.2 t ω)).toReal + c.1 t ω * y + dot (c.2 t ω) z

/-- `J = (J₁, …, J_d)` are Itô integrals `Jⱼ = ∫₀^· γʲ_s dBʲ_s` on `[0, T]` (in the sense of
`Peng1990.SMP.IsItoIntegral`) whose paths are continuous on `[0, T]` for every `ω`
(a continuous version). -/
def IsContItoIntegral {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (γ : ℝ≥0 → Ω → Fin d → ℝ) (J : Fin d → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ j, Peng1990.SMP.IsItoIntegral 𝓕 P T (fun s ω => B s ω j) (fun s ω => γ s ω j) (J j) ∧
    ∀ ω, ContinuousOn (fun s => J j s ω) (Set.Iic T)

/-- The solution `Γ_{t,s}`, `t ≤ s ≤ T`, of the linear SDE
`dΓ_{t,s} = Γ_{t,s}(β_s ds + (γ_s, dB_s))`, `Γ_{t,t} = 1`, in closed (Doléans-Dade) form
`Γ_{t,s} = exp(∫ₜˢ β_r dr + Σⱼ (Jⱼ(s) − Jⱼ(t)) − ½ ∫ₜˢ |γ_r|² dr)`, where `Jⱼ = ∫₀^· γʲ dBʲ`.
`Γ_{0,s}` is the process `Γ_s` of Proposition 7.1. -/
noncomputable def linGamma {d : ℕ} (β : ℝ≥0 → Ω → ℝ) (γ : ℝ≥0 → Ω → Fin d → ℝ)
    (J : Fin d → ℝ≥0 → Ω → ℝ) (t s : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp ((∫ r in Set.Icc (t : ℝ) s, β r.toNNReal ω) + ∑ j, (J j s ω - J j t ω)
    - (1 / 2) * ∫ r in Set.Icc (t : ℝ) s, ∑ j, γ r.toNNReal ω j ^ 2)

/-- Proposition 7.1, p. 724: the payoff
`Γ_v ξ 1_{v=T} + Γ_v S_v 1_{v<T} + ∫ₜᵛ Γ_s δ_s ds` of the stopping time `v`, with `Γ_s = Γ_{0,s}`. -/
noncomputable def affinePayoff {d : ℕ} (T : ℝ≥0) (ξ : Ω → ℝ) (S δ β : ℝ≥0 → Ω → ℝ)
    (γ : ℝ≥0 → Ω → Fin d → ℝ) (J : Fin d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (v : Ω → ℝ≥0) (ω : Ω) : ℝ :=
  linGamma β γ J 0 (v ω) ω * ξ ω * (if v ω = T then 1 else 0)
    + linGamma β γ J 0 (v ω) ω * S (v ω) ω * (if v ω < T then 1 else 0)
    + ∫ s in Set.Icc (t : ℝ) (v ω), linGamma β γ J 0 s.toNNReal ω * δ s.toNNReal ω

/-- Theorem 7.2, p. 725: the payoff
`Φ(t, v, β, γ) = Γ^{β,γ}_{t,v}[S_v 1_{v<T} + ξ 1_{v=T}] + ∫ₜᵛ Γ^{β,γ}_{t,s} F(s, β_s, γ_s) ds`,
where `J` are the Itô integrals of `γ` defining `Γ^{β,γ}` (`F` read as a real number). -/
noncomputable def payoff {d : ℕ} (T : ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (S : ℝ≥0 → Ω → ℝ) (c : Control Ω d) (J : Fin d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (v : Ω → ℝ≥0)
    (ω : Ω) : ℝ :=
  linGamma c.1 c.2 J t (v ω) ω
      * (S (v ω) ω * (if v ω < T then 1 else 0) + ξ ω * (if v ω = T then 1 else 0))
    + ∫ s in Set.Icc (t : ℝ) (v ω),
        linGamma c.1 c.2 J t s.toNNReal ω
          * (conj f ω s.toNNReal (c.1 s.toNNReal ω) (c.2 s.toNNReal ω)).toReal

end ReflectedBSDE.StoppingControl


