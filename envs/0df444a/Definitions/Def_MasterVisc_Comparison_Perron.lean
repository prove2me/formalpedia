-- Prove2me | Definitions.Def_MasterVisc_Comparison_Perron
-- name    : MasterVisc_Comparison_Perron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:47:35.724412+00:00
-- url     : https://prove2.me/theorems/0e07d763-d529-460b-9f12-2600c5c6bc3a
-- title:
--   (4.17)–(4.18) — the Perron classes 𝒰, 𝒰̄_g, 𝒰̲_g and the envelopes V̄, V̲
-- statement:
--   Let $g\in C^0(\mathcal P_2;\mathbb R)$ be a terminal condition. The class $\mathcal U$ consists of the adapted functions $\psi:\Theta\to\mathbb R$, continuous in $\mu$ and càdlàg in $t$, for which there is a partition $0=t_0<\dots<t_n=T$ such that $\psi\in C_b^{1,1,1}([t_i,t_{i+1})\times\mathcal P_L(t_i,\mu))$ for all $t_i$, $\mu\in\mathcal P_2$ and $L>0$. Then (4.18)
--   $$\overline{\mathcal U}_g=\{\psi\in\mathcal U:\ \psi(T,\cdot)\ge g,\ \psi_{t_i}\le\psi_{t_i-},\ \psi\text{ is a classical supersolution of (3.1) on each }[t_{i-1},t_i)\},$$
--   $$\underline{\mathcal U}_g=\{\psi\in\mathcal U:\ \psi(T,\cdot)\le g,\ \psi_{t_i}\ge\psi_{t_i-},\ \psi\text{ is a classical subsolution of (3.1) on each }[t_{i-1},t_i)\},$$
--   and the Perron envelopes (4.17) are
--   $$\overline V(t,\mu)=\inf\{\psi(t,\mu):\psi\in\overline{\mathcal U}_g\},\qquad \underline V(t,\mu)=\sup\{\psi(t,\mu):\psi\in\underline{\mathcal U}_g\}.$$
--
--   These piecewise classical sub- and supersolutions bracket every viscosity solution, which is how uniqueness is obtained in Theorem 4.13.
--
--   **Formalization Note.** A member of $\mathcal U$ comes with its partition and, on each piece, the derivative data of $\psi$; $\overline{\mathcal U}_g$ and $\underline{\mathcal U}_g$ refer to that same partition. "$\psi\in C_b^{1,1,1}([t_i,t_{i+1})\times\mathcal P_L(t_i,\mu))$" on the half-open piece is read as membership in $C_b^{1,1,1}([t_i,s]\times\mathcal P_L(t_i,\mu))$ for every $s\in(t_i,t_{i+1})$ (the bounds may depend on $s$). The piece data are moreover required to be continuous on $[t_i,t_{i+1})\times\mathcal P_2$, so that the classical inequality $\mathbb L\psi\gtrless0$ "for all $(t,\mu)$" in the piece is about well-defined derivatives at every $\mathcal P_2$ law and not only at semimartingale laws. $\psi_{t_i-}$ is the left limit in $t$ for each fixed $\mu$, for $i\ge1$. The envelopes take values in the extended reals: $\overline V=+\infty$ if $\overline{\mathcal U}_g=\emptyset$, $\underline V=-\infty$ if $\underline{\mathcal U}_g=\emptyset$; statements use them only through equality with a real-valued function.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), §4.5, (4.17)–(4.18), pp. 964–965

import Mathlib
import Definitions.Def_MasterVisc_Comparison_Setting
import Definitions.Def_MasterVisc_Comparison_Viscosity

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace MasterVisc.Comparison

/-- Piecewise data of a member of `𝒰` (4.17): a partition `0 = τ₀ < ⋯ < τₙ = T` and, for each piece
`[τᵢ, τᵢ₊₁)`, the `C^{1,1,1}` data of `ψ` there. -/
structure PWData (d : ℕ) (T : ℝ≥0) where
  /-- the number of pieces -/
  n : ℕ
  /-- the partition points `τ₀, …, τₙ` -/
  τ : Fin (n + 1) → ℝ≥0
  /-- the derivative data on the `i`-th piece `[τᵢ, τᵢ₊₁)` -/
  Φ : Fin n → C111Data d T

variable {d : ℕ} {T : ℝ≥0}

/-- `ψ ∈ 𝒰` with partition data `D` (4.17): `ψ` is adapted, continuous in `μ`, càdlàg in `t`;
`0 = τ₀ < ⋯ < τₙ = T`; and on each piece `[τᵢ, τᵢ₊₁)` `ψ` coincides with `D.Φ i`, whose data are
continuous on `[τᵢ, τᵢ₊₁) × 𝒫₂` and which is in `C_b^{1,1,1}([τᵢ, s] × 𝒫_L(τᵢ, μ))` for every
`s ∈ (τᵢ, τᵢ₊₁)`, `μ ∈ 𝒫₂`, `L > 0`. -/
def InU (ψ : ℝ≥0 → Measure (Path d T) → ℝ) (D : PWData d T) : Prop :=
  StrictMono D.τ ∧ D.τ 0 = 0 ∧ D.τ (Fin.last D.n) = T ∧
  IsAdaptedΘ ψ ∧
  (∀ t, t ≤ T → IsC0On (fun s P => s = t ∧ IsP2 P) ψ) ∧
  (∀ μ, IsP2 μ →
    (∀ s, s < T → ContinuousWithinAt (fun r => ψ r μ) (Set.Ici s) s) ∧
    (∀ s, 0 < s → s ≤ T → ∃ l : ℝ, Tendsto (fun r => ψ r μ) (𝓝[<] s) (𝓝 l))) ∧
  ∀ i : Fin D.n,
    (∀ s P, D.τ i.castSucc ≤ s → s < D.τ i.succ → IsP2 P → (D.Φ i).fn s P = ψ s P) ∧
    IsSlabC0 (Set.Ico (D.τ i.castSucc) (D.τ i.succ)) (D.Φ i) ∧
    ∀ s L μ, D.τ i.castSucc < s → s < D.τ i.succ → 0 < L → IsP2 μ →
      IsC111b (D.τ i.castSucc) s (InPL L (D.τ i.castSucc) μ) (D.Φ i)

/-- `ψ ∈ 𝒰̄_g` (4.18): `ψ ∈ 𝒰`, `ψ(T, ·) ≥ g`, `ψ_{τᵢ} ≤ ψ_{τᵢ−}` for `i ≥ 1`, and on each `[τᵢ, τᵢ₊₁)`
`ψ` is a classical supersolution of (3.1). -/
def InUbar (G : Gen d T) (g : Measure (Path d T) → ℝ) (ψ : ℝ≥0 → Measure (Path d T) → ℝ)
    (D : PWData d T) : Prop :=
  InU ψ D ∧ (∀ μ, IsP2 μ → g μ ≤ ψ T μ) ∧
  (∀ i : Fin (D.n + 1), 0 < i → ∀ μ, IsP2 μ →
    ψ (D.τ i) μ ≤ Function.leftLim (fun r => ψ r μ) (D.τ i)) ∧
  ∀ i : Fin D.n, ∀ s μ, D.τ i.castSucc ≤ s → s < D.τ i.succ → IsP2 μ → Lop G (D.Φ i) s μ ≤ 0

/-- `ψ ∈ 𝒰̲_g` (4.18): `ψ ∈ 𝒰`, `ψ(T, ·) ≤ g`, `ψ_{τᵢ} ≥ ψ_{τᵢ−}` for `i ≥ 1`, and on each `[τᵢ, τᵢ₊₁)`
`ψ` is a classical subsolution of (3.1). -/
def InUunder (G : Gen d T) (g : Measure (Path d T) → ℝ) (ψ : ℝ≥0 → Measure (Path d T) → ℝ)
    (D : PWData d T) : Prop :=
  InU ψ D ∧ (∀ μ, IsP2 μ → ψ T μ ≤ g μ) ∧
  (∀ i : Fin (D.n + 1), 0 < i → ∀ μ, IsP2 μ →
    Function.leftLim (fun r => ψ r μ) (D.τ i) ≤ ψ (D.τ i) μ) ∧
  ∀ i : Fin D.n, ∀ s μ, D.τ i.castSucc ≤ s → s < D.τ i.succ → IsP2 μ → 0 ≤ Lop G (D.Φ i) s μ

/-- `V̄(t, μ) = inf{ψ(t, μ) : ψ ∈ 𝒰̄_g}` (4.17), in `EReal` (`+∞` if `𝒰̄_g = ∅`). -/
noncomputable def Vbar (G : Gen d T) (g : Measure (Path d T) → ℝ) (t : ℝ≥0)
    (μ : Measure (Path d T)) : EReal :=
  ⨅ ψ : {ψ : ℝ≥0 → Measure (Path d T) → ℝ // ∃ D, InUbar G g ψ D}, ((ψ.1 t μ : ℝ) : EReal)

/-- `V̲(t, μ) = sup{ψ(t, μ) : ψ ∈ 𝒰̲_g}` (4.17), in `EReal` (`−∞` if `𝒰̲_g = ∅`). -/
noncomputable def Vunder (G : Gen d T) (g : Measure (Path d T) → ℝ) (t : ℝ≥0)
    (μ : Measure (Path d T)) : EReal :=
  ⨆ ψ : {ψ : ℝ≥0 → Measure (Path d T) → ℝ // ∃ D, InUunder G g ψ D}, ((ψ.1 t μ : ℝ) : EReal)

end MasterVisc.Comparison


