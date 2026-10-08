-- Prove2me | Definitions.Def_WeakMFG_Existence_FixedPoint
-- name    : WeakMFG_Existence_FixedPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:38.829592+00:00
-- url     : https://prove2.me/theorems/88118738-b803-4338-8092-525889ae9fa3
-- title:
--   The space M with its stable topology, the BSDE (7.1), the optimal-control sets 𝔸(µ, ν) of (7.4), M_q of (7.5) and the set Q of (7.6)
-- statement:
--   These are the objects of the fixed-point argument of §7.
--
--   1. **The space $\mathcal M$.** Positive Borel measures $\nu$ on $[0,T]\times\mathcal P(A)$ whose first projection is Lebesgue measure; each disintegrates as $\nu(dt,dq)=\nu_t(dq)\,dt$ with a measurable $t\mapsto\nu_t\in\mathcal P(\mathcal P(A))$. The *stable topology* is the weakest one making $\nu\mapsto\int\varphi\,d\nu$ continuous for every bounded measurable $\varphi:[0,T]\times\mathcal P(A)\to\mathbb R$ with $\varphi(t,\cdot)$ continuous for each $t$.
--   2. **Extensions.** For $\nu\in\mathcal P(\mathcal P(A))$, $f(t,x,\mu,\nu,a):=\int\nu(dq)\,f(t,x,\mu,q,a)$ and $H(t,x,\mu,\nu,z):=\int\nu(dq)\,H(t,x,\mu,q,z)$; $J^{\mu,\nu}(\alpha)$ is the reward with $f(t,X,\mu,\nu_t,\alpha_t)$ in place of $f(t,X,\mu,q_t,\alpha_t)$.
--   3. **The BSDE (7.1).** $(Y^{\mu,\nu},Z^{\mu,\nu})$ solves
--   $$Y^{\mu,\nu}_t=g(X,\mu)+\int_t^TH(s,X,\mu,\nu_s,Z^{\mu,\nu}_s)\,ds-\int_t^TZ^{\mu,\nu}_s\,dW_s .$$
--   4. **Optimal controls (7.4).** $\mathbb A(\mu,\nu)=\{\alpha\in\mathbb A:\alpha_t\in A(t,X,\mu,Z^{\mu,\nu}_t)\ dt\times dP\text{-a.e.}\}$.
--   5. **Moments (7.5) and the set $\mathcal Q$ (7.6).** With $\Phi(\mu,\alpha)=(P^{\mu,\alpha}\circ X^{-1},\delta_{P^{\mu,\alpha}\circ\alpha_t^{-1}}(dq)dt)$,
--   $$M_q=\sup_{(\mu,\alpha)\in\mathcal P_\psi(\mathcal C)\times\mathbb A}\int\Big(\frac{d\Phi(\mu,\alpha)}{d\mathcal X}\Big)^q d\mathcal X,\qquad M=\max(M_2,M_{-1}),$$
--   $$\mathcal Q=\Big\{\mu\in\mathcal P_\psi(\mathcal C):\mu\sim\mathcal X,\ \int\Big(\frac{d\mu}{d\mathcal X}\Big)^2d\mathcal X\le M,\ \int\frac{d\mathcal X}{d\mu}\,d\mathcal X\le M\Big\}.$$
--   6. **Joint measurability (disclosed addition).** For each $\mu$, $(t,x,q,a)\mapsto f(t,x,\mu,q,a)$ is measurable for the progressive $\sigma$-field on $[0,T]\times\mathcal C$ and the Borel $\sigma$-fields of $\mathcal P(A)$ and $A$; this is what makes the extension $\int\nu_t(dq)f(t,X,\mu,q,a)$ a measurable process.
--
--   **Formalization Note** $\nu\in\mathcal M$ is encoded by its disintegration $t\mapsto\nu_t$ (measurable for the Borel $\sigma$-field of the weak topology), and convergence in $\mathcal M$ by sequential stable convergence ($\mathcal M$ is compact metrizable). The BSDE is the published `Peng1990.SMP.SolvesBSDE` with a one-dimensional $Y$; solutions are always hypotheses, never chosen. In (7.4) the maximizer set is evaluated at a fixed $q_0\in\mathcal P(A)$: by (S.5) it does not depend on $q$. $M_q$ is a supremum in $[0,\infty]$, over all density versions too, with $0^q=\infty$ for $q<0$; the first component of $\Phi(\mu,\alpha)$ is all that (7.5) uses.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §7, pp. 21–22 (M, extensions, (7.1), (7.4), Φ); Lemma 7.7, (7.5) and (7.6), p. 24

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WeakMFG_Existence_Model
import Definitions.Def_WeakMFG_Existence_Hyp
import Definitions.Def_WeakMFG_Existence_Reward

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Existence

variable {d : ℕ} {T : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω]
  {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]

/-- The space `M` (§7, p. 21) of positive Borel measures `ν` on `[0, T] × P(A)` whose first
projection is Lebesgue measure, encoded by its disintegration `ν(dt, dq) = ν_t(dq) dt`: a map
`t ↦ ν_t ∈ P(P(A))`, measurable for the Borel σ-field of the weak topology on `P(P(A))`.
Formalization Note: only `t ∈ [0, T]` matters; the disintegration is determined up to a.e.
equality. -/
def Mflow (A : Set EA) : Type _ :=
  {ν : ℝ≥0 → ProbabilityMeasure (PA A) //
    @Measurable _ _ _ (borel (ProbabilityMeasure (PA A))) ν}

/-- Convergence `νⁿ → ν` in the stable topology of `M` (p. 21: the weakest topology making
`ν ↦ ∫ φ dν` continuous for each bounded measurable `φ : [0, T] × P(A) → ℝ` with `φ(t, ·)`
continuous for each `t`), stated for sequences: `∫₀ᵀ ∫ φ(t, q) νⁿ_t(dq) dt → ∫₀ᵀ ∫ φ(t, q) ν_t(dq) dt`
for every such `φ`. -/
def StableTendsto (T : ℝ≥0) {A : Set EA} (νn : ℕ → Mflow A) (ν : Mflow A) : Prop :=
  ∀ φ : ℝ≥0 → PA A → ℝ, Measurable (Function.uncurry φ) → (∃ C, ∀ t q, |φ t q| ≤ C) →
    (∀ t, Continuous (φ t)) →
    Tendsto (fun n => ∫ t in Set.Icc (0 : ℝ) T,
        ∫ q, φ t.toNNReal q ∂((νn n).1 t.toNNReal : Measure (PA A))) atTop
      (𝓝 (∫ t in Set.Icc (0 : ℝ) T, ∫ q, φ t.toNNReal q ∂(ν.1 t.toNNReal : Measure (PA A))))

/-- The extension of `f` to `ν ∈ P(P(A))`, `f(t, x, μ, ν, a) := ∫ ν(dq) f(t, x, μ, q, a)` (p. 21). -/
noncomputable def fbar {ψ : Path d T → ℝ} {A : Set EA}
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ)
    (t : ℝ≥0) (x : Path d T) (μ : Ppsi ψ) (ν : ProbabilityMeasure (PA A)) (a : EA) : ℝ :=
  ∫ q, f t x μ q a ∂(ν : Measure (PA A))

/-- The extension of `H` to `ν ∈ P(P(A))`, `H(t, x, μ, ν, z) := ∫ ν(dq) H(t, x, μ, q, z)`
(p. 21, Remark 7.1). -/
noncomputable def Hbar {ψ : Path d T → ℝ} {A : Set EA}
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ)
    (t : ℝ≥0) (x : Path d T) (μ : Ppsi ψ) (ν : ProbabilityMeasure (PA A)) (z : Fin d → ℝ) : ℝ :=
  ∫ q, Ham σ b f t x μ q z ∂(ν : Measure (PA A))

/-- `J^{μ,ν}(α) = E^{μ,α}[∫₀ᵀ f(t, X, μ, ν_t, α_t) dt + g(X, μ)]` for `ν ∈ M` (§7, p. 22), for
a density version `D` of `dP^{μ,α}/dP`. -/
noncomputable def JrewNu {ψ : Path d T → ℝ} {A : Set EA} (B : Base d T Ω)
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ)
    (Xp : Ω → Path d T) (μ : Ppsi ψ) (ν : Mflow A) (α : ℝ≥0 → Ω → EA) (D : Ω → ℝ) : ℝ :=
  ∫ ω, D ω * ((∫ t in Set.Icc (0 : ℝ) T,
      fbar f t.toNNReal (Xp ω) μ (ν.1 t.toNNReal) (α t.toNNReal ω)) + g (Xp ω) μ) ∂B.P

/-- `(Y, Z)` solves the BSDE (7.1) (p. 21):
`Y_t = g(X, μ) + ∫ₜᵀ H(s, X, μ, ν_s, Z_s) ds − ∫ₜᵀ Z_s dW_s`, in the sense of
`Peng1990.SMP.SolvesBSDE` (one-dimensional `Y`, indexed by `Unit`; `Y, Z ∈ L²_F`). -/
def IsBSDE71 {ψ : Path d T → ℝ} {A : Set EA} (B : Base d T Ω)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ)
    (Xp : Ω → Path d T) (μ : Ppsi ψ) (ν : Mflow A)
    (Y : ℝ≥0 → Ω → Unit → ℝ) (Z : Fin d → ℝ≥0 → Ω → Unit → ℝ) : Prop :=
  Peng1990.SMP.SolvesBSDE B.filt B.P T B.W (fun ω _ => g (Xp ω) μ)
    (fun s ω _ z _ => Hbar σ b f s (Xp ω) μ (ν.1 s) (fun j => z j ())) Y Z

/-- The set `𝔸(μ, ν) = {α ∈ 𝔸 : α_t ∈ A(t, X, μ, Z^{μ,ν}_t) dt × dP-a.e.}` (7.4), for the
`Z`-component `Z` of a solution of (7.1). The maximizer set is evaluated at a fixed `q₀ ∈ P(A)`:
by (S.5) it does not depend on `q`, and statements quantify over every `q₀`. -/
def Aopt {ψ : Path d T → ℝ} {A : Set EA} (B : Base d T Ω)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ)
    (Xp : Ω → Path d T) (μ : Ppsi ψ) (Z : Fin d → ℝ≥0 → Ω → Unit → ℝ) (q₀ : PA A) :
    Set (ℝ≥0 → Ω → EA) :=
  {α | IsAdmissible B A α ∧
    ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod B.P),
      α p.1.toNNReal p.2 ∈
        Amax σ b f p.1.toNNReal (Xp p.2) μ q₀ (fun j => Z j p.1.toNNReal p.2 ())}

/-- `M_q = sup_{(μ, α) ∈ P_ψ(C) × 𝔸} ∫ (dΦ(μ, α)/d𝒳)^q d𝒳` (7.5), where the first component of
`Φ(μ, α)` is `P^{μ,α} ∘ X⁻¹` (p. 22) and `𝒳 = P ∘ X⁻¹`; the supremum also runs over all density
versions. Formalization Note: computed in `ℝ≥0∞` with `rnDeriv` and `rpow` (`0 ^ q = ⊤` for
`q < 0`), so the supremum is never junk. -/
noncomputable def Mq {ψ : Path d T → ℝ} {A : Set EA} (B : Base d T Ω)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ)) (Xp : Ω → Path d T) (q : ℝ) : ℝ≥0∞ :=
  ⨆ (μ : Ppsi ψ) (α : ℝ≥0 → Ω → EA) (_ : IsAdmissible B A α) (D : Ω → ℝ)
    (_ : IsDensity B σ b Xp μ α D),
    ∫⁻ x, (((Pma B.P D).map Xp).rnDeriv (lawX B Xp) x) ^ q ∂(lawX B Xp)

/-- `M := max(M₂, M₋₁)` (p. 24). -/
noncomputable def Mbound {ψ : Path d T → ℝ} (B : Base d T Ω) (A : Set EA)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ)) (Xp : Ω → Path d T) : ℝ≥0∞ :=
  max (Mq (A := A) B σ b Xp 2) (Mq (A := A) B σ b Xp (-1))

/-- The set `Q = {μ ∈ P_ψ(C) : μ ∼ 𝒳, ∫ (dμ/d𝒳)² d𝒳 ≤ M, ∫ (d𝒳/dμ) d𝒳 ≤ M}` (7.6). -/
def Qset {ψ : Path d T → ℝ} (B : Base d T Ω) (A : Set EA)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ)) (Xp : Ω → Path d T) : Set (Ppsi ψ) :=
  {μ | MEquiv μ.toMeasure (lawX B Xp) ∧
    ∫⁻ x, (μ.toMeasure.rnDeriv (lawX B Xp) x) ^ 2 ∂(lawX B Xp) ≤ Mbound B A σ b Xp ∧
    ∫⁻ x, (lawX B Xp).rnDeriv μ.toMeasure x ∂(lawX B Xp) ≤ Mbound B A σ b Xp}

/-- The filtration `pathFilt t ⊗ B(P(A)) ⊗ B(EA)` on `C × P(A) × EA`. -/
noncomputable def prodFilt (d : ℕ) (T : ℝ≥0) (A : Set EA) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Path d T × (PA A × EA))) where
  seq t := (pathFilt d T t).prod inferInstance
  mono' _ _ hst := sup_le_sup_right (MeasurableSpace.comap_mono ((pathFilt d T).mono hst)) _
  le' t := sup_le_sup_right (MeasurableSpace.comap_mono ((pathFilt d T).le t)) _

/-- Joint measurability of the running reward (disclosed addition D5): for each `μ`,
`(t, x, q, a) ↦ f(t, x, μ, q, a)` is progressively measurable for the progressive σ-field on
`[0, T] × C` and the Borel σ-fields of `P(A)` and `EA`. This is what makes the extension
`∫ ν_t(dq) f(t, X, μ, q, a)` of p. 21 a measurable function of `(t, ω)`. -/
def JointProg {ψ : Path d T → ℝ} (A : Set EA)
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) : Prop :=
  ∀ μ, IsStronglyProgressive (prodFilt d T A)
    (fun t (y : Path d T × (PA A × EA)) => f t y.1 μ y.2.1 y.2.2)

end WeakMFG.Existence


