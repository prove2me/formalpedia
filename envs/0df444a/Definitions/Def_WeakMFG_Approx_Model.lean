-- Prove2me | Definitions.Def_WeakMFG_Approx_Model
-- name    : WeakMFG_Approx_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:31.910479+00:00
-- url     : https://prove2.me/theorems/1588b88f-cc59-4750-bad5-6d6fa4c8b8b8
-- title:
--   Path space $\mathcal C$, $\mathcal P_\psi(\mathcal C)$ with $\tau_\psi$, $\mathcal P(A)$, the base space $(\xi, W)$ with its augmented filtration, admissible controls (§3.1)
-- statement:
--   Fix a dimension $d\ge 0$ and a horizon $T>0$. The **path space** is $\mathcal C = C([0,T];\mathbb R^d)$ with the sup norm $\|x\| = \sup_{s\in[0,T]}|x(s)|$ and its Borel $\sigma$-field. Its **canonical filtration** is $\mathcal F^{\mathcal C}_t = \sigma(x(s) : s\le t\wedge T)$; a map $(t,x)\mapsto\varphi(t,x)$ is *progressively measurable* when it is progressive for this filtration. For $t\ge 0$ the **stopping map** sends $x$ to $x_{\cdot\wedge t}$, the path frozen after time $t$. The **progressive $\sigma$-field** of a filtration $(\mathcal F_t)$ on $\Omega$ consists of the sets $S\subseteq[0,\infty)\times\Omega$ whose trace on $[0,t]\times\Omega$ is $\mathcal B([0,t])\otimes\mathcal F_t$-measurable for every $t$.
--
--   Given a measurable $\psi:\mathcal C\to[1,\infty)$, let
--   $$\mathcal P_\psi(\mathcal C) = \Big\{\mu \in \mathcal P(\mathcal C) : \int\psi\,d\mu<\infty\Big\},\qquad B_\varphi(\mathcal C) = \Big\{f:\mathcal C\to\mathbb R \text{ measurable} : \sup_x |f(x)|/\varphi(x)<\infty\Big\}.$$
--   The topology $\tau_\psi(\mathcal C)$ on $\mathcal P_\psi(\mathcal C)$ is the weakest topology making $\mu\mapsto\int f\,d\mu$ continuous for every $f\in B_\psi(\mathcal C)$; $\mathcal P_\psi(\mathcal C)$ always carries this topology. Two measures are **equivalent**, $\mu\sim\mu'$, when each is absolutely continuous with respect to the other. For a subset $A$ of a normed space, $\mathcal P(A)$ is the set of Borel probability measures on $A$ with the topology of weak convergence.
--
--   The **base space** is a probability space $(\Omega,\mathcal F,P)$ carrying an $\mathbb R^d$-valued random variable $\xi$ with law $\lambda_0$ and a standard $d$-dimensional Wiener process $W$ independent of $\xi$. Its filtration $\mathbb F=(\mathcal F_t)$ is $\sigma((\xi,W_s):0\le s\le t)$ completed by the $P$-null sets. An **admissible control** $\alpha\in\mathbb A$ is an $\mathbb F$-progressively measurable process with values in $A$.
--
--   These are the objects on which the mean field game of §3 and the $n$-player game of §4 are built.
--
--   **Formalization Note** The base space is abstract (any space with such $\xi$, $W$), which contains the canonical space $\mathbb R^d\times\mathcal C$ of the paper as an instance; every object of the theorems is a law. Augmentation adds the measurable $P$-null sets, since Lean's measurable spaces are not complete. $\mathcal P_\psi(\mathcal C)$ is a structure (measure, probability, $\int\psi\,d\mu<\infty$) so that it carries only $\tau_\psi$. Time runs over $[0,\infty)$; only $[0,T]$ matters.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §3.1, pp. 8–9 (P_ψ, B_ψ, τ_ψ, the base space, (S.1)); (F.2) p. 12 (stopping map)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WeakMFG_Existence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace WeakMFG.Approx

instance instBorelSpacePath (d : ℕ) (T : ℝ≥0) : BorelSpace (WeakMFG.Existence.Path d T) := ⟨rfl⟩

/-- The coordinate `x ↦ x(min t T)` of a path at time `t ∈ ℝ≥0` (frozen after `T`). -/
def coord {d : ℕ} {T : ℝ≥0} (t : ℝ≥0) (x : WeakMFG.Existence.Path d T) : Fin d → ℝ :=
  x ⟨min (t : ℝ) T, le_min t.2 T.2, min_le_right _ _⟩

lemma continuous_coord {d : ℕ} {T : ℝ≥0} (t : ℝ≥0) : Continuous (coord (d := d) (T := T) t) :=
  continuous_eval_const _

/-- The canonical filtration on `C`: `pathFilt t = σ(x(s) : s ≤ t ∧ T)`.
"`(t, x) ↦ φ(t, x)` is progressively measurable" (§3.1, p. 9) is
`IsStronglyProgressive pathFilt φ`. -/
noncomputable def pathFilt {d : ℕ} {T : ℝ≥0} : Filtration ℝ≥0 (WeakMFG.Existence.instMeasurableSpacePath d T) :=
  Filtration.natural (fun t (x : WeakMFG.Existence.Path d T) => coord t x)
    (fun t => (continuous_coord t).stronglyMeasurable)

/-- The stopping map `C ∋ x ↦ x_{·∧t} ∈ C` of (F.2), p. 12. -/
def stopAt {d : ℕ} {T : ℝ≥0} (t : ℝ≥0) (x : WeakMFG.Existence.Path d T) : WeakMFG.Existence.Path d T :=
  x.comp ⟨fun s => ⟨min (s : ℝ) t, le_min s.2.1 t.2, (min_le_left _ _).trans s.2.2⟩,
    by fun_prop⟩

/-- The progressive σ-field on `ℝ≥0 × Ω` of a filtration `𝓕`: `S` is progressive iff for every `t`,
`{(s, ω) ∈ [0, t] × Ω : (s, ω) ∈ S}` is `𝓑([0, t]) ⊗ 𝓕_t`-measurable. A map on `ℝ≥0 × Ω` is
measurable for it iff it is progressively measurable. Used in (F.3), p. 12. -/
@[instance_reducible]
def progSigma {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m) :
    MeasurableSpace (ℝ≥0 × Ω) :=
  ⨅ t : ℝ≥0, MeasurableSpace.map (fun p : Set.Iic t × Ω => ((p.1 : ℝ≥0), p.2))
    (@Prod.instMeasurableSpace _ _ _ (𝓕 t))

lemma nullSigma_le {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) : WeakMFG.Existence.nullSigma P ≤ m :=
  MeasurableSpace.generateFrom_le fun _ hs => hs.1

/-- The filtration `σ(ξ, W_s : s ≤ t)` augmented by the measurable `P`-null sets (p. 8). -/
noncomputable def augFilt {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable ξ) {W : ℝ≥0 → Ω → Fin d → ℝ}
    (hW : Peng1990.SMP.IsStdBrownian P W) : Filtration ℝ≥0 m where
  seq t := MeasurableSpace.comap ξ inferInstance ⊔ Peng1990.SMP.brownianFiltration hW t ⊔
    WeakMFG.Existence.nullSigma P
  mono' _ _ hst := sup_le_sup_right (sup_le_sup_left ((Peng1990.SMP.brownianFiltration hW).mono hst) _) _
  le' t := sup_le (sup_le hξ.comap_le ((Peng1990.SMP.brownianFiltration hW).le t)) (nullSigma_le P)

/-- `P_ψ(C)`: probability measures `μ` on `C` with `∫ ψ dμ < ∞` (p. 8). A structure, not a
subtype of `ProbabilityMeasure`, so that it carries only the topology `τ_ψ(C)`. -/
structure Ppsi {d : ℕ} {T : ℝ≥0} (ψ : WeakMFG.Existence.Path d T → ℝ) where
  μ : Measure (WeakMFG.Existence.Path d T)
  isProb : IsProbabilityMeasure μ
  integ : ∫⁻ x, ENNReal.ofReal (ψ x) ∂μ < ⊤

/-- `τ_φ` on `P_ψ(C)`: the weakest topology making `μ ↦ ∫ f dμ` continuous for every `f ∈ B_φ(C)`
(p. 8). `τ_ψ(C)` is `tauTop ψ ψ`. -/
@[instance_reducible]
noncomputable def tauTop {d : ℕ} {T : ℝ≥0} (ψ φ : WeakMFG.Existence.Path d T → ℝ) : TopologicalSpace (Ppsi ψ) :=
  TopologicalSpace.induced (fun (μ : Ppsi ψ) (f : WeakMFG.Existence.Bpsi φ) => ∫ x, f.1 x ∂μ.μ) inferInstance

/-- Unless stated otherwise `P_ψ(C)` carries `τ_ψ(C)` (p. 8). -/
noncomputable instance instTopPpsi {d : ℕ} {T : ℝ≥0} (ψ : WeakMFG.Existence.Path d T → ℝ) : TopologicalSpace (Ppsi ψ) :=
  tauTop ψ ψ

/-- `P(A)`, probability measures on the control set `A` with the weak topology (Mathlib's
`ProbabilityMeasure`); its σ-field is taken to be `borel (PA A)` wherever measurability is used
("`P(A)` is endowed with the weak topology and its corresponding Borel σ-field", p. 9). -/
abbrev PA {EA : Type*} [TopologicalSpace EA] [MeasurableSpace EA] (A : Set EA) :=
  ProbabilityMeasure A

/-- The base space of §3.1 (p. 8), abstracted (D1): a probability space carrying `ξ` and a standard
`d`-dimensional Brownian motion `W` independent of `ξ`; `λ₀ = P ∘ ξ⁻¹`. -/
structure Base (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  isProb : IsProbabilityMeasure P
  ξ : Ω → Fin d → ℝ
  ξ_meas : Measurable ξ
  W : ℝ≥0 → Ω → Fin d → ℝ
  hW : Peng1990.SMP.IsStdBrownian P W
  indep : IndepFun ξ (fun ω t => W t ω) P

/-- `𝔽 = (𝓕_t)`: the completion of `σ((ξ, W_s) : 0 ≤ s ≤ t)` by `P`-null sets (p. 8). -/
noncomputable def Base.filt {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (B : Base d Ω) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
  augFilt B.P B.ξ B.ξ_meas B.hW

/-- The admissible controls `𝔸` (S.1): `𝔽`-progressively measurable `A`-valued processes. -/
def IsAdmissible {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {EA : Type*} [TopologicalSpace EA]
    (B : Base d Ω) (A : Set EA) (α : ℝ≥0 → Ω → EA) : Prop :=
  IsStronglyProgressive B.filt α ∧ ∀ t ω, α t ω ∈ A

end WeakMFG.Approx


