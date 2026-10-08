-- Prove2me | Definitions.Def_BERicci_Main_Regular
-- name    : BERicci_Main_Regular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:41.224544+00:00
-- url     : https://prove2.me/theorems/3096b0b2-9370-4dc3-84e0-cd1ae417aae6
-- title:
--   §4 — Fisher information, absolute continuity, and regular curves
-- statement:
--   The Fisher information of a nonnegative density is $F(f)=4\mathcal E(\sqrt f)$. A curve $\rho_s$ in $\mathcal P_2(X)$ is $AC^2$ when it has an $L^2$ metric speed; its action is the integral of the squared minimal speed. A regular curve, in the sense of Definition 4.10, has bounded entropy, $C^1$ densities in $L^1$, densities obtained by time mollification of the $L^1$ heat flow, a continuous $L^1$ generator, and uniformly bounded Fisher information over compact time intervals.
--
--   $$\mathcal A(\rho)=\int_0^1|\dot\rho_s|^2\,ds,\qquad R_K(t)=\frac{t}{I_K(t)}. $$
--
--   These definitions state the precise domain of the action estimate in Theorem 4.16.
--
--   **Formalization Note** The action is the infimum over admissible speeds, equal to the integral of the squared metric derivative. The $L^1$ heat flow $P_r\tilde f$ is determined only $m$-a.e. for each $r$, so condition (d) asks for a jointly measurable version of $(r,x)\mapsto P_r\tilde f(x)$; then the time mollification $\mathfrak h^\eta\tilde f(x)=\eta^{-1}\int_0^\infty \kappa(r/\eta)P_r\tilde f(x)\,dr$ does not depend on the version, $m$-a.e.
-- source:
--   arXiv:1209.5786v4, §3.1, p. 21; (2.17)–(2.18), pp. 13–14; §4.1, p. 43; Definition 4.10, pp. 50–51; (4.29), p. 56

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Contract_Dual

namespace BERicci.Main

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The L¹ extension of the heat semigroup (p. 13): on L¹ ∩ L² it agrees almost everywhere
with the original heat flow, and on L¹ it is a positive, mass preserving contraction semigroup. -/
def IsL1Extension (m : Measure X) (P P1 : ℝ → (X → ℝ) → X → ℝ) : Prop :=
  (∀ t ≥ (0 : ℝ), ∀ f : X → ℝ, Integrable f m → Integrable (P1 t f) m) ∧
  (∀ t ≥ (0 : ℝ), ∀ f : X → ℝ, Integrable f m → MemLp f 2 m → P1 t f =ᵐ[m] P t f) ∧
  (∀ t ≥ (0 : ℝ), ∀ f : X → ℝ, Integrable f m → 0 ≤ᵐ[m] f → 0 ≤ᵐ[m] P1 t f) ∧
  (∀ t ≥ (0 : ℝ), ∀ f : X → ℝ, Integrable f m → ∫ x, P1 t f x ∂m = ∫ x, f x ∂m) ∧
  (∀ t ≥ (0 : ℝ), ∀ f : X → ℝ, Integrable f m →
    eLpNorm (P1 t f) 1 m ≤ eLpNorm f 1 m) ∧
  (∀ t ≥ (0 : ℝ), ∀ f g : X → ℝ, Integrable f m → Integrable g m →
    f =ᵐ[m] g → P1 t f =ᵐ[m] P1 t g) ∧
  (∀ t ≥ (0 : ℝ), ∀ f g : X → ℝ, Integrable f m → Integrable g m →
    P1 t (f + g) =ᵐ[m] P1 t f + P1 t g) ∧
  (∀ t ≥ (0 : ℝ), ∀ (c : ℝ) (f : X → ℝ), Integrable f m →
    P1 t (c • f) =ᵐ[m] c • P1 t f) ∧
  (∀ f : X → ℝ, Integrable f m → P1 0 f =ᵐ[m] f) ∧
  (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ f : X → ℝ, Integrable f m →
    P1 (s + t) f =ᵐ[m] P1 s (P1 t f))

/-- The Fisher information of §4.1, `F(f) = 4 E(√f)`. -/
noncomputable def fisher (E : (X → ℝ) → ℝ≥0∞) (f : X → ℝ) : ℝ≥0∞ :=
  4 * E (fun x => Real.sqrt (f x))

/-- An admissible speed for an `AC²` curve in `(P₂(X), W₂)` (§3.1, p. 21). -/
def IsAC2Speed (ρ : ℝ → Measure X) (v : ℝ → ℝ) : Prop :=
  (∀ s ∈ Set.Icc (0 : ℝ) 1, BERicci.Gamma.InP2 (ρ s)) ∧
  IntegrableOn v (Set.Icc (0 : ℝ) 1) ∧
  (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), 0 ≤ v s) ∧
  (∫⁻ s in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (v s ^ 2) ∂volume) < ⊤ ∧
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, s ≤ t →
    BERicci.Gamma.W2sq (ρ s) (ρ t) ≤ ENNReal.ofReal (∫ u in s..t, v u) ^ 2

/-- `AC²([0,1]; (P₂(X), W₂))`, §3.1. -/
def IsAC2 (ρ : ℝ → Measure X) : Prop := ∃ v, IsAC2Speed ρ v

/-- The squared metric action. The least admissible speed is the metric derivative almost
everywhere (§3.1, p. 21), so this infimum is `∫₀¹ |ρ̇_s|² ds`. -/
noncomputable def action (ρ : ℝ → Measure X) : ℝ≥0∞ :=
  ⨅ (v : ℝ → ℝ) (_ : IsAC2Speed ρ v),
    ∫⁻ s in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (v s ^ 2) ∂volume

/-- A smooth, nonnegative time mollifier supported in `(0,∞)` and of mass one (2.17). -/
def IsTimeMollifier (κ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ tsupport κ ⊆ Set.Ioi 0 ∧
  (∀ r, 0 ≤ κ r) ∧ (∫ r, κ r) = 1

/-- The time mollification `h^η f` of (2.17)–(2.18). -/
noncomputable def hEta (P1 : ℝ → (X → ℝ) → X → ℝ) (κ : ℝ → ℝ)
    (η : ℝ) (f : X → ℝ) : X → ℝ :=
  fun x => η⁻¹ * ∫ r in Set.Ioi (0 : ℝ), κ (r / η) * P1 r f x ∂volume

/-- `g = Δ_E^(1) f`, the L¹ generator of the heat semigroup (p. 13). -/
def IsL1Generator (m : Measure X) (P1 : ℝ → (X → ℝ) → X → ℝ)
    (f g : X → ℝ) : Prop :=
  Integrable f m ∧ Integrable g m ∧
    Tendsto (fun h : ℝ => eLpNorm (h⁻¹ • (P1 h f - f) - g) 1 m) (𝓝[>] 0) (𝓝 0)

/-- `C¹([0,1]; L¹(X,m))` in terms of L¹ convergence of the difference quotients. -/
def IsC1L1 (m : Measure X) (f : ℝ → X → ℝ) : Prop :=
  ∃ f' : ℝ → X → ℝ,
    (∀ s ∈ Set.Icc (0 : ℝ) 1, Integrable (f s) m ∧ Integrable (f' s) m) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun t : ℝ => eLpNorm ((t - s)⁻¹ • (f t - f s) - f' s) 1 m)
        (𝓝[≠] s ⊓ 𝓟 (Set.Icc (0 : ℝ) 1)) (𝓝 0)) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun t : ℝ => eLpNorm (f' t - f' s) 1 m)
        (𝓝[Set.Icc (0 : ℝ) 1] s) (𝓝 0))

/-- Definition 4.10, pp. 50–51: a regular curve of probability densities.
The parameters `P1` and `κ` pin the time mollification used in condition (d). `P1 r f̃` is pinned
only `m`-a.e. for each `r`, so (d) asks for a jointly measurable version of `(r, x) ↦ P1 r f̃ x`;
by Fubini the pointwise integral `h^η f̃` is then independent of the version, `m`-a.e. -/
def IsRegularCurve (m : Measure X) (E : (X → ℝ) → ℝ≥0∞)
    (P1 : ℝ → (X → ℝ) → X → ℝ) (κ : ℝ → ℝ)
    (ρ : ℝ → Measure X) (f : ℝ → X → ℝ) : Prop :=
  IsAC2 ρ ∧
  (∀ s ∈ Set.Icc (0 : ℝ) 1,
    0 ≤ᵐ[m] f s ∧
    ρ s = m.withDensity (fun x => ENNReal.ofReal (f s x))) ∧
  (∃ L U : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
    (L : EReal) ≤ BERicci.Gamma.entropy m (ρ s) ∧ BERicci.Gamma.entropy m (ρ s) ≤ (U : EReal)) ∧
  IsC1L1 m f ∧
  (∃ η : ℝ, 0 < η ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
    ∃ ftilde : X → ℝ, Integrable ftilde m ∧
      AEStronglyMeasurable (fun p : ℝ × X => P1 p.1 ftilde p.2)
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod m) ∧
      (∀ᵐ x ∂m, IntegrableOn (fun r : ℝ => κ (r / η) * P1 r ftilde x) (Set.Ioi 0)) ∧
      f s =ᵐ[m] hEta P1 κ η ftilde) ∧
  (∃ g : ℝ → X → ℝ,
    (∀ s ∈ Set.Icc (0 : ℝ) 1, IsL1Generator m P1 (f s) (g s)) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun t : ℝ => eLpNorm (g t - g s) 1 m)
        (𝓝[Set.Icc (0 : ℝ) 1] s) (𝓝 0))) ∧
  (∀ T : ℝ, 0 < T → ∃ B : ℝ≥0∞, B < ⊤ ∧
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) T,
      fisher E (P1 t (f s)) ≤ B)

/-- `R_K(t) = t/I_K(t)` of (4.29), used only for `t > 0`. -/
noncomputable def RK (K t : ℝ) : ℝ := t / BERicci.Gamma.IK K t

end BERicci.Main


