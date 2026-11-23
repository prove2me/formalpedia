-- Prove2me | Definitions.Def_MMDarkPool_Exchange_Supplement_MeasureCounterexample
-- name    : MMDarkPool_Exchange_Supplement_MeasureCounterexample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:23:27.777397+00:00
-- url     : https://prove2.me/theorems/5f5e0e92-ab47-44a2-904a-d8f315c23188
-- title:
--   §2.2.1, pp. 4–6 (corrected: refutation instance) — parameters and terminal requirements for the source-density counterexample
-- statement:
--   Let ε,r > 0. The numerical instance has T = tick = σ = γ = Aˡ = Aᵈ = θˡ = θᵈ = q̄ = 1, impacts Γˡ = Γᵈ = r, and both trade-size sets {1,2}. Every posted volume is 1. These definitions construct this instance, its literal printed terminal density after integrating the indicator gates, and necessary terminal-mean requirements on the reference and controlled size-2 counts.
--
--   $$R(ω)=\exp\!\left(\sum_{i,j}\sum_{k\in\{1,2\}}\log(\lambda^{i,j}/\epsilon)C^{i,j,k}(ω)-(\lambda^{i,j}-\epsilon)B^{i,j,k}(ω)\right),\qquad \lambda^{i,j}=e^{-1/2}.$$
--
--   Here C and B are the integrated gates against dN and dt respectively. TerminalMeasureRequirements asks for a probability reference measure, a measurable natural count with integrable reference mean ε, a measurable printed density R, the controlled law with density R, and integrable controlled count mean zero. These are necessary consequences of the simultaneous printed claims, not a replacement definition of the whole market model.
--
--   **Formalization Note.** Arbitrary C and B, subject to measurability of R, strengthen the refutation certificate. The reference Poisson law and controlled martingale are used only through their necessary mean consequences. All order-flow parameters remain fixed while ε tends to zero. No stochastic law for latency marks is introduced.
--
--   Differences from the source:
--   - correction: The controlled measure has both the printed density and the prescribed size-specific intensities (pp. 5–6). → A constant admissible numerical instance makes their necessary terminal consequences incompatible.; reason: The printed exponential density is strictly positive, so a measurable such density preserves null sets. An unposted size-2 count is prescribed compensator zero but has positive reference mean ε at T = 1. The source claim is refuted rather than silently repairing the density.
--   - generalization: The reference count is Poisson with rate ε and the controlled count minus its compensator is a martingale, starting at zero. → Only their integrable terminal-mean consequences are required, and the integrated inventory/size gates may be arbitrary real functions giving a measurable density.; reason: Impossibility with fewer stochastic assumptions applies to every model the source allows. Strict positivity of an exponential makes the particular gate integrals irrelevant. The parameters A, θ, σ and tick are fixed at 1 while ε and the positive impact r may be arbitrarily small.
--   - encoding: The printed density is an exponential of stochastic integrals with constant baseline coefficients in this instance. → activeCounts and activeTimes denote the already integrated indicators, and withDensity encodes the terminal change of measure.; reason: Pulling constant coefficients outside the two integrals yields exactly printedDensity. The density and count are explicitly measurable, and both count integrals require Integrable, so no totality default is used.
-- source:
--   Baldacci, Manziuk, Mastrolia & Rosenbaum, arXiv:1912.01129v1, §2.2.1, pp. 4–6, controlled intensities and printed change-of-measure density.

import Mathlib
import Definitions.Def_MMDarkPool_Exchange_Supplement_Model

namespace MMDarkPool.Exchange.Supplement

/-!
Counterexample to the controlled-measure specification, pp. 4–5 of
arXiv:1912.01129v1. All four posted volumes are 1; both size sets are {1,2}.
Set σ = θ = A = 1, independently of ε. Every baseline λ is exp(-1/2).
The printed density is strictly positive for every path, so any measurable
such density preserves null sets. But the size-2 counting process is assigned
intensity 0, requiring a zero terminal count almost surely. Its reference
terminal mean at T = 1 is ε > 0. This works for arbitrarily small ε while
all order-flow parameters remain fixed.

The arguments activeCounts and activeTimes stand for the integrals of each
inventory/size indicator against dN and dt in the printed density. Allowing
arbitrary real values, subject to measurability of the resulting density,
only strengthens the impossibility certificate: an exponential is positive
regardless of those values. No law of latency marks is used. The reference
Poisson law and the claimed controlled martingale are used only through
their necessary terminal-mean consequences, explicitly recorded in
TerminalMeasureRequirements. This is not a definition of the full model.
-/

/-- A numerical instance; impact r can be arbitrarily small and positive. -/
noncomputable def counterParams (ε r : ℝ) : Params where
  T := 1
  tick := 1
  σ := 1
  γ := 1
  ε := ε
  A := fun _ => 1
  θ := fun _ => 1
  Γ := fun _ => r
  qbar := 1
  V := fun _ => {1, 2}

/-- A constant posting permitted by the source's finite-volume and sum constraints. -/
def counterPosting : Vol := fun _ _ => 1

/-- The source's density at T = 1 after pulling the constant baseline rates
outside the integrals of the inventory/size gates. -/
noncomputable def printedDensity {Ω : Type*} (ε r : ℝ)
    (activeCounts activeTimes : Side → Pool → ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  Real.exp (∑ i : Side, ∑ j : Pool, ∑ k ∈ (counterParams ε r).V j,
    (Real.log (lam (counterParams ε r) i j counterPosting / ε) * activeCounts i j k ω -
      (lam (counterParams ε r) i j counterPosting - ε) * activeTimes i j k ω))

/-- Necessary terminal consequences of the source's simultaneous density and
intensity claims. The reference size-2 count has mean ε; its prescribed zero
controlled compensator and zero initial count would force controlled mean 0.
Integrability is explicit so neither integral can acquire a junk value. -/
def TerminalMeasureRequirements {Ω : Type*} [MeasurableSpace Ω]
    (ε r : ℝ) (μ₀ : MeasureTheory.Measure Ω) (N : Ω → ℕ)
    (activeCounts activeTimes : Side → Pool → ℕ → Ω → ℝ) : Prop :=
  MeasureTheory.IsProbabilityMeasure μ₀ ∧
    Measurable N ∧
    Measurable (printedDensity ε r activeCounts activeTimes) ∧
  MeasureTheory.Integrable (fun ω => (N ω : ℝ)) μ₀ ∧
  (∫ ω, (N ω : ℝ) ∂μ₀) = ε ∧
  ∃ μ : MeasureTheory.Measure Ω,
    μ = μ₀.withDensity (fun ω => ENNReal.ofReal (printedDensity ε r activeCounts activeTimes ω)) ∧
    MeasureTheory.Integrable (fun ω => (N ω : ℝ)) μ ∧
    (∫ ω, (N ω : ℝ) ∂μ) = 0

end MMDarkPool.Exchange.Supplement


