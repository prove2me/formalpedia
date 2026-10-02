-- Prove2me | Definitions.Def_ChapterMixedLinearEsa
-- name    : ChapterMixedLinearEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-02T10:38:30.2873+00:00
-- url     : https://prove2.me/theorems/663b09f8-e752-4e74-bdda-739c2eabe714
-- title:
--   Chapter MixedLinearEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMixedLinearEsa.lean`): generated def bundle for ChapterMixedLinearEsa. See BookProof/ChapterMixedLinearEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMixedLinearEsa.lean

import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterWaveUnboundedPotential
import Mathlib


/-!
# The mixed first-order operator `⟪x, b⟫ − i ∂_m`

`BookProof.ChapterShiftedQuadraticDegenerate` proves essential self-adjointness of the
inhomogeneous quadratic Hamiltonian `H_A + ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` whenever the first-order
coefficients are orthogonal to the kernel of `A`, and records the residual case: in a
kernel direction the Hamiltonian degenerates to the *first-order* operator
`b x + b' π`, which has no `L²` eigenvector, so the Hermite-eigenbasis route cannot see
it.  `BookProof.ChapterFourierMultiplierEsa` settles the purely-momentum part `b' π` by
the Plancherel route.  This module settles the remaining, genuinely mixed case
`b x + b' π` with **both** coefficients non-zero.

## What is proved

* `posOp_essentiallySelfAdjoint` — **the position operator** (multiplication by the real
  linear function `x ↦ ⟪x, b⟫`) is symmetric and essentially self-adjoint on the Schwartz
  core of `L²(V)`.  The deficiency equation is killed by dividing a *compactly supported*
  test function by `⟪x, b⟫ − z̄`, so no Fourier transform is needed;
* `momentum_test_compactSupport_extend` — **compactly supported test functions suffice**
  for the momentum operator: if the deficiency identity of `π_m = −i ∂_m` holds against
  every smooth compactly supported test function, it holds against every Schwartz
  function.  The proof is a cut-off argument: `χ(x/n) f → f` and
  `π_m (χ(·/n) f) → π_m f` pointwise, with a uniform integrable dominating function;
* `gaugeFun`, `hasDerivAt_gaugeFun_line`, `mixedLinearOp_gauge` — **the gauge**: with the
  quadratic phase `θ(x) = −⟪x,b⟫⟪x,m⟫/‖m‖² + ⟪b,m⟫⟪x,m⟫²/(2‖m‖⁴)`, which satisfies
  `∂_m θ = −⟪x, b⟫`, the unimodular factor `e^{iθ}` intertwines the mixed operator with
  the pure momentum operator: `(⟪·,b⟫ − i∂_m)(e^{iθ}φ) = e^{iθ}(−i∂_m φ)`;
* `mixedLinearOp_essentiallySelfAdjoint` — **the headline**: for arbitrary `b, m ∈ V` the
  operator `⟪x, b⟫ − i ∂_m` is symmetric and essentially self-adjoint on the Schwartz core
  of `L²(V)`.  Multiplying a compactly supported test function by `e^{iθ}` keeps it
  compactly supported, which is why the previous item is exactly what the gauge argument
  needs (`e^{iθ}` is *not* known to preserve Schwartz space here).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.MixedLinearEsa

open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ## 1. The position operator -/



/-- Multiplication by the real linear function `x ↦ ⟪x, b⟫` on Schwartz space. -/
noncomputable def posOp (b : V) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  smulLeftCLM ℂ (fun x => ((inner ℝ x b : ℝ) : ℂ))











/-! ## 2. The mixed operator -/

/-- The mixed first-order operator `⟪x, b⟫ − i ∂_m`. -/
noncomputable def mixedLinearOp (b m : V) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  posOp b + momentumOp m









/-! ## 3. Compactly supported test functions suffice for the momentum operator -/



/-- Multiplying a Schwartz function by a smooth compactly supported real function. -/
noncomputable def cutSchwartz (g : V → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgcs : HasCompactSupport g) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ((hgcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).mul_right).toSchwartzMap
    ((Complex.ofRealCLM.contDiff.comp hg).mul (f.smooth ⊤))











/-! ## 4. The gauge -/

/-- The quadratic phase `θ(x) = −⟪x,b⟫⟪x,m⟫/‖m‖² + ⟪b,m⟫⟪x,m⟫²/(2‖m‖⁴)`, whose derivative
along `m` is `−⟪x, b⟫`. -/
noncomputable def gaugePhase (b m : V) (x : V) : ℝ :=
  -(inner ℝ x b) * (inner ℝ x m) / ‖m‖ ^ 2
    + (inner ℝ b m) * (inner ℝ x m) ^ 2 / (2 * ‖m‖ ^ 4)

/-- The unimodular gauge factor `e^{iθ}`. -/
noncomputable def gaugeFun (b m : V) (x : V) : ℂ :=
  Complex.exp (Complex.I * ((gaugePhase b m x : ℝ) : ℂ))





omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma contDiff_gaugePhase (b m : V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gaugePhase b m) := by
  unfold gaugePhase
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : V => (inner ℝ x b : ℝ)) :=
    ((innerSL ℝ).flip b).contDiff
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : V => (inner ℝ x m : ℝ)) :=
    ((innerSL ℝ).flip m).contDiff
  exact ((h1.neg.mul h2).div_const _).add ((contDiff_const.mul (h2.pow 2)).div_const _)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma contDiff_gaugeFun (b m : V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gaugeFun b m) := by
  unfold gaugeFun
  exact ((Complex.contDiff_exp (𝕜 := ℂ)).restrict_scalars ℝ).comp
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_gaugePhase b m)))



/-- The gauged test function `e^{iθ}φ`: still smooth and compactly supported, hence still a
Schwartz function.  (Multiplication by `e^{iθ}` is *not* claimed to preserve Schwartz space
in general.) -/
noncomputable def gaugeSchwartz (b m : V) (φ : 𝓢(V, ℂ))
    (hφ : HasCompactSupport (φ : V → ℂ)) : 𝓢(V, ℂ) :=
  (hφ.mul_left (f := gaugeFun b m)).toSchwartzMap
    ((contDiff_gaugeFun b m).mul (φ.smooth ⊤))





/-! ## 5. Essential self-adjointness of the mixed operator -/





/-! ## 6. An arbitrary potential with a gauge along `m`

The gauge argument never uses that the potential is *linear*: it uses only that the phase
`θ` solves the transport equation `∂_m θ = −W` along the momentum direction.  Written that
way it is an instrument, and it covers unbounded polynomial potentials — for instance the
quartic `x⁴ − i d/dx` on `L²(ℝ)`, which is neither a Fourier multiplier nor an operator
with an `L²` eigenvector. -/

/-- The operator `W(x) − i ∂_m`: an arbitrary real potential of temperate growth plus a
momentum term. -/
noncomputable def potMomOp (W : V → ℝ) (m : V) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  potentialOp W + momentumOp m





/-- The unimodular gauge factor `e^{iθ}` of an arbitrary real phase. -/
noncomputable def phaseFun (θ : V → ℝ) (x : V) : ℂ :=
  Complex.exp (Complex.I * ((θ x : ℝ) : ℂ))



omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma contDiff_phaseFun {θ : V → ℝ} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (phaseFun θ) := by
  unfold phaseFun
  exact ((Complex.contDiff_exp (𝕜 := ℂ)).restrict_scalars ℝ).comp
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hθ))



/-- The gauged test function `e^{iθ}φ`, still smooth and compactly supported. -/
noncomputable def phaseSchwartz {θ : V → ℝ} (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (φ : 𝓢(V, ℂ)) (hφ : HasCompactSupport (φ : V → ℂ)) : 𝓢(V, ℂ) :=
  (hφ.mul_left (f := phaseFun θ)).toSchwartzMap ((contDiff_phaseFun hθ).mul (φ.smooth ⊤))









/-! ## 7. Polynomial potentials along the momentum direction -/

/-- The polynomial potential `W(x) = ∑_{i<n} cᵢ ⟪x, m⟫ⁱ` in the momentum direction. -/
noncomputable def polyPotential (c : ℕ → ℝ) (n : ℕ) (m : V) (x : V) : ℝ :=
  ∑ i ∈ Finset.range n, c i * (inner ℝ x m : ℝ) ^ i

/-- Its transport phase `θ(x) = −∑_{i<n} cᵢ ⟪x,m⟫^{i+1}/((i+1)‖m‖²)`. -/
noncomputable def polyPhase (c : ℕ → ℝ) (n : ℕ) (m : V) (x : V) : ℝ :=
  ∑ i ∈ Finset.range n, -(c i * (inner ℝ x m : ℝ) ^ (i + 1) / ((i + 1) * ‖m‖ ^ 2))











end BookProof.MixedLinearEsa


