-- Prove2me | Definitions.Def_ChapterScalaronCoreEsa
-- name    : ChapterScalaronCoreEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-15T11:37:03.457522+00:00
-- url     : https://prove2.me/theorems/30534c3e-f188-46a1-97ae-3c7de4a714a8
-- title:
--   The scalaron sector: essential self-adjointness with an exponentially growing potential The point What is proved Honest boundary
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.ScalaronCoreEsa`, source chapter `BookProof/ChapterScalaronCoreEsa.lean`): The scalaron sector: essential self-adjointness with an exponentially growing potential The point What is proved Honest boundary
--
--   Plan item **A5** (`CONSOLIDATED_PLAN.md` §10.5), the step that the Starobinsky wave left open at the *continuum* level: the Einstein-frame scalaron potential
--
--   `V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²`
--
--   is **not** of temperate growth — it grows exponentially as `φ → −∞`, so the multiplication-operator theorem of `BookProof.ChapterWaveUnboundedPotential` (`potentialOp_essentiallySelfAdjoint`, stated for potentials of temperate growth on the Schwartz core) does not apply to it. This module removes that restriction.
--
--   Temperate growth is needed only to make the *Schwartz* core invariant. On the smaller — and still dense — core of **smooth compactly supported** functions no growth hypothesis is needed at all: multiplication by any smooth real function maps the core into itself, and the deficiency argument of `ChapterWaveUnboundedPotential` (divide a test bump `χ` by the nowhere-vanishing smooth function `W − z̄`) stays inside the core. What survives of the analytic hypotheses is only what the plan records: *the operator must be defined on a dense core*, and for the combination with the kinetic term the potential must be *bounded below* — and the Starobinsky potential is bounded below in the strongest way, being a square.
--
--   **1. The compactly supported smooth core.** `ccDomain E` is the image in `L²(E)` of the smooth compactly supported functions, `ccDomain_dense` its density, and `ccDomain_le_schwartzDomain` the inclusion in the Schwartz core.
--
--   **2. Multiplication by an arbitrary smooth potential.** `opCc W hW` is multiplication by a real `W`, assumed *only* smooth: `smoothPotential_symmetric`, `smoothPotential_deficiencyTrivial` (at every non-real `z`) and `smoothPotential_essentiallySelfAdjoint`. No growth, no boundedness and no semiboundedness hypothesis.
--
--   **3. The scalaron potential.** `contDiff_starobinskyV`; `starobinskyV_not_hasTemperateGrowth` — the potential genuinely falls outside the temperate class, so item 2 is needed; `starobinskyV_essentiallySelfAdjoint` — and it is nevertheless essentially self-adjoint on the compactly supported core, as is the full `V₃(R_c) + V(φ)` potential of the gauge-fixed `R + αR²` Hamiltonian (`scalaronFullPotential_essentiallySelfAdjoint`), which is moreover bounded below by `−M⁴/(16α)` (`scalaronFullPotential_ge`).
--
--   **4. The d'Alembertian with the scalaron potential.** `wave_add_scalaron_symmetric` — the gauge-fixed Hamiltonian `□ + V` is a well-defined symmetric operator on the dense compactly supported core, and `wave_add_smoothTruncatedPotential_essentiallySelfAdjoint` — every localization of it is essentially self-adjoint on the Schwartz core, again with smoothness as the only hypothesis on the potential (`wave_add_scalaronTruncated_esa` for the scalaron potential itself). This is the exponential-growth analogue of `wave_add_truncatedPotential_essentiallySelfAdjoint`.
--
--   **5. The full mode Hamiltonian with the scalaron sector, and its flow.** At the mode level the gravity fiber operator is multiplication by `(1/16)a_k² − (1/24)b_k² + V₃(R_c k) + V(φ_k)`: `qgScalaronMode_esa` (essential self-adjointness on the dense maximal domain), `qgScalaronMode_potential_ge` (the uniform lower bound `−M⁴/(16α)`, unaffected by the non-negative scalaron term) and **`qgScalaron_stone_flow`** — the complete unitary group of the `R + αR²` Hamiltonian *including* the scalaron potential.
--
--   Unchanged from `CONSOLIDATED_PLAN.md` §10.3/§10.5: the continuum `L²(ℝ⁸⁴)` essential self-adjointness of the *sum* `□ + V` still needs the Strichartz finite-speed / gluing input, which is not claimed here. What this module settles is the point at issue for the scalaron: the exponential wall is not an obstruction — the potential term is essentially self-
--
--   ...
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

import Definitions.Def_ChapterStarobinskyPotential
import Mathlib
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStrichartzWave


/-!
# The scalaron sector: essential self-adjointness with an exponentially growing potential

Plan item **A5** (`CONSOLIDATED_PLAN.md` §10.5), the step that the Starobinsky wave left
open at the *continuum* level: the Einstein-frame scalaron potential

`V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²`

is **not** of temperate growth — it grows exponentially as `φ → −∞`, so the
multiplication-operator theorem of `BookProof.ChapterWaveUnboundedPotential`
(`potentialOp_essentiallySelfAdjoint`, stated for potentials of temperate growth on the
Schwartz core) does not apply to it.  This module removes that restriction.

## The point

Temperate growth is needed only to make the *Schwartz* core invariant.  On the smaller —
and still dense — core of **smooth compactly supported** functions no growth hypothesis is
needed at all: multiplication by any smooth real function maps the core into itself, and the
deficiency argument of `ChapterWaveUnboundedPotential` (divide a test bump `χ` by the
nowhere-vanishing smooth function `W − z̄`) stays inside the core.  What survives of the
analytic hypotheses is only what the plan records: *the operator must be defined on a dense
core*, and for the combination with the kinetic term the potential must be *bounded below*
— and the Starobinsky potential is bounded below in the strongest way, being a square.

## What is proved

**1. The compactly supported smooth core.**  `ccDomain E` is the image in `L²(E)` of the
smooth compactly supported functions, `ccDomain_dense` its density, and
`ccDomain_le_schwartzDomain` the inclusion in the Schwartz core.

**2. Multiplication by an arbitrary smooth potential.**  `opCc W hW` is multiplication by a
real `W`, assumed *only* smooth: `smoothPotential_symmetric`,
`smoothPotential_deficiencyTrivial` (at every non-real `z`) and
`smoothPotential_essentiallySelfAdjoint`.  No growth, no boundedness and no semiboundedness
hypothesis.

**3. The scalaron potential.**  `contDiff_starobinskyV`; `starobinskyV_not_hasTemperateGrowth`
— the potential genuinely falls outside the temperate class, so item 2 is needed;
`starobinskyV_essentiallySelfAdjoint` — and it is nevertheless essentially self-adjoint on
the compactly supported core, as is the full `V₃(R_c) + V(φ)` potential of the gauge-fixed
`R + αR²` Hamiltonian (`scalaronFullPotential_essentiallySelfAdjoint`), which is moreover
bounded below by `−M⁴/(16α)` (`scalaronFullPotential_ge`).

**4. The d'Alembertian with the scalaron potential.**  `wave_add_scalaron_symmetric` — the
gauge-fixed Hamiltonian `□ + V` is a well-defined symmetric operator on the dense compactly
supported core, and `wave_add_smoothTruncatedPotential_essentiallySelfAdjoint` — every
localization of it is essentially self-adjoint on the Schwartz core, again with smoothness
as the only hypothesis on the potential (`wave_add_scalaronTruncated_esa` for the scalaron
potential itself).  This is the exponential-growth analogue of
`wave_add_truncatedPotential_essentiallySelfAdjoint`.

**5. The full mode Hamiltonian with the scalaron sector, and its flow.**  At the mode level
the gravity fiber operator is multiplication by `(1/16)a_k² − (1/24)b_k² + V₃(R_c k) +
V(φ_k)`: `qgScalaronMode_esa` (essential self-adjointness on the dense maximal domain),
`qgScalaronMode_potential_ge` (the uniform lower bound `−M⁴/(16α)`, unaffected by the
non-negative scalaron term) and **`qgScalaron_stone_flow`** — the complete unitary group of
the `R + αR²` Hamiltonian *including* the scalaron potential.

## Honest boundary

Unchanged from `CONSOLIDATED_PLAN.md` §10.3/§10.5: the continuum `L²(ℝ⁸⁴)` essential
self-adjointness of the *sum* `□ + V` still needs the Strichartz finite-speed / gluing
input, which is not claimed here.  What this module settles is the point at issue for the
scalaron: the exponential wall is not an obstruction — the potential term is essentially
self-adjoint on a dense core with no growth hypothesis, every localization of the sum is
essentially self-adjoint, and the potential has the correct (bounded below) sign.
-/

open Filter Topology MeasureTheory SchwartzMap

namespace BookProof.ScalaronEsa

open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## 1. The compactly supported smooth core -/

/-- The compactly supported Schwartz functions, as a submodule of `𝓢(E, ℂ)`. -/
def ccSchwartz (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Submodule ℂ 𝓢(E, ℂ) where
  carrier := {f | HasCompactSupport (f : E → ℂ)}
  add_mem' := by
    intro f g hf hg
    have h : HasCompactSupport ((f : E → ℂ) + (g : E → ℂ)) := hf.add hg
    refine h.mono ?_
    intro x hx
    simp only [Function.mem_support, SchwartzMap.add_apply] at hx ⊢
    simpa using hx
  zero_mem' := by
    have h : HasCompactSupport (fun _ : E => (0 : ℂ)) := HasCompactSupport.zero
    exact h.mono (by intro x hx; simp at hx)
  smul_mem' := by
    intro c f hf
    refine hf.mono ?_
    intro x hx
    simp only [Function.mem_support, SchwartzMap.smul_apply, smul_eq_mul, ne_eq] at hx ⊢
    intro h
    exact hx (by simp [h])



/-- The compactly supported smooth functions, mapped into `L²(E)`. -/
def ccInclLM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ccSchwartz E →ₗ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (toLpCLM ℂ ℂ 2 (volume : Measure E)).toLinearMap ∘ₗ (ccSchwartz E).subtype



lemma ccInclLM_injective : Function.Injective (ccInclLM E) := by
  intro f g hfg
  exact Subtype.ext (SchwartzMap.injective_toLp 2 (volume : Measure E) hfg)

/-- **The compactly supported smooth core** of `L²(E)`. -/
def ccDomain (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    Submodule ℂ (Lp ℂ 2 (volume : Measure E)) := LinearMap.range (ccInclLM E)

/-- Compactly supported smooth functions are in bijection with the core. -/
def ccEquiv (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ccSchwartz E ≃ₗ[ℂ] ccDomain E :=
  LinearEquiv.ofInjective (ccInclLM E) ccInclLM_injective



/-- The compactly supported core sits inside the Schwartz core. -/
lemma ccDomain_le_schwartzDomain : ccDomain E ≤ schwartzDomain E := by
  rintro _ ⟨f, rfl⟩
  exact ⟨(f : 𝓢(E, ℂ)), rfl⟩



/-! ## 2. Multiplication by an arbitrary smooth real potential -/

/-- Multiplication by a real `W`, as a map of the compactly supported core into Schwartz
space.  Only smoothness of `W` is required: compact support of `f` does the rest. -/
def mulCc (W : E → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    ccSchwartz E →ₗ[ℂ] 𝓢(E, ℂ) where
  toFun f :=
    (HasCompactSupport.mul_left f.2 :
        HasCompactSupport (fun x => (W x : ℂ) * (f : 𝓢(E, ℂ)) x)).toSchwartzMap
      ((Complex.ofRealCLM.contDiff.comp hW).mul ((f : 𝓢(E, ℂ)).smooth _))
  map_add' f g := by
    refine SchwartzMap.ext fun x => ?_
    change (W x : ℂ) * ((f : 𝓢(E, ℂ)) x + (g : 𝓢(E, ℂ)) x)
      = (W x : ℂ) * (f : 𝓢(E, ℂ)) x + (W x : ℂ) * (g : 𝓢(E, ℂ)) x
    ring
  map_smul' c f := by
    refine SchwartzMap.ext fun x => ?_
    change (W x : ℂ) * (c • (f : 𝓢(E, ℂ))) x = c • ((W x : ℂ) * (f : 𝓢(E, ℂ)) x)
    simp only [SchwartzMap.smul_apply, smul_eq_mul]
    ring



/-- Multiplication by a smooth real potential, as an unbounded operator on `L²(E)` with the
compactly supported smooth core as its domain. -/
def opCc (W : E → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    ccDomain E →ₗ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (toLpCLM ℂ ℂ 2 (volume : Measure E)).toLinearMap ∘ₗ mulCc W hW ∘ₗ
    (ccEquiv E).symm.toLinearMap











/-! ## 3. The Starobinsky scalaron potential -/









/-- The full gauge-fixed `R + αR²` potential: the regularized conformal-mode parabola plus
the Einstein-frame scalaron potential, as a function of `(R_c, φ)` read off a pair of
directions of the field space. -/
def scalaronFullPotential (M alpha : ℝ) (eRc ephi : E) (x : E) : ℝ :=
  confV M alpha (inner ℝ x eRc) + starobinskyV M alpha (inner ℝ x ephi)







/-! ## 4. The d'Alembertian with the scalaron potential -/

/-- The d'Alembertian, restricted to the compactly supported smooth core. -/
def waveCc (n : ℕ) : ccDomain (SpaceTime n) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (SpaceTime n)) :=
  opL2 (waveOp n 0) ∘ₗ Submodule.inclusion ccDomain_le_schwartzDomain

/-- **The gauge-fixed Hamiltonian `□ + W`** on the compactly supported smooth core, for an
arbitrary smooth real potential. -/
def waveAddSmoothPotential (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    ccDomain (SpaceTime n) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (SpaceTime n)) :=
  waveCc n + opCc W hW

















/-! ## 5. The mode Hamiltonian with the scalaron sector, and its flow -/

variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc phi : ℕ → ℝ)

/-- The full `R + αR²` mode potential: the regularized conformal-mode parabola plus the
Einstein-frame scalaron potential. -/
def qgScalaronModePotential : ℕ → ℝ :=
  fun k => confV M alpha (Rc k) + starobinskyV M alpha (phi k)

/-- **The gauge-fixed `R + αR²` mode Hamiltonian including the scalaron sector**:
multiplication by `(1/16)a_k² − (1/24)b_k² + V₃(R_c k) + V(φ_k)`. -/
def qgScalaronModeHamiltonian :
    mulSymbolDomain (qgModeSymbol a b (qgScalaronModePotential M alpha Rc phi)) →ₗ[ℂ] L2Nat :=
  qgModeHamiltonian a b (qgScalaronModePotential M alpha Rc phi)











end

end BookProof.ScalaronEsa


