-- Prove2me | Definitions.Def_ChapterQgOuterFockOneParticle
-- name    : ChapterQgOuterFockOneParticle
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T03:08:53.765785+00:00
-- url     : https://prove2.me/theorems/6ce6963c-b252-472a-8dc5-c3124040455a
-- title:
--   Chapter QgOuterFockOneParticle
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQgOuterFockOneParticle.lean`): generated def bundle for ChapterQgOuterFockOneParticle. See BookProof/ChapterQgOuterFockOneParticle.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockOneParticle.lean

import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronFiberFL
import Mathlib


/-!
# The outer Fock Hamiltonian is a one-particle operator between `a†` and `a`

The quantum-gravity Hamiltonian of `BookProof.ScalaronOuterFockFL` acts on a *Fock space of a
Fock space*: the outer Hilbert space `Sec ι = ℓ²(ι ; L²(ℝ_φ))` carries one excitation labelled
by a vielbein mode configuration `a : ι`, and the inner Hilbert space `L²(ℝ_φ)` is the
scalaron line.  The outer Hamiltonian is *number conserving* and *one-particle*: it is of the
form

`H = Σ_{a,b} a†_a  h_{ab}  a_b`,

where the one-particle kernel `h_{ab}` is an operator on the inner space.  This file makes
that structure explicit and completely elementary:

* `oneParticleOp W Q a b` is the kernel
  `h_{ab} = δ_{ab} (−d²/dφ² + φ²/4 + V(φ) + σ_b) + A_{ab} · 1 + B_{ab} · φ`,
  i.e. the fibre scalaron Hamiltonian with the **full exponential** wall on the diagonal, the
  vielbein self-interaction `A` and the scalaron–vielbein coupling `B` off it;
* `secHam_single`: applying `H` to a single-mode state `a†_b u |0⟩` gives the column
  `a ↦ h_{ab} u` of the kernel;
* `secHam_matrix_element`: `⟪a†_a v, H a†_b u⟫ = ⟪v, h_{ab} u⟫` — the promised sandwich of the
  one-particle operator between a creation operator on the left and an annihilation operator
  on the right;
* `oneParticleOp_herm`: the kernel is Hermitian, `h_{ba}^* = h_{ab}`;
* `secHam_eq_sum_oneParticle`: on the whole core, `H` is reassembled from its kernel,
  `(Hx)_a = Σ_b h_{ab} x_b`, the sum being finite because of the band structure.

Nothing here is an extra hypothesis: it is a description of the operator whose essential
self-adjointness is proved by the Faris–Lavine argument in
`BookProof.ScalaronOuterFockFL`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgOuterFockOneParticle

open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL

noncomputable section

variable {ι : Type*} [DecidableEq ι] (W : WallPot) (Q : QgModeData ι)



/-- **The one-particle kernel** of the gauge-fixed quantum-gravity Hamiltonian:
`h_{ab} = δ_{ab}(−d²/dφ² + φ²/4 + V(φ) + σ_b) + A_{ab}·1 + B_{ab}·φ`, an operator from the
scalaron core to the scalaron line. -/
def oneParticleOp (a b : ι) : ccDomain ℝ →ₗ[ℂ] L2R :=
  (if a = b then W.ham (Q.sig b) else 0) + Q.A a b • (ccDomain ℝ).subtype + Q.B a b • xCc

@[simp] theorem oneParticleOp_apply (a b : ι) (u : ccDomain ℝ) :
    oneParticleOp W Q a b u
      = (if a = b then W.ham (Q.sig b) u else 0) + Q.A a b • (u : L2R) + Q.B a b • xCc u := by
  simp only [oneParticleOp, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply]
  by_cases h : a = b <;> simp [h]











/-! ## The physical continuum instance -/

section Continuum

open BookProof.QgContinuumModeInstance



end Continuum

end

end BookProof.QgOuterFockOneParticle


