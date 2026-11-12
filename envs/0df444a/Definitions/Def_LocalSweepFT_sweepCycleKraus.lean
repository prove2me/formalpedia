-- Prove2me | Definitions.Def_LocalSweepFT_sweepCycleKraus
-- name    : LocalSweepFT_sweepCycleKraus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:43:17.252669+00:00
-- url     : https://prove2.me/theorems/a3797994-6fd3-42c0-81f7-cd841def246f
-- title:
--   The sweep cycle as a quantum channel on one register
-- statement:
--   Fix a sweep rule $\mathrm{rule}_1$ for the $(d,d')$ complex and a sweep rule $\mathrm{rule}_2$ for the dual $(d,d-d')$ complex. The **sweep cycle** on a register is
--   1. measure the X-syndrome $\sigma=\partial^-y$ and flip the chain returned by one parallel step of $\mathrm{rule}_1$ (Kraus operators $X^{\mathrm{step}(\sigma)}\Pi_\sigma$, $\Pi_\sigma$ the projector on basis states with syndrome $\sigma$);
--   2. apply $\hat H_\phi=\phi\circ H^{\otimes F^n_{d'}}$, moving to the $(d,d-d')$-Toric code;
--   3. the same step with $\mathrm{rule}_2$ on the dual register;
--   4. apply $\hat H_\phi^\dagger$.
--
--   This is the time-independent correction cycle of the construction: the even layers of a Toric encoded circuit apply it to every register.
--
--   **Formalization Note** The two sectors have independent rules. The cycle sees no faults inside it (p.14: "we are allowed to assume having constant depth cycles that don't observe faults").
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Definition 4.9, p.21; Definition 4.31 and Claim 4.33, pp.32–33

import Mathlib
import Definitions.Def_LocalSweepFT_Chain
import Definitions.Def_LocalSweepFT_IsSweepRule
import Definitions.Def_LocalSweepFT_liftOn
import Definitions.Def_LocalSweepFT_encMat

open Matrix

namespace LocalSweepFT

/-! Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…): the sweep cycle (Def 4.9, p.21) on one register of the
`(d, d′)`-Toric code, as a quantum channel. -/

variable {d d' n : ℕ} [NeZero n]

open Classical in
/-- The projector `Π_σ = Σ_{y : ∂⁻y = σ} |y⟩⟨y|` onto the basis states of a register whose
X-syndrome (Def 4.3: the checks on `F_{d′−1}` with matrix `∂⁻`) is `σ`. -/
noncomputable def syndromeProj (σ : QCell d (d' - 1) n → ZMod 2) : Op (QCell d d' n) :=
  fun a b => if a = b ∧ ⇑(bdry (toChain b)) = σ then 1 else 0

/-- One parallel application of the sweep rule `rule` at every vertex, in the computational basis
(Def 4.9, stage 1): measure the X-syndrome `σ` and flip `sweepStep rule σ`. Kraus operators
`X^{sweepStep rule σ} Π_σ`, one per syndrome `σ`. -/
noncomputable def xStepKraus (rule : LocalRule d d') : List (Op (QCell d d' n)) :=
  (Finset.univ : Finset (QCell d (d' - 1) n → ZMod 2)).toList.map
    fun σ => xOn ⇑(sweepStep rule (toChain σ)) * syndromeProj σ

/-- `ϕ ∘ H^{⊗F^n_{d′}}` (Def 4.9, stage 2; Claim 4.33, p.33): the transversal Hadamard followed by
moving the qubit on the `d′`-cell `c` to the `(d − d′)`-cell `ϕ(c)` of the dual register. -/
noncomputable def dualU (h : d' + (d - d') = d) :
    Matrix (QCell d (d - d') n → ZMod 2) (QCell d d' n → ZMod 2) ℂ :=
  fun b a => ((Real.sqrt 2 : ℂ)⁻¹) ^ Fintype.card (QCell d d' n) *
    sgn (∑ c : QCell d d' n, b (phiCell h c) * a c)

/-- The sweep cycle (Def 4.9, p.21) on one register, as a Kraus family:
1. the sweep rule `rule₁` at each vertex in the computational basis;
2. `H^{⊗F^n_{d′}}` followed by the `ϕ`-transpose, into the `(d, d − d′)`-Toric code;
3. the sweep rule `rule₂` at each vertex of the dual code;
4. the inverse of stage 2.

**Formalization Note.** The two sectors have independent rules `rule₁ : LocalRule d d′` and
`rule₂ : LocalRule d (d − d′)`. The cycle is one layer of the circuit model and sees no faults
inside it (p.14: "we are allowed to assume having constant depth cycles that don't observe
faults"). -/
noncomputable def sweepCycleKraus (h : d' + (d - d') = d) (rule₁ : LocalRule d d')
    (rule₂ : LocalRule d (d - d')) : List (Op (QCell d d' n)) :=
  compK (xStepKraus rule₁)
    (compK [dualU h] (compK (xStepKraus rule₂) [(dualU h).conjTranspose]))

end LocalSweepFT


