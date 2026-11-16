-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_Supplement_Quantum
-- name    : PSPACEOracleSynth_Main_Supplement_Quantum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:23:07.639204+00:00
-- url     : https://prove2.me/theorems/6a15e3cb-2f3b-43bb-9307-9c2a0b001169
-- title:
--   Finite channels, partial isometries, completions and distances
-- statement:
--   Registers are finite qubit spaces. A state is a positive semidefinite matrix of trace one, and a pure state is the rank-one operator of a unit ket. This module reuses the published finite Kraus-channel and instrument objects. It defines applying a channel while leaving a reference register untouched, trace distance $D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$, and the full diamond norm of channel differences over all pure inputs and reference qubit registers.
--
--   A partial isometry is $U=Y\Pi$, with $Y^\dagger Y=I$ and $\Pi$ an orthogonal projector. Its channel completions satisfy $\Phi(\Pi\rho\Pi)=U\rho U^\dagger$ for every state, including the zero-support case. The memory marginal is the unnormalized matrix $\langle\chi|\Omega|\chi\rangle$. These objects are shared by the channel and interaction statements.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, pp. 9, 13–14, 39

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms QAlgorithms.Complexity
open scoped Matrix ComplexOrder Kronecker ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace PSPACEOracleSynth.Main.Supplement

/-! Wang, STOC 2027 submission #1740, pp. 9, 13–14: finite quantum objects.
The general channel and instrument objects are the published Kraus models. -/

abbrev Op (I : Type) := Matrix I I ℂ
abbrev Map (I O : Type) := Superop I O

/-- A ket's rank-one operator; no normalization is silently imposed. -/
def ket {I : Type} (v : I → ℂ) : Op I := fun a b => v a * star (v b)

def UnitKet {I : Type} [Fintype I] (v : I → ℂ) : Prop := ∑ i, ‖v i‖ ^ 2 = 1

/-- Applying a map to the first register, leaving all reference coherences intact. -/
def withRef {I O R : Type} (C : Map I O) : Map (I × R) (O × R) :=
  fun X a b => C (fun i j => X (i, a.2) (j, b.2)) a.1 b.1

/-- Half the trace norm, p. 9. -/
noncomputable def dist {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Op I) : ℝ :=
  traceNorm (ρ - σ) / 2

/-- The full diamond norm for differences of channels, p. 9. The supremum is in ℝ≥0∞;
all qubit reference registers, including zero qubits, and all unit pure inputs are covered. -/
noncomputable def diamond {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (C : Map I O) : ℝ≥0∞ :=
  ⨆ (r : ℕ) (ψ : I × Bits r → ℂ) (_ : UnitKet ψ),
    ENNReal.ofReal (traceNorm (withRef C (ket ψ)))

/-- Normalization is used only under a positive trace hypothesis. -/
noncomputable def normalized {I : Type} [Fintype I] (ρ : Op I) : Op I :=
  ((ρ.trace.re : ℂ)⁻¹) • ρ

/-- Partial isometry U=YΠ, pp. 13–14. Zero and full support are both allowed. -/
structure PartialIso (a b : ℕ) where
  projector : Op (Bits a)
  hermitian : projectorᴴ = projector
  idempotent : projector * projector = projector
  iso : Matrix (Bits b) (Bits a) ℂ
  isometry : isoᴴ * iso = 1

noncomputable def PartialIso.mat {a b : ℕ} (U : PartialIso a b) := U.iso * U.projector

/-- Agreement on the support, including the zero-support case; p. 14. -/
def Completion {a b : ℕ} (U : PartialIso a b) (Φ : Map (Bits a) (Bits b)) : Prop :=
  IsChannel Φ ∧ ∀ ρ, IsDensityMatrix ρ →
    Φ (U.projector * ρ * U.projector) = U.mat * ρ * U.matᴴ

/-- The specified unnormalized memory marginal ⟨χ|Ω|χ⟩, p. 39. -/
noncomputable def memoryMarginal {C M : Type} [Fintype C]
    (χ : C → ℂ) (Ω : Op (C × M)) : Op M :=
  fun a b => ∑ i, ∑ j, star (χ i) * Ω (i,a) (j,b) * χ j

end PSPACEOracleSynth.Main.Supplement


