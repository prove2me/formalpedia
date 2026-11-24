-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T15:44:00.873168+00:00
-- url     : https://prove2.me/theorems/1139d726-c77f-4a7d-b9e0-33d879a67f4c
-- title:
--   Long Weyl Element
-- statement:
--   Definitions and structural lemmas for Long Weyl Element, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x5__Heis_eq_adc2ccc881fd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
namespace Formalism.FourierDecayAlt.P.LongWeylElement
section PartL
def mid (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) : Prop := 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
def blk (k r' : ℕ) (x : Mt k (1 + r')) : Mt k r' := fun s t => x (levPos k 1 r' s) (levPos k 1 r' t)
end PartL
section PartW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
def iZ (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩
def iL (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩
end PartW
section PartU
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end PartU
section PartF
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
abbrev midW (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k
end PartF
section PartG
section General
variable {α α' β β' : Type*} [MeasurableSpace α] [MeasurableSpace α'] [MeasurableSpace β] [MeasurableSpace β']
end General
def splitC (r' : ℕ) (c : Fin (1 + r') → ℂ) : ℂ × (Fin r' → ℂ) := (c (a0 r'), fun a => c (Fin.natAdd 1 a))
def splitE (r' : ℕ) : (Fin (1 + r') → ℂ) ≃ᵐ ℂ × (Fin r' → ℂ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (finCongr (Nat.add_comm r' 1))).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0)
end PartG
section PartM
variable {k r r' : ℕ}
def adjF (x : Mt k r) : Mt k r := (Matrix.of x : Mat k r).adjugate
def detF (x : Mt k r) : ℂ := (Matrix.of x : Mat k r).det
def heisF (k r' : ℕ) (x : HPar k r') : Mt k (1 + r') := heis0 k r' x
def bcF (k r : ℕ) (c : Fin r → ℂ) : Mt k r := bigCell k r c 1
def w0F (k r' : ℕ) (c : ℂ) : Mt k (1 + r') := w0 k r' c
end PartM
section PartK
variable {k r r' : ℕ}
def thetaF (k r' : ℕ) (p : HPar k r' × Mt k r') : Mt k (1 + r') := mulM (levM k r' p.2, heisF k r' p.1)
theorem μHeis_eq (k r' : ℕ) : μHeis k r' = (volume : Measure (HPar k r')).map (heisF k r') := rfl
theorem sfHeis : SFinite (μHeis k r') := by
  rw [μHeis_eq]
  infer_instance
attribute [local instance] sfHeis
end PartK
section PartS
variable {k r r' : ℕ}
def IterAt (k r : ℕ) : Prop :=
  ∀ (μG μN μb : Measure (Mt k r)), IsHaarOn (GV k r) μG → IsHaarOn (Nset k r) μN → IsHaarOn (UWb k r) μb →
    ∃ C : ℝ≥0, 0 < C ∧ ∀ f : Mt k r → ℝ≥0∞, Measurable f →
      (∫⁻ g, f g ∂μG) = (C : ℝ≥0∞) * ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (cWeight k r c) *
        ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
          f ((Matrix.of p.1.1)⁻¹ * bigCell k r c 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb)
end PartS
end Formalism.FourierDecayAlt.P.LongWeylElement
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


