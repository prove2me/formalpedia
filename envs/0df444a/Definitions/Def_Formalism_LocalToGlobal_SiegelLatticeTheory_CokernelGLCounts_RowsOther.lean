-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:46:44.522109+00:00
-- url     : https://prove2.me/theorems/1fb2f556-5e45-4ace-b8ac-60ff220efffb
-- title:
--   Rows Other
-- statement:
--   Definitions and structural lemmas for Rows Other, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Formalism.L2.SG.RowsOther
open Formalism.FourierDecayAlt
section Gen
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
def KppTermZero : Prop := ∀ t ∈ X.degSet, X.op t = 0
def KppOff : Prop := X.part X.degSet = 0
def KppDiag (du : ℝ) (k f : ℕ) : Prop :=
  ‖X.part X.degSet‖ ^ 2 ≤ du * Real.exp (-((k : ℝ) * f * Real.log k))
def PairsDeg (Pg du : ℝ) (k f : ℕ) : Prop :=
  Pg * X.pairAbs (X.allPairs X.degSet) ≤ du * Real.exp (-((k : ℝ) * f * Real.log k))
def IdOne (one : H) : Prop := X.part X.idSet = one
def DiagRow (one : H) (Gm dd : ℝ) : Prop := ‖X.K0 - one‖ ^ 2 ≤ Gm * dd
def noId : PB.Terms τ Rw I H H₁ := { X with isId := fun _ => False }
section Loops
def PP : Set (τ × τ) := X.big X.nzSet ∪ X.nsc X.genSet
def ampSum (Q : Set (τ × τ)) : ℝ := ∑' p : τ × τ, Q.indicator (fun p => ‖X.vec p.1‖ * ‖X.vec p.2‖) p
def LoopsAmp (A C : ℝ) (k r f : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ) : Prop :=
  Summable ((PP X).indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖)) ∧
  X.Gam1 * ampSum X (PP X) ≤
    A * (∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v Gam Xi +
      Gam ^ 2 * ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v Gam Xi +
      C ^ f * Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C (2 * r + 2) f b ^ (C * ((2 * r + 2 : ℕ) : ℝ) ^ 3) * Gam *
        Real.exp (C * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * f * Real.log b) *
        Real.sqrt ((C * g⁻¹ ^ (2 * r + 1) * ((k : ℝ) ^ r)⁻¹) ^ (k * f))) * dd
def PairsDegAmp (Pg du : ℝ) (k f : ℕ) : Prop :=
  Summable ((X.allPairs X.degSet).indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖)) ∧
  Pg * (X.Gam1 * ampSum X (X.allPairs X.degSet)) ≤ du * Real.exp (-((k : ℝ) * f * Real.log k))
end Loops
section NG
variable {E : Type} [Field E] [NumberField E] {r : ℕ} {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu)
def NGFin (k f C1 C0 : ℕ) (rd g TT AAre e1 : ℝ) : Prop :=
  PN.ClassInput X N ∧ PN.AmpInput X N ∧ PN.NormalsInput X N (rd ^ (12 * r * (r + 1) * f) * TT ^ (6 * f)) ∧
  PN.PointsInput X N ∧ PN.LocalInput X N C1 C0 k ∧ PN.GenMassInput X N AAre e1 ∧ PN.HeightInput X N (g ^ f)
def NGReal (f A : ℕ) (CB b cSt Ire : ℝ) : Prop :=
  PN.MeasureInput X N cSt ∧
  PN.PointSumInput X N (A * (r + 1) ^ 2) (Real.exp (CB * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) * Ire)
end NG
end Gen
end Formalism.L2.SG.RowsOther


