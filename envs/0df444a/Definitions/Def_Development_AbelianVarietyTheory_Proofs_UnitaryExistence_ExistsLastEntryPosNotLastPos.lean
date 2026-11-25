-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:44:59.459523+00:00
-- url     : https://prove2.me/theorems/140bcb39-6cec-42ec-94bb-895ad213b0a2
-- title:
--   Exists Last Entry Pos Not Last Pos
-- statement:
--   Definitions and structural lemmas for Exists Last Entry Pos Not Last Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLastEntryPosNotLastPos.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaClaimsCompare
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
section Minors
variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (col : ∀ σ, Fin (r σ) → Fin n)
def minor (R : Type) [CommRing R] (σ : T) (s : Fin (r σ)) : MvPolynomial (Letter T r n) R :=
  (Matrix.of fun i j : Fin (s + 1) =>
    (X ⟨σ, Fin.castLE s.isLt i, col σ (Fin.castLE s.isLt j)⟩ : MvPolynomial (Letter T r n) R)).det
def minorsP (R : Type) [CommRing R] (a : T → ℕ → ℕ) : MvPolynomial (Letter T r n) R :=
  ∏ σ, ∏ s : Fin (r σ), minor r n col R σ s ^ (a σ s - a σ (s + 1))
end Minors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
def trunc (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : (E →+* ℂ) × ℕ → ℕ :=
  fun x => if x.2 < Dw.mult x.1 then a x else 0
variable (Xo : Moduli Dw l) (c : Coeff l)
def LastPosAt (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (τ : E →+* ℂ) : Prop :=
  0 < Dw.p ∧ 0 < a (τ, Dw.p - 1)
def RowsOnly (Cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ a a' n, (∀ τ (i : Fin (Dw.mult τ)), a (τ, i) = a' (τ, i)) → Cusp a n = Cusp a' n
def ShapeOK {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ σ, GoodEmb c σ → r = Dw.p + Dw.q ∧
    ∀ k, ((U σ).X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ ((U σ).X k).Ψ ↔ InPsi H τ
variable {Xo c}
def SomeGeneratorNeZeroEven (Xo : Moduli Dw l) (c : Coeff l) (nab : NabV Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (al : 𝓞 E) (q : ℕ), Even n → 0 < n → InJetRange Dw l a n al q →
    ∃ f ∈ thGen Xo c nab a n, f ≠ 0
end GlobalTheory.ThetaClaimsCompare


