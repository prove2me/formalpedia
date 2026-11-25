-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:09.094642+00:00
-- url     : https://prove2.me/theorems/08e1c79f-440f-4402-979a-5fc96459fcf5
-- title:
--   Prod Factorial Diag
-- statement:
--   Definitions and structural lemmas for Prod Factorial Diag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
namespace GlobalTheory.MinorGerm
section General
variable {C : Type} [Field C] {σ : Type}
def Low (α : σ →₀ ℕ) (g : MvPowerSeries σ C) : Prop :=
  MvPowerSeries.coeff α g = 1 ∧
    ∀ m : σ →₀ ℕ, m.degree ≤ α.degree → m ≠ α → MvPowerSeries.coeff m g = 0
def kill (p : σ → Prop) [DecidablePred p] : MvPolynomial σ C →ₐ[C] MvPolynomial σ C :=
  MvPolynomial.aeval fun x => if p x then MvPolynomial.X x else 0
def Lead (p : σ → Prop) [DecidablePred p] (α : σ →₀ ℕ) (P : MvPolynomial σ C) : Prop :=
  kill p P = MvPolynomial.monomial α 1 ∧ P.IsHomogeneous α.degree ∧ ∀ x ∈ α.support, p x
variable {p : σ → Prop} [DecidablePred p]
end General
section Diagonal
variable {C : Type} [Field C] {σ : Type} {N N' : ℕ}
def dgOne (j : Fin N × Fin N' → σ) (ρ n : ℕ) : σ →₀ ℕ :=
  if h : ρ < N ∧ ρ < N' then Finsupp.single (j (⟨ρ, h.1⟩, ⟨ρ, h.2⟩)) n else 0
def dg (j : Fin N × Fin N' → σ) (f : ℕ → ℕ) : σ →₀ ℕ := ∑ ρ ∈ Finset.range N, dgOne j ρ (f ρ)
variable {p : σ → Prop} [DecidablePred p]
end Diagonal
section Valuation
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
end Valuation
end GlobalTheory.MinorGerm


