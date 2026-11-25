-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieJet
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:05.524381+00:00
-- url     : https://prove2.me/theorems/0eec6d55-22e3-4aca-b98e-250a472b161c
-- title:
--   Row Tie Jet
-- statement:
--   Definitions and structural lemmas for Row Tie Jet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
section Disjoint
variable {K : Type} [Field K] {σ : Type}
def rtjSerIn (A : Set σ) (F : MvPowerSeries σ K) : Prop :=
  ∀ μ : σ →₀ ℕ, MvPowerSeries.coeff μ F ≠ 0 → (↑μ.support : Set σ) ⊆ A
end Disjoint
section Rename
variable {K : Type} [Field K] {σ τ : Type}
end Rename
section Rows
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}
def rtjR (ρ : Fin N) : WV I ↪ Fin N × WV I := ⟨fun w => (ρ, w), Prod.mk_right_injective ρ⟩
def rtjE {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl) (i : Fin K) :
    Fin (what₂ i) × WV I ↪ Fin N × WV I :=
  ⟨fun x => (pl ⟨i, x.1⟩, x.2), fun x y h => by
    have h' : (pl ⟨i, x.1⟩, x.2) = (pl ⟨i, y.1⟩, y.2) := h
    have h1 : pl ⟨i, x.1⟩ = pl ⟨i, y.1⟩ := (Prod.ext_iff.1 h').1
    have h2 : x.2 = y.2 := (Prod.ext_iff.1 h').2
    have h3 := hpl h1
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h3
    exact Prod.ext h3 h2⟩
def rtjH (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) (k : Knd d) : MvPowerSeries (WV I) C :=
  match k with
  | some (g, a, a') => hL g a a'
  | none => 0
end Rows
end Formalism.L2.FormalSeriesBounds


