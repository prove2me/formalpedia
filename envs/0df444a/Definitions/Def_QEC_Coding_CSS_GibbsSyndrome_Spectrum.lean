-- Prove2me | Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
-- name    : QEC_Coding_CSS_GibbsSyndrome_Spectrum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:03:58.595445+00:00
-- url     : https://prove2.me/theorems/c7b35b2b-7a1c-415a-b44d-7e445c86bac2
-- title:
--   Spectrum
-- statement:
--   Definitions and structural lemmas for Spectrum, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Spectrum.lean

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
local instance _p2m_local_instance_ea4515a18e_14 : Fintype (LinearMap.range P) := Fintype.ofFinite _
local instance _p2m_local_instance_ea4515a18e_15 : Fintype (LinearMap.range Q) := Fintype.ofFinite _
def checkRank : Nat := Module.finrank (ZMod 2) (LinearMap.range P)
def multiplicity : Nat := 2 ^ (Fintype.card ι - checkRank P - checkRank Q)
def realizableEmbedding : Realizable P Q ↪ Word (ZMod 2) (Sum κP κQ) where
  toFun s := joinSyndrome s.1.val s.2.val
  inj' s t h := by
    apply Prod.ext
    · apply Subtype.ext; funext j; exact congrFun h (.inl j)
    · apply Subtype.ext; funext j; exact congrFun h (.inr j)
def realizableSyndromes : Finset (Word (ZMod 2) (Sum κP κQ)) :=
  Finset.univ.map (realizableEmbedding P Q)
def hamiltonian : Operator (Qubit.QubitRegister ι) :=
  -(∑ j : Sum κP κQ, toQubitOperator (binaryCSSParityCheckGenerators P Q j))
def energy (_P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (_Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (s : Word (ZMod 2) (Sum κP κQ)) : ℝ :=
  -(Fintype.card κP + Fintype.card κQ : Nat) + 2 * HammingWeight s
end QEC.Coding.CSSGibbs


