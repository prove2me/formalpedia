-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
-- name    : LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:54:16.135698+00:00
-- url     : https://prove2.me/theorems/5d0a85c0-f792-4383-8f11-9e64cdb08f22
-- title:
--   Ray Compatibility
-- statement:
--   Definitions and structural lemmas for Ray Compatibility, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
section RepeatFactorRay
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}
end RepeatFactorRay
section Compatibility
variable [DecidableEq α]
def PrefixOverlap (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Prop :=
  Ju < Ωu.onset ∧ Ωv.suffixBeforeOnset Jv <:+ Ωu.prefixBeforeOnset ∧
      (Ωu.suffixBeforeOnset Ju).length ≤ (Ωv.suffixBeforeOnset Jv).length
def PeriodicTailOverlap (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Prop :=
  Ωu.onset ≤ Ju ∧ Ωv.suffixBeforeOnset Jv <:+ Ωu.prefixBeforeOnset ∧ ∀ t, Ωv.stream (Ωv.onset + t) =
      Ωu.stream (Ωu.onset + t)
def ReversePrefixOverlap (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Prop :=
  Ωu.suffixBeforeOnset Ju ≠ [] ∧ Ωu.suffixBeforeOnset Ju <:+ Ωv.prefixBeforeOnset ∧
      (Ωv.suffixBeforeOnset Jv).length ≤ (Ωu.suffixBeforeOnset Ju).length
def NoForbiddenRayOverlap (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Prop :=
  ¬ PrefixOverlap Ωv Ωu Jv Ju ∧ ¬ PeriodicTailOverlap Ωv Ωu Jv Ju ∧
      ¬ ReversePrefixOverlap Ωv Ωu Jv Ju
instance (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Decidable (PrefixOverlap Ωv Ωu Jv Ju) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Decidable (PeriodicTailOverlap Ωv Ωu Jv Ju) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ t, Ωv.stream (Ωv.onset + t) = Ωu.stream (Ωu.onset + t)))
instance (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Decidable (ReversePrefixOverlap Ωv Ωu Jv Ju) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (Ωv Ωu : Ray α) (Jv Ju : ℕ) : Decidable (NoForbiddenRayOverlap Ωv Ωu Jv Ju) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
variable {ι : Type} [Fintype S]
section NoCycle
variable [Fintype ι] [DecidableEq ι] (M : StructuralReader α S k) (st : ι → S) (Ω : ι → Ray α)
  (J : ι → ℕ) (v : ι)
def CandidateInvariant (x : ι) : Prop :=
  J x < (Ω x).onset ∧ (Ω v).suffixBeforeOnset (J v) <:+ (Ω x).suffixBeforeOnset (J x) ∧
    (∀ t, (Ω x).stream ((Ω x).onset + t) = (Ω v).stream ((Ω v).onset + t)) ∧
    (x = v ∨ ((Ω v).suffixBeforeOnset (J v)).length < ((Ω x).suffixBeforeOnset (J x)).length)
variable {M st Ω J v}
end NoCycle
end Compatibility
section Count
variable [DecidableEq α] [Fintype S]
    [DecidableEq S] {M : StructuralReader α S k} {W : Fin k → List α}
  {u v : Fin k} {Ωu : Ray α} {κ : Type} (R : Finset κ) (Ωc : κ → Ray α) (Ec : κ → ℕ)
end Count
end DeciSigma1.Holes.Tail


