-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T12:52:45.744931+00:00
-- url     : https://prove2.me/theorems/f946a962-bfc5-4928-9cde-ba78a2050161
-- title:
--   Gelfand Ps B
-- statement:
--   Definitions and structural lemmas for Gelfand Ps B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace GPs
def Wset (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :=
  {p | p.2.2 * p.1 * p.2.1 ∈ OmegaSet n}
def g0 (μ : Fin n → ℤ) :
    Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun p => PhiM μ (p.2.2 * p.1 * p.2.1)
def DH (X : Matrix (Fin n) (Fin n) ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun p => fderiv ℂ g p (X * p.1, 0)
def I0 (n : ℕ) := fderiv ℂ (fun y : Matrix (Fin n) (Fin n) ℂ =>
  ((y, 0) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) 0
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
local notation "𝕄f" => Fin n → Fin n → ℂ
def cK (T : KType ε Λ) : ℂ := (Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)
def Pk (T : KType ε Λ) (k : KG ε) : T.V →L[ℂ] T.V := T.op k * projW T * T.op k⁻¹
def emb (x : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) :
    Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ :=
  (x, toMK k, toMK k⁻¹)
def Fint (T : KType ε Λ)
    (g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) : T.V →L[ℂ] T.V :=
  cK T • ∫ k, g (emb x k) • Pk T k ∂(muK ε)
def FD (T : KType ε Λ)
    (g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) : 𝕄f →L[ℂ] (T.V →L[ℂ] T.V) :=
  fderiv ℂ (fun y : 𝕄f => g (emb y k) • Pk T k) x
section Int
variable {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
variable [CompactSpace (KG ε)]
end Int
section Ops
variable {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ} [CompactSpace (KG ε)]
end Ops
end GPs
end ReciprocityTheory.ChartRestriction.DS.S7


