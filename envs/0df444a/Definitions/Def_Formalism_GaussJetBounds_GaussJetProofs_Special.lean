-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
-- name    : Formalism_GaussJetBounds_GaussJetProofs_Special
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:12:45.797842+00:00
-- url     : https://prove2.me/theorems/19a7255e-5359-4aff-ab7a-c960c75be13d
-- title:
--   Special
-- statement:
--   Definitions and structural lemmas for Special, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
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
universe u v
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
section Pure
variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
def spLdeg (lt : ι → σ) (t : σ) (n : ι →₀ ℕ) : ℕ := ∑ k, if lt k = t then n k else 0
variable (lt : ι → σ) (N : σ → ι → R)
variable {lt N} (hN : ∀ s k, N s k ≠ 0 → lt k = s)
include hN
end Pure
section Minor
variable {R : Type*} [CommRing R] {m p : ℕ}
def spV (top : Fin (p + 1) → R) (o : Option (Fin m)) (c : Fin (p + 1)) :
    MvPolynomial (Fin m × Fin (p + 1)) R :=
  o.elim (MvPolynomial.C (top c)) (fun k => MvPolynomial.X (k, c))
def spEx (o : Option (Fin m)) (c : Fin (p + 1)) : Fin m × Fin (p + 1) →₀ ℕ :=
  o.elim 0 (fun k => Finsupp.single (k, c) 1)
def spCo (top : Fin (p + 1) → R) (o : Option (Fin m)) (c : Fin (p + 1)) : R :=
  o.elim (top c) (fun _ => 1)
end Minor
end Formalism.DworkPowerSeriesWeights


