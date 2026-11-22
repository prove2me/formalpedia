-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop
-- name    : Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:13:17.524786+00:00
-- url     : https://prove2.me/theorems/95b359d0-9a66-4a11-a72d-08f2c3c2ac3a
-- title:
--   Minor Product Support Top
-- statement:
--   Definitions and structural lemmas for Minor Product Support Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MinorProductSupportTop.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementH
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
universe u
namespace Formalism.DworkPowerSeriesWeights
open MvPolynomial
section ShapeSec
variable {σ : Type}
end ShapeSec
def shapeSet {R : Type u} [CommRing R] {J : Type} {N1 p : ℕ} (A : Fin p → J → R)
    (I : Fin p → Fin N1) : Set (J × Fin N1 →₀ ℕ) :=
  {mono | ∃ τ : Fin p → J, Function.Injective τ ∧
    (∃ π : Equiv.Perm (Fin p), ∀ i, A (π i) (τ i) ≠ 0) ∧ mono = ∑ i, Finsupp.single (τ i, I i) 1}
def shapeATop {R : Type u} [CommRing R] {N0 m : ℕ} (T : Fin N0 → Fin m → R) (i : Fin N0) :
    Option (Fin m) → R
  | none => if i.val = 0 then 1 else 0
  | some k => if i.val = 0 then 0 else T i k
end Formalism.DworkPowerSeriesWeights


