-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
-- name    : Formalism_FrobeniusOrbits_HostOrbitsPlaces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:11:36.543357+00:00
-- url     : https://prove2.me/theorems/486bf7c3-ffa9-4768-abe0-f4cc78e827b9
-- title:
--   Host Orbits Places
-- statement:
--   Definitions and structural lemmas for Host Orbits Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/HostOrbitsPlaces.lean

import Definitions.Def_Formalism_FrobeniusOrbits_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
def HostOrbits : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, (φ.1 = c0 ∨ φ.1 = ((1 : ℤˣ), (-1 : ℤˣ))) →
    (∀ τ ∈ Psi e, ∀ i : ℕ, φ ^ i * τ ∈ Psi e ↔ Even i) ∧
    (φ.1 = c0 → φ.2 ≠ 1 → Even (orderOf φ.2) ∧ orderOf φ = orderOf φ.2)
def placeOf {e : ℕ} (g : GG e) : GG e := if g.1.2 = 1 then g else cc e * g
def HostOrbitsPlaces : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, (φ.1 = c0 ∨ φ.1 = ((1 : ℤˣ), (-1 : ℤˣ))) → ∀ τ ∈ Psi e, ∀ i : ℕ,
    (placeOf (φ ^ i * τ)).2 = φ.2 ^ i * τ.2 ∧
    (φ.1 = c0 → (placeOf (φ ^ i * τ)).1 = τ.1) ∧
    (φ.1 = ((1 : ℤˣ), (-1 : ℤˣ)) →
      (placeOf (φ ^ i * τ)).1 = (if Even i then 1 else (sg e).1) * τ.1)
def HostOrbitCount : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, φ.1 = c0 → ∀ τ ∈ Psi e,
    (Set.range fun i : ℕ => placeOf (φ ^ i * τ)).ncard = orderOf φ.2
def HostFiniteOrder : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (k g : ℕ), g.Prime → ∀ M : Matrix (Fin k) (Fin k) (hostE ζ a b), M ^ g = 1 → M ≠ 1 →
    g - 1 ≤ 2 ^ (e + 2) * k
end Formalism.FrobeniusOrbits


