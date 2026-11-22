-- Prove2me | Definitions.Def_Formalism_RankGapBounds_ConjInOrbit
-- name    : Formalism_RankGapBounds_ConjInOrbit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:59.954376+00:00
-- url     : https://prove2.me/theorems/539644d6-7fbf-44f4-962a-038e2949c4bc
-- title:
--   Conj In Orbit
-- statement:
--   Definitions and structural lemmas for Conj In Orbit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/ConjInOrbit.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.RankGapBounds.ExistsSmulMemTer
abbrev G0 := ZMod 2 × ZMod 2
abbrev GG (e : ℕ) := G0 × ZMod (2 ^ e)
def sg : G0 := (1, 0)
def c0 : G0 := (0, 1)
def cc (e : ℕ) : GG e := (c0, 0)
def InPhi {e : ℕ} (γ : GG e) : Prop := γ.1.2 = 0
def place {e : ℕ} (γ : GG e) : GG e := if γ.1.2 = 0 then γ else γ + cc e
def OrbitParity : Prop :=
  ∀ (e : ℕ) (φ τ : GG e) (i : ℕ), φ.1.2 = 1 → InPhi τ → (InPhi (i • φ + τ) ↔ Even i)
def OrbitCoord : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)) (i : ℕ), (place (i • φ + ((0 : G0), t))).2 = t + i • φ.2
def OrbitOver : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)) (i : ℕ),
    (φ.1 = c0 → (place (i • φ + ((0 : G0), t))).1 = 0) ∧
    (φ.1 = sg + c0 → (place (i • φ + ((0 : G0), t))).1 = if Even i then 0 else sg)
def ConjInOrbit : Prop :=
  ∀ (e : ℕ) (φ : GG e), φ.1.2 = 1 → (cc e ∈ AddSubgroup.zmultiples φ ↔ φ = cc e)
def OrbitCard : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)), φ.1 = c0 → φ.2 ≠ 0 →
    (Set.range fun i : ℕ => place (i • φ + ((0 : G0), t))).ncard = addOrderOf φ.2 ∧
    Even (addOrderOf φ.2)
end Formalism.RankGapBounds.ExistsSmulMemTer


