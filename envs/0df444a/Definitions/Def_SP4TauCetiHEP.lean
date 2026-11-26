-- Prove2me | Definitions.Def_SP4TauCetiHEP
-- name    : SP4TauCetiHEP
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-26T14:18:48.212732+00:00
-- url     : https://prove2.me/theorems/4b37f682-7724-58ae-b778-dc5d007cc5e0
-- title:
--   Homotopy extension property (TauCeti)
-- statement:
--   This is the homotopy extension property in the sense used by TauCeti: a subset $A\subseteq X$ has HEP if every homotopy defined on $A$, whose value at time $0$ extends to a map on $X$, extends to a homotopy on all of $X$. In a Hausdorff space such a subset is closed, and closed HEP subsets extend homotopies into targets in arbitrary universes. The definition records exactly the extension property needed for the skeleton-by-skeleton proofs of cellular approximation and the compression lemma.
-- source:
--   TauCetiProject/TauCeti, TauCeti.exists_homotopicRel_cellMap, TauCeti.exists_continuousMap_prod_skeletonLT_succ and TauCeti.hasHomotopyExtensionProperty_skeletonLT (https://github.com/TauCetiProject/TauCeti); A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1, proofs of Lemma 4.6 and Theorem 4.8.

import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic

set_option autoImplicit false

open scoped ContinuousMap unitInterval
open ContinuousMap Metric Set Topology Topology.RelCWComplex unitInterval

universe u

namespace SP4TauCeti

variable {X : Type u} [TopologicalSpace X]

/-- The homotopy extension property of a subset `A ⊆ X` (TauCeti,
`HasHomotopyExtensionProperty`): every homotopy out of `A` whose initial map extends to `X`
is itself the restriction of a homotopy out of `X`.

Only targets in the universe of `X` are quantified here.  For a closed subset this is no
restriction: `HasHomotopyExtensionProperty.exists_extension_of_isClosed` extends homotopies
with values in an arbitrary universe. -/
def HasHomotopyExtensionProperty (A : Set X) : Prop :=
  ∀ {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (H : C(I × A, Y)),
    (∀ a : A, H (0, a) = f a) →
      ∃ G : C(I × X, Y), (∀ x, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a)

/-- Unfolding of `HasHomotopyExtensionProperty`, so the property can be used in modules that
only import this definition. -/
theorem hasHomotopyExtensionProperty_iff (A : Set X) :
    HasHomotopyExtensionProperty A ↔
      ∀ {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (H : C(I × A, Y)),
        (∀ a : A, H (0, a) = f a) →
          ∃ G : C(I × X, Y), (∀ x, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) :=
  Iff.rfl

end SP4TauCeti


