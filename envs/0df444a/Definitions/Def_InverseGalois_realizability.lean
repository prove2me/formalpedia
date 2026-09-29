-- Prove2me | Definitions.Def_InverseGalois_realizability
-- name    : InverseGalois_realizability
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T02:00:45.075983+00:00
-- url     : https://prove2.me/theorems/f0e6f063-dde1-4682-bca8-bb78b5931b1c
-- title:
--   Galois realizations and realizability of a group over a field
-- statement:
--   A **Galois realization** of a group $G$ over a field $K$ is the following package of data:
--
--   - a type $L$, together with a field structure on $L$ and a $K$-algebra structure on $L$;
--   - a proof that the extension $L/K$ is **Galois** (normal and separable, in Mathlib's sense `IsGalois K L`);
--   - a group isomorphism
--   $$ G \;\cong\; \mathrm{Gal}(L/K), $$
--   where $\mathrm{Gal}(L/K)$ is the group of $K$-algebra automorphisms of $L$.
--
--   Note that no finiteness or algebraicity condition is imposed on $L$ itself: the extension $L/K$ is only required to be Galois, and the isomorphism is with its full automorphism group.
--
--   A group $G$ is then said to be **realizable over $K$** when the type of Galois realizations of $G$ over $K$ is nonempty, i.e. when there exists at least one Galois extension $L/K$ with $\mathrm{Gal}(L/K) \cong G$. This is recorded as a single-field type class `IsRealizable K G`, so that the various statements of the mission read as "$G$ is realizable over $K$".
--
--   The structure and the class are taken verbatim from the Formal Conjectures entry for the inverse Galois problem.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026); Formal Conjectures, InverseGalois.lean, https://github.com/google-deepmind/formal-conjectures

import Mathlib

namespace InverseGalois

universe u v

/-- A realization of a group `G` as a Galois group over the field `K`: a type `L`
carrying a field structure and a `K`-algebra structure, such that `L / K` is a Galois
extension, together with a group isomorphism from `G` to `Gal(L/K) = L ≃ₐ[K] L`. -/
structure GaloisRealization (K : Type u) (G : Type v) [Field K] [Group G] where
  L : Type u
  to_field : Field L
  to_algebra : Algebra K L
  to_isGalois : IsGalois K L
  iso : G ≃* (L ≃ₐ[K] L)

/--
Say a group `G` is realizable over a field `K` if it
is isomorphic to the Galois group of a Galois extension
of `K`
-/
class IsRealizable (K : Type u) (G : Type v) [Field K] [Group G] where
  exists_realization : Nonempty (GaloisRealization K G)

end InverseGalois


