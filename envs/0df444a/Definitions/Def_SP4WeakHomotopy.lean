-- Prove2me | Definitions.Def_SP4WeakHomotopy
-- name    : SP4WeakHomotopy
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-09T01:53:19.230915+00:00
-- url     : https://prove2.me/theorems/671d0099-a894-4a3d-8d1f-6d93446626c3
-- title:
--   Weak contractibility (all homotopy groups trivial)
-- statement:
--   A topological space $X$ is **weakly contractible** if it is nonempty and the map from $X$ to a one-point space is a weak homotopy equivalence, that is, for every $n\ge0$ and every base point $x\in X$ the homotopy group
--
--   $$
--   \pi_n(X,x)
--   $$
--
--   is trivial. In degree $0$ this says that $X$ is path connected, in degree $1$ that it is simply connected. Every contractible space is weakly contractible; the converse holds for spaces having the homotopy type of a CW complex, by Whitehead's theorem, but fails in general: Hatcher's "quasi-circle" is a noncontractible space all of whose homotopy groups are trivial, and the long line is a weakly contractible manifold that is not contractible.
--
--   **Formalization Note** `SP4WeakHomotopy.WeaklyContractible X` is `Nonempty X ∧ ∀ n x, Subsingleton (HomotopyGroup.Pi n X x)`, using Mathlib's homotopy groups `π_ n X x` (classes of maps from the $n$-cube sending its boundary to $x$, up to homotopy relative to the boundary). Mathlib identifies `π_ 0 X x` with the set of path components and `π_ 1 X x` with the fundamental group, so the definition agrees with the classical one in all degrees.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §4.1, p. 352: "A map f : X → Y is called a weak homotopy equivalence if it induces isomorphisms πₙ(X, x₀) → πₙ(Y, f(x₀)) for all n ≥ 0 and all choices of basepoint x₀"; weak contractibility is the case of the map to a point. Theorem 4.5 (Whitehead), p. 346, and the remark following the definition on p. 352.

import Mathlib.Topology.Homotopy.HomotopyGroup

set_option autoImplicit false

namespace SP4WeakHomotopy

/-- **Weak contractibility** (Hatcher, *Algebraic Topology*, §4.1, p. 352): a space `X` is weakly
contractible if it is nonempty and the map to a point is a weak homotopy equivalence, that is,
every homotopy group `π_n(X, x)` is trivial for every `n ≥ 0` and every base point `x ∈ X`.
In degree `0` this says that `X` is path connected; in degree `1` that `X` is simply connected. -/
def WeaklyContractible (X : Type*) [TopologicalSpace X] : Prop :=
  Nonempty X ∧ ∀ (n : ℕ) (x : X), Subsingleton (HomotopyGroup.Pi n X x)

end SP4WeakHomotopy


