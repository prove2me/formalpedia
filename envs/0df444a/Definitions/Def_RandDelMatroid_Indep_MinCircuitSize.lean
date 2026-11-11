-- Prove2me | Definitions.Def_RandDelMatroid_Indep_MinCircuitSize
-- name    : RandDelMatroid_Indep_MinCircuitSize
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T18:28:28.774033+00:00
-- url     : https://prove2.me/theorems/1e53b589-3eba-4c96-ad9f-5c4c1d1d2e23
-- title:
--   Minimum circuit size $g(M)$ (Definition 1)
-- statement:
--   For a matroid $M$, a **circuit** is an inclusion-wise minimal dependent set, and the **minimum circuit size** is
--
--   $$g(M)=\min\{|C| : C \text{ is a circuit of } M\}.$$
--
--   The predicate "$g$ is the minimum circuit size of $M$" says that some circuit of $M$ has exactly $g$ elements and every circuit has at least $g$ elements.
--
--   The quantity $g$ sets the keep probability of the random deletion algorithm and the thresholds $g/2$ and $g$ throughout the proof.
--
--   **Formalization Note** The minimum exists only when $M$ has at least one circuit; the predicate `IsMinCircuitSize M g` requires one, instead of using `sInf` with its junk value on the empty set. Circuits are Mathlib's `Matroid.IsCircuit`.
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 8, Definition 1

import Mathlib

set_option autoImplicit false

namespace RandDelMatroid.Indep

/-- Definition 1 (p. 8). `g` is the minimum circuit size `g(M) = min {|C| : C a circuit of M}`:
some circuit of `M` has exactly `g` elements and every circuit has at least `g` elements.
The minimum exists only when `M` has a circuit, and this predicate requires one. -/
def IsMinCircuitSize {β : Type} (M : Matroid β) (g : ℕ) : Prop :=
  (∃ C : Set β, M.IsCircuit C ∧ C.ncard = g) ∧ ∀ C : Set β, M.IsCircuit C → g ≤ C.ncard

end RandDelMatroid.Indep


