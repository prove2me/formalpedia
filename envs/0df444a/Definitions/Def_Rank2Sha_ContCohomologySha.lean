-- Prove2me | Definitions.Def_Rank2Sha_ContCohomologySha
-- name    : Rank2Sha_ContCohomologySha
-- status  : Definition
-- author  : @barindersbanwait
-- created : 2026-11-25T01:00:00.812147+00:00
-- url     : https://prove2.me/theorems/f98c6ec0-ed86-449d-8f7d-bd0ffefcabc8
-- title:
--   The Shafarevich–Tate group of a Galois module
-- statement:
--   Let $K$ be a field with absolute Galois group $G_K$, let $A$ be a topological abelian group with a continuous action of $G_K$, and let $(K_v)_{v \in V}$ be a family of field extensions of $K$ indexed by an arbitrary set $V$. Fix $n \ge 0$.
--
--   For each $v$ the inclusion $K \to K_v$ induces a restriction map on continuous cohomology
--
--   $$
--   \mathrm{res}_v : H^n(G_K, A) \longrightarrow H^n(G_{K_v}, A),
--   $$
--
--   where $G_{K_v}$ acts on $A$ through $G_{K_v} \to G_K$. The **Shafarevich–Tate group** of $A$ in degree $n$ with respect to the family is
--
--   $$
--   \text{Ш}^n\big((K_v)_v, A\big) = \bigcap_{v \in V} \ker(\mathrm{res}_v) \subseteq H^n(G_K, A).
--   $$
--
--   When $K$ is a global field, $V$ its set of places and $K_v$ the completions, this is the group of cohomology classes that are locally trivial everywhere.
--
--   **Formalization Note** The coefficient module is the same module $A$ at every $v$; it is not replaced by a module of points over $\overline{K_v}$. The code is copied without change from formal-conjectures, which copied it from Mathlib pull request 43529; the file is absent from the Mathlib revision of this environment.
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/6bc2f7490a49cc0258406ffb675483f4318a04b5/FormalConjecturesForMathlib/RepresentationTheory/Homological/ContCohomology/Sha.lean ; Mathlib pull request https://github.com/leanprover-community/mathlib4/pull/43529 ; J. Neukirch, A. Schmidt, K. Wingberg, Cohomology of Number Fields, 2nd ed., Definition 8.6.2 (as cited in the Mathlib file)

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
/-
The copied Mathlib source carries the following attribution:
Copyright (c) 2026 Edison Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, David Kurniadi Angdinata
-/

import Mathlib.FieldTheory.IsSepClosed
import Definitions.Def_Rank2Sha_AbsoluteGaloisGroup
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# The Tate–Shafarevich group of a Galois module

This file defines a general notion of a *Tate–Shafarevich group* of a Galois module (i.e. an abelian
group `A` equipped with a continuous action of the absolute Galois group `G_K` of a field `K`), as
the intersection of the kernels of the maps `Hⁿ(G_K, A) → Hⁿ(G_Kᵥ, A)`, induced by the map
`G_Kᵥ → G_K`, where `Kᵥ` is a field extension of `K` for each `v` in an arbitrary indexing set `V`.

These definitions were introduced in Mathlib by Edison Xie and David Kurniadi Angdinata's
[pull request #43529](https://github.com/leanprover-community/mathlib4/pull/43529).
They are absent from this repository's Mathlib `v4.33.1` dependency. The added code is copied
verbatim from `Mathlib.RepresentationTheory.Homological.ContCohomology.Sha` at commit
`a4c43ae1f99cb19aabfa62308b3ea75a340e470f`, except that `Mathlib.FieldTheory.AbsoluteGaloisGroup`
is replaced by this repository's copy, which supplies `Field.absoluteGaloisGroup.map`.

## Main definitions

* `ContinuousCohomology.tateShafarevich`: the Tate–Shafarevich group of a Galois module.

## TODOs

* Add a notation for `ContinuousCohomology.tateShafarevich`.
* Prove that `ContinuousCohomology.tateShafarevich` of a discrete Galois module is torsion.
* Define the classical Tate–Shafarevich group in `Mathlib/AlgebraicGeometry/EllipticCurve`.

## Implementation notes

Mathematicians seem to use "Tate–Shafarevich group" in at least three distinct contexts. They have
in common the set-up that `K` is a global field, `A` is a discrete `G_K`-module, `V` is the set of
places of `K`, and `Kᵥ` is the completion of `K` at a place `v` in `V`.

The first context is when `A` is finite. This is used, for example, in the statement of global
Poitou-Tate duality. In this theorem, the Tate–Shafarevich group is defined exactly as in this file.
It agrees with Definition 8.6.2 of [Neukirch–Schmidt–Wingberg].

The second context is when `A` is the `Kˢ`-valued points of a group scheme `J` such as an abelian
variety. Then the Tate–Shafarevich group is usually defined as the intersection of the kernels of
the maps `H¹(G_K, J(Kˢ)) → H¹(G_Kᵥ, J(Kᵥˢ))`. Note that in particular the module changes as well as
the group, so technically this is not quite what is happening in this definition. However the
inclusion `H¹(G_Kᵥ, J(Kᵥˢ)) → H¹(G_Kᵥ, J(Kˢ))` is an isomorphism by the Greenberg approximation
theorem, so the definition in this file is still mathematically correct.
See Remark I.3.10 of [Milne].

The third context is when `A` is the quotient of a `p`-adic `G_K`-module by a `G_K`-invariant
lattice, which is different from the definition in this PR. See Section 1 of [Flach].

## References

* [Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*](https://link.springer.com/book/10.1007/978-3-540-37889-1)
* [Milne, *Arithmetic Duality Theorems*](https://www.jmilne.org/math/Books/ADTnot.pdf)
* [Flach, *A finiteness theorem for the symmetric square of an elliptic curve*](https://link.springer.com/article/10.1007/BF01232029)
-/


universe u v

variable {K : Type u} {V : Type v} [Field K] (f : V → Type u) [∀ v, Field (f v)]
  [∀ v, Algebra K (f v)] (A : TopRep ℤ (Field.absoluteGaloisGroup K)) (n : ℕ)

open CategoryTheory

namespace ContinuousCohomology

/-- The Tate–Shafarevich group of a Galois module. -/
@[simps!]
noncomputable def tateShafarevich : AddSubgroup (continuousCohomology n A) :=
  ⨅ v, (map (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom.ker

lemma tateShafarevich_eq_iInf : tateShafarevich f A n =
    ⨅ v : V, (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom.ker := rfl

lemma tateShafarevich_eq_ker_pi : tateShafarevich f A n =
    (AddMonoidHom.pi fun v : V ↦ (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom).ker := by
  ext; simp [tateShafarevich_eq_iInf, funext_iff]

@[simp]
lemma mem_tateShafarevich (x : continuousCohomology n A) : x ∈ tateShafarevich f A n ↔
    ∀ v : V, (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom x = 0 := by
  simp [tateShafarevich_eq_iInf]

end ContinuousCohomology


