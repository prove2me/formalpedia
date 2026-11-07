-- Prove2me | Definitions.Def_GeoQAC_ReflLayer
-- name    : GeoQAC_ReflLayer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:23.156195+00:00
-- url     : https://prove2.me/theorems/a95e68ad-cbf9-4bf1-8b37-2feee100aba5
-- title:
--   Product reflections and layers of product reflections
-- statement:
--   A **product reflection** on $G\subseteq V$ has the form $R=I-2\Pi$, where
--   $$
--   \Pi=|\phi\rangle\langle\phi|\otimes I_{G^c},\qquad |\phi\rangle=\bigotimes_{v\in G}|\phi_v\rangle
--   $$
--   is a product unit vector. Conjugating a generalized controlled-Z gate by one-qubit unitaries gives a product reflection with the same support, so every QAC circuit can be written as $C=V_dU_d\cdots U_1$, where each $U_j$ is a **layer of product reflections** with pairwise disjoint supports and $V_d$ is a tensor product of one-qubit unitaries.
--
--   A layer of product reflections is a finite set of pairwise disjoint nonempty supports $G_g$, each with a product unit vector; its unitary is $U=\prod_g R_g$.
--
--   **Formalization Note** Only the one-qubit factors $\phi_v$ with $v\in G$ enter $\Pi$. The reflections of a layer commute, so the product is taken in an arbitrary fixed order.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), §2.3, p.10; Lemma 3.9, p.16

import Mathlib
import Definitions.Def_DHRUniq_IsUnitVec

namespace GeoQAC

open DHRUniq (IsUnitVec)

/-!
# Product reflections and layers of product reflections

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), §2.3, p.10: "A product reflection on G has
the form R = I − 2Π, where Π = |ϕ⟩⟨ϕ| ⊗ I_{G^c} and |ϕ⟩ = ⊗_{v∈G} |ϕ_v⟩ is a product unit vector."
Conjugating a layer of generalized controlled-Z gates by one-qubit unitaries gives a layer of
product reflections with the same (pairwise disjoint) supports (p.10); Lemma 3.9 (p.16) is about
such a layer `U = ∏_g R_g`.

**Formalization Note.**
* `φ v : Bool → ℂ` is the one-qubit factor at `v`; only the factors at `v ∈ G` enter `Π`, and the
  theorems assume they are unit vectors.
* A `ReflLayer` carries one product vector per support. Reflections with disjoint supports commute,
  so `ReflLayer.matrix` multiplies them in the (arbitrary) order of `Finset.toList`; the product does
  not depend on it.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The projector `Π = |⊗_{v ∈ G} φ_v⟩⟨⊗_{v ∈ G} φ_v| ⊗ I_{Gᶜ}` (p.10). -/
noncomputable def reflProj (G : Finset V) (φ : V → Bool → ℂ) : Matrix (V → Bool) (V → Bool) ℂ :=
  Matrix.of fun x y =>
    if (∀ v, v ∉ G → x v = y v) then ∏ v ∈ G, (φ v (x v) * star (φ v (y v))) else 0

/-- The product reflection `R = I − 2Π` on `G` (p.10). -/
noncomputable def productReflection (G : Finset V) (φ : V → Bool → ℂ) :
    Matrix (V → Bool) (V → Bool) ℂ :=
  1 - 2 • reflProj G φ

/-- A layer of product reflections with pairwise disjoint nonempty supports (p.10, Lemma 3.9). -/
structure ReflLayer (V : Type) [Fintype V] [DecidableEq V] where
  /-- The supports `G_g` of the reflections. -/
  supp : Finset (Finset V)
  /-- Every support is nonempty. -/
  nonempty : ∀ S ∈ supp, S.Nonempty
  /-- The supports are pairwise disjoint. -/
  disjoint : (supp : Set (Finset V)).PairwiseDisjoint id
  /-- `vec S v` is the one-qubit factor at `v ∈ S` of the product vector of the reflection on `S`. -/
  vec : Finset V → V → Bool → ℂ
  /-- The one-qubit factors are unit vectors. -/
  vec_unit : ∀ S ∈ supp, ∀ v ∈ S, IsUnitVec (vec S v)

/-- The unitary `U = ∏_g R_g` of a layer of product reflections (the factors commute). -/
noncomputable def ReflLayer.matrix (L : ReflLayer V) : Matrix (V → Bool) (V → Bool) ℂ :=
  (L.supp.toList.map fun S => productReflection S (L.vec S)).prod

end GeoQAC


