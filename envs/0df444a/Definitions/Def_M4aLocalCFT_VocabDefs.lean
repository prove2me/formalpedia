-- Prove2me | Definitions.Def_M4aLocalCFT_VocabDefs
-- name    : M4aLocalCFT_VocabDefs
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/dba4dc91-daea-5de6-a9de-3ef7c2c49553
-- title:
--   Norm and σ−1 maps on unit groups under a decomposition subgroup
-- statement:
--   Throughout, $L/K$ is an extension of fields, $A$ is a valuation subring of $L$ which is a discrete valuation ring, complete with respect to the adic topology of its maximal ideal, with finite residue field, and whose decomposition subgroup $G = A.\text{decompositionSubgroup}\,K$ (the subgroup of $K$-algebra automorphisms of $L$ preserving $A$) is finite and cyclic. Under these standing assumptions the module introduces two parallel triples of monoid endomorphisms, one on $A^\times$ and one on $L^\times$.
--
--   For $s \in G$, `unitsAct` is the endomorphism of $A^\times$ obtained by applying the ring automorphism of $A$ attached to $s$ by the semiring action of $G$ on $A$, i.e. $u \mapsto s(u)$ on units. `unitsNorm` is the product, in the abelian group of monoid homomorphisms $A^\times \to A^\times$, of `unitsAct A s` over all $s \in G$; thus it sends $u$ to $\prod_{s \in G} s(u)$, the product being indexed by the elements of the group $G$ (so of length $|G|$) rather than by a degree of a field extension. For $g \in G$, `unitsDerive` is the quotient of `unitsAct A g` by the identity homomorphism, i.e. $u \mapsto g(u)\,u^{-1}$, the $(g-1)$-operator written multiplicatively.
--
--   The declarations `fieldUnitsAct`, `fieldUnitsNorm` and `fieldUnitsDerive` are the same three constructions on $L^\times$, with $s \in G$ acting through its underlying $K$-algebra automorphism $L \simeq_K L$: the action $u \mapsto s(u)$, the product $\prod_{s \in G} s(\cdot)$, and $u \mapsto g(u)\,u^{-1}$. All six are monoid homomorphisms; no Galois-theoretic hypothesis beyond the finiteness and cyclicity of $G$ is imposed, and no cohomology group is formed here.
--
--   **Relation to Mathlib.** Mathlib supplies `ValuationSubring.decompositionSubgroup` together with its semiring action on the valuation subring, which is what the action maps here use; the norm and $(g-1)$ endomorphisms of the unit groups, formed as products and quotients in the group of monoid homomorphisms, are the project's own and are distinct from Mathlib's `Algebra.norm` of a field extension.
--
--   **Where it is used.** These maps are the basic vocabulary for the Tate-cohomology computations of local class field theory used in the local analysis of Galois representations: the cyclic group $G$ acts on $A^\times$ and $L^\times$, and the norm and $(g-1)$ maps are the maps whose kernels and images enter Herbrand-quotient and Hilbert-90 style arguments in the modules that import this one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_M4aLocalCFT_VocabDefs.lean

import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.Card

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing ValuationSubring

namespace M4aLocalCFT

section Carrier

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
variable [Finite (IsLocalRing.ResidueField A)]
variable [Finite (A.decompositionSubgroup K)] [IsCyclic (A.decompositionSubgroup K)]

noncomputable def unitsAct (s : A.decompositionSubgroup K) : Aˣ →* Aˣ :=
  Units.map (MulSemiringAction.toRingAut (A.decompositionSubgroup K) A s).toRingHom.toMonoidHom

noncomputable def unitsNorm : Aˣ →* Aˣ :=
  letI := Fintype.ofFinite (A.decompositionSubgroup K)
  ∏ s : A.decompositionSubgroup K, unitsAct A s

noncomputable def unitsDerive (g : A.decompositionSubgroup K) : Aˣ →* Aˣ :=
  (unitsAct A g) / (MonoidHom.id Aˣ)

end Carrier

section FieldUnits

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
variable [Finite (IsLocalRing.ResidueField A)]
variable [Finite (A.decompositionSubgroup K)] [IsCyclic (A.decompositionSubgroup K)]

noncomputable def fieldUnitsAct (s : A.decompositionSubgroup K) : Lˣ →* Lˣ :=
  Units.map (s : L ≃ₐ[K] L).toAlgHom.toRingHom.toMonoidHom

noncomputable def fieldUnitsNorm : Lˣ →* Lˣ :=
  letI := Fintype.ofFinite (A.decompositionSubgroup K)
  ∏ s : A.decompositionSubgroup K, fieldUnitsAct A s

noncomputable def fieldUnitsDerive (g : A.decompositionSubgroup K) : Lˣ →* Lˣ :=
  (fieldUnitsAct A g) / (MonoidHom.id Lˣ)

end FieldUnits

end M4aLocalCFT


