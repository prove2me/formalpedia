-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Equivalences
-- name    : OAI_RepresentationTheory_PartialPermutation_Equivalences
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:18:54.689811+00:00
-- url     : https://prove2.me/theorems/93db188b-1e78-4151-94e7-920ee4a3c85d
-- title:
--   Transporting irreducible representations along group isomorphisms
-- statement:
--   Let $G$ and $K$ be groups and let $V$ be a complex vector space.
--
--   1. **Subrepresentations of a pulled-back representation.** For a representation $\rho$ of $G$ on $V$ and a group isomorphism $e\colon K\to G$, the representation $\rho\circ e$ of $K$ has the same invariant subspaces as $\rho$; this gives an order isomorphism between the lattices of subrepresentations of $\rho\circ e$ and of $\rho$.
--   2. **Irreducibility is preserved.** If $\rho$ is irreducible, then so is $\rho\circ e$.
--
--   Now let $G$ and $K$ be finite. For a finite group $\Gamma$, let $\operatorname{Irr}(\Gamma)$ be the set of isotypic components of the left regular representation of $\Gamma$ on $\ell^2(\Gamma)$, regarded as a $\mathbb{C}[\Gamma]$-module, and for $c\in\operatorname{Irr}(\Gamma)$ let $\pi^{\Gamma}_c$ be the irreducible representation of $\Gamma$ on the simple submodule chosen to represent the type of $c$; every irreducible finite-dimensional complex representation of $\Gamma$ is equivalent to exactly one $\pi^{\Gamma}_c$.
--
--   3. **Index map.** For a group isomorphism $e\colon G\to K$ and $c\in\operatorname{Irr}(G)$, the index $\varphi_e(c)\in\operatorname{Irr}(K)$ is the unique index with $\pi^{K}_{\varphi_e(c)}\cong\pi^{G}_{c}\circ e^{-1}$, and this equivalence is recorded.
--   4. **Inverse.** $\varphi_{e^{-1}}(\varphi_e(c))=c$ for every $c\in\operatorname{Irr}(G)$.
--   5. **Bijection.** $\varphi_e$ is a bijection $\operatorname{Irr}(G)\to\operatorname{Irr}(K)$ with inverse $\varphi_{e^{-1}}$.
--
--   In short,
--
--   $$
--   \varphi_e\colon\operatorname{Irr}(G)\xrightarrow{\ \sim\ }\operatorname{Irr}(K),\qquad \pi^{K}_{\varphi_e(c)}\;\cong\;\pi^{G}_{c}\circ e^{-1}.
--   $$
--
--   Since equivalent representations have the same dimension, $\varphi_e$ preserves degrees, so sums over irreducible representations that depend only on the degrees (such as $\sum_c d_c^{-u}$) agree for isomorphic groups. This is used to identify subgroups of permutation groups with standard symmetric groups.
--
--   **Formalization Note** The items are `subrepresentationCompEquiv`, the instance `irreducible_comp_mulEquiv`, `irreducibleIndexMap e c` (chosen from the unique-existence statement `irreducibleRep_complete`) with `irreducibleIndexMap_spec`, `irreducibleIndexMap_inverse` and `irreducibleIndexEquiv e`. Here $\operatorname{Irr}(\Gamma)$ is `IrreducibleIndex` and $\pi^{\Gamma}_c$ is `irreducibleRep c`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/Equivalences.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Equivalences.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PartialPermutation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation
noncomputable section
variable {G K V W : Type*} [Group G] [Group K]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def subrepresentationCompEquiv (ρ : Representation ℂ G V) (e : K ≃* G) :
    Subrepresentation (ρ.comp e.toMonoidHom) ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        simpa using S.apply_mem_toSubmodule (e.symm g) hv }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g v hv => S.apply_mem_toSubmodule (e g) hv }
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := Iff.rfl

instance irreducible_comp_mulEquiv (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] (e : K ≃* G) :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom) :=
  (subrepresentationCompEquiv ρ e).isSimpleOrder_iff.mpr inferInstance

variable [Fintype G] [Fintype K]

def irreducibleIndexMap (e : G ≃* K) (c : IrreducibleIndex G) : IrreducibleIndex K :=
  (irreducibleRep_complete ((irreducibleRep c).comp e.symm.toMonoidHom)).choose

lemma irreducibleIndexMap_spec (e : G ≃* K) (c : IrreducibleIndex G) :
    Nonempty (Representation.Equiv (irreducibleRep (irreducibleIndexMap e c))
      ((irreducibleRep c).comp e.symm.toMonoidHom)) :=
  (irreducibleRep_complete ((irreducibleRep c).comp e.symm.toMonoidHom)).choose_spec.1

lemma irreducibleIndexMap_inverse (e : G ≃* K) (c : IrreducibleIndex G) :
    irreducibleIndexMap e.symm (irreducibleIndexMap e c) = c := by
  obtain ⟨a⟩ := irreducibleIndexMap_spec e c
  obtain ⟨b⟩ := irreducibleIndexMap_spec e.symm (irreducibleIndexMap e c)
  have h : Nonempty (Representation.Equiv
      (irreducibleRep (irreducibleIndexMap e.symm (irreducibleIndexMap e c)))
      (irreducibleRep c)) := by
    refine ⟨Representation.Equiv.mk (b.toLinearEquiv.trans a.toLinearEquiv) ?_⟩
    intro g
    apply LinearMap.ext
    intro x
    change a (b (irreducibleRep _ g x)) = irreducibleRep c g (a (b x))
    calc
      _ = a (irreducibleRep (irreducibleIndexMap e c) (e g) (b x)) :=
        congrArg a (congrArg (fun L : _ →ₗ[ℂ] _ => L x) (b.isIntertwining' g))
      _ = _ := by
        have ha := congrArg (fun L : _ →ₗ[ℂ] _ => L (b x)) (a.isIntertwining' (e g))
        change a (irreducibleRep (irreducibleIndexMap e c) (e g) (b x)) =
          irreducibleRep c (e.symm (e g)) (a (b x)) at ha
        simpa only [MulEquiv.symm_apply_apply] using ha
  exact (componentRep_equiv_iff (regularRep G) _ _).mp h

def irreducibleIndexEquiv (e : G ≃* K) : IrreducibleIndex G ≃ IrreducibleIndex K where
  toFun := irreducibleIndexMap e
  invFun := irreducibleIndexMap e.symm
  left_inv := irreducibleIndexMap_inverse e
  right_inv := irreducibleIndexMap_inverse e.symm

end
end PartialPermutation

end

end OAI


