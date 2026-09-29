-- Prove2me | Definitions.Def_GroupCohomology_TateDimensionShift
-- name    : GroupCohomology_TateDimensionShift
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/46ac490d-6f65-5f28-a35d-107d6b1bff87
-- title:
--   Dimension-shifting short complexes via induction from the trivial subgroup
-- statement:
--   Fix a commutative ring $k$, a group $G$ and a representation $A \in \mathrm{Rep}_k(G)$. The module names the representation $A_* :=$ [`Rep.indBot A`](../def/GroupCohomology_TateDimensionShift.html#L18), obtained by restricting $A$ along the inclusion $\bot \hookrightarrow G$ of the trivial subgroup and inducing back along the same inclusion; since Mathlib realises induction as coinvariants of $k[G] \otimes_k V$ for the subgroup action, and the subgroup here is trivial, $A_*$ is $k[G] \otimes_k A$ with $G$ acting through the left regular action on $k[G]$. Together with it come the $k$-linear maps $a \mapsto [g \otimes a]$ ([`Rep.indBotMk`](../def/GroupCohomology_TateDimensionShift.html#L21), with [`Rep.indBotMk_apply`](../def/GroupCohomology_TateDimensionShift.html#L24) recording the defining formula), the special case $\sigma =$ [`Rep.indBotσ`](../def/GroupCohomology_TateDimensionShift.html#L30) at $g = 1$, and the $k$-linear map $r =$ [`Rep.indBotr`](../def/GroupCohomology_TateDimensionShift.html#L32), induced on coinvariants by $f \otimes a \mapsto f(1)\,a$ on $k[G] \otimes_k A$. The morphism $\pi =$ [`Rep.indBotπ`](../def/GroupCohomology_TateDimensionShift.html#L27)$: A_* \to A$ is defined as the image of the identity of $\mathrm{Res}\,A$ under the inverse of the adjunction bijection `Rep.indResHomEquiv`, i.e. the counit of $\mathrm{Ind} \dashv \mathrm{Res}$ at $A$; dually, for $G$ finite, $\iota =$ [`Rep.indBotι`](../def/GroupCohomology_TateDimensionShift.html#L54)$: A \to A_*$ is the unit of `Rep.resIndAdjunction` at $A$. Neither map is given by an explicit formula here.
--
--   From these, two objects of $\mathrm{Rep}_k(G)$ are formed: [`Rep.dimShiftDownObj A`](../def/GroupCohomology_TateDimensionShift.html#L37), the subrepresentation of $A_*$ carried by $\ker \pi$, and (for $G$ finite) [`Rep.dimShiftUpObj A`](../def/GroupCohomology_TateDimensionShift.html#L57), the quotient of $A_*$ by the image of $\iota$; in each case the required stability of the submodule under the action is part of the definition. Finally [`Rep.dimShiftDown A`](../def/GroupCohomology_TateDimensionShift.html#L42) and [`Rep.dimShiftUp A`](../def/GroupCohomology_TateDimensionShift.html#L62) package these into short complexes $\ker\pi \to A_* \xrightarrow{\pi} A$ and $A \xrightarrow{\iota} A_* \to A_*/\iota(A)$, with the inclusion and the quotient map as the remaining morphisms and the vanishing of the composite as the short-complex datum. Exactness is not asserted at this stage.
--
--   **Relation to Mathlib.** Built on Mathlib's `Rep.ind`, `Rep.res`, the hom-equivalence `Rep.indResHomEquiv` and the adjunction `Rep.resIndAdjunction`, and on Mathlib's realisation of induced representations as coinvariants of $k[G] \otimes_k V$; the named splittings, the kernel/cokernel representations and the two short complexes are the project's own packaging.
--
--   **Where it is used.** The two short complexes are the input to dimension shifting for the Tate cohomology of a finite group defined in the imported module: once their exactness and the vanishing of the Tate cohomology of $A_*$ in all degrees are available, they yield isomorphisms $\hat H^q(G, A_*/\iota A) \cong \hat H^{q+1}(G, A)$ and $\hat H^q(G, A) \cong \hat H^{q+1}(G, \ker\pi)$, reducing statements about Tate cohomology in arbitrary degrees to low degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_TateDimensionShift.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

section DimShift

variable {k G : Type u} [CommRing k] [Group G]

abbrev indBot (A : Rep.{u} k G) : Rep.{u} k G :=
  Rep.ind (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A)

def indBotMk (A : Rep.{u} k G) (g : G) : A →ₗ[k] A.indBot :=
  Representation.IndV.mk (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A).ρ g

lemma indBotMk_apply (A : Rep.{u} k G) (g : G) (a : A) :
    A.indBotMk g a = Representation.IndV.mk (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A).ρ g a := rfl

def indBotπ (A : Rep.{u} k G) : A.indBot ⟶ A :=
  (Rep.indResHomEquiv (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A) A).symm (𝟙 _)

def indBotσ (A : Rep.{u} k G) : A →ₗ[k] A.indBot := A.indBotMk 1

def indBotr (A : Rep.{u} k G) : A.indBot →ₗ[k] A :=
  Representation.Coinvariants.lift _ (TensorProduct.lift ((LinearMap.lsmul k A).comp
      ((Finsupp.lapply 1).comp (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)))
    (fun s => by rw [Subsingleton.elim s 1, map_one]; rfl)

abbrev dimShiftDownObj (A : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (Representation.subrepresentation A.indBot.ρ (LinearMap.ker (indBotπ A).hom.toLinearMap) fun g x hx => by
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply] at hx ⊢
    rw [Rep.hom_comm_apply, hx, map_zero])

def dimShiftDown (A : Rep.{u} k G) : ShortComplex (Rep.{u} k G) where
  X₁ := A.dimShiftDownObj
  X₂ := A.indBot
  X₃ := A
  f := Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩
  g := indBotπ A
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => x.2))

variable [Fintype G]

open scoped Classical in

def indBotι (A : Rep.{u} k G) : A ⟶ A.indBot :=
  (Rep.resIndAdjunction k (⊥ : Subgroup G)).unit.app A

abbrev dimShiftUpObj (A : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (Representation.quotient A.indBot.ρ (LinearMap.range (indBotι A).hom.toLinearMap) fun g => by
    rintro _ ⟨a, rfl⟩
    exact ⟨A.ρ g a, Rep.hom_comm_apply (indBotι A) g a⟩)

def dimShiftUp (A : Rep.{u} k G) : ShortComplex (Rep.{u} k G) where
  X₁ := A
  X₂ := A.indBot
  X₃ := A.dimShiftUpObj
  f := indBotι A
  g := Rep.ofHom ⟨Submodule.mkQ _, fun _ => rfl⟩
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun a =>
    (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩))

end DimShift

end Rep

end


