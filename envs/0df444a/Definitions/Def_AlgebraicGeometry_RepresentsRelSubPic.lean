-- Prove2me | Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
-- name    : AlgebraicGeometry_RepresentsRelSubPic
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/8c264d24-f326-50fd-af34-5bb87d6d02c1
-- title:
--   Representability of sub-presheaves of the rigidified Picard functor
-- statement:
--   Fix a commutative ring $R$, a scheme $C$, a structure morphism $c \colon C \to \operatorname{Spec} R$ and a section $\varepsilon$ of $c$ (an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`). Recall that for $t \colon T \to \operatorname{Spec} R$ a `RigidifiedLineBundle c ε t` consists of a module $L$ on the fibre product $C \times_{\operatorname{Spec} R} T$ that is invertible (locally isomorphic to the unit module), together with the mere existence of an isomorphism between the pullback of $L$ along the section $\varepsilon \times T$ and the unit module on $T$.
--
--   `SubPicCondition c ε` is a structure packaging a family of predicates $P_t$ on such bundles, one for each $T$ and each $t$, together with three closure properties as fields: the unit bundle satisfies $P_t$; $P_t$ is invariant under the relation 'the underlying modules are isomorphic' (isomorphism of the modules $L$ only, with no compatibility with the rigidifications demanded); and $P$ is stable under `pullbackAlong`, i.e. under base change along any morphism $T' \to T$ over $\operatorname{Spec} R$. `SubPicCondition.top` is the identically true condition.
--
--   Given such a $P$ and a designation $D$ (a scheme $D.P$ over $\operatorname{Spec} R$ with a zero section), `RepresentsRelSubPic c ε P D` records: a rigidified bundle `poincare` on $C \times_{\operatorname{Spec} R} D.P$ satisfying $P$; the universal property that for every $t \colon T \to \operatorname{Spec} R$ and every rigidified $M$ with $P_t(M)$ there is a unique morphism $g \colon T \to D.P$ over $\operatorname{Spec} R$ whose pullback of `poincare` has underlying module isomorphic to that of $M$ (uniqueness of $g$ on the nose, while the classifying relation is only isomorphism of modules); and the normalisation that pulling `poincare` back along the zero section gives a module isomorphic to the unit. The helpers `classify`, `classify_spec` and `classify_unique` extract the classifying morphism and its characterisation from the universal property, and `ext_of_iso` deduces that two $T$-points of $D.P$ pulling `poincare` back to isomorphic modules coincide.
--
--   **Relation to Mathlib.** Mathlib has no relative Picard functor or representability predicate for it; these are the project's own notions, formulated using Mathlib's schemes, fibre products and sheaves of modules.
--
--   **Where it is used.** This fixes the shape of 'represents' used for relative Picard and Jacobian constructions in the project, to be instantiated with a particular condition $P$ (the degree-zero cut) when the Jacobian of a curve over a base is produced and its good reduction properties are used.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RepresentsRelSubPic.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

structure SubPicCondition (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : Type (u + 1) where

  P : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), RigidifiedLineBundle c ε t → Prop
  unit_mem : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), P t (RigidifiedLineBundle.unit t)
  congr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t),
    Nonempty (M.L ≅ M'.L) → P t M → P t M'
  pullback_mem : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t), P t M → P t' (M.pullbackAlong ψ)

def SubPicCondition.top (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    SubPicCondition c ε where
  P := fun _ _ => True
  unit_mem := fun _ => trivial
  congr := fun _ _ _ _ _ => trivial
  pullback_mem := fun _ _ _ _ _ => trivial

structure RepresentsRelSubPic (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (P : SubPicCondition c ε) (D : RelativePic0Designation R c) : Type (u + 1) where

  poincare : RigidifiedLineBundle c ε D.toBase
  poincare_mem : P.P D.toBase poincare

  univ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t), P.P t M →
    ∃! g : SchemeHomOver t D.toBase, Nonempty ((poincare.pullbackAlong g).L ≅ M.L)

  zero : Nonempty ((poincare.pullbackAlong ⟨D.zeroSection, D.zeroSection_toBase⟩).L ≅
    (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 _)).L)

namespace RepresentsRelSubPic

variable {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {P : SubPicCondition c ε} {D : RelativePic0Designation R c}

noncomputable def classify (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : P.P t M) : SchemeHomOver t D.toBase :=
  (h.univ t M hM).choose

theorem classify_spec (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : P.P t M) :
    Nonempty ((h.poincare.pullbackAlong (h.classify t M hM)).L ≅ M.L) :=
  (h.univ t M hM).choose_spec.1

theorem classify_unique (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : P.P t M) (g : SchemeHomOver t D.toBase)
    (hg : Nonempty ((h.poincare.pullbackAlong g).L ≅ M.L)) : g = h.classify t M hM :=
  (h.univ t M hM).unique hg (h.classify_spec t M hM)

theorem ext_of_iso (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (g g' : SchemeHomOver t D.toBase)
    (hgg' : Nonempty ((h.poincare.pullbackAlong g).L ≅ (h.poincare.pullbackAlong g').L)) : g = g' := by
  have hmem : P.P t (h.poincare.pullbackAlong g') := P.pullback_mem _ _ g' _ h.poincare_mem
  have h1 := h.classify_unique t _ hmem g hgg'
  have h2 := h.classify_unique t _ hmem g' ⟨Iso.refl _⟩
  exact h1.trans h2.symm

end RepresentsRelSubPic

end AlgebraicGeometry.RelPicard


