-- Prove2me | Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
-- name    : AlgebraicGeometry_RelEffCartierDivOfPoint
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/1e781454-bd68-55a6-9507-84306faa6fca
-- title:
--   Graphs of points and degree-one relative divisors
-- statement:
--   Fix schemes and a morphism $f \colon \mathcal{C} \to S$, together with $g \colon T \to S$. For a morphism $a \colon T \to \mathcal{C}$ with $a$ followed by $f$ equal to $g$, `graphOver` is the graph $\Gamma_a \colon T \to \mathcal{C} \times_S T$, characterised by having first projection $a$ and second projection $\mathrm{id}_T$; the two companion lemmas record exactly these two identities, and a third records that it is the morphism induced by the pair $(a, \mathrm{id}_T)$. When $f$ is separated, $\Gamma_a$ is a closed immersion (it is a section of the separated projection $\mathcal{C} \times_S T \to T$), and the closed subscheme of $\mathcal{C} \times_S T$ cut out by the kernel ideal sheaf $\ker \Gamma_a$ has structural morphism to $T$ — its inclusion followed by the second projection — an isomorphism.
--
--   On this basis, `RelEffCartierDiv.ofPoint` attaches to such a point $a$ a relative effective divisor of degree $1$ for $f$ over $g$: an object of the project's structure `RelEffCartierDiv f 1 g`, consisting of an ideal sheaf on $\mathcal{C} \times_S T$ whose closed subscheme is finite, flat and locally of finite presentation over $T$ with flat rank $1$ at every point of $T$. Its ideal sheaf is $\ker \Gamma_a$, the rank being $1$ because the structural morphism is an isomorphism.
--
--   In the converse direction, for an arbitrary $D \colon$ `RelEffCartierDiv f 1 g` the finite flat morphism from the subscheme of $D.I$ to $T$ has everywhere flat rank $1$ and is therefore an isomorphism; `RelEffCartierDiv.toPoint` is its inverse followed by the inclusion and the first projection, giving a morphism $T \to \mathcal{C}$, and `RelEffCartierDiv.toPoint_comp` states that this morphism followed by $f$ is $g$, so that it is a $T$-point of $\mathcal{C}$ over $S$.
--
--   **Relation to Mathlib.** Mathlib supplies the pullback calculus for schemes, ideal sheaf data with its closed subscheme and inclusion, the kernel ideal sheaf of a morphism, and the flat-rank function on a finite flat morphism; the structure `RelEffCartierDiv` of relative effective divisors of a given degree, and the passage between degree-one such divisors and points, are the project's own.
--
--   **Where it is used.** These constructions are part of the project's theory of relative effective divisors on curves, where they provide the two mutually inverse assignments between $T$-points of $\mathcal{C}$ over $S$ and degree-one relative divisors, the starting point for identifying the degree-one divisor functor with the curve itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelEffCartierDivOfPoint.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T : Scheme.{u}} {g : T ⟶ S}

noncomputable def graphOver (a : T ⟶ 𝒞) (ha : a ≫ f = g) : T ⟶ pullback f g :=
  pullback.lift a (𝟙 T) (ha.trans (Category.id_comp g).symm)

lemma graphOver_eq_lift (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha = pullback.lift a (𝟙 T) (ha.trans (Category.id_comp g).symm) := rfl

@[reassoc (attr := simp)]
lemma graphOver_fst (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha ≫ pullback.fst f g = a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graphOver_snd (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha ≫ pullback.snd f g = 𝟙 T :=
  pullback.lift_snd _ _ _

instance isClosedImmersion_graphOver [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    IsClosedImmersion (graphOver f a ha) := by
  have : IsClosedImmersion (graphOver f a ha ≫ pullback.snd f g) := by
    rw [graphOver_snd]; infer_instance
  exact .of_comp (graphOver f a ha) (pullback.snd f g)

instance isIso_ker_graphOver_subschemeIota_snd [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    IsIso ((graphOver f a ha).ker.subschemeι ≫ pullback.snd f g) := by
  have h : (graphOver f a ha).toImage ≫ ((graphOver f a ha).ker.subschemeι ≫ pullback.snd f g)
      = 𝟙 T := by
    rw [← Category.assoc]
    change ((graphOver f a ha).toImage ≫ (graphOver f a ha).imageι) ≫ _ = _
    rw [Scheme.Hom.toImage_imageι, graphOver_snd]
  exact IsIso.of_isIso_fac_left h

noncomputable def RelEffCartierDiv.ofPoint [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    RelEffCartierDiv f 1 g where
  I := (graphOver f a ha).ker
  isFinite := inferInstance
  flat := inferInstance
  locallyOfFinitePresentation := inferInstance
  finrank_eq t := by
    rw [Scheme.Hom.finrank_eq_one_of_isIso ((graphOver f a ha).ker.subschemeι ≫ pullback.snd f g)]
    rfl

@[simp] lemma RelEffCartierDiv.ofPoint_I [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    (RelEffCartierDiv.ofPoint f a ha).I = (graphOver f a ha).ker := rfl

variable {f} in

instance RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one (D : RelEffCartierDiv f 1 g) :
    IsIso (D.I.subschemeι ≫ pullback.snd f g) := by
  have := D.isFinite
  have := D.flat
  exact (Scheme.Hom.isIso_iff_finrank_eq _).mpr (funext fun t => D.finrank_eq t)

variable {f} in

noncomputable def RelEffCartierDiv.toPoint (D : RelEffCartierDiv f 1 g) : T ⟶ 𝒞 :=
  inv (D.I.subschemeι ≫ pullback.snd f g) ≫ D.I.subschemeι ≫ pullback.fst f g

variable {f} in

@[reassoc (attr := simp)]
lemma RelEffCartierDiv.toPoint_comp (D : RelEffCartierDiv f 1 g) : D.toPoint ≫ f = g := by
  calc D.toPoint ≫ f
      = inv (D.I.subschemeι ≫ pullback.snd f g) ≫ D.I.subschemeι ≫ (pullback.fst f g ≫ f) := by
        simp only [RelEffCartierDiv.toPoint, Category.assoc]
    _ = inv (D.I.subschemeι ≫ pullback.snd f g) ≫ (D.I.subschemeι ≫ pullback.snd f g) ≫ g := by
        rw [pullback.condition, Category.assoc]
    _ = g := by rw [IsIso.inv_hom_id_assoc]

end AlgebraicGeometry


