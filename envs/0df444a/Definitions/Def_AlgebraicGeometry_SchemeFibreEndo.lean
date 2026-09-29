-- Prove2me | Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
-- name    : AlgebraicGeometry_SchemeFibreEndo
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/86caebd1-513b-573a-8654-8cfe36db2e09
-- title:
--   Endomorphism induced on a scheme-theoretic fibre
-- statement:
--   Let $f \colon X \to S$ be a morphism of schemes (in a fixed universe) and let $h \colon X \to X$ satisfy $h$ followed by $f$ equals $f$, i.e. $f \circ h = f$, so that $h$ is an endomorphism of $X$ over $S$. For a point $s$ of $S$, the fibre of $f$ at $s$ is taken in the form of the pullback of $f$ along the canonical morphism $\operatorname{Spec}\kappa(s) \to S$ from the residue field at $s$ (Mathlib's `Scheme.fromSpecResidueField`), so $X_s = X \times_S \operatorname{Spec}\kappa(s)$ as a chosen pullback object. The definition `schemeFibreEndo` produces an endomorphism of this object: it is the morphism into the pullback determined by the pair consisting of the first projection followed by $h$, and the second projection, the required compatibility being the identity $f \circ h = f$ combined with the defining square of the pullback. Thus `schemeFibreEndo f h hcomm s` is the map $h_s \colon X_s \to X_s$ induced by $h$ on the fibre over $s$, recorded as a concrete morphism between the chosen pullback objects rather than as a morphism of an abstractly characterised fibre.
--
--   The two accompanying lemmas record its two defining properties, each as a simp lemma: composing $h_s$ with the first projection $X_s \to X$ gives the first projection followed by $h$, and composing $h_s$ with the second projection $X_s \to \operatorname{Spec}\kappa(s)$ gives the second projection unchanged (so $h_s$ is a morphism over $\operatorname{Spec}\kappa(s)$). Together they characterise $h_s$ uniquely by the universal property of the pullback.
--
--   **Relation to Mathlib.** Built from Mathlib's pullbacks of schemes and its residue-field morphism `Scheme.fromSpecResidueField`; Mathlib has no notion of the endomorphism induced by an $S$-endomorphism on a fibre, so this is the project's own packaging.
--
--   **Where it is used.** This is infrastructure for the fibrewise criterion for flatness of an $S$-endomorphism: under suitable finiteness and flatness hypotheses on $f$, flatness of $h$ is tested on the maps $h_s$ over the points $s$ of the base. It is used in the project when verifying flatness of multiplication-by-$N$ type endomorphisms on group schemes arising in the study of Galois representations attached to elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SchemeFibreEndo.lean

import Mathlib.AlgebraicGeometry.ResidueField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

def schemeFibreEndo {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X) (hcomm : h ≫ f = f)
    (s : S) :
    Limits.pullback f (S.fromSpecResidueField s)
      ⟶ Limits.pullback f (S.fromSpecResidueField s) :=
  Limits.pullback.lift (Limits.pullback.fst _ _ ≫ h) (Limits.pullback.snd _ _)
    (by rw [Category.assoc, hcomm, Limits.pullback.condition])

@[simp] theorem schemeFibreEndo_fst {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X)
    (hcomm : h ≫ f = f) (s : S) :
    schemeFibreEndo f h hcomm s ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ ≫ h :=
  Limits.pullback.lift_fst _ _ _

@[simp] theorem schemeFibreEndo_snd {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X)
    (hcomm : h ≫ f = f) (s : S) :
    schemeFibreEndo f h hcomm s ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ :=
  Limits.pullback.lift_snd _ _ _

end AlgebraicGeometry


