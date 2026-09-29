-- Prove2me | Definitions.Def_Deformations_LiftFunctor
-- name    : Deformations_LiftFunctor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/3f5d9a4a-02e7-5a6e-aa76-79075bef950e
-- title:
--   Representation, lift and deformation functors on pro-Artinian algebras
-- statement:
--   Fix a finite index type $n$, a topological group $G$ and a local ring $\mathcal O$, and work over the category `ProartinianCat 𝓞` whose objects are topological $\mathcal O$-algebras $R$ that are local, pro-Artinian, with $\mathcal O \to R$ local and inducing a surjection onto the residue field of $R$, and whose morphisms are continuous $\mathcal O$-algebra maps; this category has terminal object `ProartinianCat.residueField`, the residue field $k$ of $\mathcal O$ with the discrete topology.
--
--   `repnFunctor n G 𝓞` sends $R$ to the set of continuous monoid homomorphisms $G \to \mathrm{GL}_n(R)$ and a morphism $f\colon R \to S$ to push-forward along the entrywise map $\mathrm{GL}_n(R)\to\mathrm{GL}_n(S)$; `repnFunctor_map` records the pointwise formula $((\mathrm{repnFunctor}).map\,f\,\rho)(x) = \mathrm{GL}_n(f)(\rho x)$. `toRepresentation` turns such a point into a `Representation R G (n → R)`, i.e. a homomorphism of $G$ into the $R$-endomorphisms of $R^n$, by composing $\rho$ with $\mathrm{GL}_n(R)\to\mathrm{GL}(R^n)$ and the inclusion of units.
--
--   `repnQuotFunctor n G 𝓞` sends $R$ to the orbit quotient of $G \to_{\mathrm{cont}} \mathrm{GL}_n(R)$ under the conjugation action of the subgroup of $\mathrm{ConjAct}(\mathrm{GL}_n(R))$ corresponding to the kernel of $\mathrm{GL}_n(R)\to\mathrm{GL}_n(k)$ induced by `ProartinianCat.toResidueField R`; that is, quotient by strict equivalence. Functoriality of this quotient is part of the definition, and `toRepnQuot` is the natural transformation given objectwise by the quotient map.
--
--   For a point $\bar\rho$ of `repnFunctor` at the terminal object, `liftFunctor` and `deformationFunctor` are the subfunctors obtained from `Subfunctor.ofIsTerminal` applied to the singleton $\{\bar\rho\}$, respectively its class: objectwise, the continuous $\rho\colon G\to\mathrm{GL}_n(R)$ whose reduction along the unique map $R \to k$ equals $\bar\rho$, and the strict equivalence classes reducing to the class of $\bar\rho$.
--
--   **Relation to Mathlib.** Mathlib has no deformation functors; these are the project's own, built on Mathlib's `CategoryTheory.Subfunctor`, `Matrix.GeneralLinearGroup`, `Representation` and `MulAction.orbitRel.Quotient`, together with the project's category of local pro-Artinian $\mathcal O$-algebras and the construction of a subfunctor from a subset of the value at a terminal object.
--
--   **Where it is used.** These are the functors whose pro-representing objects are the universal lifting and universal deformation rings of a residual representation $\bar\rho$, the deformation-theoretic input to the modularity lifting argument; deformation conditions are imposed as further subfunctors of the lift functor.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Deformations/LiftFunctor.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Deformations_LiftFunctor.lean

import Mathlib
import Definitions.Def_Deformations_ProartinianCat
import Definitions.Def_CategoryTheory_Subfunctor_OfIsTerminal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory IsLocalRing

namespace Deformation

universe u

variable {n : Type} [Fintype n] [DecidableEq n] (G : Type u) [Group G] [TopologicalSpace G]
variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]

variable (n) in

def repnFunctor : ProartinianCat 𝓞 ⥤ Type u where
  obj R := G →ₜ* GL n R
  map {R S} f := ↾ (fun ρ ↦ .comp (Units.mapₜ f.hom.mapMatrix.toContinuousMonoidHom) ρ)

omit [IsLocalRing 𝓞] in
@[simp]
lemma repnFunctor_map {R S : ProartinianCat 𝓞} (f : R ⟶ S) (ρ : G →ₜ* GL n R) (x : G) :
    DFunLike.coe (F := G →ₜ* GL n S) ((repnFunctor n G 𝓞).map f ρ) x =
      Matrix.GeneralLinearGroup.map (n := n) f.hom.toRingHom (ρ x) := rfl

variable {G 𝓞} in

def toRepresentation {R} (ρ : (repnFunctor n G 𝓞).obj R) :
    Representation R G (n → R) :=
  (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ.toMonoidHom)

variable (n)

set_option backward.isDefEq.respectTransparency false in

noncomputable
def repnQuotFunctor : ProartinianCat 𝓞 ⥤ Type u where
  obj R := MulAction.orbitRel.Quotient ((Matrix.GeneralLinearGroup.map (n := n)
    (ProartinianCat.toResidueField R).hom.toRingHom).ker.comap (ConjAct.ofConjAct.toMonoidHom))
    (G →ₜ* GL n R)
  map {R S} f := ↾Quotient.map ((repnFunctor n G 𝓞).map f) (by
    rintro _ ρ ⟨⟨g, hg⟩, rfl⟩
    refine ⟨⟨.toConjAct (Matrix.GeneralLinearGroup.map f.hom.toRingHom g.ofConjAct), ?_⟩, ?_⟩
    · simpa [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
        ← RingHom.coe_comp, ← ContinuousAlgHom.coe_comp,
        -AlgHomClass.toRingHom_toAlgHom, ← AlgHom.comp_toRingHom, ← ProartinianCat.hom_comp,
        Subsingleton.elim _ R.toResidueField]
    · obtain ⟨g, rfl⟩ := ConjAct.toConjAct.surjective g
      ext1 γ
      simp [ConjAct.toConjAct_smul, ← map_inv, -ConjAct.ofConjAct_inv, ← map_mul])
  map_id _ := by ext ⟨_⟩; rfl
  map_comp _ _ := by ext ⟨_⟩; rfl

noncomputable
def toRepnQuot : repnFunctor n G 𝓞 ⟶ repnQuotFunctor n G 𝓞 where
  app _ := ↾Quotient.mk''
  naturality _ _ _ := rfl

noncomputable
def liftFunctor (ρ : (repnFunctor n G 𝓞).obj .residueField) : Subfunctor (repnFunctor n G 𝓞) :=
  .ofIsTerminal _ ProartinianCat.isTerminalResidueField {ρ}

noncomputable
def deformationFunctor (ρ : (repnFunctor n G 𝓞).obj .residueField) :
    Subfunctor (repnQuotFunctor n G 𝓞) :=
  .ofIsTerminal _ ProartinianCat.isTerminalResidueField {(toRepnQuot n G 𝓞).app _ ρ}

end Deformation


