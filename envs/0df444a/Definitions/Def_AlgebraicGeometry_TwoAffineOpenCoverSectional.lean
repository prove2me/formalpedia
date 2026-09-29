-- Prove2me | Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
-- name    : AlgebraicGeometry_TwoAffineOpenCoverSectional
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/195a4400-f5a0-5004-8b5e-a2ec51fc846a
-- title:
--   Sectional two-chart covers, evaluation and boundary residues
-- statement:
--   Throughout, $R$ is a commutative ring, $X$ a scheme, $\mathcal V$ a two-affine open cover of $X$ — a pair of affine opens $U_0,U_1$ with affine intersection and $U_0\sqcup U_1=\top$ — and $c\colon X\to\operatorname{Spec}R$ a morphism; the associated two-chart Čech cover $\mathcal V.\mathrm{cover}\,c$ has $A_0=\Gamma(X,U_0)$, $A_1=\Gamma(X,U_1)$, $A_{01}=\Gamma(X,U_0\cap U_1)$, made into $R$-algebras through $c$ and linked by the restriction maps.
--
--   `IsSectional` is a predicate on a family $\sigma\colon\iota\to\mathrm{Hom}(\operatorname{Spec}R,X)$ indexed by an arbitrary type, recording four conditions: each $\sigma_i$ followed by $c$ is the identity of $\operatorname{Spec}R$, so $\sigma_i$ is a section of $c$; the set-theoretic range of the underlying map of each $\sigma_i$ lies in $U_0$; the complement of $U_1$, as a subset of $X$, is exactly the union of these ranges; and the ranges are pairwise disjoint. Nothing is asserted about the $\sigma_i$ being immersions, nor about Laurent expansions existing along them.
--
--   `sectionAlgHom` attaches to a single section $\sigma$ of $c$ whose range lies in $U_0$ the evaluation map: the pullback $\sigma^{*}\colon\Gamma(X,U_0)\to\Gamma(\operatorname{Spec}R,\top)$ composed with the canonical identification $\Gamma(\operatorname{Spec}R,\top)\cong R$, presented as a map of $R$-algebras $A_0\to R$; the $R$-algebra compatibility is where the hypothesis $\sigma\circ$ (i.e. $c\circ\sigma=\mathrm{id}$) is used.
--
--   `sectionResidue` is notation: given a family $\Lambda\colon\iota\to$ Laurent charts of $\mathcal V.\mathrm{cover}\,c$ and an index $i$, it is the $R$-linear residue map $\Omega_{A_{01}/R}\to R$ of $\Lambda_i$, namely $\omega\mapsto$ the coefficient of $t^{-1}$ in the Laurent series obtained from $\omega$ through the derivation induced by the expansion homomorphism of $\Lambda_i$.
--
--   **Relation to Mathlib.** Mathlib has affine open covers of schemes but no notion of a two-chart cover, of a sectional family of boundary sections, or of Laurent charts; these are the project's own. The evaluation map is assembled from Mathlib's `Scheme.Hom.appLE` and `Scheme.ΓSpecIso`.
--
--   **Where it is used.** These notions set up the explicit two-chart Čech description of line bundles on a curve over a base $R$, with $U_0$ a chart containing the marked sections and $U_1$ its complementary chart, so that $U_0\cap U_1$ is $U_0$ with the boundary sections removed. Evaluation along a section and the residues of the associated Laurent charts are the ingredients of the resulting cohomology and duality computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoAffineOpenCoverSectional.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open CategoryTheory CategoryTheory.Limits Opposite

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

structure IsSectional {ι : Type v} (σ : ι → (Spec (.of R) ⟶ X)) : Prop where

  comp_eq : ∀ i, σ i ≫ c = 𝟙 _

  range_subset : ∀ i, Set.range (σ i).base ⊆ (𝒱.U0 : Set X)

  compl_eq_iUnion : (𝒱.U1 : Set X)ᶜ = ⋃ i, Set.range (σ i).base

  pairwise_disjoint : Pairwise fun i j => Disjoint (Set.range (σ i).base) (Set.range (σ j).base)

variable {𝒱 c}

def sectionAlgHom (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ c = 𝟙 _) (hU : Set.range σ.base ⊆ (𝒱.U0 : Set X)) :
    (𝒱.cover c).A0 →ₐ[R] R :=
  letI := algebraOfHom c 𝒱.U0
  { (σ.appLE 𝒱.U0 ⊤ (fun x _ => hU ⟨x, rfl⟩) ≫ (Scheme.ΓSpecIso (.of R)).hom).hom with
    commutes' := fun r => by
      change ((Scheme.ΓSpecIso (.of R)).inv ≫ (c.appLE ⊤ 𝒱.U0 le_top ≫ σ.appLE 𝒱.U0 ⊤ _) ≫
        (Scheme.ΓSpecIso (.of R)).hom).hom r = r
      rw [Scheme.Hom.appLE_comp_appLE]
      suffices key : ∀ (φ : Spec (.of R) ⟶ Spec (.of R)), φ = 𝟙 _ → ∀ (e : (⊤ : (Spec (.of R)).Opens) ≤ φ ⁻¹ᵁ ⊤),
          (Scheme.ΓSpecIso (.of R)).inv ≫ φ.appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso (.of R)).hom = 𝟙 _ by
        rw [key _ hσ]; rfl
      rintro φ rfl e
      have hid : (𝟙 (Spec (.of R)) : Spec (.of R) ⟶ Spec (.of R)).appLE ⊤ ⊤ e = 𝟙 _ := by
        change (𝟙 (Spec (.of R)) : Spec (.of R) ⟶ Spec (.of R)).app ⊤ ≫ (Spec (.of R)).presheaf.map _ = _
        rw [Scheme.Hom.id_app]
        erw [Category.id_comp]
        exact (congrArg (Spec (.of R)).presheaf.map (Subsingleton.elim _ _)).trans ((Spec (.of R)).presheaf.map_id _)
      rw [hid, Category.id_comp, Iso.inv_hom_id] }

abbrev sectionResidue {ι : Type v} (Λ : ι → (𝒱.cover c).LaurentChart) (i : ι) :
    Ω[(𝒱.cover c).A01⁄R] →ₗ[R] R :=
  (Λ i).residue

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end


