-- Prove2me | Definitions.Def_PhilipponMultiplicity_GenericCurveCoverFamily
-- name    : PhilipponMultiplicity_GenericCurveCoverFamily
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-25T21:37:13.181617+00:00
-- url     : https://prove2.me/theorems/473a2404-ae2c-4967-820b-7f623e95bb00
-- title:
--   Normal projective base and dominating smooth generic-curve covering family
-- statement:
--   For a field $k$, schemes $S,X$, maps $\pi:S\to\operatorname{Spec}k$ and $q:X\to S$, and a specified point $\eta\in S$, this predicate records a normal projective base model and a dominating smooth generic-curve covering family. The coefficient field is the actual residue field $\kappa(\eta)$, with its $k$-algebra structure induced by $\pi$.
--
--   The data comprise a finite intermediate field $E$ inside the prescribed algebraic closure of $\kappa(\eta)$; a normal finitely generated $k$-subalgebra $B\subset E$ with fraction field $E$; and a normal integral projective scheme $N$ mapping properly and surjectively to $S$, with the same dimension. A specified dense affine chart $\operatorname{Spec}B\hookrightarrow N$ retains the $k$-structure equation and the exact generic spectrum map.
--
--   On a dense open $U\subset N$, the predicate records an actual smooth proper family $Y\to U$, a flat proper target $Z=X\times_S U$, and a proper surjection $Y\to Z$ whose composite to $X$ is dominant. It includes a closed embedding of a projective ambient source model over a principal localization of $B$ and its cartesian restriction to $U$.
--
--   Finally it retains a smooth projective $E$-scheme $C_0$ of dimension at most one, a proper surjection $C_0\to X_\eta$ with exact scalar compatibility, a factorization $\operatorname{Spec}E\to U$, and a cartesian comparison $C_0\to Y$. The composite to $X$ is exactly the original covering map followed by the generic-fibre inclusion. The existence theorem under projective fibration hypotheses is published separately.
-- source:
--   Finite-base and family preparation for the Philippon alteration frontier https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249 . Uses the accepted normal projective finite-generic-field base model https://prove2.me/theorems/a2fa0ad5-6962-47c5-9e21-5fc176c6d9cb , actual scalar-extended curve cover https://prove2.me/theorems/a0fdd6ed-d4f7-42ef-8b17-f8add5de7610 , and projective generic-cover family construction https://prove2.me/theorems/9d194c42-8928-4185-90b1-2e9ba53665ea . Exact iterated pullback comparisons preserve the original generic covering map, and density of the actual generic fibre proves dominance of the resulting map to X. This is the preparation stage; semistable compactification, base alteration and global regularization are not supplied.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual finite-generic-field base data and a dominating smooth projective
covering family, retaining the original generic covering map. -/
noncomputable def AlgebraicGeometry.HasNormalProjectiveBaseSmoothCurveCoverFamily
    (k : Type u) [Field k] {S X : Scheme.{u}}
    (π : S ⟶ Spec (.of k)) (q : X ⟶ S) (η : S) : Prop :=
    letI : Algebra k (S.residueField η) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ S.presheaf.germ ⊤ η trivial ≫ S.residue η).hom.toAlgebra
    ∃ E : IntermediateField (S.residueField η) (AlgebraicClosure (S.residueField η)),
      FiniteDimensional (S.residueField η) E ∧
      letI : Algebra k E := ((algebraMap (S.residueField η) E).comp (algebraMap k (S.residueField η))).toAlgebra
      ∃ B : Subalgebra k E, Algebra.FiniteType k B ∧ IsIntegrallyClosed B ∧ IsFractionRing B E ∧
        ∃ (N : Scheme.{u}) (qN : N ⟶ S) (t : Spec (.of B) ⟶ N),
          IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
          IsProper qN ∧ Surjective qN ∧ IsOpenImmersion t ∧ IsDominant t ∧
          topologicalKrullDim N = topologicalKrullDim S ∧
          t ≫ (qN ≫ π) = Spec.map (CommRingCat.ofHom (algebraMap k B)) ∧
          Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t ≫ qN =
            Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) E)) ≫ S.fromSpecResidueField η ∧
          (∃ (nN : ℕ) (iN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (nN + 1)) k)),
            IsClosedImmersion iN ∧ iN ≫ ProjSpace.π k nN = qN ≫ π) ∧
          ∃ a : B, a ≠ 0 ∧ ∃ (nM : ℕ) (M : Scheme.{u})
            (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (nM + 1)) (Localization.Away a))),
            IsClosedImmersion iM ∧
            ∃ (U : Scheme.{u}) (j : U ⟶ Spec (.of (Localization.Away a))),
              IsOpenImmersion j ∧ DenseRange j ∧
              let u : U ⟶ N := (j ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a)))) ≫ t
              IsOpenImmersion u ∧ IsDominant u ∧
              ∃ (Y Z : Scheme.{u}) (pY : Y ⟶ U) (pZ : Z ⟶ U)
                (tY : Y ⟶ M) (tZ : Z ⟶ X) (h : Y ⟶ Z),
                IsPullback tY pY (iM ≫ ProjSpace.π (Localization.Away a) nM) j ∧
                IsPullback tZ pZ q (u ≫ qN) ∧ Flat pZ ∧ IsProper pZ ∧
                h ≫ pZ = pY ∧ IsProper h ∧ Surjective h ∧
                Smooth pY ∧ IsProper pY ∧ IsDominant (h ≫ tZ) ∧
                ∃ (C₀ : Scheme.{u}) (p₀ : C₀ ⟶ Spec (.of E)) (a₀ : C₀ ⟶ q.fiber η),
                  Smooth p₀ ∧ IsProper p₀ ∧ topologicalKrullDim C₀ ≤ 1 ∧
                  IsProper a₀ ∧ Surjective a₀ ∧
                  a₀ ≫ q.fiberToSpecResidueField η = p₀ ≫
                    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) E)) ∧
                  (∃ i₀ : C₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (nM + 1)) E),
                    IsClosedImmersion i₀ ∧ i₀ ≫ ProjSpace.π E nM = p₀) ∧
                  ∃ (b : Spec (.of E) ⟶ U) (eC : C₀ ⟶ Y),
                    b ≫ u = Spec.map (CommRingCat.ofHom (algebraMap B E)) ≫ t ∧
                    IsPullback eC p₀ pY b ∧ eC ≫ h ≫ tZ = a₀ ≫ q.fiberι η


