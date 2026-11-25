-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_007
-- name    : RPLib_FX_EtPBC_007
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T17:25:02.081223+00:00
-- url     : https://prove2.me/theorems/790ee0bd-8d44-50a3-b58d-9b6d3a2284d4
-- title:
--   Proper base change for the projective line, library file 007
-- statement:
--   File 007 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_NilLift`: S4-EtPBC-A, R4-F1a/b: etale algebras lift uniquely along nilpotent thickenings
--   * `S4.Def_RP_EtPBC_A_CovL1`: S4-EtPBC-A, R4-T2 (A1a): away maps, localized base change and the reduction map
--   * `S4.Def_RP_EtPBC_A_CovAR`: S4-EtPBC-A, R4-T2 (A2c-1b): uniform relations of `p` on the base charts (Artin-Rees)
--   * `S4.Def_RP_EtPBC_A_CovAs1`: S4-EtPBC-A, R4-T2 (A3 assembly, As1): base change of the chart data along a flat algebra
--   * `S4.Def_RP_EtPBC_A_CovAs2`: S4-EtPBC-A, R4-T2 (A3 assembly, As2): the level-0 cover over generic charts, and the fibre kernel
--   * `S4.Def_RP_EtPBC_A_CovFl`: S4-EtPBC-A, R4-T2 (A2c-1c): relations on a flat level-`m` chart come from the base (equational criterion)
--   * `S4.Def_RP_EtPBC_A_CovAs3e`: S4-EtPBC-A, R4-T2 (A3 assembly, As3e): residue and base-change facts for the instantiation over `Â`
--   * `S4.Def_RP_EtPBC_A_CovAsN1`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN1): power series map onto the adic completion
--   * `S4.Def_RP_EtPBC_A_CovAsN2`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN2): `A⟦X_σ⟧` is precomplete for the ideal of the variables
--   * `S4.Def_RP_EtPBC_A_CovAs3f`: S4-EtPBC-A, R4-T2 (A3 assembly, As3f): the completed cover over `Â` from the `CoverLiftAt₂` data
--   * `S4.Def_RP_EtPBC_A_CovAs5a`: S4-EtPBC-A, R4-T2 (A3 assembly, As5a): lifting polynomials and memberships to a f.g. subalgebra
--   * `S4.Def_RP_EtPBC_A_CovPr16`: S4-EtPBC-A, R4-T2 (A3p): the residue `θh` of a descended presentation from a chart `E` (generic)
--   * `S4.Def_RP_EtPBC_A_Z3Res`: S4-EtPBC-A, (Z) geometric layer 2: chart conditions from affine opens and finite morphisms
--   * `S4.Def_RP_EtPBC_A_Z4Base`: S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`
--   * `S4.Def_RP_EtPBC_A_Z4FibB`: S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovCh`: S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`
--   * `S4.Def_RP_EtPBC_A_Inj0a`: S4-EtPBC-A, G1a: germs of a pulled-back section control the support
--   * `S4.Def_RP_EtPBC_A_Xi`: S4-EtPBC-A, M2 F5: the germ `ξ_s(b)` of a section of a pullback
--   * `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
--   * `S4.Def_RP_EtPBC_A_VPart`: S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values
--   * `S4.Def_RP_EtPBC_A_NbExt1`: S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods
--   * `S4.Def_RP_EtPBC_A_DescG1`: S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart
--   * `S4.Def_RP_EtPBC_A_DescG2`: S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens
--   * `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
--   * `S4.Def_RP_EtPBC_A_NbExt2`: S4-EtPBC-A, M2 F8a: extending a clopen of `Y_s` to an etale neighbourhood
--   * `S4.Def_RP_EtPBC_A_FBCv`: S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre
--   * `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
--   * `S4.Def_RP_EtPBC_A_T3dA`: S4-EtPBC-A, R4-T3d (part A): classes as extensions, and the kill by an extension
--   * `S4.Def_RP_EtPBC_A_T3dB`: S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`
--   * `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
--   * `S4.Def_RP_EtPBC_A_O2Fs`: S4-EtPBC-A, O2 (MV route), Fs: stalks of free sheaves
--   * `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
--   * `S4.Def_RP_EtPBC_A_O2Gl2e`: S4-EtPBC-A, O2 GLOB (O2Gl2e): stage S4, the values of `H` on the pieces of `W₂`
--   * `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
--   * `S4.Def_RP_EtPBC_A_O2PP2`: S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)
--   * `S4.Def_RP_EtPBC_A_O2Gl1a`: S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point
--   * `S4.Def_RP_EtPBC_A_O2PP4f`: S4-EtPBC-A, O2 PP' (O2PP4f): PP' at a chart `D` for a piece `p` and a Kummer radical `α`
--   * `S4.Def_RP_EtPBC_A_O2L1a`: S4-EtPBC-A, L1a (MVr combinatorics): exactness of the free MV complex fibrewise over `C`
--   * `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_001
import Definitions.Def_RPLib_FX_EtPBC_002
import Definitions.Def_RPLib_FX_EtPBC_004

/-!
# Proper base change for the projective line, library file 007

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_NilLift`: S4-EtPBC-A, R4-F1a/b: etale algebras lift uniquely along nilpotent thickenings
* `S4.Def_RP_EtPBC_A_CovL1`: S4-EtPBC-A, R4-T2 (A1a): away maps, localized base change and the reduction map
* `S4.Def_RP_EtPBC_A_CovAR`: S4-EtPBC-A, R4-T2 (A2c-1b): uniform relations of `p` on the base charts (Artin-Rees)
* `S4.Def_RP_EtPBC_A_CovAs1`: S4-EtPBC-A, R4-T2 (A3 assembly, As1): base change of the chart data along a flat algebra
* `S4.Def_RP_EtPBC_A_CovAs2`: S4-EtPBC-A, R4-T2 (A3 assembly, As2): the level-0 cover over generic charts, and the fibre kernel
* `S4.Def_RP_EtPBC_A_CovFl`: S4-EtPBC-A, R4-T2 (A2c-1c): relations on a flat level-`m` chart come from the base (equational criterion)
* `S4.Def_RP_EtPBC_A_CovAs3e`: S4-EtPBC-A, R4-T2 (A3 assembly, As3e): residue and base-change facts for the instantiation over `Â`
* `S4.Def_RP_EtPBC_A_CovAsN1`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN1): power series map onto the adic completion
* `S4.Def_RP_EtPBC_A_CovAsN2`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN2): `A⟦X_σ⟧` is precomplete for the ideal of the variables
* `S4.Def_RP_EtPBC_A_CovAs3f`: S4-EtPBC-A, R4-T2 (A3 assembly, As3f): the completed cover over `Â` from the `CoverLiftAt₂` data
* `S4.Def_RP_EtPBC_A_CovAs5a`: S4-EtPBC-A, R4-T2 (A3 assembly, As5a): lifting polynomials and memberships to a f.g. subalgebra
* `S4.Def_RP_EtPBC_A_CovPr16`: S4-EtPBC-A, R4-T2 (A3p): the residue `θh` of a descended presentation from a chart `E` (generic)
* `S4.Def_RP_EtPBC_A_Z3Res`: S4-EtPBC-A, (Z) geometric layer 2: chart conditions from affine opens and finite morphisms
* `S4.Def_RP_EtPBC_A_Z4Base`: S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`
* `S4.Def_RP_EtPBC_A_Z4FibB`: S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovCh`: S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`
* `S4.Def_RP_EtPBC_A_Inj0a`: S4-EtPBC-A, G1a: germs of a pulled-back section control the support
* `S4.Def_RP_EtPBC_A_Xi`: S4-EtPBC-A, M2 F5: the germ `ξ_s(b)` of a section of a pullback
* `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
* `S4.Def_RP_EtPBC_A_VPart`: S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values
* `S4.Def_RP_EtPBC_A_NbExt1`: S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods
* `S4.Def_RP_EtPBC_A_DescG1`: S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart
* `S4.Def_RP_EtPBC_A_DescG2`: S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens
* `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
* `S4.Def_RP_EtPBC_A_NbExt2`: S4-EtPBC-A, M2 F8a: extending a clopen of `Y_s` to an etale neighbourhood
* `S4.Def_RP_EtPBC_A_FBCv`: S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre
* `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
* `S4.Def_RP_EtPBC_A_T3dA`: S4-EtPBC-A, R4-T3d (part A): classes as extensions, and the kill by an extension
* `S4.Def_RP_EtPBC_A_T3dB`: S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`
* `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
* `S4.Def_RP_EtPBC_A_O2Fs`: S4-EtPBC-A, O2 (MV route), Fs: stalks of free sheaves
* `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
* `S4.Def_RP_EtPBC_A_O2Gl2e`: S4-EtPBC-A, O2 GLOB (O2Gl2e): stage S4, the values of `H` on the pieces of `W₂`
* `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
* `S4.Def_RP_EtPBC_A_O2PP2`: S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)
* `S4.Def_RP_EtPBC_A_O2Gl1a`: S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point
* `S4.Def_RP_EtPBC_A_O2PP4f`: S4-EtPBC-A, O2 PP' (O2PP4f): PP' at a chart `D` for a piece `p` and a Kummer radical `α`
* `S4.Def_RP_EtPBC_A_O2L1a`: S4-EtPBC-A, L1a (MVr combinatorics): exactness of the free MV complex fibrewise over `C`
* `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_NilLift =====
section

/-!
# S4-EtPBC-A, R4-F1a/b: etale algebras lift uniquely along nilpotent thickenings

`φ : R →+* R₀` surjective with nilpotent kernel `J`.

* `isUnit_of_map`: units lift along a surjection with nilpotent kernel.
* **`exists_etale_lift`**: every etale `R₀`-algebra `B₀` is `B ⧸ J B` for an etale `R`-algebra `B`
  (`f : B →+* B₀` surjective, `ker f = J B`, compatible with `φ`), and `B` is finite over `R` when `B₀` is finite
  over `R₀`. Proof: a global submersive presentation of relative dimension `0` of `B₀`
  (`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`), lift its relations, the Jacobian stays a unit.
* **`exists_hom_lift`**, `hom_lift_unique`: ring maps from an etale `R`-algebra lift uniquely along a surjection
  with nilpotent kernel (compatible with `R`).
* **`exists_iso_lift`**: two etale lifts of the same `B₀` are isomorphic over `B₀`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.NilLift

universe u

open MvPolynomial

variable {R R₀ : Type u} [CommRing R] [CommRing R₀]

/-- **Etale algebras lift along nilpotent thickenings** (finite ones to finite ones). -/
theorem exists_etale_lift (φ : R →+* R₀) (hφ : Function.Surjective φ) (hJ : IsNilpotent (RingHom.ker φ))
    (B₀ : Type u) [CommRing B₀] [Algebra R₀ B₀] [Algebra.Etale R₀ B₀] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B) (f : B →+* B₀),
      Algebra.Etale R B ∧ Function.Surjective f ∧
      RingHom.ker f = (RingHom.ker φ).map (algebraMap R B) ∧
      f.comp (algebraMap R B) = (algebraMap R₀ B₀).comp φ ∧
      (Module.Finite R₀ B₀ → Module.Finite R B) := by
  classical
  obtain ⟨ι, σ, _, _, P₀, hP₀⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp ‹_›).out
  letI : Fintype σ := Fintype.ofFinite σ
  have hmap := MvPolynomial.map_surjective (σ := ι) φ hφ
  let v : σ → MvPolynomial ι R := fun j => (hmap (P₀.relation j)).choose
  have hv : ∀ j, MvPolynomial.map φ (v j) = P₀.relation j := fun j => (hmap _).choose_spec
  let I : Ideal (MvPolynomial ι R) := Ideal.span (Set.range v)
  let g : MvPolynomial ι R →+* B₀ :=
    (MvPolynomial.aeval (R := R₀) P₀.val).toRingHom.comp (MvPolynomial.map φ)
  have hg : ∀ p, g p = MvPolynomial.aeval (R := R₀) P₀.val (MvPolynomial.map φ p) := fun p => rfl
  have hIg : I ≤ RingHom.ker g := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simp [hg, hv, P₀.aeval_val_relation]
  let f : (MvPolynomial ι R ⧸ I) →+* B₀ := Ideal.Quotient.lift I g hIg
  have hf : ∀ p, f (Ideal.Quotient.mk I p) = g p := fun p => rfl
  have hfsurj : Function.Surjective f := by
    intro b
    obtain ⟨p, rfl⟩ := P₀.aeval_val_surjective b
    obtain ⟨q, rfl⟩ := hmap p
    exact ⟨Ideal.Quotient.mk I q, rfl⟩
  have hcomp : f.comp (algebraMap R (MvPolynomial ι R ⧸ I)) = (algebraMap R₀ B₀).comp φ := by
    ext r
    rw [RingHom.comp_apply, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply R (MvPolynomial ι R) (MvPolynomial ι R ⧸ I),
      Ideal.Quotient.algebraMap_eq, hf, hg, MvPolynomial.algebraMap_eq, MvPolynomial.map_C,
      MvPolynomial.aeval_C]
  have hker : RingHom.ker f = (RingHom.ker φ).map (algebraMap R (MvPolynomial ι R ⧸ I)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      have h1 : MvPolynomial.map φ p ∈ P₀.ker := by
        rw [Algebra.Generators.ker_eq_ker_aeval_val, RingHom.mem_ker]
        exact hx
      rw [← P₀.span_range_relation_eq_ker] at h1
      have h2 : Ideal.span (Set.range P₀.relation) = I.map (MvPolynomial.map φ) := by
        rw [Ideal.map_span, ← Set.range_comp]
        congr 2
        funext j
        exact (hv j).symm
      rw [h2, Ideal.mem_map_iff_of_surjective _ hmap] at h1
      obtain ⟨q, hq, hqp⟩ := h1
      have h3 : p - q ∈ RingHom.ker (MvPolynomial.map (σ := ι) φ) := by
        rw [RingHom.mem_ker, map_sub, hqp, sub_self]
      rw [MvPolynomial.ker_map] at h3
      have h4 : Ideal.Quotient.mk I p = Ideal.Quotient.mk I (p - q) := by
        rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hq, sub_zero]
      rw [h4, IsScalarTower.algebraMap_eq R (MvPolynomial ι R) (MvPolynomial ι R ⧸ I), ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ h3
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
        RingHom.mem_ker.mp hr, map_zero]
  have hnil : IsNilpotent (RingHom.ker f) := by
    rw [hker]
    exact isNilpotent_map _ hJ
  -- the lifted presentation is submersive
  let P := Algebra.PreSubmersivePresentation.naive (v := v) P₀.map P₀.map_inj
  have hjac : f P.jacobian = P₀.jacobian := by
    rw [P.jacobian_eq_jacobiMatrix_det, P₀.jacobian_eq_jacobiMatrix_det]
    change f (Ideal.Quotient.mk I P.jacobiMatrix.det) = _
    have hM : (MvPolynomial.map φ).mapMatrix P.jacobiMatrix = P₀.jacobiMatrix := by
      refine Matrix.ext fun i j => ?_
      rw [RingHom.mapMatrix_apply, Matrix.map_apply,
        Algebra.PreSubmersivePresentation.jacobiMatrix_naive, ← MvPolynomial.pderiv_map, hv,
        P₀.jacobiMatrix_apply]
    rw [hf, hg, Algebra.Generators.algebraMap_apply, RingHom.map_det, hM]
  have hunit : IsUnit P.jacobian := isUnit_of_map f hfsurj hnil (hjac ▸ P₀.jacobian_isUnit)
  let P' : Algebra.SubmersivePresentation R (MvPolynomial ι R ⧸ I) ι σ := ⟨P, hunit⟩
  have hsm : Algebra.IsStandardSmoothOfRelativeDimension 0 R (MvPolynomial ι R ⧸ I) :=
    ⟨ι, σ, inferInstance, inferInstance, P', hP₀⟩
  have het : Algebra.Etale R (MvPolynomial ι R ⧸ I) :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr hsm
  refine ⟨MvPolynomial ι R ⧸ I, inferInstance, inferInstance, f, het, hfsurj, hker, hcomp, ?_⟩
  intro hfin
  have : Algebra.IsIntegral R (MvPolynomial ι R ⧸ I) := by
    constructor
    intro x
    obtain ⟨p₀, hm₀, hp₀⟩ := (Algebra.IsIntegral.isIntegral (R := R₀) (f x))
    obtain ⟨p, hpm, -, hpmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      ((Polynomial.mem_lifts p₀).mpr (Polynomial.map_surjective φ hφ p₀)) hm₀
    have hpx : Polynomial.aeval x p ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, ← Polynomial.eval₂_map, hpm]
      exact hp₀
    obtain ⟨n, hn⟩ := hnil
    refine ⟨p ^ n, hpmon.pow n, ?_⟩
    rw [Polynomial.eval₂_pow, ← Polynomial.aeval_def]
    have := Ideal.pow_mem_pow hpx n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  exact Algebra.IsIntegral.finite

end RamanujanPetersson.EtPBC.NilLift

end

end

-- ===== S4.Def_RP_EtPBC_A_CovL1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A1a): away maps, localized base change and the reduction map

* `isLocalization_of_isAwayMap`, `isAwayMap_of_isLocalization`, `isAwayMap_comp_equiv`: `IsAwayMap` at a unit is
  `IsLocalization.Away`.
* For `N = B₀[1/t₀]` and a `B₀`-algebra `E₀`, the base change `N ⊗[B₀] E₀` is `E₀[1/t₀]` (Mathlib
  `IsLocalization.Away.tensorRight`, with `Algebra.TensorProduct.rightAlgebra`). Given `f₀ : E₀ → e₀` and
  `g : e₀ → e` with `g τ` a unit, `τ = f₀ t₀`, **`red`** `: N ⊗[B₀] E₀ → e` is the induced map;
  `red_eq`, `red_alg`, **`red_surj`**, **`red_ker`** (`ker red = (ker f₀) · (N ⊗ E₀)` when `g` is an away map).
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Away

end Away

section Red

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B₀ : Type u} (N : Type u) {E₀ e₀ e : Type u} [CommRing B₀] [CommRing N] [CommRing E₀] [CommRing e₀] [CommRing e]
  [Algebra B₀ N] [Algebra B₀ E₀] (t₀ : B₀) [IsLocalization.Away t₀ N]
  (f₀ : E₀ →+* e₀) (g : e₀ →+* e) (τ : e₀) (hτ : f₀ (algebraMap B₀ E₀ t₀) = τ) (hu : IsUnit (g τ))

/-- **The reduction map** `N ⊗[B₀] E₀ = E₀[1/t₀] → e` of `g ∘ f₀`. -/
def red : N ⊗[B₀] E₀ →+* e :=
  IsLocalization.lift (M := Submonoid.powers (algebraMap B₀ E₀ t₀)) (red_units t₀ f₀ g τ hτ hu)

theorem red_eq (x : E₀) : red N t₀ f₀ g τ hτ hu (algebraMap E₀ (N ⊗[B₀] E₀) x) = g (f₀ x) :=
  IsLocalization.lift_eq _ x

theorem red_comp : (red N t₀ f₀ g τ hτ hu).comp (algebraMap E₀ (N ⊗[B₀] E₀)) = g.comp f₀ :=
  RingHom.ext (red_eq N t₀ f₀ g τ hτ hu)

end Red

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAR =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-1b): uniform relations of `p` on the base charts (Artin-Rees)

For `α : Fin g → R` and `ιB : R → B`:
* **`RelV p α ιB n`**: vectors `w` with entries in `p^n B` and `∑ αᵢ wᵢ = 0`; `muB`, `mem_smul_top_pi`, `mem_relV_iff`;
* **`relV_transport`**: a chart-0 relation is `t₀^f` times a chart-1 relation on the overlap `N`;
* **`relV_uniform`** (Artin-Rees, `B₀` noetherian): one bound `F` such that for every `n` the relations `RelV n` are
  `p^(n-n')`-combinations of finitely many relations in `RelV n'` (`n' ≤ n`) whose transition exponents are `≤ F`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section RelV

variable {R : Type u} [CommRing R] (p : Ideal R) {g : ℕ} (α : Fin g → R)

theorem mem_relV_iff {B : Type u} [CommRing B] (ιB : R →+* B) (n : ℕ) (w : Fin g → B) :
    w ∈ RelV p α ιB n ↔
      w ∈ (p.map ιB) ^ n • (⊤ : Submodule B (Fin g → B)) ⊓ LinearMap.ker (muB α ιB) := by
  rw [Submodule.mem_inf, mem_smul_top_pi, LinearMap.mem_ker, ← Ideal.map_pow]
  exact Iff.rfl

end RelV

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As1): base change of the chart data along a flat algebra

* `tmap_id_left`: `map id φ` on `S ⊗[A] B` is `φ.lTensor S`.
* **`away_bc`**: for `S` flat over `A`, `IsAwayMap φ t` gives `IsAwayMap (map id φ) (1 ⊗ t)`.
* `tmul_one_mul_one`: `x * y = 1` gives `(1 ⊗ x) * (1 ⊗ y) = 1`.
* `hat_complete`, `hat_jac`: the completion `Â` is `p Â`-adically complete and `p Â ≤ jacobson ⊥` (`p` f.g.).
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section BC

end BC

section Hat

variable (A : Type u) [CommRing A] (p : Ideal A)

theorem hat_jac (hp : p.FG) :
    p.map (algebraMap A (AdicCompletion p A)) ≤ (⊥ : Ideal (AdicCompletion p A)).jacobson := by
  haveI := hat_complete A p hp
  exact IsAdicComplete.le_jacobson_bot _

end Hat

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As2): the level-0 cover over generic charts, and the fibre kernel

* `eqvG J β hs hk : B ⧸ J ^ (0 + 1) ≃+* F` for `β` surjective with `ker β = J` (`eqvG_mk`), `eqvG_comm`;
* **`baseG`**: a fibre cover `Eᵢ` over `Fᵢ` gives a level-0 two-chart cover `LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ 0`
  (CovL4 `base` with generic ideals);
* **`ker_kap`**: for `χ` surjective and `ker βQ = (ker χ) B`, `ker kap = (ker χ') (R' ⊗ B)`.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section EqvG

theorem eqvG_mk {B F : Type u} [CommRing B] [CommRing F] (J : Ideal B) (β : B →+* F)
    (hs : Function.Surjective β) (hk : RingHom.ker β = J) (b : B) :
    eqvG J β hs hk (Ideal.Quotient.mk _ b) = β b := by
  simp only [eqvG, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem eqvG_comm {B N F Fn : Type u} [CommRing B] [CommRing N] [CommRing F] [CommRing Fn] (φ : B →+* N)
    (J : Ideal B) (JN : Ideal N) (h : J.map φ = JN) (β : B →+* F) (βn : N →+* Fn)
    (hs : Function.Surjective β) (hsn : Function.Surjective βn) (hk : RingHom.ker β = J)
    (hkn : RingHom.ker βn = JN) (φb : F →+* Fn) (hρ : φb.comp β = βn.comp φ) :
    φb.comp (eqvG J β hs hk).toRingHom = (eqvG JN βn hsn hkn).toRingHom.comp (qmap J φ JN h 0) := by
  apply Ideal.Quotient.ringHom_ext
  ext b
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    eqvG_mk, Ideal.quotientMap_mk]
  exact RingHom.congr_fun hρ b

end EqvG

section BaseG

end BaseG

section KerKap

end KerKap

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFl =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-1c): relations on a flat level-`m` chart come from the base (equational criterion)

* `mem_span_mul_fun`: `x ∈ span (range f) * 𝔟` is `∑ fᵢ eᵢ` with `eᵢ ∈ 𝔟`;
* **`flat_rel`**: for `q : B₀ ↠ b` with kernel `(p B₀)^(m+1)` and `E` a flat `b`-algebra, a relation vector `w` of `α` on
  `E` with entries in `p^n E` (`n ≤ m`) is `∑ yκ · rκ + v` with `rκ ∈ RelV p α ιB₀ n` (relations on `B₀` itself)
  and `v` with entries in `p^m E`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Fl

variable {R : Type u} [CommRing R] (p : Ideal R) {g : ℕ} (α : Fin g → R) {B₀ : Type u} [CommRing B₀]
  (ιB₀ : R →+* B₀)

set_option maxHeartbeats 400000 in
/-- **Relations on a flat chart come from the base**, up to entries in `p^m E`. -/
theorem flat_rel [IsNoetherianRing R] (hα : p = Ideal.span (Set.range α)) {b E : Type u} [CommRing b]
    [CommRing E] [Algebra b E] [Module.Flat b E] (q : B₀ →+* b) (hq : Function.Surjective q) (m : ℕ)
    (hk : RingHom.ker q = (p.map ιB₀) ^ (m + 1)) (n : ℕ) (hn : n ≤ m)
    (w : Fin g → E) (hw : ∀ i, w i ∈ (p ^ n).map (((algebraMap b E).comp q).comp ιB₀))
    (hμ : ∑ i, algebraMap b E (q (ιB₀ (α i))) * w i = 0) :
    ∃ (K : ℕ) (y : Fin K → E) (r : Fin K → Fin g → B₀) (v : Fin g → E), (∀ κ, r κ ∈ RelV p α ιB₀ n) ∧
      (∀ i, v i ∈ (p ^ m).map (((algebraMap b E).comp q).comp ιB₀)) ∧
      ∀ i, w i = ∑ κ, y κ * algebraMap b E (q (r κ i)) + v i := by
  obtain ⟨h, π, hπ⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (p ^ n))
  have hπm : ∀ v, π v ∈ p ^ n := fun v => by
    rw [← hπ]
    exact Submodule.subset_span ⟨v, rfl⟩
  have hmap : (p ^ n).map (((algebraMap b E).comp q).comp ιB₀) =
      Ideal.span (Set.range ((((algebraMap b E).comp q).comp ιB₀) ∘ π)) := by
    rw [Set.range_comp, ← Ideal.map_span]
    congr 1
    exact hπ.symm
  have hc : ∀ i, ∃ c : Fin h → E, ∑ v, c v * (((algebraMap b E).comp q).comp ιB₀) (π v) = w i := by
    intro i
    have := hw i
    rw [hmap] at this
    exact Ideal.mem_span_range_iff_exists_fun.1 this
  choose c hc using hc
  obtain ⟨fc, hfc⟩ : ∃ fc : Fin h × Fin g → b, ∀ j, fc j = q (ιB₀ (π j.1 * α j.2)) := ⟨_, fun _ => rfl⟩
  obtain ⟨xc, hxc⟩ : ∃ xc : Fin h × Fin g → E, ∀ j, xc j = c j.2 j.1 := ⟨_, fun _ => rfl⟩
  have hrel : ∑ j, fc j • xc j = 0 := by
    refine Eq.trans ?_ hμ
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [hfc, hxc, Algebra.smul_def, RingHom.comp_apply, map_mul]
    ring
  obtain ⟨K, A, y, hxA, hfA⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := b) (M := E) (f := fc) (x := xc) hrel
  choose Ã hÃ using fun j κ => hq (A j κ)
  obtain ⟨rt, hrt⟩ : ∃ rt : Fin K → Fin g → B₀, ∀ κ i, rt κ i = ∑ v, ιB₀ (π v) * Ã (v, i) κ :=
    ⟨_, fun _ _ => rfl⟩
  have hker : ∀ κ, q (∑ i, ιB₀ (α i) * rt κ i) = 0 := by
    intro κ
    refine Eq.trans ?_ (hfA κ)
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [map_sum, map_mul, hrt, hÃ, Finset.mul_sum, hfc]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hpspan : p.map ιB₀ = Ideal.span (Set.range (ιB₀ ∘ α)) := by
    rw [hα, Ideal.map_span, Set.range_comp]
  have hmem : ∀ κ, ∑ i, ιB₀ (α i) * rt κ i ∈ Ideal.span (Set.range (ιB₀ ∘ α)) * (p.map ιB₀) ^ m := by
    intro κ
    rw [← hpspan, ← pow_succ', ← hk]
    exact RingHom.mem_ker.2 (hker κ)
  choose e he hse using fun κ => mem_span_mul_fun (ιB₀ ∘ α) _ _ (hmem κ)
  have hen : ∀ κ i, e κ i ∈ (p ^ m).map ιB₀ := fun κ i => by
    rw [Ideal.map_pow]
    exact he κ i
  refine ⟨K, y, fun κ i => rt κ i - e κ i, fun i => ∑ κ, y κ * algebraMap b E (q (e κ i)), fun κ => ⟨fun i => ?_, ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · refine Ideal.sub_mem _ ?_ (Ideal.map_mono (Ideal.pow_le_pow_right hn) (hen κ i))
    rw [hrt]
    exact Ideal.sum_mem _ fun v _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hπm v))
  · simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hse κ]
    simp only [Function.comp_apply, sub_self]
  · refine Ideal.sum_mem _ fun κ _ => Ideal.mul_mem_left _ _ ?_
    have := Ideal.mem_map_of_mem ((algebraMap b E).comp q) (hen κ i)
    rw [Ideal.map_map] at this
    exact this
  · have hwi : w i = ∑ κ, y κ * algebraMap b E (q (rt κ i)) := by
      rw [← hc i]
      have e2 : ∀ v, c i v = ∑ κ, algebraMap b E (A (v, i) κ) * y κ := fun v => by
        have := hxA (v, i)
        simp only [hxc, Algebra.smul_def] at this
        exact this
      simp only [e2, hrt, map_sum, map_mul, hÃ, Finset.sum_mul, Finset.mul_sum, RingHom.comp_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      ring
    rw [hwi]
    simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
    ring

end Fl

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs3e =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As3e): residue and base-change facts for the instantiation over `Â`

* **`ker_resHat`**: `ker (resHat χ) = (ker χ) Â` (`A` noetherian); `chi_surj`.
* `kap_surj`: `kap` is surjective when the fibre chart is; **`kap_comm`**: `kap` commutes with the gluing maps.
* `bc_tmul`, **`bc_inc`**: `map id φ` on pure tensors, and it fixes the image of `R'`.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section ResHat

variable (K : Type u) [Field K] (A : Type u) [CommRing A] [Algebra K A]

/-- **The kernel of the residue map of `Â`** is `(ker χ) Â`. -/
theorem ker_resHat [IsNoetherianRing A] (χ : A →ₐ[K] K) :
    RingHom.ker (resHat K A χ) = (RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A)) := by
  have hinj : Function.Injective (Ideal.Quotient.lift (RingHom.ker χ) (χ : A →+* K)
      (fun _ h => RingHom.mem_ker.mp h)) :=
    RingHom.lift_injective_of_ker_le_ideal _ _ (fun _ h => h)
  rw [← AdicCompletion.ker_evalOneₐ_eq_map (I := RingHom.ker χ) (Ideal.fg_of_isNoetherianRing _)]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, resHat_eq, map_eq_zero_iff _ hinj]

end ResHat

section KapA

variable {K A R' B N : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B]
  [CommRing N] [Algebra A N] (χ : A →+* K) (χ' : R' →+* K) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a)

theorem bc_inc (φ : B →ₐ[A] N) :
    (Algebra.TensorProduct.map (AlgHom.id A R') φ : R' ⊗[A] B →+* R' ⊗[A] N).comp
      Algebra.TensorProduct.includeLeftRingHom = Algebra.TensorProduct.includeLeftRingHom :=
  RingHom.ext fun r => by
    rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, bc_tmul, map_one,
      Algebra.TensorProduct.includeLeftRingHom_apply]

/-- **`kap` commutes with the gluing maps** (`φb` is `K`-linear because `χ` is surjective). -/
theorem kap_comm (hχs : Function.Surjective χ) {F Fn : Type u} [CommRing F] [CommRing Fn] [Algebra K F]
    [Algebra K Fn] (β : B →+* F) (βn : N →+* Fn) (hβ : ∀ a, β (algebraMap A B a) = algebraMap K F (χ a))
    (hβn : ∀ a, βn (algebraMap A N a) = algebraMap K Fn (χ a)) (φ : B →ₐ[A] N) (φb : F →+* Fn)
    (hρ : ∀ b, φb (β b) = βn (φ b)) :
    φb.comp (kap χ (algebraMap K F) β hβ χ' hχ') =
      (kap χ (algebraMap K Fn) βn hβn χ' hχ').comp
        (Algebra.TensorProduct.map (AlgHom.id A R') φ : R' ⊗[A] B →+* R' ⊗[A] N) := by
  have hK : ∀ k, φb (algebraMap K F k) = algebraMap K Fn k := fun k => by
    obtain ⟨a, rfl⟩ := hχs k
    rw [← hβ, hρ, AlgHom.commutes, hβn]
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul r b => rw [RingHom.comp_apply, RingHom.comp_apply, bc_tmul, kap_tmul, kap_tmul, map_mul, hK, hρ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end KapA

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAsN1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, AsN1): power series map onto the adic completion

For `a : σ → A` (`σ` finite) and `p = span (range a)`:
* `aeval_monomial_mem_pow`, `aeval_mem_pow_of_coeff`, `mk_aeval_eq`: a polynomial whose coefficients vanish below total
  degree `n` evaluates (at `a`) into `p ^ n`.
* `truncEval a n : MvPowerSeries σ A →+* A ⧸ p ^ n`, `F ↦ mk (aeval a (truncTotal n F))`, `truncEval_compat`.
* **`hatPhi a : MvPowerSeries σ A →+* AdicCompletion p A`**, `evalₐ_hatPhi`, `hatPhi_X`, `hatPhi_C`.
-/

set_option autoImplicit false

open MvPowerSeries

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u v

section HatN1

variable {A : Type u} [CommRing A] {σ : Type v} [Fintype σ] (a : σ → A)

theorem aeval_mem_pow_of_coeff {n : ℕ} (P : MvPolynomial σ A)
    (hP : ∀ x : σ →₀ ℕ, x.degree < n → P.coeff x = 0) :
    MvPolynomial.aeval a P ∈ (Ideal.span (Set.range a)) ^ n := by
  rw [P.as_sum, map_sum]
  refine Ideal.sum_mem _ fun x hx => ?_
  have hx' : n ≤ x.degree := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hx) (hP x (not_le.mp h))
  exact Ideal.pow_le_pow_right hx' (aeval_monomial_mem_pow a x _)

end HatN1

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAsN2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, AsN2): `A⟦X_σ⟧` is precomplete for the ideal of the variables

`Xid σ A = span (range X)`.
* `one_le_order_of_mem_Xid`, `le_order_of_mem_pow`, `coeff_zero_of_mem_Xid_pow`: `F ∈ Xid ^ m` kills coefficients of
  total degree `< m`.
* `mem_Xid_pow_of_coeff` (`σ` finite): the converse (decomposition `F = ∑ X i * G i`).
* `smod_Xid_iff`, **`isPrecomplete_Xid`**: `IsPrecomplete (Xid σ A) (MvPowerSeries σ A)`.
-/

set_option autoImplicit false

open MvPowerSeries

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u v

section HatN2

variable {A : Type u} [CommRing A] {σ : Type v}

theorem one_le_order_of_mem_Xid {F : MvPowerSeries σ A} (hF : F ∈ Xid σ A) :
    ((1 : ℕ) : ℕ∞) ≤ F.order := by
  refine nat_le_order fun d hd => ?_
  have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (Nat.lt_one_iff.mp hd)
  subst hd0
  rw [coeff_zero_eq_constantCoeff_apply]
  have hle : Xid σ A ≤ RingHom.ker (constantCoeff (σ := σ) (R := A)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact constantCoeff_X i
  exact (RingHom.mem_ker).mp (hle hF)

theorem mem_Xid_pow_of_coeff [Fintype σ] : ∀ (m : ℕ) (F : MvPowerSeries σ A),
    (∀ x : σ →₀ ℕ, x.degree < m → coeff x F = 0) → F ∈ (Xid σ A) ^ m
  | 0, F, _ => by simp
  | m + 1, F, hF => by
    classical
    rcases isEmpty_or_nonempty σ with hσ | hσ
    · have hF0 : F = 0 := by
        ext x
        have hx : x = 0 := Finsupp.ext fun i => isEmptyElim i
        rw [hx, map_zero]
        exact hF 0 (by simp)
      rw [hF0]
      exact Ideal.zero_mem _
    · have hex : ∀ α : σ →₀ ℕ, ∃ i : σ, α ≠ 0 → α i ≠ 0 := by
        intro α
        by_cases hα : α = 0
        · exact ⟨Classical.arbitrary σ, fun h => absurd hα h⟩
        · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hα
          exact ⟨i, fun _ => Finsupp.mem_support_iff.mp hi⟩
      choose pick hpick using hex
      obtain ⟨G, hG⟩ : ∃ G : σ → MvPowerSeries σ A, ∀ i β, coeff β (G i) =
          if pick (β + Finsupp.single i 1) = i then coeff (β + Finsupp.single i 1) F else 0 :=
        ⟨fun i β => if pick (β + Finsupp.single i 1) = i then coeff (β + Finsupp.single i 1) F else 0,
          fun _ _ => rfl⟩
      have hXG : ∀ i α, coeff α (X i * G i) =
          if Finsupp.single i 1 ≤ α then (if pick α = i then coeff α F else 0) else 0 := by
        intro i α
        rw [X_def, coeff_monomial_mul]
        by_cases h1 : Finsupp.single i 1 ≤ α
        · rw [if_pos h1, if_pos h1, one_mul, hG, tsub_add_cancel_of_le h1]
        · rw [if_neg h1, if_neg h1]
      have hsum : F = ∑ i, X i * G i := by
        ext α
        rw [map_sum]
        simp_rw [hXG]
        by_cases hα : α = 0
        · subst hα
          rw [hF 0 (by simp)]
          refine (Finset.sum_eq_zero fun i _ => ?_).symm
          rw [if_neg]
          intro h
          simpa using Finsupp.single_le_iff.mp h
        · rw [Finset.sum_eq_single (pick α) (fun b _ hb => by simp [Ne.symm hb])
            (fun h => absurd (Finset.mem_univ _) h)]
          rw [if_pos (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (hpick α hα))), if_pos rfl]
      rw [hsum, pow_succ']
      refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) ?_
      refine mem_Xid_pow_of_coeff m (G i) fun β hβ => ?_
      rw [hG]
      split_ifs
      · exact hF _ (by rw [map_add, Finsupp.degree_single]; omega)
      · rfl

theorem smod_Xid_iff {m : ℕ} (F G : MvPowerSeries σ A) :
    F ≡ G [SMOD ((Xid σ A) ^ m • ⊤ : Submodule (MvPowerSeries σ A) (MvPowerSeries σ A))] ↔
      F - G ∈ (Xid σ A) ^ m := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]

end HatN2

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs3f =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As3f): the completed cover over `Â` from the `CoverLiftAt₂` data

**`hat_lift`**: under the hypotheses of `CoverLiftAt₂` (and `A` noetherian), there are rings `Ê₀, Ê₁, Ê` with
finite etale `Â ⊗ B₀ → Ê₀`, `Â ⊗ B₁ → Ê₁`, glued by away maps over `Â ⊗ N → Ê`, and surjections `θ̂ᵢ : Êᵢ ↠ Eᵢ`
with kernel `(ker χ) Êᵢ`, compatible with `ψᵢ` and with `r ⊗ b ↦ resHat r * βᵢ b`. (`hat_cov` over `R = Â`,
charts `Â ⊗ Bᵢ`, level-0 cover `baseG` with fibre charts `kap`.)
-/

set_option autoImplicit false

open Polynomial TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section AwayA

variable {A B₀ N : Type u} [CommRing A] [CommRing B₀] [Algebra A[X] B₀] [Algebra A B₀] [IsScalarTower A A[X] B₀]
  [CommRing N] [Algebra A[X] N] [Algebra A N] [IsScalarTower A A[X] N] (φ₀ : B₀ →ₐ[A[X]] N)

theorem hts_hat {B₁ : Type u} [CommRing B₁] [Algebra A[X] B₁] [Algebra A B₁] (φ₁ : B₁ →ₐ[A] N) (S : Type u)
    [CommRing S] [Algebra A S] (hX : algebraMap A[X] N X * φ₁ (algebraMap A[X] B₁ X) = 1) :
    (Algebra.TensorProduct.map (AlgHom.id A S) (φ₀.restrictScalars A) : S ⊗[A] B₀ →+* S ⊗[A] N)
        ((1 : S) ⊗ₜ[A] algebraMap A[X] B₀ X) *
      (Algebra.TensorProduct.map (AlgHom.id A S) φ₁ : S ⊗[A] B₁ →+* S ⊗[A] N)
        ((1 : S) ⊗ₜ[A] algebraMap A[X] B₁ X) = 1 := by
  rw [bc_tmul, bc_tmul, AlgHom.restrictScalars_apply, AlgHom.commutes]
  exact tmul_one_mul_one hX

end AwayA

section HatLift

end HatLift

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs5a =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As5a): lifting polynomials and memberships to a f.g. subalgebra

For a flat `A`-algebra `S` and an `A`-algebra `B`, with `tvC B C : C ⊗ B → S ⊗ B` and, for `C ≤ D`,
`tiC B h : C ⊗ B → D ⊗ B`:
* `exists_lift_polys`: finitely many polynomials over `S ⊗ B` come from one f.g. `C`;
* `exists_lift_monic`: a monic polynomial over `S ⊗ B` comes from a monic one over `C ⊗ B`;
* **`desc_mem`**: finitely many ideal memberships `x_k ∈ (g)` over `S ⊗ B` already hold over `C ⊗ B` for a f.g.
  `C ≥ C₀` (cofactors lifted by `exists_lift_polys`, the identities descended by `desc_mvPoly`).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section Lift

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]

/-- `C ⊗ B → D ⊗ B` for `C ≤ D`. -/
abbrev tiC (B : Type u) [CommRing B] [Algebra A B] {C D : Subalgebra A S} (h : C ≤ D) :
    C ⊗[A] B →+* D ⊗[A] B :=
  (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A B)).toRingHom

end Lift

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovPr16 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3p): the residue `θh` of a descended presentation from a chart `E` (generic)

* `presCongr h : Pres g₁ ≃ₐ[P] Pres g₂` for `h : g₁ = g₂` (`presCongr_mk`);
* **`ker_comp_algEquiv`**: `ker (θ ∘ e) = I · X` when `ker θ = I · Y` and `e : X ≃ₐ[P] Y`;
* `surj_comp_algEquiv`, `comp_algEquiv_algebraMap`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Gen

variable {P : Type u} [CommRing P] {r : ℕ}

theorem presCongr_mk {g₁ g₂ : Fin r → MvPolynomial (Fin r) P} (h : g₁ = g₂) (x : MvPolynomial (Fin r) P) :
    presCongr h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x :=
  rfl

end Gen

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3Res =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 2: chart conditions from affine opens and finite morphisms

* `res_away_surj`, `res_away_zero`: for an affine open `U`, `f ∈ Γ(X, U)` and `W = D(f)`, the restriction
  `Γ(X, U) → Γ(X, W)` satisfies the two localization conditions of `exists_etale_idem_of_loc`
  (Mathlib `IsAffineOpen.isLocalization_basicOpen`).
* `finite_app_of_surj`: for `π` finite and `U` affine, `Γ(Y, U) → Γ(X, π⁻¹ U)` stays finite after precomposing
  with a surjection `R ↠ Γ(Y, U)` (e.g. `A[t] ↠ Γ(P_A, Q₀)`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

open RamanujanPetersson.EtPBC.Z2

universe u

variable {X : Scheme.{u}}

theorem res_away_surj {U W : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) (hW : W = X.basicOpen f)
    (hWU : W ≤ U) (y : Γ(X, W)) :
    ∃ (k : ℕ) (a : Γ(X, U)), X.presheaf.map (homOfLE hWU).op f ^ k * y = X.presheaf.map (homOfLE hWU).op a := by
  subst hW
  have := hU.isLocalization_basicOpen f
  exact away_surj f y

theorem res_away_zero {U W : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) (hW : W = X.basicOpen f)
    (hWU : W ≤ U) (a : Γ(X, U)) (ha : X.presheaf.map (homOfLE hWU).op a = 0) : ∃ k : ℕ, f ^ k * a = 0 := by
  subst hW
  have := hU.isLocalization_basicOpen f
  exact away_zero f a ha

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4Base =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`

* `isoSpec_inv_appTop'`, `eq_Spec_map` (a morphism `Spec R ⟶ V`, `V` affine, is `Spec` of its ring map).
* `pushout_inl_surj`, `pushout_inl_ker`: in a pushout of commutative rings along a surjection `g : A ↠ C`, the map
  `inl : B → P` is surjective with kernel `(ker g) B`.
* `hV V R' : Spec R' ⟶ V`, `hV_appTop`; `YV K gV π R' = Y ×_V Spec R'` with its `Γ(V)`-algebra structure `algYV`;
  `fR : R' →ₐ Γ(Y_{V'}, ⊤)`, `gS : secAlg →ₐ Γ(Y_{V'}, ⊤)`, **`PhiY = lift fR gS`**; `isClopen_PhiY`: for an
  idempotent `e'` of `R' ⊗ secAlg`, `D(PhiY e')` is clopen.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

/-- A morphism `Spec R ⟶ V` to an affine scheme is `Spec` of its ring map. -/
theorem eq_Spec_map {V : Scheme.{u}} [IsAffine V] {R : CommRingCat.{u}} (x : Spec R ⟶ V) :
    x = Spec.map (x.appTop ≫ (Scheme.ΓSpecIso R).hom) ≫ V.isoSpec.inv := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, isoSpec_inv_appTop', ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

theorem hV_appTop (V : Scheme.{u}) [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R'] :
    (hV V R').appTop =
      CommRingCat.ofHom (algebraMap Γ(V, ⊤) R') ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv := by
  rw [hV, Scheme.Hom.comp_appTop, isoSpec_inv_appTop', Scheme.ΓSpecIso_inv_naturality]
  rfl

section Base

end Base

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4FibB =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`

* `ψx K x : Γ(V) → K`, `px K x = ker ψx` (prime), `ker_appTop_eq`, `κx : κ(p) → K`, `κx_algebraMap`.
* For `P` over `p` with `κ(p) ≅ κ(P)` (`hbij`): `χx : R' → K`, `χx_algebraMap`, **`hxχ`**:
  `Spec χx ≫ hV V R' = x`, `xχ_appTop`.
* **`yxMap K gV π R' x x' hx' : Y_x ⟶ Y ×_V Spec R'`**, `yxMap_fR`, `yxMap_gS`, `yxMap_PhiY_tmul`.
* `exists_fibreRing`: a ring map `κ(p) ⊗ Γ(Y, U) → Γ(Y_x, fx⁻¹ U)`, `c ⊗ b ↦ c · fx^* b`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

section Res

variable (K : Type u) [Field K] {V : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ V)

/-- The prime `p = ker ψx`. -/
abbrev px : Ideal Γ(V, ⊤) := RingHom.ker (ψx K x)

instance px_isPrime : (px K x).IsPrime := RingHom.ker_isPrime _

end Res

section Map

end Map

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_CovCh =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`

For `V` affine, `π : Y ⟶ P¹_V` finite, a `K`-point `x` of `V` and a finite etale `q : T ⟶ Y_x`, the charts
`Γ(Y_x, fx⁻¹ Yᵢ)` and `Γ(T, q⁻¹ fx⁻¹ Yᵢ)` satisfy every hypothesis of `CoverLiftAt`. **`nonempty_liftD`**: under
`CoverLiftAt K Γ(V) χ` (`χ` the point `x`), the lift data `LiftD` (= `CoverLift` at these charts) exist.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ V)

/-- The `K`-point `x` as a `K`-algebra map `Γ(V) → K`. -/
def χV (hx : x ≫ gV = 𝟙 _) : @AlgHom K Γ(V, ⊤) K _ _ _ (algKV K gV) _ :=
  @AlgHom.mk K Γ(V, ⊤) K _ _ _ (algKV K gV) _ (ψx K x) (fun c => by
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (x.appTop.hom (gV.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))) = c
    rw [gx_appTop K gV x hx]
    exact congrArg (fun φ => CommRingCat.Hom.hom φ c) (Iso.inv_hom_id (Scheme.ΓSpecIso (CommRingCat.of K))))

section Cover

end Cover

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Inj0a =====
section

/-!
# S4-EtPBC-A, G1a: germs of a pulled-back section control the support

For `f : X ⟶ Y`, a geometric point `s` of `X`, a sheaf `G` on `Y`, `V : Y.Etale`, a fibre point `b` of `s` over
`f⁻¹ V` and `z ∈ G(V)`:
* `cpt f s b : V.left`, the point of `V` under `b`; `cpt_map` (naturality in `V`);
* **`comap_germ_eq_zero`**: if the germ of `η_G(z) ∈ (f^* G)(f⁻¹ V)` at `b` vanishes, so does the germ of `z` at `b`
  for the point `comapPt f s` of `Y` (Mathlib's stalk isomorphism `(f^* G)_s ≅ G_{s ≫ f}`, `comapIso_hom_app`);
* `exists_nbhd_of_comap_germ`: such a germ vanishes on an etale neighbourhood;
* **`cpt_not_mem_supp`**: then `cpt b` is not in the support `supp G z`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeomPt X)

/-- **Germs of `η_G(z)` control the germs of `z` at `comapPt f s`.** -/
theorem comap_germ_eq_zero (G : EtSh Λ Y) {V : Y.Etale} (b : (comapPt f s).fiber.obj V) (z : G.obj.obj (op V))
    (h : (s.point.toPresheafFiber ((etPull f).obj V) b ((pull f Λ).obj G).obj).hom
      ((((pullAdj f Λ).unit.app G).hom.app (op V)).hom z) = 0) :
    ((comapPt f s).toPresheafFiber V b G.obj).hom z = 0 := by
  have e := germ_unit_pushFib Λ f s G V b
  have e2 := comapIso_hom_app Λ f s G
  have hiso : IsIso ((comapPt f s).sheafFiber.map ((pullAdj f Λ).unit.app G) ≫ pushFib Λ f s ((pull f Λ).obj G)) := by
    rw [← e2]
    infer_instance
  have hinj : Function.Injective
      ((comapPt f s).sheafFiber.map ((pullAdj f Λ).unit.app G) ≫ pushFib Λ f s ((pull f Λ).obj G)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have e' := congrArg (fun φ => φ.hom z) e
  apply hinj
  refine (e'.trans h).trans ?_
  exact (LinearMap.map_zero _).symm

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_Xi =====
section

/-!
# S4-EtPBC-A, M2 F5: the germ `ξ_s(b)` of a section of a pullback

For `f : X ⟶ Y`, a geometric point `s` of `X`, a sheaf `G` on `Y` and `b : Λ_X ⟶ f^* G`:
* **`pullStalkIso_germ`**: the stalk isomorphism `(f^* G)_s ≅ G_{s ≫ f}` sends the germ of `η_G(z)` at `b'` to the germ
  of `z` at the corresponding fibre point of `s ≫ f`;
* `xi f s G b ∈ G_{s ≫ f}`: the image of the germ of `b(1)`; `xi_sub`, `germ_eq_zero_of_xi`;
* **`xi_bc`**: for `f = ι : P_s ⟶ P`, `ξ(u_v ≫ ι^* φ)` is the germ of `φ(1)` at the neighbourhood point.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

section Xi

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeomPt X)

/-- **Germs of `η_G(z)` under the stalk isomorphism of a pullback.** -/
theorem pullStalkIso_germ (G : EtSh Λ Y) (W : Y.Etale) (b : (comapPt f s).fiber.obj W) (z : G.obj.obj (op W)) :
    ((pullStalkIso f Λ s).hom.app G).hom
      ((s.point.toPresheafFiber ((etPull f).obj W) b ((pull f Λ).obj G).obj).hom
        ((((pullAdj f Λ).unit.app G).hom.app (op W)).hom z)) =
    ((s.map f).point.toPresheafFiber W ((fiberMapIso f s).inv.app W b) G.obj).hom z := by
  have e' : ((s.point.sheafFiberComapIso (etPull f) (etPull_coverPreserving f) (ModuleCat.{u} Λ)).hom.app G).hom
      (((comapPt f s).toPresheafFiber W b G.obj).hom z) =
      (s.point.toPresheafFiber ((etPull f).obj W) b ((pull f Λ).obj G).obj).hom
        ((((pullAdj f Λ).unit.app G).hom.app (op W)).hom z) := by
    rw [comapIso_hom_app]
    exact ConcreteCategory.congr_hom (germ_unit_pushFib Λ f s G W b) z
  have hinv := ConcreteCategory.congr_hom (Iso.hom_inv_id_app
    (s.point.sheafFiberComapIso (etPull f) (etPull_coverPreserving f) (ModuleCat.{u} Λ)) G)
    (((comapPt f s).toPresheafFiber W b G.obj).hom z)
  rw [← e']
  refine (congrArg ((comapPtIso f s).hom.presheafFiber.app G.obj).hom hinv).trans ?_
  exact ConcreteCategory.congr_hom (germ_comapPtIso f s G.obj W b) z

end Xi

section XiBC

end XiBC

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_VLoc =====
section

/-!
# S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`

For `ι : X ⟶ P`, `π : Y ⟶ P`, `C = constSh Λ Y M`, `b : Λ_X ⟶ ι^* π_* C` and a separably closed `Ω`:
* `sigPt τ`: the geometric point `τ ≫ π_s` of `X` for `τ : Spec Ω ⟶ Y ×_P X`; `xMor τ`: the `Ω`-point of the fibre
  `fib π (τ ≫ π_s ≫ ι)` given by `τ`;
* `vval b τ := psi (ξ_{sigPt τ}(b)) (xMor τ)`, the value of `b` at `τ`;
* `kap h`: for a local representation `h : U ⟶ ι⁻¹ W`, the map `(Y ×_P X) ×_X U ⟶ π⁻¹ W`;
* **`vval_of_lift`**: along a local representation, `vval b τ = cval z (kap h (l pt))` for any lift `l` of `τ`;
* **`vval_locConst`**: `vval b` is locally constant: every `τ` has an open neighbourhood `N` of its point such that
  `vval b τ' = vval b τ` for all `τ'` with point in `N`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

variable {Λ : Type u} [CommRing Λ] {X P Y : Scheme.{u}} (ι : X ⟶ P) (π : Y ⟶ P) {M : ModuleCat.{u} Λ}
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]

theorem xPt_cond (τ : Spec (CommRingCat.of Ω) ⟶ pullback π ι) :
    (τ ≫ pullback.fst π ι) ≫ π = 𝟙 _ ≫ ((sigPt ι π τ).map ι).pt := by
  show (τ ≫ pullback.fst π ι) ≫ π = 𝟙 _ ≫ ((τ ≫ pullback.snd π ι) ≫ ι)
  rw [Category.id_comp, Category.assoc, Category.assoc, pullback.condition]

theorem lift_cond {U : X.Etale} (τ : Spec (CommRingCat.of Ω) ⟶ pullback π ι)
    (l : Spec (CommRingCat.of Ω) ⟶ pullback (pullback.snd π ι) U.hom) (hl : l ≫ pullback.fst _ _ = τ) :
    (l ≫ pullback.snd (pullback.snd π ι) U.hom) ≫ U.hom = (sigPt ι π τ).pt := by
  show (l ≫ pullback.snd (pullback.snd π ι) U.hom) ≫ U.hom = τ ≫ pullback.snd π ι
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, hl]

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_VPart =====
section

/-!
# S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values

* `vval_locConst₂`: `vval_locConst` with test points over any separably closed field;
* `vv b q := vval b (geomPtAt q).pt`, **`vval_eq_vv`** (`vval b τ = vv b (τ pt)`), **`isLocallyConstant_vv`**;
* `fibInc σ : fib π (σ ≫ ι) ⟶ Y ×_P X` and **`psi_xi_eq_vval`**: `Ψ(ξ_σ b)(x) = vval b (x̄ ≫ fibInc σ)`;
* `ysj j : Y ×_P P_s ⟶ Y ×_P P_V` and **`vval_bc`**: the value of a base-changed class is `cval z ∘ ysj j`;
* **`bc_eq_of_vv`**: a section `z` over `Y ×_P P_V` with `cval z ∘ ysj j = vv b` gives `bc z = b`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

section Gen

variable {Λ : Type u} [CommRing Λ] {X P Y : Scheme.{u}} (ι : X ⟶ P) (π : Y ⟶ P) {M : ModuleCat.{u} Λ}

/-- The map `fib π (σ ≫ ι) ⟶ Y ×_P X`. -/
def fibInc (σ : GeomPt X) : fib π (σ.map ι) ⟶ pullback π ι :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ σ.pt) (fibInc_cond ι π σ)

end Gen

section BC

end BC

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_NbExt1 =====
section

/-!
# S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods

Plain-morphism version: a neighbourhood is given by `hj : V ⟶ S` and `v : Spec Ω ⟶ V` with `v ≫ hj = s.pt`.
* `pMapV : V ×_S P ≅ P¹_V`, `piVV : Y_V ⟶ P¹_V` (finite), `xV = (s ≫ g_K)⁻¹ ≫ v : Spec K ⟶ V`;
* `fibV : P_s ⟶ V ×_S P`, `ysV : Y_s ⟶ Y_V` (definitionally `ysj` for a `Nbhd`);
* `eYV : Y_s ⟶ Y_x` and `eY'V : Y_x ⟶ Y_s` with **`eYV_eY'V`** (`eYV ≫ eY'V = 𝟙`);
* for an etale `Γ(V)`-algebra `R'` and a lift `x'` of `xV`: `kapV : Y_{V'} ⟶ Y ×_V Spec R'` with
  **`ysV_kapV`**: `ysV' ≫ kapV = eYV ≫ yxMap`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {S : Scheme.{u}} (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S) {Y : Scheme.{u}} {V : Scheme.{u}} (hj : V ⟶ S)

variable [IsIso (s.pt ≫ gK)] (v : Spec (CommRingCat.of s.Ω) ⟶ V)

section Ext

variable [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

variable (x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R')) (v' : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of R'))

theorem hv'_of (hx' : x' ≫ hV V R' = xV K gK s v) (hvx : (s.pt ≫ gK) ≫ x' = v') : v' ≫ hV V R' = v := by
  rw [← hvx, Category.assoc, hx', xV, IsIso.hom_inv_id_assoc]

theorem hvR (hv' : v' ≫ hV V R' = v) (hv : v ≫ hj = s.pt) : v' ≫ hV V R' ≫ hj = s.pt := by
  rw [reassoc_of% hv', hv]

end Ext

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG1 =====
section

/-!
# S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart

For a short exact sequence `0 → F →a E →b Q → 0` of etale sheaves on `X`, an etale `V` and `e ∈ E(V)` whose
restrictions along any two maps `W ⟶ V` have the same image in `Q`:
* `dif a b hab hS e he W w₁ w₂ ∈ F(W)` with `a (dif) = w₁^* e - w₂^* e` (`f_dif`, unique: `dif_eq`);
  `dif_self`, `dif_add` (cocycle), `dif_map` (naturality); `he_of_glob` (the hypothesis from a global section).
* Charts: `σ : Spec A ⟶ X` etale, `τ : Spec C ⟶ V` over `σ` (`hτ`), `C` etale over `A`. `etS σ R` (= `Spec R` as
  an etale `X`-object for an etale `A`-algebra `R`), `homS σ φ`, `kmap σ τ hτ φ : etS σ R ⟶ V`, `homS_kmap`,
  `cval_comap`.
* For `F = M_X` (`M` finite): `cU` (the values of `dif` on `Spec (C ⊗[A] C)`), `cU_diag`, `cU_coc`, and
  **`datU : Datum A C M`** (`DescB.mkDatum`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Dif

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} {F E Q : EtSh Λ X} (a : F ⟶ E) (b : E ⟶ Q)
  (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) {V : X.Etale} (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

include he in
theorem g_difX (W : X.Etale) (w₁ w₂ : W ⟶ V) : (b.hom.app (op W)).hom (difX e W w₁ w₂) = 0 := by
  rw [difX, map_sub, he W w₁ w₂, sub_self]

/-- The difference cocycle: `a (dif w₁ w₂) = w₁^* e - w₂^* e`. -/
def dif (W : X.Etale) (w₁ w₂ : W ⟶ V) : F.obj.obj (op W) :=
  (sec_exact hS W (difX e W w₁ w₂) (g_difX b e he W w₁ w₂)).choose

end Dif

section Chart

instance etale_tensor₃ (A C : Type u) [CommRing A] [CommRing C] [Algebra A C] [Algebra.Etale A C] :
    Algebra.Etale A (C ⊗[A] (C ⊗[A] C)) :=
  Algebra.Etale.comp A C (C ⊗[A] (C ⊗[A] C))

end Chart

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG2 =====
section

/-!
# S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens

* Cross-chart maps `homX σ σ' ρA hσ φ hφ : etS σ' R' ⟶ etS σ R` (for `Spec ρA ≫ σ = σ'`), `homX_kmap`,
  `cval_comapX`; **`datU_compat`**: `psiMap ρA φC hφC (datU ...).ε m = (datU' ...).ε m`.
* On affine opens `U` of `X` (for `V` etale over `X` with `V.hom` affine): `CU V U = Γ(V, V.hom⁻¹ U)` as an etale
  `Γ(X, U)`-algebra, the chart datum `datA`, restriction maps `mapU`, the functor
  **`FU : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat`**, `alphaU : 𝒪_X ⟶ FU` and **`coequifibered_alphaU`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Cross

end Cross

section Pres

end Pres

section Glue

variable {X : Scheme.{u}}

instance (V : X.Etale) (U : X.AffineZariskiSite) : CommRing (CU V U) :=
  inferInstanceAs (CommRing Γ(V.left, V.hom ⁻¹ᵁ U.1))

instance (V : X.Etale) (U : X.AffineZariskiSite) : Algebra Γ(X, U.1) (CU V U) :=
  (V.hom.app U.1).hom.toAlgebra

variable (V : X.Etale) [IsAffineHom V.hom]

/-- The chart `Spec (CU V U) ⟶ V`. -/
def tauU (U : X.AffineZariskiSite) : Spec (CommRingCat.of (CU V U)) ⟶ V.left :=
  (U.2.preimage V.hom).fromSpec

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M] {E Q : EtSh Λ X}
  (a : constSh Λ X M ⟶ E) (b : E ⟶ Q) (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact)
  (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

/-- Restriction `CU V U → CU V U'`. -/
abbrev phiV {U U' : X.AffineZariskiSite} (h : U'.1 ≤ U.1) : CU V U →+* CU V U' :=
  (V.left.presheaf.map (homOfLE (Scheme.Hom.preimage_mono V.hom h)).op).hom

end Glue

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG3 =====
section

/-!
# S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective

* Generic (any coequifibered `α : 𝒪_X ⟶ F` on affine opens): `glD H` (the relative gluing data),
  `cover_toBase` (`Spec F(U) ⟶ U₀ ⟶ X` is `Spec α_U ≫ U.fromSpec`), `prop_toBase` (a Zariski-local property holds
  for `toBase` once it holds for every `Spec α_U`), `isFinite_toBase`, `etale_toBase`, `surjective_toBase`.
* For `V` etale and surjective over `X` with `V.hom` affine: `surj_comap`, the instance
  `Module.FaithfullyFlat Γ(X, U) (CU V U)`, and for the descended presheaf `FU`:
  **`U0`**, **`toU0`** `: U0 ⟶ X` with `IsFinite`, `Etale`, `Surjective`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Base

variable {X : Scheme.{u}} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)

instance glD_isLocallyDirected : ((glD H).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

theorem cover_toBase (U : X.AffineZariskiSite) :
    (glD H).cover.f U ≫ (glD H).toBase = Spec.map (α.app (op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency.types false in
theorem toBase_preimage (U : X.affineOpens) :
    (glD H).toBase ⁻¹ᵁ U = ((glD H).cover.f U).opensRange := by
  simpa using! (glD H).toBase_preimage_eq_opensRange_ι U

end Base

section Cover

end Cover

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_NbExt2 =====
section

/-!
# S4-EtPBC-A, M2 F8a: extending a clopen of `Y_s` to an etale neighbourhood

* `ysj_map`: `ysj j' ≫ (restriction along a : j' ⟶ j) = ysj j`;
* `etale_hV`, `nbR` (the neighbourhood `Spec R' ⟶ V ⟶ S` through `x'`), `nbRHom : nbR ⟶ j`;
* **`exists_clopen_nbhd`**: for an affine noetherian neighbourhood `j` and a clopen `O ⊆ Y_s` there is an affine
  noetherian `j' ⟶ j` and a clopen `C ⊆ Y_{j'}` with `ysj j' ⁻¹' C = O`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

universe u

section Map

end Map

theorem etale_hV (V : Scheme.{u}) [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']
    [Algebra.Etale Γ(V, ⊤) R'] : Etale (hV V R') := by
  unfold hV
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(V, ⊤) R'))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2 inferInstance)
  infer_instance

section Nbhd

end Nbhd

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FBCv =====
section

/-!
# S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre

For `π : Y ⟶ P` finite, a geometric point `t` of `P`, a neighbourhood `j` of `t` and any `v : π⁻¹(j) → M`, after
refining `j` there is a section `z` of `M_Y` over `π⁻¹(j')` whose values along the fibre `fib π t` are those of `v`.
* `PhiU`: `R' ⊗_{Γ(W)} Γ(U) → Γ(U')` for a square `U' → U → W`, `U' → Spec R' → W`; `comap_PhiU_left/right`;
* `exists_sec_vals_aff` (affine `j`), **`exists_sec_vals`** (Stacks 00UL via
  `Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.FBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.Z3

universe u

section Phi

variable {W U U' : Scheme.{u}} [IsAffine W] (g : U ⟶ W) (R' : Type u) [CommRing R'] [Algebra Γ(W, ⊤) R']
  (f₁ : U' ⟶ Spec (CommRingCat.of R')) (f₂ : U' ⟶ U) [Algebra Γ(W, ⊤) Γ(U, ⊤)] [Algebra Γ(W, ⊤) Γ(U', ⊤)]

/-- `Γ(U, ⊤) → Γ(U', ⊤)` along `f₂`. -/
def gEU (hg : algebraMap Γ(W, ⊤) Γ(U, ⊤) = g.appTop.hom)
    (h' : algebraMap Γ(W, ⊤) Γ(U', ⊤) = (f₁ ≫ hV W R').appTop.hom) (hf : f₂ ≫ g = f₁ ≫ hV W R') :
    Γ(U, ⊤) →ₐ[Γ(W, ⊤)] Γ(U', ⊤) where
  toRingHom := f₂.appTop.hom
  commutes' a := by
    show f₂.appTop.hom (algebraMap Γ(W, ⊤) Γ(U, ⊤) a) = algebraMap Γ(W, ⊤) Γ(U', ⊤) a
    rw [hg, h', ← hf, Scheme.Hom.comp_appTop]
    rfl

end Phi

section Main

end Main

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FBCa =====
section

/-!
# S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values

* `cval_uC`: values of `uC g M : M_X ⟶ g_* M_Y` (the section pulled back to `V ×_X Y`);
* `muU h Φ V : V ×_P U₁ ⟶ V ×_P U₂`, `kapU` (the same into `(V ×_P U₂) ×_{U₂} U₁`), `kapU_nat`;
* **`rU h Φ M : Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}`** with **`cval_rU`** (`cval (rU z) w = cval z (muU w)`);
* `nuU h Φ t : fib (h ≫ Φ) t ⟶ fib Φ t`, `muU_fibToNbhd`, **`cval_rU_fib`**;
* `muU_injective` for a closed immersion `h`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.FBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.SgUnit

universe u

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

section RU

variable {U₁ U₂ P : Scheme.{u}} (h : U₁ ⟶ U₂) (Φ : U₂ ⟶ P)

@[reassoc]
theorem muU_fst (V : P.Etale) : muU h Φ V ≫ pullback.fst V.hom Φ = pullback.fst V.hom (h ≫ Φ) :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem muU_snd (V : P.Etale) : muU h Φ V ≫ pullback.snd V.hom Φ = pullback.snd V.hom (h ≫ Φ) ≫ h :=
  pullback.lift_snd _ _ _

/-- The underlying map of `kapU`. -/
def kapL (V : P.Etale) : pullback V.hom (h ≫ Φ) ⟶ pullback (pullback.snd V.hom Φ) h :=
  pullback.lift (muU h Φ V) (pullback.snd _ _) (muU_snd h Φ V)

end RU

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_T3dA =====
section

/-!
# S4-EtPBC-A, R4-T3d (part A): classes as extensions, and the kill by an extension

* `sesPb`: pulling the injective presentation `0 → A → I → I/A → 0` back along `x : X ⟶ I/A`;
* **`exists_ses_extClass`**: every `β ∈ Ext¹(X, A)` is the class of a short exact `0 → A → E → X → 0`;
* **`exists_bc_of_ses_kill`**: for `f : P' ⟶ P` etale with a closed lift `ι'` of the fibre inclusion, `Φ : U ⟶ P'`
  finite and a mono `m : f^* G ⟶ Φ_* M_U`, the class of an extension `0 → ι^* G →a E → Λ → 0` on `P_s` is a germ
  as soon as `(ι^* G ⟶ ι'^* f^* G ⟶ ι'^* Φ_* M_U ≅ φs_* M_{U_s})` extends along `a`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.T3d

universe w v₁ u₁

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

section Pb

variable {A I Q X : C} (i : A ⟶ I) (p : I ⟶ Q) (x : X ⟶ Q)

/-- The map from the pulled-back complex to `A ⟶ I ⟶ Q`. -/
def sesPbMap (hip : i ≫ p = 0) : sesPb i p x hip ⟶ ShortComplex.mk i p hip where
  τ₁ := 𝟙 A
  τ₂ := pullback.fst p x
  τ₃ := x
  comm₁₂ := by
    simp only [sesPb, Category.id_comp]
    exact (pullback.lift_fst _ _ _).symm
  comm₂₃ := by
    exact pullback.condition (f := p) (g := x)

theorem sesPb_shortExact (hip : i ≫ p = 0) (h : (ShortComplex.mk i p hip).ShortExact) :
    (sesPb i p x hip).ShortExact := by
  have hmi : Mono i := h.mono_f
  have hep : Epi p := h.epi_g
  have hm : Mono (sesPb i p x hip).f := ⟨fun u v huv => by
    have h1 := eq_whisker huv (pullback.fst p x)
    simp only [Category.assoc, pullback.lift_fst] at h1
    exact hmi.right_cancellation u v h1⟩
  have he : Epi (sesPb i p x hip).g := by
    change Epi (pullback.snd p x)
    infer_instance
  refine ShortComplex.ShortExact.mk' ?_ hm he
  refine ShortComplex.exact_of_f_is_kernel _ ?_
  refine KernelFork.IsLimit.ofι _ _
    (fun {W'} k hk => h.exact.lift (k ≫ pullback.fst p x) ?_) ?_ ?_
  · have hk' : k ≫ pullback.snd p x = 0 := hk
    change (k ≫ pullback.fst p x) ≫ p = 0
    rw [Category.assoc, pullback.condition, ← Category.assoc, hk', zero_comp]
  · intro W' k hk
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact h.exact.lift_f _ _
    · have hk' : k ≫ pullback.snd p x = 0 := hk
      rw [Category.assoc, pullback.lift_snd, comp_zero, hk']
  · intro W' k hk n hn
    apply hmi.right_cancellation
    rw [h.exact.lift_f, ← hn, Category.assoc]
    exact congrArg (n ≫ ·) (pullback.lift_fst _ _ _).symm

end Pb

end Abstract

section Geo

open AlgebraicGeometry RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.PushKill RamanujanPetersson.EtPBC.FBC

universe u

end Geo

end RamanujanPetersson.EtPBC.T3d

end

end

-- ===== S4.Def_RP_EtPBC_A_T3dB =====
section

/-!
# S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`

* `isClosedImmersion_of_isIso_comp`: a point `σ : Spec Ω ⟶ V` with `σ ≫ gV` an isomorphism is a closed immersion;
* `sec_ext_cval`: sections of a constant sheaf are determined by their values;
* `rUq`, `cval_rUq`: restriction along a commutative triangle; `cval_pushCompIso_inv`;
* `resAdj_symm_app`, `mR_app`, `cval_mR`: the transpose `mR` on sections and values (kernel-cheap: generic lemmas);
* `mS : π_* M_Y ⟶ f_* Φ_* M_U` (restriction along `h : U ⟶ Y`, `h ≫ π = Φ ≫ f`), `mP := (f^* ⊣ f_*)`-adjoint;
* **`mono_mP`**: for `f` etale and `U ⟶ P' ×_P Y` surjective, `mP : f^* π_* M_Y ⟶ Φ_* M_U` is a monomorphism.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.T3d

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.FBC

universe u

section Geo0

end Geo0

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

section RUq

end RUq

section M

variable {P P' Y U : Scheme.{u}} (π : Y ⟶ P) (f : P' ⟶ P) (Φ : U ⟶ P') (h : U ⟶ Y) (hh : h ≫ π = Φ ≫ f)

variable [Etale f]

theorem thU_fst (W : P'.Etale) :
    thU π f Φ h hh W ≫ pullback.fst ((etComp f).obj W).hom π = pullback.fst W.hom Φ := by
  have k1 := muq_fst h π (Φ ≫ f) hh ((etComp f).obj W)
  have k2 := etPullCompIso_inv_fst Φ f ((etComp f).obj W)
  have k3 := etPull_map_left_fst_assoc Φ ((etCompAdj f).unit.app W) (pullback.fst ((etComp f).obj W).hom f)
  have k4 := etCompAdj_unit_fst f W
  exact (Category.assoc _ _ _).trans <|
    (whisker_eq _ ((Category.assoc _ _ _).trans (whisker_eq _ k1))).trans <|
      (whisker_eq _ k2).trans <| k3.trans <| (whisker_eq _ k4).trans (Category.comp_id _)

theorem thU_snd (W : P'.Etale) :
    thU π f Φ h hh W ≫ pullback.snd ((etComp f).obj W).hom π = pullback.snd W.hom Φ ≫ h := by
  have k1 := muq_snd h π (Φ ≫ f) hh ((etComp f).obj W)
  have k2 := etPullCompIso_inv_snd_assoc Φ f ((etComp f).obj W) h
  have k3 := etPull_map_left_snd_assoc Φ ((etCompAdj f).unit.app W) h
  exact (Category.assoc _ _ _).trans <|
    (whisker_eq _ ((Category.assoc _ _ _).trans (whisker_eq _ k1))).trans <|
      (whisker_eq _ k2).trans k3

theorem thU_surjective (hs : Function.Surjective ⇑(pullback.lift Φ h hh.symm : U ⟶ pullback f π))
    (W : P'.Etale) : Function.Surjective ⇑(thU π f Φ h hh W) :=
  surj_of_comp π f Φ h hh hs W.hom ((etComp f).obj W).hom rfl (thU π f Φ h hh W)
    (thU_fst π f Φ h hh W) (thU_snd π f Φ h hh W)

end M

end RamanujanPetersson.EtPBC.T3d

end

end

-- ===== S4.Def_RP_EtPBC_A_DescK1 =====
section

/-!
# S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`

`0 → F → E → Λ_X → 0` short exact, `σ ∈ E(T)` with `b σ = 1`:
* `secT σ : Hom(Λ|_T, E|_T)` (the section `1 ↦ σ`), `secT_b`: `secT σ ≫ b = 1`;
* `retT : Hom(E|_T, F|_T)` with `a ≫ retT = 1` (`a_retT`): `x ↦ a⁻¹ (x - secT (b x))`;
* for `ψ : Z ⟶ T`, **`tau : E ⟶ (ψ ≫ T.hom)_* N_Z`** (`F = N_X`) with **`a_tau`**: `a ≫ tau = uC`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescK

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.SgUnit RamanujanPetersson.EtPBC

universe u

section Ret

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} {F E : EtSh Λ X}
  (a : F ⟶ E) (b : E ⟶ unitSh Λ X) (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact)
  {T : X.Etale} (σ : E.obj.obj (op T))
  (hσ : (b.hom.app (op T)).hom σ = (constUnit (ModuleCat.of Λ Λ) T).hom 1)

/-- `x ↦ x - secT (b x)`. -/
def piT (W : (Over T)ᵒᵖ) :
    ((Over.forget T).op ⋙ E.obj).obj W →ₗ[Λ] ((Over.forget T).op ⋙ E.obj).obj W :=
  LinearMap.id - ((secT σ).app W).hom ∘ₗ ((wh b T).app W).hom

end Ret

section Tau

end Tau

end RamanujanPetersson.EtPBC.DescK

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Fs =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fs: stalks of free sheaves

For `W : P.Etale` and `x : P`, the stalk of `Λ[W]` at `x̄ = geomPtAt x` is the free module on the geometric fibre of
`W` over `x̄`:
* `fibDesc`: the map `presheafFiber (Λ[Hom(-, W)]) → (fibre →₀ Λ)`, `h ↦ fiber.map h b` at `(V, b)`;
* `stalkFree`: the induced map out of the stalk of `Λ[W]`, `stalkFree_germ` (germ of the tautological section at `a`
  goes to `single a 1`);
* `freeLin W x : (fibre →₀ Λ) →ₗ stalk`, `a ↦ germ_a(taut)`; **`freeStalkEquiv`** (bijective);
* `freeMap_taut`, **`freeLin_natural`**: the stalk map of `Λ[w]` is `lmapDomain (fiber.map w)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.FreeStk

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

variable (Λ) in
/-- The components of `fibDesc`. -/
def fibFun (W : P.Etale) (x : P) (V : P.Etale) (b : (geomPtAt x).point.fiber.obj V) :
    (freePre Λ W).obj (op V) ⟶ ModuleCat.of Λ ((geomPtAt x).point.fiber.obj W →₀ Λ) :=
  ModuleCat.ofHom (Finsupp.lmapDomain Λ Λ (fun h : V ⟶ W => (geomPtAt x).point.fiber.map h b))

theorem isIso_fib (W : P.Etale) (x : P) : IsIso (((geomPtAt x).point.presheafFiber (A := ModuleCat.{u} Λ)).map
    (toSheafify P.smallEtaleTopology (freePre Λ W))) := by
  have h : IsIso (((geomPtAt x).point.presheafFiber (A := ModuleCat.{u} Λ)).map
    (toSheafify P.smallEtaleTopology (freePre Λ W))) := inferInstance
  exact h

end RamanujanPetersson.EtPBC.FreeStk

end

end

-- ===== S4.Def_RP_EtPi1_FunA =====
section

/-!
# S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change

`A → A'`, `K → K'` compatible (`A → K → K'`, `A → A' → K'`), `ι : K̄ →ₐ[K] K̄'` any `K`-embedding.

* `bcField f = K'(roots of f)` in `K̄'` (splitting field, finite, Galois when `f` is separable);
* `rootSet_bc`: the roots of `f` in `K̄'` are the `ι`-images of its roots in `K̄`;
* `icMap`: `integralClosure A L → integralClosure A' L'` induced by `ι`;
* `bcField_unram`: for `L ∈ unramSet A K` the splitting field of `L` over `K'` has trivial inertia over `A'`
  (an inertia element restricts, via `ι`, to an inertia element of `Gal(L/K)`, which is trivial);
* `map_mem_maxUnram`: `ι (K_U(A)) ⊆ K_U(A')`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace EtPi1

open GalCover Polynomial

noncomputable section

section FunA

variable {A K A' K' : Type} [CommRing A] [Field K] [Algebra A K]
  [CommRing A'] [Field K'] [Algebra A' K'] [Algebra K K'] [Algebra A A'] [Algebra A K']
  [IsScalarTower A K K'] [IsScalarTower A A' K']
  (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure K')

theorem rootSet_bc (f : K[X]) :
    (f.map (algebraMap K K')).rootSet (AlgebraicClosure K') = ι '' f.rootSet (AlgebraicClosure K) := by
  rw [(IsAlgClosed.splits _ : (f.map (algebraMap K (AlgebraicClosure K))).Splits).image_rootSet ι]
  ext w
  rw [mem_rootSet, mem_rootSet, Polynomial.map_ne_zero_iff (algebraMap K K').injective, aeval_map_algebraMap]

end FunA

end

end EtPi1
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2e =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2e): stage S4, the values of `H` on the pieces of `W₂`

GLOB/REL PLAN v1, stage S4 (piece level). `d = d₂₁ ≫ d₀ : D₂ ⟶ D₁ ⟶ D_{g₀}`, `q` a piece of `W₂`, `q₁` a piece of
`W₁`, `Ψ : Frac(Γ(W₁) ⧸ q₁) → Frac(Γ(W₂) ⧸ q)` compatible with `(wm (prdMap d₂₁)).appTop`:
* `piece_value`: `m^* H · bK_q(φ₂ r)^N = Ψ (toPiQ ((prdMap d₀)^* y) q₁)` when `H · ρ(r)^N = ρ y`;
* `piece_t`: `Ψ (toPiQ (gamMap shG₁ r) q₁) = bK_q (φ₂ r)`;
* `frac_value`: `X T₂^N = Ψ(T₁^N w (1 - T₁ z))`, `Ψ T₁ = T₂ ≠ 0` ⇒ `X = Ψ w (1 + T₂ (-Ψ z))` (the shape of `hHp`/`hHq`
  of `uk_diff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtDeg

section Frac

theorem frac_value {K₁ K₂ : Type*} [Field K₁] [Field K₂] (Ψ : K₁ →+* K₂) {X T₂ : K₂} {T₁ w z : K₁} {N : ℕ}
    (hT : Ψ T₁ = T₂) (hT₂ : T₂ ≠ 0) (hX : X * T₂ ^ N = Ψ (T₁ ^ N * w * (1 - T₁ * z))) :
    X = Ψ w * (1 + T₂ * -Ψ z) := by
  rw [map_mul, map_mul, map_pow, map_sub, map_one, map_mul, hT] at hX
  apply mul_right_cancel₀ (pow_ne_zero N hT₂)
  rw [hX]
  ring

end Frac

section Gen

end Gen

section Piece

end Piece

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel4 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals

REL PLAN v2 (s126) + s128 fix. At a bad point `c(b)` (`G = (X - C b)^m G_b`, `G_b(b) ≠ 0`, `c(b) ∉ U₀`), the chart
`D' := D_{G_b} = chEt c (locF G_b)` satisfies the hypotheses of `bad_term_zero'` (O2Bd5):
* fibres: **`subsingleton_fib_of_mono`**, **`nonempty_fib_of_mem`** (generic);
* **`bad_pt`**, **`badCh_r₁`** (`hDr₁`), **`badCh_r`** (`hDr`), **`badCh_D'`** (`hD'`), **`badCh_hUo`**, **`isAffine_badCh`**,
  **`badCh_hta`** (`hta`), **`badCh_n`** (`hDn`);
* CRT ideals `J b := (X - C b) S`: **`span_coprime_pow`** (`hJt`), **`pairwise_span_coprime`** (`hJ`) of `exists_S23_chart`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Cech

section Fib

end Fib

section BadCh

end BadCh

section BadCh2

end BadCh2

section JAlg

variable {k : Type} [Field k] {S : Type} [CommRing S] [Algebra k[X] S]

/-- **`hJt`** of `exists_S23_chart`. -/
theorem span_coprime_pow {a b : k} (hab : a ≠ b) (n : ℕ) :
    IsCoprime (Ideal.span {algebraMap k[X] S (X - C a) ^ n}) (Ideal.span {algebraMap k[X] S (X - C b)}) := by
  rw [Ideal.isCoprime_span_singleton_iff]
  exact ((isCoprime_X_sub_C_ne hab).map (algebraMap k[X] S)).pow_left

/-- **`hJ`** of `exists_S23_chart`. -/
theorem pairwise_span_coprime {ι : Type} {s : ι → k} (hs : Function.Injective s) :
    Pairwise fun i j => IsCoprime (Ideal.span {algebraMap k[X] S (X - C (s i))})
      (Ideal.span {algebraMap k[X] S (X - C (s j))}) := fun i j hij => by
  dsimp only
  rw [Ideal.isCoprime_span_singleton_iff]
  exact (isCoprime_X_sub_C_ne (hs.ne hij)).map (algebraMap k[X] S)

end JAlg

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP2 =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)

GLOB/REL PLAN v1 stage S4 data: for `G = g₀ c₀' t` (an opaque variable with `hGdef`), the `D_G` and
`D₂ := D₁_{c₀'}` instances (`isAffine_prdG`, `isAffine_prdUo`, Km6 instances), the `D₂` fibre data (ZarCh) and `hD₂`,
`hR₂₁`, then `pp_core` (O2PP1).
* helpers: `dvd_of_Gdef`, `tdvd_of_Gdef`, `ne_zero_of_Gdef`, `hpt_of_ne_zero`, `isUnit_locF_self`, `hzU_of`,
  `hUo_of_range`, `mem_opnDg_or`, `mem_opnDg_prd'`, `nontrivial_of_fpt`;
* **`pp_G`** (DEF): the target class at `D₁` lies in `Gr`, from the S2-S3 output and `c₀'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer

section Helpers

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {a : k} {Uo Uz : P.Opens}

theorem ne_zero_of_Gdef {g₀ c₀' G : k[X]} (hg0 : g₀ ≠ 0) (hc : c₀' ≠ 0) (hGdef : G = g₀ * c₀' * (X - C a)) :
    G ≠ 0 :=
  fun h0 => mul_ne_zero (mul_ne_zero hg0 hc) (X_sub_C_ne_zero a) (hGdef.symm.trans h0)

end Helpers

section PPG

end PPG

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl1a =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point

GLOB/REL PLAN v1, stage S2 input (`h1` of `exists_approx_crt`, O2Ap1). Over an algebraically closed `k`:
* `exists_const_add_mul`: if `B` is unramified and essentially of finite type over `k[X]` and `q` is the only maximal
  ideal containing `t = X - a`, then every `x : B` is `c₀ + t·y` with `c₀ ∈ k[X]`;
* `chart_h1`: the same for a chart `Spec B ⟶ A¹ ⟶ P` with exactly one geometric point over `c(X = a)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtDeg

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtKum

universe u

section Alg

variable {k : Type u} [Field k]

theorem span_X_sub_C_eq_of_mem (a : k) (I : Ideal k[X]) [hI : I.IsPrime] (h : X - C a ∈ I) :
    I = Ideal.span {X - C a} :=
  ((isMaximal_span_X_sub_C a).eq_of_le hI.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm

end Alg

section Chart

end Chart

end RamanujanPetersson.EtPBC.EtDeg

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP4f =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP4f): PP' at a chart `D` for a piece `p` and a Kummer radical `α`

GLOB/REL PLAN v1 stage S1: `u = x / y` with `x ∣ c_x`, `y ∣ c_y` (`exists_frac_dvd`, (3a)), the density element `L`
(`exists_L`, (3b), algebra `gamAlg`), the splits `c_• = t^e c_•'`, `L = t^e L'` (`exists_eq_pow_mul_eval_ne_zero`, (3c)) and
`F := g₀ L' c_x' c_y'` (opaque via `∃`-elim), then `pp_D1` (O2PP4e).
* helpers: `ne_zero_of_pow_eq`, `F_facts`;
* **`pp_D`** (DEF): the target class `ε(D)∘θ⁻¹(kapS p (kumD α))` lies in `Gr`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer

/-- `F = g L c₁ c₂`: divisibilities and `F(a) ≠ 0`. -/
theorem F_facts {k : Type*} [Field k] {a : k} {g L c₁ c₂ F : k[X]} (hF : F = g * L * c₁ * c₂)
    (hg : g.eval a ≠ 0) (hL : L.eval a ≠ 0) (h₁ : c₁.eval a ≠ 0) (h₂ : c₂.eval a ≠ 0) :
    g ∣ F ∧ L ∣ F ∧ c₁ ∣ F ∧ c₂ ∣ F ∧ F.eval a ≠ 0 := by
  subst hF
  refine ⟨((dvd_mul_right g L).mul_right c₁).mul_right c₂, ((dvd_mul_left L g).mul_right c₁).mul_right c₂,
    (dvd_mul_left c₁ (g * L)).mul_right c₂, dvd_mul_left c₂ _, ?_⟩
  rw [eval_mul, eval_mul, eval_mul]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hg hL) h₁) h₂

section PPD

end PPD

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L1a =====
section

/-!
# S4-EtPBC-A, L1a (MVr combinatorics): exactness of the free MV complex fibrewise over `C`

For maps `p₁ : A' → A`, `p₂ : A' → B`, `w : A → C`, `v : B → C` with `w ∘ p₁ = v ∘ p₂`, the complex
`Λ[A'] → Λ[A] ⊕ Λ[B] → Λ[C]`, `l ↦ (p₁ l, -p₂ l)`, `(p, q) ↦ w p + v q`, is exact (and the first map injective,
the last surjective) when every `c : C` satisfies `MVG1` (one point of `A` over `c`, `p₂` bijective over `c`) or
`MVG2` (one point of `B` over `c`, `p₁` bijective over `c`): `mv_inj`, `mv_surj`, `mv_exact`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

section MVComb

universe u₀ u₁ u₂ u₃ u₄

variable {Λ : Type u₀} [CommRing Λ] {A' : Type u₁} {A : Type u₂} {B : Type u₃} {C : Type u₄}
  (p₁ : A' → A) (p₂ : A' → B) (w : A → C) (v : B → C)

theorem mv_inj (hsq : ∀ a', w (p₁ a') = v (p₂ a')) (hg : ∀ c, MVG1 p₂ w v c ∨ MVG2 p₁ w v c)
    (l : A' →₀ Λ) (h1 : Finsupp.mapDomain p₁ l = 0) (h2 : Finsupp.mapDomain p₂ l = 0) : l = 0 := by
  ext a'
  rcases hg (w (p₁ a')) with ⟨_, _, h⟩ | ⟨_, _, h⟩
  · obtain ⟨a₀, _, hu⟩ := h (p₂ a') (hsq a').symm
    have key : ∀ x, p₂ x = p₂ a' ↔ x = a' := fun x =>
      ⟨fun hx => (hu x hx).trans (hu a' rfl).symm, fun hx => hx ▸ rfl⟩
    have := mapDomain_apply_unique p₂ l key
    rw [h2] at this
    simpa using this.symm
  · obtain ⟨a₀, _, hu⟩ := h (p₁ a') rfl
    have key : ∀ x, p₁ x = p₁ a' ↔ x = a' := fun x =>
      ⟨fun hx => (hu x hx).trans (hu a' rfl).symm, fun hx => hx ▸ rfl⟩
    have := mapDomain_apply_unique p₁ l key
    rw [h1] at this
    simpa using this.symm

variable (hsq : ∀ a', w (p₁ a') = v (p₂ a')) (hg : ∀ c, MVG1 p₂ w v c ∨ MVG2 p₁ w v c)
include hsq hg

theorem mvE₁_p₁ (a : A) :
    Finsupp.mapDomain p₁ (mvE₁ Λ p₁ p₂ w v a) = Finsupp.single a 1 - mvF Λ p₂ w v (w a) := by
  by_cases h1 : MVG1 p₂ w v (w a)
  · rw [mvE₁, dif_neg (fun h => h.1 h1), mvF, dif_pos h1, Finsupp.mapDomain_zero,
      h1.1 _ a (Classical.choose_spec h1.2.1) rfl, sub_self]
  · obtain ⟨_, _, hu⟩ := (hg (w a)).resolve_left h1
    have he : ∃ a', p₁ a' = a := (hu a rfl).exists
    rw [mvE₁, dif_pos ⟨h1, he⟩, mvF, dif_neg h1, Finsupp.mapDomain_single, Classical.choose_spec he, sub_zero]

theorem mvE₂_p₁ (b : B) : Finsupp.mapDomain p₁ (mvE₂ Λ p₂ w v b) = - mvF Λ p₂ w v (v b) := by
  by_cases h1 : MVG1 p₂ w v (v b)
  · have he : ∃ a', p₂ a' = b := (h1.2.2 b rfl).exists
    rw [mvE₂, dif_pos ⟨h1, he⟩, mvF, dif_pos h1, Finsupp.mapDomain_single, ← Finsupp.single_neg]
    congr 1
    apply h1.1
    · rw [hsq, Classical.choose_spec he]
    · exact Classical.choose_spec h1.2.1
  · rw [mvE₂, dif_neg (fun h => h1 h.1), mvF, dif_neg h1, Finsupp.mapDomain_zero, neg_zero]

end MVComb

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6b2 =====
section

/-!
# S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`

For a chart `D = chEt c φ` (`B` Dedekind, `(X - a)` a nonzero prime) and `s' : D ⟶ ιP^* W`:
* the point `d₀ = (X - a)` of `D` over `z = c a` and its `K`-point `δ₀` (`δ₀_hom : δ₀ ≫ D.hom = ptz`);
* `wK = s'(d₀)`, the `K`-point `v'` of `Vs` over `sK` (`v'_hom`), `gE₀ : D ⟶ Es` (`v ↦ (s' v, σ₀ v)`);
* `Vb = gE₀⁻¹(Og)`, `Db = opn D Vb` (`d₀ ∈ Vb`), its fibre at `z` (subsingleton, nonempty) and `hSb`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.Z3 RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum

section Sq

end Sq

section Pt

variable {K : Type} [Field K] [IsAlgClosed K] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)]

theorem d₀_max [IsDedekindDomain B] (ht : φ.hom (X - C a) ≠ 0)
    (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime) : (Ideal.span {φ.hom (X - C a)}).IsMaximal :=
  hP.isMaximal (by rwa [Ne, Ideal.span_singleton_eq_bot])

end Pt

section Fib

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end


