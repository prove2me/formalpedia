-- Prove2me | Definitions.Def_RPLib_F2_035
-- name    : RPLib_F2_035
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T12:25:39.230437+00:00
-- url     : https://prove2.me/theorems/976f7942-9f1e-4814-b0e2-d8c07dd720b2
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 035 of 70
-- statement:
--   File 035 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_ChartE2`: S4-Lefschetz L4g part 2: the chart over `∞` of a finite subcover
--   * `S4.Def_RP_Lefschetz_ShapData`: S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover
--   * `S4.Def_RP_Lefschetz_BlockE`: S4-Lefschetz, L3d3b: the cover `E` of an open subgroup, in the `Rfin` chart
--   * `S4.Def_RP_Lefschetz_BlockE2`: S4-Lefschetz, L3d3b part 2: the constant field and the Frobenius of the block cover `E`
--   * `S4.Def_RP_Lefschetz_ZFin1`: S4-Lefschetz, L6z (1): finiteness of cocycle modules, the group-theoretic part
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_024
import Definitions.Def_RPLib_F2_032

/-!
# Ramanujan-Petersson curve library (flat edition), file 035 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_ChartE2`: S4-Lefschetz L4g part 2: the chart over `∞` of a finite subcover
* `S4.Def_RP_Lefschetz_ShapData`: S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover
* `S4.Def_RP_Lefschetz_BlockE`: S4-Lefschetz, L3d3b: the cover `E` of an open subgroup, in the `Rfin` chart
* `S4.Def_RP_Lefschetz_BlockE2`: S4-Lefschetz, L3d3b part 2: the constant field and the Frobenius of the block cover `E`
* `S4.Def_RP_Lefschetz_ZFin1`: S4-Lefschetz, L6z (1): finiteness of cocycle modules, the group-theoretic part
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_ChartE2 =====
section

/-!
# S4-Lefschetz L4g part 2: the chart over `∞` of a finite subcover

`E ⊆ K_U` a finite subextension of `K̄`, `k' = Kc 𝔽_q E`. Value lemmas for `jE`, `theta`, `pi1CongrEquiv`
(proved generically, never through `equivOfEq` composites), then:
* `thetaE_val`, `uE_smul`: `uE (σ y) = thetaE σ (uE y)`;
* `isIntegral_chartE_iff`: `IsIntegral R_∞(k', E) y ↔ IsIntegral O_∞(𝔽_q) (y : Ē)`; `isIntegral_iotaE_iff`;
* `chartE : proChart(E) ≃+* proChart(K)` (charts over `∞`), `chartE_smul`, `chartE_symm_smul`;
* boundary primes and inertia correspond: `chartQ`/`chartP`, `isBdryPrime_chartQ/P`, `mem_inertia_chartQ_iff`
  (generic forms `isBdryPrime_comap`, `mem_inertia_comap_iff` for any isomorphism of pro-charts).
Concrete `Ideal.inertia` statements on these charts need `(α := proChart ..)` explicitly (else `α` stays a
metavariable: the chart's `Subalgebra.toSemiring` does not unify with `Ring.toSemiring ?_`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover CurveCoh

noncomputable section

section ValGen

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram A K) [FiniteDimensional K E]

end ValGen

section EqVal

variable {F L : Type} [Field F] [Field L] [Algebra F L]

end EqVal

section CongrVal

variable {A B K : Type} [CommRing A] [CommRing B] [Field K] [Algebra A K] [Algebra B K]

end CongrVal

section ChartGen

variable {A K R0 : Type} [CommRing A] [Field K] [Algebra A K] [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
variable {A' K' R0' : Type} [CommRing A'] [Field K'] [Algebra A' K'] [CommRing R0'] [Algebra R0' K']
  [Algebra R0' (maxUnram A' K')] [IsScalarTower R0' K' (maxUnram A' K')]

end ChartGen

section ChartE2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

/-- Step 4 of `thetaE_val`: `theta` at the inner element. -/
theorem thetaE_val_t (σ : Pi1 (Rfin (Kc Fq E) E) E) (x : maxUnram (Rfin Fq K) K) :
    ((theta Fq[X] K E hE (pi1CongrEquiv (maxUnram_rfin_Kc Fq E) σ)
        ((IntermediateField.equivOfEq (maxUnram_rfin Fq K).symm).symm x) : maxUnram Fq[X] K) :
          AlgebraicClosure K) =
      ιE K E ((pi1CongrEquiv (maxUnram_rfin_Kc Fq E) σ ((jE Fq[X] K E hE).symm
        (eExt hE ((IntermediateField.equivOfEq (maxUnram_rfin Fq K).symm).symm x))) : maxUnram Fq[X] E) :
          AlgebraicClosure E) :=
  theta_val Fq[X] K E hE _ _

/-- Step 5 of `thetaE_val`: the inner value. -/
theorem thetaE_val_v (σ : Pi1 (Rfin (Kc Fq E) E) E) (x : maxUnram (Rfin Fq K) K) :
    ((pi1CongrEquiv (maxUnram_rfin_Kc Fq E) σ ((jE Fq[X] K E hE).symm
        (eExt hE ((IntermediateField.equivOfEq (maxUnram_rfin Fq K).symm).symm x))) : maxUnram Fq[X] E) :
          AlgebraicClosure E) =
      ((σ ((uE Fq K E hE).symm x) : maxUnram (Rfin (Kc Fq E) E) E) : AlgebraicClosure E) := by
  rw [thetaE_val_i, uE_symm_eq]

/-- The value of `thetaE σ` on `K_U`: transport of `σ` along `uE`. -/
theorem thetaE_val (σ : Pi1 (Rfin (Kc Fq E) E) E) (x : maxUnram (Rfin Fq K) K) :
    ((thetaE Fq K E hE σ x : maxUnram (Rfin Fq K) K) : AlgebraicClosure K) =
      ιE K E ((σ ((uE Fq K E hE).symm x) : maxUnram (Rfin (Kc Fq E) E) E) : AlgebraicClosure E) :=
  (thetaE_val_o Fq K E hE σ x).trans ((thetaE_val_t Fq K E hE σ x).trans
    (congrArg (ιE K E) (thetaE_val_v Fq K E hE σ x)))

/-- **`uE` is `thetaE`-equivariant.** -/
theorem uE_smul (σ : Pi1 (Rfin (Kc Fq E) E) E) (y : maxUnram (Rfin (Kc Fq E) E) E) :
    uE Fq K E hE (σ y) = thetaE Fq K E hE σ (uE Fq K E hE y) := by
  apply Subtype.ext
  rw [thetaE_val, RingEquiv.symm_apply_apply, uE_val]

theorem uE_symm_smul (σ : Pi1 (Rfin (Kc Fq E) E) E) (x : maxUnram (Rfin Fq K) K) :
    (uE Fq K E hE).symm (thetaE Fq K E hE σ x) = σ ((uE Fq K E hE).symm x) := by
  rw [RingEquiv.symm_apply_eq, uE_smul, RingEquiv.apply_symm_apply]

/-! ### The chart of `E` over `∞` -/

instance towerChartE : IsScalarTower (Oinf Fq) (Rinf Fq E) (maxUnram (Rfin (Kc Fq E) E) E) :=
  IsScalarTower.of_algebraMap_eq fun g => Subtype.ext <| by
    show algebraMap (Oinf Fq) (AlgebraicClosure E) g =
      algebraMap (Rinf Fq E) (AlgebraicClosure E) (algebraMap (Oinf Fq) (Rinf Fq E) g)
    rw [IsScalarTower.algebraMap_apply (Oinf Fq) E (AlgebraicClosure E),
      IsScalarTower.algebraMap_apply (Rinf Fq E) E (AlgebraicClosure E)]
    rfl

theorem algebraMap_rinf_val (r : Rinf Fq E) :
    ((algebraMap (Rinf Fq E) (maxUnram (Rfin (Kc Fq E) E) E) r : maxUnram (Rfin (Kc Fq E) E) E) :
      AlgebraicClosure E) = algebraMap E (AlgebraicClosure E) (r : E) := by
  show algebraMap (Rinf Fq E) (AlgebraicClosure E) r = _
  rw [IsScalarTower.algebraMap_apply (Rinf Fq E) E (AlgebraicClosure E)]
  rfl

theorem algebraMap_rinfKc_val (r : Rinf (Kc Fq E) E) :
    ((algebraMap (Rinf (Kc Fq E) E) (maxUnram (Rfin (Kc Fq E) E) E) r : maxUnram (Rfin (Kc Fq E) E) E) :
      AlgebraicClosure E) = algebraMap E (AlgebraicClosure E) (r : E) := by
  show algebraMap (Rinf (Kc Fq E) E) (AlgebraicClosure E) r = _
  rw [IsScalarTower.algebraMap_apply (Rinf (Kc Fq E) E) E (AlgebraicClosure E)]
  rfl

theorem isIntegral_rinfKc_iff (y : maxUnram (Rfin (Kc Fq E) E) E) :
    IsIntegral (Rinf (Kc Fq E) E) y ↔ IsIntegral (Rinf Fq E) y := by
  constructor
  · intro h
    exact IsIntegral.map_of_comp_eq (S := maxUnram (Rfin (Kc Fq E) E) E) (U := maxUnram (Rfin (Kc Fq E) E) E)
      (rinfKcEquiv Fq E).toRingHom (RingHom.id _) (RingHom.ext fun r => Subtype.ext (by
        simp only [RingHom.comp_apply, RingHom.id_apply, algebraMap_rinf_val, algebraMap_rinfKc_val,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, rinfKcEquiv_val])) h
  · intro h
    exact IsIntegral.map_of_comp_eq (S := maxUnram (Rfin (Kc Fq E) E) E) (U := maxUnram (Rfin (Kc Fq E) E) E)
      (rinfKcEquiv Fq E).symm.toRingHom (RingHom.id _) (RingHom.ext fun r => Subtype.ext (by
        simp only [RingHom.comp_apply, RingHom.id_apply, algebraMap_rinf_val, algebraMap_rinfKc_val,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, rinfKcEquiv_symm_val])) h

/-- An element of `K_U(E)` lies in the chart over `∞` iff it is integral over `O_∞(𝔽_q)` in `Ē`. -/
theorem isIntegral_chartE_iff (y : maxUnram (Rfin (Kc Fq E) E) E) :
    IsIntegral (Rinf (Kc Fq E) E) y ↔ IsIntegral (Oinf Fq) (y : AlgebraicClosure E) := by
  have : Algebra.IsIntegral (Oinf Fq) (Rinf Fq E) := ⟨fun r => integralClosure.isIntegral r⟩
  rw [isIntegral_rinfKc_iff, IntermediateField.coe_isIntegral_iff]
  exact ⟨fun h => isIntegral_trans y h, fun h => h.tower_top⟩

/-- `ι_E` as an `O_∞(𝔽_q)`-algebra map. -/
def iotaOinf : AlgebraicClosure E →ₐ[Oinf Fq] AlgebraicClosure K :=
  { (ιE K E).toRingEquiv.toRingHom with
    commutes' := fun r => by
      show ιE K E (algebraMap (Oinf Fq) (AlgebraicClosure E) r) = algebraMap (Oinf Fq) (AlgebraicClosure K) r
      rw [IsScalarTower.algebraMap_apply (Oinf Fq) E (AlgebraicClosure E), AlgEquiv.commutes]
      rfl }

theorem isIntegral_iotaE_iff (z : AlgebraicClosure E) :
    IsIntegral (Oinf Fq) (ιE K E z) ↔ IsIntegral (Oinf Fq) z :=
  isIntegral_algHom_iff (iotaOinf Fq K E) (ιE K E).injective

/-- **The charts over `∞` agree**: `proChart(E) ≃+* proChart(K)`, `y ↦ uE y`. -/
def chartE : proChart (Rfin (Kc Fq E) E) E (Rinf (Kc Fq E) E) ≃+* proChart (Rfin Fq K) K (Rinf Fq K) where
  toFun y := ⟨uE Fq K E hE y.1, (isIntegral_chartK_iff Fq K _).2 (by
    rw [uE_val, isIntegral_iotaE_iff]
    exact (isIntegral_chartE_iff Fq K E _).1 y.2)⟩
  invFun x := ⟨(uE Fq K E hE).symm x.1, (isIntegral_chartE_iff Fq K E _).2 (by
    rw [← isIntegral_iotaE_iff Fq K E, uE_symm_val, AlgEquiv.apply_symm_apply]
    exact (isIntegral_chartK_iff Fq K _).1 x.2)⟩
  left_inv y := Subtype.ext ((uE Fq K E hE).symm_apply_apply y.1)
  right_inv x := Subtype.ext ((uE Fq K E hE).apply_symm_apply x.1)
  map_mul' a b := Subtype.ext (map_mul (uE Fq K E hE) a.1 b.1)
  map_add' a b := Subtype.ext (map_add (uE Fq K E hE) a.1 b.1)

theorem chartE_val (y : proChart (Rfin (Kc Fq E) E) E (Rinf (Kc Fq E) E)) :
    ((chartE Fq K E hE y : proChart (Rfin Fq K) K (Rinf Fq K)) : maxUnram (Rfin Fq K) K) =
      uE Fq K E hE (y : maxUnram (Rfin (Kc Fq E) E) E) := rfl

theorem chartE_symm_val (x : proChart (Rfin Fq K) K (Rinf Fq K)) :
    (((chartE Fq K E hE).symm x : proChart (Rfin (Kc Fq E) E) E (Rinf (Kc Fq E) E)) :
      maxUnram (Rfin (Kc Fq E) E) E) = (uE Fq K E hE).symm (x : maxUnram (Rfin Fq K) K) := rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- Cached: the `π₁(E)`-action on the chart of `E` over `∞` (the search times out at `k' = Kc 𝔽_q E`). -/
instance mulSemiringAction_chartE :
    MulSemiringAction (Pi1 (Rfin (Kc Fq E) E) E) (proChart (Rfin (Kc Fq E) E) E (Rinf (Kc Fq E) E)) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
theorem chartE_symm_smul (σ : Pi1 (Rfin (Kc Fq E) E) E) (x : proChart (Rfin Fq K) K (Rinf Fq K)) :
    (chartE Fq K E hE).symm (thetaE Fq K E hE σ • x) = σ • (chartE Fq K E hE).symm x :=
  Subtype.ext (uE_symm_smul Fq K E hE σ x.1)

/-! ### Boundary primes and inertia -/

end ChartE2

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ShapData =====
section

/-!
# S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover

Generic part (`ShapGen`): two pro-charts with boundary data `D` (of `V`) and `D'` (of `U`), an isomorphism
`f : proChart(V) ≃+* proChart(U)` equivariant along an injective `r : π₁(U) →* π₁(V)` with `r⁻¹(Γ) = Γ_U`, and
"stabiliser in `Γ` ⇒ inertia" on `V`. Then `gπ`, `gxT` (from `D.cover`), `gJ` satisfy the three Shapiro
hypotheses `InertiaLift`, `DCover`, `DDisj` of `CurveCoh_ShapiroCone` for `H = range r`.

Concrete part (`ShapE`): `V = K`, `U = E ⊆ K_U` over `k' = Kc 𝔽_q E`, `f = chartE.symm`, `r = thetaE`:
`thetaE_mem_pi1geo_iff`, `thetaE_injective`, `stab_mem_inertia_K`, the objects `bdPiE`, `bdxE`, `bdJE` and
`shap_inertiaLift`, `shap_dCover`, `shap_dDisj`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover CurveCoh CP4a

noncomputable section

section ShapGen

variable {A K R0 : Type} [CommRing A] [Field K] [Algebra A K] [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
variable {A' K' R0' : Type} [CommRing A'] [Field K'] [Algebra A' K'] [CommRing R0'] [Algebra R0' K']
  [Algebra R0' (maxUnram A' K')] [IsScalarTower R0' K' (maxUnram A' K')]

variable {q q' : ℕ} {S T : Type} (D : BdryData A K q R0 S) (D' : BdryData A' K' q' R0' T)
  (f : proChart A K R0 ≃+* proChart A' K' R0')
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q) (hD'B : ∀ Q, D'.B Q ↔ IsBdryPrime A' K' R0' Q)

variable (r : Pi1 A' K' →* Pi1 A K) (hf : ∀ σ x, f (r σ • x) = σ • f x) (hr : Function.Injective r)
  (hgeo : ∀ σ, r σ ∈ pi1geo A K q ↔ σ ∈ pi1geo A' K' q')
  (hstab : ∀ Q, IsBdryPrime A K R0 Q → ∀ σ ∈ pi1geo A K q, σ • Q = Q → σ ∈ Q.inertia (Pi1 A K))

include hf hr in
theorem gen_inertiaLift :
    InertiaLift (pi1geo A K q) r.range D.inertia (gJ D' r) (gπ D D' f hDB hD'B) (gxT D D' f hDB hD'B) := by
  intro t h
  obtain ⟨σ0, hσ0⟩ := MonoidHom.mem_range.1 (h : r.range).2
  have e1 : (h : r.range) ∈ gJ D' r t ↔ σ0 ∈ D'.inertia t := by
    rw [gJ, Subgroup.mem_subgroupOf, ← hσ0, Subgroup.mem_map_iff_mem hr]
  rw [e1, ← hσ0]
  have e2 := mem_inertia_comap_iff f r hf (D'.P t) σ0
  rw [gxT_spec D D' f hDB hD'B t, mem_inertia_smul_iff] at e2
  exact e2

include hf hgeo hstab in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem gen_dCover :
    DCover (pi1geo A K q) r.range D.inertia (gπ D D' f hDB hD'B) (gxT D D' f hDB hD'B) := by
  intro s y
  have hQ : IsBdryPrime A K R0 ((y : Pi1 A K) • D.P s) :=
    isBdryPrime_smul A K R0 (y : Pi1 A K) ((hDB _).1 (D.mem s))
  obtain ⟨t, g', hg', hQ'⟩ := D'.cover _ ((hD'B _).2 (isBdryPrime_comap f.symm hQ))
  have hg'K : r g' ∈ pi1geo A K q := (hgeo g').2 hg'
  have h1 : (y : Pi1 A K) • D.P s =
      (r g' * (gxT D D' f hDB hD'B t : Pi1 A K)) • D.P (gπ D D' f hDB hD'B t) := by
    have h2 := congrArg (Ideal.comap f) hQ'
    rw [comap_comap_symm, comap_smul_equiv f r hf, gxT_spec D D' f hDB hD'B t,
      ← mul_smul (r g') (gxT D D' f hDB hD'B t : Pi1 A K) (D.P (gπ D D' f hDB hD'B t))] at h2
    exact h2
  have hπ : gπ D D' f hDB hD'B t = s := by
    refine D.disj _ _ ((y : Pi1 A K)⁻¹ * (r g' * (gxT D D' f hDB hD'B t : Pi1 A K))) ?_ ?_
    · exact (pi1geo A K q).mul_mem ((pi1geo A K q).inv_mem y.2)
        ((pi1geo A K q).mul_mem hg'K (gxT D D' f hDB hD'B t).2)
    · rw [mul_smul ((y : Pi1 A K)⁻¹) (r g' * (gxT D D' f hDB hD'B t : Pi1 A K)) (D.P (gπ D D' f hDB hD'B t)), ← h1, inv_smul_smul]
  have hg0 : (r g' * (gxT D D' f hDB hD'B t : Pi1 A K))⁻¹ * (y : Pi1 A K) ∈ pi1geo A K q :=
    (pi1geo A K q).mul_mem ((pi1geo A K q).inv_mem
      ((pi1geo A K q).mul_mem hg'K (gxT D D' f hDB hD'B t).2)) y.2
  have hfix : ((r g' * (gxT D D' f hDB hD'B t : Pi1 A K))⁻¹ * (y : Pi1 A K)) • D.P s = D.P s :=
    calc ((r g' * (gxT D D' f hDB hD'B t : Pi1 A K))⁻¹ * (y : Pi1 A K)) • D.P s = (r g' * (gxT D D' f hDB hD'B t : Pi1 A K))⁻¹ • ((y : Pi1 A K) • D.P s) :=
          mul_smul _ _ _
      _ = (r g' * (gxT D D' f hDB hD'B t : Pi1 A K))⁻¹ • ((r g' * (gxT D D' f hDB hD'B t : Pi1 A K)) • D.P (gπ D D' f hDB hD'B t)) :=
          congrArg (fun Q : Ideal (proChart A K R0) => (r g' * (gxT D D' f hDB hD'B t : Pi1 A K))⁻¹ • Q) h1
      _ = D.P (gπ D D' f hDB hD'B t) := inv_smul_smul _ _
      _ = D.P s := congrArg D.P hπ
  have hI : (r g' * (gxT D D' f hDB hD'B t : Pi1 A K))⁻¹ * (y : Pi1 A K) ∈ D.inertia s :=
    hstab (D.P s) ((hDB _).1 (D.mem s)) ((r g' * (gxT D D' f hDB hD'B t : Pi1 A K))⁻¹ * (y : Pi1 A K)) hg0 hfix
  refine ⟨t, hπ, ⟨⟨r g', MonoidHom.mem_range.2 ⟨g', rfl⟩⟩, Subgroup.mem_subgroupOf.2 hg'K⟩,
    ⟨_, hg0⟩, hI, ?_⟩
  exact (mul_inv_cancel_left (r g' * (gxT D D' f hDB hD'B t : Pi1 A K)) (y : Pi1 A K)).symm

include hf hr hgeo in
set_option synthInstance.maxHeartbeats 400000 in
theorem gen_dDisj :
    DDisj (pi1geo A K q) r.range D.inertia (gπ D D' f hDB hD'B) (gxT D D' f hDB hD'B) := by
  intro t t' hπ h g hg hx
  obtain ⟨σ0, hσ0⟩ := MonoidHom.mem_range.1 (h : r.range).2
  have hσΓ : σ0 ∈ pi1geo A' K' q' := by
    rw [← hgeo, hσ0]
    exact Subgroup.mem_subgroupOf.1 h.2
  have hfix : (g : Pi1 A K) • D.P (gπ D D' f hDB hD'B t) = D.P (gπ D D' f hDB hD'B t) :=
    Ideal.inertia_le_stabilizer (M := Pi1 A K) (D.P (gπ D D' f hDB hD'B t)) hg
  have key : (D'.P t).comap f = (σ0 • D'.P t').comap f := by
    rw [comap_smul_equiv f r hf, hσ0, gxT_spec D D' f hDB hD'B t, gxT_spec D D' f hDB hD'B t', hx,
      mul_smul (((h : r.range) : Pi1 A K) * (gxT D D' f hDB hD'B t' : Pi1 A K)) (g : Pi1 A K) (D.P (gπ D D' f hDB hD'B t)),
      mul_smul ((h : r.range) : Pi1 A K) (gxT D D' f hDB hD'B t' : Pi1 A K) ((g : Pi1 A K) • D.P (gπ D D' f hDB hD'B t)),
      hfix, hπ]
  exact (D'.disj t' t σ0 hσΓ (comap_injective_equiv f key)).symm

end ShapGen

section ShapE

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

/-- `thetaE` matches the geometric subgroups (levels `#𝔽_q` on `K`, `#k'` on `E`). -/
theorem thetaE_mem_pi1geo_iff (σ : Pi1 (Rfin (Kc Fq E) E) E) :
    thetaE Fq K E hE σ ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq) ↔
      σ ∈ pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) :=
  (pi1Congr_mem_pi1geo_iff (maxUnram_rfin Fq K).symm (Fintype.card Fq) (theta Fq[X] K E hE (pi1Kc Fq E σ))).trans
    ((theta_mem_pi1geo_iff Fq[X] K E hE (Fintype.card Fq) (pi1Kc Fq E σ)).trans (pi1Kc_mem_pi1geo_iff Fq E σ))

theorem thetaE_injective : Function.Injective (thetaE Fq K E hE) := by
  intro a b hab
  rw [thetaE_eq, thetaE_eq] at hab
  exact (pi1Kc Fq E).injective (theta_injective Fq[X] K E hE ((pi1Congr _).injective hab))

set_option synthInstance.maxHeartbeats 400000 in
/-- The boundary point of `K` under the boundary point `t` of `E`. -/
def bdPiE : BdryS (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) (Rinf (Kc Fq E) E) →
    BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K) :=
  gπ (bdryInf Fq K) (bdryInf (Kc Fq E) E) (chartE Fq K E hE).symm (fun _ => Iff.rfl) (fun _ => Iff.rfl)

set_option synthInstance.maxHeartbeats 400000 in
/-- The representative `x_t ∈ Γ`: `chartQ (P_E t) = x_t • P_K (bdPiE t)`. -/
def bdxE : BdryS (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) (Rinf (Kc Fq E) E) →
    pi1geo (Rfin Fq K) K (Fintype.card Fq) :=
  gxT (bdryInf Fq K) (bdryInf (Kc Fq E) E) (chartE Fq K E hE).symm (fun _ => Iff.rfl) (fun _ => Iff.rfl)

set_option synthInstance.maxHeartbeats 400000 in
/-- The inertia at `t` (boundary point of `E`), inside `H = range thetaE`. -/
def bdJE : BdryS (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) (Rinf (Kc Fq E) E) →
    Subgroup (thetaE Fq K E hE).range :=
  gJ (bdryInf (Kc Fq E) E) (thetaE Fq K E hE)

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
/-- On `K`: an element of `π₁^geo` stabilising a boundary prime lies in its inertia. -/
theorem stab_mem_inertia_K (Q : Ideal (proChart (Rfin Fq K) K (Rinf Fq K)))
    (hQ : IsBdryPrime (Rfin Fq K) K (Rinf Fq K) Q) (σ : Pi1 (Rfin Fq K) K)
    (hσ : σ ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq)) (hfix : σ • Q = Q) :
    σ ∈ Ideal.inertia (α := proChart (Rfin Fq K) K (Rinf Fq K)) (Pi1 (Rfin Fq K) K) Q := by
  have := hQ.1
  obtain ⟨hfin, hcard⟩ := good_inf hq Q hQ
  have := hfin
  rw [hq] at hσ
  exact Residue.stab_mem_inertia (p := p) he (exists_zeta_level (Fq := Fq) (F := K) he) hcard hσ hfix

end ShapE

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockE =====
section

/-!
# S4-Lefschetz, L3d3b: the cover `E` of an open subgroup, in the `Rfin` chart

For an open `H ≤ π₁(U)` (`U = Spec Rfin`): `exists_E_of_open` gives a finite separable `E ⊆ K_U` with
`range thetaE = H`, every `τ ∈ H` fixing `E` and every point of `K_U` fixed by `H` lying in `E` (Galois
correspondence through `pi1Congr`). `thetaE_isFrobLift_iff` transports Frobenius lifts along `thetaE` at any level.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a

section Val

variable {K : Type} [Field K]

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A K] [Algebra B K]

end Val

section BlockE

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

/-- A point of `K_U` (`Rfin` chart) fixed by the `pi1Congr`-image of `Δ` lies in `fixedField Δ`. -/
theorem mem_fixedField_of_pi1Congr (Δ : Subgroup (Pi1 Fq[X] K)) (y : maxUnram (Rfin Fq K) K)
    (hy2 : (y : AlgebraicClosure K) ∈ maxUnram Fq[X] K) (hy : ∀ τ' ∈ Δ, pi1Congr (maxUnram_rfin Fq K).symm τ' y = y) :
    (⟨(y : AlgebraicClosure K), hy2⟩ : maxUnram Fq[X] K) ∈ IntermediateField.fixedField Δ := by
  rw [IntermediateField.mem_fixedField_iff]
  intro τ' hτ'
  apply Subtype.ext
  have hv := pi1Congr_val (maxUnram_rfin Fq K).symm τ' ⟨(y : AlgebraicClosure K), hy2⟩ y (Subtype.coe_mk _ _)
  rw [hy τ' hτ'] at hv
  exact hv.symm.trans (Subtype.coe_mk _ _).symm

end BlockE

section FixGen

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

end FixGen

section CongrGen

variable {A B K : Type} [CommRing A] [CommRing B] [Field K] [Algebra A K] [Algebra B K]

theorem mem_comap_pi1Congr (h : maxUnram A K = maxUnram B K) (H : Subgroup (Pi1 B K)) (τ : Pi1 A K) :
    τ ∈ H.comap (pi1Congr h).toMulEquiv.toMonoidHom ↔ pi1Congr h τ ∈ H := by
  rw [Subgroup.mem_comap, cme_toMonoidHom_apply]

theorem isOpen_comap_pi1Congr (h : maxUnram A K = maxUnram B K) (H : Subgroup (Pi1 B K))
    (hH : IsOpen (H : Set (Pi1 B K))) :
    IsOpen ((H.comap (pi1Congr h).toMulEquiv.toMonoidHom : Subgroup (Pi1 A K)) : Set (Pi1 A K)) :=
  hH.preimage (pi1Congr h).continuous

end CongrGen

section EOpen

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

/-- Transport of the fixed-point property: a point of `K_U` (`Rfin` chart) fixed by `H` lies in `E`. -/
theorem mem_E_of_fix (H : Subgroup (Pi1 (Rfin Fq K) K)) (E : IntermediateField K (AlgebraicClosure K))
    (hfixE : ∀ z : maxUnram Fq[X] K,
      (∀ τ' ∈ H.comap (pi1Congr (maxUnram_rfin Fq K).symm).toMulEquiv.toMonoidHom, τ' z = z) →
        (z : AlgebraicClosure K) ∈ E)
    (y : maxUnram (Rfin Fq K) K) (hy : ∀ τ ∈ H, τ y = y) : (y : AlgebraicClosure K) ∈ E := by
  have hy2 : (y : AlgebraicClosure K) ∈ maxUnram Fq[X] K := by
    rw [← maxUnram_rfin Fq K]
    exact y.2
  have hz := mem_fixedField_of_pi1Congr Fq K
    (H.comap (pi1Congr (maxUnram_rfin Fq K).symm).toMulEquiv.toMonoidHom) y hy2
    (fun τ' hτ' => hy _ ((mem_comap_pi1Congr _ H τ').1 hτ'))
  rw [IntermediateField.mem_fixedField_iff] at hz
  have h3 := hfixE ⟨(y : AlgebraicClosure K), hy2⟩ hz
  rw [Subtype.coe_mk] at h3
  exact h3

/-- `H`-fixing transported to the `Rfin` chart. -/
theorem fix_of_mem_H (H : Subgroup (Pi1 (Rfin Fq K) K)) (E : IntermediateField K (AlgebraicClosure K))
    (hE : E ≤ maxUnram Fq[X] K)
    (hΔE : ∀ τ' : Pi1 Fq[X] K, τ' ∈ H.comap (pi1Congr (maxUnram_rfin Fq K).symm).toMulEquiv.toMonoidHom ↔
      ∀ x (hx : x ∈ E), τ' ⟨x, hE hx⟩ = ⟨x, hE hx⟩)
    (τ : Pi1 (Rfin Fq K) K) (hτ : τ ∈ H) (y : maxUnram (Rfin Fq K) K) (hy : (y : AlgebraicClosure K) ∈ E) :
    τ y = y := by
  have he : pi1Congr (maxUnram_rfin Fq K).symm ((pi1Congr (maxUnram_rfin Fq K).symm).symm τ) = τ :=
    ContinuousMulEquiv.apply_symm_apply _ τ
  have hτ' : (pi1Congr (maxUnram_rfin Fq K).symm).symm τ ∈
      H.comap (pi1Congr (maxUnram_rfin Fq K).symm).toMulEquiv.toMonoidHom := by
    rw [mem_comap_pi1Congr, he]
    exact hτ
  have h2 := pi1Congr_fix Fq K E hE _ ((hΔE _).1 hτ') y hy
  rw [he] at h2
  exact h2

/-- `range thetaE = H` from the `Fq[X]`-chart description. -/
theorem mem_range_thetaE_of (H : Subgroup (Pi1 (Rfin Fq K) K)) (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [Algebra.IsSeparable K E] (hE : E ≤ maxUnram Fq[X] K)
    (hΔE : ∀ τ' : Pi1 Fq[X] K, τ' ∈ H.comap (pi1Congr (maxUnram_rfin Fq K).symm).toMulEquiv.toMonoidHom ↔
      ∀ x (hx : x ∈ E), τ' ⟨x, hE hx⟩ = ⟨x, hE hx⟩)
    (τ : Pi1 (Rfin Fq K) K) : τ ∈ (thetaE Fq K E hE).range ↔ τ ∈ H := by
  have he : pi1Congr (maxUnram_rfin Fq K).symm ((pi1Congr (maxUnram_rfin Fq K).symm).symm τ) = τ :=
    ContinuousMulEquiv.apply_symm_apply _ τ
  rw [mem_range_thetaE_iff, mem_range_theta, ← hΔE, mem_comap_pi1Congr, he]

/-- **The cover of an open subgroup**: `E` finite separable in `K_U` with `range thetaE = H`, `H` fixing `E`, and
the `H`-fixed points of `K_U` in `E`. -/
theorem exists_E_of_open (H : Subgroup (Pi1 (Rfin Fq K) K)) (hHo : IsOpen (H : Set (Pi1 (Rfin Fq K) K))) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram Fq[X] K) (_ : FiniteDimensional K E)
      (_ : Algebra.IsSeparable K E),
      (∀ τ, τ ∈ (thetaE Fq K E hE).range ↔ τ ∈ H) ∧
      (∀ τ ∈ H, ∀ y : maxUnram (Rfin Fq K) K, (y : AlgebraicClosure K) ∈ E → τ y = y) ∧
      (∀ y : maxUnram (Rfin Fq K) K, (∀ τ ∈ H, τ y = y) → (y : AlgebraicClosure K) ∈ E) := by
  obtain ⟨E, hE, hfd, hΔE, hfixE⟩ := exists_sub_fix Fq[X] K _
    (isOpen_comap_pi1Congr (maxUnram_rfin Fq K).symm H hHo)
  have hsep := isSeparable_of_le_maxUnram Fq[X] K E hE
  exact ⟨E, hE, hfd, hsep, mem_range_thetaE_of Fq K H E hE hΔE, fix_of_mem_H Fq K H E hE hΔE,
    mem_E_of_fix Fq K H E hfixE⟩

end EOpen

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockE2 =====
section

/-!
# S4-Lefschetz, L3d3b part 2: the constant field and the Frobenius of the block cover `E`

For an open `H ≤ π₁(U)` with cover `E` (`exists_E_of_open`) containing `g` with `g⁻¹ x = x^(q^m)` on constants,
fixing every `y` with `y^(q^m) = y`, and a primitive `(q^m - 1)`-th root of unity in `K_U`:
`card_Kc_block`: the full constant field of `E` has `q^m` elements; `exists_frobE`: `g⁻¹ = thetaE σ` for a
Frobenius lift `σ` of `E` over its constant field.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a

section BlockE2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

include hE in
/-- Every constant of `E` satisfies `c^(q^m) = c` (it is fixed by `g⁻¹ ∈ H`, which acts as `x ↦ x^(q^m)`). -/
theorem kc_pow_fix (H : Subgroup (Pi1 (Rfin Fq K) K))
    (hfixH : ∀ τ ∈ H, ∀ y : maxUnram (Rfin Fq K) K, (y : AlgebraicClosure K) ∈ E → τ y = y)
    {g : Pi1 (Rfin Fq K) K} (hgH : g ∈ H) {m : ℕ}
    (hg : ∀ x : maxUnram (Rfin Fq K) K, IsConst (Fintype.card Fq) x → g⁻¹ x = x ^ (Fintype.card Fq ^ m))
    (c : Kc Fq E) : c ^ (Fintype.card Fq ^ m) = c := by
  have hxU : (((c : E) : AlgebraicClosure K)) ∈ maxUnram (Rfin Fq K) K := by
    rw [maxUnram_rfin Fq K]
    exact hE (c : E).2
  obtain ⟨y, hy⟩ : ∃ y : maxUnram (Rfin Fq K) K, (y : AlgebraicClosure K) = ((c : E) : AlgebraicClosure K) :=
    ⟨⟨_, hxU⟩, rfl⟩
  have hcf : c ^ (Fintype.card Fq ^ Module.finrank Fq (Kc Fq E)) = c := by
    rw [← card_Kc_eq_pow Fq E]
    exact FiniteField.pow_card c
  have hyc : IsConst (Fintype.card Fq) y := by
    refine ⟨Module.finrank Fq (Kc Fq E), finrank_Kc_pos Fq E, Subtype.ext ?_⟩
    rw [IntermediateField.coe_pow, hy, ← IntermediateField.coe_pow, ← IntermediateField.coe_pow, hcf]
  have hyE : (y : AlgebraicClosure K) ∈ E := by
    rw [hy]
    exact (c : E).2
  have hyfix : y ^ (Fintype.card Fq ^ m) = y := (hg y hyc).symm.trans (hfixH g⁻¹ (H.inv_mem hgH) y hyE)
  apply Subtype.ext
  apply Subtype.ext
  rw [IntermediateField.coe_pow, IntermediateField.coe_pow, ← hy, ← IntermediateField.coe_pow, hyfix]

/-- `#k'_E ≤ q^m`. -/
theorem card_Kc_le_block {m : ℕ} (hm : 0 < m) (hA : ∀ c : Kc Fq E, c ^ (Fintype.card Fq ^ m) = c) :
    Fintype.card (Kc Fq E) ≤ Fintype.card Fq ^ m := by
  have h1 : 1 < Fintype.card Fq ^ m := Nat.one_lt_pow hm.ne' Fintype.one_lt_card
  have hne := FiniteField.X_pow_card_sub_X_ne_zero (Kc Fq E) h1
  have hsub : (Finset.univ : Finset (Kc Fq E)).val ⊆ (X ^ (Fintype.card Fq ^ m) - X : (Kc Fq E)[X]).roots := by
    intro a _
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hA a, sub_self]
  calc Fintype.card (Kc Fq E) = (Finset.univ : Finset (Kc Fq E)).card := Finset.card_univ.symm
    _ ≤ (X ^ (Fintype.card Fq ^ m) - X : (Kc Fq E)[X]).natDegree :=
        Polynomial.card_le_degree_of_subset_roots hsub
    _ = Fintype.card Fq ^ m := FiniteField.X_pow_card_sub_X_natDegree_eq (Kc Fq E) h1

/-- `m ∣ [k'_E : 𝔽_q]`: a primitive `(q^m - 1)`-th root of unity of `K_U` lies in `E` and is constant. -/
theorem dvd_finrank_Kc_block (H : Subgroup (Pi1 (Rfin Fq K) K))
    (hfixE : ∀ y : maxUnram (Rfin Fq K) K, (∀ τ ∈ H, τ y = y) → (y : AlgebraicClosure K) ∈ E)
    {m : ℕ} (hm : 0 < m)
    (hHfix : ∀ τ ∈ H, ∀ y : maxUnram (Rfin Fq K) K, y ^ (Fintype.card Fq ^ m) = y → τ y = y)
    (z : maxUnram (Rfin Fq K) K) (hz : IsPrimitiveRoot z (Fintype.card Fq ^ m - 1)) :
    m ∣ Module.finrank Fq (Kc Fq E) := by
  have h1 : 1 < Fintype.card Fq ^ m := Nat.one_lt_pow hm.ne' Fintype.one_lt_card
  have hz1 : z ^ (Fintype.card Fq ^ m) = z := prim_pow_fix h1.le hz
  have hzE : (z : AlgebraicClosure K) ∈ E := hfixE z (fun τ hτ => hHfix τ hτ z hz1)
  obtain ⟨z', hz'⟩ : ∃ z' : E, (z' : AlgebraicClosure K) = z := ⟨⟨_, hzE⟩, rfl⟩
  have hz'1 : z' ^ (Fintype.card Fq ^ m) = z' := by
    apply Subtype.ext
    rw [IntermediateField.coe_pow, hz', ← IntermediateField.coe_pow, hz1]
  have hz'alg : z' ∈ constField Fq E := by
    rw [mem_algebraicClosure_iff]
    refine ⟨X ^ (Fintype.card Fq ^ m) - X, FiniteField.X_pow_card_sub_X_ne_zero Fq h1, ?_⟩
    rw [map_sub, map_pow, Polynomial.aeval_X, hz'1, sub_self]
  obtain ⟨c, hc⟩ : ∃ c : Kc Fq E, (c : E) = z' := ⟨⟨_, hz'alg⟩, rfl⟩
  have hcf : c ^ (Fintype.card Fq ^ Module.finrank Fq (Kc Fq E)) = c := by
    rw [← card_Kc_eq_pow Fq E]
    exact FiniteField.pow_card c
  have hzf : z ^ (Fintype.card Fq ^ Module.finrank Fq (Kc Fq E)) = z := by
    apply Subtype.ext
    rw [IntermediateField.coe_pow, ← hz', ← hc, ← IntermediateField.coe_pow, ← IntermediateField.coe_pow, hcf]
  exact dvd_of_pow_fix Fintype.one_lt_card hm hz hzf

end BlockE2

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ZFin1 =====
section

/-!
# S4-Lefschetz, L6z (1): finiteness of cocycle modules, the group-theoretic part

* `HomLC D A`: locally constant homomorphisms `D → A`.
* `z1_eq_of_reps`: a cocycle on `Δ` is determined by its values on `Δ ∩ ker π` and on representatives of `π(Δ)`.
* `finite_Z1_regRep`: `Z¹(Δ, Λ[Gf])` is finite once `Hom_lc(Δ ∩ ker π, Λ)` is (`Λ`, `Gf` finite).
* `finite_Z1_inertia`: from a residue hypothesis (`Ldet`), every `Z¹(Γ ⊓ I_s, Λ[Gf])` is finite.
* `finite_Z1_triv`: `Z¹(Γ, Λ)` (trivial action) is finite once `H¹_c(Γ, {I_s}; Λ)` and all `Z¹(Γ ⊓ I_s, Λ)` are.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx

/-- Locally constant homomorphisms `D → A`. -/
abbrev HomLC (D A : Type) [Mul D] [TopologicalSpace D] [Add A] : Type :=
  {f : D → A // IsLocallyConstant f ∧ ∀ a b, f (a * b) = f a + f b}

section Gen

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G]
  {A : Type} [AddCommGroup A] [Module Λ A] (ρ : Representation Λ G A)

variable [Finite Λ] [IsTopologicalGroup G] {Gf : Type} [Group Gf] [Finite Gf]

variable (π : G →* Gf) (Γ : Subgroup G) {S : Type} [Fintype S] [DecidableEq S]
  (I : S → Subgroup G) [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]

end Gen

section Triv

variable {Λ : Type} [CommRing Λ] [Finite Λ] {G : Type} [Group G] [TopologicalSpace G]

end Triv

end

end Lefschetz
end RamanujanPetersson


end


