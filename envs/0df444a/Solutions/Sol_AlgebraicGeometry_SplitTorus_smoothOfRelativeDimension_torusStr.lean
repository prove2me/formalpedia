-- Prove2me | solution 1 for AlgebraicGeometry.SplitTorus.smoothOfRelativeDimension_torusStr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7cafc700-7007-5034-aede-9edc1282195f

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SplitTorus_smoothOfRelativeDimension_torusStr

set_option autoImplicit false

universe u v

open MvPolynomial

namespace SplitTorusSmoothEngine

variable (S : Type u) [CommRing S] (ι : Type v)

noncomputable def polyGenerators : Algebra.Generators S (MvPolynomial ι S) ι where
  val := X
  σ' := _root_.id
  aeval_val_σ' s := by simp
  algebra := Algebra.id _
  algebraMap_eq := by
    ext p
    · simp
    · simp

theorem polyGenerators_ker : (polyGenerators S ι).ker = ⊥ := by
  rw [Algebra.Generators.ker_eq_ker_aeval_val]
  refine (RingHom.ker_eq_bot_iff_eq_zero _).mpr fun p hp => ?_
  simpa [polyGenerators] using hp

noncomputable def polyPresentation : Algebra.Presentation S (MvPolynomial ι S) ι PEmpty.{1} where
  toGenerators := polyGenerators S ι
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    rw [polyGenerators_ker]
    simp

noncomputable def polyPreSubmersive :
    Algebra.PreSubmersivePresentation S (MvPolynomial ι S) ι PEmpty.{1} where
  toPresentation := polyPresentation S ι
  map := PEmpty.elim
  map_inj a := a.elim

theorem polyPreSubmersive_jacobian : (polyPreSubmersive S ι).jacobian = 1 := by
  classical
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have h : (polyPreSubmersive S ι).jacobiMatrix = 1 := Matrix.ext fun i _ => i.elim
  rw [h, Matrix.det_one, map_one]

noncomputable def polySubmersive :
    Algebra.SubmersivePresentation S (MvPolynomial ι S) ι PEmpty.{1} where
  toPreSubmersivePresentation := polyPreSubmersive S ι
  jacobian_isUnit := by rw [polyPreSubmersive_jacobian]; exact isUnit_one

theorem isStandardSmoothOfRelativeDimension_mvPolynomial [Finite ι] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) S (MvPolynomial ι S) :=
  (polySubmersive S ι).isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

theorem isStandardSmoothOfRelativeDimension_mvPolynomial_fin (d : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension d S (MvPolynomial (Fin d) S) := by
  simpa using isStandardSmoothOfRelativeDimension_mvPolynomial S (Fin d)

end SplitTorusSmoothEngine

namespace SplitTorusSmoothEngine

variable (S : Type u) [CommRing S] (d : ℕ)

noncomputable def expHom (d : ℕ) : (Fin d →₀ ℕ) →+ (Fin d → ℤ) :=
  (Finsupp.coeFnAddHom).comp (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ))

theorem expHom_apply (v : Fin d →₀ ℕ) (i : Fin d) : expHom d v i = (v i : ℤ) := rfl

theorem expHom_injective : Function.Injective (expHom d) := by
  intro v w h
  ext i
  have := congrFun h i
  rw [expHom_apply, expHom_apply] at this
  exact_mod_cast this

noncomputable def polyToTorus : MvPolynomial (Fin d) S →ₐ[S] AddMonoidAlgebra S (Fin d → ℤ) :=
  AddMonoidAlgebra.mapDomainAlgHom S S (expHom d)

theorem polyToTorus_monomial (v : Fin d →₀ ℕ) (s : S) :
    polyToTorus S d (MvPolynomial.monomial v s) = AddMonoidAlgebra.single (expHom d v) s := by
  change AddMonoidAlgebra.mapDomain (expHom d) (AddMonoidAlgebra.single v s) = _
  rw [AddMonoidAlgebra.mapDomain_single]

theorem polyToTorus_injective : Function.Injective (polyToTorus S d) := fun _ _ h =>
  AddMonoidAlgebra.mapDomain_injective (expHom_injective d) h

theorem polyToTorus_X (i : Fin d) :
    polyToTorus S d (X i) = AddMonoidAlgebra.single (Pi.single i 1) 1 := by
  rw [MvPolynomial.X, polyToTorus_monomial]
  congr 1
  funext j
  rw [expHom_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [Ne.symm h]

theorem polyToTorus_prod_X_pow (k : ℕ) :
    polyToTorus S d ((∏ i, X i) ^ k) = AddMonoidAlgebra.single (fun _ => (k : ℤ)) 1 := by
  rw [map_pow, map_prod]
  simp_rw [polyToTorus_X]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one, AddMonoidAlgebra.single_pow, one_pow,
    Finset.univ_sum_single (fun _ : Fin d => (1 : ℤ))]
  congr 1
  funext i
  simp

theorem exists_single_mul_eq (v : Fin d → ℤ) (s : S) :
    ∃ (k : ℕ) (x : MvPolynomial (Fin d) S),
      AddMonoidAlgebra.single v s * polyToTorus S d ((∏ i, X i) ^ k) = polyToTorus S d x := by
  refine ⟨∑ i, (v i).natAbs,
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (v i + ∑ j, (v j).natAbs).toNat) s, ?_⟩
  rw [polyToTorus_prod_X_pow, polyToTorus_monomial, AddMonoidAlgebra.single_mul_single, mul_one]
  congr 1
  funext i
  rw [expHom_apply, Finsupp.coe_equivFunOnFinite_symm, Pi.add_apply, Int.toNat_of_nonneg]
  have h1 : -(v i) ≤ |v i| := neg_le_abs _
  have h2 : |v i| ≤ ∑ j, |v j| := Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)
  push_cast
  linarith

theorem exists_mul_eq (z : AddMonoidAlgebra S (Fin d → ℤ)) :
    ∃ (k : ℕ) (x : MvPolynomial (Fin d) S), z * polyToTorus S d ((∏ i, X i) ^ k) = polyToTorus S d x := by
  induction z using AddMonoidAlgebra.induction_on with
  | of v => exact exists_single_mul_eq S d v 1
  | add f g hf hg =>
    obtain ⟨k, x, hx⟩ := hf
    obtain ⟨l, y, hy⟩ := hg
    refine ⟨k + l, x * (∏ i, X i) ^ l + y * (∏ i, X i) ^ k, ?_⟩
    rw [add_mul, map_add, map_mul, map_mul, ← hx, ← hy, pow_add, map_mul]
    ring
  | smul r f hf =>
    obtain ⟨k, x, hx⟩ := hf
    refine ⟨k, r • x, ?_⟩
    rw [smul_mul_assoc, hx, map_smul]

theorem isLocalization_away_polyToTorus :
    letI := (polyToTorus S d).toRingHom.toAlgebra
    IsLocalization.Away (∏ i, X i : MvPolynomial (Fin d) S) (AddMonoidAlgebra S (Fin d → ℤ)) := by
  letI := (polyToTorus S d).toRingHom.toAlgebra
  have halg : ∀ x, algebraMap (MvPolynomial (Fin d) S) (AddMonoidAlgebra S (Fin d → ℤ)) x =
      polyToTorus S d x := fun _ => rfl
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, k, rfl⟩
    rw [halg, polyToTorus_prod_X_pow]
    exact ⟨(AddMonoidAlgebra.of S (Fin d → ℤ)).toHomUnits (Multiplicative.ofAdd fun _ => (k : ℤ)), rfl⟩
  · intro z
    obtain ⟨k, x, hx⟩ := exists_mul_eq S d z
    exact ⟨⟨x, ⟨_, k, rfl⟩⟩, by rw [halg, halg]; exact hx⟩
  · intro x y h
    rw [halg, halg] at h
    exact ⟨1, by rw [polyToTorus_injective S d h]⟩

theorem isStandardSmoothOfRelativeDimension_torusCoord :
    Algebra.IsStandardSmoothOfRelativeDimension d S (AddMonoidAlgebra S (Fin d → ℤ)) := by
  letI := (polyToTorus S d).toRingHom.toAlgebra
  haveI : IsScalarTower S (MvPolynomial (Fin d) S) (AddMonoidAlgebra S (Fin d → ℤ)) :=
    IsScalarTower.of_algebraMap_eq fun s => ((polyToTorus S d).commutes s).symm
  haveI := isLocalization_away_polyToTorus S d
  haveI h0 : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin d) S)
      (AddMonoidAlgebra S (Fin d → ℤ)) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (∏ i, X i : MvPolynomial (Fin d) S)
  haveI := isStandardSmoothOfRelativeDimension_mvPolynomial_fin S d
  have := Algebra.IsStandardSmoothOfRelativeDimension.trans (n := d) (m := 0) (R := S)
    (S := MvPolynomial (Fin d) S) (T := AddMonoidAlgebra S (Fin d → ℤ))
  rwa [zero_add] at this

open CategoryTheory AlgebraicGeometry in
theorem smoothOfRelativeDimension_torus :
    SmoothOfRelativeDimension d
      (Spec.map (CommRingCat.ofHom (algebraMap S (AddMonoidAlgebra S (Fin d → ℤ))))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr
    (isStandardSmoothOfRelativeDimension_torusCoord S d)

end SplitTorusSmoothEngine

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SplitTorus in
theorem solution
    (S : Type u) [CommRing S] (d : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension d S (torusCoord S d) ∧
      SmoothOfRelativeDimension d (torusStr S d) :=
  ⟨SplitTorusSmoothEngine.isStandardSmoothOfRelativeDimension_torusCoord S d,
    SplitTorusSmoothEngine.smoothOfRelativeDimension_torus S d⟩

end S_AlgebraicGeometry_SplitTorus_smoothOfRelativeDimension_torusStr
end P2MW
export P2MW.S_AlgebraicGeometry_SplitTorus_smoothOfRelativeDimension_torusStr (solution)
