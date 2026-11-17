-- Prove2me | Definitions.Def_N25_LocalKummerEquivariance
-- name    : N25_LocalKummerEquivariance
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:08:44.011594+00:00
-- url     : https://prove2.me/theorems/edabf954-9e7f-429b-9088-17a6fcfacc6b
-- title:
--   Galois equivariance of the label-$13$ diamond action
-- statement:
--   Records that arithmetic Galois action commutes with the label-$13$ diamond operator $γ$ and with the selected polynomial operator $π$, namely $σ(γx)=γ(σx)$ and $σ(πx)=π(σx)$. This makes $ker(π)$ Galois-stable and permits it to carry the representation used in the descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_LocalCarrier
/-! Galois equivariance of the label-13 diamond operator and of the selected polynomial operator `piEnd`.
These lemmas are kept in the definition layer because the Galois action on the kernel `V` of `piEnd` needs them. -/
set_option autoImplicit false
noncomputable section
open AlgebraicCurve IntermediateField HahnSeries
open scoped MatrixGroups
namespace N25
namespace DiamondGalois
open ModularCurve
section Semilinear

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem mul_ofAlgAut_comm (g : SemilinearAut K F) (τ : F ≃ₐ[K] F)
    (h : ∀ x : F, g • (τ x) = τ (g • x)) :
    g * SemilinearAut.ofAlgAut τ = SemilinearAut.ofAlgAut τ * g := by
  apply Subtype.ext
  apply Prod.ext
  · apply RingEquiv.ext
    intro x
    exact h x
  · apply RingEquiv.ext
    intro a
    change (SemilinearAut.baseAut g * 1) a = (1 * SemilinearAut.baseAut g) a
    rw [mul_one, one_mul]

private theorem smul_smul_comm_of_mul_comm (A B : SemilinearAut K F) (h : A * B = B * A) (P : Pic0 K F) :
    A • (B • P) = B • (A • P) := by
  rw [← mul_smul, ← mul_smul, h]

end Semilinear

/- Rational generators determine maps of the scalar-extended function field. -/
section Rational

variable {L : Type*} [Field L] [Algebra ℚ L]

private theorem ringHom_apply_eq_of_eqOn_generators {X : Type*} [DivisionRing X]
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} {R : Set (LaurentSeries ℚ)} (hRF : R ⊆ F₀)
    (hFR : F₀ ≤ IntermediateField.adjoin ℚ R) (f₁ f₂ : laurentBaseChange L F₀ →+* X)
    (hconst : ∀ (a : L) (ha : algebraMap L (LaurentSeries L) a ∈ laurentBaseChange L F₀),
      f₁ ⟨algebraMap L (LaurentSeries L) a, ha⟩ = f₂ ⟨algebraMap L (LaurentSeries L) a, ha⟩)
    (hgen : ∀ (r : LaurentSeries ℚ) (hr : r ∈ R),
      f₁ ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ =
        f₂ ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩)
    (x : laurentBaseChange L F₀) : f₁ x = f₂ x := by

  let T : Subfield (LaurentSeries L) :=
    (RingHom.eqLocusField f₁ f₂).map (SubringClass.subtype (laurentBaseChange L F₀))
  have hT : ∀ z : laurentBaseChange L F₀, f₁ z = f₂ z → (z : LaurentSeries L) ∈ T := fun z hz =>
    Subfield.mem_map.mpr ⟨z, hz, rfl⟩

  suffices hx : (x : LaurentSeries L) ∈ T by
    obtain ⟨x', hx', hx'x⟩ := Subfield.mem_map.mp hx
    have hxx : x' = x := Subtype.ext hx'x
    subst hxx
    exact hx'

  have hgenT : ∀ r ∈ R, coeffEmb L r ∈ T := fun r hr =>
    hT ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ (hgen r hr)

  have hF₀ : ∀ z ∈ F₀, coeffEmb L z ∈ T := by
    intro z hz
    have hz' : z ∈ (IntermediateField.adjoin ℚ R).toSubfield :=
      (IntermediateField.mem_toSubfield _ _).mpr (hFR hz)
    rw [IntermediateField.adjoin_toSubfield] at hz'
    have hle : Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ R) ≤
        T.comap (coeffEmb L) := by
      rw [Subfield.closure_le]
      rintro w (⟨a, rfl⟩ | hw)
      · rw [SetLike.mem_coe, Subfield.mem_comap, eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) a,
          map_ratCast]
        exact SubfieldClass.ratCast_mem T a
      · rw [SetLike.mem_coe, Subfield.mem_comap]
        exact hgenT w hw
    exact Subfield.mem_comap.mp (hle hz')

  have hx := x.2
  rw [mem_laurentBaseChange_iff] at hx
  refine (Subfield.closure_le.mpr ?_) hx
  rintro _ (⟨a, rfl⟩ | ⟨z, hz, rfl⟩)
  · exact hT ⟨algebraMap L (LaurentSeries L) a, (laurentBaseChange L F₀).algebraMap_mem a⟩
      (hconst a _)
  · exact hF₀ z hz

private theorem arithmeticRingAut_comm_of_rational_on_generators
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} {R : Set (LaurentSeries ℚ)} (hRF : R ⊆ F₀)
    (hFR : F₀ ≤ IntermediateField.adjoin ℚ R)
    (τ : laurentBaseChange L F₀ →+* laurentBaseChange L F₀)
    (hτL : ∀ (a : L) (ha : algebraMap L (LaurentSeries L) a ∈ laurentBaseChange L F₀),
      τ ⟨algebraMap L (LaurentSeries L) a, ha⟩ = ⟨algebraMap L (LaurentSeries L) a, ha⟩)
    (hτ : ∀ (r : LaurentSeries ℚ) (hr : r ∈ R), ∃ y : LaurentSeries ℚ,
      ((τ ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ : laurentBaseChange L F₀) :
        LaurentSeries L) = coeffEmb L y)
    (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) :
    arithmeticRingAut F₀ σ (τ x) = τ (arithmeticRingAut F₀ σ x) := by
  refine ringHom_apply_eq_of_eqOn_generators (X := laurentBaseChange L F₀) hRF hFR
    ((arithmeticRingAut F₀ σ).toRingHom.comp τ) (τ.comp (arithmeticRingAut F₀ σ).toRingHom)
    ?_ ?_ x
  ·
    intro a ha
    have h1 : ∀ (b : L) (hb : algebraMap L (LaurentSeries L) b ∈ laurentBaseChange L F₀),
        arithmeticRingAut F₀ σ ⟨algebraMap L (LaurentSeries L) b, hb⟩ =
          ⟨algebraMap L (LaurentSeries L) (σ b), (laurentBaseChange L F₀).algebraMap_mem (σ b)⟩ :=
      fun b hb => Subtype.ext (coeffMap_algebraMap (σ : L →+* L) b)
    change arithmeticRingAut F₀ σ (τ _) = τ (arithmeticRingAut F₀ σ _)
    rw [hτL a ha, h1, hτL]
  ·
    intro r hr
    obtain ⟨y, hy⟩ := hτ r hr
    have hfix : arithmeticRingAut F₀ σ
        (⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ : laurentBaseChange L F₀) =
          ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ :=
      Subtype.ext (coeffMap_coeffEmb σ r)
    change arithmeticRingAut F₀ σ (τ _) = τ (arithmeticRingAut F₀ σ _)
    rw [hfix]
    apply Subtype.ext
    rw [coe_arithmeticRingAut_apply, hy, coeffMap_coeffEmb]

end Rational

/- Rational diamond automorphisms commute with coefficientwise arithmetic action. -/
section Diamond

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

private theorem isDiamondAutHBar_rational {d : (ZMod M)ˣ}
    {τ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H}
    (hτ : IsDiamondAutHBar M H d τ) (r : LaurentSeries ℚ)
    (hr : r ∈ intFormRatiosC ℚ (CohCarrier.GammaH M H)) :
    ∃ y : LaurentSeries ℚ,
      (((τ : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H)
          ⟨coeffEmb (AlgebraicClosure ℚ) r, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (intFormRatiosC_subset ℚ (CohCarrier.GammaH M H) hr)⟩ : xHFunctionFieldBar M H) :
        LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hr

  obtain ⟨γ, hγ⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  have h00 : (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    have h1 : (((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) : ZMod M) =
        (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) := rfl
    rw [← h1, hγ, inv_inv]
  obtain ⟨y, -, hy, -⟩ := hτ k f g pf pg hf hg hg0 γ γ.2 h00
  exact ⟨y, hy⟩

private theorem arithmeticRingAut_diamondAutHBar_comm {d : (ZMod M)ˣ}
    (hτ : IsDiamondAutHBar M H d (diamondAutHBar M H d))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : xHFunctionFieldBar M H) :
    arithmeticRingAut (xHFunctionField M H) σ
        ((diamondAutHBar M H d : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H) x) =
      (diamondAutHBar M H d : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H)
        (arithmeticRingAut (xHFunctionField M H) σ x) :=
  arithmeticRingAut_comm_of_rational_on_generators
    (intFormRatiosC_subset ℚ (CohCarrier.GammaH M H)) le_rfl
    (diamondAutHBar M H d : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H)
    (fun a _ => (diamondAutHBar M H d).commutes a)
    (isDiamondAutHBar_rational M H hτ) σ x

private theorem arithmeticGalois_mul_ofAlgAut_diamondAutHBar {d : (ZMod M)ˣ}
    (hτ : IsDiamondAutHBar M H d (diamondAutHBar M H d))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (xHFunctionField M H) σ * SemilinearAut.ofAlgAut (diamondAutHBar M H d) =
      SemilinearAut.ofAlgAut (diamondAutHBar M H d) * arithmeticGalois (xHFunctionField M H) σ :=
  mul_ofAlgAut_comm _ _ (arithmeticRingAut_diamondAutHBar_comm M H hτ σ)

private theorem galois_smul_diamondHBar (d : (ZMod M)ˣ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : JH M H) :
    σ • diamondHBar M H d P = diamondHBar M H d (σ • P) := by
  rcases Classical.em (∃ τ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d τ) with hex | hex
  · rw [diamondHBar_apply, diamondHBar_apply, galois_smul_pic0_def, galois_smul_pic0_def]
    exact smul_smul_comm_of_mul_comm _ _
      (arithmeticGalois_mul_ofAlgAut_diamondAutHBar M H (isDiamondAutHBar_diamondAutHBar hex) σ) P
  · rw [diamondHBar_of_not M H hex, diamondHBar_of_not M H hex]

end Diamond

end DiamondGalois
/-- The diamond operator with label 13 commutes with arithmetic Galois action. -/
theorem gamma_galois_comm (σ : N25.Gal) (x : N25.J) : σ • N25.gamma x = N25.gamma (σ • x) := by
  exact DiamondGalois.galois_smul_diamondHBar 25 H25
    (ZMod.unitOfCoprime 13 (by decide)) σ x

/-- The selected polynomial operator commutes with arithmetic automorphisms. -/
theorem piEnd_galois_comm (σ : Gal) (x : J) :
    σ • piEnd x = piEnd (σ • x) := by
  let a : J →+ J :=
    { toFun := fun y => σ • y
      map_zero' := smul_zero (A := J) σ
      map_add' := fun y z => smul_add σ y z }
  have hg (y : J) : a (gamma y) = gamma (a y) := gamma_galois_comm σ y
  change a (piEnd x) = piEnd (a x)
  simp only [piEnd, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
    AddMonoidHom.id_apply, AddMonoidHom.comp_apply, map_add, map_nsmul, hg]
end N25


