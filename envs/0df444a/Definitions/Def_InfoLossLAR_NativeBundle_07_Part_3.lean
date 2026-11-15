-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_07_Part_3
-- name    : InfoLossLAR_NativeBundle_07_Part_3
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T15:44:48.991358+00:00
-- url     : https://prove2.me/theorems/cbea8443-e34e-4072-9649-1a2826cecfbd
-- title:
--   Selected, tagged and ordinary root-channel interfaces
-- statement:
--   This package defines the complete first-coefficient and tagged selected-root objects, their channel and norm interfaces, and the ordinary selected-root, mean and hybrid families used in assembling the current response.
--
--   At fixed order $R$, the retained coefficients are indexed by primary and body arities with
--   $$r+s\le R.$$
--   Their data keeps the selected control roles, tagged source coordinates, and ordinary components separate, so later root-response identities can refer to the same finite experiment.
--
--   The package supplies these concrete coefficient and channel interfaces. Quantitative norm, cancellation and complete-response guarantees remain in their separately submitted proof dependencies.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; native source modules lean/CurrentAFT/CompleteFirstCoefficient.lean, lean/CurrentAFT/RootTaggedSelected.lean, lean/CurrentAFT/RootTaggedSelectedNorm.lean, lean/CurrentAFT/RootTaggedSelectedChannel.lean, lean/CurrentAFT/SelectedOrdinaryRoot.lean, lean/CurrentAFT/SelectedOrdinaryRootProperties.lean, lean/CurrentAFT/SelectedOrdinaryMean.lean, lean/CurrentAFT/SelectedOrdinaryHybrid.lean. Exact oracle-selected Definition bodies; split from the unaccepted NativeBundle_07 after its recorded server timeout. Source SHA256 4020cfd45c91cd37ead92f6d05478de10510aeed0cb69ed11ba86514f745c243. Header-only transitive import reduction verified by Lean module-data and parser oracles; imported module closure and all non-import source bytes are unchanged. Alternate sparse native dependencies preserve the original non-import body bytes and all public types; this header-only packaging is recorded in sparse_live/manifest.json. Current source SHA256 4020cfd45c91cd37ead92f6d05478de10510aeed0cb69ed11ba86514f745c243.

import Definitions.Def_InfoLossLAR_NativeBundle_07_Part_2











section

















/-! # Exact first and higher parts of a general centered local signed mass -/
namespace CurrentAFT.CompleteFirstCoefficient

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability LocalCoefficientFamily LocalCoefficientNorm
  NormalizedLocalPolynomial LocalRaisingFirst LocalRaisingNorm BackgroundFamilies LocalReferenceEnergy
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def firstScore (security order : ℕ) (horder : 1 ≤ order) (mass : (Fin 4 → Palette security) → ℝ) : Palette security → ℝ :=
  primaryCoefficient (primaryLaw security) (bodyReference security) order horder (completeFamily security order mass)

theorem firstScore_centered (security order : ℕ) (horder : 1 ≤ order) (mass : (Fin 4 → Palette security) → ℝ) :
    (primaryLaw security).expectation (firstScore security order horder mass) = 0 := by
  let color : Palette security := ⟨0, (Parameters.modulus_spec security).2.pos⟩
  let kernel : canonicalKernels (primaryLaw security) (bodyReference security) 1 0 :=
    completeFamily security order mass (primaryArity order horder)
  have h := kernel.property.1 (0 : Fin 1) (fun _ => color) Fin.elim0
  have hupdate (input : Palette security) : Function.update (fun _ : Fin 1 => color) 0 input = (fun _ => input) := by
    funext index
    have hi := Fin.eq_zero index
    subst index
    exact Function.update_self _ _ _
  simp only [hupdate] at h
  exact h

def firstFamily (security order : ℕ) (horder : 1 ≤ order) (mass : (Fin 4 → Palette security) → ℝ) : Family security order :=
  primaryFamily (primaryLaw security) (bodyReference security) order horder (firstScore security order horder mass)
    (firstScore_centered security order horder mass)

theorem complete_sub_first_raises (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 4 → Palette security) → ℝ) (hmass : ∑ word, mass word = 0) :
    GradedInverse.VanishesBelow (primaryLaw security) (bodyReference security) order 2
      (completeFamily security order mass - firstFamily security order horder mass) := by
  intro arity hsmall
  change completeFamily security order mass arity - firstFamily security order horder mass arity = 0
  by_cases hb : 0 < arity.val.2.val
  · rw [completeFamily_no_body security order mass arity hb]
    unfold firstFamily primaryFamily
    rw [Pi.single_eq_of_ne, sub_zero]
    intro hequal
    have h := congrArg (fun item : TruncatedArity order => item.val.2.val) hequal
    change arity.val.2.val = 0 at h
    omega
  · have hs : arity.val.2.val = 0 := by omega
    by_cases hr : arity.val.1.val = 0
    · have harity : arity = zeroArity order := by
        apply Subtype.ext
        exact Prod.ext (Fin.ext hr) (Fin.ext hs)
      subst arity
      rw [completeFamily_zeroArity, hmass, zero_smul]
      unfold firstFamily primaryFamily
      rw [Pi.single_eq_of_ne, sub_zero]
      intro hequal
      have h := congrArg (fun item : TruncatedArity order => item.val.1.val) hequal
      change 0 = 1 at h
      omega
    · have hrone : arity.val.1.val = 1 := by omega
      have harity : arity = primaryArity order horder := by
        apply Subtype.ext
        exact Prod.ext (Fin.ext hrone) (Fin.ext hs)
      subst arity
      apply sub_eq_zero.mpr
      unfold firstFamily primaryFamily
      rw [Pi.single_eq_same]
      apply Subtype.ext
      funext (colors : Fin 1 → Palette security) (centers : Fin 0 → SafePalette security)
      have hcolors : colors = (fun _ => colors 0) := by
        funext index
        have hi := Fin.eq_zero index
        subst index
        rfl
      have hcenters : centers = Fin.elim0 := Subsingleton.elim _ _
      rw [hcolors, hcenters]
      rfl

theorem complete_eq_first_add_higher (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 4 → Palette security) → ℝ) (hmass : ∑ word, mass word = 0) :
    completeFamily security order mass = firstFamily security order horder mass + higherFamily security order mass := by
  funext arity
  change completeFamily security order mass arity = firstFamily security order horder mass arity + higherFamily security order mass arity
  by_cases hsmall : arity.val.1.val + arity.val.2.val < 2
  · rw [higherFamily_vanishesBelow security order mass arity hsmall, add_zero]
    exact sub_eq_zero.mp (complete_sub_first_raises security order horder mass hmass arity hsmall)
  · have hfirst : firstFamily security order horder mass arity = 0 := by
      unfold firstFamily primaryFamily
      rw [Pi.single_eq_of_ne]
      intro hequal
      have h := congrArg (fun item : TruncatedArity order => item.val.1.val + item.val.2.val) hequal
      change arity.val.1.val + arity.val.2.val = 1 + 0 at h
      omega
    rw [hfirst, zero_add]
    unfold completeFamily higherFamily
    simp only [hmass, zero_smul, zero_add, Finset.sum_apply]
    symm
    apply Finset.sum_subset
    · intro selected hselected
      apply Finset.mem_erase.mpr
      constructor
      · intro hequal
        have hcard := (Finset.mem_filter.mp hselected).2
        rw [hequal, Finset.card_empty] at hcard
        omega
      · exact Finset.mem_univ _
    · intro selected _ hnot
      have hcard : selected.card < 2 := by
        by_contra! hcard
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩)
      unfold selectedFamily
      split_ifs with hdegree
      · rw [Pi.single_eq_of_ne]
        intro hequal
        have h := congrArg (fun item : TruncatedArity order => item.val.1.val + item.val.2.val) hequal
        change arity.val.1.val + arity.val.2.val = selected.card + 0 at h
        omega
      · rfl

theorem firstFamily_norm (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 4 → Palette security) → ℝ) (hmass : ∑ word, mass word = 0)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) :
    familyNorm (primaryLaw security) (bodyReference security) order primaryFactor bodyFactor
      (firstFamily security order horder mass) ≤
        primaryFactor * (2 / activation security) * Real.sqrt 2 *
          Real.sqrt (BlockFock.tensorEnergy (LocalTensors.degreeTensor
            (fun _ : Fin 4 => uniformReference security) mass 1)) := by
  let profile := LocalTensors.signedColorCount mass
  have hscore : firstScore security order horder mass =
      PrimaryTensorInverse.densityInverse security (fun color => profile color / (primaryLaw security).weight color) :=
    completeFamily_primary_centered security order horder mass hmass
  have hraw : (primaryLaw security).l2Sq (fun color => profile color / (primaryLaw security).weight color) =
      profileSquareNorm (primaryLaw security).weight profile := by
    change densitySquareNorm (primaryLaw security).weight _ = _
    exact densityScore_square _ _
  have henergy := PrimaryTensorInverse.densityInverse_energy security
    (fun color => profile color / (primaryLaw security).weight color)
  rw [hraw] at henergy
  have hcount := OrdinaryRaising.profile_primary_energy_le_uniform security profile
  have hfock := LocalTensors.degreeTensor_one_energy_zero_mass (uniformReference security)
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security)) mass hmass
  have htotal : (primaryLaw security).l2Sq (firstScore security order horder mass) ≤
      (2 / activation security) ^ 2 * (2 * BlockFock.tensorEnergy
        (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security) mass 1)) := by
    rw [hscore]
    exact henergy.trans (mul_le_mul_of_nonneg_left (hcount.trans_eq (by rw [hfock])) (sq_nonneg _))
  unfold firstFamily
  rw [primaryFamily_norm]
  apply (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htotal) hprimary).trans_eq
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg (by norm_num) (activation_pos security).le),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

end
end CurrentAFT.CompleteFirstCoefficient

end

section















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.RaisingBodySlots
end CurrentAFT.RaisingBodySlots





/-!
# Selected primary groups with their two actual roots

The compensator and attachment roots are integrated together with one
joint primary score. The same protected scalar is used in the leg pair
and attachment. A root tag is an argument of this joint score; two tags
in one group do not duplicate its public-control norm. No root atom is
inverted, so the actual reference may have zero weights.
-/
namespace CurrentAFT.RootTaggedSelected

open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst PhysicalSynthesis
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm GradedControlStability
  LocalCoefficientFamily LocalRaisingFirst LocalRaisingBounds NormalizedLocalPolynomial
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev RootPair (security : ℕ) := Root security × Root security
abbrev Sample (security : ℕ) := RootPair security × FirstHistogram.Scalar security

def rootsLaw (security : ℕ) : FiniteDist (RootPair security) :=
  (rootReference security).prod (rootReference security)

def sourceLaw (security : ℕ) : FiniteDist (Sample security) :=
  (rootsLaw security).prod (scalarLaw security)

def inputEnergy (security : ℕ) (score : RootPair security → Palette security → ℝ) : ℝ :=
  (rootsLaw security).expectation (fun roots => (primaryLaw security).l2Sq (score roots))

theorem inputEnergy_nonneg (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    0 ≤ inputEnergy security score :=
  Finset.sum_nonneg (fun roots _ => mul_nonneg ((rootsLaw security).nonneg roots) ((primaryLaw security).l2Sq_nonneg _))

def massLinear (security : ℕ) :
    (RootPair security → Palette security → ℝ) →ₗ[ℝ] ((Fin 4 → Palette security) → ℝ) :=
  ∑ sample : Sample security, (sourceLaw security).weight sample •
    ((pairedMassLinear security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2).comp
      (LinearMap.proj sample.1))

def mass (security : ℕ) (score : RootPair security → Palette security → ℝ) := massLinear security score

theorem mass_eq_joint (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    mass security score = jointPairedMass security (sourceLaw security)
      (fun sample => (sample.1.1.val : ℤ)) (fun sample => (sample.1.2.val : ℤ))
      (fun sample => sample.2) (fun sample => score sample.1) := by
  funext word
  simp only [mass, massLinear, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, pairedMassLinear_apply, jointPairedMass, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem source_score_energy (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    (sourceLaw security).expectation (fun sample => (primaryLaw security).l2Sq (score sample.1)) =
      inputEnergy security score := by
  unfold sourceLaw
  rw [FiniteDist.expectation_prod]
  simp only [FiniteDist.expectation_const]
  rfl

theorem mass_zero (security : ℕ) (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    (∑ word, mass security score word) = 0 := by
  rw [mass_eq_joint]
  unfold jointPairedMass
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, fixedMass_sum, hcentered, mul_zero, Finset.sum_const_zero]



theorem mass_full_energy (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight
      (mass security score) ≤ (4128 * pairBudget security) * inputEnergy security score := by
  rw [mass_eq_joint]
  let reference := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  apply (profileSquareNorm_average_le (sourceLaw security) reference.weight reference.nonneg _).trans
  calc
    _ ≤ ∑ sample, (sourceLaw security).weight sample * ((4128 * pairBudget security) *
        (primaryLaw security).l2Sq (score sample.1)) := by
      apply Finset.sum_le_sum
      intro sample _
      exact mul_le_mul_of_nonneg_left (pairedMassAt_energy security _ _ sample.2 (score sample.1))
        ((sourceLaw security).nonneg sample)
    _ = _ := by
      change (sourceLaw security).expectation (fun sample => (4128 * pairBudget security) *
        (primaryLaw security).l2Sq (score sample.1)) = _
      rw [FiniteDist.expectation_const_mul, source_score_energy]

def firstConstant : ℝ := 16 + 1310740 * Real.exp Real.pi

theorem mass_first_energy (security : ℕ) (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (mass security score) 1) ≤ firstConstant * (Parameters.base security : ℝ) ^ 31 * inputEnergy security score := by
  rw [mass_eq_joint]
  have h := jointPaired_first_polynomial security (sourceLaw security)
    (fun sample => (sample.1.1.val : ℤ)) (fun sample => (sample.1.2.val : ℤ))
    (fun sample => sample.2) (fun sample => score sample.1) (fun sample => hcentered sample.1)
  change _ ≤ firstConstant * (Parameters.base security : ℝ) ^ 31 *
    (sourceLaw security).expectation (fun sample => (primaryLaw security).l2Sq (score sample.1)) at h
  rwa [source_score_energy] at h

def normalizedResponse (security order : ℕ) (score : RootPair security → Palette security → ℝ) : Family security order :=
  NormalizedLocalPolynomial.normalizedFamily security order (independentPositiveLaw security) (mass security score)



theorem normalizedResponse_vanishesBelow_one (security order : ℕ) (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    GradedInverse.VanishesBelow (primaryLaw security) (bodyReference security) order 1
      (normalizedResponse security order score) :=
  GradedInverse.vanishesBelow_mul _ _ order 1 0 _ _
    (completeFamily_vanishes_one security order _ (mass_zero security score hcentered))
    (GradedInverse.vanishesBelow_zero _ _ order _)



def liftZero (security : ℕ) (score : Palette security → ℝ) : RootPair security → Palette security → ℝ := fun _ => score











end
end CurrentAFT.RootTaggedSelected

end

section















/-! # Joint two-root selected-primary norm budgets from the current laws -/
namespace CurrentAFT.RootTaggedSelectedNorm

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability LocalCoefficientFamily LocalCoefficientNorm
  LocalRaisingNorm LocalRaisingBounds CompleteFirstCoefficient RootTaggedSelected
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def firstNormConstant : ℝ := 8 * Real.sqrt 2 * Real.sqrt RootTaggedSelected.firstConstant

def selectedConstant : ℝ := 2 * (firstNormConstant + LocalRaisingBounds.higherConstant)

theorem firstNormConstant_nonneg : 0 ≤ firstNormConstant := by unfold firstNormConstant; positivity

theorem selectedConstant_nonneg : 0 ≤ selectedConstant :=
  mul_nonneg (by norm_num) (add_nonneg firstNormConstant_nonneg higherConstant_nonneg)

 theorem primaryFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.primaryFactor security := by
  unfold BackgroundRates.primaryFactor
  positivity

 theorem bodyFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.bodyFactor security := by
  unfold BackgroundRates.bodyFactor BackgroundRates.radius
  positivity

 theorem base_ge_one (security : ℕ) : (1 : ℝ) ≤ Parameters.base security := by
  exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)

theorem first_energy_sqrt (security : ℕ) (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    Real.sqrt (BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => LocalReferenceEnergy.uniformReference security)
      (mass security score) 1)) ≤
      Real.sqrt RootTaggedSelected.firstConstant * (Parameters.base security : ℝ) ^ 16 * Real.sqrt (inputEnergy security score) := by
  have hc : 0 ≤ RootTaggedSelected.firstConstant := by unfold RootTaggedSelected.firstConstant; positivity
  have hpower : (Parameters.base security : ℝ) ^ 31 ≤ (Parameters.base security : ℝ) ^ 32 :=
    pow_le_pow_right₀ (base_ge_one security) (by omega)
  have h := (mass_first_energy security score hcentered).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hc) (inputEnergy_nonneg security score))
  apply (Real.sqrt_le_sqrt h).trans_eq
  rw [Real.sqrt_mul (mul_nonneg hc (pow_nonneg (FirstResponse.base_pos security).le _)), Real.sqrt_mul hc,
    show (32 : ℕ) = 16 * 2 by omega, pow_mul, Real.sqrt_sq (pow_nonneg (FirstResponse.base_pos security).le _)]

theorem firstFamily_norm (security order : ℕ) (horder : 1 ≤ order)
    (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    LocalRaisingBounds.coefficientNorm security order (CompleteFirstCoefficient.firstFamily security order horder (mass security score)) ≤
      (firstNormConstant / (Parameters.base security : ℝ) ^ 47) * Real.sqrt (inputEnergy security score) := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security) (show (0 : ℝ) ≤ 2 by norm_num)
    simpa only [div_eq_mul_inv, one_mul, ← mul_assoc, show (2 : ℝ) * 4 = 8 by norm_num] using h
  have h := CompleteFirstCoefficient.firstFamily_norm security order horder (mass security score)
    (mass_zero security score hcentered) (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (primaryFactor_nonneg security)
  apply h.trans
  calc
    _ ≤ ((1 / (Parameters.base security : ℝ) ^ 64) * (8 * (Parameters.base security : ℝ)) * Real.sqrt 2) *
        (Real.sqrt RootTaggedSelected.firstConstant * (Parameters.base security : ℝ) ^ 16 * Real.sqrt (inputEnergy security score)) := by
      apply mul_le_mul _ (first_energy_sqrt security score hcentered) (Real.sqrt_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv (primaryFactor_nonneg security)) (Real.sqrt_nonneg 2)
          |>.trans_eq (by rw [BackgroundRates.primaryFactor_eq])
    _ = _ := by
      unfold firstNormConstant
      rw [show (64 : ℕ) = 47 + 17 by omega, pow_add, show (17 : ℕ) = 1 + 16 by omega, pow_add, pow_one]
      field_simp [hb.ne']

theorem primaryMass_sqrt (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    Real.sqrt (primaryMassEnergy security (mass security score)) ≤
      Real.sqrt 66048 * Real.sqrt LocalRaisingBounds.pairConstant * (Parameters.base security : ℝ) ^ 24 *
        Real.sqrt (inputEnergy security score) := by
  have hmass : primaryMassEnergy security (mass security score) ≤
      (66048 * LocalReferenceEnergy.pairBudget security) * inputEnergy security score :=
    (primaryMassEnergy_uniform_le security _).trans ((mul_le_mul_of_nonneg_left
      (mass_full_energy security score) (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))
  calc
    _ ≤ Real.sqrt ((66048 * LocalReferenceEnergy.pairBudget security) * inputEnergy security score) := Real.sqrt_le_sqrt hmass
    _ = Real.sqrt 66048 * Real.sqrt (LocalReferenceEnergy.pairBudget security) * Real.sqrt (inputEnergy security score) := by
      rw [Real.sqrt_mul (mul_nonneg (by norm_num) (PairedReferenceEnergy.pairBudget_nonneg security)),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 66048)]
    _ ≤ _ := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pairBudget_sqrt_polynomial security)
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).trans_eq (by ring)

theorem higherFamily_norm (security order : ℕ) (score : RootPair security → Palette security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (LocalCoefficientFamily.higherFamily security order (mass security score)) ≤
      (LocalRaisingBounds.higherConstant / (Parameters.base security : ℝ) ^ 102) * Real.sqrt (inputEnergy security score) := by
  have hb := FirstResponse.base_pos security
  have h := LocalRaisingNorm.higherFamily_norm security order (mass security score)
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (primaryFactor_nonneg security) (bodyFactor_nonneg security)
  apply h.trans
  apply (mul_le_mul (actual_higherEnvelope security) (primaryMass_sqrt security score) (Real.sqrt_nonneg _)
    (by positivity : (0 : ℝ) ≤ 16384 / (Parameters.base security : ℝ) ^ 126)).trans_eq
  unfold LocalRaisingBounds.higherConstant
  rw [show (126 : ℕ) = 102 + 24 by omega, pow_add]
  field_simp [hb.ne']

theorem completeFamily_norm (security order : ℕ) (horder : 1 ≤ order)
    (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    LocalRaisingBounds.coefficientNorm security order (NormalizedLocalPolynomial.completeFamily security order (mass security score)) ≤
      ((firstNormConstant + LocalRaisingBounds.higherConstant) / (Parameters.base security : ℝ) ^ 47) *
        Real.sqrt (inputEnergy security score) := by
  rw [complete_eq_first_add_higher security order horder _ (mass_zero security score hcentered)]
  apply (familyNorm_add_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _).trans
  have hpower : (Parameters.base security : ℝ) ^ 47 ≤ (Parameters.base security : ℝ) ^ 102 :=
    pow_le_pow_right₀ (base_ge_one security) (by omega)
  have hdiv := div_le_div_of_nonneg_left higherConstant_nonneg (pow_pos (FirstResponse.base_pos security) 47) hpower
  exact (add_le_add (firstFamily_norm security order horder score hcentered)
    ((higherFamily_norm security order score).trans (mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg _)))).trans_eq (by ring)

/-- A selected paired group consumes the norm of the original joint
root/control input once, even when both body roots carry tags. -/
theorem normalizedResponse_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * LocalRaisingBounds.positiveConstant ≤ (Parameters.base security : ℝ))
    (score : RootPair security → Palette security → ℝ)
    (hcentered : ∀ roots, (primaryLaw security).expectation (score roots) = 0) :
    LocalRaisingBounds.coefficientNorm security order (normalizedResponse security order score) ≤
      (selectedConstant / (Parameters.base security : ℝ) ^ 47) * Real.sqrt (inputEnergy security score) := by
  have hcomplete := completeFamily_norm security order horder score hcentered
  have hn : 0 ≤ LocalRaisingBounds.coefficientNorm security order
      (NormalizedLocalPolynomial.completeFamily security order (mass security score)) :=
    familyNorm_nonneg _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _
  unfold normalizedResponse NormalizedLocalPolynomial.normalizedFamily
  apply (familyNorm_product_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _).trans
  calc
    _ ≤ LocalRaisingBounds.coefficientNorm security order
        (NormalizedLocalPolynomial.completeFamily security order (mass security score)) * 2 :=
      mul_le_mul_of_nonneg_left (LocalRaisingBounds.positiveInverse_bounds security order hlarge).1 hn
    _ ≤ (((firstNormConstant + LocalRaisingBounds.higherConstant) / (Parameters.base security : ℝ) ^ 47) *
        Real.sqrt (inputEnergy security score)) * 2 := mul_le_mul_of_nonneg_right hcomplete (by norm_num)
    _ = _ := by unfold selectedConstant; ring



end
end CurrentAFT.RootTaggedSelectedNorm

end

section















/-! # Actual selected root/control channels on complete joint Hilbert inputs -/
namespace CurrentAFT.RootTaggedSelectedChannel

open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm
  LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds CoefficientHilbert
  RootTaggedSelected RootTaggedSelectedNorm
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Input (security : ℕ) := RootPair security × Palette security


def inputLaw (security : ℕ) : FiniteDist (Input security) := (rootsLaw security).prod (primaryLaw security)


def responseLinear (security order : ℕ) :
    (RootPair security → Palette security → ℝ) →ₗ[ℝ] Family security order where
  toFun score := (completeFamilyLinear security order (massLinear security score)) * LocalRaisingBounds.positiveInverse security order
  map_add' first second := by rw [map_add, map_add, add_mul]
  map_smul' scalar score := by rw [map_smul, map_smul, smul_mul_assoc, RingHom.id_apply]



def curryLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (RootPair security → Palette security → ℝ) where
  toFun score roots primary := score (roots, primary)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def controlCenterLinear (security : ℕ) :
    (RootPair security → Palette security → ℝ) →ₗ[ℝ] (RootPair security → Palette security → ℝ) where
  toFun score roots := centerLinear (primaryLaw security) (score roots)
  map_add' first second := by
    funext roots
    exact (centerLinear (primaryLaw security)).map_add (first roots) (second roots)
  map_smul' scalar score := by
    funext roots
    exact (centerLinear (primaryLaw security)).map_smul scalar (score roots)

theorem controlCenter_energy_le (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    inputEnergy security (controlCenterLinear security score) ≤ inputEnergy security score :=
  Finset.sum_le_sum (fun roots _ => mul_le_mul_of_nonneg_left (center_energy_le _ (score roots)) ((rootsLaw security).nonneg roots))

theorem inputEnergy_curry (security : ℕ) (score : Input security → ℝ) :
    inputEnergy security (curryLinear security score) = (inputLaw security).l2Sq score := by
  unfold inputLaw FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod]
  rfl

/-- Centering acts only on the selected primary control. Its two roots
remain one joint input, and are never divided by their reference atoms. -/
def channel (security order : ℕ) : (Input security → ℝ) →ₗ[ℝ] Family security order :=
  (responseLinear security order).comp ((controlCenterLinear security).comp (curryLinear security))



theorem channel_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * LocalRaisingBounds.positiveConstant ≤ (Parameters.base security : ℝ)) (score : Input security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (channel security order score) ≤
      (selectedConstant / (Parameters.base security : ℝ) ^ 47) * Real.sqrt ((inputLaw security).l2Sq score) := by
  have hcentered (roots : RootPair security) :
      (primaryLaw security).expectation (controlCenterLinear security (curryLinear security score) roots) = 0 :=
    center_mean _ _
  have h := normalizedResponse_norm security order horder hlarge
    (controlCenterLinear security (curryLinear security score)) hcentered
  apply h.trans
  have hinput := controlCenter_energy_le security (curryLinear security score)
  rw [inputEnergy_curry] at hinput
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinput)
    (div_nonneg selectedConstant_nonneg (pow_nonneg (FirstResponse.base_pos security).le _))

theorem channel_vanishesBelow_one (security order : ℕ) (score : Input security → ℝ) :
    GradedInverse.VanishesBelow (primaryLaw security) (bodyReference security) order 1 (channel security order score) :=
  normalizedResponse_vanishesBelow_one security order _ (fun _ => center_mean _ _)





def zeroLiftLinear (security : ℕ) : (Palette security → ℝ) →ₗ[ℝ] (Input security → ℝ) where
  toFun score sample := score sample.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl











/-- Zero, compensator-only, attachment-only and double-root interfaces all
inherit the same physical channel, with exact reference-energy isometries. -/
def zeroChannel (security order : ℕ) := (channel security order).comp (zeroLiftLinear security)









end
end CurrentAFT.RootTaggedSelectedChannel

end

section















/-!
# Actual selected ordinary root/control response

One root and its original safe body control are retained as a joint input.
The physical signed output is the real cyclic translate of that control.
A genuine first-primary inverse lifts its centered mass, followed by the
finite positive reciprocal of the independent ordinary output law.
-/
namespace CurrentAFT.SelectedOrdinaryRoot

open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds CoefficientHilbert PrimaryTensorInverse
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Input (security : ℕ) := Root security × SafePalette security

def inputLaw (security : ℕ) : FiniteDist (Input security) := (rootReference security).prod (bodyReference security)

section Push
variable {Source Output : Type*} [Fintype Source] [Fintype Output]

def pushLinear (law : FiniteDist Source) (embedding : Source → Output) : (Source → ℝ) →ₗ[ℝ] (Output → ℝ) where
  toFun score output := ∑ source, if embedding source = output then law.weight source * score source else 0
  map_add' first second := by
    funext output
    change (∑ source, if embedding source = output then law.weight source * (first source + second source) else 0) =
      (∑ source, if embedding source = output then law.weight source * first source else 0) +
        ∑ source, if embedding source = output then law.weight source * second source else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro source _
    split_ifs <;> ring
  map_smul' scalar score := by
    funext output
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    split_ifs <;> ring

theorem push_test (law : FiniteDist Source) (embedding : Source → Output) (score : Source → ℝ) (test : Output → ℝ) :
    (∑ output, pushLinear law embedding score output * test output) = law.expectation (fun source => score source * test (embedding source)) := by
  simp only [pushLinear, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem push_energy (law : FiniteDist Source) (embedding : Source → Output) (hinjective : Function.Injective embedding)
    (reference : Output → ℝ) (score : Source → ℝ) :
    profileSquareNorm reference (pushLinear law embedding score) =
      ∑ source, (law.weight source * score source) ^ 2 / reference (embedding source) := by
  have hpoint (output : Output) : pushLinear law embedding score output ^ 2 / reference output =
      ∑ source, if embedding source = output then (law.weight source * score source) ^ 2 / reference output else 0 := by
    by_cases hexists : ∃ source, embedding source = output
    · obtain ⟨source, hequal⟩ := hexists
      subst output
      have heq (other : Source) : embedding other = embedding source ↔ other = source := hinjective.eq_iff
      simp only [pushLinear, LinearMap.coe_mk, AddHom.coe_mk, heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · have hnone (source : Source) : embedding source ≠ output := fun hequal => hexists ⟨source, hequal⟩
      simp only [pushLinear, LinearMap.coe_mk, AddHom.coe_mk, hnone, if_false, Finset.sum_const_zero,
        zero_pow (by decide : 2 ≠ 0), zero_div]
  unfold profileSquareNorm
  simp only [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  simp

theorem push_energy_le (law : FiniteDist Source) (embedding : Source → Output) (hinjective : Function.Injective embedding)
    (reference : Output → ℝ) (hpositive : ∀ output, 0 < reference output) (bound : ℝ)
    (hratio : ∀ source, law.weight source ≤ bound * reference (embedding source)) (score : Source → ℝ) :
    profileSquareNorm reference (pushLinear law embedding score) ≤ bound * law.l2Sq score := by
  rw [push_energy law embedding hinjective]
  unfold FiniteDist.l2Sq FiniteDist.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro source _
  apply (div_le_iff₀ (hpositive _)).mpr
  calc
    _ = (law.weight source * score source ^ 2) * law.weight source := by ring
    _ ≤ (law.weight source * score source ^ 2) * (bound * reference (embedding source)) :=
      mul_le_mul_of_nonneg_left (hratio source) (mul_nonneg (law.nonneg source) (sq_nonneg (score source)))
    _ = _ := by ring
end Push

def rootEmbedding (security : ℕ) (root : Root security) (center : SafePalette security) : Palette security :=
  (shiftEquiv security (root.val : ℤ)) center.val

theorem rootEmbedding_injective (security : ℕ) (root : Root security) : Function.Injective (rootEmbedding security root) :=
  (shiftEquiv security (root.val : ℤ)).injective.comp Subtype.val_injective

def sliceLinear (security : ℕ) (root : Root security) : (Input security → ℝ) →ₗ[ℝ] (SafePalette security → ℝ) where
  toFun score center := score (root, center)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rawMassLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (Palette security → ℝ) :=
  ∑ root : Root security, (rootReference security).weight root •
    ((pushLinear (bodyReference security) (rootEmbedding security root)).comp (sliceLinear security root))

def rawMass (security : ℕ) (score : Input security → ℝ) := rawMassLinear security score

theorem rawMass_apply (security : ℕ) (score : Input security → ℝ) (output : Palette security) :
    rawMass security score output = ∑ root, (rootReference security).weight root *
      pushLinear (bodyReference security) (rootEmbedding security root) (fun center => score (root, center)) output := by
  simp only [rawMass, rawMassLinear, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    sliceLinear, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem rawMass_physical (security : ℕ) (score : Input security → ℝ) (test : Palette security → ℝ) :
    (∑ output, rawMass security score output * test output) =
      (inputLaw security).expectation (fun sample => score sample * test (rootEmbedding security sample.1 sample.2)) := by
  simp only [rawMass_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold inputLaw
  rw [FiniteDist.expectation_prod]
  apply Finset.sum_congr rfl
  intro root _
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [push_test]

theorem rawMass_mass (security : ℕ) (score : Input security → ℝ) :
    (∑ output, rawMass security score output) = (inputLaw security).expectation score := by
  have h := rawMass_physical security score (fun _ => 1)
  simpa only [mul_one] using h

theorem fixed_uniform_energy (security : ℕ) (root : Root security) (score : SafePalette security → ℝ) :
    profileSquareNorm (LocalReferenceEnergy.uniformReference security).weight
      (pushLinear (bodyReference security) (rootEmbedding security root) score) ≤ 4 * (bodyReference security).l2Sq score := by
  apply push_energy_le _ _ (rootEmbedding_injective security root)
    (LocalReferenceEnergy.uniformReference security).weight
    (fun color => by rw [LocalReferenceEnergy.uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    4 (fun center => by rw [LocalReferenceEnergy.uniformReference_weight]; exact (bodyReference_upper security center).trans_eq (by ring))

theorem rawMass_uniform_energy (security : ℕ) (score : Input security → ℝ) :
    profileSquareNorm (LocalReferenceEnergy.uniformReference security).weight (rawMass security score) ≤ 4 * (inputLaw security).l2Sq score := by
  have hequal : rawMass security score = fun output => ∑ root, (rootReference security).weight root *
      pushLinear (bodyReference security) (rootEmbedding security root) (fun center => score (root, center)) output :=
    funext (rawMass_apply security score)
  rw [hequal]
  apply (profileSquareNorm_average_le (rootReference security) (LocalReferenceEnergy.uniformReference security).weight
    (LocalReferenceEnergy.uniformReference security).nonneg _).trans
  calc
    _ ≤ ∑ root, (rootReference security).weight root * (4 * (bodyReference security).l2Sq (fun center => score (root, center))) :=
      Finset.sum_le_sum (fun root _ => mul_le_mul_of_nonneg_left (fixed_uniform_energy security root _) ((rootReference security).nonneg root))
    _ = _ := by
      change (rootReference security).expectation (fun root => 4 * (bodyReference security).l2Sq (fun center => score (root, center))) = _
      rw [FiniteDist.expectation_const_mul]
      unfold inputLaw FiniteDist.l2Sq
      rw [FiniteDist.expectation_prod]

theorem rawMass_primary_energy (security : ℕ) (score : Input security → ℝ) :
    profileSquareNorm (primaryLaw security).weight (rawMass security score) ≤ 8 * (inputLaw security).l2Sq score :=
  (OrdinaryRaising.profile_primary_energy_le_uniform security _).trans
    ((mul_le_mul_of_nonneg_left (rawMass_uniform_energy security score) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

def controlCenterLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (Input security → ℝ) where
  toFun score sample := centerLinear (bodyReference security) (fun center => score (sample.1, center)) sample.2
  map_add' first second := by
    funext sample
    exact congrFun ((centerLinear (bodyReference security)).map_add (fun center => first (sample.1, center)) (fun center => second (sample.1, center))) sample.2
  map_smul' scalar score := by
    funext sample
    exact congrFun ((centerLinear (bodyReference security)).map_smul scalar (fun center => score (sample.1, center))) sample.2

theorem controlCenter_energy_le (security : ℕ) (score : Input security → ℝ) :
    (inputLaw security).l2Sq (controlCenterLinear security score) ≤ (inputLaw security).l2Sq score := by
  unfold inputLaw FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_prod]
  apply Finset.sum_le_sum
  intro root _
  exact mul_le_mul_of_nonneg_left (center_energy_le (bodyReference security) (fun center => score (root, center))) ((rootReference security).nonneg root)

theorem centeredMass_zero (security : ℕ) (score : Input security → ℝ) :
    (∑ output, rawMass security (controlCenterLinear security score) output) = 0 := by
  rw [rawMass_mass]
  unfold inputLaw
  rw [FiniteDist.expectation_prod]
  have hmean (root : Root security) : (bodyReference security).expectation (fun center => controlCenterLinear security score (root, center)) = 0 :=
    center_mean _ _
  simp only [hmean, FiniteDist.expectation_const]

def densityLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (Palette security → ℝ) :=
  (densityInverse security).comp ((diagonal (fun color => ((primaryLaw security).weight color)⁻¹)).comp
    ((rawMassLinear security).comp (controlCenterLinear security)))

theorem densityLinear_apply (security : ℕ) (score : Input security → ℝ) :
    densityLinear security score = densityInverse security
      (fun color => rawMass security (controlCenterLinear security score) color / (primaryLaw security).weight color) := by
  apply congrArg (densityInverse security)
  funext color
  simp only [diagonal, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  change ((primaryLaw security).weight color)⁻¹ * rawMass security (controlCenterLinear security score) color = _
  ring

theorem densityLinear_centered (security : ℕ) (score : Input security → ℝ) :
    (primaryLaw security).expectation (densityLinear security score) = 0 := by
  rw [densityLinear_apply, densityInverse_mean]
  have hmean : (primaryLaw security).expectation
      (fun color => rawMass security (controlCenterLinear security score) color / (primaryLaw security).weight color) = 0 := by
    have hpoint (color : Palette security) : (primaryLaw security).weight color *
        (rawMass security (controlCenterLinear security score) color / (primaryLaw security).weight color) =
      rawMass security (controlCenterLinear security score) color := by field_simp [(primaryReference_positive security color).ne']
    simpa only [FiniteDist.expectation, hpoint] using centeredMass_zero security score
  rw [hmean, mul_zero]

def centeredDensityLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] centeredScores security :=
  (densityLinear security).codRestrict (centeredScores security) (densityLinear_centered security)

def numeratorLinear (security order : ℕ) (horder : 1 ≤ order) : (Input security → ℝ) →ₗ[ℝ] Family security order :=
  (primaryEmbeddingLinear security order horder).comp (centeredDensityLinear security)

def channel (security order : ℕ) (horder : 1 ≤ order) : (Input security → ℝ) →ₗ[ℝ] Family security order where
  toFun score := numeratorLinear security order horder score * OrdinaryRaising.positiveInverse security order horder
  map_add' first second := by rw [map_add, add_mul]
  map_smul' scalar score := by rw [map_smul, smul_mul_assoc, RingHom.id_apply]

end
end CurrentAFT.SelectedOrdinaryRoot

end

section















/-! # Norm and physical identities of the actual selected ordinary root channel -/
namespace CurrentAFT.SelectedOrdinaryRootProperties

open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds PrimaryTensorInverse
  SelectedOrdinaryRoot
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference


 theorem primaryFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.primaryFactor security := by
  unfold BackgroundRates.primaryFactor
  positivity

 theorem bodyFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.bodyFactor security := by
  unfold BackgroundRates.bodyFactor BackgroundRates.radius
  positivity

theorem densityLinear_energy (security : ℕ) (score : Input security → ℝ) :
    (primaryLaw security).l2Sq (densityLinear security score) ≤
      (2 / activation security) ^ 2 * (8 * (inputLaw security).l2Sq score) := by
  rw [densityLinear_apply]
  have hraw : (primaryLaw security).l2Sq
      (fun color => rawMass security (controlCenterLinear security score) color / (primaryLaw security).weight color) =
      profileSquareNorm (primaryLaw security).weight (rawMass security (controlCenterLinear security score)) := by
    change densitySquareNorm (primaryLaw security).weight _ = _
    exact densityScore_square _ _
  have h := densityInverse_energy security
    (fun color => rawMass security (controlCenterLinear security score) color / (primaryLaw security).weight color)
  rw [hraw] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact (rawMass_primary_energy security (controlCenterLinear security score)).trans
    (mul_le_mul_of_nonneg_left (controlCenter_energy_le security score) (by norm_num : (0 : ℝ) ≤ 8))

theorem numerator_norm (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (numeratorLinear security order horder score) ≤
      (24 / (Parameters.base security : ℝ) ^ 63) * Real.sqrt ((inputLaw security).l2Sq score) := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security) (show (0 : ℝ) ≤ 2 by norm_num)
    convert h using 1 <;> first | rfl | ring
  have hsqrt := Real.sqrt_le_sqrt (densityLinear_energy security score)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg (by norm_num) ha.le),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)] at hsqrt
  change familyNorm (primaryLaw security) (bodyReference security) order
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (BackgroundFamilies.primaryFamily _ _ order horder (densityLinear security score) (densityLinear_centered security score)) ≤ _
  rw [BackgroundFamilies.primaryFamily_norm]
  calc
    _ ≤ BackgroundRates.primaryFactor security * ((2 / activation security) * Real.sqrt 8 * Real.sqrt ((inputLaw security).l2Sq score)) :=
      by simpa only [FiniteDist.l2Sq, FiniteDist.expectation, mul_assoc] using mul_le_mul_of_nonneg_left hsqrt (primaryFactor_nonneg security)
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * ((8 * (Parameters.base security : ℝ)) * 3 * Real.sqrt ((inputLaw security).l2Sq score)) := by
      rw [BackgroundRates.primaryFactor_eq]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul hinv (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by
      rw [show (64 : ℕ) = 63 + 1 by omega, pow_add, pow_one]
      field_simp [hb.ne']
      ring

theorem channel_norm (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (channel security order horder score) ≤
      (48 / (Parameters.base security : ℝ) ^ 63) * Real.sqrt ((inputLaw security).l2Sq score) := by
  have hn : 0 ≤ LocalRaisingBounds.coefficientNorm security order (numeratorLinear security order horder score) :=
    familyNorm_nonneg _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _
  change LocalRaisingBounds.coefficientNorm security order
    (numeratorLinear security order horder score * OrdinaryRaising.positiveInverse security order horder) ≤ _
  apply (familyNorm_product_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _).trans
  calc
    _ ≤ LocalRaisingBounds.coefficientNorm security order (numeratorLinear security order horder score) * 2 :=
      mul_le_mul_of_nonneg_left (OrdinaryRaising.positiveInverse_bounds security order horder).1 hn
    _ ≤ ((24 / (Parameters.base security : ℝ) ^ 63) * Real.sqrt ((inputLaw security).l2Sq score)) * 2 :=
      mul_le_mul_of_nonneg_right (numerator_norm security order horder score) (by norm_num)
    _ = _ := by ring







theorem channel_vanishesBelow_one (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 1 (channel security order horder score) := by
  apply vanishesBelow_mul _ _ order 1 0
  · apply vanishesBelow_one_of_zero
    change BackgroundFamilies.primaryFamily _ _ order horder (densityLinear security score) (densityLinear_centered security score)
      (zeroArity order) = 0
    unfold BackgroundFamilies.primaryFamily
    rw [Pi.single_eq_of_ne]
    intro hequal
    have h := congrArg (fun arity : TruncatedArity order => arity.val.1.val) hequal
    change 0 = 1 at h
    omega
  · exact vanishesBelow_zero _ _ order _



end
end CurrentAFT.SelectedOrdinaryRootProperties

end

section















/-! # Root averaging for a selected ordinary control

The body control is not resampled. These maps average or center only its
actual independent modular root, including when the root law has zero atoms.
-/
namespace CurrentAFT.SelectedOrdinaryMean
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm GradedControlStability
  LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds CoefficientHilbert SelectedOrdinaryRoot
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

def rootMean (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (SafePalette security → ℝ) where
  toFun score center := (rootReference security).expectation (fun root => score (root, center))
  map_add' first second := by funext center; exact FiniteDist.expectation_add _ _ _
  map_smul' scalar score := by funext center; exact FiniteDist.expectation_const_mul _ _ _

def constantRoot (security : ℕ) : (SafePalette security → ℝ) →ₗ[ℝ] (Input security → ℝ) where
  toFun score sample := score sample.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rootCenter (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (Input security → ℝ) :=
  LinearMap.id - (constantRoot security).comp (rootMean security)

theorem rootMean_constant (security : ℕ) (score : SafePalette security → ℝ) :
    rootMean security (constantRoot security score) = score := by
  funext center
  change (rootReference security).expectation (fun _ => score center) = _
  rw [FiniteDist.expectation_const]

theorem rootCenter_constant (security : ℕ) (score : SafePalette security → ℝ) :
    rootCenter security (constantRoot security score) = 0 := by
  change constantRoot security score - constantRoot security (rootMean security (constantRoot security score)) = 0
  rw [rootMean_constant, sub_self]

theorem rootMean_energy_le (security : ℕ) (score : Input security → ℝ) :
    (bodyReference security).l2Sq (rootMean security score) ≤ (inputLaw security).l2Sq score := by
  unfold inputLaw FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_comm]
  apply Finset.sum_le_sum
  intro center _
  apply mul_le_mul_of_nonneg_left _ ((bodyReference security).nonneg center)
  have h := (rootReference security).l2Sq_nonneg (centerLinear (rootReference security) (fun root => score (root, center)))
  rw [center_energy] at h
  exact sub_nonneg.mp h

theorem rootCenter_energy_le (security : ℕ) (score : Input security → ℝ) :
    (inputLaw security).l2Sq (rootCenter security score) ≤ (inputLaw security).l2Sq score := by
  unfold inputLaw FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_prod]
  conv_lhs => rw [FiniteDist.expectation_comm]
  conv_rhs => rw [FiniteDist.expectation_comm]
  apply Finset.sum_le_sum
  intro center _
  exact mul_le_mul_of_nonneg_left (center_energy_le (rootReference security) (fun root => score (root, center))) ((bodyReference security).nonneg center)

theorem rootCenter_centered (security : ℕ) (score : Input security → ℝ) (center : SafePalette security) :
    (rootReference security).expectation (fun root => rootCenter security score (root, center)) = 0 :=
  center_mean _ _

theorem rootMean_zero_of_centered (security : ℕ) (score : Input security → ℝ)
    (hcentered : ∀ center, (rootReference security).expectation (fun root => score (root, center)) = 0) :
    rootMean security score = 0 := funext hcentered

theorem rootCenter_eq_of_centered (security : ℕ) (score : Input security → ℝ)
    (hcentered : ∀ center, (rootReference security).expectation (fun root => score (root, center)) = 0) :
    rootCenter security score = score := by
  change score - constantRoot security (rootMean security score) = score
  rw [rootMean_zero_of_centered security score hcentered, map_zero, sub_zero]







end
end CurrentAFT.SelectedOrdinaryMean

end

section













/-! # The selected ordinary group with a retained leading body slot

Root averaging retains the original body coefficient. Root-centered
responses use the actual pure-primary inverse. Their sum is a genuine
linear lift of the same physical root/control experiment.
-/
namespace CurrentAFT.SelectedOrdinaryHybrid
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse LocalCoefficientFamily LocalRaisingLinear LocalRaisingFirst LocalRaisingBounds CoefficientHilbert
  SelectedOrdinaryRoot SelectedOrdinaryMean
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference

 theorem hp (security : ℕ) : 0 ≤ BackgroundRates.primaryFactor security :=
  (RaisingPatternBudget.primaryFactor_pos security).le
 theorem hb (security : ℕ) : 0 ≤ BackgroundRates.bodyFactor security :=
  (RaisingPatternBudget.bodyFactor_pos security).le

def independentChannel (security order : ℕ) (horder : 1 ≤ order) :
    (SafePalette security → ℝ) →ₗ[ℝ] Family security order where
  toFun score := RaisingChannels.bodyLeading security order horder score * OrdinaryRaising.positiveInverse security order horder
  map_add' first second := by rw [map_add, add_mul]
  map_smul' scalar score := by rw [map_smul, smul_mul_assoc, RingHom.id_apply]





theorem independentChannel_norm (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    coefficientNorm security order (independentChannel security order horder score) ≤
      (2 * BackgroundRates.bodyFactor security) * Real.sqrt ((bodyReference security).l2Sq score) := by
  have hn := familyNorm_nonneg (primaryLaw security) (bodyReference security) order _ _ (hp security) (hb security)
    (RaisingChannels.bodyLeading security order horder score)
  apply (familyNorm_product_le _ _ order _ _ (hp security) (hb security) _ _).trans
  calc
    _ ≤ coefficientNorm security order (RaisingChannels.bodyLeading security order horder score) * 2 :=
      mul_le_mul_of_nonneg_left (OrdinaryRaising.positiveInverse_bounds security order horder).1 hn
    _ ≤ (BackgroundRates.bodyFactor security * Real.sqrt ((bodyReference security).l2Sq score)) * 2 :=
      mul_le_mul_of_nonneg_right (RaisingChannels.bodyLeading_norm security order horder score) (by norm_num)
    _ = _ := by ring

def channel (security order : ℕ) (horder : 1 ≤ order) : (Input security → ℝ) →ₗ[ℝ] Family security order :=
  (independentChannel security order horder).comp (rootMean security) +
    (SelectedOrdinaryRoot.channel security order horder).comp (rootCenter security)

theorem channel_apply (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    channel security order horder score = independentChannel security order horder (rootMean security score) +
      SelectedOrdinaryRoot.channel security order horder (rootCenter security score) := rfl

theorem channel_constant (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    channel security order horder (constantRoot security score) = independentChannel security order horder score := by
  rw [channel_apply, rootMean_constant, rootCenter_constant, map_zero, add_zero]

theorem channel_on_centered (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ)
    (hcentered : ∀ center, (rootReference security).expectation (fun root => score (root, center)) = 0) :
    channel security order horder score = SelectedOrdinaryRoot.channel security order horder score := by
  rw [channel_apply, rootMean_zero_of_centered security score hcentered,
    rootCenter_eq_of_centered security score hcentered, map_zero, zero_add]









theorem independentChannel_vanishesBelow_one (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 1 (independentChannel security order horder score) := by
  apply vanishesBelow_mul _ _ order 1 0
  · apply vanishesBelow_one_of_zero
    change BackgroundFamilies.bodyFamily _ _ order horder _ _ (zeroArity order) = 0
    unfold BackgroundFamilies.bodyFamily
    rw [Pi.single_eq_of_ne]
    intro hequal
    have h := congrArg (fun arity : TruncatedArity order => arity.val.2.val) hequal
    change 0 = 1 at h
    omega
  · exact vanishesBelow_zero _ _ order _

theorem channel_vanishesBelow_one (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 1 (channel security order horder score) := by
  rw [channel_apply]
  exact vanishesBelow_add _ _ order 1 _ _ (independentChannel_vanishesBelow_one security order horder _)
    (SelectedOrdinaryRootProperties.channel_vanishesBelow_one security order horder _)





end
end CurrentAFT.SelectedOrdinaryHybrid

end


