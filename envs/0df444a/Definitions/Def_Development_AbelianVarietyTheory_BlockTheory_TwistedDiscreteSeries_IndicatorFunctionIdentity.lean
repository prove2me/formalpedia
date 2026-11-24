-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T19:38:12.677101+00:00
-- url     : https://prove2.me/theorems/b75455a4-fd61-47a4-a9c9-63d69f28f9ca
-- title:
--   Indicator Function Identity
-- statement:
--   Definitions and structural lemmas for Indicator Function Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/IndicatorFunctionIdentity.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Theorems.Thm_GlobalTheory_LatPair_FFStar_mem_EqForm
import Theorems.Thm_GlobalTheory_LatPair_FF_mem_EqForm
import Theorems.Thm_GlobalTheory_LatPair_U_mem_EqForm
import Theorems.Thm_GlobalTheory_LatPair_dia_mem_EqForm
import Theorems.Thm_GlobalTheory_LatPair_phiOne_smul
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity
open GlobalTheory.SplitWeil GlobalTheory.LatPair
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
theorem maps_std_iff (x : Matrix n n' k) :
    (∀ y ∈ stdLat k n', x *ᵥ y ∈ stdLat k n) ↔ ∀ i j, x i j ∈ 𝒪[k] := by
  constructor
  · intro H i j
    have h1 : (Pi.single j 1 : n' → k) ∈ stdLat k n' := by
      rw [mem_stdLat]
      intro l
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h2 := mem_stdLat.1 (H _ h1) i
    simpa [Matrix.mulVec_single_one] using h2
  · intro H y hy
    rw [mem_stdLat] at hy ⊢
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (H i j) (hy j)
theorem maps_smul_iff (g : GL n' k) (h : GL n k) (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k))
    (x : Matrix n n' k) :
    (∀ y ∈ g • S, x *ᵥ y ∈ h • L) ↔ ∀ y ∈ S, ((h⁻¹ : GL n k).val * x * g.val) *ᵥ y ∈ L := by
  have key : ∀ y : n' → k, ((h⁻¹ : GL n k).val * x * g.val) *ᵥ y = (h⁻¹ : GL n k) • (x *ᵥ (g • y)) := by
    intro y
    simp only [Units.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  constructor
  · intro H y hy
    rw [key, ← mem_smul_iff]
    exact H _ (Submodule.smul_mem_pointwise_smul y g S hy)
  · intro H y hy
    rw [mem_smul_iff] at hy ⊢
    have h1 := H _ hy
    rw [key, smul_inv_smul] at h1
    exact h1
lemma isCompact_isOpen_isClosed_integral_matrices : IsCompact {x : Matrix n n' k | ∀ i j, x i j ∈ 𝒪[k]} ∧
    IsOpen {x : Matrix n n' k | ∀ i j, x i j ∈ 𝒪[k]} ∧ IsClosed {x : Matrix n n' k | ∀ i j, x i j ∈ 𝒪[k]} := by
  have e : {x : Matrix n n' k | ∀ i j, x i j ∈ 𝒪[k]} =
      Set.univ.pi fun _ : n => Set.univ.pi fun _ : n' => (𝒪[k] : Set k) := by
    ext x
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  have hc : IsClosed (𝒪[k] : Set k) := (𝒪[k]).toAddSubgroup.isClosed_of_isOpen (isOpen_int k)
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int k,
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k,
    isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => hc⟩
lemma exists_sideMul_preimage_integral (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsLattice k]
    [L.IsLattice k] : ∃ (g : GL n' k) (h : GL n k), {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} =
      (sideMul g h) ⁻¹' {x : Matrix n n' k | ∀ i j, x i j ∈ 𝒪[k]} := by
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n') S
  obtain ⟨h, rfl⟩ := exists_smul_lat (stdLat k n) L
  refine ⟨g, h, ?_⟩
  ext x
  change (∀ y ∈ g • stdLat k n', x *ᵥ y ∈ h • stdLat k n) ↔
    ∀ i j, ((h⁻¹ : GL n k).val * x * g.val) i j ∈ 𝒪[k]
  rw [maps_smul_iff, maps_std_iff]
theorem hom_lat (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsLattice k] [L.IsLattice k] :
    IsCompact {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} ∧ IsOpen {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} := by
  obtain ⟨g, h, e⟩ := exists_sideMul_preimage_integral S L
  rw [e]
  exact ⟨(sideMul g h).isCompact_preimage.2 isCompact_isOpen_isClosed_integral_matrices.1, isCompact_isOpen_isClosed_integral_matrices.2.1.preimage (sideMul g h).continuous⟩
lemma phiOne_congr_of_sub_mulVec_mem_ker {P : Pair k n'} {Q : Pair k n} {x z : Matrix n n' k}
    (hz : ∀ y ∈ P.lat, (z - x) *ᵥ y ∈ Q.ker) : phiOne P Q z = phiOne P Q x := by
  have key : Maps P Q z ↔ Maps P Q x := by
    rw [maps_iff_hasVal, maps_iff_hasVal]
    refine forall_congr' fun y => forall_congr' fun a => imp_congr_right fun hy => ?_
    have hd : Q.HasVal ((z - x) *ᵥ y) 0 := Pair.mem_ker.1 (hz y hy.mem)
    rw [Matrix.sub_mulVec] at hd
    constructor
    · intro h1
      simpa using h1.sub hd
    · intro h1
      simpa using h1.add hd
  unfold phiOne
  by_cases hx : Maps P Q x
  · rw [if_pos (key.2 hx), if_pos hx]
  · rw [if_neg (mt key.1 hx), if_neg hx]
lemma isClosed_setOf_mulVec_mem (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsLattice k]
    [L.IsLattice k] : IsClosed {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} := by
  obtain ⟨g, h, e⟩ := exists_sideMul_preimage_integral S L
  rw [e]
  exact isCompact_isOpen_isClosed_integral_matrices.2.2.preimage (sideMul g h).continuous
theorem phiOne_mem (P : Pair k n') (Q : Pair k n) : phiOne P Q ∈ SB (Matrix n n' k) := by
  change IsLocallyConstant (phiOne P Q) ∧ HasCompactSupport (phiOne P Q)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hH0 : {d : Matrix n n' k | ∀ y ∈ P.lat, d *ᵥ y ∈ Q.ker} ∈ nhds (0 : Matrix n n' k) := by
      refine (hom_lat P.lat Q.ker).2.mem_nhds ?_
      intro y _
      rw [Matrix.zero_mulVec]
      exact zero_mem _
    have ht : Filter.Tendsto (fun z : Matrix n n' k => z - x) (nhds x) (nhds 0) := by
      simpa using (continuous_sub_right x).tendsto x
    filter_upwards [ht hH0] with z hz
    exact phiOne_congr_of_sub_mulVec_mem_ker hz
  · refine HasCompactSupport.intro' (hom_lat P.lat Q.lat).1 (isClosed_setOf_mulVec_mem P.lat Q.lat) fun x hx => ?_
    unfold phiOne
    rw [if_neg]
    rintro ⟨hm, -⟩
    exact hx hm
def phiOneSB (P : Pair k n') (Q : Pair k n) : SB (Matrix n n' k) := ⟨phiOne P Q, phiOne_mem P Q⟩
lemma det_mem_of_integral_entries {u : GL n k} (hu : ∀ i j, u.val i j ∈ 𝒪[k]) : u.val.det ∈ 𝒪[k] := by
  let M : Matrix n n 𝒪[k] := fun i j => ⟨u.val i j, hu i j⟩
  have e : u.val = (𝒪[k]).subtype.mapMatrix M := by
    ext i j
    rfl
  rw [e, ← RingHom.map_det]
  exact (M.det).2
theorem valuation_det_of_fix (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] {h : GL n k} (hh : h • L = L) :
    valuation k ((Matrix.GeneralLinearGroup.det h : kˣ) : k) = 1 := by
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  obtain ⟨u, hu⟩ : ∃ u : GL n k, u = g⁻¹ * h * g := ⟨_, rfl⟩
  have hfix : u • stdLat k n = stdLat k n := by
    rw [hu, mul_smul, mul_smul, hh, inv_smul_smul]
  have hint : ∀ w : GL n k, w • stdLat k n = stdLat k n → ∀ i j, w.val i j ∈ 𝒪[k] := by
    intro w hw
    refine (maps_std_iff w.val).1 ?_
    intro y hy
    have h1 : w • y ∈ w • stdLat k n := Submodule.smul_mem_pointwise_smul y w _ hy
    rw [hw] at h1
    exact h1
  have h1 := det_mem_of_integral_entries (hint u hfix)
  have h2 := det_mem_of_integral_entries (hint u⁻¹ (by rw [inv_smul_eq_iff, hfix]))
  have hdet : Matrix.GeneralLinearGroup.det u = Matrix.GeneralLinearGroup.det h := by
    rw [hu, map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det g), mul_inv_cancel_left]
  rw [← hdet, Matrix.GeneralLinearGroup.val_det_apply]
  have hp : u.val.det * (u⁻¹ : GL n k).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have v1 := (Valuation.mem_integer_iff _ _).1 h1
  have v2 := (Valuation.mem_integer_iff _ _).1 h2
  have v3 : valuation k u.val.det * valuation k (u⁻¹ : GL n k).val.det = 1 := by
    rw [← map_mul, hp, map_one]
  refine le_antisymm v1 ?_
  calc (1 : ValueGroupWithZero k) = valuation k u.val.det * valuation k (u⁻¹ : GL n k).val.det := v3.symm
    _ ≤ valuation k u.val.det * 1 := by gcongr
    _ = valuation k u.val.det := mul_one _
variable {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
def IsEquivTheta (μ : kˣ →* ℂˣ) (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V)
    (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V) : Prop :=
  ∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)),
    Ψ'.1 = om μ g h Ψ.1 → θ (π' g v) Ψ' = π h (θ v Ψ)
variable {μ : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
theorem theta_mem (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) (v : V') :
    θ v (phiOneSB P₀ Q₀) ∈ levelVec π Q₀ := by
  change ∀ h : GL n k, h • Q₀ = Q₀ → π h (θ v (phiOneSB P₀ Q₀)) = θ v (phiOneSB P₀ Q₀)
  intro h hh
  have hv : valuation k ((Matrix.GeneralLinearGroup.det h : kˣ) : k) = 1 :=
    valuation_det_of_fix Q₀.lat (by rw [← Pair.smul_lat, hh])
  have hfun : (phiOneSB P₀ Q₀).1 = om μ 1 h (phiOneSB P₀ Q₀).1 := by
    funext x
    have e1 : phiOne P₀ Q₀ x = phiOne P₀ Q₀ ((h⁻¹ : GL n k).val * x * (1 : GL n' k).val) := by
      rw [← phiOne_smul (1 : GL n' k) h, one_smul, hh]
    change phiOne P₀ Q₀ x = om μ 1 h (phiOne P₀ Q₀) x
    rw [e1]
    simp only [om, map_one, Units.val_one, hμ _ hv, inv_one, nabs_one, nabs_eq_one_of_valuation_eq_one hv,
      Real.one_rpow, Complex.ofReal_one, one_mul]
  have h1 := hθ 1 h v _ _ hfun
  simpa using h1.symm
def kerVec (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) :
    levelVec π' P₀ →ₗ[ℂ] levelVec π Q₀ :=
  LinearMap.codRestrict _ (θ.flip (phiOneSB P₀ Q₀) ∘ₗ (levelVec π' P₀).subtype)
    fun v => theta_mem hμ hθ P₀ Q₀ v.1
def K (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) :
    EqForm π' →ₗ[ℂ] EqForm π :=
  (evalEquiv π Q₀).symm.toLinearMap ∘ₗ kerVec hμ hθ P₀ Q₀ ∘ₗ (evalEquiv π' P₀).toLinearMap
theorem K_apply (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) (φ : EqForm π')
    (h : GL n k) : (K hμ hθ P₀ Q₀ φ).1 (h • Q₀) = π h (θ (φ.1 P₀) (phiOneSB P₀ Q₀)) := by
  change formOf π Q₀ (kerVec hμ hθ P₀ Q₀ (evalEquiv π' P₀ φ)) (h • Q₀) = _
  rw [formOf_smul]
  rfl
open Classical in

def midInd (q : Unif k) (L : Submodule 𝒪[k] (n' → k)) (e₁ : n' → k) (Q : Pair k n) (x : Matrix n n' k) : ℂ :=
  if (∀ y ∈ L, x *ᵥ y ∈ Q.lat) ∧ Q.HasVal (x *ᵥ (q.1 • e₁)) 1 then 1 else 0
open Classical in

def IndicatorIdentity : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n n' : Type) [Fintype n] [Fintype n'] (q : Unif k) (P₁ : Pair k n') (e₁ : n' → k) (_ : P₁.HasVal e₁ 1)
    (Q : Pair k n) (x : Matrix n n' k),
    ∑ Q₁ ∈ withKer Q.lat with cross q Q₁ Q = 1, phiOne P₁ Q₁ x = midInd q P₁.ker e₁ Q x ∧
      midInd q P₁.ker e₁ Q x = ∑ P ∈ withLat P₁.ker with cross q P₁ P = 1, phiOne P Q x
def scal (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) : ℂ :=
  (((resCard k : ℝ) ^ (((t : ℝ) + 1) / 2) : ℝ) : ℂ)
def OperatorRules : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (t : ℕ)
    (_ : Fintype.card n = Fintype.card n' + (t + 1))
    (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1)
    (μ : kˣ →* ℂˣ) (hμ : IsUnram μ) (_ : ∀ x, ‖(μ x : ℂ)‖ = 1)
    (V' V : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
    (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V) (_ : IsSmoothRep π') (_ : IsSmoothRep π)
    (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n),
    (∀ φ : EqForm π', U q (K hμ hθ P₀ Q₀ φ).1 =
      scal k t • (K hμ hθ P₀ Q₀ ⟨U q φ.1, U_mem_EqForm q φ.2⟩).1) ∧
    (∀ (s : 𝓀[k]ˣ) (φ : EqForm π'), (K hμ hθ P₀ Q₀ ⟨dia s φ.1, dia_mem_EqForm s φ.2⟩).1 =
      dia s (K hμ hθ P₀ Q₀ φ).1) ∧
    (∀ φ : EqForm π', φ.1 ∈ Mram k n' V' →
      (K hμ hθ P₀ Q₀ φ).1 ∈ Mram k n V ∧
      FF q (resChar ψ hψ q) (K hμ hθ P₀ Q₀ φ).1 =
        scal k t • (K hμ hθ P₀ Q₀ ⟨FF q (resChar ψ hψ q) φ.1, FF_mem_EqForm q _ φ.2⟩).1 ∧
      FFStar q (resChar ψ hψ q) (K hμ hθ P₀ Q₀ φ).1 =
        scal k t • (K hμ hθ P₀ Q₀ ⟨FFStar q (resChar ψ hψ q) φ.1, FFStar_mem_EqForm q _ φ.2⟩).1)
def KernelsCommute : Prop := IndicatorIdentity ∧ OperatorRules
example (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) (φ : EqForm π') :
    (K hμ hθ P₀ Q₀ φ).1 Q₀ = θ (φ.1 P₀) (phiOneSB P₀ Q₀) := by
  simpa using K_apply hμ hθ P₀ Q₀ φ 1
example (t : ℕ) : scal k t ^ 2 = (resCard k : ℂ) ^ (t + 1) := by
  rw [scal, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  rw [show ((t : ℝ) + 1) / 2 * (2 : ℕ) = ((t + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  push_cast
  rfl
end GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity


