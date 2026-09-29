-- Prove2me | solution 1 for AutomorphicForm.exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8055853c-e8ed-5ac5-966d-447a41024069

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_NumberField_PlaceTransport_transport_adicCompletionSemialgHom
import Theorems.Thm_NumberField_PlaceTransport_exists_pow_smul_eq_of_forall_mem_zpowers
import Theorems.Thm_NumberField_PlaceTransport_under_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions NumberField.PlaceTransport

noncomputable section

namespace SemiLocalGaloisStructure

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

def pl (k : ℕ) : v.Extension (𝓞 L) :=
  ⟨(σ ^ k)⁻¹ • w.1, by rw [NumberField.PlaceTransport.under_smul K L]; exact w.2⟩

theorem pl_val (k : ℕ) : (pl K L σ v w k).1 = (σ ^ k)⁻¹ • w.1 := rfl

theorem smul_pl (k : ℕ) : (σ ^ k) • (pl K L σ v w k).1 = w.1 := smul_inv_smul _ _

theorem pl_zero : pl K L σ v w 0 = w := by
  apply Subtype.ext
  rw [pl_val, pow_zero, inv_one, one_smul]

variable {K L σ v w}

theorem pow_mul_smul {r : ℕ} (hper : (σ ^ r) • w.1 = w.1) (q : ℕ) : (σ ^ (r * q)) • w.1 = w.1 := by
  induction q with
  | zero => rw [mul_zero, pow_zero, one_smul]
  | succ q ih => rw [Nat.mul_succ, pow_add, mul_smul, hper, ih]

theorem pl_add_mul {r : ℕ} (hper : (σ ^ r) • w.1 = w.1) (k q : ℕ) :
    pl K L σ v w (k + r * q) = pl K L σ v w k := by
  apply Subtype.ext
  rw [pl_val, pl_val, add_comm, pow_add, mul_inv_rev, mul_smul]
  congr 1
  rw [inv_smul_eq_iff, pow_mul_smul hper]

theorem pl_mod {r : ℕ} (hper : (σ ^ r) • w.1 = w.1) (k : ℕ) :
    pl K L σ v w (k % r) = pl K L σ v w k := by
  conv_rhs => rw [← Nat.mod_add_div k r]
  exact (pl_add_mul hper (k % r) (k / r)).symm

theorem pl_injective {m : ℕ} (hmin : ∀ k, 0 < k → k ≤ m → (σ ^ k) • w.1 ≠ w.1) :
    Function.Injective fun j : Fin (m + 1) => pl K L σ v w j := by
  have key : ∀ i j : Fin (m + 1), (i : ℕ) ≤ j → pl K L σ v w i = pl K L σ v w j → i = j := by
    intro i j hij h
    have h1 : (σ ^ ((j : ℕ) - i)) • w.1 = w.1 := by
      have h2 := congrArg Subtype.val h
      rw [pl_val, pl_val] at h2
      rw [pow_sub _ hij, mul_smul, h2, smul_inv_smul]
    by_contra hne
    have hlt : (i : ℕ) < j := lt_of_le_of_ne hij fun h' => hne (Fin.ext h')
    exact hmin _ (Nat.sub_pos_of_lt hlt) (by omega) h1
  intro i j h
  rcases le_total (i : ℕ) j with hij | hji
  · exact key i j hij h
  · exact (key j i hji h.symm).symm

theorem pl_surjective [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hper : (σ ^ (m + 1)) • w.1 = w.1) :
    Function.Surjective fun j : Fin (m + 1) => pl K L σ v w j := by
  intro q
  obtain ⟨n, hn⟩ := NumberField.PlaceTransport.exists_pow_smul_eq_of_forall_mem_zpowers K L σ hgen v q w
  refine ⟨⟨n % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩, ?_⟩
  show pl K L σ v w (n % (m + 1)) = q
  rw [pl_mod hper]
  apply Subtype.ext
  rw [pl_val, eq_comm, eq_inv_smul_iff, hn]

def plEquiv [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hper : (σ ^ (m + 1)) • w.1 = w.1) (hmin : ∀ k, 0 < k → k ≤ m → (σ ^ k) • w.1 ≠ w.1) :
    Fin (m + 1) ≃ v.Extension (𝓞 L) :=
  Equiv.ofBijective (fun j : Fin (m + 1) => pl K L σ v w j) ⟨pl_injective hmin, pl_surjective hgen hper⟩

theorem plEquiv_apply [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hper : (σ ^ (m + 1)) • w.1 = w.1) (hmin : ∀ k, 0 < k → k ≤ m → (σ ^ k) • w.1 ≠ w.1) (j : Fin (m + 1)) :
    plEquiv hgen hper hmin j = pl K L σ v w j := rfl

variable (K L σ v w)

theorem exists_period : ∃ m : ℕ, (σ ^ (m + 1)) • w.1 = w.1 ∧ ∀ k, 0 < k → k ≤ m → (σ ^ k) • w.1 ≠ w.1 := by
  classical
  have hex : ∃ k, 0 < k ∧ (σ ^ k) • w.1 = w.1 :=
    ⟨orderOf σ, orderOf_pos σ, by rw [pow_orderOf_eq_one, one_smul]⟩
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · rw [Nat.sub_add_cancel (Nat.find_spec hex).1]
    exact (Nat.find_spec hex).2
  · intro k hk hkm h
    have hlt : k < Nat.find hex := by
      have := (Nat.find_spec hex).1
      omega
    exact Nat.find_min hex hlt ⟨hk, h⟩

theorem transport_algebraMap (g : L ≃ₐ[K] L) {q q' : HeightOneSpectrum (𝓞 L)} (h : g • q = q') (x : L) :
    NumberField.PlaceTransport.transport g h (algebraMap L (q.adicCompletion L) x) =
      algebraMap L (q'.adicCompletion L) (g x) := by
  rw [show algebraMap L (q.adicCompletion L) x =
      ((WithVal.toVal (q.valuation L) x : WithVal (q.valuation L)) : q.adicCompletion L) from rfl,
    NumberField.PlaceTransport.transport_coe, WithVal.congr_apply]
  rfl

def T (k : ℕ) : (pl K L σ v w k).1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L :=
  AlgEquiv.ofRingEquiv (f := NumberField.PlaceTransport.transport (σ ^ k) (smul_pl K L σ v w k)) fun y =>
    NumberField.PlaceTransport.transport_adicCompletionSemialgHom K L (σ ^ k) (pl K L σ v w k) w
      (smul_pl K L σ v w k) y

theorem T_apply (k : ℕ) (y : (pl K L σ v w k).1.adicCompletion L) :
    T K L σ v w k y = NumberField.PlaceTransport.transport (σ ^ k) (smul_pl K L σ v w k) y := rfl

theorem T_algebraMap (k : ℕ) (x : L) :
    T K L σ v w k (algebraMap L _ x) = algebraMap L (w.1.adicCompletion L) ((σ ^ k) x) := by
  rw [T_apply, transport_algebraMap]

theorem T_mem_integers_iff (k : ℕ) (y : (pl K L σ v w k).1.adicCompletion L) :
    T K L σ v w k y ∈ w.1.adicCompletionIntegers L ↔ y ∈ (pl K L σ v w k).1.adicCompletionIntegers L := by
  rw [T_apply]
  exact NumberField.PlaceTransport.transport_mem_adicCompletionIntegers_iff _ _ y

variable {K L σ v w}

def theta {m : ℕ} (hper : (σ ^ (m + 1)) • w.1 = w.1) :
    w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L :=
  AlgEquiv.ofRingEquiv (f := NumberField.PlaceTransport.transport (σ ^ (m + 1)) hper) fun y =>
    NumberField.PlaceTransport.transport_adicCompletionSemialgHom K L (σ ^ (m + 1)) w w hper y

theorem theta_apply {m : ℕ} (hper : (σ ^ (m + 1)) • w.1 = w.1) (y : w.1.adicCompletion L) :
    theta hper y = NumberField.PlaceTransport.transport (σ ^ (m + 1)) hper y := rfl

theorem theta_algebraMap {m : ℕ} (hper : (σ ^ (m + 1)) • w.1 = w.1) (x : L) :
    theta hper (algebraMap L _ x) = algebraMap L (w.1.adicCompletion L) ((σ ^ (m + 1)) x) := by
  rw [theta_apply, transport_algebraMap]

theorem valued_theta {m : ℕ} (hper : (σ ^ (m + 1)) • w.1 = w.1) (y : w.1.adicCompletion L) :
    Valued.v (theta hper y) = Valued.v y := by
  rw [theta_apply]
  exact NumberField.PlaceTransport.valued_transport _ _ y

theorem theta_pow_algebraMap {m : ℕ} (hper : (σ ^ (m + 1)) • w.1 = w.1) (k : ℕ) (x : L) :
    (theta hper ^ k) (algebraMap L _ x) = algebraMap L (w.1.adicCompletion L) ((σ ^ ((m + 1) * k)) x) := by
  induction k with
  | zero => rw [pow_zero, mul_zero, pow_zero, AlgEquiv.one_apply, AlgEquiv.one_apply]
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, theta_algebraMap, ← AlgEquiv.mul_apply, ← pow_add,
      show (m + 1) + (m + 1) * k = (m + 1) * (k + 1) by ring]

theorem algEquiv_eq_one_of_forall_algebraMap (f : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hf : ∀ x : L, f (algebraMap L _ x) = algebraMap L _ x) : f = 1 := by
  apply AlgEquiv.ext
  intro y
  have hc : Continuous f := IsModuleTopology.continuous_of_linearMap f.toLinearEquiv.toLinearMap
  obtain ⟨y⟩ := y
  refine UniformSpace.Completion.induction_on
    (p := fun y => f (HeightOneSpectrum.adicCompletion.ofCompletion y) = (1 : _ ≃ₐ[_] _) (HeightOneSpectrum.adicCompletion.ofCompletion y)) y ?_ ?_
  · exact isClosed_eq (hc.comp (HeightOneSpectrum.adicCompletion.continuous_ofCompletion (K := L) (v := w.1)))
      (HeightOneSpectrum.adicCompletion.continuous_ofCompletion (K := L) (v := w.1))
  · intro a
    have ha : (a : w.1.adicCompletion L) = algebraMap L (w.1.adicCompletion L) a.ofVal := rfl
    rw [ha, AlgEquiv.one_apply]
    exact hf _

theorem theta_pow_eq_one_iff {m : ℕ} (hper : (σ ^ (m + 1)) • w.1 = w.1) (k : ℕ) :
    theta hper ^ k = 1 ↔ σ ^ ((m + 1) * k) = 1 := by
  constructor
  · intro h
    apply AlgEquiv.ext
    intro x
    have h1 := theta_pow_algebraMap hper k x
    rw [h, AlgEquiv.one_apply] at h1
    exact ((algebraMap L (w.1.adicCompletion L)).injective h1).symm
  · intro h
    apply algEquiv_eq_one_of_forall_algebraMap
    intro x
    rw [theta_pow_algebraMap, h, AlgEquiv.one_apply]

theorem succ_dvd_orderOf {m : ℕ} (hper : (σ ^ (m + 1)) • w.1 = w.1)
    (hmin : ∀ k, 0 < k → k ≤ m → (σ ^ k) • w.1 ≠ w.1) : (m + 1) ∣ orderOf σ := by
  have h1 : (σ ^ (orderOf σ % (m + 1))) • w.1 = w.1 := by
    have h2 : (σ ^ orderOf σ) • w.1 = w.1 := by rw [pow_orderOf_eq_one, one_smul]
    conv_lhs at h2 => rw [← Nat.mod_add_div (orderOf σ) (m + 1), pow_add, mul_smul, pow_mul_smul hper]
    exact h2
  by_contra hnd
  have hpos : 0 < orderOf σ % (m + 1) := Nat.pos_of_ne_zero fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
  exact hmin _ hpos (Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos m))) h1

theorem orderOf_theta {m : ℕ} (hper : (σ ^ (m + 1)) • w.1 = w.1)
    (hmin : ∀ k, 0 < k → k ≤ m → (σ ^ k) • w.1 ≠ w.1) :
    orderOf (theta hper) = orderOf σ / (m + 1) := by
  set f := orderOf σ / (m + 1) with hf
  have hn : orderOf σ = (m + 1) * f := (Nat.mul_div_cancel' (succ_dvd_orderOf hper hmin)).symm
  have key : ∀ k, theta hper ^ k = 1 ↔ f ∣ k := by
    intro k
    rw [theta_pow_eq_one_iff, ← orderOf_dvd_iff_pow_eq_one, hn]
    exact Nat.mul_dvd_mul_iff_left (Nat.succ_pos m)
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((key f).2 dvd_rfl)
  · exact (key _).1 (pow_orderOf_eq_one _)

section Coordinates

variable (K L v)

scoped instance freeLq (q : v.Extension (𝓞 L)) : Module.Free (v.adicCompletion K) (q.1.adicCompletion L) :=
  Module.Free.of_divisionRing _ _

def Phi : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (Π q : v.Extension (𝓞 L), q.1.adicCompletion L) :=
  AlgEquiv.ofRingEquiv (f := (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toRingEquiv)
    (fun s => by
      funext q
      change HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v ((1 : L) ⊗ₜ[K] s) q = _
      rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul, Pi.algebraMap_apply])

theorem Phi_apply (z : L ⊗[K] v.adicCompletion K) :
    Phi K L v z = HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v z := rfl

theorem Phi_tmul (x : L) (y : v.adicCompletion K) (q : v.Extension (𝓞 L)) :
    Phi K L v (x ⊗ₜ[K] y) q = algebraMap L _ x * algebraMap (v.adicCompletion K) _ y := by
  rw [Phi_apply, HeightOneSpectrum.adicCompletion.baseChange_tmul_apply]

variable (σ w)

def psi (m : ℕ) : (L ⊗[K] v.adicCompletion K) →ₐ[v.adicCompletion K] (Fin (m + 1) → w.1.adicCompletion L) :=
  Pi.algHom (v.adicCompletion K) (fun _ : Fin (m + 1) => w.1.adicCompletion L) fun j : Fin (m + 1) =>
    ((T K L σ v w j).toAlgHom.comp
      (Pi.evalAlgHom (v.adicCompletion K) (fun q : v.Extension (𝓞 L) => q.1.adicCompletion L)
        (pl K L σ v w j))).comp (Phi K L v).toAlgHom

theorem psi_apply (m : ℕ) (z : L ⊗[K] v.adicCompletion K) (j : Fin (m + 1)) :
    psi K L σ v w m z j = T K L σ v w j (Phi K L v z (pl K L σ v w j)) := rfl

theorem psi_tmul (m : ℕ) (x : L) (y : v.adicCompletion K) (j : Fin (m + 1)) :
    psi K L σ v w m (x ⊗ₜ[K] y) j =
      algebraMap L (w.1.adicCompletion L) ((σ ^ (j : ℕ)) x) * algebraMap (v.adicCompletion K) _ y := by
  rw [psi_apply, Phi_tmul, map_mul, T_algebraMap, AlgEquiv.commutes]

variable {K L σ v w}

theorem psi_injective [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hper : (σ ^ (m + 1)) • w.1 = w.1) : Function.Injective (psi K L σ v w m) := by
  intro z z' h
  apply (Phi K L v).injective
  funext q
  obtain ⟨j, rfl⟩ := pl_surjective hgen hper q
  have hj := congrFun h j
  rw [psi_apply, psi_apply] at hj
  exact (T K L σ v w j).injective hj

theorem finrank_pi_eq [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hper : (σ ^ (m + 1)) • w.1 = w.1) (hmin : ∀ k, 0 < k → k ≤ m → (σ ^ k) • w.1 ≠ w.1) :
    Module.finrank (v.adicCompletion K) (Π q : v.Extension (𝓞 L), q.1.adicCompletion L) =
      Module.finrank (v.adicCompletion K) (Fin (m + 1) → w.1.adicCompletion L) := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  letI : Fintype (v.Extension (𝓞 L)) := Fintype.ofFinite _
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  symm
  apply Fintype.sum_equiv (plEquiv hgen hper hmin)
  intro j
  rw [plEquiv_apply]
  exact ((T K L σ v w j).toLinearEquiv.finrank_eq).symm

theorem psi_bijective [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hper : (σ ^ (m + 1)) • w.1 = w.1) (hmin : ∀ k, 0 < k → k ≤ m → (σ ^ k) • w.1 ≠ w.1) :
    Function.Bijective (psi K L σ v w m) := by
  refine ⟨psi_injective hgen hper, ?_⟩
  have hrank : Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) =
      Module.finrank (v.adicCompletion K) (Fin (m + 1) → w.1.adicCompletion L) := by
    rw [(Phi K L v).toLinearEquiv.finrank_eq, finrank_pi_eq hgen hper hmin]
  have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
    (f := (psi K L σ v w m).toLinearMap)).1 (psi_injective hgen hper)
  exact this

def Psi [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hper : (σ ^ (m + 1)) • w.1 = w.1) (hmin : ∀ k, 0 < k → k ≤ m → (σ ^ k) • w.1 ≠ w.1) :
    (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (Fin (m + 1) → w.1.adicCompletion L) :=
  AlgEquiv.ofBijective (psi K L σ v w m) (psi_bijective hgen hper hmin)

theorem Psi_apply [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hper : (σ ^ (m + 1)) • w.1 = w.1) (hmin : ∀ k, 0 < k → k ≤ m → (σ ^ k) • w.1 ≠ w.1)
    (z : L ⊗[K] v.adicCompletion K) : Psi hgen hper hmin z = psi K L σ v w m z := rfl

end Coordinates

section Properties

variable [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {m : ℕ}
  (hper : (σ ^ (m + 1)) • w.1 = w.1) (hmin : ∀ k, 0 < k → k ≤ m → (σ ^ k) • w.1 ≠ w.1)

include hgen hper hmin

theorem Psi_sigmaTensor (z : L ⊗[K] v.adicCompletion K) :
    (∀ k : Fin m, Psi hgen hper hmin (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) k.castSucc =
        Psi hgen hper hmin z k.succ) ∧
      Psi hgen hper hmin (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) (Fin.last m) =
        theta hper (Psi hgen hper hmin z 0) := by
  simp only [Psi_apply]
  induction z using TensorProduct.induction_on with
  | zero =>
    refine ⟨fun k => ?_, ?_⟩
    · rw [map_zero, map_zero, Pi.zero_apply, Pi.zero_apply]
    · rw [map_zero, map_zero, Pi.zero_apply, Pi.zero_apply, map_zero]
  | tmul x y =>
    have hσ : AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ (x ⊗ₜ[K] y) = σ x ⊗ₜ[K] y := by
      simp [AutomorphicForm.sigmaTensor]
    refine ⟨fun k => ?_, ?_⟩
    · rw [hσ, psi_tmul, psi_tmul, Fin.val_castSucc, Fin.val_succ, pow_succ, AlgEquiv.mul_apply]
    · rw [hσ, psi_tmul, psi_tmul, Fin.val_last, Fin.val_zero, pow_zero, AlgEquiv.one_apply, map_mul,
        theta_algebraMap, AlgEquiv.commutes, pow_succ, AlgEquiv.mul_apply]
  | add z z' hz hz' =>
    refine ⟨fun k => ?_, ?_⟩
    · rw [map_add, map_add, Pi.add_apply, hz.1 k, hz'.1 k, map_add, Pi.add_apply]
    · rw [map_add, map_add, Pi.add_apply, hz.2, hz'.2, map_add, Pi.add_apply, map_add]

theorem Psi_tmul_one (x : L) (j : Fin (m + 1)) :
    Psi hgen hper hmin (x ⊗ₜ[K] (1 : v.adicCompletion K)) j = algebraMap L (w.1.adicCompletion L) ((σ ^ (j : ℕ)) x) := by
  rw [Psi_apply, psi_tmul, map_one, mul_one]

theorem mem_semiLocalIntegers_iff (z : L ⊗[K] v.adicCompletion K) :
    z ∈ AutomorphicForm.semiLocalIntegers K L v ↔ ∀ j, Psi hgen hper hmin z j ∈ w.1.adicCompletionIntegers L := by
  have hrange := HeightOneSpectrum.range_baseChange_comp_tensorAdicCompletionTo_eq_pi K L (𝓞 L) v
  have hinj : Function.Injective (HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v) :=
    (HeightOneSpectrum.adicCompletion.baseChange_bijective K L (𝓞 L) v).1
  have h1 : z ∈ AutomorphicForm.semiLocalIntegers K L v ↔
      ∀ q : v.Extension (𝓞 L), Phi K L v z q ∈ q.1.adicCompletionIntegers L := by
    constructor
    · rintro ⟨u, rfl⟩ q
      have hu : (HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v ∘
          HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v) u ∈
          Set.univ.pi (fun q : v.Extension (𝓞 L) => (q.1.adicCompletionIntegers L).carrier) := by
        rw [← hrange]; exact Set.mem_range_self u
      exact hu q (Set.mem_univ q)
    · intro h
      have hz : Phi K L v z ∈
          Set.univ.pi (fun q : v.Extension (𝓞 L) => (q.1.adicCompletionIntegers L).carrier) :=
        fun q _ => h q
      rw [← hrange] at hz
      obtain ⟨u, hu⟩ := hz
      exact ⟨u, hinj hu⟩
  rw [h1]
  constructor
  · intro h j
    rw [Psi_apply, psi_apply, T_mem_integers_iff]
    exact h _
  · intro h q
    obtain ⟨j, rfl⟩ := pl_surjective hgen hper q
    have hj := h j
    rw [Psi_apply, psi_apply, T_mem_integers_iff] at hj
    exact hj

theorem succ_mul_finrank_eq :
    (m + 1) * Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L := by
  have h1 : Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) = Module.finrank K L :=
    TensorProduct.finrank_rightAlgebra L
  rw [← h1, (Psi hgen hper hmin).toLinearEquiv.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem orderOf_theta_eq_finrank :
    orderOf (theta hper) = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  rw [orderOf_theta hper hmin, orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank,
    ← succ_mul_finrank_eq hgen hper hmin, Nat.mul_div_cancel_left _ (Nat.succ_pos m)]

theorem theta_apply_eq_self_iff (y : w.1.adicCompletion L) :
    theta hper y = y ↔ y ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)) := by
  constructor
  · intro hy
    classical
    have hf := orderOf_theta_eq_finrank hgen hper hmin
    have hpos : 0 < Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := Module.finrank_pos

    have hcard_le : Nat.card (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) ≤
        Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
      rw [Nat.card_eq_fintype_card]; exact AlgEquiv.card_le
    have hcard_ge : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) ≤
        Nat.card (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) := by
      rw [← hf, ← Nat.card_zpowers]
      exact Nat.card_le_card_of_injective _ (Subgroup.subtype_injective _)
    have hcard := le_antisymm hcard_le hcard_ge
    haveI : IsGalois (v.adicCompletion K) (w.1.adicCompletion L) := IsGalois.of_card_aut_eq_finrank _ _ hcard
    have htop : Subgroup.zpowers (theta hper) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hf, hcard]
    have hstab : ∀ g : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L, g y = y := by
      intro g
      have hg : g ∈ MulAction.stabilizer (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) y := by
        have hle : Subgroup.zpowers (theta hper) ≤
            MulAction.stabilizer (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) y :=
          Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hy)
        rw [htop] at hle
        exact hle (Subgroup.mem_top g)
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hg
      exact hg
    have hmem : y ∈ IntermediateField.fixedField
        (⊤ : Subgroup (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)) :=
      (IntermediateField.mem_fixedField_iff _ _).2 fun g _ => hstab g
    rw [IsGalois.fixedField_top] at hmem
    exact IntermediateField.mem_bot.1 hmem
  · rintro ⟨s, rfl⟩
    exact (theta hper).commutes s

theorem natCard_extension : Nat.card (v.Extension (𝓞 L)) = m + 1 := by
  rw [← Nat.card_congr (plEquiv hgen hper hmin), Nat.card_eq_fintype_card, Fintype.card_fin]

end Properties

theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) :
    ∃ (m : ℕ) (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
      (Ψ : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (Fin (m + 1) → w.1.adicCompletion L)),
      (∀ z : L ⊗[K] v.adicCompletion K,
        (∀ k : Fin m, Ψ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) k.castSucc = Ψ z k.succ) ∧
          Ψ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) (Fin.last m) = θ (Ψ z 0)) ∧
      (∀ z : L ⊗[K] v.adicCompletion K,
        z ∈ AutomorphicForm.semiLocalIntegers K L v ↔ ∀ j, Ψ z j ∈ w.1.adicCompletionIntegers L) ∧
      (∀ (x : L) (j : Fin (m + 1)),
        Ψ (x ⊗ₜ[K] (1 : v.adicCompletion K)) j = algebraMap L (w.1.adicCompletion L) ((σ ^ (j : ℕ)) x)) ∧
      orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) ∧
      (∀ y : w.1.adicCompletion L,
        θ y = y ↔ y ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))) ∧
      (∀ y : w.1.adicCompletion L, Valued.v (θ y) = Valued.v y) ∧
      (m + 1) * Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L ∧
      Nat.card (v.Extension (𝓞 L)) = m + 1 := by
  obtain ⟨m, hper, hmin⟩ := exists_period K L σ v w
  exact ⟨m, theta hper, Psi hgen hper hmin, Psi_sigmaTensor hgen hper hmin, mem_semiLocalIntegers_iff hgen hper hmin,
    Psi_tmul_one hgen hper hmin, orderOf_theta_eq_finrank hgen hper hmin, theta_apply_eq_self_iff hgen hper hmin,
    valued_theta hper, succ_mul_finrank_eq hgen hper hmin, natCard_extension hgen hper hmin⟩

end SemiLocalGaloisStructure
p2m_reactivate "P2MW.S_AutomorphicForm_exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers.SemiLocalGaloisStructure"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers.SemiLocalGaloisStructure"

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) :
    ∃ (m : ℕ) (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
      (Ψ : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] (Fin (m + 1) → w.1.adicCompletion L)),
      (∀ z : L ⊗[K] v.adicCompletion K,
        (∀ k : Fin m, Ψ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) k.castSucc = Ψ z k.succ) ∧
          Ψ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ z) (Fin.last m) = θ (Ψ z 0)) ∧
      (∀ z : L ⊗[K] v.adicCompletion K,
        z ∈ AutomorphicForm.semiLocalIntegers K L v ↔ ∀ j, Ψ z j ∈ w.1.adicCompletionIntegers L) ∧
      (∀ (x : L) (j : Fin (m + 1)),
        Ψ (x ⊗ₜ[K] (1 : v.adicCompletion K)) j = algebraMap L (w.1.adicCompletion L) ((σ ^ (j : ℕ)) x)) ∧
      orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) ∧
      (∀ y : w.1.adicCompletion L,
        θ y = y ↔ y ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))) ∧
      (∀ y : w.1.adicCompletion L, Valued.v (θ y) = Valued.v y) ∧
      (m + 1) * Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L ∧
      Nat.card (v.Extension (𝓞 L)) = m + 1 :=
  SemiLocalGaloisStructure.main K L σ hgen v w

end S_AutomorphicForm_exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers
end P2MW
export P2MW.S_AutomorphicForm_exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers (solution)
