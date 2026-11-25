-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:22.716135+00:00
-- url     : https://prove2.me/theorems/3f9b31b1-f1e2-46c8-b390-2de1b718081c
-- title:
--   Statements Rest
-- statement:
--   Definitions and structural lemmas for Statements Rest, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsRest.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_F_eq_cb105611b658
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_J_eq_083d9017b1ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_decomp_c8d39b1d7eb7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_fib_eq_3eb15ec2cff6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_mu_eq_f35e2c531be1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isFlagIntegral_one_1b5265d8358b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
def restRename (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) :
    MvPolynomial (Fin f × Fin N) ℝ →ₐ[ℝ] RootPoly f j k :=
  rename fun p => (p.1, e p.2)
def restTransport (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) :
    RestTerms.RootRing f N →+* RootPoly f j k :=
  (restRename f j k N e).toRingHom.comp (map (algebraMap ℚ ℝ))
def realFlagIntegral (f N : ℕ) (P : MvPolynomial (Fin f × Fin N) ℝ) : ℝ :=
  ∑ α ∈ (RestTerms.blockVandermonde f N).support,
    coeff α P * ((coeff α (RestTerms.blockVandermonde f N) *
      α.prod (fun _ e => (e.factorial : ℚ)) : ℚ) : ℝ)
def restStair (f N : ℕ) : RestTerms.RootRing f N :=
  ∏ τ : Fin f, ∏ i : Fin N, X (τ, i) ^ (i : ℕ)
def restPsumIdeal (f N : ℕ) : Ideal (RestTerms.RootRing f N) :=
  Ideal.span {P | ∃ k τ, 1 ≤ k ∧ k ≤ N ∧ P = RestTerms.blockPowerSum f N k τ}
def restCompareConst (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (I : RootPoly f j k →ₗ[ℝ] ℝ) : ℝ :=
  I (restTransport f j k N e (restStair f N)) / (RestTerms.flagIntegral f N (restStair f N) : ℝ)
def restLastEquiv (j k : ℕ) : Fin (k + j) ≃ Fin j ⊕ Fin k :=
  (finCongr (Nat.add_comm k j)).trans finSumFinEquiv.symm
def restFirstEquiv (j k : ℕ) : Fin (j + k) ≃ Fin j ⊕ Fin k :=
  finSumFinEquiv.symm
def RestCutTransportPsum.Statement : Prop :=
  ∀ (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (m : ℕ) (τ : Fin f),
    restTransport f j k N e (RestTerms.blockPowerSum f N m τ) = rootPsum f j k m τ
def RestCutTransportLast.Statement : Prop :=
  ∀ f j k : ℕ, k ≤ j →
    restTransport f j k (k + j) (restLastEquiv j k)
        (RestTerms.restPolynomial f k j .last) = restInput f j k ∧
      restTransport f j k (k + j) (restLastEquiv j k)
        (RestTerms.smallBlockMu f k j .last ^ (f * (k * j)) * RestTerms.fibreClass f k j .last) =
        degreeInput f j k
def RestCutTransportFirst.Statement : Prop :=
  ∀ f j k : ℕ, j < k →
    restTransport f j k (j + k) (restFirstEquiv j k)
        (RestTerms.restPolynomial f j k .first) = restInput f j k ∧
      restTransport f j k (j + k) (restFirstEquiv j k)
        (RestTerms.smallBlockMu f j k .first ^ (f * (j * k)) * RestTerms.fibreClass f j k .first) =
        degreeInput f j k
def RestCutLieLast.Statement : Prop :=
  ∀ f j k : ℕ, k ≤ j → ∀ (m : ℕ) (σ : Fin f × Bool), ∃ ε : ℚ, ∃ δ : ℝ, (ε = 1 ∨ ε = -1) ∧
    lieClass f j k m σ =
      C (ε : ℝ) * restTransport f j k (k + j) (restLastEquiv j k)
          (RestTerms.smallPowerSum f k j .last m σ.1) + C δ * rootPsum f j k m σ.1
def RestCutLieFirst.Statement : Prop :=
  ∀ f j k : ℕ, j < k → ∀ (m : ℕ) (σ : Fin f × Bool), ∃ ε : ℚ, ∃ δ : ℝ, (ε = 1 ∨ ε = -1) ∧
    lieClass f j k m σ =
      C (ε : ℝ) * restTransport f j k (j + k) (restFirstEquiv j k)
          (RestTerms.smallPowerSum f j k .first m σ.1) + C δ * rootPsum f j k m σ.1
def RestCutStairHom.Statement : Prop :=
  ∀ f N : ℕ, (restStair f N).IsHomogeneous (RestTerms.topDegree f N)
def RestCutRestHom.Statement : Prop :=
  ∀ (f r a : ℕ) (c : RestTerms.SmallBlock),
    (RestTerms.smallBlockMu f r a c ^ (f * (r * a)) * RestTerms.fibreClass f r a c).IsHomogeneous
        (RestTerms.topDegree f (r + a)) ∧
      (RestTerms.restPolynomial f r a c).IsHomogeneous (RestTerms.topDegree f (r + a) + 1)
def RestCutHomDecomp.Statement : Prop :=
  ∀ (f N : ℕ) (F : RestTerms.RootRing f N) (Q : ℕ → Fin f → RestTerms.RootRing f N) (d : ℕ),
    RestTerms.IsPowerSumDecomposition f N F Q → F.IsHomogeneous d → N ≤ d →
      RestTerms.IsPowerSumDecomposition f N F fun l σ => homogeneousComponent (d - l) (Q l σ)
def RestCutIdealSum.Statement : Prop :=
  ∀ (f N : ℕ) (A : RestTerms.RootRing f N), A ∈ restPsumIdeal f N →
    ∃ G : Fin N × Fin f → RestTerms.RootRing f N,
      A = ∑ i, RestTerms.blockPowerSum f N ((i.1 : ℕ) + 1) i.2 * G i
def RestCutFlagKillsIdeal.Statement : Prop :=
  ∀ (f N : ℕ) (A : RestTerms.RootRing f N), A ∈ restPsumIdeal f N →
    RestTerms.flagIntegral f N A = 0
def RestCutIKillsIdeal.Statement : Prop :=
  ∀ (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (I : RootPoly f j k →ₗ[ℝ] ℝ),
    IsFlagIntegral f j k I → ∀ A ∈ restPsumIdeal f N, A.IsHomogeneous (flagDim f j k) →
      I (restTransport f j k N e A) = 0
def RestCutStairNonzero.Statement : Prop :=
  ∀ (f N : ℕ) (H : RestTerms.RootRing f N), H.IsHomogeneous (RestTerms.topDegree f N) →
    RestTerms.flagIntegral f N H ≠ 0 → RestTerms.flagIntegral f N (restStair f N) ≠ 0
def RestCutCompare.Statement : Prop :=
  ∀ (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (I : RootPoly f j k →ₗ[ℝ] ℝ),
    IsFlagIntegral f j k I → RestTerms.flagIntegral f N (restStair f N) ≠ 0 →
    ∀ H : RestTerms.RootRing f N, H.IsHomogeneous (flagDim f j k) →
      I (restTransport f j k N e H) =
        restCompareConst f j k N e I * RestTerms.flagIntegral f N H
def RestCutCompareReal.Statement : Prop :=
  ∀ (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (I : RootPoly f j k →ₗ[ℝ] ℝ) (c : ℝ) (d : ℕ),
    (∀ H : RestTerms.RootRing f N, H.IsHomogeneous d →
      I (restTransport f j k N e H) = c * RestTerms.flagIntegral f N H) →
    ∀ P : MvPolynomial (Fin f × Fin N) ℝ, P.IsHomogeneous d →
      I (restRename f j k N e P) = c * realFlagIntegral f N P
def RestCutPsiFlag.Statement : Prop :=
  ∀ f N : ℕ,
    (∀ H : RestTerms.RootRing f N,
      realFlagIntegral f N (map (algebraMap ℚ ℝ) H) = (RestTerms.flagIntegral f N H : ℝ)) ∧
    ∀ (ψ : ℝ →ₗ[ℚ] ℚ) (P : MvPolynomial (Fin f × Fin N) ℝ),
      ψ (realFlagIntegral f N P) = RestTerms.flagIntegral f N (KRest.psiPoly ψ P)
def RestCutRealSyzygy.Statement : Prop :=
  ∀ (f N : ℕ) (R : ℕ → Fin f → MvPolynomial (Fin f × Fin N) ℝ),
    ∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f,
        map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f N l σ) * R l σ = 0 →
    ∀ m : ℕ, 1 ≤ m → m ≤ N → ∀ (τ : Fin f) (G : RestTerms.RootRing f N),
      G.IsHomogeneous (m - 1) →
        realFlagIntegral f N (map (algebraMap ℚ ℝ) G * R m τ) = 0
def RestCutTermEq.Statement : Prop :=
  ∀ (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (I : RootPoly f j k →ₗ[ℝ] ℝ) (c : ℝ),
    (∀ P : MvPolynomial (Fin f × Fin N) ℝ, P.IsHomogeneous (flagDim f j k) →
      I (restRename f j k N e P) = c * realFlagIntegral f N P) →
    ∀ (F : RestTerms.RootRing f N) (Q₀ : ℕ → Fin f → RestTerms.RootRing f N),
      RestTerms.IsPowerSumDecomposition f N F Q₀ →
      (∀ l σ, 1 ≤ l → l ≤ N → (Q₀ l σ).IsHomogeneous (flagDim f j k + 1 - l)) →
    ∀ Q : Fin f → ℕ → RootPoly f j k,
      IsPowerSumDecomposition f j k (restTransport f j k N e F) Q →
    ∀ m : ℕ, 1 ≤ m → m ≤ N → ∀ (τ : Fin f) (G : RestTerms.RootRing f N),
      G.IsHomogeneous (m - 1) →
        I (restTransport f j k N e G * Q τ m) = c * RestTerms.flagIntegral f N (G * Q₀ m τ)
def RestCutPrimeEq.Statement : Prop :=
  ∀ (f j k r a : ℕ) (cs : RestTerms.SmallBlock) (e : Fin (r + a) ≃ Fin j ⊕ Fin k),
    1 ≤ f → 1 ≤ j → 1 ≤ k → r + a = j + k →
    (∀ (m : ℕ) (σ : Fin f × Bool), ∃ ε : ℚ, ∃ δ : ℝ, (ε = 1 ∨ ε = -1) ∧
      lieClass f j k m σ =
        C (ε : ℝ) * restTransport f j k (r + a) e (RestTerms.smallPowerSum f r a cs m σ.1) +
          C δ * rootPsum f j k m σ.1) →
    ∀ (I : RootPoly f j k →ₗ[ℝ] ℝ), IsFlagIntegral f j k I →
    ∀ (c : ℝ) (Q₀ : ℕ → Fin f → RestTerms.RootRing f (r + a)) (Q : Fin f → ℕ → RootPoly f j k),
      IsPowerSumDecomposition f j k (restInput f j k) Q →
      (∀ m : ℕ, 2 ≤ m → m ≤ r + a → ∀ τ τ' : Fin f,
        I (restTransport f j k (r + a) e (RestTerms.smallPowerSum f r a cs (m - 1) τ') * Q τ m) =
          c * RestTerms.flagIntegral f (r + a)
            (RestTerms.smallPowerSum f r a cs (m - 1) τ' * Q₀ m τ)) →
    ∀ φ : ℕ → ℕ → Fin f → Fin f × Bool,
      ∃ (s : ℕ → ℕ → Fin f → Fin f) (ε : ℕ → ℕ → Fin f → ℕ → ℚ),
        (∀ p n τ m, ε p n τ m = 1 ∨ ε p n τ m = -1) ∧
        ∀ (vol : ℝ) (p : ℕ),
          restAt f j k I vol φ Q p = vol * c * RestTerms.restPrimeModel f r a cs Q₀ s ε p
def RestCutCaseCompare.Statement : Prop :=
  ∀ (f j k r a : ℕ) (cs : RestTerms.SmallBlock) (e : Fin (r + a) ≃ Fin j ⊕ Fin k),
    1 ≤ f → 1 ≤ r → 1 ≤ a → r + a = j + k →
    restTransport f j k (r + a) e
        (RestTerms.smallBlockMu f r a cs ^ (f * (r * a)) * RestTerms.fibreClass f r a cs) =
      degreeInput f j k →
    ∀ I : RootPoly f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
      ∃ c : ℝ,
        (∀ P : MvPolynomial (Fin f × Fin (r + a)) ℝ, P.IsHomogeneous (flagDim f j k) →
          I (restRename f j k (r + a) e P) = c * realFlagIntegral f (r + a) P) ∧
        I (degreeInput f j k) = c * (RestTerms.fibreDegree f r a cs : ℝ)
def RestCutCaseDecomp.Statement : Prop :=
  ∀ (f j k r a : ℕ) (cs : RestTerms.SmallBlock) (e : Fin (r + a) ≃ Fin j ⊕ Fin k),
    1 ≤ f → r + a = j + k → 2 ≤ r + a →
    restTransport f j k (r + a) e (RestTerms.restPolynomial f r a cs) = restInput f j k →
    (∃ Q₀, RestTerms.IsPowerSumDecomposition f (r + a) (RestTerms.restPolynomial f r a cs) Q₀) →
      (∃ Q₀ : ℕ → Fin f → RestTerms.RootRing f (r + a),
        RestTerms.IsPowerSumDecomposition f (r + a) (RestTerms.restPolynomial f r a cs) Q₀ ∧
        ∀ l σ, 1 ≤ l → l ≤ r + a → (Q₀ l σ).IsHomogeneous (flagDim f j k + 1 - l)) ∧
      ∃ Q, IsPowerSumDecomposition f j k (restInput f j k) Q
def RestCutCaseSharp.Statement : Prop :=
  ∀ (f j k r a : ℕ) (cs : RestTerms.SmallBlock) (e : Fin (r + a) ≃ Fin j ⊕ Fin k),
    1 ≤ f → 1 ≤ j → 1 ≤ k → 1 ≤ r → 1 ≤ a → r + a = j + k → r * a = j * k →
    restTransport f j k (r + a) e (RestTerms.restPolynomial f r a cs) = restInput f j k →
    restTransport f j k (r + a) e
        (RestTerms.smallBlockMu f r a cs ^ (f * (r * a)) * RestTerms.fibreClass f r a cs) =
      degreeInput f j k →
    (∀ (m : ℕ) (σ : Fin f × Bool), ∃ ε : ℚ, ∃ δ : ℝ, (ε = 1 ∨ ε = -1) ∧
      lieClass f j k m σ =
        C (ε : ℝ) * restTransport f j k (r + a) e (RestTerms.smallPowerSum f r a cs m σ.1) +
          C δ * rootPsum f j k m σ.1) →
    ∀ I : RootPoly f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∀ (vol : ℝ), 0 < vol → ∀ (P : Set ℕ), (∀ p ∈ P, p.Prime) →
    ∀ (B₀ : ℝ), 4 * f * ((j + k : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ φ : ℕ → ℕ → Fin f → Fin f × Bool,
      (∃ Q, IsPowerSumDecomposition f j k (restInput f j k) Q) ∧
      ∀ Q, IsPowerSumDecomposition f j k (restInput f j k) Q →
        Summable (fun p : primesAbove P B₀ => restAt f j k I vol φ Q p.1) ∧
        |∑' p : primesAbove P B₀, restAt f j k I vol φ Q p.1| ≤
          1.6 * ((f * j * k : ℕ) + 1) * vol * |I (degreeInput f j k)|
example : (1 : ℕ) ≤ 2 ∧ (1 : ℕ) < 2 := ⟨by norm_num, by norm_num⟩
theorem restPsumIdeal_example : RestTerms.blockPowerSum 1 (1 + 1) 1 0 ∈ restPsumIdeal 1 (1 + 1) :=
  Ideal.subset_span ⟨1, 0, le_rfl, by norm_num, rfl⟩
theorem restPsum_example_isHomogeneous :
    (RestTerms.blockPowerSum 1 (1 + 1) 1 0).IsHomogeneous (flagDim 1 1 1) := by
  have h : flagDim 1 1 1 = 1 := by decide
  rw [h]
  exact IsHomogeneous.sum _ _ _ fun i _ => by
    simpa using isHomogeneous_X_pow (R := ℚ) ((0 : Fin 1), i) 1
example : IsFlagIntegral 1 1 1 flagIntegralOne ∧
    RestTerms.blockPowerSum 1 (1 + 1) 1 0 ∈ restPsumIdeal 1 (1 + 1) ∧
    (RestTerms.blockPowerSum 1 (1 + 1) 1 0).IsHomogeneous (flagDim 1 1 1) :=
  ⟨isFlagIntegral_one, restPsumIdeal_example, restPsum_example_isHomogeneous⟩
theorem restStair_one_two : restStair 1 (1 + 1) = X ((0 : Fin 1), (1 : Fin (1 + 1))) := by
  simp [restStair, Fin.prod_univ_two]
theorem flagIntegral_restStair_one_two : RestTerms.flagIntegral 1 (1 + 1) (restStair 1 (1 + 1)) = -1 := by
  have h := RestTerms.inh_J_eq
  rw [RestTerms.fibreDegree, RestTerms.inh_mu_eq, RestTerms.inh_fib_eq] at h
  rw [restStair_one_two]
  simpa using h
example : (X ((0 : Fin 1), (1 : Fin (1 + 1))) : RestTerms.RootRing 1 (1 + 1)).IsHomogeneous
      (RestTerms.topDegree 1 (1 + 1)) ∧
    RestTerms.flagIntegral 1 (1 + 1) (X ((0 : Fin 1), (1 : Fin (1 + 1)))) ≠ 0 ∧
    IsFlagIntegral 1 1 1 flagIntegralOne ∧
    RestTerms.flagIntegral 1 (1 + 1) (restStair 1 (1 + 1)) ≠ 0 := by
  refine ⟨?_, ?_, isFlagIntegral_one, by rw [flagIntegral_restStair_one_two]; norm_num⟩
  · have h : RestTerms.topDegree 1 (1 + 1) = 1 := by decide
    rw [h]
    exact isHomogeneous_X _ _
  · rw [← restStair_one_two, flagIntegral_restStair_one_two]
    norm_num
example : RestTerms.IsPowerSumDecomposition 1 (1 + 1) (RestTerms.restPolynomial 1 1 1 .last)
      (fun k _ => if k = 1 then C (2⁻¹) * (RestTerms.flagTwoSecondRoot - RestTerms.flagTwoFirstRoot)
        else if k = 2 then C (2⁻¹) else 0) ∧
    (RestTerms.restPolynomial 1 1 1 .last).IsHomogeneous 2 ∧ 1 + 1 ≤ 2 := by
  refine ⟨RestTerms.inh_decomp, ?_, le_rfl⟩
  rw [RestTerms.inh_F_eq]
  exact isHomogeneous_X_pow _ _
example : ∑ l ∈ Finset.Icc 1 (1 + 1), ∑ σ : Fin 1,
      map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum 1 (1 + 1) l σ) *
        (fun (l : ℕ) (σ : Fin 1) => if l = 1 then map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum 1 (1 + 1) 2 σ)
          else if l = 2 then -map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum 1 (1 + 1) 1 σ) else 0) l σ = 0 ∧
    (1 : RestTerms.RootRing 1 (1 + 1)).IsHomogeneous (1 - 1) := by
  refine ⟨?_, isHomogeneous_one _ _⟩
  have hI : Finset.Icc 1 (1 + 1) = ({1, 2} : Finset ℕ) := by decide
  rw [hI]
  simp
  ring
end
end GroundTheory.Heights₂.Heights


