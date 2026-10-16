-- Prove2me | Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
-- name    : OAI_InformationTheory_PhotonNumber_Continuity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:32:19.123159+00:00
-- url     : https://prove2.me/theorems/78047020-9b5d-4674-a6a7-a7788351f4d3
-- title:
--   Existence and finite energy of the beam-splitter output state, and Kraus representations of beam-splitter channels
-- statement:
--   This file constructs the output state of a beam splitter as a genuine partial trace, shows it is a beam-splitter output in the number-basis sense, bounds its energy by the input energies, and represents the beam-splitter channels by explicit Kraus families with energy control.
--
--   Notation: $\mathcal F_n = \ell^2(\mathbb{N}^n)$ with number basis $|k\rangle$ and $|k| = \sum_jk_j$; a state is a positive bounded $\rho$ with $\sum_k\operatorname{Re}\langle k|\rho|k\rangle = 1$, with root columns $r^\rho_a = \sqrt\rho\,|a\rangle$; for a square-summable family $v$ write $O(v) = \sum_i|v_i\rangle\langle v_i|$, so that $O(r^\rho) = \rho$. $\mathcal U_\eta$ ($\eta\in[0,1]$) is the beam-splitter unitary on $\ell^2(\mathbb{N}^n\times\mathbb{N}^n)$; $z_e$ is the slice of a joint vector at second index $e$; $\operatorname{Tr}_B$ is the partial trace over the second factor of an ensemble. A state $\rho_C$ is a *beam-splitter output* of $\rho_A,\rho_B$ at $\eta$ if, for all $k,l$, the series $\sum_{e\in\mathbb{N}^n}B_\eta(k,l,e)$ of number-basis output blocks
--   $$
--   B_\eta(k,l,e) = \sum_{a,b}\beta_\eta(k,e;a,k+e-a)\,\langle a|\rho_A|b\rangle\,\langle k+e-a|\rho_B|l+e-b\rangle\,\beta_\eta(l,e;b,l+e-b)
--   $$
--   (with $a_j\le k_j+e_j$, $b_j\le l_j+e_j$, and $\beta_\eta$ the multimode beam-splitter coefficient) converges to $\langle k|\rho_C|l\rangle$. The energy of a state is $E(\rho) = \sum_k|k|\,\langle k|\rho|k\rangle\in[0,\infty]$, and of a vector $\mathcal E(x) = \sum_k|k|\,|x_k|^2\in[0,\infty]$.
--
--   1. **The output state.** For $\eta\in[0,1]$ and states $\rho_A,\rho_B$, the vectors $\mathcal U_\eta(r^{\rho_A}_a\otimes r^{\rho_B}_b)$ have total squared norm $1$, and the partial trace $\rho_C$ over the second port of the ensemble $\bigl(\mathcal U_\eta(r^{\rho_A}_a\otimes r^{\rho_B}_b)\bigr)_{a,b}$ is a state which is a beam-splitter output of $\rho_A,\rho_B$ at $\eta$. More generally, for any families $v,w$ with $\sum\|v_i\|^2 = \sum\|w_j\|^2 = 1$, $O(v) = \rho$ and $O(w) = \sigma$, the partial trace of the ensemble $\mathcal U_\eta(v_i\otimes w_j)$ equals this output state of $(\rho,\sigma)$; two operators with the same number-basis entries are equal.
--
--   2. **Energy.** A finite real matrix with orthonormal columns preserves $\sum|z|^2$; consequently the block unitaries, and in particular $\mathcal U_\eta$, preserve every sector-weighted mass $\sum_{k,e}w(k+e)\,|x(k,e)|^2$ with $w:\mathbb{N}^n\to[0,\infty]$, and so preserve $\sum_{k,e}(|k|+|e|)\,|x(k,e)|^2$. With general moments $\sum_aw_a|x_a|^2$ of vectors and $\sum_aw_a\operatorname{Re}\langle a|T|a\rangle$ of operators (in $[0,\infty]$), the moment of an ensemble operator is the sum of the vector moments, the moment of a partial trace is the moment of the ensemble with weight depending on the first index, and product vectors satisfy the additive identity $\sum_{a,b}(w_a+u_b)|x_ay_b|^2 = (\sum w_a|x_a|^2)\|y\|^2 + \|x\|^2(\sum u_b|y_b|^2)$. A state has finite energy (summable $|k|\,\langle k|\rho|k\rangle$) if and only if $E(\rho)<\infty$, and
--   $$
--   E(\rho_C)\le E(\rho_A)+E(\rho_B),
--   $$
--   so the output of two finite-energy inputs has finite energy.
--
--   3. **Kraus families.** For a state $\sigma$ the first beam-splitter Kraus operators are $K_{e,b}(x) = \bigl(\mathcal U_\eta(x\otimes r^\sigma_b)\bigr)_e$, and for a state $\rho$ the second ones are $K'_{e,a}(x) = \bigl(\mathcal U_\eta(r^\rho_a\otimes x)\bigr)_e$. Both satisfy $\sum_{e,b}\|K_{e,b}x\|^2 = \|x\|^2$ (resp. $\sum_{e,a}\|K'_{e,a}x\|^2 = \|x\|^2$) and the energy bounds $\sum_{e,b}\mathcal E(K_{e,b}x)\le\mathcal E(x)+E(\sigma)\,\|x\|^2$ and $\sum_{e,a}\mathcal E(K'_{e,a}x)\le\mathcal E(x)+E(\rho)\,\|x\|^2$. If $v$ is a normalised ensemble of $\rho$ (resp. of $\sigma$), the ensemble $(K_{e,b}v_i)$ (resp. $(K'_{e,a}v_i)$) represents the output state of $(\rho,\sigma)$. Compositions $U_i\circ V_j$ of two norm-preserving Kraus families are norm-preserving, energy constants add ($\mathcal E$-bounds with $E_U$, $E_V$ give $E_U+E_V$), and the ensembles they generate are reindexings of one another; a norm-preserving family maps a family of total squared norm $t$ to one of total squared norm $t$.
--
--   4. **Ensemble means and joint Kraus maps.** A square-summable family is a vector of $\ell^2(I;E)$; its images under bounded operators remain square-summable, its mean against $Z$ is $\sum_i\langle v_i,Zv_i\rangle$, and the centering of $Z$ is $Z$ minus this mean times the identity. On the joint space, $J_e(x) = (\mathcal U_\eta x)_e$ satisfies $\sum_e\|J_ex\|^2 = \|x\|^2$; the raw joint Kraus family composes $J_e$ with the first Kraus family at a second transmissivity $\theta\in[0,1]$ and state $\tau$, and the raw dual is its dual map $Z\mapsto\Phi^*(Z)$, $\langle x,\Phi^*(Z)y\rangle = \sum\langle Kx,ZKy\rangle$.
--
--   Item 1 provides, for all inputs, a state satisfying the beam-splitter output condition of the main entropy photon-number inequality, and item 2 shows that finite input energy passes to this output.
--
--   **Formalization Note** Energies and moments are valued in $[0,\infty]$ (`ℝ≥0∞`) and use `ENNReal.ofReal`; `FiniteEnergy ρ` is the summability predicate of the main definitions and `finiteEnergy_iff` relates it to `energyMoment ρ < ⊤`. The output state is `beamOutput η hη ρA ρB` with `hη : η ∈ Set.Icc 0 1`, and `beamOutput_spec` is the statement `IsBeamSplitterOutput η ρA ρB (beamOutput η hη ρA ρB)`. Kraus families are indexed by pairs $(e,b)$ or $(e,a)$ in $\mathbb{N}^n\times\mathbb{N}^n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Continuity.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Continuity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace EntropyPhotonNumber
open TensorLp
def mixedVector {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρA ρB : State n)
    (ab : PairedIndex n) : JointFock n :=
  beamUnitary η hη (tensor (rootColumn ρA ab.1) (rootColumn ρB ab.2))

theorem mixedVector_norm {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρA ρB : State n) :
    HasSum (fun ab => ‖mixedVector η hη ρA ρB ab‖^2) 1 := by
  simpa only [mixedVector, LinearIsometryEquiv.norm_map, one_mul] using
    TraceEnsemble.hasSum_tensor_norm (rootColumn_norm ρA) (rootColumn_norm ρB)

def beamOutput {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρA ρB : State n) : State n where
  op := partialTrace (mixedVector η hη ρA ρB)
  positive := partialTrace_positive (mixedVector_norm η hη ρA ρB).summable
  trace_one := by
    simpa only [channelNumberBasis_apply, entry] using
      partialTrace_trace (mixedVector_norm η hη ρA ρB) (channelNumberBasis n)

theorem mixedVector_entry {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρA ρB : State n)
    (k l e : NumberIndex n) :
    inner ℂ (lp.single 2 (k,e) 1)
      (TraceEnsemble.operator (mixedVector η hη ρA ρB) (lp.single 2 (l,e) 1)) =
        outputBlock η ρA ρB k l e := by
  unfold mixedVector
  rw [TraceEnsemble.unitary_entry
    (TraceEnsemble.hasSum_tensor_norm (rootColumn_norm ρA) (rootColumn_norm ρB)).summable]
  rw [beam_symm_number, beam_symm_number]
  simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold outputBlock
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [TraceEnsemble.tensor_entry (rootColumn_norm ρA).summable (rootColumn_norm ρB).summable,
    rootColumn_operator, rootColumn_operator]
  simp only [entry, numberKet]
  ring

theorem beamOutput_spec {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρA ρB : State n) :
    IsBeamSplitterOutput η ρA ρB (beamOutput η hη ρA ρB) := by
  intro k l
  have h := partialTrace_entry (mixedVector_norm η hη ρA ρB).summable k l
  simpa only [mixedVector_entry, beamOutput, entry, numberKet] using h

end EntropyPhotonNumber

namespace BlockUnitary
variable {J : Type*} [Fintype J]

theorem finite_transform_norm_sq (U : J → J → ℝ)
    (hc : ∀ a b, ∑ k, U k a*U k b = if a=b then 1 else 0) (z : J → ℂ) :
    (∑ k, ‖∑ a, (U k a : ℂ)*z a‖^2) = ∑ a, ‖z a‖^2 := by
  classical
  let v : J → EuclideanSpace ℂ J := fun a => WithLp.toLp 2 (fun k => (U k a : ℂ))
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro a b
    change (∑ k, (U k b : ℂ)*star (U k a : ℂ)) = _
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum, hc]
    by_cases hab : a=b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have hi := hv.inner_sum z z Finset.univ
  have he : (∑ a, z a • v a) = WithLp.toLp 2 (fun k => ∑ a, (U k a : ℂ)*z a) := by
    ext k
    simp [v, mul_comm]
  have hnorm : ‖∑ a, z a • v a‖^2 = ∑ a, ‖z a‖^2 := by
    calc
      _ = (inner ℂ (∑ a, z a • v a) (∑ a, z a • v a)).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = (∑ a, conj (z a)*z a).re := congrArg Complex.re hi
      _ = _ := by simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  rw [he, EuclideanSpace.norm_sq_eq] at hnorm
  exact hnorm

variable {S : Type*} {I : S → Type*} [∀ s, Fintype (I s)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem unitary_coordinate (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hcol : ∀ s a d, ∑ k, U s k a*U s k d = if a=d then 1 else 0)
    (hrow : ∀ s k l, ∑ a, U s k a*U s l a = if k=l then 1 else 0)
    (x : E) (s : S) (k : I s) :
    inner ℂ (b ⟨s,k⟩) (unitary b U hcol hrow x) =
      ∑ a, (U s k a : ℂ)* inner ℂ (b ⟨s,a⟩) x := by
  have hi := (unitary b U hcol hrow).inner_map_map
    ((unitary b U hcol hrow).symm (b ⟨s,k⟩)) x
  rw [LinearIsometryEquiv.apply_symm_apply, unitary_symm_apply_basis] at hi
  rw [hi]
  simp only [sum_inner, inner_smul_left, Complex.conj_ofReal]

theorem unitary_sector_mass (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hcol : ∀ s a d, ∑ k, U s k a*U s k d = if a=d then 1 else 0)
    (hrow : ∀ s k l, ∑ a, U s k a*U s l a = if k=l then 1 else 0)
    (x : E) (s : S) :
    (∑ k, ‖inner ℂ (b ⟨s,k⟩) (unitary b U hcol hrow x)‖^2) =
      ∑ k, ‖inner ℂ (b ⟨s,k⟩) x‖^2 := by
  simp only [unitary_coordinate]
  exact finite_transform_norm_sq (U s) (hcol s) _

theorem unitary_weighted_mass (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hcol : ∀ s a d, ∑ k, U s k a*U s k d = if a=d then 1 else 0)
    (hrow : ∀ s k l, ∑ a, U s k a*U s l a = if k=l then 1 else 0)
    (x : E) (w : S → ℝ≥0∞) :
    (∑' i : Sigma I, w i.1 * ENNReal.ofReal (‖inner ℂ (b i) (unitary b U hcol hrow x)‖^2)) =
      ∑' i : Sigma I, w i.1 * ENNReal.ofReal (‖inner ℂ (b i) x‖^2) := by
  rw [ENNReal.tsum_sigma', ENNReal.tsum_sigma']
  congr 1
  funext s
  simp only [tsum_fintype, ← Finset.mul_sum]
  congr 1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
    ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _), unitary_sector_mass]

end BlockUnitary

namespace TensorLp
variable {A B I : Type*}

def vectorMoment (w : A → ℝ≥0∞) (x : H A) : ℝ≥0∞ :=
  ∑' a, w a * ENNReal.ofReal (‖x a‖^2)

def matrixMoment [DecidableEq A] (w : A → ℝ≥0∞) (T : H A →L[ℂ] H A) : ℝ≥0∞ :=
  ∑' a, w a * ENNReal.ofReal (inner ℂ (lp.single 2 a 1) (T (lp.single 2 a 1))).re

theorem vectorMoment_one (x : H A) : vectorMoment (fun _ => 1) x = ENNReal.ofReal (‖x‖^2) := by
  simp only [vectorMoment, one_mul]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hasSum_square x).summable,
    (hasSum_square x).tsum_eq]

theorem matrixMoment_ensemble [DecidableEq A] {v : I → H A}
    (hv : Summable (fun i => ‖v i‖^2)) (w : A → ℝ≥0∞) :
    matrixMoment w (TraceEnsemble.operator v) = ∑' i, vectorMoment w (v i) := by
  have he (a : A) : ENNReal.ofReal
      (inner ℂ (lp.single 2 a 1) (TraceEnsemble.operator v (lp.single 2 a 1))).re =
      ∑' i, ENNReal.ofReal (‖v i a‖^2) := by
    have h : HasSum (fun i => ‖v i a‖^2)
        (inner ℂ (lp.single 2 a 1) (TraceEnsemble.operator v (lp.single 2 a 1))).re := by
      convert! TraceEnsemble.hasSum_quadratic hv (lp.single 2 a 1) using 1
      ext i
      simp only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
    rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable]
  simp only [matrixMoment, he, ← ENNReal.tsum_mul_left, vectorMoment]
  exact ENNReal.tsum_comm

theorem partialTrace_moment [DecidableEq A] {v : I → H (A × B)}
    (hv : Summable (fun i => ‖v i‖^2)) (w : A → ℝ≥0∞) :
    matrixMoment w (partialTrace v) = ∑' i, vectorMoment (fun ab : A × B => w ab.1) (v i) := by
  rw [partialTrace, matrixMoment_ensemble (hasSum_slice_family hv.hasSum).summable]
  simp only [vectorMoment, slice_apply]
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  congr 1
  funext i
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]

theorem tensor_add_moment (w : A → ℝ≥0∞) (u : B → ℝ≥0∞) (x : H A) (y : H B) :
    vectorMoment (fun ab : A × B => w ab.1+u ab.2) (tensor x y) =
      vectorMoment w x * ENNReal.ofReal (‖y‖^2) +
      ENNReal.ofReal (‖x‖^2) * vectorMoment u y := by
  have hx : (∑' a, ENNReal.ofReal (‖x a‖^2)) = ENNReal.ofReal (‖x‖^2) := by
    simpa only [vectorMoment, one_mul] using vectorMoment_one x
  have hy : (∑' b, ENNReal.ofReal (‖y b‖^2)) = ENNReal.ofReal (‖y‖^2) := by
    simpa only [vectorMoment, one_mul] using vectorMoment_one y
  change (∑' ab : A × B, (w ab.1+u ab.2)*ENNReal.ofReal (‖x ab.1*y ab.2‖^2)) = _
  simp only [norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
    add_mul, ENNReal.tsum_add, ENNReal.tsum_prod']
  congr 1
  · simp only [← mul_assoc, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hy, vectorMoment]
  · simp only [mul_left_comm (u _) (ENNReal.ofReal _), ENNReal.tsum_mul_left,
      ENNReal.tsum_mul_right, hx, vectorMoment]

theorem ensemble_tensor_add_moment [DecidableEq A] [DecidableEq B]
    {v : I → H A} {J : Type*} {z : J → H B}
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hz : HasSum (fun j => ‖z j‖^2) 1)
    (w : A → ℝ≥0∞) (u : B → ℝ≥0∞) :
    (∑' ij : I × J, vectorMoment (fun ab : A × B => w ab.1+u ab.2) (tensor (v ij.1) (z ij.2))) =
      matrixMoment w (TraceEnsemble.operator v) + matrixMoment u (TraceEnsemble.operator z) := by
  have hv₁ : (∑' i, ENNReal.ofReal (‖v i‖^2)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hv.summable, hv.tsum_eq]
    norm_num
  have hz₁ : (∑' j, ENNReal.ofReal (‖z j‖^2)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hz.summable, hz.tsum_eq]
    norm_num
  simp only [tensor_add_moment, ENNReal.tsum_add, ENNReal.tsum_prod',
    ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hv₁, hz₁, one_mul, mul_one]
  rw [matrixMoment_ensemble hv.summable, matrixMoment_ensemble hz.summable]

end TensorLp

namespace EntropyPhotonNumber
open TensorLp FischerBeam

theorem beam_sector_weighted_mass {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (x : JointFock n) (w : NumberIndex n → ℝ≥0∞) :
    (∑' a : NumberSector n, w a.1 * ENNReal.ofReal
      (‖inner ℂ (jointSectorBasis n a) (beamUnitary η hη x)‖^2)) =
      ∑' a : NumberSector n, w a.1 * ENNReal.ofReal (‖inner ℂ (jointSectorBasis n a) x‖^2) := by
  unfold beamUnitary
  exact BlockUnitary.unitary_weighted_mass _ _ _ _ _ _

theorem beam_vector_moment {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (x : JointFock n) (w : NumberIndex n → ℝ≥0∞) :
    vectorMoment (fun ab : PairedIndex n => w (fun j => ab.1 j+ab.2 j)) (beamUnitary η hη x) =
      vectorMoment (fun ab : PairedIndex n => w (fun j => ab.1 j+ab.2 j)) x := by
  unfold vectorMoment
  rw [← (sectorEquiv n).tsum_eq (fun ab => w (fun j => ab.1 j+ab.2 j) *
    ENNReal.ofReal (‖beamUnitary η hη x ab‖^2)),
    ← (sectorEquiv n).tsum_eq (fun ab => w (fun j => ab.1 j+ab.2 j) *
    ENNReal.ofReal (‖x ab‖^2))]
  have he (a : NumberSector n) :
      (fun j => (sectorEquiv n a).1 j+(sectorEquiv n a).2 j) = a.1 := by
    funext j
    exact Nat.add_sub_of_le (Nat.le_of_lt_succ (a.2 j).isLt)
  simpa only [he, jointSectorBasis_apply, lp.inner_single_left, RCLike.inner_apply,
    map_one, one_mul, mul_one] using beam_sector_weighted_mass η hη x w

theorem beam_total_moment {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x : JointFock n) :
    vectorMoment (fun ab : PairedIndex n => (totalNumber ab.1 : ℝ≥0∞)+totalNumber ab.2)
      (beamUnitary η hη x) =
      vectorMoment (fun ab : PairedIndex n => (totalNumber ab.1 : ℝ≥0∞)+totalNumber ab.2) x := by
  simpa only [totalNumber, Finset.sum_add_distrib, Nat.cast_add] using
    beam_vector_moment η hη x (fun k => (totalNumber k : ℝ≥0∞))

def energyMoment {n : ℕ} (ρ : State n) : ℝ≥0∞ :=
  matrixMoment (fun k => (totalNumber k : ℝ≥0∞)) ρ.op

theorem energyMoment_eq {n : ℕ} (ρ : State n) :
    energyMoment ρ = ∑' k, ENNReal.ofReal ((totalNumber k : ℝ)*(entry ρ.op k k).re) := by
  simp only [energyMoment, matrixMoment, entry, numberKet,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem finiteEnergy_iff {n : ℕ} (ρ : State n) : FiniteEnergy ρ ↔ energyMoment ρ < ⊤ := by
  rw [energyMoment_eq]
  have hp (k : NumberIndex n) : 0 ≤ (totalNumber k : ℝ)*(entry ρ.op k k).re :=
    mul_nonneg (Nat.cast_nonneg _) (ρ.positive.re_inner_nonneg_right _)
  constructor
  · intro h
    exact h.tsum_ofReal_lt_top
  · intro h
    have hs := ENNReal.summable_toReal h.ne
    change Summable (fun k => (totalNumber k : ℝ)*(entry ρ.op k k).re)
    simpa only [ENNReal.toReal_ofReal (hp _)] using hs

theorem beamOutput_energy_le {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρA ρB : State n) :
    energyMoment (beamOutput η hη ρA ρB) ≤ energyMoment ρA + energyMoment ρB := by
  change matrixMoment _ (partialTrace (mixedVector η hη ρA ρB)) ≤ _
  rw [partialTrace_moment (mixedVector_norm η hη ρA ρB).summable]
  calc
    _ ≤ ∑' a, vectorMoment (fun ab : PairedIndex n =>
        (totalNumber ab.1 : ℝ≥0∞)+totalNumber ab.2) (mixedVector η hη ρA ρB a) := by
      apply ENNReal.tsum_le_tsum
      intro a
      apply ENNReal.tsum_le_tsum
      intro ab
      exact mul_le_mul' le_self_add le_rfl
    _ = ∑' a : PairedIndex n, vectorMoment (fun ab : PairedIndex n =>
        (totalNumber ab.1 : ℝ≥0∞)+totalNumber ab.2)
        (tensor (rootColumn ρA a.1) (rootColumn ρB a.2)) := by
      simp only [mixedVector, beam_total_moment]
    _ = energyMoment ρA + energyMoment ρB := by
      rw [ensemble_tensor_add_moment (rootColumn_norm ρA) (rootColumn_norm ρB)
        (fun k => (totalNumber k : ℝ≥0∞)) (fun k => (totalNumber k : ℝ≥0∞)),
        rootColumn_operator, rootColumn_operator]
      rfl

theorem beamOutput_finiteEnergy {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) {ρA ρB : State n}
    (hA : FiniteEnergy ρA) (hB : FiniteEnergy ρB) : FiniteEnergy (beamOutput η hη ρA ρB) := by
  apply (finiteEnergy_iff _).mpr
  exact (beamOutput_energy_le η hη ρA ρB).trans_lt
    (ENNReal.add_lt_top.mpr ⟨(finiteEnergy_iff ρA).mp hA, (finiteEnergy_iff ρB).mp hB⟩)

end EntropyPhotonNumber

namespace TensorLp
variable {A B : Type*}

theorem sum_slice_moment (w : A → ℝ≥0∞) (z : H (A × B)) :
    (∑' b, vectorMoment w (slice z b)) = vectorMoment (fun ab : A × B => w ab.1) z := by
  simp only [vectorMoment, slice_apply]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]

end TensorLp

namespace EntropyPhotonNumber
open TensorLp

def firstKraus {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (σ : State n)
    (eb : NumberIndex n × NumberIndex n) : Fock n →L[ℂ] Fock n :=
  sliceCLM eb.1 ∘L ((beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    tensorRight (rootColumn σ eb.2))

@[simp] theorem firstKraus_apply {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (σ : State n)
    (eb : NumberIndex n × NumberIndex n) (x : Fock n) :
    firstKraus η hη σ eb x = slice (beamUnitary η hη (tensor x (rootColumn σ eb.2))) eb.1 := rfl

theorem firstKraus_norm {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (σ : State n) (x : Fock n) :
    HasSum (fun eb => ‖firstKraus η hη σ eb x‖^2) (‖x‖^2) := by
  simp only [firstKraus_apply]
  apply hasSum_slice_family (v := fun b => beamUnitary η hη (tensor x (rootColumn σ b)))
  simpa only [LinearIsometryEquiv.norm_map, tensor_norm_sq, mul_one] using
    (rootColumn_norm σ).mul_left (‖x‖^2)

theorem firstKraus_energy {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (σ : State n) (x : Fock n) :
    (∑' eb, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (firstKraus η hη σ eb x)) ≤
      vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x +
        energyMoment σ * ENNReal.ofReal (‖x‖^2) := by
  have hn : (∑' b, ENNReal.ofReal (‖rootColumn σ b‖^2)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (rootColumn_norm σ).summable,
      (rootColumn_norm σ).tsum_eq, ENNReal.ofReal_one]
  have he : (∑' b, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (rootColumn σ b)) =
      energyMoment σ := by
    rw [← matrixMoment_ensemble (rootColumn_norm σ).summable, rootColumn_operator]
    rfl
  simp only [firstKraus_apply, ENNReal.tsum_prod']
  rw [ENNReal.tsum_comm]
  simp only [sum_slice_moment]
  calc
    _ ≤ ∑' b, vectorMoment (fun ab : NumberIndex n × NumberIndex n =>
        (totalNumber ab.1 : ℝ≥0∞)+totalNumber ab.2)
        (beamUnitary η hη (tensor x (rootColumn σ b))) := by
      apply ENNReal.tsum_le_tsum
      intro b
      apply ENNReal.tsum_le_tsum
      intro ab
      exact mul_le_mul' le_self_add le_rfl
    _ = _ := by
      simp only [beam_total_moment]
      simp_rw [tensor_add_moment (fun k : NumberIndex n => (totalNumber k : ℝ≥0∞))
        (fun k : NumberIndex n => (totalNumber k : ℝ≥0∞))]
      simp only [ENNReal.tsum_add,
        ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hn, he, mul_comm, one_mul]

def secondKraus {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρ : State n)
    (ea : NumberIndex n × NumberIndex n) : Fock n →L[ℂ] Fock n :=
  sliceCLM ea.1 ∘L ((beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    tensorLeft (rootColumn ρ ea.2))

@[simp] theorem secondKraus_apply {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρ : State n)
    (ea : NumberIndex n × NumberIndex n) (x : Fock n) :
    secondKraus η hη ρ ea x = slice (beamUnitary η hη (tensor (rootColumn ρ ea.2) x)) ea.1 := rfl

theorem secondKraus_norm {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρ : State n) (x : Fock n) :
    HasSum (fun ea => ‖secondKraus η hη ρ ea x‖^2) (‖x‖^2) := by
  simp only [secondKraus_apply]
  apply hasSum_slice_family (v := fun a => beamUnitary η hη (tensor (rootColumn ρ a) x))
  simpa only [LinearIsometryEquiv.norm_map, tensor_norm_sq, one_mul] using
    (rootColumn_norm ρ).mul_right (‖x‖^2)

theorem secondKraus_energy {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρ : State n) (x : Fock n) :
    (∑' ea, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (secondKraus η hη ρ ea x)) ≤
      vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x +
        energyMoment ρ * ENNReal.ofReal (‖x‖^2) := by
  have hn : (∑' a, ENNReal.ofReal (‖rootColumn ρ a‖^2)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (rootColumn_norm ρ).summable,
      (rootColumn_norm ρ).tsum_eq, ENNReal.ofReal_one]
  have he : (∑' a, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (rootColumn ρ a)) =
      energyMoment ρ := by
    rw [← matrixMoment_ensemble (rootColumn_norm ρ).summable, rootColumn_operator]
    rfl
  simp only [secondKraus_apply, ENNReal.tsum_prod']
  rw [ENNReal.tsum_comm]
  simp only [sum_slice_moment]
  calc
    _ ≤ ∑' a, vectorMoment (fun ab : NumberIndex n × NumberIndex n =>
        (totalNumber ab.1 : ℝ≥0∞)+totalNumber ab.2)
        (beamUnitary η hη (tensor (rootColumn ρ a) x)) := by
      apply ENNReal.tsum_le_tsum
      intro a
      apply ENNReal.tsum_le_tsum
      intro ab
      exact mul_le_mul' le_self_add le_rfl
    _ = _ := by
      simp only [beam_total_moment]
      simp_rw [tensor_add_moment (fun k : NumberIndex n => (totalNumber k : ℝ≥0∞))
        (fun k : NumberIndex n => (totalNumber k : ℝ≥0∞))]
      simp only [ENNReal.tsum_add,
        ENNReal.tsum_mul_right, hn, he, one_mul, add_comm]

def composeKraus {n : ℕ} {I J : Type*} (U : I → Fock n →L[ℂ] Fock n)
    (V : J → Fock n →L[ℂ] Fock n) (ij : I × J) : Fock n →L[ℂ] Fock n := U ij.1 ∘L V ij.2

theorem composeKraus_norm {n : ℕ} {I J : Type*} (U : I → Fock n →L[ℂ] Fock n)
    (V : J → Fock n →L[ℂ] Fock n)
    (hU : ∀ x, HasSum (fun i => ‖U i x‖^2) (‖x‖^2))
    (hV : ∀ x, HasSum (fun j => ‖V j x‖^2) (‖x‖^2)) (x : Fock n) :
    HasSum (fun ij => ‖composeKraus U V ij x‖^2) (‖x‖^2) := by
  change HasSum (fun ij : I × J => ‖U ij.1 (V ij.2 x)‖^2) (‖x‖^2)
  have hu (j : J) : (∑' i, ‖U i (V j x)‖^2) = ‖V j x‖^2 := (hU (V j x)).tsum_eq
  have hs : Summable (fun ji : J × I => ‖U ji.2 (V ji.1 x)‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    exact ⟨fun j => (hU (V j x)).summable, by simpa only [hu] using (hV x).summable⟩
  have ht : (∑' ji : J × I, ‖U ji.2 (V ji.1 x)‖^2) = ‖x‖^2 := by
    rw [hs.tsum_prod]
    simpa only [hu] using (hV x).tsum_eq
  have hsum : HasSum (fun ji : J × I => ‖U ji.2 (V ji.1 x)‖^2) (‖x‖^2) := ht ▸ hs.hasSum
  exact (Equiv.prodComm I J).hasSum_iff.mpr hsum

theorem composeKraus_energy {n : ℕ} {I J : Type*} (U : I → Fock n →L[ℂ] Fock n)
    (V : J → Fock n →L[ℂ] Fock n) {EU EV : ℝ≥0∞}
    (hV : ∀ x, HasSum (fun j => ‖V j x‖^2) (‖x‖^2))
    (hEU : ∀ x, (∑' i, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (U i x)) ≤
      vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x+EU*ENNReal.ofReal (‖x‖^2))
    (hEV : ∀ x, (∑' j, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (V j x)) ≤
      vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x+EV*ENNReal.ofReal (‖x‖^2))
    (x : Fock n) :
    (∑' ij, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (composeKraus U V ij x)) ≤
      vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x+(EU+EV)*ENNReal.ofReal (‖x‖^2) := by
  have hn : (∑' j, ENNReal.ofReal (‖V j x‖^2)) = ENNReal.ofReal (‖x‖^2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hV x).summable, (hV x).tsum_eq]
  change (∑' ij : I × J, vectorMoment _ (U ij.1 (V ij.2 x))) ≤ _
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  calc
    _ ≤ ∑' j, (vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (V j x)+EU*ENNReal.ofReal (‖V j x‖^2)) :=
      ENNReal.tsum_le_tsum (fun j => hEU (V j x))
    _ = (∑' j, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (V j x))+EU*ENNReal.ofReal (‖x‖^2) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hn]
    _ ≤ _ := by
      have hh := add_le_add_right (hEV x) (EU*ENNReal.ofReal (‖x‖^2))
      simpa only [add_mul, add_assoc, add_left_comm, add_comm] using hh

end EntropyPhotonNumber

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

omit [CompleteSpace E] in
theorem operator_reindex (e : I ≃ J) (v : J → E) : operator (fun i => v (e i)) = operator v := by
  exact e.tsum_eq (fun j => InnerProductSpace.rankOne ℂ (v j) (v j))

omit [CompleteSpace E] in
theorem kraus_hasSum {V : I → E →L[ℂ] E}
    (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    {v : J → E} {t : ℝ} (hv : HasSum (fun j => ‖v j‖^2) t) :
    HasSum (fun ij : I × J => ‖V ij.1 (v ij.2)‖^2) t := by
  have hu (j : J) : (∑' i, ‖V i (v j)‖^2) = ‖v j‖^2 := (hV (v j)).tsum_eq
  have hs : Summable (fun ji : J × I => ‖V ji.2 (v ji.1)‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    exact ⟨fun j => (hV (v j)).summable, by simpa only [hu] using hv.summable⟩
  have ht : (∑' ji : J × I, ‖V ji.2 (v ji.1)‖^2) = t := by
    rw [hs.tsum_prod]
    simpa only [hu] using hv.tsum_eq
  have hsum : HasSum (fun ji : J × I => ‖V ji.2 (v ji.1)‖^2) t := ht ▸ hs.hasSum
  exact (Equiv.prodComm I J).hasSum_iff.mpr hsum

end TraceEnsemble

namespace EntropyPhotonNumber
open TensorLp
theorem beam_ensemble {n : ℕ} {I J : Type*} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ : State n) (v : I → Fock n) (w : J → Fock n)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (hev : TraceEnsemble.operator v = ρ.op) (hew : TraceEnsemble.operator w = σ.op) :
    partialTrace (fun ij : I × J => beamUnitary η hη (tensor (v ij.1) (w ij.2))) =
      (beamOutput η hη ρ σ).op := by
  have hn : Summable (fun ij : I × J => ‖beamUnitary η hη (tensor (v ij.1) (w ij.2))‖^2) := by
    simpa only [LinearIsometryEquiv.norm_map] using (TraceEnsemble.hasSum_tensor_norm hv hw).summable
  apply entry_ext
  intro k l
  have hh : HasSum (fun e => outputBlock η ρ σ k l e)
      (entry (partialTrace (fun ij : I × J => beamUnitary η hη (tensor (v ij.1) (w ij.2)))) k l) := by
    simpa only [entry, numberKet, beam_ensemble_entry η hη ρ σ v w hv hw hev hew] using
      partialTrace_entry hn k l
  exact hh.unique (beamOutput_spec η hη ρ σ k l)

theorem firstKraus_ensemble {n : ℕ} {I : Type*} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ : State n) (v : I → Fock n) (hv : HasSum (fun i => ‖v i‖^2) 1)
    (hev : TraceEnsemble.operator v = ρ.op) :
    TraceEnsemble.operator (fun ei : (NumberIndex n × NumberIndex n) × I =>
      firstKraus η hη σ ei.1 (v ei.2)) = (beamOutput η hη ρ σ).op := by
  let e := (Equiv.prodAssoc (NumberIndex n) (NumberIndex n) I).trans
    (Equiv.prodCongr (Equiv.refl (NumberIndex n)) (Equiv.prodComm (NumberIndex n) I))
  have he := TraceEnsemble.operator_reindex e (fun z : NumberIndex n × (I × NumberIndex n) =>
    slice (beamUnitary η hη (tensor (v z.2.1) (rootColumn σ z.2.2))) z.1)
  change _ = partialTrace (fun ij : I × NumberIndex n => beamUnitary η hη (tensor (v ij.1) (rootColumn σ ij.2))) at he
  exact he.trans (beam_ensemble η hη ρ σ v (rootColumn σ) hv (rootColumn_norm σ) hev (rootColumn_operator σ))

theorem secondKraus_ensemble {n : ℕ} {I : Type*} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ : State n) (v : I → Fock n) (hv : HasSum (fun i => ‖v i‖^2) 1)
    (hev : TraceEnsemble.operator v = σ.op) :
    TraceEnsemble.operator (fun ei : (NumberIndex n × NumberIndex n) × I =>
      secondKraus η hη ρ ei.1 (v ei.2)) = (beamOutput η hη ρ σ).op := by
  have he := TraceEnsemble.operator_reindex (Equiv.prodAssoc (NumberIndex n) (NumberIndex n) I)
    (fun z : NumberIndex n × (NumberIndex n × I) =>
      slice (beamUnitary η hη (tensor (rootColumn ρ z.2.1) (v z.2.2))) z.1)
  change _ = partialTrace (fun ij : NumberIndex n × I => beamUnitary η hη (tensor (rootColumn ρ ij.1) (v ij.2))) at he
  exact he.trans (beam_ensemble η hη ρ σ (rootColumn ρ) v (rootColumn_norm ρ) hv (rootColumn_operator ρ) hev)

theorem composeKraus_ensemble {n : ℕ} {I J K : Type*}
    (U : I → Fock n →L[ℂ] Fock n) (V : J → Fock n →L[ℂ] Fock n) (v : K → Fock n) :
    TraceEnsemble.operator (fun z : (I × J) × K => composeKraus U V z.1 (v z.2)) =
      TraceEnsemble.operator (fun z : I × (J × K) => U z.1 (V z.2.1 (v z.2.2))) := by
  unfold composeKraus
  exact TraceEnsemble.operator_reindex (Equiv.prodAssoc I J K)
    (fun z : I × (J × K) => U z.1 (V z.2.1 (v z.2.2)))

end EntropyPhotonNumber

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def vector (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) : lp (fun _ : I => E) 2 :=
  ⟨v, (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
    (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hv)⟩
omit [InnerProductSpace ℂ E] in
@[simp] theorem vector_apply (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) (i : I) : vector v hv i = v i := rfl

theorem inner_sum (v w : I → E) (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun i => ‖w i‖^2)) :
    HasSum (fun i => inner ℂ (v i) (w i)) (inner ℂ (vector v hv) (vector w hw)) :=
  lp.hasSum_inner (𝕜 := ℂ) (vector v hv) (vector w hw)

theorem image_summable (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) (T : E →L[ℂ] E) :
    Summable (fun i => ‖T (v i)‖^2) := by
  apply (hv.mul_left (‖T‖^2)).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro i
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (v i)) 2

end EnsembleL2

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}
end TensorLp

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

end KrausBounded

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
def mean (v : I → E) (Z : E →L[ℂ] E) : ℂ := ∑' i, inner ℂ (v i) (Z (v i))
def center (v : I → E) (Z : E →L[ℂ] E) : E →L[ℂ] E := Z-mean v Z • ContinuousLinearMap.id ℂ E

omit [CompleteSpace E] in
theorem mean_hasSum (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    HasSum (fun i => inner ℂ (v i) (Z (v i))) (mean v Z) :=
  (inner_sum v (fun i => Z (v i)) hv (image_summable v hv Z)).summable.hasSum

end EnsembleL2

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}

end TensorLp

namespace KrausBounded

section
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

end

open scoped BigOperators ComplexConjugate
variable {E H K I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

omit [CompleteSpace E] [CompleteSpace H] in
theorem family_hasSum (V : K → E →L[ℂ] H)
    (hV : ∀ x, HasSum (fun k => ‖V k x‖^2) (‖x‖^2))
    (v : I → E) (t : ℝ) (hv : HasSum (fun i => ‖v i‖^2) t) :
    HasSum (fun ik : I × K => ‖V ik.2 (v ik.1)‖^2) t := by
  have hs : Summable (fun ik : I × K => ‖V ik.2 (v ik.1)‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun i => (hV (v i)).summable, ?_⟩
    simpa only [(hV _).tsum_eq] using hv.summable
  have he : (∑' ik : I × K, ‖V ik.2 (v ik.1)‖^2)=t := by
    rw [hs.tsum_prod]
    simpa only [(hV _).tsum_eq] using hv.tsum_eq
  exact he ▸ hs.hasSum

end KrausBounded

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J K E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end TensorLp

namespace KrausBounded
open scoped BigOperators ComplexConjugate
variable {E H F I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace E] [CompleteSpace H] [CompleteSpace F]

def composite (V : I → E →L[ℂ] H) (U : J → H →L[ℂ] F) (ij : I × J) : E →L[ℂ] F := U ij.2 ∘L V ij.1

omit [CompleteSpace E] [CompleteSpace H] [CompleteSpace F] in
theorem composite_norm (V : I → E →L[ℂ] H) (U : J → H →L[ℂ] F)
    (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (hU : ∀ x, HasSum (fun j => ‖U j x‖^2) (‖x‖^2)) (x : E) :
    HasSum (fun ij => ‖composite V U ij x‖^2) (‖x‖^2) :=
  family_hasSum U hU (fun i => V i x) _ (hV x)

end KrausBounded

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate

def jointKraus {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) (e : NumberIndex n) :
    H (NumberIndex n × NumberIndex n) →L[ℂ] Fock n :=
  sliceCLM e ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap

theorem jointKraus_norm {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (x : H (NumberIndex n × NumberIndex n)) :
    HasSum (fun e => ‖jointKraus η hη e x‖^2) (‖x‖^2) := by
  convert! hasSum_slice_norm_sq (beamUnitary η hη x) using 1
  exact (beamUnitary η hη).norm_map x |>.symm |> congrArg (fun t : ℝ => t^2)

def rawJointKraus {n : ℕ} (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (τ : State n) := composite (jointKraus η hη) (firstKraus θ hθ τ)

theorem rawJointKraus_norm {n : ℕ} (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (τ : State n) (x : H (NumberIndex n × NumberIndex n)) :
    HasSum (fun e => ‖rawJointKraus η θ hη hθ τ e x‖^2) (‖x‖^2) :=
  composite_norm _ _ (jointKraus_norm η hη) (firstKraus_norm θ hθ τ) x

def rawDual {n : ℕ} (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (τ : State n) (Z : Fock n →L[ℂ] Fock n) :=
  dual (rawJointKraus η θ hη hθ τ) (rawJointKraus_norm η θ hη hθ τ) Z

end EntropyPhotonNumber

end

end OAI


