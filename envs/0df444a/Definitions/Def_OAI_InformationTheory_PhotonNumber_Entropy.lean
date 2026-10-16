-- Prove2me | Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
-- name    : OAI_InformationTheory_PhotonNumber_Entropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:37:43.881688+00:00
-- url     : https://prove2.me/theorems/586419c7-525c-446b-9ff8-edcef2e6138d
-- title:
--   Energy-bounded state sets, thermal moments and the regularized beam-splitter objective
-- statement:
--   This file sets up the variational framework around the entropy of bosonic states: energies and number moments, sets of states with bounded moments, a regularized version of the beam-splitter output, and the objective functional combining output and input entropies.
--
--   Notation: $\mathcal F_n = \ell^2(\mathbb{N}^n)$ with number basis $|k\rangle$, $|k| = \sum_jk_j$, $\nu(k) = 1+|k|$. A state is a positive bounded operator $\rho$ with $\sum_k\operatorname{Re}\langle k|\rho|k\rangle = 1$, and its von Neumann entropy is $S(\rho) = \sum_k\operatorname{Re}\langle k|-\rho\log\rho|k\rangle$ (functional calculus with $-t\log t$). Its $m$-th number moment is $M_m(\rho) = \sum_k(1+|k|)^m\langle k|\rho|k\rangle$, and it has finite energy if $\sum_k|k|\,\langle k|\rho|k\rangle$ converges. $\mathrm{BS}_\eta(\rho,\sigma)$ ($\eta\in[0,1]$) denotes the beam-splitter output state constructed as a partial trace, and $\tau_r$ the thermal state with diagonal entries $\prod_j(r+1)^{-1}(r/(r+1))^{k_j}$.
--
--   1. **Generator pairings and drift.** For a bounded real function $f$ on $\mathbb{N}^n$ the diagonal operator multiplies $x_k$ by $f(k)$. With the weighted gains $G^\pm_j$, mode bounds $B^\pm_j$ (diagonal, entries $(k_j+[\pm=+])/\nu(k)$) and $W_1$ (entries $\nu(k)^{-1}$), the column pairing of a vector $x$ with an operator $Z$ is
--   $$
--   \sum_{j=1}^n\Bigl[(r+1)\Bigl(\operatorname{Re}\langle G^-_jx,ZG^-_jx\rangle - \tfrac{\operatorname{Re}\langle W_1x,ZB^-_jx\rangle+\operatorname{Re}\langle B^-_jx,ZW_1x\rangle}{2}\Bigr) + r\Bigl(\text{same with }+\Bigr)\Bigr],
--   $$
--   and its $j$-th summand is the component pairing. The drift of $f$ is $(\mathcal Df)(k) = \sum_j\bigl[(r+1)\,k_j\,(f(k-e_j)-f(k)) + r\,(k_j+1)\,(f(k+e_j)-f(k))\bigr]$ (with $k-e_j$ truncated at $0$).
--
--   2. **Truncations and moment sets.** The number box is $\{k: k_j\le K\ \forall j\}$; for a Hilbert basis $(b_i)$ and finite $S$, $P_S = \sum_{i\in S}|b_i\rangle\langle b_i|$ is self-adjoint and maps $b_j$ to $b_j$ or $0$ according as $j\in S$; finite matrices $c$ embed as $\sum_{i,j\in S}c_{ij}|b_i\rangle\langle b_j|$. For a basis indexed by $\mathbb{N}^n$, the energy set $\mathcal S_E$ consists of the positive operators $T$ with $\sum_k\operatorname{Re}\langle b_k,Tb_k\rangle = 1$ and $\sum_k|k|\operatorname{Re}\langle b_k,Tb_k\rangle\le E$ (convergent), and the moment set adds $\sum_kw_k\operatorname{Re}\langle b_k,Tb_k\rangle\le M$ (convergent). Elements of the moment set for the number basis and $w_k = (1+|k|)^4$ are states. States carry the topology induced by the operator norm, and the bounded states are
--   $$
--   \mathcal B(E,M) = \{\rho:\ \rho\text{ has finite energy},\ E(\rho)\le E,\ M_4(\rho)<\infty,\ M_4(\rho)\le M\},
--   $$
--   where $E(\rho) = \sum_k|k|\,\langle k|\rho|k\rangle\ge0$.
--
--   3. **Moments of thermal states.** For nonnegative summable $w$, $k\mapsto\prod_jw(k_j)$ is summable on $\mathbb{N}^n$; $1+\sum_ia_i\le\prod_i(1+a_i)$ for $a_i\ge0$; $\sum_k(1+k)^mq^k<\infty$ for $0<q<1$. Hence every thermal state $\tau_r$ ($r>0$) has finite moments of every order and finite energy; a finite $m$-th moment with $m\ge1$ implies finite energy, and for finite-energy states the $[0,\infty]$-valued energy equals $E(\rho)$. Entries of mixtures are $t\langle k|\rho|l\rangle+(1-t)\langle k|\sigma|l\rangle$, and $(x,y)\mapsto x\otimes y$ is a bounded bilinear map of norm at most $1$.
--
--   4. **Regularization and objective.** For $\eta,\delta,\kappa\in[0,1]$ and states $\tau_D,\tau_0,\rho,\sigma$, the regularized output is
--   $$
--   \mathrm{Out}(\rho,\sigma) = (1-\kappa)\,\mathrm{BS}_{1-\delta}\bigl(\mathrm{BS}_\eta(\rho,\sigma),\tau_D\bigr) + \kappa\,\tau_0 .
--   $$
--   A regularization consists of such parameters with finite-energy $\tau_D,\tau_0$ and positive constants $c,a_1,a_2,b_1,b_2,\zeta$; its objective is
--   $$
--   \Psi(\rho,\sigma) = c\,S(\mathrm{Out}(\rho,\sigma)) - a_1S(\rho) - a_2S(\sigma) + b_1E(\rho)+\zeta M_4(\rho) + b_2E(\sigma)+\zeta M_4(\sigma),
--   $$
--   and its entropy constant is $a_1n\log(2a_1/b_1+1)+a_2n\log(2a_2/b_2+1)$.
--
--   5. **Basis moments and Kraus composition.** For weights $w_i\in[0,\infty]$: $\sum_iw_i|\langle b_i,x\rangle|^2$ (basis moment of a vector), $\sum_iw_i\max(\operatorname{Re}\langle b_i,Tb_i\rangle,0)$ (basis expectation), the number moment $\sum_k|k|\,|x_k|^2$ of a vector, slice moments $\sum_i(\text{basis moment of }V_ix)$, and slice coordinates $x\mapsto\sqrt{w_j}\,\langle b_j,V_iSx\rangle$; the energy inverse is the diagonal operator with entries $\nu(k)^{-1/2}$. Finally, if $v$ is a normalised ensemble of $\rho$ ($\sum\|v_j\|^2 = 1$, $\sum|v_j\rangle\langle v_j| = \rho$), then applying the first beam-splitter Kraus family for $(\eta,\sigma)$ and then that for $(\theta,\tau)$ yields an ensemble of $\mathrm{BS}_\theta(\mathrm{BS}_\eta(\rho,\sigma),\tau)$.
--
--   The objective $\Psi$ is the functional whose behaviour over the bounded state sets is studied in the variational approach: the regularization (extra mixing with $\tau_D$ and $\tau_0$, and moment penalties) keeps all quantities finite while preserving the beam-splitter structure.
--
--   **Formalization Note** `energy ρ` and `numberMoment 4 ρ` are real `tsum`s ($0$ for divergent series), which is why finiteness is stated separately in $\mathcal B(E,M)$. The topology `stateTopology` is induced by `State.op`. `Regularization n` is a structure; `entropy` is the main definition $-\operatorname{Tr}\rho\log\rho$ computed as a `tsum` of diagonal entries.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace Annihilation
open EntropyPhotonNumber QuantumTrace WeightedShift
open scoped ComplexConjugate
variable {n : ℕ}

def diagonal (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ k, |f k| ≤ C) :
    Fock n →L[ℂ] Fock n :=
  pullCLM id Function.injective_id (fun k => (f k:ℂ)) C hC
    (fun k => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf k)

@[simp] theorem diagonal_apply (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k| ≤ C) (x : Fock n) (k : NumberIndex n) :
    diagonal f C hC hf x k=(f k:ℂ)*x k := rfl

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped BigOperators
variable {n : ℕ} {I : Type*}

def columnPairing (r : ℝ) (x : Fock n) (Z : Fock n →L[ℂ] Fock n) : ℝ :=
  ∑ j, ((r+1)*((inner ℂ (gain j false x) (Z (gain j false x))).re-
      ((inner ℂ (inverseWeight 1 x) (Z (modeBound j false x))).re+
       (inner ℂ (modeBound j false x) (Z (inverseWeight 1 x))).re)/2)+
    r*((inner ℂ (gain j true x) (Z (gain j true x))).re-
      ((inner ℂ (inverseWeight 1 x) (Z (modeBound j true x))).re+
       (inner ℂ (modeBound j true x) (Z (inverseWeight 1 x))).re)/2))

def drift (r : ℝ) (f : NumberIndex n → ℝ) (k : NumberIndex n) : ℝ :=
  ∑ j, ((r+1)*(k j:ℝ)*(f (down j k)-f k)+r*((k j:ℝ)+1)*(f (up j k)-f k))

def componentPairing (r : ℝ) (x : Fock n) (Z : Fock n →L[ℂ] Fock n) (j : Fin n) : ℝ :=
  (r+1)*((inner ℂ (gain j false x) (Z (gain j false x))).re-
    ((inner ℂ (inverseWeight 1 x) (Z (modeBound j false x))).re+
     (inner ℂ (modeBound j false x) (Z (inverseWeight 1 x))).re)/2)+
  r*((inner ℂ (gain j true x) (Z (gain j true x))).re-
    ((inner ℂ (inverseWeight 1 x) (Z (modeBound j true x))).re+
     (inner ℂ (modeBound j true x) (Z (inverseWeight 1 x))).re)/2)

end WeightedGenerator

namespace WeightedShift
variable {I K : Type*}
end WeightedShift

namespace EntropyPhotonNumber
open QuantumTrace WeightedShift Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section
open Filter Topology

def numberBox (n K : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun _ => Finset.range (K + 1))

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

def basisProjection (b : HilbertBasis ι ℂ H) (s : Finset ι) : H →L[ℂ] H :=
  basisApprox b (ContinuousLinearMap.id ℂ H) s

omit [CompleteSpace H] in
theorem basisProjection_apply_basis (b : HilbertBasis ι ℂ H) (s : Finset ι) (j : ι)
    [Decidable (j ∈ s)] : basisProjection b s (b j) = if j ∈ s then b j else 0 := by
  simpa [basisProjection] using basisApprox_apply_basis b (ContinuousLinearMap.id ℂ H) s j

theorem basisProjection_adjoint (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    adjoint (basisProjection b s) = basisProjection b s := by
  simp [basisProjection, basisApprox]

end

section
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def energySet {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H) (E : ℝ) : Set (H →L[ℂ] H) :=
  {T | T.IsPositive ∧
    HasSum (fun k => (inner ℂ (b k) (T (b k))).re) 1 ∧
    Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re) ∧
    (∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re) ≤ E}

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

def matrixEmbed (b : HilbertBasis ι ℂ H) (s : Finset ι) (c : s → s → ℂ) : H →L[ℂ] H :=
  ∑ i, ∑ j, c i j • rankOne ℂ (b i) (b j)

end

section
open ContinuousLinearMap Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def momentSet {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H)
    (w : (Fin n → ℕ) → ℝ) (E M : ℝ) : Set (H →L[ℂ] H) :=
  {T | T ∈ energySet b E ∧
    Summable (fun k => w k * (inner ℂ (b k) (T (b k))).re) ∧
    (∑' k, w k * (inner ℂ (b k) (T (b k))).re) ≤ M}

end QuantumTrace

end

namespace EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

def energy {n : ℕ} (ρ : State n) : ℝ :=
  ∑' k, (totalNumber k : ℝ) * (entry ρ.op k k).re

theorem energy_nonneg {n : ℕ} (ρ : State n) : 0 ≤ energy ρ := by
  exact tsum_nonneg (fun k => mul_nonneg (Nat.cast_nonneg _)
    (ρ.positive.re_inner_nonneg_right _))

end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal

namespace TraceEnsemble
open Filter Topology
open scoped BigOperators
variable {I A E G : Type*}
variable [NormedAddCommGroup G] [CompleteSpace G]

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end TraceEnsemble

namespace TensorLp
variable {A B : Type*}

def tensorBilinear : H A →L[ℂ] H B →L[ℂ] H (A × B) :=
  LinearMap.mkContinuous
    { toFun := tensorLeft
      map_add' := fun x y => by
        apply ContinuousLinearMap.ext
        intro z
        apply lp.ext
        funext ab
        change (x ab.1+y ab.1)*z ab.2 = x ab.1*z ab.2 + y ab.1*z ab.2
        ring
      map_smul' := fun c x => by
        apply ContinuousLinearMap.ext
        intro z
        apply lp.ext
        funext ab
        change (c*x ab.1)*z ab.2 = c*(x ab.1*z ab.2)
        ring }
    1 (fun x => by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro y
      change ‖tensor x y‖ ≤ (1*‖x‖)*‖y‖
      rw [tensor_norm, one_mul])

@[simp] theorem tensorBilinear_apply (x : H A) (y : H B) : tensorBilinear x y = tensor x y := rfl

end TensorLp

namespace EntropyPhotonNumber

section
open Filter Topology TensorLp

end

open QuantumTrace TraceEnsemble
@[simp] theorem mixture_entry {n : ℕ} (t : ℝ) (ht : t ∈ Set.Icc 0 1) (ρ σ : State n)
    (k l : NumberIndex n) :
    entry (mixture t ht ρ σ).op k l = (t : ℂ)*entry ρ.op k l + ((1-t : ℝ) : ℂ)*entry σ.op k l := by
  simp only [mixture, entry, add_apply, smul_apply,
    inner_add_right, inner_smul_right]

end EntropyPhotonNumber

namespace QuantumTrace
open scoped ENNReal

theorem summable_finite_product (n : ℕ) (w : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hs : Summable w) :
    Summable (fun k : Fin n → ℕ => ∏ j, w (k j)) := by
  have hh : (∑' k : Fin n → ℕ, ENNReal.ofReal (∏ j, w (k j))) < ⊤ := by
    simp only [ENNReal.ofReal_prod_of_nonneg (fun _ _ => hw _)]
    rw [tsum_finite_product n (fun k => ENNReal.ofReal (w k))]
    exact ENNReal.pow_lt_top hs.tsum_ofReal_lt_top
  have he := ENNReal.summable_toReal hh.ne
  simpa only [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun _ _ => hw _))] using he

theorem one_add_sum_le_product {I : Type*} (s : Finset I) (a : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) : 1+∑ i ∈ s, a i ≤ ∏ i ∈ s, (1+a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hp : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg (fun j _ => ha j)
    have hm := mul_le_mul_of_nonneg_left ih (by linarith [ha i] : 0 ≤ 1+a i)
    nlinarith [mul_nonneg (ha i) hp]

theorem summable_shift_pow_geometric {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (m : ℕ) :
    Summable (fun k : ℕ => (1+(k : ℝ))^m*q^k) := by
  have hs := (summable_pow_mul_geometric_of_norm_lt_one m
    (show ‖q‖ < 1 by rwa [Real.norm_eq_abs, abs_of_pos hq])).comp_injective Nat.succ_injective
  convert! hs.mul_left q⁻¹ using 1
  funext k
  change (1+(k : ℝ))^m*q^k = q⁻¹*((k+1 : ℕ)^m*q^(k+1))
  simp only [Nat.cast_succ, pow_succ]
  rw [add_comm (k : ℝ) 1]
  field_simp

theorem thermalWeight_moment_summable (n m : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable (fun k : Fin n → ℕ => (1+∑ j, (k j : ℝ))^m * thermalWeight n r k) := by
  let q := r/(r+1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := (div_lt_one (by linarith : 0 < r+1)).mpr (by linarith)
  have hs := summable_finite_product n
    (fun k => (1+(k : ℝ))^m*((r+1)⁻¹*q^k))
    (fun _ => by positivity)
    (by simpa only [mul_left_comm _ (r+1)⁻¹] using
      (summable_shift_pow_geometric hq hq1 m).mul_left (r+1)⁻¹)
  apply Summable.of_nonneg_of_le (fun _ => by apply mul_nonneg _ (thermalWeight_pos n hr _).le; positivity) _ hs
  intro k
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+∑ j, (k j : ℝ))
    (one_add_sum_le_product Finset.univ (fun j => (k j : ℝ)) (fun _ => Nat.cast_nonneg _)) m
  have hh := mul_le_mul_of_nonneg_right h (thermalWeight_pos n hr k).le
  simpa only [← Finset.prod_pow, thermalWeight, ← Finset.prod_mul_distrib, q] using hh

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
theorem thermalState_finiteMoment (n m : ℕ) (r : ℝ) (hr : 0 < r) :
    FiniteMoment m (thermalState n r hr) := by
  simpa only [FiniteMoment, thermalState_diagonal, totalNumber, Nat.cast_sum] using
    thermalWeight_moment_summable n m hr

theorem finiteMoment_finiteEnergy {n m : ℕ} (hm : 1 ≤ m) {ρ : State n} (hρ : FiniteMoment m ρ) :
    FiniteEnergy ρ := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (Nat.cast_nonneg _) (ρ.positive.re_inner_nonneg_right _)) _ hρ
  intro k
  have h : (1+(totalNumber k : ℝ))^1 ≤ (1+(totalNumber k : ℝ))^m :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (totalNumber k)]) hm
  exact mul_le_mul_of_nonneg_right (by simpa only [pow_one] using (by linarith :
    (totalNumber k : ℝ) ≤ (1+(totalNumber k : ℝ))^m)) (ρ.positive.re_inner_nonneg_right _)

theorem thermalState_finiteEnergy (n : ℕ) (r : ℝ) (hr : 0 < r) :
    FiniteEnergy (thermalState n r hr) :=
  finiteMoment_finiteEnergy le_rfl (thermalState_finiteMoment n 1 r hr)

end

open QuantumTrace Filter Topology

theorem energyMoment_ofReal {n : ℕ} {ρ : State n} (hρ : FiniteEnergy ρ) :
    energyMoment ρ = ENNReal.ofReal (energy ρ) := by
  rw [energyMoment_eq]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun k => mul_nonneg (Nat.cast_nonneg _) (ρ.positive.re_inner_nonneg_right _)) hρ).symm

def regularizedOutput {n : ℕ} (η δ κ : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hδ : δ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1) (τD τ0 ρ σ : State n) : State n :=
  mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
    (beamOutput (1-δ) ⟨sub_nonneg.mpr hδ.2, sub_le_self _ hδ.1⟩
      (beamOutput η hη ρ σ) τD) τ0

instance stateTopology (n : ℕ) : TopologicalSpace (State n) :=
  TopologicalSpace.induced State.op inferInstance

def boundedStates (n : ℕ) (E M : ℝ) : Set (State n) :=
  {ρ | FiniteEnergy ρ ∧ energy ρ ≤ E ∧ FiniteMoment 4 ρ ∧ numberMoment 4 ρ ≤ M}

def stateOfMomentSet {n : ℕ} {E M : ℝ}
    (T : momentSet (numberBasis n) (fun k => (1+(totalNumber k : ℝ))^4) E M) : State n where
  op := T.val
  positive := T.property.1.1
  trace_one := by simpa only [numberBasis_apply, entry] using T.property.1.2.1

structure Regularization (n : ℕ) where
  η : ℝ
  δ : ℝ
  κ : ℝ
  hη : η ∈ Set.Icc 0 1
  hδ : δ ∈ Set.Icc 0 1
  hκ : κ ∈ Set.Icc 0 1
  τD : State n
  τ0 : State n
  finiteD : FiniteEnergy τD
  finite0 : FiniteEnergy τ0
  c : ℝ
  a1 : ℝ
  a2 : ℝ
  b1 : ℝ
  b2 : ℝ
  ζ : ℝ
  hc : 0 < c
  ha1 : 0 < a1
  ha2 : 0 < a2
  hb1 : 0 < b1
  hb2 : 0 < b2
  hζ : 0 < ζ

namespace Regularization
variable {n : ℕ} (R : Regularization n)

def output (ρ σ : State n) : State n :=
  regularizedOutput R.η R.δ R.κ R.hη R.hδ R.hκ R.τD R.τ0 ρ σ

def objective (ρ σ : State n) : ℝ :=
  R.c*entropy (R.output ρ σ)-R.a1*entropy ρ-R.a2*entropy σ+
    (R.b1*energy ρ+R.ζ*numberMoment 4 ρ)+(R.b2*energy σ+R.ζ*numberMoment 4 σ)

def entropyConstant : ℝ :=
  R.a1*n*Real.log (2*R.a1/R.b1+1)+R.a2*n*Real.log (2*R.a2/R.b2+1)

end Regularization
end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I J : Type*}

def basisMoment (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  ∑' i, w i*ENNReal.ofReal (‖inner ℂ (b i) x‖^2)

def basisExpectation (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) (T : E →L[ℂ] E) : ℝ≥0∞ :=
  ∑' i, w i*ENNReal.ofReal (inner ℂ (b i) (T (b i))).re

variable [CompleteSpace E]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

def numberVectorMoment {n : ℕ} (x : Fock n) : ℝ≥0∞ :=
  basisMoment (numberBasis n) (fun k => (totalNumber k : ℝ≥0∞)) x

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

def sliceMoment (b : HilbertBasis J ℂ E) (w : J → ℝ≥0∞)
    (V : I → E →L[ℂ] E) (x : E) : ℝ≥0∞ := ∑' i, basisMoment b w (V i x)

def sliceCoordinates (b : HilbertBasis J ℂ E) (w : J → ℝ)
    (V : I → E →L[ℂ] E) (S : E →L[ℂ] E) (ij : I × J) : E →ₗ[ℂ] ℂ :=
  (Real.sqrt (w ij.2) : ℂ) • ((innerSL ℂ (b ij.2)).toLinearMap.comp
    ((V ij.1).toLinearMap.comp S.toLinearMap))

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace TensorLp

def energyInverse (n : ℕ) : Fock n →L[ℂ] Fock n :=
  inversePower rootNumberWeight rootNumberWeight_one_le 1

end

open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {ι J L : Type*}

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace TensorLp

theorem composedKraus_first_ensemble {n : ℕ} {J : Type*}
    (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (ρ σ τ : State n)
    (v : J → Fock n) (hv : HasSum (fun j => ‖v j‖^2) 1)
    (he : TraceEnsemble.operator v = ρ.op) :
    TraceEnsemble.operator (fun z : ((NumberIndex n × NumberIndex n) ×
      (NumberIndex n × NumberIndex n)) × J =>
      composeKraus (firstKraus θ hθ τ) (firstKraus η hη σ) z.1 (v z.2)) =
      (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op := by
  have hV := TraceEnsemble.kraus_hasSum (firstKraus_norm η hη σ) hv
  have heV := firstKraus_ensemble η hη ρ σ v hv he
  have heU := firstKraus_ensemble θ hθ (beamOutput η hη ρ σ) τ _ hV heV
  exact (composeKraus_ensemble (firstKraus θ hθ τ) (firstKraus η hη σ) v).trans heU

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {J : Type*}

end QuantumTrace

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

end EntropyPhotonNumber

end

end OAI


