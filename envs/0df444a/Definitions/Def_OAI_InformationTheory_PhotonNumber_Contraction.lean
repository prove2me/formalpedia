-- Prove2me | Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
-- name    : OAI_InformationTheory_PhotonNumber_Contraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T00:13:27.099641+00:00
-- url     : https://prove2.me/theorems/78be23b3-8876-49d6-b9cf-ba662c046dcf
-- title:
--   Centering, BKM quadratic form and normalized beam-splitter slice maps on operators
-- statement:
--   This file defines the linear maps on operators that compare a state's logarithmic-mean form with the forms of the beam-splitter inputs: centering with respect to a state, the Bogoliubov–Kubo–Mori (BKM) quadratic form, raw slice maps obtained from a two-stage beam-splitter channel, and their normalised versions.
--
--   Notation: for a Hilbert basis $(b_j)$ and an operator $Z$, $Z_{ij} = \langle b_i,Zb_j\rangle$; $L(p,q)$ is the logarithmic mean; $\mathcal F_n = \ell^2(\mathbb{N}^n)$; for a state $\rho$ (positive operator with $\sum_k\operatorname{Re}\langle k|\rho|k\rangle = 1$), $r^\rho_a = \sqrt\rho\,|a\rangle$ are its root columns; $\mathcal U_\eta$ is the beam-splitter unitary on $\ell^2(\mathbb{N}^n\times\mathbb{N}^n)$, and $z_e$ denotes the slice of a joint vector at second index $e$.
--
--   1. **Ensemble operations.** For a family $v$ and an operator $Z$, $\sum_i\|Zv_i\|^2$ is the second moment; the mixture of families $v$, $w$ with weight $t$ is the concatenated family $(\sqrt t\,v_i)_i\sqcup(\sqrt{1-t}\,w_j)_j$. For a thermal spectral space (basis $(b_i)$, weights $p_i>0$ summing to $1$, $r>0$) the ensemble is $(\sqrt{p_i}\,b_i)_i$.
--
--   2. **Mean, centering and the BKM form.** The mean of $Z$ under weights $p$ is $\mu_p(Z) = \sum_jp_jZ_{jj}$, and the centered operator is $Z-\mu_p(Z)\cdot1$. Entries are additive and homogeneous with $|Z_{ij}|\le\|Z\|$; for $p_j\ge0$ summable the mean series converges absolutely, $\mu_p$ is linear, and centering is a linear map. The BKM quadratic form is
--   $$
--   \mathcal Q_p(Z) = \sum_{i,j}L(p_i,p_j)\,|Z_{ij}|^2 .
--   $$
--
--   3. **Raw ensembles and slices.** For $\eta,\theta\in[0,1]$ and states $\rho,\sigma,\tau$, the raw ensemble consists of the vectors
--   $$
--   \Bigl(\mathcal U_\theta\bigl((\mathcal U_\eta(r^\rho_a\otimes r^\sigma_b))_e\otimes r^\tau_c\bigr)\Bigr)_{e'}
--   $$
--   indexed by $((a,b),(e,(e',c)))$ (together with an explicit reindexing bijection), obtained by applying the raw joint Kraus family (the joint Kraus maps $x\mapsto(\mathcal U_\eta x)_e$ followed by the first beam-splitter Kraus maps at $(\theta,\tau)$) to $r^\rho_a\otimes r^\sigma_b$. Writing $\Phi^*$ for the dual of the raw joint Kraus family, $\langle u,\Phi^*(Z)v\rangle = \sum\langle Ku,ZKv\rangle$, the raw first slice of $Z$ is the operator on $\mathcal F_n$ with
--   $$
--   \langle x,\ \mathcal R_1(Z)\,y\rangle = \sum_b\bigl\langle x\otimes r^\sigma_b,\ \Phi^*(Z)\,(y\otimes r^\sigma_b)\bigr\rangle,
--   $$
--   and the raw second slice $\mathcal R_2$ is defined in the same way with $r^\rho_a\otimes x$, $r^\rho_a\otimes y$. Both are linear in $Z$. For a thermal spectral space and $\lambda\in\mathbb{R}$, the normalisation is $Z\mapsto\lambda^{-1/2}\,(Z-\mu_p(Z)\cdot1)$, and the normalised slices are the pair (normalisation of $S_0$ with $\lambda_0$) $\circ\,\mathcal R_1$ and (normalisation of $S_1$ with $\lambda_1$) $\circ\,\mathcal R_2$.
--
--   4. **Spectral log data.** For spectral log data of a state $\rho$ (eigenbasis $(b_j)$, eigenvalues $\gamma_j>0$ summing to $1$, spectral columns $x_j$ with $W_3x_j = \sqrt{\gamma_j}\,b_j$, where $W_3$ multiplies the $k$-th coordinate by $(1+\sum_ik_i)^{-3}$) and $t>0$: the associated thermal spectral space uses $(b_j)$, $(\gamma_j)$ and $r=t$; one has $\sum_j|W_3x_j\rangle\langle W_3x_j| = \rho$, so the spectral columns form a weighted-column representation of $\rho$; and the ambient defect is the defect functional of the centered annihilation matrix on all of $\ell^2(J\times J)$.
--
--   These maps transport an operator on the output of the regularised beam splitter back to operators on each input, centred and rescaled so that their BKM-type norms can be compared with the output's.
--
--   **Formalization Note** `RawIndex n` is the index type $(\mathbb{N}^n\times\mathbb{N}^n)\times(\mathbb{N}^n\times(\mathbb{N}^n\times\mathbb{N}^n))$; `rawFirstSlice` and `rawSecondSlice` are `conditionalLeft`/`conditionalRight` of `rawDual`. The mean and the BKM form are `tsum`s ($0$ for divergent series); $\lambda^{-1/2}$ uses `Real.sqrt` and the convention $0^{-1} = 0$. `normalizedSlices` is indexed by `Fin 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Contraction.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Contraction.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

namespace EnsembleL2

section
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def secondMoment (v : I → E) (Z : E →L[ℂ] E) : ℝ := ∑' i, ‖Z (v i)‖^2

def mixture (v : I → E) (w : J → E) (t : ℝ) : I ⊕ J → E :=
  Sum.elim (fun i => (Real.sqrt t : ℂ) • v i) (fun j => (Real.sqrt (1-t) : ℂ) • w j)

end

open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

def ensemble (i : S.I) : E := (Real.sqrt (S.p i) : ℂ) • S.basis i

end ThermalSpectral.Space

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace BKM
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
def mean (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) : ℂ :=
  ∑' j, (p j : ℂ)*entry b Z j j
def center (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) : E →L[ℂ] E :=
  Z-mean b p Z • ContinuousLinearMap.id ℂ E
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace TensorLp
open KrausBounded
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate

abbrev RawIndex (n : ℕ) := (NumberIndex n × NumberIndex n) ×
  (NumberIndex n × (NumberIndex n × NumberIndex n))

def rawEnsemble {n : ℕ} (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (ik : RawIndex n) : Fock n :=
  rawJointKraus η θ hη hθ τ ik.2 (tensor (rootColumn ρ ik.1.1) (rootColumn σ ik.1.2))

def rawEnsembleEquiv (n : ℕ) : RawIndex n ≃
    (NumberIndex n × NumberIndex n) × (NumberIndex n × (NumberIndex n × NumberIndex n)) where
  toFun i := (i.2.2, (i.2.1,i.1))
  invFun i := (i.2.2,(i.2.1,i.1))
  left_inv _ := rfl
  right_inv _ := rfl

end EntropyPhotonNumber

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate
variable {n : ℕ}

def rawFirstSlice (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τ : State n) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  conditionalLeft (rootColumn σ) (rootColumn_norm σ) (rawDual η θ hη hθ τ Z)

def rawSecondSlice (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ τ : State n) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  conditionalRight (rootColumn ρ) (rootColumn_norm ρ) (rawDual η θ hη hθ τ Z)

end EntropyPhotonNumber

namespace EnsembleL2
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace EntropyPhotonNumber
open ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

end EntropyPhotonNumber

namespace BKM

section
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem entry_add (b : HilbertBasis J ℂ E) (Z T : E →L[ℂ] E) (i j : J) :
    entry b (Z+T) i j=entry b Z i j+entry b T i j := by simp [entry]
theorem entry_smul (b : HilbertBasis J ℂ E) (c : ℂ) (Z : E →L[ℂ] E) (i j : J) :
    entry b (c • Z) i j=c*entry b Z i j := by simp [entry]
theorem entry_norm_le (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (i j : J) :
    ‖entry b Z i j‖ ≤ ‖Z‖ := by
  calc
    _ ≤ ‖b i‖*‖Z (b j)‖ := norm_inner_le_norm _ _
    _ ≤ ‖b i‖*(‖Z‖*‖b j‖) := mul_le_mul_of_nonneg_left (Z.le_opNorm _) (norm_nonneg _)
    _ = ‖Z‖ := by simp [b.orthonormal.norm_eq_one]

theorem mean_summable (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z : E →L[ℂ] E) : Summable (fun j => (p j : ℂ)*entry b Z j j) := by
  apply (hs.mul_right ‖Z‖).of_norm_bounded
  intro j
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp j)]
  exact mul_le_mul_of_nonneg_left (entry_norm_le b Z j j) (hp j)

theorem mean_add (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z T : E →L[ℂ] E) : mean b p (Z+T)=mean b p Z+mean b p T := by
  simp only [mean, entry_add, mul_add]
  exact (mean_summable b p hp hs Z).tsum_add (mean_summable b p hp hs T)

theorem mean_smul (b : HilbertBasis J ℂ E) (p : J → ℝ) (c : ℂ) (Z : E →L[ℂ] E) :
    mean b p (c • Z)=c*mean b p Z := by
  simp only [mean, entry_smul, mul_left_comm (p _ : ℂ) c, tsum_mul_left]

end

section
open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def centerLM (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p) :
    (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E) where
  toFun := center b p
  map_add' Z T := by simp only [center, mean_add b p hp hs, add_smul]; abel
  map_smul' c Z := by simp [center, mean_smul, smul_sub, smul_smul]

@[simp] theorem centerLM_apply (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z : E →L[ℂ] E) : centerLM b p hp hs Z = center b p Z := rfl

end

open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end CenteredTests

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

def normalize (lam : ℝ) : (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E) :=
  (Real.sqrt lam : ℂ)⁻¹ • BKM.centerLM S.basis S.p (fun j => (S.pos j).le) S.sum.summable

end ThermalSpectral.Space

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

def rawFirstSliceLM (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τ : State n) : (Fock n →L[ℂ] Fock n) →ₗ[ℂ] (Fock n →L[ℂ] Fock n) where
  toFun := rawFirstSlice η θ hη hθ σ τ
  map_add' Z T := by simp only [rawFirstSlice, conditionalLeft, rawDual, dual_add]
  map_smul' c Z := by simp only [rawFirstSlice, conditionalLeft, rawDual, dual_smul, RingHom.id_apply]

def rawSecondSliceLM (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ τ : State n) : (Fock n →L[ℂ] Fock n) →ₗ[ℂ] (Fock n →L[ℂ] Fock n) where
  toFun := rawSecondSlice η θ hη hθ ρ τ
  map_add' Z T := by simp only [rawSecondSlice, conditionalRight, rawDual, dual_add]
  map_smul' c Z := by simp only [rawSecondSlice, conditionalRight, rawDual, dual_smul, RingHom.id_apply]

def normalizedSlices (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (S : Fin 2 → Space (Fock n)) (lam : Fin 2 → ℝ) :
    (i : Fin 2) → (Fock n →L[ℂ] Fock n) →ₗ[ℂ] (Fock n →L[ℂ] Fock n) :=
  ![((S 0).normalize (lam 0)).comp (rawFirstSliceLM η θ hη hθ σ τ),
    ((S 1).normalize (lam 1)).comp (rawSecondSliceLM η θ hη hθ ρ τ)]

end EntropyPhotonNumber

namespace BKM
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
def quadratic (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) : ℝ :=
  ∑' ij : J × J, logMean (p ij.1) (p ij.2)*Complex.normSq (entry b Z ij.1 ij.2)
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space ThermalMetric
variable {n : ℕ}

end EntropyPhotonNumber

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

def thermalSpace (t : ℝ) (ht : 0<t) : ThermalSpectral.Space (Fock n) where
  I := G.J
  basis := G.basis
  p := G.probability
  pos := G.probability_pos
  sum := G.probability_sum
  r := t
  rpos := ht

theorem inverse_spectralColumns_operator :
    CrossEnsemble.operator (fun r => inverseWeight 3 (G.spectralColumns r))
      (fun r => inverseWeight 3 (G.spectralColumns r))=ρ.op := by
  simp only [G.spectralColumns_inverse]
  exact CrossEnsemble.eigenEnsemble_operator G.basis G.probability
    (fun r => (G.probability_pos r).le) G.probability_sum.summable ρ.op ρ.positive.isSymmetric G.eigen

def weightedColumns : WeightedColumns ρ where
  Index := G.J
  vector := G.spectralColumns
  summable := G.spectralColumns_summable
  normalized := G.spectralColumns_normalized
  density := G.inverse_spectralColumns_operator

def ambientDefect (t : ℝ) (ht : 0<t) (j : Fin n) : lp (fun _ : G.J × G.J => ℂ) 2 →L[ℂ] ℂ :=
  defectFunctional t ht G.probability G.probability_pos (G.centeredMatrix j)
    (G.centeredMatrix_defect_summable t j)

end EntropyPhotonNumber.SpectralLogData

end

end OAI


