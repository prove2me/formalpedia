-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
-- name    : OAI_GroupTheory_Kervaire_SignedIncidence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:14:37.793781+00:00
-- url     : https://prove2.me/theorems/58efea15-f955-4a6b-a4d0-5e94596d83cd
-- title:
--   Paired maps and sign coordinates
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Block swap.** The unitary $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ on $L\sqcup L$.
--   2. **Paired and core maps.** For a unitary map $Y$, the maps $X\mapsto\mathrm{diag}(X,Y(X),Y(X)^*)$ and $X\mapsto\mathrm{diag}(X,1)$, and right multiplication of a unitary map by a fixed unitary.
--   3. **Sign classes.** For signs $s:I\to\mathbb Z$, the positive positions $\{s_i=1\}$ and the others. When there is one more positive than negative position, a bijection identifies the positives with a point plus the negatives.
--   4. **Repeated and signed matrices.** Block matrices repeating a unitary over positions, arranged according to the signs.
--
--   These express the traversal of a unimodular relator as a unitary map homotopic to the model.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/SignedIncidence.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/SignedIncidence.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Kervaire mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace KervaireIncidenceCurrent

section
open KervaireUnitaryHomotopy
variable {K L : Type*} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]

lemma contDiff_diag {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Mat K} {g : E → Mat L} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x ↦ diag (f x) (g x)) := by
  simp only [diag_eq_corner]
  exact ((in11 (K := K) (R := L)).contDiff.comp hf).add
    ((in22 (K := K) (R := L)).contDiff.comp hg)

def swapBlocks : unitary (Mat (L ⊕ L)) :=
  ⟨Matrix.fromBlocks 0 1 1 0,by
    constructor <;>
      simp [star_eq_conjTranspose,Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply,← Matrix.fromBlocks_one]⟩

def pairedMap (Y : UMap (Mat K) (Mat L)) : UMap (Mat K) (Mat (K ⊕ (L ⊕ L))) where
  toFun X := diag X (diag (Y X) (star (Y X)))
  smooth := contDiff_diag contDiff_id (contDiff_diag Y.smooth ((starL ℝ).contDiff.comp Y.smooth))
  unitary X := diag_unitary X.property (diag_unitary (Y.unitary X) (by
    simpa only [Unitary.star_mem_iff] using Y.unitary X))

def coreMap : UMap (Mat K) (Mat (K ⊕ (L ⊕ L))) where
  toFun X := diag X 1
  smooth := contDiff_diag contDiff_id contDiff_const
  unitary X := diag_unitary X.property (by simp)

def rightMulMap {I : Type*} [Fintype I] [DecidableEq I]
    (F : UMap (Mat K) (Mat I)) (P : unitary (Mat I)) : UMap (Mat K) (Mat I) where
  toFun X := F X * P
  smooth := F.smooth.mul contDiff_const
  unitary X := (unitary _).mul_mem (F.unitary X) P.property

end

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

def includeFirst : (K → ℂ) →ₗ[ℂ] ((K ⊕ R) → ℂ) where
  toFun v := Sum.elim v (fun _ ↦ 0)
  map_add' v w := by ext i; cases i <;> simp
  map_smul' c v := by ext i; cases i <;> simp

end

open KervaireUnitaryHomotopy
variable {K L : Type*} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
end KervaireIncidenceCurrent

namespace KervaireSignPairing

section
open Matrix
variable {I K : Type*} [Fintype I]

abbrev positive (s : I → ℤ) := {i // s i = 1}
abbrev negative (s : I → ℤ) := {i // s i ≠ 1}

noncomputable def positiveEquiv (s : I → ℤ)
    (hc : Fintype.card (positive s) = Fintype.card (negative s) + 1) :
    Unit ⊕ negative s ≃ positive s := Fintype.equivOfCardEq (by
  simpa only [Fintype.card_sum,Fintype.card_unit] using (Nat.add_comm _ _).trans hc.symm)

noncomputable def signsEquiv (s : I → ℤ)
    (hc : Fintype.card (positive s) = Fintype.card (negative s) + 1) :
    (Unit ⊕ negative s) ⊕ negative s ≃ I :=
  (Equiv.sumCongr (positiveEquiv s hc) (Equiv.refl _)).trans (Equiv.sumCompl (fun i ↦ s i = 1))

noncomputable def coordinates (s : I → ℤ)
    (hc : Fintype.card (positive s) = Fintype.card (negative s) + 1) :
    K ⊕ ((K × negative s) ⊕ (K × negative s)) ≃ K × I :=
  (Equiv.sumAssoc K (K × negative s) (K × negative s)).symm.trans
    ((Equiv.sumCongr ((Equiv.sumCongr (Equiv.prodUnique K Unit).symm (Equiv.refl _)).trans
      (Equiv.prodSumDistrib K Unit (negative s)).symm) (Equiv.refl _)).trans
        ((Equiv.prodSumDistrib K (Unit ⊕ negative s) (negative s)).symm.trans
          (Equiv.prodCongr (Equiv.refl K) (signsEquiv s hc))))

end

open Matrix KervaireIncidenceCurrent KervaireUnitaryHomotopy
open scoped Matrix.Norms.L2Operator
variable {I K D : Type*} [Fintype I] [Fintype K] [Fintype D]
  [DecidableEq I] [DecidableEq K] [DecidableEq D]

def repeatMatrix (X : Mat K) : Mat (K × D) := blockDiagonal (fun _ ↦ X)

def repeatMap : UMap (Mat K) (Mat (K × D)) where
  toFun := repeatMatrix
  smooth := by
    let L : Mat K →ₗ[ℝ] Mat (K × D) :=
      { toFun := repeatMatrix
        map_add' := by intro X Y; exact blockDiagonal_add _ _
        map_smul' := by intro c X; exact blockDiagonal_smul c _ }
    exact L.toContinuousLinearMap.contDiff
  unitary X := by
    have h1 : (X : Mat K).conjTranspose * X = 1 := X.property.1
    have h2 : (X : Mat K) * (X : Mat K).conjTranspose = 1 := X.property.2
    constructor <;>
      simp only [repeatMatrix,star_eq_conjTranspose,blockDiagonal_conjTranspose,
        ← blockDiagonal_mul,h1,h2]
    all_goals exact blockDiagonal_one

def signedMatrix (s : I → ℤ) (X : Mat K) : Mat (K × I) :=
  blockDiagonal (fun i ↦ if s i = 1 then X else star X)

end KervaireSignPairing

end

end OAI


