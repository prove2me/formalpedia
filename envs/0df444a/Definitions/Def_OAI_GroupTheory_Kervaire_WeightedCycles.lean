-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
-- name    : OAI_GroupTheory_Kervaire_WeightedCycles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:30:44.990826+00:00
-- url     : https://prove2.me/theorems/c074e07a-b90a-4c89-be1f-5b500c6b22cf
-- title:
--   Group phases and circuit weights
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Left operator.** The unitary $L(a)$ on $\ell^2(A)$, multiplicative in $a$.
--   2. **Group phase.** For a unit scalar $z$ and $a\in A$, the fractional phase of $zL(a)$ at $\delta_1$:
--   $$
--   \mathrm{gph}_z(a)=\mathrm{ph}_{\delta_1}\bigl(zL(a)\bigr).
--   $$
--   Its moments $\langle\delta_1,(zL(a))^n\delta_1\rangle$ equal $z^n$ if $a^n=1$ and $0$ otherwise.
--   3. **Circuit weights.** For a permutation $\sigma$ and labels $b$, the ordered product
--   $$
--   b(\sigma^{n-1}i)\cdots b(\sigma i)\,b(i)
--   $$
--   of labels along the first $n$ steps of the orbit of $i$. It lies in every submonoid containing the labels.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/WeightedCycles.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/WeightedCycles.lean by skeleton subtraction
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

namespace KervaireMatrix
open KervaireRegular KervaireSpectral
variable {A : Type*} [Group A]

end KervaireMatrix
namespace KervaireSpectral
open KervaireTraceCalculus
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

end KervaireSpectral

namespace KervaireRegular
open KervaireSpectral
open scoped Classical
variable {A : Type*} [Group A]

def leftOperator (a : A) : Operator A := (left a).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem leftOperator_delta (a x : A) :
    leftOperator a (delta x) = delta (a*x) := left_delta a x

@[simp] theorem leftOperator_one : leftOperator (1 : A) = 1 := by
  ext f x
  simp [leftOperator]

theorem leftOperator_mul (a b : A) : leftOperator (a*b) = leftOperator a * leftOperator b := by
  ext f x
  simp [leftOperator, mul_apply_eq_comp]

@[simp] theorem leftOperator_pow (a : A) (n : ℕ) : leftOperator (a^n) = leftOperator a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, leftOperator_mul, ih, pow_succ]

theorem leftOperator_unitary (a : A) : leftOperator a ∈ unitary (Operator A) := by
  rw [Unitary.mem_iff]
  have hs : star (leftOperator a) = leftOperator a⁻¹ := by
    change ContinuousLinearMap.adjoint (left a).toContinuousLinearEquiv.toContinuousLinearMap = _
    rw [LinearIsometryEquiv.adjoint_eq_symm]
    ext f x
    simp [leftOperator, left, reindex_symm, reindex_apply]
  rw [hs, ← leftOperator_mul, ← leftOperator_mul]
  simp

/-- Exact scalar-rotated fractional phase of a group element. -/
def groupPhase (z : ℂ) (hz : z ∈ unitary ℂ) (a : A) : ℝ :=
  let _ := isStarNormal_of_mem_unitary (Unitary.smul_mem ⟨z,hz⟩ (leftOperator_unitary a))
  vectorPhase (z • leftOperator a) (delta 1)

end KervaireRegular

namespace KervaireMatrix
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix
namespace KervaireCycle
open Fin.NatCast
variable {D B : Type*} [Monoid B]

/-- Circuit weights in their actual operator multiplication order. -/
def orbitWeight (σ : Equiv.Perm D) (b : D → B) : ℕ → D → B
  | 0, _ => 1
  | n+1, i => b ((σ^n) i) * orbitWeight σ b n i

@[simp] theorem orbitWeight_zero (σ : Equiv.Perm D) (b : D → B) (i : D) :
    orbitWeight σ b 0 i = 1 := rfl
@[simp] theorem orbitWeight_succ (σ : Equiv.Perm D) (b : D → B) (n : ℕ) (i : D) :
    orbitWeight σ b (n+1) i = b ((σ^n) i) * orbitWeight σ b n i := rfl

/-- The rotate permutation is addition modulo its size. -/
theorem rotate_pow_apply (d : ℕ) [NeZero d] (n : ℕ) (i : Fin d) :
    ((finRotate d)^n) i = i + (↑n : Fin d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, ih]
    simp [Nat.cast_add, add_assoc]

@[simp] theorem rotate_pow_self (d : ℕ) [NeZero d] : (finRotate d)^d = 1 := by
  ext i
  rw [rotate_pow_apply]
  simp

end KervaireCycle

namespace KervaireMatrix
open KervaireRegular KervaireCycle
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix
namespace KervaireCycle
variable {D B : Type*} [Monoid B]

/-- All full and partial circuit products remain in any submonoid containing the labels. -/
theorem orbitWeight_mem (H : Submonoid B) (σ : Equiv.Perm D) (b : D → B)
    (hb : ∀ i, b i ∈ H) (n : ℕ) (i : D) : orbitWeight σ b n i ∈ H := by
  induction n with
  | zero => exact H.one_mem
  | succ n ih => exact H.mul_mem (hb _) ih

end KervaireCycle

namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireCycle
open Fin.NatCast
variable {A : Type*} [Group A]

end KervaireMatrix

end

end OAI


