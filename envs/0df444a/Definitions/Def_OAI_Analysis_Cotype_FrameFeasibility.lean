-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_FrameFeasibility
-- name    : OAI_Analysis_Cotype_FrameFeasibility
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:17:24.256765+00:00
-- url     : https://prove2.me/theorems/27b61196-9670-4dbe-a649-9d103c69b338
-- title:
--   Prescribing pairings between two frames
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections.
--
--   1. **Tagged frames.** Given disjoint injections $f:\iota\to\nu$, $g:\kappa\to\nu$ and any matrix $D$, there are linearly independent families $U_i,V_j\in\mathbb K^\nu$ with $\langle V_j,U_i\rangle=D_{ij}$.
--   2. **Binary frames.** If $r+s\le n$, every $D\in\mathbb F_2^{r\times s}$ is realized by binary frames $U_1,\dots,U_r$ and $V_1,\dots,V_s$ with
--   $$
--   w_{V_j}(U_i)=\mathrm{sgn}(D_{ij}) .
--   $$
--   3. **Sign frames.** Equivalently, every sign pattern $S\in\{\pm1\}^{r\times s}$ is realized as the matrix of Walsh pairings between two frames.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/FrameFeasibility.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/FrameFeasibility.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {𝕜 : Type*} [Field 𝕜]
variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ν] [DecidableEq ν]

theorem tagged_frames_feasible (f : ι ↪ ν) (g : κ ↪ ν)
    (hfg : ∀ i j, f i ≠ g j) (D : ι → κ → 𝕜) :
    ∃ (U : ι → ν → 𝕜) (V : κ → ν → 𝕜),
      LinearIndependent 𝕜 U ∧ LinearIndependent 𝕜 V ∧
      ∀ i j, coordinateDual (V j) (U i) = D i j := by
  let U : ι → ν → 𝕜 := fun i => Pi.single (f i) 1
  let V : κ → ν → 𝕜 := fun j => (∑ i, D i j • U i) + Pi.single (g j) 1
  have hUf (i k : ι) : U i (f k) = if i = k then 1 else 0 := by
    simp [U, Pi.single_apply, f.injective.eq_iff, eq_comm]
  have hUg (i : ι) (j : κ) : U i (g j) = 0 := by
    simp [U, Ne.symm (hfg i j)]
  have hVf (i : ι) (j : κ) : V j (f i) = D i j := by
    simp [V, Finset.sum_apply, hUf, hfg i j]
  have hVg (j k : κ) : V j (g k) = if j = k then 1 else 0 := by
    simp [V, Finset.sum_apply, hUg, Pi.single_apply, g.injective.eq_iff, eq_comm]
  refine ⟨U,V,?_,?_,?_⟩
  · apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have h := congrFun hc (f i)
    simpa [Finset.sum_apply, hUf] using h
  · apply Fintype.linearIndependent_iff.mpr
    intro c hc j
    have h := congrFun hc (g j)
    simpa [Finset.sum_apply, hVg] using h
  · intro i j
    simpa [coordinateDual_apply, U, Pi.single_apply] using hVf i j

theorem binary_frames_feasible {n r s : ℕ} (hn : r+s ≤ n)
    (D : Fin r → Fin s → ZMod 2) :
    ∃ (U : Fin r → Cube n) (V : Fin s → Cube n),
      BinaryFrame U ∧ BinaryFrame V ∧
      ∀ i j, character (V j) (U i) = binarySign (D i j) := by
  let f : Fin r ↪ Fin n := ⟨fun i => Fin.castLE hn (Fin.castAdd s i), by
    intro i j h; apply Fin.ext; exact congrArg (fun x : Fin n => x.val) h⟩
  let g : Fin s ↪ Fin n := ⟨fun j => Fin.castLE hn (Fin.natAdd r j), by
    intro i j h; apply Fin.ext
    have hh := congrArg Fin.val h
    change r + i.val = r + j.val at hh
    omega⟩
  have hfg : ∀ i j, f i ≠ g j := by
    intro i j h
    have hh := congrArg Fin.val h
    change i.val = r + j.val at hh
    omega
  obtain ⟨U,V,hU,hV,hUV⟩ := tagged_frames_feasible f g hfg D
  refine ⟨fun i => (cubeBinaryEquiv n).symm (U i),
    fun j => (cubeBinaryEquiv n).symm (V j), ?_, ?_, ?_⟩
  · simpa [BinaryFrame] using hU
  · simpa [BinaryFrame] using hV
  · intro i j
    rw [character_binary_dot, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hUV]

theorem sign_frames_feasible {n r s : ℕ} (hn : r+s ≤ n) (S : Fin r × Fin s → Bool) :
    ∃ (U : Fin r → Cube n) (V : Fin s → Cube n),
      BinaryFrame U ∧ BinaryFrame V ∧
      ∀ i j, character (V j) (U i) = sign (S (i,j)) := by
  obtain ⟨U,V,hU,hV,hUV⟩ := binary_frames_feasible hn (fun i j => binaryBit (S (i,j)))
  refine ⟨U,V,hU,hV,fun i j => (hUV i j).trans ?_⟩
  cases S (i,j) <;> simp [binaryBit, sign]

end Cotype

end

end OAI


