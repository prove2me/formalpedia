-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_Reynolds
-- name    : OAI_Probability_ThorpShuffle_Reynolds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T04:10:24.65731+00:00
-- url     : https://prove2.me/theorems/8e907df6-8fa6-417a-a825-bd6922f36179
-- title:
--   Reynolds averaging of linear maps, convolution and the delta function on a finite group
-- statement:
--   Let $G$ be a finite group, and let $\rho$ and $\sigma$ be representations of $G$ on complex vector spaces $V$ and $W$ (of arbitrary dimension; no inner product is needed). The file introduces the following objects.
--
--   1. **Reynolds operator.** For a $\mathbb{C}$-linear map $A:V\to W$, its average over $G$ is the linear map
--   $$\mathcal{R}_{\rho,\sigma}(A)=\frac{1}{|G|}\sum_{g\in G}\sigma(g)\circ A\circ\rho(g^{-1}).$$
--   The file also proves that it is $G$-equivariant: $\mathcal{R}_{\rho,\sigma}(A)\big(\rho(h)v\big)=\sigma(h)\big(\mathcal{R}_{\rho,\sigma}(A)v\big)$ for all $h\in G$ and $v\in V$.
--   2. **Reynolds intertwiner.** The same map $\mathcal{R}_{\rho,\sigma}(A)$, regarded as a morphism of representations (an intertwining map) from $\rho$ to $\sigma$; this is legitimate by the equivariance in item 1.
--   3. **Convolution.** For functions $f,k:G\to\mathbb{C}$, the convolution $f*k:G\to\mathbb{C}$ is
--   $$(f*k)(x)=\sum_{g\in G}f(g)\,k(g^{-1}x),\qquad x\in G.$$
--   4. **Delta function.** $\delta:G\to\mathbb{C}$ is the indicator of the identity element: $\delta(1)=1$ and $\delta(g)=0$ for $g\ne 1$. It is the unit for convolution, $\delta*k=k=k*\delta$.
--
--   The Reynolds operator is the standard device behind Schur-lemma arguments: if $V$ is finite-dimensional and $\rho$ is irreducible, then $\mathcal{R}_{\rho,\rho}(A)$ is a scalar multiple of the identity with the same trace as $A$, and if $\rho$ and $\sigma$ are irreducible and inequivalent, then $\mathcal{R}_{\rho,\sigma}(A)=0$. Convolution and $\delta$ realise the group algebra $\mathbb{C}[G]$ as functions on $G$; in this picture the normalised characters of the irreducible representations become orthogonal idempotents, which is the starting point of the Fourier analysis on finite groups used for averaging operators $\sum_g\nu(g)\rho(g)$.
--
--   **Formalization Note** The Lean names are `reynolds`, `reynolds_intertwines` (the equivariance lemma), `reynoldsMap` (a `Representation.IntertwiningMap ρ σ`), `convolution` and `delta`, in the namespace `OAI.Thorp.Fourier`. Equality in $G$ is decided classically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/Reynolds.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/Reynolds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_DegreeBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_FirstMoment

namespace OAI

universe uG uV uW uE uI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def reynolds (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (A : V →ₗ[ℂ] W) : V →ₗ[ℂ] W :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, σ g ∘ₗ A ∘ₗ ρ g⁻¹

lemma reynolds_intertwines (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (A : V →ₗ[ℂ] W)
    (h : G) (v : V) : reynolds ρ σ A (ρ h v) = σ h (reynolds ρ σ A v) := by
  simp only [reynolds, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    map_smul, map_sum]
  congr 1
  have he := Equiv.sum_comp (Equiv.mulLeft h) (fun g : G => σ g (A (ρ g⁻¹ (ρ h v))))
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  change σ (h * g) (A (ρ (h * g)⁻¹ (ρ h v))) = σ h (σ g (A (ρ g⁻¹ v)))
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
  congr 2
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

def reynoldsMap (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (A : V →ₗ[ℂ] W) :
    Representation.IntertwiningMap ρ σ :=
  (reynolds ρ σ A).intertwiningMap_of_isIntertwiningMap ρ σ (reynolds_intertwines ρ σ A)

section Unitary
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

end Unitary
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

def convolution (f k : G → ℂ) (x : G) : ℂ := ∑ g, f g * k (g⁻¹ * x)

def delta : G → ℂ := fun g => if g = 1 then 1 else 0

end Thorp.Fourier

end

end OAI


