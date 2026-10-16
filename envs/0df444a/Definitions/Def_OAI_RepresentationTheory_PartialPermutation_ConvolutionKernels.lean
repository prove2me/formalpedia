-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
-- name    : OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:03:24.790187+00:00
-- url     : https://prove2.me/theorems/dd22ebb3-6232-4548-8d26-750570ea3c5e
-- title:
--   Right-coset mass caps and convolution of a function with a subgroup kernel
-- statement:
--   Let $G$ be a finite group, $H\le G$ a subgroup of index $[G:H]$, $f\colon G\to\mathbb{R}$ a real-valued function and $B\in\mathbb{R}$.
--
--   1. **Right-coset cap.** The function $f$ satisfies the right-coset cap for $H$ with bound $B$ if $\sum_{h\in H}f(hg)\le B/[G:H]$ for every $g\in G$, that is, if the total $f$-weight of every right coset $Hg$ is at most $B/[G:H]$. It is the right-handed counterpart of the left-coset cap $\sum_{h\in H}f(gh)\le B/[G:H]$ on left cosets $gH$.
--   2. **Convolution with a subgroup kernel.** For a function $k\colon H\to\mathbb{C}$, the convolution $k\star f\colon G\to\mathbb{C}$ of $k$ (extended by zero from $H$ to $G$) with $f$ is given by the second formula below.
--
--   In formulas,
--
--   $$
--   \sum_{h\in H}f(hg)\le\frac{B}{[G:H]}\quad\text{for all } g\in G,\qquad\qquad (k\star f)(g)=\sum_{h\in H}k(h)\,f(h^{-1}g)\quad(g\in G).
--   $$
--
--   For any representation $\rho$ of $G$, the Fourier transform of the convolution factorises as
--
--   $$
--   \sum_{g\in G}(k\star f)(g)\,\rho(g)=\Big(\sum_{h\in H}k(h)\,\rho(h)\Big)\Big(\sum_{g\in G}f(g)\,\rho(g)\Big),
--   $$
--
--   so $\ell^2$-bounds on $k\star f$, which the coset cap provides, control products of Fourier transforms of $f$ with Fourier transforms of kernels living on the subgroup $H$.
--
--   **Formalization Note** The cap is `RightCosetCap f H B`, where the index is the natural number `H.index` cast to $\mathbb{R}$ (it is at least $1$ since $G$ is finite) and the division is real division. The convolution is `leftKernel H k f`, in which the real values of $f$ are coerced to $\mathbb{C}$ and the sum runs over the elements of $H$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/ConvolutionKernels.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/ConvolutionKernels.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PartialPermutation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
namespace PartialPermutation
open scoped BigOperators ComplexConjugate

noncomputable section

def RightCosetCap {G : Type*} [Group G] [Fintype G]
    (f : G → ℝ) (H : Subgroup G) (B : ℝ) : Prop :=
  by classical exact ∀ g, ∑ h : H, f (h * g) ≤ B / H.index

section
variable {G : Type*} [Group G] [Fintype G]

def leftKernel (H : Subgroup G) (k : H → ℂ) (f : G → ℝ) (g : G) : ℂ :=
  by classical exact ∑ h : H, k h * (f ((h : G)⁻¹ * g) : ℂ)

end
end
end PartialPermutation

end

end OAI


