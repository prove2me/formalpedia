-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Transitive
-- name    : OAI_Combinatorics_EuclideanRamsey_Transitive
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T04:35:07.618617+00:00
-- url     : https://prove2.me/theorems/3cb5dc90-46b6-4e84-b112-27b77e8af4c2
-- title:
--   Distance-preserving permutations and transitivity of a finite Euclidean configuration
-- statement:
--   Let $t,D\in\mathbb{N}$ and let $y=(y_0,y_1,\dots,y_{t-1})$ be a family of $t$ points of the Euclidean space $\mathbb{R}^D$, with Euclidean distance $\|\cdot\|$ (the points need not be distinct). Write $\mathrm{Sym}(t)$ for the group of permutations of the index set $\{0,1,\dots,t-1\}$.
--
--   1. **Distance-preserving permutation group.** The set
--   $$\mathrm{Aut}(y)=\bigl\{\,\sigma\in\mathrm{Sym}(t):\ \|y_{\sigma(i)}-y_{\sigma(j)}\|=\|y_i-y_j\|\ \text{ for all } i,j\in\{0,\dots,t-1\}\,\bigr\}$$
--   contains the identity and is closed under composition and inverses, so it is a subgroup of $\mathrm{Sym}(t)$; being a subgroup of a finite group, it is finite.
--   2. **Transitive configurations.** The family $y$ is *transitive* if $\mathrm{Aut}(y)$ acts transitively on the indices: for all $i,j\in\{0,\dots,t-1\}$ there is $\sigma\in\mathrm{Aut}(y)$ with $\sigma(i)=j$.
--
--   A permutation in $\mathrm{Aut}(y)$ is the combinatorial shadow of a symmetry of the configuration: it rearranges the points while preserving all mutual distances. For example, the vertices of a regular polygon, listed in any order, form a transitive family. Transitivity is the hypothesis of the theorem that every nonempty configuration of distinct points, all of which are points of a transitive configuration of distinct points, is Ramsey; its proof averages over the finite group $\mathrm{Aut}(y)$, using that for transitive $y$ every orbit sum $\sum_{\sigma\in\mathrm{Aut}(y)}f(y_{\sigma(i)})$ is independent of $i$.
--
--   **Formalization Note** The configuration is a map `y : Fin t → Space D` with `Space D = EuclideanSpace ℝ (Fin D)`, and distances are written with `dist`. `distancePermutationGroup y : Subgroup (Equiv.Perm (Fin t))` is item 1, `distancePermutationFintype y` is the `Fintype` instance obtained from `Fintype.ofFinite`, and `IsTransitive y` quantifies over elements `σ` of this subgroup, requiring `σ.val i = j`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Transitive.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Transitive.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyTransitive mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyTransitive

namespace OAI

/-! Finite transitive Euclidean configurations and their subsets are Ramsey. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace EuclideanRamsey
namespace TransitiveConsequence

def distancePermutationGroup {t D : ℕ} (y : Fin t → Space D) :
    Subgroup (Equiv.Perm (Fin t)) where
  carrier := {σ | ∀ i j, dist (y (σ i)) (y (σ j)) = dist (y i) (y j)}
  one_mem' := by intro i j; rfl
  mul_mem' := by
    intro σ τ hσ hτ i j
    change dist (y (σ (τ i))) (y (σ (τ j))) = dist (y i) (y j)
    rw [hσ, hτ]
  inv_mem' := by
    intro σ hσ i j
    have h := hσ (σ.symm i) (σ.symm j)
    simpa using h.symm

noncomputable instance distancePermutationFintype {t D : ℕ} (y : Fin t → Space D) :
    Fintype (distancePermutationGroup y) := Fintype.ofFinite _

def IsTransitive {t D : ℕ} (y : Fin t → Space D) : Prop :=
  ∀ i j : Fin t, ∃ σ : distancePermutationGroup y, σ.val i = j

end TransitiveConsequence
end EuclideanRamsey

end

end OAI


