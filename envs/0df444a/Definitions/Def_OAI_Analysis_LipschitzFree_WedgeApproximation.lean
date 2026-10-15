-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_WedgeApproximation
-- name    : OAI_Analysis_LipschitzFree_WedgeApproximation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:45:25.283139+00:00
-- url     : https://prove2.me/theorems/80bb979d-a8cb-42d6-ba9d-c73412d157b5
-- title:
--   Linearized wedge inclusions, retractions and finite-wedge projections on Lipschitz-free spaces
-- statement:
--   For a pointed metric space $(M,o)$, $\mathrm{Lip}_0(M,o)$ denotes the real Banach space of Lipschitz functions $g\colon M\to\mathbb{R}$ with $g(o)=0$, normed by the best Lipschitz constant $\|g\|=\sup_{x\neq y}|g(x)-g(y)|/d(x,y)$; for $x\in M$ the evaluation $\delta_x(g)=g(x)$ is a bounded linear functional on it, and the Lipschitz-free space $\mathcal{F}(M,o)$ is the closed linear span of $\{\delta_x: x\in M\}$ in the dual space $\mathrm{Lip}_0(M,o)^*$. For a $1$-Lipschitz map $f\colon(M,o)\to(N,b)$ with $f(o)=b$, its linearization $\widehat f\colon\mathcal{F}(M,o)\to\mathcal{F}(N,b)$ is the bounded linear operator of norm at most $1$ determined by $\widehat f(\delta_x)=\delta_{f(x)}$.
--
--   Let $W=\bigvee_n(M_n,o_n)$ be the wedge of a sequence of pointed metric spaces (all base points glued into one point $*$, distances between different components measured through $*$), with isometric inclusions $\iota_n\colon M_n\to W$, $1$-Lipschitz retractions $r_n\colon W\to M_n$ (identity on $M_n$, everything else to $o_n$), and, for finite $F\subseteq\mathbb{N}$, the $1$-Lipschitz map $\rho_F\colon W\to W$ that keeps the components indexed by $F$ and sends the rest to $*$, which factors as $\rho_F=j_F\circ\pi_F$ through the finite sub-wedge $W_F=\rho_F(W)$ with the collapse $\pi_F\colon W\to W_F$ and the isometric embedding $j_F\colon W_F\to W$.
--
--   1. **Component inclusions.** $J_n=\widehat{\iota_n}\colon\mathcal{F}(M_n,o_n)\to\mathcal{F}(W,*)$.
--   2. **Component retractions.** $P_n=\widehat{r_n}\colon\mathcal{F}(W,*)\to\mathcal{F}(M_n,o_n)$, with
--   $$
--   P_n\circ J_n=\mathrm{id}_{\mathcal{F}(M_n,o_n)} .
--   $$
--   3. **Finite retentions.** $\widehat{\rho_F}\colon\mathcal{F}(W,*)\to\mathcal{F}(W,*)$.
--   4. **Collapse and embedding.** $\widehat{\pi_F}\colon\mathcal{F}(W,*)\to\mathcal{F}(W_F,*)$ and $\widehat{j_F}\colon\mathcal{F}(W_F,*)\to\mathcal{F}(W,*)$, with $\widehat{j_F}\circ\widehat{\pi_F}=\widehat{\rho_F}$.
--
--   All these operators have norm at most $1$. Item 2 makes each $\mathcal{F}(M_n,o_n)$ a norm-one complemented subspace of $\mathcal{F}(W,*)$, so a bounded approximation property of $\mathcal{F}(W,*)$ with constant $\Lambda$ passes to every component; item 4 lets the operators $\widehat{\rho_F}$, which converge to the identity uniformly on compact sets as $F$ grows, be factored through the free space of a finite sub-wedge. These are the two mechanisms behind a free space that has the approximation property but no bounded approximation property.
--
--   **Formalization Note** The operators are `inclusionL M o n`, `retractionL M o n`, `retainL M o F`, `collapseL M o F` and `embedL M o F`, each defined as `freeMap` of the corresponding map of the wedge; the identities are the simp lemmas `retractionL_inclusionL` and `embedL_collapseL`. The section `OperatorTools` contains no definitions in this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/WedgeApproximation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/WedgeApproximation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring
import Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction
import Definitions.Def_OAI_Analysis_LipschitzFree_Functor
import Definitions.Def_OAI_Analysis_LipschitzFree_Wedge
import Definitions.Def_OAI_Analysis_LipschitzFree_RetainedWedge

namespace OAI

/-!
# Compact-uniform approximation on wedges and contractive BAP inheritance
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical BigOperators

section OperatorTools
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

end OperatorTools

namespace MetricWedge
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

def inclusionL (n : ℕ) : FreeSpace (o n) →L[ℝ] FreeSpace (base M o) :=
  freeMap (o n) (base M o) (inclusion M o n) (inclusion_base M o n)
    (inclusion_isometry M o n).lipschitz

def retractionL (n : ℕ) : FreeSpace (base M o) →L[ℝ] FreeSpace (o n) :=
  freeMap (base M o) (o n) (retraction M o n) (retraction_base M o n)
    (retraction_lipschitz M o n)

@[simp] theorem retractionL_inclusionL (n : ℕ) :
    (retractionL M o n).comp (inclusionL M o n) = ContinuousLinearMap.id ℝ (FreeSpace (o n)) := by
  apply freeMap_ext (o n)
  intro x
  simp [inclusionL,retractionL]

def retainL (F : Finset ℕ) : FreeSpace (base M o) →L[ℝ] FreeSpace (base M o) :=
  freeMap (base M o) (base M o) (retain M o F) (retain_base M o F) (retain_lipschitz M o F)

def collapseL (F : Finset ℕ) : FreeSpace (base M o) →L[ℝ] FreeSpace (retainedBase M o F) :=
  freeMap _ _ (collapse M o F) (collapse_base M o F) (collapse_lipschitz M o F)

def embedL (F : Finset ℕ) : FreeSpace (retainedBase M o F) →L[ℝ] FreeSpace (base M o) :=
  freeMap _ _ (embed M o F) (embed_base M o F) (embed_isometry M o F).lipschitz

@[simp] theorem embedL_collapseL (F : Finset ℕ) :
    (embedL M o F).comp (collapseL M o F) = retainL M o F := by
  apply freeMap_ext (base M o)
  intro x
  rfl

end MetricWedge
end DiscreteFree
end

end

end OAI


