-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_WedgeApproximation__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_WedgeApproximation__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:40:33.516431+00:00
-- url     : https://prove2.me/theorems/9dcf88ea-424c-405a-bdf5-35bb5ec4e329
-- title:
--   Linearized wedge inclusions, retractions and finite-wedge collapses on Lipschitz-free spaces
-- statement:
--   For a pointed metric space $(M,o)$, $\mathrm{Lip}_0(M,o)$ is the real normed space of Lipschitz functions $g\colon M\to\mathbb{R}$ with $g(o)=0$, normed by the best Lipschitz constant; $\delta_x(g)=g(x)$ is the evaluation at $x\in M$; and the Lipschitz-free space $\mathcal{F}(M,o)$ is the closed linear span of $\{\delta_x:x\in M\}$ in the dual space $\mathrm{Lip}_0(M,o)^\ast$. A $1$-Lipschitz map $f\colon M\to N$ with $f(o)=b$ has a linearization $\widehat f\colon\mathcal{F}(M,o)\to\mathcal{F}(N,b)$, the bounded linear operator of norm at most $1$ given by $\widehat f(u)(g)=u(g\circ f)$, so that $\widehat f(\delta_x)=\delta_{f(x)}$.
--
--   Let $W=\bigvee_n(M_n,o_n)$ be the wedge of a sequence of pointed metric spaces, in which all base points are identified with one point $\ast$ and distances between different components are measured through $\ast$. It comes with isometric inclusions $\iota_n\colon M_n\to W$, $1$-Lipschitz retractions $r_n\colon W\to M_n$ (identity on $M_n$, every other point to $o_n$), and, for each finite $F\subseteq\mathbb{N}$, the $1$-Lipschitz map $\rho_F\colon W\to W$ that keeps the components indexed by $F$ and sends the rest to $\ast$. The map $\rho_F$ factors as $\rho_F=j_F\circ\pi_F$ through the finite sub-wedge $W_F=\{x:\rho_F(x)=x\}$, with the collapse $\pi_F\colon W\to W_F$ and the isometric embedding $j_F\colon W_F\to W$. All these maps preserve base points.
--
--   1. **Component inclusions.** $J_n=\widehat{\iota_n}\colon\mathcal{F}(M_n,o_n)\to\mathcal{F}(W,\ast)$.
--   2. **Component retractions.** $P_n=\widehat{r_n}\colon\mathcal{F}(W,\ast)\to\mathcal{F}(M_n,o_n)$, with
--   $$
--   P_n\circ J_n=\mathrm{id}_{\mathcal{F}(M_n,o_n)} .
--   $$
--   3. **Finite retentions.** $\widehat{\rho_F}\colon\mathcal{F}(W,\ast)\to\mathcal{F}(W,\ast)$.
--   4. **Collapse and embedding.** $\widehat{\pi_F}\colon\mathcal{F}(W,\ast)\to\mathcal{F}(W_F,\ast)$ and $\widehat{j_F}\colon\mathcal{F}(W_F,\ast)\to\mathcal{F}(W,\ast)$, with $\widehat{j_F}\circ\widehat{\pi_F}=\widehat{\rho_F}$.
--
--   All of these operators have norm at most $1$. Item 2 makes each $\mathcal{F}(M_n,o_n)$ a norm-one complemented subspace of $\mathcal{F}(W,\ast)$, so a bounded approximation property of $\mathcal{F}(W,\ast)$ with constant $\Lambda$ passes to every component; item 4 factors the finite-retention operators through the free spaces of finite sub-wedges. These are the operator-level tools for transferring approximation properties between the free space of a wedge, its components and its finite sub-wedges.
--
--   **Formalization Note** The operators are `inclusionL M o n`, `retractionL M o n`, `retainL M o F`, `collapseL M o F` and `embedL M o F`, each defined as `freeMap` of the corresponding map of the wedge; the two identities are the simp lemmas `retractionL_inclusionL` and `embedL_collapseL`. The section `OperatorTools` contains no definitions in this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/WedgeApproximation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/WedgeApproximation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Words__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Functor__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Wedge__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_RetainedWedge__RealL1Renorming

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


