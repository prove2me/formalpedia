-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_RetainedWedge__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_RetainedWedge__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:38:19.38904+00:00
-- url     : https://prove2.me/theorems/be8137bd-0478-4e4c-a3b8-a7e9020ea582
-- title:
--   Finite sub-wedges of a metric wedge and the $1$-Lipschitz collapse onto them
-- statement:
--   Let $(M_n,o_n)_{n\in\mathbb{N}}$ be a sequence of pointed metric spaces with metrics $d_n$, and let $W=\bigvee_n(M_n,o_n)$ be their wedge: the point set $\{\ast \}\sqcup\bigsqcup_n(M_n\setminus\{o_n\})$, in which all base points are identified with $\ast$, with the metric $d(x,y)=d_n(x,y)$ for $x,y$ in the same component $M_n$, $d(x,y)=d_n(x,o_n)+d_m(y,o_m)$ for $x\in M_n$ and $y\in M_m$ with $n\neq m$, and $d(x,\ast)=d_n(x,o_n)$. For a finite set $F\subseteq\mathbb{N}$, $\rho_F\colon W\to W$ is the $1$-Lipschitz map that fixes $\ast$ and the points of the components $M_n$ with $n\in F$ and sends every other point to $\ast$.
--
--   1. **Idempotence.** $\rho_F\circ\rho_F=\rho_F$.
--   2. **Finite sub-wedge.** $W_F=\{x\in W:\rho_F(x)=x\}$, consisting of $\ast$ and the non-base points of the components $M_n$ with $n\in F$, with the metric restricted from $W$ and base point $\ast_F=\ast$.
--   3. **Collapse.** $\pi_F\colon W\to W_F$, $\pi_F(x)=\rho_F(x)$. It is $1$-Lipschitz and $\pi_F(\ast)=\ast_F$.
--   4. **Embedding.** $j_F\colon W_F\to W$, the inclusion map. It is an isometry, $j_F(\ast_F)=\ast$, and
--   $$
--   j_F\circ\pi_F=\rho_F .
--   $$
--
--   Thus $\rho_F$ factors through the wedge $W_F$ of the finitely many components indexed by $F$, by a $1$-Lipschitz collapse followed by an isometric embedding, both preserving base points. After linearization this factors the finite-retention operator on the free space of $W$ through the free space of a finite sub-wedge, which is how approximation properties of finite sub-wedges are transported to the whole wedge.
--
--   **Formalization Note** The objects are the simp lemma `retain_idempotent`, the subtype `Retained M o F` of `Point M o` with the induced metric, `retainedBase`, `collapse` and `embed`, together with `collapse_base`, `embed_base`, `embed_collapse`, `embed_isometry` and `collapse_lipschitz`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/RetainedWedge.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/RetainedWedge.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Separated metric wedges and bounded finite-component retracts
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricWedge
open scoped Classical BigOperators
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem retain_idempotent (F : Finset ℕ) (x : Point M o) :
    retain M o F (retain M o F x) = retain M o F x := by
  rcases x with _ | ⟨n,x⟩
  · rfl
  · by_cases hn : n ∈ F <;> simp [retain,hn] <;> rfl

def Retained (F : Finset ℕ) := {x : Point M o // retain M o F x = x}

instance (F : Finset ℕ) : MetricSpace (Retained M o F) :=
  inferInstanceAs (MetricSpace {x : Point M o // retain M o F x = x})

def retainedBase (F : Finset ℕ) : Retained M o F := ⟨base M o,rfl⟩

def collapse (F : Finset ℕ) (x : Point M o) : Retained M o F :=
  ⟨retain M o F x,retain_idempotent M o F x⟩

def embed (F : Finset ℕ) (x : Retained M o F) : Point M o := x.val

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem collapse_base (F : Finset ℕ) :
    collapse M o F (base M o) = retainedBase M o F := rfl

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem embed_base (F : Finset ℕ) :
    embed M o F (retainedBase M o F) = base M o := rfl

omit [∀ n, MetricSpace (M n)] in
@[simp] theorem embed_collapse (F : Finset ℕ) (x : Point M o) :
    embed M o F (collapse M o F x) = retain M o F x := rfl

theorem embed_isometry (F : Finset ℕ) : Isometry (embed M o F) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rfl

theorem collapse_lipschitz (F : Finset ℕ) : LipschitzWith 1 (collapse M o F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (retain_lipschitz M o F).dist_le_mul x y

end DiscreteFree.MetricWedge
end

end

end OAI


