-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_RetainedWedge
-- name    : OAI_Analysis_LipschitzFree_RetainedWedge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:43:26.890316+00:00
-- url     : https://prove2.me/theorems/17eb7646-abb4-4b38-8903-9f14f2d9c859
-- title:
--   Finite sub-wedges of a metric wedge and the $1$-Lipschitz collapse onto them
-- statement:
--   Let $(M_n,o_n)_{n\in\mathbb{N}}$ be a sequence of pointed metric spaces with metrics $d_n$. Their wedge $W=\bigvee_{n}(M_n,o_n)$ glues all base points into one point $*$: its points are $*$ together with the points of $M_n\setminus\{o_n\}$ for every $n$, and two points of the same component keep their distance while points of different components are joined through $*$. Explicitly $d(x,y)=d_n(x,y)$ for $x,y$ in the same component $M_n$, $d(x,y)=d_n(x,o_n)+d_m(y,o_m)$ for $x\in M_n$, $y\in M_m$ with $n\neq m$, and $d(x,*)=d_n(x,o_n)$. For a finite set $F\subseteq\mathbb{N}$, $\rho_F\colon W\to W$ is the $1$-Lipschitz map that fixes $*$ and the points of the components $M_n$ with $n\in F$ and sends all other points to $*$.
--
--   1. **Idempotence.** $\rho_F\circ\rho_F=\rho_F$.
--   2. **Finite sub-wedge.** $W_F=\{x\in W:\rho_F(x)=x\}$, the point $*$ together with the non-base points of the components $M_n$, $n\in F$, with the metric restricted from $W$ and base point $*_F=*$.
--   3. **Collapse.** $\pi_F\colon W\to W_F$, $\pi_F(x)=\rho_F(x)$; it is $1$-Lipschitz and $\pi_F(*)=*_F$.
--   4. **Embedding.** $j_F\colon W_F\to W$, the inclusion; it is an isometry with $j_F(*_F)=*$, and
--   $$
--   j_F\circ\pi_F=\rho_F .
--   $$
--
--   Thus $\rho_F$ factors through the wedge $W_F$ of the finitely many components indexed by $F$. When the components are uniformly separated and bounded, $W_F$ is again uniformly separated and bounded, so its free space has the bounded approximation property; transporting approximating operators through $\pi_F$ and $j_F$ is how the approximation property of the free space of the whole wedge is obtained.
--
--   **Formalization Note** The objects are `retain_idempotent`, `Retained M o F` (a subtype of `Point M o` with the induced metric), `retainedBase`, `collapse` and `embed`, together with `collapse_base`, `embed_base`, `embed_collapse`, `embed_isometry` and `collapse_lipschitz`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/RetainedWedge.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/RetainedWedge.lean by skeleton subtraction
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


