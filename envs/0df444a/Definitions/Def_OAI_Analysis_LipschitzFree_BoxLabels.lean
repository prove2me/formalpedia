-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
-- name    : OAI_Analysis_LipschitzFree_BoxLabels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:59:12.790593+00:00
-- url     : https://prove2.me/theorems/98702d2e-9f41-467a-a8c2-a769249d949f
-- title:
--   Finite boxes of labels $\{0,\dots,\mathrm{cap}\}^C$ with the supremum metric
-- statement:
--   Let $C$ be a finite set (of colours) and $\mathrm{cap}\in\mathbb{N}$. A *box label* is a function $a:C\to\{0,1,\dots,\mathrm{cap}\}$, so the box labels form the finite box $\{0,\dots,\mathrm{cap}\}^C$. Their distance is the supremum (Chebyshev) distance
--   $$\rho(a,b)=\max_{i\in C}\,|a_i-b_i|\ \in\mathbb{N},$$
--   with $\rho(a,b)=0$ when $C$ is empty.
--
--   1. Each coordinate is controlled by the distance, $|a_i-b_i|\le\rho(a,b)$ for every $i\in C$, and $\rho(a,b)\le n$ holds iff $|a_i-b_i|\le n$ for all $i\in C$.
--   2. $\rho(a,a)=0$, $\rho(a,b)=\rho(b,a)$, $\rho(a,c)\le\rho(a,b)+\rho(b,c)$, and $\rho(a,b)=0$ implies $a=b$.
--   3. Consequently the box $\{0,\dots,\mathrm{cap}\}^C$ is a finite metric space with metric $\rho$, and this is the metric placed on box labels.
--
--   In the construction, every vertex of a coloured port graph receives as box label the vector of its capped distances to the colour classes; the supremum metric on labels defines the distances between label anchors and measures how far apart the labels of two points are.
--
--   **Formalization Note** `BoxLabel C cap` is the function type `C → Fin (cap+1)`, with a `Fintype` instance. `BoxLabel.distance` is `Finset.univ.sup` of the coordinatewise `Nat.dist`, so the empty supremum is $0$; the `MetricSpace` instance has `dist a b = (distance a b : ℝ)` (`dist_eq`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/BoxLabels.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/BoxLabels.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters

namespace OAI

/-!
# Finite box labels with the supremum metric
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical

def BoxLabel (C : Type*) (cap : ℕ) := C → Fin (cap+1)

instance (C : Type*) [Fintype C] (cap : ℕ) : Fintype (BoxLabel C cap) :=
  inferInstanceAs (Fintype (C → Fin (cap+1)))

namespace BoxLabel
variable {C : Type*} [Fintype C] {cap : ℕ}

def distance (a b : BoxLabel C cap) : ℕ := Finset.univ.sup (fun i => Nat.dist (a i).val (b i).val)

theorem coord_le (a b : BoxLabel C cap) (i : C) :
    Nat.dist (a i).val (b i).val ≤ distance a b := Finset.le_sup (f := fun i => Nat.dist (a i).val (b i).val) (Finset.mem_univ i)

theorem distance_le_iff {a b : BoxLabel C cap} {n : ℕ} :
    distance a b ≤ n ↔ ∀ i, Nat.dist (a i).val (b i).val ≤ n := by
  simp [distance, Finset.sup_le_iff]

@[simp] theorem distance_self (a : BoxLabel C cap) : distance a a = 0 := by
  simp [distance]

theorem distance_comm (a b : BoxLabel C cap) : distance a b = distance b a := by
  simp only [distance, Nat.dist_comm]

theorem distance_triangle (a b c : BoxLabel C cap) :
    distance a c ≤ distance a b + distance b c := by
  rw [distance_le_iff]
  intro i
  exact (Nat.dist.triangle_inequality _ _ _).trans (Nat.add_le_add (coord_le a b i) (coord_le b c i))

theorem eq_of_distance_zero {a b : BoxLabel C cap} (h : distance a b = 0) : a = b := by
  funext i
  apply Fin.ext
  exact Nat.eq_of_dist_eq_zero (Nat.eq_zero_of_le_zero ((coord_le a b i).trans_eq h))

instance : MetricSpace (BoxLabel C cap) where
  dist a b := distance a b
  dist_self a := by simp
  dist_comm a b := by rw [distance_comm]
  dist_triangle a b c := by exact_mod_cast distance_triangle a b c
  eq_of_dist_eq_zero h := eq_of_distance_zero (by exact_mod_cast h)

@[simp] theorem dist_eq (a b : BoxLabel C cap) : dist a b = (distance a b : ℝ) := rfl

end BoxLabel
end DiscreteFree
end

end

end OAI


