-- Prove2me | Definitions.Def_OnlineTransportation1195_Main_RedPatches
-- name    : OnlineTransportation1195_Main_RedPatches
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:35:21.22143+00:00
-- url     : https://prove2.me/theorems/68fa0f33-d409-4bdd-b02c-d6e445c09715
-- title:
--   DFS red edges, root patches and the budget function
-- statement:
--   Fix a root-based DFS $L$ before selecting a time budget. For edge $e$, let $x_e$ be its downward prefix cost through the first traversal. At time $t$, an edge is red exactly when $x_e+t>d_e$. The root patch is the set of red edges connected to the root by red edges, equivalently those whose root-path edges are all red. An empty edge set is permitted.
--
--   Write $R(t)$ for total red weight, $R^{\rm in}(t)$ for root-patch weight, and $R^{\rm out}(t)$ for weight of red edges outside that patch. Define
--
--   $$F(s)=\sum_{e\in E} w_e\min\{1,s/d_e\}.$$
--
--   The budget predicate records $t>0$, $0\le s\le t$, an empty root patch or its normalization by $\min\{d_e,s\}$, the detour inequality, and a proper root patch. These quantities are computed from the tree, deadlines and fixed DFS; none is an independent supplied function. The auxiliary $x_e$ returns zero for an unvisited edge outside its intended domain; every result using it assumes a valid DFS.
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), Definition 3.2 and root patch/F definitions, PDF / printed p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Definitions.Def_OnlineTransportation1195_Main_TreeWalk

open scoped BigOperators
open Classical

namespace OnlineTransportation1195.Main
namespace Tree

variable {n : ℕ} (T : Tree n)

/-- Definition 3.2: first downward prefix cost of the fixed DFS. Outside the
DFS domain an unvisited edge has value zero; every theorem requires DFS. -/
noncomputable def x (L : List (Fin n)) (e : Fin n) : ℝ := by
  classical
  exact match (List.range L.length).find? (fun i => decide (T.DownAt L e i)) with
    | some i => T.downPrefix L i
    | none => 0

noncomputable def red (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) : Finset (Fin n) :=
  T.edges.filter (fun e => d e < T.x L e + t)

/-- An edge is in the root patch iff every edge on its root path is red. -/
noncomputable def rootPatch (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) : Finset (Fin n) :=
  (T.red d L t).filter (fun e => ∀ a ∈ T.edges, T.IsAnc a e → a ∈ T.red d L t)

noncomputable def R (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) : ℝ :=
  ∑ e ∈ T.red d L t, T.W e

noncomputable def Rin (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) : ℝ :=
  ∑ e ∈ T.rootPatch d L t, T.W e

noncomputable def Rout (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) : ℝ :=
  ∑ e ∈ T.red d L t \ T.rootPatch d L t, T.W e

noncomputable def F (d : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ e ∈ T.edges, T.W e * min 1 (s / d e)

noncomputable def patchNormalization (d : Fin n → ℝ) (L : List (Fin n)) (s t : ℝ) : ℝ :=
  ∑ e ∈ T.rootPatch d L t, T.W e / min (d e) s

/-- Full mathematical output specification of Lemma 3.3. Positivity of s in
the nonempty-patch branch follows from its normalization, not a new premise. -/
def Budget (d : Fin n → ℝ) (L : List (Fin n)) (s t : ℝ) : Prop :=
  0 < t ∧ 0 ≤ s ∧ s ≤ t ∧
    (T.rootPatch d L t = ∅ ∨ T.patchNormalization d L s t = 1) ∧
    s + T.Rout d L t ≤ t ∧ T.rootPatch d L t ≠ T.edges

end Tree
end OnlineTransportation1195.Main


