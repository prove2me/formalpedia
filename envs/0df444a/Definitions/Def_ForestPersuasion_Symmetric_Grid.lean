-- Prove2me | Definitions.Def_ForestPersuasion_Symmetric_Grid
-- name    : ForestPersuasion_Symmetric_Grid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:21:34.479977+00:00
-- url     : https://prove2.me/theorems/81960978-92f2-4d8e-9027-0e029799ceea
-- title:
--   Threshold grid and descendant adoption counts
-- statement:
--   The finite set $\Theta$ contains $0$, $1$, and every receiver threshold $t_i$. Its increasing enumeration is $0=\tau_0<\cdots<\tau_m=1$. A grid vector assigns a member of $\Theta$ to every receiver; $S(\bar l)$ contains precisely those $i$ whose assigned value is at least $t_i$.
--
--   The count $k_i(\bar l)$ is the number of adopters in $D_i\setminus\{i\}$. A subtree vector has only the coordinates in $D_i$. A scheme is grid-supported when all receiver posteriors lie in $\Theta$ at every joint message having positive probability in either state.
--
--   The code indexes vectors directly by distinct grid values instead of their positions in the sorted list, avoiding duplicate-threshold indices without changing the grid.
-- source:
--   Konstantin Zabarnyi, Designing Information in a Forest: Algorithmic Aspects, STOC 2027 submission #271 (October 2026; PDF dated November 2, 2026), Notation 3; §5 definition of k_i, PDF pp. 8, 12 (printed pp. 7, 11). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/271.pdf

import Mathlib
import Definitions.Def_ForestPersuasion_Symmetric_Model

noncomputable section
open scoped NNReal ENNReal
open Classical

namespace ForestPersuasion.Symmetric

/-- The distinct thresholds together with 0 and 1. No ordering of receivers is assumed. -/
def theta {n : ℕ} (I : Model n) : Finset ℝ :=
  insert 0 (insert 1 (Finset.univ.image (threshold I)))

abbrev Grid {n : ℕ} (I : Model n) := {q : ℝ // q ∈ theta I}

/-- Increasing grid enumeration τ, provided for comparison to the paper's notation. -/
def tau {n : ℕ} (I : Model n) : Fin (theta I).card → ℝ :=
  fun l => ((theta I).sort (· ≤ ·))[l.val]'(by simp only [Finset.length_sort]; exact l.isLt)

/-- L, with each index replaced by its corresponding distinct grid value. -/
abbrev GridVector {n : ℕ} (I : Model n) := Fin n → Grid I

abbrev SubtreeVector {n : ℕ} (I : Model n) (i : Fin n) :=
  {j // j ∈ I.hierarchy.descendants i} → Grid I

instance gridFintype {n : ℕ} (I : Model n) : Fintype (Grid I) := Fintype.ofFinite _
instance gridDecidableEq {n : ℕ} (I : Model n) : DecidableEq (Grid I) := Classical.decEq _

/-- p(l̄). -/
def gridPosterior {n : ℕ} (I : Model n) (l : GridVector I) : Fin n → ℝ :=
  fun i => (l i).val

/-- S(l̄), with the weak inequality required by the sender-favourable tie rule. -/
def gridAdopters {n : ℕ} (I : Model n) (l : GridVector I) : Finset (Fin n) :=
  Finset.univ.filter (fun i => threshold I i ≤ (l i).val)

def k {n : ℕ} (I : Model n) (l : GridVector I) (i : Fin n) : ℕ :=
  ((I.hierarchy.descendants i).erase i |>.filter
    (fun j => threshold I j ≤ (l j).val)).card

/-- Almost surely on both conditional state distributions, all posteriors are grid valued. -/
def GridSupported {n : ℕ} (I : Model n) {M : Type} (σ : Scheme n M) : Prop :=
  ∀ (w : Bool) (s : Fin n → M), σ w s ≠ 0 → ∀ i, posterior I σ i s ∈ theta I

end ForestPersuasion.Symmetric


