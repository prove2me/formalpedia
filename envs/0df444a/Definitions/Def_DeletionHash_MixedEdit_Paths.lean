-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_Paths
-- name    : DeletionHash_MixedEdit_Paths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:13.54572+00:00
-- url     : https://prove2.me/theorems/4a7989c8-5763-4805-baec-a93e5f4b054d
-- title:
--   Directed de Bruijn edges and the path spelled by a word
-- statement:
--   The de Bruijn graph has length-$(L-1)$ words as vertices and length-$L$ grams as labelled directed edges. A gram joins its length-$(L-1)$ prefix to its suffix. The path spelled by a word consists of its actual successive windows: its vertices are all length-$(L-1)$ windows and its edges are the consecutive length-$L$ windows with those prefix and suffix incidences. Being simple means these vertices are pairwise distinct. The predicate also identifies the edge support with the spectrum support. No arbitrary supplied walk replaces the word's actual windows. Path-vertex sets are used to define bubble intersections.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), §2.1, de Bruijn graph and word-spelled walk, printed p. 5 (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Spectrum
import Definitions.Def_DeletionHash_MixedEdit_UniqueWords

namespace DeletionHash.MixedEdit

universe u

def gramPrefix {α : Type u} {L : ℕ} (g : Gram α L) : Gram α (L-1) :=
  fun i => g ⟨i.val, by omega⟩

def gramSuffix {α : Type u} {L : ℕ} (g : Gram α L) : Gram α (L-1) :=
  fun i => g ⟨i.val + 1, by omega⟩

/-- The word's actual consecutive vertices and gram edges, with no arbitrary supplied walk. -/
def SpellsSimplePath {α : Type u} [DecidableEq α] (L : ℕ) (y : List α) : Prop :=
  (windows (L-1) y).Nodup ∧
  (∀ i ∈ starts L y, ∃ g : Gram α L,
    List.ofFn g = window L y i ∧
    List.ofFn (gramPrefix g) = window (L-1) y i ∧
    List.ofFn (gramSuffix g) = window (L-1) y (i+1)) ∧
  (∀ g : Gram α L, spectrum L y g ≠ 0 ↔ List.ofFn g ∈ windows L y)

def PathVertices {α : Type u} (L : ℕ) (y : List α) : Set (Gram α (L-1)) :=
  {v | List.ofFn v ∈ windows (L-1) y}

end DeletionHash.MixedEdit


