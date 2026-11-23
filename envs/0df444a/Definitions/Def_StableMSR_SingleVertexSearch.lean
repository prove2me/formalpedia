-- Prove2me | Definitions.Def_StableMSR_SingleVertexSearch
-- name    : StableMSR_SingleVertexSearch
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-22T23:56:41.875232+00:00
-- url     : https://prove2.me/theorems/eda41d57-cef3-4566-9d96-c2f6880325a2
-- title:
--   The single-vertex separator recurrence
-- statement:
--   The single-vertex separator recurrence, its independent child productions with labelled interior outputs, and the root grammar.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_WindowSeparatorCuts
import Definitions.Def_StableMSR_DecompositionSearch_Recurrence
open scoped Classical
set_option autoImplicit false
namespace StableMSR.Recovery.SingleSearch
open DecompositionSearch WindowCuts
variable {V X : Type} [Fintype V] [DecidableEq V]
/-- One new vertex is chosen at each nonempty interior. -/
noncomputable def one (G : SimpleGraph V) (w : ℕ) : ℕ → Finset V → Finset V → Prop
  | 0,_,_ => False
  | m+1,S,C => S.card≤ w ∧ ∃v∈C, ∀D∈children G (insert v S) C,
      (boundary G D).card≤ w ∧ one G w m (boundary G D) D
noncomputable def starts (G : SimpleGraph V) (w : ℕ) :=
  ∀C∈PartialDecompositions.components G ∅,one G w (Fintype.card V) ∅ C
variable [DecidableEq X]
def labels (C : Finset V) (f : V→X) := C.image (fun v=>(v,f v))
/-- A production tests one fresh vertex label. Children see the parent's labeling on their own exterior boundaries. The output records only labels of interior vertices. -/
noncomputable def run (G : SimpleGraph V) (D : V→Finset X) (test : V→V→X→X→Prop) (w : ℕ) :
    ℕ → Finset V → Finset V → (V→X) → Finset (V×X) → Prop
  | 0,_,_,_,_ => False
  | m+1,S,C,a,O => S.card≤ w ∧ ∃v∈C,∃x : X,
      let B:=insert v S
      let b:=Function.update a v x
      let K:=children G B C
      okay G D test B b ∧ ∃out : Finset V→Finset (V×X),
        (∀E∈K,(boundary G E).card≤ w ∧ run G D test w m (boundary G E) E b (out E)) ∧
        O=insert (v,x) (K.biUnion out)
noncomputable def root (G : SimpleGraph V) (D : V→Finset X) (test : V→V→X→X→Prop)
    (w : ℕ) (a : V→X) (O : Finset (V×X)) :=
  let K:=PartialDecompositions.components G ∅
  ∃out : Finset V→Finset (V×X),(∀C∈K,run G D test w (Fintype.card V) ∅ C a (out C)) ∧ O=K.biUnion out
end StableMSR.Recovery.SingleSearch


