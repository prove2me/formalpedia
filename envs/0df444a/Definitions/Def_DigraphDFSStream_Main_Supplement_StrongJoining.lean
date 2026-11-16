-- Prove2me | Definitions.Def_DigraphDFSStream_Main_Supplement_StrongJoining
-- name    : DigraphDFSStream_Main_Supplement_StrongJoining
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:55:32.495207+00:00
-- url     : https://prove2.me/theorems/7ff46af7-1ba9-45fc-9ddf-19d48a0ccace
-- title:
--   Definition 4.2 — strong maximal joining
-- statement:
--   Let $H$ be a finite directed graph, $\mathcal P$ a family of vertex-disjoint nonempty simple directed paths, and $T$ a set of designated sinks disjoint from their vertices. A strong maximal joining is a family $\mathcal Q$ of vertex-disjoint simple directed paths with the following properties.
--
--   Each output starts with a nonempty prefix of one input path, continues only through vertices outside all input paths, and ends at a sink. An injective assignment from output paths to input paths enforces that each input path supplies at most one prefix. Output vertex disjointness enforces that no sink is used twice. Finally,
--   $$\nexists\ x\leadsto t\text{ in }H-V(\mathcal Q),\quad x\in V(\mathcal P)\setminus V(\mathcal Q),\ t\in T\setminus V(\mathcal Q).$$
--   This last condition includes discarded suffixes of matched input paths as well as entirely unmatched input paths. Abandoned vertices are not removed from the residual graph. Empty input and output families are allowed. Sinks are designated terminal vertices; outgoing edges are not assumed absent.
--
--   The output buffer encodes the entire ordered list of output paths. This is the common joining interface used by the separator reduction.
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), Definition 4.2, printed p.12 (PDF p.13)

import Definitions.Def_DigraphDFSStream_Main_GraphSemantics
import Definitions.Def_DigraphDFSStream_Main_Supplement_ParameterizedStreaming

set_option autoImplicit false

namespace DigraphDFSStream.Main.Supplement

def JoiningInput {m : ℕ} (E : Finset (Fin m × Fin m))
    (paths : List (List (Fin m))) (sinks : List (Fin m)) : Prop :=
  (∀ P ∈ paths, SimplePath E Finset.univ P) ∧
    (paths.map List.toFinset).Pairwise Disjoint ∧ sinks.Nodup ∧
    Disjoint paths.flatten.toFinset sinks.toFinset

/-- Definition 4.2. The injective assignment records which original input path supplies each
nonempty prefix. All residual reachability is in the original graph minus output vertices;
discarded suffixes remain in that graph. Sinks are designated terminals, not a loop-free axiom. -/
def StrongJoining {m : ℕ} (E : Finset (Fin m × Fin m))
    (paths : List (List (Fin m))) (sinks : List (Fin m))
    (outputs : List (List (Fin m))) : Prop :=
  (∀ Q ∈ outputs, SimplePath E Finset.univ Q) ∧
    (outputs.map List.toFinset).Pairwise Disjoint ∧
    (∃ source : Fin outputs.length → Fin paths.length,
      Function.Injective source ∧ ∀ i : Fin outputs.length,
        ∃ (t : ℕ) (tail : List (Fin m)) (z : Fin m),
          0 < t ∧ t ≤ (paths.get (source i)).length ∧ tail ≠ [] ∧
          outputs.get i = (paths.get (source i)).take t ++ tail ∧
          (∀ v ∈ tail, v ∉ paths.flatten) ∧
          (outputs.get i).getLast? = some z ∧ z ∈ sinks) ∧
    ∀ x ∈ paths.flatten.toFinset \ outputs.flatten.toFinset,
      ∀ z ∈ sinks.toFinset \ outputs.flatten.toFinset,
        ¬ Reach E (Finset.univ \ outputs.flatten.toFinset) x z

def JoiningOutput {m : ℕ} (E : Finset (Fin m × Fin m))
    (paths : List (List (Fin m))) (sinks : List (Fin m)) (out : List Bool) : Prop :=
  ∃ Q, out = familyCode Q ∧ StrongJoining E paths sinks Q

end DigraphDFSStream.Main.Supplement


