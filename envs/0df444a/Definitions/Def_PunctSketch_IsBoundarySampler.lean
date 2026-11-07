-- Prove2me | Definitions.Def_PunctSketch_IsBoundarySampler
-- name    : PunctSketch_IsBoundarySampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:00.197939+00:00
-- url     : https://prove2.me/theorems/caea4bd0-788f-42ee-99ce-31b55783ce98
-- title:
--   A boundary sampling oracle for $G\setminus F$ (Definition 2.1)
-- statement:
--   A randomized procedure $\mathrm{BS}$, with coins uniform on a finite space, is a boundary sampling oracle for $G\setminus F$ with failure probability $\delta$ and hallucination probability $\eta$ when, for each $C$ disjoint from $F$:
--
--   1. if $\partial_{-F}C\ne\emptyset$, then $\Pr[\mathrm{BS}(C)=\bot]\le\delta$;
--   2. in all cases, $\Pr[\mathrm{BS}(C)\ne\bot\wedge\mathrm{BS}(C)\notin\partial_{-F}C]\le\eta$.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Definition 2.1, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_PunctSketch_puncturedBoundary
import Definitions.Def_PunctSketch_coinProb

namespace PunctSketch

/-- **A boundary sampling oracle for `G ∖ F` (Definition 2.1).** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), Definition 2.1, p.6:
"If ∂C ≠ ∅, then Pr[BS(C) = ⊥] ≤ δ. In all cases, Pr[BS(C) ≠ ⊥ ∧ BS(C) ∉ ∂C] ≤ η."

Queries are the sets `C` disjoint from `F`; the boundary is taken in `G ∖ F`; `none` is the failure
symbol `⊥`; the randomness is uniform on the finite space `Ω`. -/
def IsBoundarySampler {V Ω : Type*} [Fintype Ω] (G : SimpleGraph V) (F : Finset V) (δ η : ℝ)
    (BS : Finset V → Ω → Option (Sym2 V)) : Prop :=
  ∀ C : Finset V, Disjoint C F →
    (puncturedBoundary G F C ≠ ∅ → coinProb (fun ω => BS C ω = none) ≤ δ) ∧
      coinProb (fun ω => ∃ e, BS C ω = some e ∧ e ∉ puncturedBoundary G F C) ≤ η

end PunctSketch


