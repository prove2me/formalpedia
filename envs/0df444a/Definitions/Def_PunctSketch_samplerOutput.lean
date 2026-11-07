-- Prove2me | Definitions.Def_PunctSketch_samplerOutput
-- name    : PunctSketch_samplerOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:46:24.839657+00:00
-- url     : https://prove2.me/theorems/13916fee-d6e3-4bdb-8a3c-6b620db37d17
-- title:
--   The boundary sampler of Lemma 5.1
-- statement:
--   For $F$, $C$ and one round's coins: go through the levels $l$ from $\lceil 2\log n\rceil$ down to $0$. At level $l$, decode a purported boundary from the sparse-recovery sketches of the subsampled graph, and keep the pairs that cross $C$. Compute its fingerprint from $\boldsymbol r$. If the kept set is nonempty and the fingerprint equals $\sum_{v\in C}\tilde{\boldsymbol f}_{F,r,l}(v)$ in all $c+k-|F|$ coordinates, return an element of it. If no level accepts, return $\bot$.
--
--   **Formalization Note** The fingerprint on p.16 reads only crossing pairs, so a junk return of the decoder has to be cut down to those pairs before an edge is returned.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), proof of Lemma 5.1, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_PunctSketch_alpha
import Definitions.Def_PunctSketch_puncture
import Definitions.Def_PunctSketch_fingerprint
import Definitions.Def_PunctSketch_boundaryFp
import Definitions.Def_PunctSketch_IsPuncturableRetrieval
import Definitions.Def_PunctSketch_subsampled
import Definitions.Def_PunctSketch_RoundCoins

namespace PunctSketch

open Classical in
/-- **One level of the sampler.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), proof of Lemma 5.1, p.16. At level `l`: decode a purported
boundary from the sparse-recovery sketches of the level's subgraph, keep the pairs that cross `C`,
compute their fingerprint from `𝒓`, and accept when it equals `Σ_{v∈C} 𝒇̃_{F,r,l}(v)` in all of the
`c + k − |F|` coordinates and the boundary is nonempty. An accepted level returns an edge of it.

**Formalization Note.** The fingerprint on p.16 only reads pairs that cross `C`, so a junk return from
the decoder must be cut down to those pairs before an edge is returned. -/
noncomputable def levelOutput {n D Q : ℕ} (Ψ : Matrix (Fin D) (Fin n) (ZMod Q))
    (dec : Finset (Fin n) → Finset (Fin n) → (Fin n → Fin D → ZMod Q) → Finset (Sym2 (Fin n)))
    (pick : Finset (Sym2 (Fin n)) → Sym2 (Fin n)) (c k : ℕ) (G : SimpleGraph (Fin n))
    (F C : Finset (Fin n)) (ω : RoundCoins n Q (levelTop n)) (l : Fin (levelTop n + 1)) :
    Option (Sym2 (Fin n)) :=
  let Gl := subsampled G (ω.1 l)
  let r : Sym2 (Fin n) → ZMod Q := fun e => ((ω.2 l e : (ZMod Q)ˣ) : ZMod Q)
  let b := (dec F C (matrixSketch Ψ Gl)).filter (fun e => e ∈ crossingPairs F C)
  if b.Nonempty ∧ ∀ t, t + F.card < c + k →
      ∑ v ∈ C, puncture (alpha Q) F (fingerprint Gl (alpha Q) r v) v t =
        boundaryFp (alpha Q) F C r (b : Set (Sym2 (Fin n))) t
  then some (pick b) else none

/-- **The boundary sampler of Lemma 5.1.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), proof of Lemma 5.1, p.16: "Go through all
subsampling levels l from ⌈2 log n⌉ to 0"; the output is that of the first level that accepts, `⊥`
if there is none. `c` is the collision parameter of the fingerprint. -/
noncomputable def samplerOutput {n D Q : ℕ} (Ψ : Matrix (Fin D) (Fin n) (ZMod Q))
    (dec : Finset (Fin n) → Finset (Fin n) → (Fin n → Fin D → ZMod Q) → Finset (Sym2 (Fin n)))
    (pick : Finset (Sym2 (Fin n)) → Sym2 (Fin n)) (c k : ℕ) (G : SimpleGraph (Fin n))
    (F C : Finset (Fin n)) (ω : RoundCoins n Q (levelTop n)) : Option (Sym2 (Fin n)) :=
  (List.finRange (levelTop n + 1)).reverse.findSome? (levelOutput Ψ dec pick c k G F C ω)

end PunctSketch


