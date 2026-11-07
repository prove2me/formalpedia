-- Prove2me | Definitions.Def_PunctSketch_IsPuncturableRetrieval
-- name    : PunctSketch_IsPuncturableRetrieval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:45.27882+00:00
-- url     : https://prove2.me/theorems/1499f51d-1b69-48a3-ac31-322a0647dc5f
-- title:
--   A puncturable boundary-retrieval scheme
-- statement:
--   A sketching matrix $\Psi$ and a decoder form a puncturable retrieval scheme with parameter $k$ and capacity $s$ when, for every graph $G$ on the vertex set and every $F$ with $|F|<k$, the map sending $C$ to the decoder's answer on $F$, $C$ and the sketches $(\Psi\boldsymbol a^\pm_v)_v$ is a boundary retrieval oracle for $G\setminus F$ with capacity $s$.
--
--   The matrix and the decoder come before $G$: the decoder sees $G$ only through the sketches.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Theorem 4, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_PunctSketch_signedAdj
import Definitions.Def_PunctSketch_IsBoundaryRetrievalOracle

namespace PunctSketch

/-- The linear sketch `Ψ 𝒂±_v` of the signed adjacency vector of `v`. Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §2, p.5, proof of
Theorem 4, p.10. -/
noncomputable def matrixSketch {n D Q : ℕ} (Ψ : Matrix (Fin D) (Fin n) (ZMod Q))
    (G : SimpleGraph (Fin n)) (v : Fin n) : Fin D → ZMod Q :=
  fun t => ∑ u, Ψ t u * ((signedAdj G v u : ℤ) : ZMod Q)

/-- **A puncturable boundary-retrieval scheme.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), Theorem 4, p.10: "For every F ⊆ V with |F| < k,
the receiver of these sketches can implement a boundary retrieval oracle for G ⧵ F with capacity d."

The matrix `Ψ` and the decoder `dec` come before the graph: for every `G` and `|F| < k`, the map
`C ↦ dec F C (Ψ𝒂±_v)_v` is a boundary retrieval oracle for `G ∖ F` with capacity `cap`. -/
def IsPuncturableRetrieval {n D Q : ℕ} (k cap : ℕ) (Ψ : Matrix (Fin D) (Fin n) (ZMod Q))
    (dec : Finset (Fin n) → Finset (Fin n) → (Fin n → Fin D → ZMod Q) →
      Finset (Sym2 (Fin n))) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) (F : Finset (Fin n)), F.card < k →
    IsBoundaryRetrievalOracle G F cap (fun C => dec F C (matrixSketch Ψ G))

end PunctSketch


