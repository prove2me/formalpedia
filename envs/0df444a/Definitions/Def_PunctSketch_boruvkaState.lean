-- Prove2me | Definitions.Def_PunctSketch_boruvkaState
-- name    : PunctSketch_boruvkaState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:32.839658+00:00
-- url     : https://prove2.me/theorems/17a616da-ffca-45a5-adaf-f6774ecdd5f2
-- title:
--   The Borůvka process
-- statement:
--   The process keeps a set $T$ of pairs; its blobs are the components of $T\setminus F$, and it starts from $T=\emptyset$, the partition into singletons. In a round, with the round's fresh coins, the sampler is queried at the blob of each vertex outside $F$, the blobs being those at the start of the round. A returned pair is added to $T$ when its endpoints are distinct and not yet connected. After $R$ rounds, $T$ is the output.
--
--   **Formalization Note** A returned pair that touches $F$ is added too, and then $T$ fails to be a forest on $V\setminus F$, which is what the coordinator tests on p.22.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §2, p.6 (PDF p.7); §5.1, p.16 (PDF p.17); proof of Lemma 5.2, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_PunctSketch_forestGraph

namespace PunctSketch

open Classical in
/-- **The blob of `x`.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §2, p.6, §5.1, p.16: the vertices connected to `x` in `T ∖ F`. -/
noncomputable def blob {V : Type*} [Fintype V] (F : Finset V) (T : Finset (Sym2 V)) (x : V) :
    Finset V :=
  Finset.univ.filter (fun y => ConnAvoid (forestGraph T) F x y)

open Classical in
/-- Merge along a returned pair: add it when its two endpoints are distinct and not yet connected in
`T ∖ F`, which keeps `T` free of cycles. A pair that touches `F` is added too; it then shows up as
`T` not being a forest on `V ∖ F`. -/
noncomputable def addIfJoins {V : Type*} (F : Finset V) (T : Finset (Sym2 V)) (e : Sym2 V) :
    Finset (Sym2 V) :=
  if ∃ x y, e = s(x, y) ∧ x ≠ y ∧ ¬ ConnAvoid (forestGraph T) F x y then insert e T else T

open Classical in
/-- **One Borůvka round.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §2, p.6, §5.1, p.16, proof of Lemma 5.2, p.17. Query the round's
sampler, with the round's coins, at the blob of every vertex outside `F` (the blobs are those at the
start of the round) and merge along the returned pairs. -/
noncomputable def boruvkaRound {n : ℕ} {Ω : Type*} (BS : Finset (Fin n) → Ω → Option (Sym2 (Fin n)))
    (F : Finset (Fin n)) (ω : Ω) (T : Finset (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  (List.finRange n).foldl
    (fun T' x =>
      if x ∈ F then T' else
        match BS (blob F T x) ω with
        | some e => addIfJoins F T' e
        | none => T')
    T

/-- **The state of the Borůvka process after `r` rounds**, from the partition into singletons. Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…),
§5.1, p.16, step 3. Round `r` uses the fresh coins `ω r`; rounds past `R` change nothing. -/
noncomputable def boruvkaState {n R : ℕ} {Ω : Type*}
    (BS : Finset (Fin n) → Ω → Option (Sym2 (Fin n))) (F : Finset (Fin n)) (ω : Fin R → Ω) :
    ℕ → Finset (Sym2 (Fin n))
  | 0 => ∅
  | r + 1 =>
      if h : r < R then boruvkaRound BS F (ω ⟨r, h⟩) (boruvkaState BS F ω r)
      else boruvkaState BS F ω r

end PunctSketch


