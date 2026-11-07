-- Prove2me | Definitions.Def_PunctSketch_alpha
-- name    : PunctSketch_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:42.304224+00:00
-- url     : https://prove2.me/theorems/924d3536-3a58-469c-8e72-91de71e00f61
-- title:
--   The field elements $\alpha_v$
-- statement:
--   For a modulus $Q$, $\alpha_v$ is the image in $\mathbb Z/Q$ of the $(v+1)$-st prime number, for $v\in\{0,\dots,n-1\}$. These are the evaluation points of all the sketches.
--
--   **Formalization Note** Vertices are zero-indexed, so the paper's $\alpha_1,\dots,\alpha_n$ are $\alpha_0,\dots,\alpha_{n-1}$ here.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), proof of Theorem 4, p.10 (PDF p.11)

import Mathlib

namespace PunctSketch

/-- **The field elements `α_v`.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), proof of Theorem 4, p.10: "Let α_1, ..., α_n be the images,
under the canonical ring homomorphism from ℤ to 𝔽_Q, of the first n prime numbers."

**Formalization Note.** Vertices are `Fin n`, zero-indexed, so `α_v` is the image of the
`(v+1)`-st prime, `Nat.nth Nat.Prime v`. -/
noncomputable def alpha (Q : ℕ) {n : ℕ} (v : Fin n) : ZMod Q :=
  ((Nat.nth Nat.Prime (v : ℕ) : ℕ) : ZMod Q)

end PunctSketch


