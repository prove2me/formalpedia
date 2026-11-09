-- Prove2me | Definitions.Def_HybridXorLift_xorComp
-- name    : HybridXorLift_xorComp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:39.781853+00:00
-- url     : https://prove2.me/theorems/8c6d0a06-6f46-43d2-bf7f-c3ba620779ce
-- title:
--   Composed partial function $f \circ \mathrm{XOR}_r$
-- statement:
--   Let $f : D \to \{0,1\}$ be a partial Boolean function with $D \subseteq \{0,1\}^n$ and let $r \ge 1$. The **composed function** $f \circ \mathrm{XOR}_r$ is the partial function on $nr$ physical bits given by
--   $$
--   (f \circ \mathrm{XOR}_r)(x) = f(\sigma(x)), \qquad \text{promised inputs } \{x : \sigma(x) \in D\},
--   $$
--   where $\sigma$ is the outer string of block parities.
--
--   This is the function whose one-query hybrid complexity the mission bounds from below.
--
--   **Formalization Note** It is the published block composition of partial functions (`NoPerfectRandComp.PartialFn.comp`) applied to $f$ and the total parity gadget on each block, so its domain is exactly $\{x : \sigma(x) \in D\}$ and its value is $f(\sigma(x))$; values of $f$ outside $D$ are never constrained.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §2.3, p.10 (PDF p.12)

import Definitions.Def_NoPerfectRandComp_PartialFn
import Definitions.Def_HybridXorLift_outer

namespace HybridXorLift

/-- The composed partial function `f ∘ XOR_r` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §2.3, p.10 (PDF p.12)): it maps a physical
input `x` to `f(σ(x))`, and its promised inputs are the strings `x` with `σ(x) ∈ D`.

**Formalization Note** It is the published block composition `NoPerfectRandComp.PartialFn.comp`
with the total parity gadget `blockParity r` on each block; its domain is
`{x | (fun i => blockParity r (x (i, ·))) ∈ f.dom} = {x | outer x ∈ f.dom}` and its value is
`f.val (outer x)`. -/
def xorComp {n : ℕ} (f : NoPerfectRandComp.PartialFn (Fin n)) (r : ℕ) :
    NoPerfectRandComp.PartialFn (Fin n × Fin r) :=
  f.comp (NoPerfectRandComp.PartialFn.total (blockParity r))

end HybridXorLift


