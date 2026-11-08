-- Prove2me | Definitions.Def_ValiantModel_IsWeakScheme
-- name    : ValiantModel_IsWeakScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:25.870079+00:00
-- url     : https://prove2.me/theorems/42eed2ea-a921-4407-aad3-aba5c6509e41
-- title:
--   Definition 13, p.22 — weak query-based compression scheme
-- statement:
--   A deterministic adaptive query strategy $\sigma$ is a **weak query-based compression scheme** for a finite set $S\subseteq\{0,1\}^d$ if, for every response transcript $r$ of $\sigma$ realizable with respect to $V(S)$,
--
--   $$
--   \Bigl|S\cap\bigcap_{h\in V(\sigma,r)}\mathrm{supp}(h)\Bigr|\ge\frac13\,|S| .
--   $$
--
--   A weak scheme certifies a constant fraction of $S$ rather than all of it; recursing on the rest gives Definition 2.
--
--   **Formalization Note** Realizable transcripts are encoded as in Definition 2, through a hypothesis $h_0\in V(S)$.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.22 (PDF p.24), Definition 13

import Mathlib
import Definitions.Def_ValiantModel_Strategy
import Definitions.Def_ValiantModel_VersionSpaces

namespace ValiantModel

/-- **Definition 13 (Weak Query-Based Compression Scheme)**, arXiv:2605.13840 (version held), p.22
(PDF p.24): for every response transcript of `σ` realizable with respect to `V(S)`,
`|S ∩ ⋂_{h ∈ V(σ, r)} supp(h)| ≥ (1/3) |S|`. Realizable transcripts are encoded as in
`IsCompressionScheme`. -/
def IsWeakScheme {d : ℕ} (Hd : Set (Hypothesis d)) (S : Finset (Point d)) (σ : Strategy d) : Prop :=
  ∀ h₀ ∈ positiveVS Hd S,
    (1 / 3 : ℝ) * (S.card : ℝ) ≤
      ((S.filter fun x => closureOf (transcriptVS Hd (σ.transcript h₀)) x = true).card : ℝ)

end ValiantModel


