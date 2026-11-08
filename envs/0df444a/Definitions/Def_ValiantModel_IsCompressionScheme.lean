-- Prove2me | Definitions.Def_ValiantModel_IsCompressionScheme
-- name    : ValiantModel_IsCompressionScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:49.36883+00:00
-- url     : https://prove2.me/theorems/2ca72803-28ea-43b1-be1a-ffd5d9e4b5d0
-- title:
--   Definition 2, p.3 — adaptive-query compression scheme
-- statement:
--   Fix $d$ and $S\subseteq\{0,1\}^d$ with $V(S)\neq\emptyset$. A deterministic adaptive query strategy $\Sigma_S$ is an **adaptive-query compression scheme** for $S$ if, for every response transcript $r$ of $\Sigma_S$ that is realizable with respect to $V(S)$,
--
--   $$
--   S\subseteq\bigcap_{h\in V(\Sigma_S,r)}\mathrm{supp}(h).
--   $$
--
--   Its **size** is the depth of $\Sigma_S$. A transcript is realizable with respect to $V(S)$ if $\Sigma_S$ produces it on some hypothesis in $V(S)$. The version space $V(\Sigma_S,r)$ ranges over all of $H_d$: restricting it to $V(S)$ would make depth $0$ work for every class. Transcripts realized by no member of $V(S)$ are unconstrained, though they count in the depth.
--
--   **Formalization Note** The quantifier over realizable transcripts is written as a quantifier over a hypothesis $h_0\in V(S)$, with $r$ the responses of $h_0$ along $\Sigma_S$.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.3 (PDF p.5), Definition 2 and footnote 3

import Mathlib
import Definitions.Def_ValiantModel_Strategy
import Definitions.Def_ValiantModel_VersionSpaces

namespace ValiantModel

/-- **Definition 2 (Adaptive-Query Compression Scheme)**, arXiv:2605.13840 (version held), p.3
(PDF p.5): `σ` is a scheme for `S` if, for every response transcript of `σ` realizable with respect
to `V(S)`, `S ⊆ ⋂_{h ∈ V(σ, r)} supp(h)`. Its size is `σ.depth`.

**Formalization Note.** A transcript realizable with respect to `V(S)` is by footnote 3 the
transcript of `σ` on some `h₀ ∈ V(S)`, so the quantifier is over such `h₀`, and
`V(σ, r) = transcriptVS Hd (σ.transcript h₀)` (display (2), p.16, PDF p.18) ranges over all of
`Hd`. Transcripts realized by no hypothesis of `V(S)` are unconstrained, but count in the depth. -/
def IsCompressionScheme {d : ℕ} (Hd : Set (Hypothesis d)) (S : Finset (Point d))
    (σ : Strategy d) : Prop :=
  ∀ h₀ ∈ positiveVS Hd S, ∀ x ∈ S, closureOf (transcriptVS Hd (σ.transcript h₀)) x = true

end ValiantModel


