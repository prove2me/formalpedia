-- Prove2me | Definitions.Def_DoublingMST_IsAlg2Graph
-- name    : DoublingMST_IsAlg2Graph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:40:21.200597+00:00
-- url     : https://prove2.me/theorems/b4311c75-0b46-4354-9879-1f6ec5531085
-- title:
--   Graph $G$ built by Algorithm 2 (Lines 1–15)
-- statement:
--   For $\epsilon=2^{-K}$, a net hierarchy $N$, a set $\Psi$ of pairs and a set $G$ of edges: $G$ is a graph **that Algorithm 2 can build** if $\Psi$ is an output of Algorithm 1 on $N$ with $t=32$, and for some critical level $\ell^*$ and some choice of an edge $(p,q)$ for each $(u,v)\in\Psi$ following Lines 6–14, $G$ is the set of chosen edges $\{p,q\}$.
--
--   **Formalization Note** All choices the algorithm leaves open (the run of Algorithm 1, ties in $\ell^*$ and in the argmins) are existential here.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Algorithm 2, Lines 1–15, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_DoublingMST_IsAlg1Output
import Definitions.Def_DoublingMST_IsCriticalLevel
import Definitions.Def_DoublingMST_IsRepEdge

namespace DoublingMST

/-- **A graph G that Algorithm 2 can build (Lines 1–15).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Algorithm 2, Lines 1–15, p.18 (PDF p.20): compute the net hierarchy; "let ℓ* ←
argmax_{0≤ℓ≤L} 2^{ℓ/2} · |N_ℓ|"; "apply Lemma 3.3 with t = 32 to compute the collection Ψ of pairs of
net points"; "let G ← (X, ∅)"; for each `(u, v) ∈ Ψ` choose `(p, q)` by Lines 6–14; "add (p, q) to G".

`IsAlg2Graph H K Ψ G`, for `ϵ = 2^{−K}`: `Ψ` is an output of Algorithm 1 on `H` with `t = 32`, some
critical level `ℓs` and some choice `(u, v) ↦ (p, q)` obeying Lines 6–14 give `G` as the set of
the chosen edges `{p, q}`.

**Formalization Note.** Every nondeterministic choice of the algorithm (the run of Algorithm 1,
ties in ℓ\* and in the argmins) is existential here; statements about "the" graph quantify over
every `(H, Ψ, G)` with this property. -/
def IsAlg2Graph {n : ℕ} {d : Fin n → Fin n → ℝ} (H : NetHierarchy d) (K : ℕ)
    (Ψ : Finset ((Fin n × ℕ) × (Fin n × ℕ))) (G : Finset (Sym2 (Fin n))) : Prop :=
  IsAlg1Output H 32 Ψ ∧ ∃ ℓs : ℕ, IsCriticalLevel H ℓs ∧
    ∃ pick : (Fin n × ℕ) × (Fin n × ℕ) → Fin n × Fin n,
      (∀ uv ∈ Ψ, IsRepEdge H K ℓs uv.1 uv.2 (pick uv).1 (pick uv).2) ∧
      G = Ψ.image fun uv => s((pick uv).1, (pick uv).2)

end DoublingMST


