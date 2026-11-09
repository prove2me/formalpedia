-- Prove2me | Definitions.Def_HopRamsey_CallInv
-- name    : HopRamsey_CallInv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:16.670876+00:00
-- url     : https://prove2.me/theorems/b1a75033-fbc4-47cf-935e-cdbb2316e15f
-- title:
--   Standing assumptions of §4 and the call invariant
-- statement:
--   The analysis of §4 works under **standing assumptions**: $N=|V|\ge2$, every edge weight is at least $2$, $\Phi\ge2$, $\varepsilon\in(0,1)$ and $h\ge1$. A call Hop-Stochastic-Embedding$(G,X,M,h,\Delta)$ satisfies the **call invariant** when
--
--   $$
--   X\neq\emptyset,\qquad M\subseteq X,\qquad \Delta\ge1,\qquad \mathrm{diam}^{(2k(L+1)h)}_G(X)\le\Delta .
--   $$
--
--   The paper assumes the diameter bound recursively (§4.1) and proves it for every call (Corollary 1); $\Delta\ge1$ is shown at the start of the proof of Lemma 1. Lemmas 1 and 2 and Claim 2 are stated for calls satisfying the invariant.
--
--   **Formalization Note** The diameter is in $[0,\infty]$, with $k$ and $L$ the global parameters of Figure 2.
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), §4.1, p.14 (PDF p.16); proof of Lemma 1, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HopRamsey_hopDist
import Definitions.Def_HopRamsey_Fig2Params

open scoped ENNReal

namespace HopRamsey

open ARTreeCover

/-- The standing assumptions of §4 (p.14, PDF p.16) on the graph and the global parameters:
`P.N = |V| ≥ 2`, every edge weight is at least `2` ("We assume that the minimum edge weight in G is
2"), `Φ ≥ 2`, `ε ∈ (0, 1)` and `h ≥ 1`. -/
def Standing {V : Type} [Fintype V] (P : Fig2Params) (G : WGraph V) (h : ℕ) : Prop :=
  P.N = Fintype.card V ∧ 2 ≤ P.N ∧ (∀ e ∈ G.graph.edgeSet, 2 ≤ G.w e) ∧ 2 ≤ P.Φ ∧
    0 < P.ε ∧ P.ε < 1 ∧ 1 ≤ h

/-- The invariant of a call `Hop-Stochastic-Embedding(G, X, M, h, ∆)`.

Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), §4.1, p.14
(PDF p.16): "we treat X as the current active set, and M ⊆ X as the padded vertices. [...] We also
recursively assume that diam^{(2k·(L+1)·h)}_G(X) ≤ ∆"; proof of Lemma 1, p.19 (PDF p.21): "every
call (including calls with n = 1) has ∆ ≥ 1".

**Formalization Note.** The invariant is `X ≠ ∅`, `M ⊆ X`, `∆ ≥ 1` and
`diam^{(2k(L+1)h)}_G(X) ≤ ∆` (in `[0, ∞]`). Corollary 1 shows that every call the algorithm makes
from the root call satisfies it. -/
def CallInv {V : Type} (P : Fig2Params) (G : WGraph V) (h : ℕ) (X M : Finset V) (Δ : ℝ) : Prop :=
  X.Nonempty ∧ M ⊆ X ∧ 1 ≤ Δ ∧
    hopDiam G (2 * P.k * (P.L + 1) * h) X ≤ ENNReal.ofReal Δ

end HopRamsey


