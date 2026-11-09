-- Prove2me | Definitions.Def_DirectedHamiltonicity_Main_ArcCopies
-- name    : DirectedHamiltonicity_Main_ArcCopies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:28.549305+00:00
-- url     : https://prove2.me/theorems/b2a95284-f180-45ea-844c-179b2d9ae487
-- title:
--   Random arc copies, incoming groups, group selections, the path polynomial and the cancellation space
-- statement:
--   Let $G=(V,A)$ be a simple directed graph, $s,t$ vertices and $d\ge1$ an integer, $[d]=\{1,\dots,d\}$, and
--   $$\delta=\frac1{1+(2^d-1)^2}.$$
--
--   1. For each arc $uv\in A$ a set $S_{uv}\subseteq[d]$ is drawn, independently over the arcs, with $\Pr[S_{uv}=\varnothing]=\delta$ and $\Pr[S_{uv}=S]=\frac{1-\delta}{2^d-1}=(2^d-1)\delta$ for every nonempty $S$. The probability of an event is the sum, over the joint outcomes in the event, of the product of these per-arc probabilities.
--   2. For each $\ell\in S_{uv}$ there is one labelled copy $(uv,\ell)$ of the arc $uv$, placed in the **incoming group** $\widehat A_{v,\ell}$. The multigraph $\widehat G$ has all these copies as its arcs.
--   3. A **group selection** is a tuple $(\ell_v)_{v\ne s}\in[d]^{n-1}$; its selected multigraph $(V,\bigcup_{v\ne s}\widehat A_{v,\ell_v})$ has the copies in the selected groups.
--   4. The **path polynomial** over $\mathbb F_2$, in indeterminates $z_{v\ell}$ ($v\ne s$, $\ell\in[d]$), is
--   $$f(z)=\sum_{P\in\mathcal P_{s,t}(G)}\prod_{uv\in P}\Bigl(\sum_{\ell\in S_{uv}}z_{v\ell}\Bigr).$$
--   5. For a field $K$, nonzero $f_1,\dots,f_p$ in a polynomial ring over $K$ and distinct indeterminates $z_{i\ell}$, the **cancellation space** is $W=\{c\in K^{[p]\times[d]}:\sum_{i=1}^p\sum_{\ell=1}^d c_{i\ell}z_{i\ell}f_i=0\}$, the kernel of a linear map.
--
--   These are the random construction of §2 and the algebraic objects of §3.
--
--   **Formalization Note** $[d]$ is `Fin d` (indices $0,\dots,d-1$). In $f$, a factor for an arc entering $s$ would be $0$; the theorems assume, as §2 does, that no arc enters $s$. The cancellation space is `LinearMap.ker` of $c\mapsto\sum_{(i,\ell)}c_{i\ell}\,X_{z(i,\ell)}f_i$ in `MvPolynomial σ K`.
-- source:
--   Tomohiro Koana, Soh Kumabe, Breaking the $2^n$ barrier for directed hamiltonicity, STOC 2027 submission #811 (October 2026), source.pdf SHA-256 103ec74bdf635a66ec16e2c21d6fbc0896c1aa986065e20007ae217a701fffb3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf, PDF p.4 / printed p.3 (§2 construction, δ and the law of the copy sets), PDF pp.5–6 / printed pp.4–5 (§3, ρ, f(z), Lemma 6's W)

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_Graphs

namespace DirectedHamiltonicity.Main

open Multidigraph

/-!
# §2–§3: random arc copies, incoming groups, group selections and the path polynomial

T. Koana, S. Kumabe, STOC 2027 submission #811 (October 2026), §2 (PDF p.4 / printed p.3) and §3
(PDF pp.5–6 / printed pp.4–5).

`G` is a simple digraph on `V` given by an adjacency relation `adj` (its arcs are the pairs `(u,v)`
with `adj u v`). For an integer `d`, every arc `uv` independently receives a set `S_uv ⊆ [d]`
(here `[d] = Fin d`) with `Pr[S_uv = ∅] = δ` and `Pr[S_uv = S] = (1 − δ)/(2^d − 1)` for each nonempty
`S`, where `δ = 1/(1 + (2^d − 1)^2)`. For each `ℓ ∈ S_uv` one labelled copy `(uv, ℓ)` is placed in the
incoming group `Â_{v,ℓ}`. The multigraph `Ĝ` consists of all copies.
-/

variable {V : Type}

/-- The arcs of the simple digraph `adj`: ordered pairs `(u, v)` with `adj u v`. -/
abbrev SArc (adj : V → V → Prop) := {a : V × V // adj a.1 a.2}

/-- `δ = 1/(1 + (2^d − 1)^2)` (§2, PDF p.4). -/
noncomputable def delta (d : ℕ) : ℝ := 1 / (1 + ((2 : ℝ) ^ d - 1) ^ 2)

/-- The law of one set `S_uv ⊆ [d]`: `δ` for the empty set and `(1 − δ)/(2^d − 1)` for each nonempty
set (§2, PDF p.4; §3, PDF p.5, where this value is called `ρ = (2^d − 1)δ`). -/
noncomputable def copySetProb (d : ℕ) (S : Finset (Fin d)) : ℝ :=
  if S = ∅ then delta d else (1 - delta d) / ((2 : ℝ) ^ d - 1)

/-- The probability of one joint outcome `S = (S_uv)_{uv}`: the sets are independent. -/
noncomputable def assignProb {adj : V → V → Prop} [Fintype (SArc adj)] (d : ℕ)
    (S : SArc adj → Finset (Fin d)) : ℝ :=
  ∏ a, copySetProb d (S a)

open Classical in
/-- `Pr_S[E]`: the probability, under independent sets `S_uv` with the law `copySetProb d`, of an
event `E` on the joint outcome. -/
noncomputable def copyProb {adj : V → V → Prop} [Fintype (SArc adj)] (d : ℕ)
    (E : (SArc adj → Finset (Fin d)) → Prop) : ℝ :=
  ∑ S ∈ Finset.univ.filter E, assignProb d S

/-- The labelled copies `(uv, ℓ)`, `ℓ ∈ S_uv`: the arc set of `Ĝ`. -/
abbrev ArcCopy (adj : V → V → Prop) {d : ℕ} (S : SArc adj → Finset (Fin d)) :=
  Σ a : SArc adj, {ℓ : Fin d // ℓ ∈ S a}

/-- The multigraph `Ĝ` of all copies: the copy `(uv, ℓ)` goes from `u` to `v`. -/
def copyGraph (adj : V → V → Prop) {d : ℕ} (S : SArc adj → Finset (Fin d)) :
    Multidigraph V (ArcCopy adj S) :=
  ⟨fun c => c.1.1.1, fun c => c.1.1.2⟩

/-- The copy `c = (uv, ℓ)` lies in the selected group of its head: `v ≠ s` and `ℓ = ℓ_v`. (The copy
`(uv, ℓ)` belongs to the group `Â_{v,ℓ}`.) -/
def InSelectedGroup (adj : V → V → Prop) {d : ℕ} (S : SArc adj → Finset (Fin d)) (s : V)
    (sel : {v // v ≠ s} → Fin d) (c : ArcCopy adj S) : Prop :=
  ∃ h : c.1.1.2 ≠ s, c.2.1 = sel ⟨c.1.1.2, h⟩

/-- The multigraph `(V, ⋃_{v ≠ s} Â_{v,ℓ_v})` of the copies in the selected groups. -/
def selectedGraph (adj : V → V → Prop) {d : ℕ} (S : SArc adj → Finset (Fin d)) (s : V)
    (sel : {v // v ≠ s} → Fin d) : Multidigraph V {c // InSelectedGroup adj S s sel c} :=
  (copyGraph adj S).restrictArcs (InSelectedGroup adj S s sel)

/-- The path polynomial of §3 (PDF p.6) over `𝔽₂` in the indeterminates `z_{vℓ}`, `v ≠ s`, `ℓ ∈ [d]`:
`f(z) = ∑_{P ∈ 𝒫_{s,t}(G)} ∏_{uv ∈ P} (∑_{ℓ ∈ S_uv} z_{vℓ})`. A factor for an arc entering `s` would
be `0`; under the standing assumption of §2 there is no such arc. -/
noncomputable def pathPoly [Fintype V] [DecidableEq V] (adj : V → V → Prop) [Fintype (SArc adj)] {d : ℕ}
    (s t : V) (S : SArc adj → Finset (Fin d)) : MvPolynomial ({v // v ≠ s} × Fin d) (ZMod 2) :=
  ∑ P ∈ (ofAdj adj).hamPaths s t,
    ∏ i, ∑ ℓ ∈ S (P i),
      (if h : (P i).1.2 ≠ s then MvPolynomial.X (⟨(P i).1.2, h⟩, ℓ) else 0)

/-- The cancellation space `W` of Lemma 6 (§3, PDF p.6): the coefficient vectors `c ∈ K^{[p]×[d]}` with
`∑_{i,ℓ} c_{iℓ} z_{iℓ} f_i = 0` in the polynomial ring `MvPolynomial σ K`, where `z_{iℓ}` is the
indeterminate `X (z (i, ℓ))`. -/
noncomputable def cancelSpace {K σ : Type} [Field K] {p d : ℕ} (z : Fin p × Fin d → σ)
    (f : Fin p → MvPolynomial σ K) : Submodule K (Fin p × Fin d → K) :=
  LinearMap.ker
    (∑ j : Fin p × Fin d,
      (LinearMap.proj j : (Fin p × Fin d → K) →ₗ[K] K).smulRight
        (MvPolynomial.X (z j) * f j.1))

end DirectedHamiltonicity.Main


