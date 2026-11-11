-- Prove2me | Definitions.Def_SnarlSPQR_Snarls_Snarl
-- name    : SnarlSPQR_Snarls_Snarl
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:28:17.227009+00:00
-- url     : https://prove2.me/theorems/7ec34dcf-567a-4582-9e8f-90c70f70158e
-- title:
--   Splitting a vertex-side, separable pairs of vertex-sides, and snarls of a bidirected graph (Definition 3)
-- statement:
--   **Splitting** the vertex-side $u\alpha$ of a loopless bidirected graph $G=(V,E)$ produces $G'=(V\cup\{u'\},E')$, where
--   $$E' = E\setminus\{\{u\hat\alpha,v\beta\}\in E\}\ \cup\ \{\{u'\hat\alpha,v\beta\} : \{u\hat\alpha,v\beta\}\in E\}.$$
--   Every edge incident to $u$ with sign $\hat\alpha$ is moved to a new vertex $u'$. Splitting vertex-sides of distinct vertices commutes.
--
--   **Definition 3.** Let $x\alpha$ and $y\beta$ be vertex-sides with $x\neq y$.
--   - $\{x\alpha,y\beta\}$ is **separable** in $G$ if, in the graph obtained by splitting $x\alpha$ and $y\beta$, the component $X$ of $x$ (in the underlying undirected graph) contains $y$ but neither $x'$ nor $y'$. $X$ is the **snarl component**.
--   - $\{x\alpha,y\beta\}$ is a **snarl** of $G$ if it is separable and **minimal**: there are no vertex $z\notin\{x,y\}$ and sign $\gamma$ such that $X$ has the vertex-sides $z\gamma$ and $z\hat\gamma$ and both $\{x\alpha,z\gamma\}$ and $\{z\hat\gamma,y\beta\}$ are separable in $G$.
--
--   Snarls are bubble-like subgraphs of bidirected (pangenome) graphs. A graph can have quadratically many of them.
--
--   **Formalization Note.** `split G S` splits every vertex-side of `S` at once. It lives on the vertex type `V × Bool`: `(v, false)` is $v$ and `(v, true)` is the copy $v'$. An endpoint $a\sigma$ moves to $a'$ exactly when $a\hat\sigma\in S$. `Separable` and `Snarl` are predicates on ordered pairs, and both are symmetric in the two vertex-sides. The condition $z\notin\{x,y\}$ is a reading: the printed definition omits it, but Definition 2(b) and every proof use it. "$X$ has $z\gamma$" means that $(z,\mathrm{false})$ is reachable from $x$ in the split graph and some edge of the split graph contains $z\gamma$.
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), pp. 28–29, §5.1 (splitting) and Definition 3

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_BiGraph

open Classical

namespace SnarlSPQR.Snarls

/-!
# Splitting vertex-sides, separable pairs and snarls (§5.1, Definition 3, pp. 28–29)

Sena et al., arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), §5.1 (p. 28) and
Definition 3 (p. 29).

**Splitting** a vertex-side `uα` of `G = (V, E)` gives `G' = (V ∪ {u'}, E')` with
`E' = E \ {{uα̂, vβ} ∈ E} ∪ {{u'α̂, vβ} : {uα̂, vβ} ∈ E}`: every edge incident to `u` with sign
`α̂` is re-attached to a new vertex `u'`. Splitting several vertex-sides of distinct vertices
commutes. `split G S` splits all vertex-sides in `S` at once; its vertex type is `V × Bool`, where
`(v, false)` is the original `v` and `(v, true)` is the new copy `v'`. An endpoint `aσ` of an edge
moves to `a'` exactly when `aσ̂ ∈ S`.

**Definition 3.** For vertex-sides `xα, yβ` with `x ≠ y`:
* `{xα, yβ}` is **separable** in `G` if, in the graph `G'` created by splitting `xα` and `yβ`, the
  component `X` of `x` (in `U(G')`) contains `y` but neither `x'` nor `y'`; `X` is the snarl
  component;
* it is a **snarl** if it is separable and minimal: `X` has no vertex-sides `zγ` and `zγ̂` such
  that `{xα, zγ}` and `{zγ̂, yβ}` are separable in `G`.

Reading (BRIEF): in minimality `z ∉ {x, y}`, as in Definition 2(b) ("different from a and b") and
in every proof (Lemma 11: "with `w ≠ u, v`"). "`X` has the vertex-side `zγ`" means `z` is a vertex
of `X` and some edge of `G'` (equivalently of `G`, `z` not being split) contains `zγ`.

Both notions are predicates on ordered pairs and are symmetric in the two vertex-sides, so they
are predicates on the unordered pair `{xα, yβ}`.
-/

namespace BiGraph

variable {V : Type*}

/-- The new position of the endpoint `aσ` after splitting the vertex-sides in `S`. -/
noncomputable def splitSide (S : Finset (V × Sign)) (p : V × Sign) : (V × Bool) × Sign :=
  ((p.1, decide ((p.1, p.2.opp) ∈ S)), p.2)

/-- The graph obtained from `G` by splitting every vertex-side of `S`: original vertices
`(v, false)`, new vertices `(u, true)` (`u'`) for `uα ∈ S`, and every edge `{aσ, bτ}` re-attached
endpoint by endpoint (`splitSide`). -/
noncomputable def split (G : BiGraph V) (S : Finset (V × Sign)) : BiGraph (V × Bool) where
  verts := G.verts.image (fun v => (v, false)) ∪ S.image (fun p => (p.1, true))
  edges := G.edges.image (Sym2.map (splitSide S))

/-- The graph created by splitting `xα` and `yβ`. -/
noncomputable def split2 (G : BiGraph V) (a b : V × Sign) : BiGraph (V × Bool) := G.split {a, b}

/-- `{xα, yβ}` is separable in `G` (Definition 3(a)): `x ≠ y` and, after splitting `xα` and
`yβ`, `x` reaches `y` but neither `x'` nor `y'` in the underlying undirected graph. -/
def Separable (G : BiGraph V) (a b : V × Sign) : Prop :=
  a.1 ≠ b.1 ∧ (G.split2 a b).U.Reach (a.1, false) (b.1, false) ∧
    ¬ (G.split2 a b).U.Reach (a.1, false) (a.1, true) ∧
    ¬ (G.split2 a b).U.Reach (a.1, false) (b.1, true)

/-- The snarl component `X` of `{xα, yβ}` has the vertex-side `zγ`: `z` is a vertex of the
component of `x` after splitting `xα, yβ`, and some edge of the split graph contains `zγ`. -/
def CompHasSide (G : BiGraph V) (a b : V × Sign) (z : V) (γ : Sign) : Prop :=
  (G.split2 a b).U.Reach (a.1, false) (z, false) ∧ (G.split2 a b).HasSide (z, false) γ

/-- `{xα, yβ}` is a snarl of `G` (Definition 3): separable, and minimal — no `z ∉ {x, y}` and sign
`γ` such that the snarl component has `zγ` and `zγ̂` and both `{xα, zγ}` and `{zγ̂, yβ}` are
separable in `G`. -/
def Snarl (G : BiGraph V) (a b : V × Sign) : Prop :=
  G.Separable a b ∧
    ¬ ∃ z γ, z ≠ a.1 ∧ z ≠ b.1 ∧ G.CompHasSide a b z γ ∧ G.CompHasSide a b z γ.opp ∧
      G.Separable a (z, γ) ∧ G.Separable (z, γ.opp) b

end BiGraph

end SnarlSPQR.Snarls


