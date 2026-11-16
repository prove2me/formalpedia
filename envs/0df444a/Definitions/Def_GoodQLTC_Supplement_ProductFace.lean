-- Prove2me | Definitions.Def_GoodQLTC_Supplement_ProductFace
-- name    : GoodQLTC_Supplement_ProductFace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:59:31.363642+00:00
-- url     : https://prove2.me/theorems/4ec552c2-55dc-46ef-916a-632d7d1c741b
-- title:
--   Product face poset of Bruhat–Tits trees, parities, labels and orbit quotients
-- statement:
--   Let $L$ be a field with a discrete valuation ring $\mathcal O_L\subseteq L$. The **Bruhat–Tits tree** $T(L)$ has as vertices the homothety classes $[\Lambda]$ of lattices $\Lambda\subseteq L^2$ (free $\mathcal O_L$-submodules of rank two spanning $L^2$), with $[\Lambda]$ adjacent to $[\Lambda']$ when representatives satisfy $\pi_L\Lambda\subsetneq\Lambda'\subsetneq\Lambda$; $\mathrm{GL}_2(L)$ acts by $g[\Lambda]=[g\Lambda]$. A **cell** of $T(L)$ is a vertex or an edge (an unordered pair of adjacent vertices). The **parity** of a vertex is
--   $$\phi_L([g\mathcal O_L^2]) := v_L(\det g) \bmod 2,$$
--   where $v_L$ is the normalized valuation.
--
--   For trees $T_1,\dots,T_t$ the **product face poset** is
--   $$\mathcal T := \bigsqcup_{I\subseteq[t]}\ \prod_{i\in I}T_i(1)\times\prod_{i\notin I}T_i(0),$$
--   the set of choices of one cell in each coordinate, ordered coordinatewise (a vertex lies below the edges containing it). The **label** of a face has a star $\star$ in each edge coordinate and the vertex parity in every other coordinate. An element $g=(g_i)\in\prod_i\mathrm{GL}_2(L_i)$ acts on faces coordinatewise.
--
--   For a set $\Gamma$ of group elements acting through $\rho:G\to\prod_i\mathrm{GL}_2(L_i)$, a map $p:\mathcal T\to X$ onto a poset $X$ with labels $\varphi_X$ **is the orbit poset** $\Gamma\backslash\mathcal T$ if $p$ is onto, $p(f)=p(g)$ iff $\gamma f=g$ for some $\gamma\in\Gamma$, $p(f)\le p(g)$ iff $\gamma f\le g$ for some $\gamma\in\Gamma$, and $\varphi_X(p(f))$ is the label of $f$. Finally, $p$ **induces poset isomorphisms on upward stars** if for every $f\in\mathcal T$ the map $g\mapsto p(g)$ is an order isomorphism $\mathcal T_{\ge f}\to X_{\ge p(f)}$.
--
--   These are the objects of Theorem 11.1 and Theorem 14.1.
--
--   **Formalization Note** $T(L)$ is the published Bruhat–Tits tree `CerednikDrinfeld.BruhatTits.tree O L` (lattices are finitely generated $\mathcal O_L$-submodules spanning $L^2$, which over a discrete valuation ring are exactly the free rank-two lattices, and adjacency uses an irreducible $\varpi$, i.e. a uniformizer up to a unit). A cell is a `Finset` of one vertex or of two adjacent vertices, so the face order is coordinatewise inclusion. $v_L(\det g)$ is even iff $\det g=u y^2$ with $u\in\mathcal O_L^\times$, $y\in L^\times$. The orbit poset is characterized up to isomorphism by the surjection $p$ instead of being constructed as a quotient type, so that its finiteness and poset axioms are statements of the theorems.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §11, p.33 (PDF 36): T(L), parity, product face poset, labels, orbit order; Theorem 11.1 (2), p.34

import Mathlib
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_GoodQLTC_dir

namespace GoodQLTC.Supplement

open LT.LatticeTree CerednikDrinfeld.BruhatTits

open Classical in
/-- A **cell** of the Bruhat–Tits tree `T(L)`, Gay–Jeronimo, arXiv:2609.20780 (held version), §11,
p.33: a vertex `{x}` or an edge `{x, y}` (an unordered pair of adjacent vertices).

**Formalization Note.** `T(L)` is the published `CerednikDrinfeld.BruhatTits.tree O L`: its vertices
are the homothety classes of full `O`-lattices in `L²` (finitely generated `O`-submodules spanning
`L²`, which over a discrete valuation ring are exactly the free rank-two lattices of the paper), and
`[Λ]` is adjacent to `[Λ']` iff representatives satisfy `ϖΛ < Λ' < Λ` for an irreducible `ϖ`
(over a discrete valuation ring the irreducibles are the uniformizers `π_L` up to units). A cell is a
`Finset` of vertices, so that a vertex lies below an edge iff it is one of its two endpoints. -/
def IsTreeCell {L : Type} [Field L] (O : ValuationSubring L) (s : Finset (Vertex O L)) : Prop :=
  (∃ x, s = {x}) ∨ ∃ x y, (tree O L).Adj x y ∧ s = {x, y}

/-- `v` has **even normalized valuation**: `v_L(d)` is even iff `d = u y²` with `u ∈ O_L^×` and
`y ∈ L^×` (for a discrete valuation ring `O_L`, `v_L(u π^n) = n`). -/
def IsEvenVal {L : Type} [Field L] (O : ValuationSubring L) (d : L) : Prop :=
  ∃ u : Oˣ, ∃ y : L, y ≠ 0 ∧ d = ((u : O) : L) * y ^ 2

open Classical in
/-- The **parity** `ϕ_L([gO_L²]) := v_L(det g) mod 2` of a vertex of `T(L)`, Gay–Jeronimo,
arXiv:2609.20780 (held version), §11, p.33 (`true` = 1, `false` = 0).

**Formalization Note.** `[O_L²]` is the published `stdVertex O L` and `g • [Λ] = [gΛ]` is the
published `GL₂(L)`-action. The parity is `true` iff some `g ∈ GL₂(L)` with `g[O_L²] = x` has
`v_L(det g)` odd (`¬ IsEvenVal`); since the parity is well defined (Lemma 11.2, a property, not an
assumption), this is the same as "every such `g`". -/
noncomputable def vertexParity {L : Type} [Field L] (O : ValuationSubring L) (x : Vertex O L) :
    Bool :=
  decide (∃ g : GL (Fin 2) L, g • stdVertex O L = x ∧ ¬ IsEvenVal O (Matrix.det (g : Matrix (Fin 2) (Fin 2) L)))

/-- The **product face poset** `T := ⊔_{I⊆[t]} ∏_{i∈I} T_i(1) × ∏_{i∉I} T_i(0)` of trees
`T_i = T(L_i)`, Gay–Jeronimo, arXiv:2609.20780 (held version), §11, p.33: a face is a choice of a
cell (vertex or edge) in each coordinate; the edge coordinates form `I`.

**Formalization Note.** A face is a function `f` with `f i` a cell of `T(L_i)` (`IsTreeCell`). The
subtype carries the coordinatewise order `f ≤ g ↔ ∀ i, f i ⊆ g i` (Mathlib's order on functions to
`Finset`), which is the paper's coordinatewise face order. -/
def ProductFace {t : ℕ} {L : Fin t → Type} [∀ i, Field (L i)] (O : ∀ i, ValuationSubring (L i)) :
    Type :=
  {f : ∀ i, Finset (Vertex (O i) (L i)) // ∀ i, IsTreeCell (O i) (f i)}

instance {t : ℕ} {L : Fin t → Type} [∀ i, Field (L i)] (O : ∀ i, ValuationSubring (L i)) :
    PartialOrder (ProductFace O) := by
  unfold ProductFace
  infer_instance

open Classical in
/-- The **label** of a product face, Gay–Jeronimo, arXiv:2609.20780 (held version), §11, p.33: a star
(`none`) in each edge coordinate and the vertex parity in every other coordinate. -/
noncomputable def faceLabel {t : ℕ} {L : Fin t → Type} [∀ i, Field (L i)]
    {O : ∀ i, ValuationSubring (L i)} (f : ∀ i, Finset (Vertex (O i) (L i))) :
    Fin t → Option Bool :=
  fun i => if (f i).card = 2 then none else some (decide (∃ x ∈ f i, vertexParity (O i) x = true))

open Classical in
/-- The coordinatewise action of `g = (g_i) ∈ ∏_i GL₂(L_i)` on faces: `(g f)_i := g_i f_i`
(arXiv:2609.20780, §11, p.33: a group acting "preserving the factors"). -/
noncomputable def faceAct {t : ℕ} {L : Fin t → Type} [∀ i, Field (L i)]
    {O : ∀ i, ValuationSubring (L i)} (g : ∀ i, GL (Fin 2) (L i))
    (f : ∀ i, Finset (Vertex (O i) (L i))) : ∀ i, Finset (Vertex (O i) (L i)) :=
  fun i => (f i).image fun x => g i • x

/-- `p : T → X` **is the orbit poset** `Γ\T` of the group elements `Γ` acting through
`ρ : G → ∏_i GL₂(L_i)`, Gay–Jeronimo, arXiv:2609.20780 (held version), §11, p.33: `p` is onto,
`p f = p g` iff `γ f = g` for some `γ ∈ Γ`, the order is `[f] ≤ [g]` iff `γ f ≤ g` for some
`γ ∈ Γ`, and the label of `[f]` is the label of `f`.

**Formalization Note.** The orbit poset is described up to isomorphism by a surjection `p` onto a
poset `X` with these properties (this avoids proving, inside a definition, that the orbit relation
is an equivalence and the orbit order a partial order; in the theorems those are conclusions,
carried by the `PartialOrder X` and `Fintype X` that are asserted to exist). -/
structure IsOrbitQuotient {t : ℕ} {L : Fin t → Type} [∀ i, Field (L i)]
    {O : ∀ i, ValuationSubring (L i)} {G : Type} (ρ : G → ∀ i, GL (Fin 2) (L i)) (Γ : Set G)
    {X : Type} [PartialOrder X] (p : ProductFace O → X) (φX : X → Fin t → Option Bool) : Prop where
  surj : Function.Surjective p
  eq_iff : ∀ f g : ProductFace O, p f = p g ↔ ∃ γ ∈ Γ, faceAct (ρ γ) f.1 = g.1
  le_iff : ∀ f g : ProductFace O, p f ≤ p g ↔ ∃ γ ∈ Γ, faceAct (ρ γ) f.1 ≤ g.1
  label : ∀ f : ProductFace O, φX (p f) = faceLabel f.1

/-- For every `f ∈ T`, **the quotient map induces a poset isomorphism `T_{≥f} → X_{≥[f]}`**,
Gay–Jeronimo, arXiv:2609.20780 (held version), Theorem 11.1 (2), p.34: on `T_{≥f}` the map
`g ↦ p g` reflects and preserves the order (hence is injective and lands in `X_{≥p f}`) and every
`x ≥ p f` is `p g` for some `g ≥ f`. -/
def IsUpwardStarIso {t : ℕ} {L : Fin t → Type} [∀ i, Field (L i)]
    {O : ∀ i, ValuationSubring (L i)} {X : Type} [PartialOrder X] (p : ProductFace O → X) : Prop :=
  ∀ f : ProductFace O,
    (∀ g g' : ProductFace O, f ≤ g → f ≤ g' → (p g ≤ p g' ↔ g ≤ g')) ∧
    ∀ x : X, p f ≤ x → ∃ g : ProductFace O, f ≤ g ∧ p g = x

end GoodQLTC.Supplement


