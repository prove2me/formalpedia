-- Prove2me | Definitions.Def_HDXNbhdPCP_Main_Complex
-- name    : HDXNbhdPCP_Main_Complex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:58:06.885996+00:00
-- url     : https://prove2.me/theorems/94980cfa-2026-43df-a654-00e014470b48
-- title:
--   Weighted coloured complexes, bipartite expanders and samplers, regrouping, colour merging, links, path and cycle complexes, $\varepsilon$-products, 1-coboundary expansion (Definitions 2.1–2.14)
-- statement:
--   All distributions are finitely supported. A **finite distribution** on a type $\alpha$ is a finite support $S\subseteq\alpha$ with weights $w$; it is a probability distribution of full support when $w>0$ on $S$ and $\sum_{a\in S}w(a)=1$. Probabilities, expectations, push-forwards $f_*D$, conditionings $D\mid E$ and uniform distributions are the usual finite sums.
--
--   1. **Bipartite graphs (p. 12).** A weighted bipartite graph $G=(L,R,E,\pi_G)$ is a distribution $\pi_G$ on $L\times R$; $E$ is its support and $L$, $R$ are the supports of its marginals (so no vertex is isolated). Its **averaging operator** is $(Af)(r)=\mathbb E_{\ell\sim r}[f(\ell)]$ (conditional law of $\ell$ given $r$).
--   2. **Expanders (Definition 2.1).** $G$ is a $\lambda$-expander if $\|Af\|_2\le\lambda\|f\|_2$ for every $f:L\to\mathbb R$ with $\mathbb E_{\ell\sim L}f(\ell)=0$, norms taken in $L^2$ of the marginals.
--   3. **Samplers (Definition 2.3).** $G$ is an $\eta$-sampler if for every $f:L\to[0,1]$ and every $\varepsilon>0$,
--   $$\Pr_{r\sim R}\Big[\big|\mathbb E_{\ell\sim r}f(\ell)-\mathbb E_{\ell\sim L}f(\ell)\big|>\varepsilon\Big]\le\frac{\eta}{\varepsilon^2}\,\mathbb E_{\ell\sim L}f(\ell).$$
--   A bipartite graph is $D$-regular if every vertex has exactly $D$ neighbours in $E$, and balanced if $|L|=|R|$.
--   4. **Coloured complexes (Definition 2.5).** For a finite colour set $I$ and vertex types $V_i$, an $I$-coloured complex $K$ is a distribution $\pi_K$ of full support on a finite set of facets $x=(x_i)_{i\in I}$; $K[i]=\{x_i\}$ is the vertex set of colour $i$, $K[B]=\{x_B\}$ the $B$-faces with the push-forward distribution.
--   5. **Regrouping (Definition 2.6).** For $\phi:J\to 2^I$, $K[\phi]$ has facets $(x_{\phi(j)})_{j\in J}$ with the push-forward distribution. $K[i,j]$ and $K[S,T]$ are the bipartite graphs of pairs $(x_i,x_j)$ and $(x_S,x_T)$.
--   6. **Links (Definition 2.8).** For a face $\sigma=y_J$, the link $K_\sigma$ is the conditional law of $x$ given $x_J=\sigma$ (the coordinates in $J$ are then constant; the link proper is the restriction to $I\setminus J$).
--   7. **Colour merging (Definition 2.7).** For distinct $a,b$, $K\langle a\sqcup b\rangle$ has colours $(I\setminus\{a,b\})\cup\{\star\}$, $K\langle a\sqcup b\rangle[\star]=K[a]\sqcup K[b]$, and facet law that of $(x_R,x_c)$ for $x\sim K$ and an independent uniform $c\in\{a,b\}$.
--   8. **Path and cycle complexes (Definitions 2.9, 2.10).** An $[n]$-coloured $K$ is a path complex if for all $J$, faces $\sigma\in K[J]$ and $a<b$ outside $J$ separated by some $c\in J$, the $a$- and $b$-coordinates of $K_\sigma$ are independent. A $\mathbb Z_n$-coloured $K$ ($n\ge3$) is a cycle complex if every vertex link $K_v$, $v\in K[i]$, recoloured by $j\mapsto i+j$ ($j\in[n-1]$), is a path complex.
--   9. **$\varepsilon$-products (Definition 2.11).** $K$ is an $\varepsilon$-product if every $K_\sigma[i,j]$ ($J\subseteq I$, $\sigma\in K[J]$, distinct $i,j\notin J$, including $J=\emptyset$) is an $\varepsilon$-expander.
--   10. **1-coboundary expansion (Definition 2.14).** For a group $\Gamma$ and $\beta>0$, $K$ has 1-coboundary expansion at least $\beta$ over $\Gamma$ if every antisymmetric edge labelling $f$ ($f(v,u)=f(u,v)^{-1}$) admits a vertex labelling $g$ with
--   $$\Pr_{\{u,v\}\sim K(1)}\big[f(u,v)\ne g(v)g(u)^{-1}\big]\le\frac1\beta\Pr_{\{u,v,w\}\sim K(2)}\big[f(v,w)f(u,v)f(w,u)\ne1\big],$$
--   where $K(1)$, $K(2)$ choose a uniform set of two (three) colours and then a face. This is stated for a colour restriction $K[C]$.
--   11. **Isomorphism.** Two complexes on the same colours are isomorphic if colour-preserving maps, injective on vertex sets, carry one facet distribution onto the other.
--
--   These objects are the substrate of every statement of the mission; they are reusable for any work on high-dimensional expanders and agreement testing.
--
--   **Formalization Note** A complex is a finitely supported weight function `FinDist` on the product of the vertex types; full support is the hypothesis `IsProb`. Links are conditioned facet distributions with the conditioned coordinates kept, so the two-colour graphs $K_\sigma[i,j]$ are `pairGraph (condFace K J y) i j`. The range $\varepsilon\in[0,1]$ of Definition 2.11 is not part of `IsProduct`; the theorems state it as a hypothesis where the paper assumes a product. Edges and triangles are sampled through uniformly random *ordered* colour tuples, which induces the paper's distributions on unordered faces; the events are orientation-independent. The merged colour $\star$ is `none` in `Option {i // i ≠ a ∧ i ≠ b}`.
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), pp. 12-15, Definitions 2.1, 2.3, 2.5-2.11, 2.14 (and the paragraph on bipartite graphs, p. 12)

import Mathlib

/-!
# Weighted colored complexes and their expansion (Dikstein–Dinur–Hopkins–Singer, §2.1–2.3)

* `FinDist α` : a finitely supported weight function on `α`; `IsProb` says it is a probability
  distribution of full support on its finite support.
* `BipGraph L R` : a weighted bipartite graph `(L, R, E, π_G)` (Definition-paragraph p. 12), its
  averaging operator, bipartite `λ`-expanders (Definition 2.1), `η`-samplers (Definition 2.3).
* `ColoredComplex I V` : an `I`-colored complex given by its facet distribution
  (Definition 2.5); faces, regrouping (Definition 2.6), colour merging (Definition 2.7),
  links (Definition 2.8, encoded by conditioning), path and cycle complexes (Definitions 2.9,
  2.10), `ε`-products (Definition 2.11), 1-coboundary expansion (Definition 2.14).
-/

namespace HDXNbhdPCP.Main

open Classical

noncomputable section

/-- A finitely supported weight function: a finite support `supp` and a weight `w`
(the values of `w` outside `supp` are never used). -/
structure FinDist (α : Type) where
  /-- the finite support -/
  supp : Finset α
  /-- the weight of each point -/
  w : α → ℝ

namespace FinDist

variable {α β : Type}

/-- `D` is a probability distribution with full support on `D.supp`. -/
def IsProb (D : FinDist α) : Prop :=
  (∀ a ∈ D.supp, 0 < D.w a) ∧ ∑ a ∈ D.supp, D.w a = 1

/-- The probability of an event. -/
def prob (D : FinDist α) (E : α → Prop) : ℝ := ∑ a ∈ D.supp.filter E, D.w a

/-- The expectation of a real function. -/
def expect (D : FinDist α) (f : α → ℝ) : ℝ := ∑ a ∈ D.supp, D.w a * f a

/-- The weight extended by zero outside the support. -/
def wt (D : FinDist α) (a : α) : ℝ := if a ∈ D.supp then D.w a else 0

/-- Push-forward along a map. -/
def map (D : FinDist α) (f : α → β) : FinDist β where
  supp := D.supp.image f
  w b := ∑ a ∈ D.supp.filter (fun a => f a = b), D.w a

/-- Conditioning on an event. -/
def cond (D : FinDist α) (E : α → Prop) : FinDist α where
  supp := D.supp.filter E
  w a := D.w a / D.prob E

/-- The uniform distribution on a finite set. -/
def uniform (s : Finset α) : FinDist α where
  supp := s
  w _ := 1 / (s.card : ℝ)

/-- The equal-weight mixture of the distributions `D i`, `i ∈ s`. -/
def mixUniform {ι : Type} (s : Finset ι) (D : ι → FinDist α) : FinDist α where
  supp := s.biUnion (fun i => (D i).supp)
  w a := (1 / (s.card : ℝ)) * ∑ i ∈ s, (D i).wt a

/-- Two weight functions are the same distribution: same support, same weights on it. -/
def Same (D₁ D₂ : FinDist α) : Prop :=
  D₁.supp = D₂.supp ∧ ∀ a ∈ D₁.supp, D₁.w a = D₂.w a

end FinDist

/-- A weighted bipartite graph `G = (L, R, E, π_G)`: the edge distribution `π_G` on `L × R`;
`E` is its support and the vertex sets are the supports of its two marginals (so no vertex is
isolated). -/
abbrev BipGraph (L R : Type) := FinDist (L × R)

namespace BipGraph

variable {L R : Type}

/-- The left marginal (the distribution on `L`). -/
def left (G : BipGraph L R) : FinDist L := FinDist.map G Prod.fst

/-- The right marginal (the distribution on `R`). -/
def right (G : BipGraph L R) : FinDist R := FinDist.map G Prod.snd

/-- The averaging operator `(A f)(r) = E_{ℓ ∼ r} [f(ℓ)]` (neighbourhood distribution of `r`). -/
def avg (G : BipGraph L R) (f : L → ℝ) (r : R) : ℝ :=
  (∑ e ∈ G.supp.filter (fun e => e.2 = r), G.w e * f e.1) / G.right.w r

/-- Definition 2.1: `G` is a `λ`-expander if `‖A f‖₂ ≤ λ ‖f‖₂` for every mean-zero `f : L → ℝ`,
norms taken with respect to the marginals. -/
def IsExpander (G : BipGraph L R) (lam : ℝ) : Prop :=
  ∀ f : L → ℝ, G.left.expect f = 0 →
    Real.sqrt (G.right.expect (fun r => G.avg f r ^ 2)) ≤
      lam * Real.sqrt (G.left.expect (fun l => f l ^ 2))

/-- Definition 2.3: `G` is an `η`-sampler if for every `f : L → [0,1]` and every `ε > 0`,
`P_{r ∈ R}[|E_{ℓ ∼ r} f(ℓ) − E_{ℓ ∈ L} f(ℓ)| > ε] ≤ (η / ε²) E_{ℓ ∈ L} f(ℓ)`. -/
def IsSampler (G : BipGraph L R) (eta : ℝ) : Prop :=
  ∀ f : L → ℝ, (∀ l, 0 ≤ f l ∧ f l ≤ 1) → ∀ ε : ℝ, 0 < ε →
    G.right.prob (fun r => |G.avg f r - G.left.expect f| > ε) ≤ eta / ε ^ 2 * G.left.expect f

/-- Every vertex (on either side) has exactly `D` neighbours in the edge set. -/
def IsRegular (G : BipGraph L R) (D : ℕ) : Prop :=
  (∀ l ∈ G.left.supp, (G.supp.filter (fun e => e.1 = l)).card = D) ∧
    (∀ r ∈ G.right.supp, (G.supp.filter (fun e => e.2 = r)).card = D)

/-- The two sides have the same number of vertices. -/
def IsBalanced (G : BipGraph L R) : Prop := G.left.supp.card = G.right.supp.card

end BipGraph

/-- An `I`-colored complex (Definition 2.5), given by its facet distribution `π_K` on
`∏_{i ∈ I} V i`: the facets are the support, the vertices of colour `i` are the `i`-coordinates of
facets. It is a weighted complex in the sense of the paper when `IsProb` holds. -/
abbrev ColoredComplex (I : Type) (V : I → Type) := FinDist ((i : I) → V i)

namespace ColoredComplex

variable {I : Type} {V : I → Type}

/-- The vertex set `K[i]`. -/
def vertices (K : ColoredComplex I V) (i : I) : Finset (V i) := K.supp.image (fun x => x i)

/-- The restriction `x_B` of a facet to the colours in `B`. -/
def restrictTo (B : Finset I) (x : (i : I) → V i) : (i : B) → V i := fun i => x i

/-- The face distribution of `K[B]` (Definition 2.5). -/
def faceDist (K : ColoredComplex I V) (B : Finset I) : FinDist ((i : B) → V i) :=
  FinDist.map K (restrictTo B)

/-- Regrouping `K[ϕ]` (Definition 2.6): colour `j` of the new complex has as vertices the
`ϕ j`-faces of `K`. -/
def regroup {J : Type} (K : ColoredComplex I V) (ϕ : J → Finset I) :
    ColoredComplex J (fun j => (i : ϕ j) → V i) :=
  FinDist.map K (fun x j => restrictTo (ϕ j) x)

/-- The two-colour bipartite graph `K[i, j]`. -/
def pairGraph (K : ColoredComplex I V) (i j : I) : BipGraph (V i) (V j) :=
  FinDist.map K (fun x => (x i, x j))

/-- The bipartite graph `K[S, T]` between `S`-faces and `T`-faces. -/
def setPairGraph (K : ColoredComplex I V) (S T : Finset I) :
    BipGraph ((i : S) → V i) ((i : T) → V i) :=
  FinDist.map K (fun x => (restrictTo S x, restrictTo T x))

/-- The link of the face `y_J` (Definition 2.8), encoded as the facet distribution conditioned on
`x_J = y_J` (the coordinates in `J` are then constant; the link is its restriction to `I \ J`). -/
def condFace (K : ColoredComplex I V) (J : Finset I) (y : (i : I) → V i) :
    ColoredComplex I V :=
  FinDist.cond K (fun x => ∀ i ∈ J, x i = y i)

/-- The set `{x_c : x a facet satisfying P}`, e.g. the vertex set of colour `c` of a link. -/
def vertexSetGiven (K : ColoredComplex I V) (P : ((i : I) → V i) → Prop) (c : I) :
    Finset (V c) :=
  (K.supp.filter P).image (fun x => x c)

/-- Definition 2.11: `K` is an `ε`-product if for every `J ⊆ I`, every face `σ ∈ K[J]` and every
pair of distinct colours `i, j ∉ J`, the graph `K_σ[i, j]` is an `ε`-expander (`J = ∅` included). -/
def IsProduct (K : ColoredComplex I V) (eps : ℝ) : Prop :=
  ∀ (J : Finset I) (y : (i : I) → V i), y ∈ K.supp → ∀ i j : I, i ∉ J → j ∉ J → i ≠ j →
    ((K.condFace J y).pairGraph i j).IsExpander eps

/-- The colours of the merged complex `K⟨a ⊔ b⟩`: `none` is the new colour `⋆`, `some i` an
unmerged colour `i ∈ R = I \ {a, b}`. -/
abbrev MColor (I : Type) (a b : I) := Option {i : I // i ≠ a ∧ i ≠ b}

/-- The vertex types of `K⟨a ⊔ b⟩`: `K⟨a ⊔ b⟩[⋆] = K[a] ⊔ K[b]`. -/
def MV (V : I → Type) (a b : I) : MColor I a b → Type
  | none => V a ⊕ V b
  | some i => V i.1

/-- The facet `(x_R, x_c)` of `K⟨a ⊔ b⟩` (`c = a` when the coin is `true`, `c = b` otherwise). -/
def mergeFacet (a b : I) (x : (i : I) → V i) (coin : Bool) :
    (m : MColor I a b) → MV V a b m
  | none => if coin then Sum.inl (x a) else Sum.inr (x b)
  | some i => x i.1

/-- Definition 2.7: the colour-merged complex `K⟨a ⊔ b⟩`: the distribution of `(x_R, x_c)` for
`x ∼ K` and an independent uniform `c ∈ {a, b}`. -/
def merge (K : ColoredComplex I V) (a b : I) : ColoredComplex (MColor I a b) (MV V a b) :=
  FinDist.mixUniform (Finset.univ : Finset Bool)
    (fun coin => FinDist.map K (fun x => mergeFacet a b x coin))

/-- Definition 2.9 (colours `[n]`, written `Fin n` with its order): `K` is a path complex if for
every `J`, every face `σ ∈ K[J]` and every `a < b` outside `J` with some `c ∈ J`, `a < c < b`,
the colours `a` and `b` are independent in `K_σ`: `π_{K_σ[a,b]} = π_{K_σ[a]} ⊗ π_{K_σ[b]}`. -/
def IsPathComplex {n : ℕ} {W : Fin n → Type} (K : ColoredComplex (Fin n) W) : Prop :=
  ∀ (J : Finset (Fin n)) (y : (i : Fin n) → W i), y ∈ K.supp →
    ∀ a b : Fin n, a ∉ J → b ∉ J → a < b → (∃ c ∈ J, a < c ∧ c < b) →
      ∀ (u : W a) (v : W b),
        ((K.condFace J y).pairGraph a b).wt (u, v) =
          ((K.condFace J y).pairGraph a b).left.wt u *
            ((K.condFace J y).pairGraph a b).right.wt v

/-- The colour `i + j` of `ℤ_n` (`Fin n` with addition mod `n`) for the 0-based index `j` of the
paper's `j + 1 ∈ [n − 1]`. -/
def shiftColor {n : ℕ} (i : Fin n) (j : Fin (n - 1)) : Fin n :=
  ⟨(i.1 + (j.1 + 1)) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.2)⟩

/-- Definition 2.10: a `ℤ_n`-coloured complex (`n ≥ 3`) is a cycle complex if for every colour `i`
and vertex `v ∈ K[i]` the link `K_v`, recoloured by `ϕ_i(j) = i + j` (`j ∈ [n − 1]`), is a path
complex. -/
def IsCycleComplex {n : ℕ} {W : Fin n → Type} (K : ColoredComplex (Fin n) W) : Prop :=
  3 ≤ n ∧ ∀ (i : Fin n) (y : (j : Fin n) → W j), y ∈ K.supp →
    IsPathComplex (W := fun j => W (shiftColor i j))
      (FinDist.map (K.condFace {i} y) (fun x j => x (shiftColor i j)))

/-- A coloured vertex: a colour together with a vertex of that colour. -/
abbrev CVert (V : I → Type) := (i : I) × V i

/-- The distribution on (ordered) edges of the colour restriction `K[C]`: a uniform ordered pair
of distinct colours of `C`, then an edge of that colour pair. Its image on unordered edges is the
induced distribution of `K[C](1)` (a uniform 2-subset of colours, then a face). -/
def edgeDistOn (K : ColoredComplex I V) (C : Finset I) : FinDist (CVert V × CVert V) :=
  FinDist.mixUniform ((C ×ˢ C).filter (fun p => p.1 ≠ p.2))
    (fun p => FinDist.map K (fun x => (⟨p.1, x p.1⟩, ⟨p.2, x p.2⟩)))

/-- The distribution on (ordered) triangles of `K[C]`: a uniform ordered triple of distinct
colours of `C`, then a face of those colours (image on unordered triangles: `K[C](2)`). -/
def triDistOn (K : ColoredComplex I V) (C : Finset I) :
    FinDist (CVert V × CVert V × CVert V) :=
  FinDist.mixUniform ((C ×ˢ C ×ˢ C).filter (fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2))
    (fun t => FinDist.map K (fun x => (⟨t.1, x t.1⟩, ⟨t.2.1, x t.2.1⟩, ⟨t.2.2, x t.2.2⟩)))

/-- Definition 2.14: the colour restriction `K[C]` has 1-coboundary expansion at least `β > 0` over
the group `Γ`: every antisymmetric edge labelling `f` has a vertex labelling `g` with
`P_{u,v}[f(u,v) ≠ g(v) g(u)⁻¹] ≤ (1/β) P_{u,v,w}[f(v,w) f(u,v) f(w,u) ≠ 1]`. -/
def HasCobExpOn (K : ColoredComplex I V) (C : Finset I) (Γ : Type) [Group Γ] (β : ℝ) : Prop :=
  0 < β ∧
    ∀ f : CVert V → CVert V → Γ,
      (∀ e ∈ (K.edgeDistOn C).supp, f e.2 e.1 = (f e.1 e.2)⁻¹) →
      ∃ g : CVert V → Γ,
        (K.edgeDistOn C).prob (fun e => f e.1 e.2 ≠ g e.2 * (g e.1)⁻¹) ≤
          1 / β * (K.triDistOn C).prob
            (fun t => f t.2.1 t.2.2 * f t.1 t.2.1 * f t.2.2 t.1 ≠ 1)

/-- Two complexes on the same colours are isomorphic: colour-preserving maps, injective on each
vertex set, carrying the facet distribution of `K` onto that of `K'`. -/
def IsIsomorphic {W : I → Type} (K : ColoredComplex I V) (K' : ColoredComplex I W) : Prop :=
  ∃ f : (i : I) → V i → W i, (∀ i, Set.InjOn (f i) (K.vertices i : Set (V i))) ∧
    FinDist.Same (FinDist.map K (fun x i => f i (x i))) K'

end ColoredComplex

end

end HDXNbhdPCP.Main


