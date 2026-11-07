-- Prove2me | Definitions.Def_MetricMSO_Sat
-- name    : MetricMSO_Sat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:17.327922+00:00
-- url     : https://prove2.me/theorems/3b826dbd-a9f0-4f28-8b16-243eaecd0d2e
-- title:
--   Satisfaction $G,\alpha\models\varphi$
-- statement:
--   The satisfaction relation of a formula on an instance under an assignment $\alpha$ of the four sorts of variables. Vertex variables range over $V(G)$, edge variables over $E(G)$, vertex-set variables over subsets of $V(G)$ and edge-set variables over subsets of $E(G)$. The atom $\mathrm{card}_{a,\ell}(X)$ holds iff $\ell\ge2$, $a<\ell$ and $|X|\equiv a\pmod\ell$. The metric atoms are read in the original graph $G$, also when the surrounding formula uses edge variables.
--
--   **Formalization Note** An assignment is four lists indexed by de Bruijn level, and a quantifier appends the new value to its list. An atom with a variable level outside its list, or a predicate index outside the instance, is false; a modulo atom with constants outside the range $\ell\ge2$, $0\le a<\ell$ is false.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §2.7, p.16 (PDF 18); §2.8, pp.18–19 (PDF 20–21)

import Mathlib
import Definitions.Def_MetricMSO_Instance
import Definitions.Def_MetricMSO_Formula
import Definitions.Def_MetricMSO_IsShortestPathSet
import Definitions.Def_MetricMSO_EqGC

namespace MetricMSO

/-- **An assignment of the four variable sorts** on a graph with vertex set `Fin n`: the values of
the vertex, edge, vertex-set and edge-set variables, listed by de Bruijn level (the variable of
level `i` of a sort is the `i`-th entry of the list of that sort). -/
structure Env (n : ℕ) where
  v : List (Fin n)
  e : List (Sym2 (Fin n))
  s : List (Finset (Fin n))
  es : List (Finset (Sym2 (Fin n)))

/-- **Satisfaction `G, α ⊨ φ`** of a CMSO2[SP, EqGC] formula on an instance under an assignment.

Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), §2.7, p.16 (PDF 18)
(FO, MSO1, MSO2 on the incidence structure I(G), the atoms card_{a,ℓ}(X) "expressing that
|X| ≡ a (mod ℓ), where ℓ ≥ 2 and 0 ≤ a < ℓ"); §2.8, p.18 (PDF 20), Definitions 2.10, 2.11, 2.15
("We always measure distances in the original graph G, also when we interpret the surrounding
formula on the incidence structure I(G)").

* Vertex variables range over `V(G) = Fin n`, edge variables over `E(G)`, vertex-set variables over
  subsets of `V(G)`, edge-set variables over subsets of `E(G)`.
* `adj x y` is adjacency in `G`, `inc e x` says that `x` is an endpoint of `e`, `vpred j x` and
  `epred j e` are membership in the `j`-th input predicate.
* `cardV a l X` holds iff `2 ≤ ℓ`, `a < ℓ` and `|X| ≡ a (mod ℓ)`; a modulo atom with constants
  outside this range is false.
* `sp P s t` is `IsShortestPathSet G P s t`, and `eqgc C x y u v` is `EqGC G C x y u v`.
* A quantifier appends the new value to the list of its sort (de Bruijn levels).

**Formalization Note** An atom that mentions a variable level outside its list, or a predicate
index `j ≥ q`, is false. -/
def Sat (I : Instance) : Env I.n → Formula → Prop
  | _, .ff => False
  | ρ, .adj x y => ∃ a b, ρ.v[x]? = some a ∧ ρ.v[y]? = some b ∧ I.G.Adj a b
  | ρ, .eqV x y => ∃ a b, ρ.v[x]? = some a ∧ ρ.v[y]? = some b ∧ a = b
  | ρ, .eqE e f => ∃ a b, ρ.e[e]? = some a ∧ ρ.e[f]? = some b ∧ a = b
  | ρ, .inc e x => ∃ d a, ρ.e[e]? = some d ∧ ρ.v[x]? = some a ∧ a ∈ d
  | ρ, .memV x X => ∃ a S, ρ.v[x]? = some a ∧ ρ.s[X]? = some S ∧ a ∈ S
  | ρ, .memE e Y => ∃ d S, ρ.e[e]? = some d ∧ ρ.es[Y]? = some S ∧ d ∈ S
  | ρ, .vpred j x => ∃ (h : j < I.q) (a : Fin I.n), ρ.v[x]? = some a ∧ a ∈ I.vpred ⟨j, h⟩
  | ρ, .epred j e => ∃ (h : j < I.q') (d : Sym2 (Fin I.n)), ρ.e[e]? = some d ∧
      d ∈ I.epred ⟨j, h⟩
  | ρ, .cardV a l X => ∃ S, ρ.s[X]? = some S ∧ 2 ≤ l ∧ a < l ∧ S.card % l = a
  | ρ, .cardE a l Y => ∃ S, ρ.es[Y]? = some S ∧ 2 ≤ l ∧ a < l ∧ S.card % l = a
  | ρ, .sp P s t => ∃ S a b, ρ.s[P]? = some S ∧ ρ.v[s]? = some a ∧ ρ.v[t]? = some b ∧
      IsShortestPathSet I.G S a b
  | ρ, .eqgc C x y u v => ∃ S a b c d, ρ.s[C]? = some S ∧ ρ.v[x]? = some a ∧
      ρ.v[y]? = some b ∧ ρ.v[u]? = some c ∧ ρ.v[v]? = some d ∧ EqGC I.G S a b c d
  | ρ, .neg φ => ¬ Sat I ρ φ
  | ρ, .and φ ψ => Sat I ρ φ ∧ Sat I ρ ψ
  | ρ, .exV φ => ∃ a : Fin I.n, Sat I { ρ with v := ρ.v ++ [a] } φ
  | ρ, .exE φ => ∃ d : Sym2 (Fin I.n), d ∈ I.G.edgeSet ∧ Sat I { ρ with e := ρ.e ++ [d] } φ
  | ρ, .exVS φ => ∃ S : Finset (Fin I.n), Sat I { ρ with s := ρ.s ++ [S] } φ
  | ρ, .exES φ => ∃ S : Finset (Sym2 (Fin I.n)), (∀ d ∈ S, d ∈ I.G.edgeSet) ∧
      Sat I { ρ with es := ρ.es ++ [S] } φ

end MetricMSO


