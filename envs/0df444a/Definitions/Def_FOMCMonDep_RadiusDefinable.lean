-- Prove2me | Definitions.Def_FOMCMonDep_RadiusDefinable
-- name    : FOMCMonDep_RadiusDefinable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:19.219017+00:00
-- url     : https://prove2.me/theorems/0ba9ac6a-72d1-4082-9c4c-ff588d3fb2a6
-- title:
--   Definable induced partial graphs and radius-$r$ definable construction sequences (Definitions 4.5, 4.6)
-- statement:
--   Let $G$ be a graph with vertex set $V$ and $H$ a partial graph with vertex set $W\subseteq V$.
--
--   1. (**Definition 4.5**) $H$ is **definable in $G$ by formulas of quantifier rank $q$ using $c$ unary predicates and $w$ parameters** if there are an expansion $G^+$ of $G$ by $c$ unary predicates and a set $S\subseteq V$ with $|S|\le w$ such that for every relation symbol $Q$ of $H$, of arity $k$, some formula $\varphi_Q(x_1,\dots,x_k)$ of quantifier rank $q$ with parameters from $S$ satisfies
--   $$G^+\models\varphi_Q(\bar v)\iff \bar v\in W^k\ \text{and}\ H\models Q(\bar v)\qquad\text{for all }\bar v\in V^k.$$
--   2. The **induced partial graph** $H[W]$ has vertex set $W$, the edges and non-edges of $H$ inside $W$, and the parts of $H$ intersected with $W$.
--   3. (**Definition 4.6**) A construction sequence $G_1,\dots,G_\lambda$ of $G$ is **radius-$r$ definable with $c$ unary predicates, $s$ parameters and quantifier rank $q_0$** if for all $t\in[\lambda-1]$ and $v\in V$ the induced partial graph $G_t[\mathrm{Ball}^{G_{t+1}}_r(v)]$ is definable in $G$ by formulas of quantifier rank $q_0$ using $c$ unary predicates and $s$ parameters. The expansion and the parameters may depend on $t$ and $v$.
--
--   This is how Part II transfers the type bound of Part I, which counts types in $G$, to the partial graphs of a construction sequence.
--
--   **Formalization Note** "Of quantifier rank $q$" is read as "of quantifier rank at most $q$". The relation symbols are $E$, $N$ and every color; a color with no vertex in $W$ is defined by $\bot$. All formulas share one parameter set.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §4.1.2, p.14 (PDF 16); §3, p.12 (PDF 14)

import Mathlib
import Definitions.Def_MonDepMW_coloredGraph
import Definitions.Def_FOMCMonDep_ConstructionSeq

set_option autoImplicit false

open FirstOrder FirstOrder.Language

namespace FOMCMonDep

/-- **Definable induced partial graphs (Definition 4.5).** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §4.1.2, p.14 (PDF 16):
"Let G be a graph with vertex set V and let H be a partial graph with vertex set W ⊆ V. For q, c, w ∈ N, we say that
H is definable in G by formulas of quantifier rank q using c unary predicates and w parameters, if there is an
expansion G⁺ of G by c unary predicates and a set S ⊆ V(G) of parameters with |S| ⩽ w, such that for every relation
symbol Q of H (when viewed as a relational structure) of arity k there is some formula φ_Q(x1, . . . , xk) of
quantifier rank q with parameters from S such that G⁺ |= φ_Q(v̄) ⇐⇒ v̄ ∈ W^k and H |= Q(v̄) for all v̄ ∈ V^k."
`DefinesInduced G H W q c w` says this of the induced partial graph `H[W]` (§3, p.12: "the partial graph with vertex
set W, edges E(H) ∩ (W choose 2), non-edges N(H) ∩ (W choose 2), and partition {P ∩ W : P ∈ 𝒫} − {∅}"), whose
relations are those of `H` restricted to `W`: `H[W] |= Q(v̄)` iff `v̄ ∈ W^k` and `H |= Q(v̄)`.

**Formalization Note.** "of quantifier rank q" is read as "of quantifier rank at most q" (a formula of smaller rank
pads to rank exactly `q` with a dummy quantifier, so the readings agree for `q ≥ 1`). The expansion is the published
`MonDepMW.coloredStructure G col` with `c` predicates (they need not be disjoint), and the parameters `S` are free
variables `Sum.inr s` assigned `s` itself. Every relation symbol of `PGLang` is covered: `E`, `N` and every color
`c ∈ ℕ` (a color with no vertex in `W` is defined by `⊥`), all with one shared set `S` of parameters. -/
def DefinesInduced {n : ℕ} (G : SimpleGraph (Fin n)) (H : PartialGraph n) (W : Set (Fin n)) (q c w : ℕ) : Prop :=
  ∃ (col : Fin c → Set (Fin n)) (S : Finset (Fin n)), S.card ≤ w ∧
    ∀ (l : ℕ) (R : PGLang.Relations l),
      ∃ φ : (MonDepMW.coloredGraph c).Formula (Fin l ⊕ (S : Set (Fin n))), qrank φ ≤ q ∧
        ∀ v : Fin l → Fin n,
          (@Formula.Realize _ _ (MonDepMW.coloredStructure G col) _ φ (Sum.elim v Subtype.val) ↔
            ((∀ i, v i ∈ W) ∧ @Structure.RelMap PGLang _ H.toStructure l R v))

/-- **Radius-`r` definable construction sequences (Definition 4.6).** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §4.1.2, p.14
(PDF 16): "Let G be a graph and r, c, s, q0 ∈ N. A construction sequence G1, . . . , Gλ of G is radius-r definable with
c unary predicates, s parameters, and quantifier rank q0 if for all t ∈ [λ − 1] and v ∈ V(G), the induced partial
graph Gt[Ball^{Gt+1}_r(v)] is definable in G by formulas of quantifier rank q0 using c unary predicates and s
parameters. Note that the expansion and the parameters may depend on t and v."

**Formalization Note.** `c` and `s` are bounds: definable with fewer predicates or parameters implies definable with
`c` and `s` (unused predicates, the same parameters). -/
def RadiusDefinable {n : ℕ} (G : SimpleGraph (Fin n)) (seq : List Step) (r c s q₀ : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 (seqLength seq - 1), ∀ v : Fin n,
    DefinesInduced G (stage (n := n) seq t) ((stage (n := n) seq (t + 1)).ball r v) q₀ c s

end FOMCMonDep


