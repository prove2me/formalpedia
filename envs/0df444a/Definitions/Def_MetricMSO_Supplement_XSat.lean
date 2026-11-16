-- Prove2me | Definitions.Def_MetricMSO_Supplement_XSat
-- name    : MetricMSO_Supplement_XSat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:54:05.093771+00:00
-- url     : https://prove2.me/theorems/23f84b46-580a-41b6-9982-52118c72937b
-- title:
--   Semantics of the metric atoms: Dist, EqDist, Close, NearLab, Sep, Cover
-- statement:
--   Let $G$ be a finite simple graph with unary input predicates $L_1,\dots,L_q$, let $\eta$ be a valuation of the numerical parameter symbols and $\alpha$ an assignment of the variables. Write $d_G(u,v)\in\mathbb Z_{\ge0}\cup\{\infty\}$ for the distance, with $d_G(u,v)=\infty$ for vertices in different components, and $d_G(v,A)=\min_{a\in A}d_G(v,a)$ with $\min\emptyset=\infty$. The atoms are interpreted as in §2.8:
--
--   1. $\mathrm{Dist}(u,v,\delta)\iff d_G(u,v)\ge\eta(\delta)$;
--   2. $\mathrm{EqDist}(x,y,u,v)\iff d_G(x,y)=d_G(u,v)<\infty$;
--   3. $\mathrm{Close}(x,u,v)\iff d_G(x,u)<d_G(x,v)$ in $\mathbb Z_{\ge0}\cup\{\infty\}$, so a finite distance is smaller than $\infty$ and $\infty<\infty$ is false;
--   4. $\mathrm{NearLab}_i(v;S)\iff \exists u\in S\cap L_i:\ d_G(v,u)=d_G(v,S)$, false when $S=\emptyset$.
--
--   Separation and covering are predicates on vertex sets:
--
--   $$\mathrm{Sep}_d(X,Y)\iff \forall x\in X\ \forall y\in Y\ (x\ne y\Rightarrow d_G(x,y)\ge d),\qquad \mathrm{Cover}_r(U,Y)\iff \forall u\in U\ \exists y\in Y\ d_G(u,y)\le r.$$
--
--   Thus $\mathrm{Sep}$ ignores equal vertices and does not force disjointness, and $\mathrm{Cover}_r(U,\emptyset)$ holds exactly when $U=\emptyset$. The target set of a covering atom is $V(G)$ or one input predicate $L_j$. Distances are always measured in the original graph $G$, also when the surrounding formula is read on the incidence structure.
--
--   **Formalization Note** Distances are Mathlib's `SimpleGraph.edist` in $\mathbb N_\infty$. An atom whose variable, label index or symbol index is out of range is false; a target $L_j$ with $j\ge q$ is the empty set. The embedding of the published formulas agrees with the published semantics `MetricMSO.Sat` by definition.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c5863…), §2.1, p.12 (PDF 14); Definitions 2.12–2.14, pp.18–19 (PDF 20–21)

import Mathlib
import Definitions.Def_MetricMSO_Sat
import Definitions.Def_MetricMSO_Supplement_XFormula

set_option autoImplicit false

namespace MetricMSO.Supplement

open MetricMSO

/-- **Distance from a vertex to a set**, `d_G(v, A) := min_{a ∈ A} d_G(v, a)` with `min ∅ = ∞`
(§2.1, p.12 (PDF 14): "where we take the minimum of an empty set to be ∞").

**Formalization Note** Distances are Mathlib's `SimpleGraph.edist`, valued in `ℕ∞`: the length of
a shortest walk, and `⊤ = ∞` for vertices in different components (§2.1, p.12: "if they lie in
different components, we put d_G(u, v) = ∞"). -/
noncomputable def distSet {V : Type} (G : SimpleGraph V) (v : V) (A : Finset V) : ℕ∞ :=
  ⨅ a ∈ A, G.edist v a

/-- **Satisfaction of an extended formula** `(G, η), α ⊨ φ` on an instance `I`, under the valuation
`η` of the numerical parameter symbols (symbol `δ` has the value `η[δ]`) and the assignment `α`.

Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), §2.8, pp.18–19
(PDF 20–21):
* `base φ` is the published `MetricMSO.Sat` in the same assignment;
* Definition 2.12: "Dist(u, v, δ) ⇐⇒ d_G(u, v) ≥ η(δ)";
* Definition 2.13: "NearLab_i(v; S) ⇐⇒ ∃u ∈ S ∩ L_i : d_G(v, u) = d_G(v, S)" ("We interpret
  every such atom as false when S = ∅");
* Definition 2.14: "EqDist(x, y, u, v) as requiring d_G(x, y) = d_G(u, v) < ∞", and
  "Close(x, u, v) … d_G(x, u) < d_G(x, v), using the usual order on Z≥0 ∪ {∞}. Thus a finite
  distance is smaller than ∞, while ∞ < ∞ is false";
* "We always measure distances in the original graph G, also when we interpret the surrounding
  formula on the incidence structure I(G)" (§2.8, p.18).

**Formalization Note** As in `MetricMSO.Sat`, an atom with a variable level outside its list, a
label index `i ≥ q`, or a symbol index outside `η`, is false. Label `i` is the `i`-th vertex input
predicate (`0`-based; the paper's `L_{i+1}`). -/
def XSat (I : Instance) (η : List ℕ) : Env I.n → XFormula → Prop
  | ρ, .base φ => Sat I ρ φ
  | ρ, .dist x y δ => ∃ a b d, ρ.v[x]? = some a ∧ ρ.v[y]? = some b ∧ η[δ]? = some d ∧
      (d : ℕ∞) ≤ I.G.edist a b
  | ρ, .eqDist x y u v => ∃ a b c d, ρ.v[x]? = some a ∧ ρ.v[y]? = some b ∧ ρ.v[u]? = some c ∧
      ρ.v[v]? = some d ∧ I.G.edist a b = I.G.edist c d ∧ I.G.edist a b ≠ ⊤
  | ρ, .close x u v => ∃ a b c, ρ.v[x]? = some a ∧ ρ.v[u]? = some b ∧ ρ.v[v]? = some c ∧
      I.G.edist a b < I.G.edist a c
  | ρ, .nearLab i x S => ∃ (h : i < I.q) (a : Fin I.n) (T : Finset (Fin I.n)),
      ρ.v[x]? = some a ∧ ρ.s[S]? = some T ∧
      ∃ u ∈ T, u ∈ I.vpred ⟨i, h⟩ ∧ I.G.edist a u = distSet I.G a T
  | ρ, .neg φ => ¬ XSat I η ρ φ
  | ρ, .and φ ψ => XSat I η ρ φ ∧ XSat I η ρ ψ
  | ρ, .or φ ψ => XSat I η ρ φ ∨ XSat I η ρ ψ
  | ρ, .exV φ => ∃ a : Fin I.n, XSat I η { ρ with v := ρ.v ++ [a] } φ
  | ρ, .exE φ => ∃ d : Sym2 (Fin I.n), d ∈ I.G.edgeSet ∧ XSat I η { ρ with e := ρ.e ++ [d] } φ
  | ρ, .exVS φ => ∃ S : Finset (Fin I.n), XSat I η { ρ with s := ρ.s ++ [S] } φ
  | ρ, .exES φ => ∃ S : Finset (Sym2 (Fin I.n)), (∀ d ∈ S, d ∈ I.G.edgeSet) ∧
      XSat I η { ρ with es := ρ.es ++ [S] } φ

/-- The empty assignment (no variable of any sort), used for sentences. -/
def Env.empty (n : ℕ) : Env n := ⟨[], [], [], []⟩

/-- The embedding of `MetricMSO.Formula` agrees with the published semantics. -/
theorem xsat_base (I : Instance) (η : List ℕ) (ρ : Env I.n) (φ : Formula) :
    XSat I η ρ (.base φ) ↔ Sat I ρ φ := Iff.rfl

/-- **Separation** `Sep_d(X, Y)` (Definition 2.12, p.18 (PDF 20)): "d_G(x, y) ≥ η(δ) for every
x ∈ X and y ∈ Y with x ≠ y. We omit equal vertices even when X and Y are different variables, so
the atom does not require the sets to be disjoint". -/
def SepHolds {V : Type} (G : SimpleGraph V) (d : ℕ) (X Y : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, x ≠ y → (d : ℕ∞) ≤ G.edist x y

/-- **Covering** `Cover_r(U, Y)` (Definition 2.12, p.18 (PDF 20)): "every u ∈ U has a vertex
y ∈ Y with d_G(u, y) ≤ η(ρ)". In particular `Cover_r(U, ∅)` holds exactly when `U = ∅`
(p.19). -/
def CoverHolds {V : Type} (G : SimpleGraph V) (r : ℕ) (U Y : Finset V) : Prop :=
  ∀ u ∈ U, ∃ y ∈ Y, G.edist u y ≤ r

/-- **The target set of a covering atom** (§1, p.7; Definition 6.1): `none` is `V(G)`, `some j` is
the `j`-th unary input predicate `L_{j+1}`.

**Formalization Note** An index `j ≥ q` names no predicate and gives the empty set, as an
out-of-range predicate atom of `MetricMSO.Sat` is false. -/
def targetSet (I : Instance) : Option ℕ → Finset (Fin I.n)
  | none => Finset.univ
  | some j => if h : j < I.q then I.vpred ⟨j, h⟩ else ∅

end MetricMSO.Supplement


