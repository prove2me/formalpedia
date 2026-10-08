-- Prove2me | Definitions.Def_BoundedDegreeST_LowerUpper_Tokens
-- name    : BoundedDegreeST_LowerUpper_Tokens
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:50.42019+00:00
-- url     : https://prove2.me/theorems/61d1189c-f4ea-4a96-8b66-005f65a68e6e
-- title:
--   Tokens, excess, special supernodes, members, D(S) and special sets (Definition 5.5), pp. 667–669
-- statement:
--   Fix a feasible $x^*$ with support $E^*$, a laminar family $\mathcal L$ and a vertex set $T$. A vertex is **active** if some edge of $E^*$ is incident to it; it receives $\deg_{E^*}(v)$ tokens, and its **excess** is $\deg_{E^*}(v)-2[v\in T]$. The excess of a supernode is the sum of the excesses of its active vertices, and a supernode is **special** if its excess is exactly one.
--
--   In the forest of $\mathcal L$, $R$ is a **child** of $S$ if $S$ is the smallest member of $\mathcal L$ strictly containing $R$. The **members** of $S$ are its children together with the supernodes $C\subseteq S$ contained in no child of $S$; $D(S)$ is the set of edges of $E^*$ whose endpoints lie in two different members of $S$.
--
--   **Definition 5.5.** A set $S\neq V$ is **special** if
--   1. $|\delta(S)|=3$, counted in $E^*$;
--   2. $x^*(\delta(S))=1$ or $x^*(\delta(S))=2$;
--   3. $\chi_{\delta(S)}$ lies in the linear span, in $\mathbb R^{E^*}$, of the vectors $\chi_{E(R)}$ for $R\in\mathcal L$ with $R\subseteq S$ and $\chi_{\delta(v)}$ for $v\in S\cap T$.
--
--   A member is **special** if it is a special supernode or a special set. Finally, the **surplus** of $S$ is
--
--   $$
--   \sum_{v\in S}\deg_{E^*}(v)\;-\;2\,|T\cap S|\;-\;2\,\bigl|\{R\in\mathcal L: R\subsetneq S\}\bigr|,
--   $$
--
--   the number of tokens of the vertices of $S$ left after two are reserved for every vertex of $T\cap S$ and every set of $\mathcal L$ strictly inside $S$.
--
--   These notions are the vocabulary of the counting argument of §5.1.
--
--   **Formalization Note** The paper contracts a supernode with one active vertex into a single vertex as a proof device (p. 668); no contraction is built in here: supernodes are the components of $F$ in the original graph, and their excess sums over their active vertices. "Descendants (including possibly $\chi_{E(S)}$)" is read as the members of $\mathcal L$ contained in $S$, $S$ included.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, pp. 667–669: tokens and excess (p. 668), special supernodes (p. 668), Definition 5.5 (p. 668), members, special members and D(S) (p. 669); forest of a laminar family (p. 667)

import Definitions.Def_BoundedDegreeST_LowerUpper_LP

namespace BoundedDegreeST.LowerUpper

/-- A vertex is active if some edge of the support `E*` is incident to it. -/
def Active {V : Type*} (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) (v : V) : Prop :=
  0 < degree (support E x) v

/-- Excess tokens of a vertex: its `deg_{E*}(v)` tokens minus the two tokens a
vertex of `T` needs. -/
noncomputable def vertexExcess {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) (T : Finset V) (v : V) : ℤ :=
  (degree (support E x) v : ℤ) - (if v ∈ T then 2 else 0)

/-- Excess tokens of a supernode `C` (p. 668): the sum of the excess tokens of
the active vertices in `C`. -/
noncomputable def supernodeExcess {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) (T : Finset V) (C : Finset V) : ℤ := by
  classical
  exact ∑ v ∈ C.filter (fun v => Active E x v), vertexExcess E x T v

/-- A special supernode (p. 668): a supernode whose excess is exactly one. -/
def IsSpecialSupernode {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (F : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (T : Finset V) (C : Finset V) : Prop :=
  C ∈ supernodes F ∧ supernodeExcess E x T C = 1

/-- `R` is a child of `S` in the forest of the laminar family `𝓛` (p. 667):
`S` is the smallest member of `𝓛` strictly containing `R`. -/
def IsChild {V : Type*} [DecidableEq V] (L : Finset (Finset V)) (S R : Finset V) : Prop :=
  R ∈ L ∧ R ⊂ S ∧ ∀ R' ∈ L, R ⊂ R' → ¬ R' ⊂ S

/-- The children of `S` in the forest of `𝓛`. -/
noncomputable def children {V : Type*} [DecidableEq V]
    (L : Finset (Finset V)) (S : Finset V) : Finset (Finset V) := by
  classical
  exact L.filter (fun R => IsChild L S R)

/-- The members of `S` (p. 669): its children in the forest of `𝓛`, together with
the supernodes `C ⊆ S` that are contained in no child of `S`. -/
noncomputable def members {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Sym2 V)) (L : Finset (Finset V)) (S : Finset V) :
    Finset (Finset V) := by
  classical
  exact children L S ∪
    (supernodes F).filter (fun C => C ⊆ S ∧ ∀ R ∈ children L S, ¬ C ⊆ R)

/-- `D(S)` (p. 669): the edges of the support `E*` whose two endpoints lie in
two different members of `S`. -/
noncomputable def crossing {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (F : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact (support E x).filter (fun e =>
    ∃ R₁ ∈ members F L S, ∃ R₂ ∈ members F L S, R₁ ≠ R₂ ∧
      ∃ u ∈ R₁, ∃ w ∈ R₂, e = s(u, w))

/-- Definition 5.5 (p. 668): a set `S ≠ V` is special if
1. `|δ(S)| = 3` (in the support `E*`);
2. `x*(δ(S)) = 1` or `x*(δ(S)) = 2`;
3. `χ_{δ(S)}` is a linear combination, in `ℝ^{E*}`, of the vectors `χ_{E(R)}`
   for the members `R ∈ 𝓛` with `R ⊆ S` (its descendants, possibly `S` itself)
   and the vectors `χ_{δ(v)}` for `v ∈ S ∩ T`. -/
def IsSpecialSet {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (T : Finset V) (S : Finset V) : Prop :=
  S ≠ Finset.univ ∧
  (cut (support E x) S).card = 3 ∧
  (BoundedDegreeST.PlusOne.edgeSum x (cut E S) = 1 ∨ BoundedDegreeST.PlusOne.edgeSum x (cut E S) = 2) ∧
  indicatorOnSupport E x (cut E S) ∈ Submodule.span ℝ
    ((fun R => indicatorOnSupport E x (internal E R)) '' {R | R ∈ L ∧ R ⊆ S} ∪
     (fun v => indicatorOnSupport E x (cut E {v})) '' {v | v ∈ S ∧ v ∈ T})

/-- A special member `R` of a set (p. 669): `R` is a special supernode or a
special set. -/
def IsSpecialMember {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (F : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (T : Finset V) (R : Finset V) : Prop :=
  IsSpecialSupernode E F x T R ∨ IsSpecialSet E x L T R

/-- The tokens of the vertices of `S` left after giving two to every vertex of
`T ∩ S` and two to every member of `𝓛` strictly inside `S`. Lemma 5.6's token
distribution exists exactly when this is at least the root's share. -/
noncomputable def surplus {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (T : Finset V) (S : Finset V) : ℤ :=
  (∑ v ∈ S, (degree (support E x) v : ℤ)) - 2 * ((T ∩ S).card : ℤ) -
    2 * ((L.filter (fun R => R ⊂ S)).card : ℤ)

end BoundedDegreeST.LowerUpper


