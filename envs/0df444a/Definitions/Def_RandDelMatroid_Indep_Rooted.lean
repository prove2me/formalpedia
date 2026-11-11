-- Prove2me | Definitions.Def_RandDelMatroid_Indep_Rooted
-- name    : RandDelMatroid_Indep_Rooted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T18:31:07.897004+00:00
-- url     : https://prove2.me/theorems/bad1fa5f-c632-4fb1-949f-13104bc75f5f
-- title:
--   Rooted decomposition trees, R-goodness, node absorption and admissible paths (§5.1–5.3, Definition 13)
-- statement:
--   Root the clean unordered decomposition tree $T$ at a node $r$. For a node $u$, $Q_u$ is $u$ together with its descendants, and $S_u$ is the boundary set of the edge joining $u$ to its parent ($S_r=\emptyset$).
--
--   **R-goodness (Definition 13).** Let $R\subseteq E$. The node $u$ is **$R$-good** if
--
--   1. no circuit of $M_{Q_u}$ avoiding $S_u$ is contained in $R$, and
--   2. for every $s\in S_u$, every completion $P$ of $s$ in $Q_u$ with $P\subseteq R$ has $|P|<g/2$.
--
--   **Absorption at a node (§5.2).** For every child $v$ attached through a 2- or 3-sum and every $s\in S_v$ a minimum-cardinality completion $P_{Q_v,s}$ of $s$ in $Q_v$ is chosen. $(\hat M_u,w_u)$ is an absorption (Lemma 11) of all these children with these completions, in which the parent boundary $S_u$ is kept with weight $0$, so that $w_u(\hat D)=|D^+\setminus S_u|$.
--
--   **Graphic nodes (§5.3).** If $M_u=M(G_u)$, let $H_u=G_u-S_u$. For an edge $e$ of $H_u$ put $A_e=\{e\}$ if $e\in E_u\cap E$ and $A_e=P_{Q_v,e}$ if $e\in S_v$ for a child $v$, and $\ell_u(e)=|A_e|$. An edge set $F$ is **admissible** if $|F\cap S_v|\le1$ for every child $v$, and its length is $\ell_u(F)=\sum_{e\in F}\ell_u(e)$. A path is **simple** if it repeats no vertex.
--
--   **Formalization Note** Children, descendants and the parent are read off graph distances from the root: $v$ is a child of $u$ if they are adjacent and $d(r,v)=d(r,u)+1$; $Q_u$ is the set of $w$ with $d(r,w)=d(r,u)+d(u,w)$. `IsNodeAbsorption` is `IsAbsorptionData` with $Z=S_u$ for the children with nonempty boundary, plus weight $0$ on $S_u$. `IsMinCompletionChoice` says `P s` is a minimum-cardinality completion for every child boundary element. A simple path is given by its edge set (`IsSimplePathEdges`: distinct vertices $x=x_0,\dots,x_n=y$ and edges $e_i$ joining $x_{i-1},x_i$); `edgeExpansion M P e` is $A_e$ (`{e}` when `e ∈ M.E`).
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), pp. 25–27, §5.1, Definition 13, §5.2, §5.3

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_Absorption

set_option autoImplicit false

namespace RandDelMatroid.Indep

open scoped NNReal

variable {β ι : Type}

/-- §5.1 (p. 25), tree rooted at `r`: `v` is a child of `u`. -/
def IsChild (T : SimpleGraph ι) (r u v : ι) : Prop :=
  T.Adj u v ∧ T.dist r v = T.dist r u + 1

open Classical in
/-- §5.1 (p. 25): `Q_u`, the node `u` together with all its descendants (the nodes `w` such that
`u` lies on the path from `r` to `w`). -/
noncomputable def below (T : SimpleGraph ι) [Fintype ι] (r u : ι) : Finset ι :=
  Finset.univ.filter (fun w => T.dist r w = T.dist r u + T.dist u w)

/-- §5.1 (p. 25): `S_u`, the boundary set on the edge joining `u` to its parent; `S_r = ∅` for the
root (which has no parent). -/
def parentBoundary (T : SimpleGraph ι) (Mn : ι → Matroid β) (r u : ι) : Set β :=
  {x | ∃ p, T.Adj u p ∧ T.dist r p + 1 = T.dist r u ∧ x ∈ edgeBoundary Mn u p}

/-- Definition 13 (p. 25): the node `u` is *R-good* (the event `G_u^R` holds):
1. no circuit of `M_{Q_u}` avoiding `S_u` is contained in `R`;
2. for every `s ∈ S_u`, every completion `P` of `s` in `Q_u` with `P ⊆ R` has `|P| < g/2`. -/
def IsRGood (T : SimpleGraph ι) [Fintype ι] (Mn : ι → Matroid β) (r : ι) (g : ℕ) (R : Set β)
    (u : ι) : Prop :=
  (∀ C : Set β, (subtreeMatroid T Mn (below T r u)).IsCircuit C →
      Disjoint C (parentBoundary T Mn r u) → ¬ C ⊆ R) ∧
    ∀ s ∈ parentBoundary T Mn r u, ∀ P : Set β,
      IsCompletion T Mn (below T r u) (parentBoundary T Mn r u) s P → P ⊆ R →
        (P.ncard : ℝ) < (g : ℝ) / 2

open Classical in
/-- §5.2 (p. 26): the children of `u` attached through a 2- or 3-sum (nonempty boundary). -/
noncomputable def sumChildren (T : SimpleGraph ι) [Fintype ι] (Mn : ι → Matroid β) (r u : ι) :
    Finset ι :=
  Finset.univ.filter (fun v => IsChild T r u v ∧ (edgeBoundary Mn u v).Nonempty)

/-- §5.2 (p. 26): `P` chooses, for every child `v` of `u` and every `s ∈ S_v`, a
minimum-cardinality completion `P s = P_{Q_v,s}` of `s` in `Q_v`. -/
def IsMinCompletionChoice (T : SimpleGraph ι) [Fintype ι] (Mn : ι → Matroid β) (r u : ι)
    (P : β → Set β) : Prop :=
  ∀ v, IsChild T r u v → ∀ s ∈ edgeBoundary Mn u v,
    IsMinCompletion T Mn (below T r v) (edgeBoundary Mn u v) s (P s)

/-- §5.2 (p. 26): `(M̂_u, w_u, corr)` is the absorption at `u` of all children attached through 2-
or 3-sums, with the chosen completions `P`: the properties of Lemma 11 hold, the parent boundary
`S_u` is kept in `Ê_u` with weight `0`, and the weight of `D̂` counts exactly the elements of `E` in
the expansion, `w_u(D̂) = |D⁺ \ S_u|`. -/
def IsNodeAbsorption (T : SimpleGraph ι) [Fintype ι] [DecidableEq ι] (Mn : ι → Matroid β)
    (r u : ι) (P : β → Set β) (Mh : Matroid (β ⊕ ℕ)) (w : β ⊕ ℕ → ℝ≥0)
    (corr : Set β → Set (β ⊕ ℕ)) : Prop :=
  IsAbsorptionData T Mn u (sumChildren T Mn r u) P (parentBoundary T Mn r u) Mh w corr ∧
    ∀ s ∈ parentBoundary T Mn r u, w (Sum.inl s) = 0

/-- §5.3 (p. 27): `A_e = {e}` if `e ∈ E_u ∩ E`, and `A_e = P_{Q_v,e}` if `e ∈ S_v` for a child `v`. -/
noncomputable def edgeExpansion (M : Matroid β) (P : β → Set β) (e : β) : Set β := by
  classical
  exact if e ∈ M.E then {e} else P e

/-- §5.3 (p. 27): `ℓ_u(F) = ∑_{e ∈ F} ℓ_u(e)` with `ℓ_u(e) = |A_e|`. -/
noncomputable def pathLength (M : Matroid β) (P : β → Set β) (F : Set β) : ℝ :=
  ∑ᶠ e ∈ F, ((edgeExpansion M P e).ncard : ℝ)

/-- §5.3 (p. 27): `F` is *admissible*: `|F ∩ S_v| ≤ 1` for every child `v` of `u`. -/
def IsAdmissible (T : SimpleGraph ι) (Mn : ι → Matroid β) (r u : ι) (F : Set β) : Prop :=
  ∀ v, IsChild T r u v → (F ∩ edgeBoundary Mn u v).ncard ≤ 1

/-- `F` is the edge set of a simple `x`–`y` path (no repeated vertices) in the multigraph with
endpoint map `ends`: vertices `x = x₀, x₁, …, xₙ = y`, pairwise distinct, and edges `e₁, …, eₙ`
with `eᵢ` joining `x_{i-1}` and `xᵢ`. -/
def IsSimplePathEdges {V : Type} (ends : β → Sym2 V) (x y : V) (F : Set β) : Prop :=
  ∃ (n : ℕ) (vs : Fin (n + 1) → V) (es : Fin n → β), Function.Injective vs ∧ vs 0 = x ∧
    vs (Fin.last n) = y ∧ (∀ i : Fin n, ends (es i) = s(vs i.castSucc, vs i.succ)) ∧
    F = Set.range es

end RandDelMatroid.Indep


