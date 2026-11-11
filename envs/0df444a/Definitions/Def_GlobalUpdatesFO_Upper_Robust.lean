-- Prove2me | Definitions.Def_GlobalUpdatesFO_Upper_Robust
-- name    : GlobalUpdatesFO_Upper_Robust
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:21:14.454205+00:00
-- url     : https://prove2.me/theorems/173e4e96-5dbc-46f9-b33f-2c14b3a50027
-- title:
--   k-common and k-noble elements, k-robust sets, k-closures, (tight) k-robust decompositions, prefixes, the preorder ≼^k_A and the first-order index µ_q
-- statement:
--   Fix $k$ and a $\Sigma$-structure $A$. An element $v$ is **$k$-common** if some set $S \subseteq U(A)$ with $|S| = k$ satisfies $\mathrm{tp}^k(A, v) = \mathrm{tp}^k(A, u)$ for all $u \in S$ ($v \in S$ allowed); otherwise $v$ is a **$k$-noble**. A set $K \subseteq U(A)$ is **$k$-robust** if the flattening $A^K$ has no $k$-nobles. A **$k$-closure** of $X$ is an inclusion-wise minimal $k$-robust superset of $X$; the $k$-closure of $A$ is that of $\emptyset$.
--
--   A **decomposition** $\mathcal F = (F, \mathrm{bag})$ of $A$ is a rooted forest $F$ with a nonempty bag for every node such that $U(A)$ is the disjoint union of the bags; $\mathrm{bag}^{-1}(u)$ is the node whose bag contains $u$. With $\mathcal F_{\le t}$ ($\mathcal F_{\ge t}$) the union of the bags of the ancestors (descendants) of $t$, $t$ included, and $\mathcal F_{<t} = \mathcal F_{\le t} \setminus \mathrm{bag}(t)$, the **residual substructure** is
--   $$A^{\mathcal F}_t = A^{\mathcal F_{<t}}\bigl[\mathcal F_{\ge t}\bigr].$$
--   $\mathcal F$ is a **$k$-robust decomposition** if every edge $uv$ of $G(A)$ joins ancestor-related nodes $\mathrm{bag}^{-1}(u), \mathrm{bag}^{-1}(v)$ and every $\mathrm{bag}(t)$ is $k$-robust in $A^{\mathcal F}_t$. A node $t$ is **tight** if $G(A^{\mathcal F}_t)$ is connected and $\mathrm{bag}(t)$ is the $k$-closure of $A^{\mathcal F}_t$; $\mathcal F$ is **tight** if all its nodes are. The **depth** of $\mathcal F$ is the height of $F$. A set $X$ is a **prefix** of $\mathcal F$ if it is the union of the bags of an ancestor-closed set of nodes. The preorder $u \preccurlyeq^k_A v$ holds when $\mathrm{bag}^{-1}(u)$ is an ancestor of (or equal to) $\mathrm{bag}^{-1}(v)$ in the tight $k$-robust decomposition of $A$.
--
--   The **first-order index** is
--   $$\mu_q(A) = \min\{|U(A')| : A' \text{ a finite } \Sigma\text{-structure with } A' \equiv_q A\},$$
--   with no treedepth restriction on $A'$.
--
--   **Formalization Note** A decomposition is a rooted forest (`SNPTreedepth.RootedForest`, parent function and depth) on a node type $N$ with a surjective map $\mathrm{bag}^{-1} : U \to N$; the bags are its fibres. The ancestor relation is reflexive. $X$ is a prefix iff with every $u \in X$ it contains every $v$ whose bag is an ancestor of the bag of $u$. $\preccurlyeq^k_A$ is defined through *some* tight $k$-robust decomposition, which is unique up to renaming nodes whenever $k \ge k_{4.11}$ (Lemma 4.11). In $\mu_q$ the candidate structures are taken on $\{0,\dots,m-1\}$, which loses nothing since full types are invariant under isomorphism.
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), pp. 26–27, §4.1–4.2; p. 31–32, §4.3; p. 15 (prefix); p. 41, §4.5

import Mathlib
import Definitions.Def_SNPTreedepth_treedepth
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula
import Definitions.Def_GlobalUpdatesFO_Upper_Flattening

set_option autoImplicit false

namespace GlobalUpdatesFO.Upper

noncomputable section

open Classical

variable {σ : Signature} {U : Type*}

/-- `v` is **`k`-common** in `A` (Korhonen, Sokołowski, *On efficient global updates in first-order
logic*, STOC 2027 submission, §4.1, p. 26): there is a set `S ⊆ U(A)` with `|S| = k` such that
`tp^k(A, v) = tp^k(A, u)` for all `u ∈ S` (`v ∈ S` is allowed). -/
def IsCommon (k : ℕ) (A : Structure σ U) (v : U) : Prop :=
  ∃ S : Finset U, S.card = k ∧ ∀ u ∈ S, tp k A (fun _ : Fin 1 => v) = tp k A (fun _ : Fin 1 => u)

/-- `v` is a **`k`-noble** of `A` (§4.1, p. 26): it is not `k`-common. -/
def IsNoble (k : ℕ) (A : Structure σ U) (v : U) : Prop :=
  ¬ IsCommon k A v

/-- `K ⊆ U(A)` is **`k`-robust** (§4.2, p. 27): the flattening `A^K` has no `k`-nobles. -/
def IsRobust (k : ℕ) (A : Structure σ U) (K : Finset U) : Prop :=
  ∀ v, IsCommon k (flattenAt A K) v

/-- `Y` is a **`k`-closure** of `X` (§4.2, p. 27): an inclusion-wise minimal `k`-robust superset of
`X`. The `k`-closure of `A` is the `k`-closure of `∅`. -/
def IsClosure (k : ℕ) (A : Structure σ U) (X Y : Finset U) : Prop :=
  X ⊆ Y ∧ IsRobust k A Y ∧ ∀ Y' : Finset U, X ⊆ Y' → Y' ⊆ Y → IsRobust k A Y' → Y' = Y

/-- A **decomposition** `F = (F, bag)` of a structure on `U` (§4.3, p. 31): a rooted forest on the
node set `N` and the map `bag⁻¹ : U → N` sending each element to the node whose bag contains it. Bags
are the fibres of `bag⁻¹`; they are nonempty (surjectivity) and `U` is their disjoint union. The
forest is `SNPTreedepth.RootedForest` (parent function and depth, a root has depth `1`). -/
structure Decomp (U : Type*) (N : Type*) where
  /-- the rooted forest `F` -/
  forest : SNPTreedepth.RootedForest N
  /-- `bag⁻¹`: the node whose bag contains a given element -/
  bagOf : U → N
  /-- every bag is nonempty -/
  surj : Function.Surjective bagOf

namespace Decomp

variable {N : Type*}

/-- `bag(t)`. -/
def bag (F : Decomp U N) (t : N) : Set U := {u | F.bagOf u = t}

/-- `F_{≤t}`: the union of the bags of the ancestors of `t` (including `t`). -/
def le (F : Decomp U N) (t : N) : Set U := {u | F.forest.IsAncestor (F.bagOf u) t}

/-- `F_{<t} = F_{≤t} \ bag(t)`. -/
def lt (F : Decomp U N) (t : N) : Set U := F.le t \ F.bag t

/-- `F_{≥t}`: the union of the bags of the descendants of `t` (including `t`). -/
def ge (F : Decomp U N) (t : N) : Set U := {u | F.forest.IsAncestor t (F.bagOf u)}

/-- A set `X ⊆ U(A)` is a **prefix** of `F` (§4.3, p. 31): `X` is the union of the bags of an
ancestor-closed set of nodes; equivalently, with every element `u ∈ X` it contains every element
whose bag is an ancestor of (or equal to) the bag of `u`. -/
def IsPrefix (F : Decomp U N) (X : Set U) : Prop :=
  ∀ u ∈ X, ∀ v : U, F.forest.IsAncestor (F.bagOf v) (F.bagOf u) → v ∈ X

/-- The **depth** of `F` (§4.3, p. 31): the height of the forest (maximum number of nodes on a
root-to-leaf path; `0` for the empty forest). -/
def depth [Fintype N] (F : Decomp U N) : ℕ := F.forest.height

/-- The **residual substructure** `A^F_t = A^{F_{<t}}[F_{≥t}]` (§4.3, p. 31): flatten `A` at
`F_{<t}`, then take the substructure induced by `F_{≥t}`. -/
def residual [Fintype U] (A : Structure σ U) (F : Decomp U N) (t : N) :
    Structure (flatSig σ (F.lt t).toFinset.card)
      ↥{x : {u : U // u ∉ Set.range (enumOf (F.lt t).toFinset)} | x.val ∈ F.ge t} :=
  (flattenAt A (F.lt t).toFinset).induced {x | x.val ∈ F.ge t}

/-- `bag(t)` as a subset of the universe of the residual substructure `A^F_t`. -/
def bagIn [Fintype U] (F : Decomp U N) (t : N) :
    Finset ↥{x : {u : U // u ∉ Set.range (enumOf (F.lt t).toFinset)} | x.val ∈ F.ge t} :=
  Set.toFinset {x | F.bagOf x.val.val = t}

/-- `F` is a **`k`-robust decomposition** of `A` (§4.3, p. 31):
* elimination forest property: for every edge `uv` of `G(A)`, `bag⁻¹(u)` and `bag⁻¹(v)` are in the
  ancestor–descendant relationship;
* robustness: for every node `t`, `bag(t)` is a `k`-robust set in `A^F_t`. -/
def IsRobustDecomp [Fintype U] (k : ℕ) (A : Structure σ U) (F : Decomp U N) : Prop :=
  (∀ u v : U, A.gaifman.Adj u v →
      F.forest.IsAncestor (F.bagOf u) (F.bagOf v) ∨ F.forest.IsAncestor (F.bagOf v) (F.bagOf u)) ∧
  ∀ t : N, IsRobust k (residual A F t) (bagIn F t)

/-- A node `t` is **tight** (§4.3, p. 31): `G(A^F_t)` is connected and `bag(t)` is the `k`-closure of
`A^F_t`. -/
def IsTightNode [Fintype U] (k : ℕ) (A : Structure σ U) (F : Decomp U N) (t : N) : Prop :=
  (residual A F t).gaifman.Connected ∧ IsClosure k (residual A F t) ∅ (bagIn F t)

/-- `F` is a **tight `k`-robust decomposition** of `A` (§4.3, p. 31): a `k`-robust decomposition all
of whose nodes are tight. -/
def IsTight [Fintype U] (k : ℕ) (A : Structure σ U) (F : Decomp U N) : Prop :=
  IsRobustDecomp k A F ∧ ∀ t : N, IsTightNode k A F t

end Decomp

/-- The preorder **`u ≼^k_A v`** (§4.3, p. 32): `bag⁻¹(u)` is an ancestor of `bag⁻¹(v)` (equality
allowed) in the tight `k`-robust decomposition of `A`.

**Formalization Note** Stated as: in some tight `k`-robust decomposition of `A`; tight
decompositions are unique up to renaming nodes when they exist (Lemma 4.11), so this is the
paper's relation. -/
def Prec [Fintype U] (k : ℕ) (A : Structure σ U) (u v : U) : Prop :=
  ∃ (N : Type) (_ : Fintype N) (F : Decomp U N),
    Decomp.IsTight k A F ∧ F.forest.IsAncestor (F.bagOf u) (F.bagOf v)

/-- The **first-order index** `µ_q(A) = min{|U(A′)| : A′ a Σ-structure with A′ ≡_q A}` (§4.5,
p. 41), the minimum over all finite `Σ`-structures with no treedepth restriction; `A′ ≡_q A` means
equal full sentence `q`-types. A structure on `m` elements is taken on `Fin m` (every finite
`Σ`-structure is isomorphic to one of these, and full types are invariant under isomorphism). -/
def foIndex (q : ℕ) (A : Structure σ U) : ℕ :=
  sInf {m : ℕ | ∃ A' : Structure σ (Fin m), tp0 q A' = tp0 q A}

end

end GlobalUpdatesFO.Upper


