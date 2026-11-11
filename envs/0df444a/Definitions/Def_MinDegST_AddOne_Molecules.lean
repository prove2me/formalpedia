-- Prove2me | Definitions.Def_MinDegST_AddOne_Molecules
-- name    : MinDegST_AddOne_Molecules
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:52:24.356672+00:00
-- url     : https://prove2.me/theorems/14aa8969-9f19-4109-9228-1829b086c516
-- title:
--   Molecules, molecular and θ-molecular decompositions (Defs. 14.1, 14.2), reducible regions, junctions, augmenting chains (Def. 14.7)
-- statement:
--   Fix $G$, a forest $F$ of $G$ and a threshold $k$. For a forest edge $(x,y)$ the **normal molecule** $T^F_{x\leftarrow y}$ is the component of $x$ after deleting $(x,y)$ from $F$, with root $y$ outside it; a **special molecule** is a whole component of $F$ with a chosen root $r$ inside it.
--
--   **Definition 14.1.** A set $M$ of molecules is a **molecular decomposition** of $F$ if its molecules are pairwise node-disjoint and the root of every normal $M$-molecule lies in no $M$-molecule. A node is $M$-covered if it lies in an $M$-molecule, $M$-free otherwise, and **internal** if it is $M$-free and not the root of a normal $M$-molecule.
--
--   **Definition 14.2.** $M$ is a **$\theta$-molecular decomposition** if (1) the components of $F$ with at most $2\theta$ nodes are exactly the special $M$-molecules; (2) every special root is slack; (3) every normal $M$-molecule has at most $\theta$ nodes; (4) every normal molecule $T^F_{x\leftarrow y}\notin M$ containing an $M$-free node has at least $\theta+1$ nodes.
--
--   **Reducible regions (§14.2).** On a molecule $T$: start with every slack node of $T$ as a singleton region; while an edge $(x,y)\in E(G)$ joins two different regions, merge all regions meeting the forest path $P_{x,y}$ together with the nodes of that path into one region. The final regions over all $M$-molecules form $\mathcal R_M$. An $M$-covered node in no region is a **junction**; $v$ lies **below** $z$ if $v\ne z$ lies in an $M$-molecule $\mu$ and $z$ lies on the forest path from $v$ to the root of $\mu$.
--
--   **Definition 14.7.** $(w_0,z_1,w_1,\dots,w_{\ell-1},z_\ell)$, $\ell\ge1$, is an **augmenting chain** if (1) $w_0$ lies in the region containing the root of a special molecule; (2) for $1\le i\le\ell-1$: $(w_{i-1},z_i)\in E$, $z_i$ is the root of a normal molecule or a junction, and $w_i$ lies in a region below $z_i$; (3) $(w_{\ell-1},z_\ell)\in E$, $z_\ell$ is not in the region of $w_{\ell-1}$, and $z_\ell$ lies in a region or is slack.
--
--   **Formalization Note.** The region procedure is a relation: `RegionOutcome` holds for every final state reachable by merge steps (the paper treats the result as unique), and `IsRegionsOf G F k M 𝓡` says $\mathcal R$ is the union over $M$ of such final states. Inside a molecule the forest path between two of its nodes is the path of the molecule. Chains are stored as `ws = [w₀,…,w_{ℓ−1}]`, `zs = [z₁,…,z_ℓ]`; molecules and chains have integer encodings for algorithm outputs.
--
--   The θ-decomposition predicate records the four clauses without a built-in range restriction: Lemma 14.3 assumes 1 ≤ θ ≤ n, while §16 uses θ = ⌈10n/f⌉ even when it exceeds n. Foresthood and feasibility are separate hypotheses at every use.
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 36–38, Definitions 14.1, 14.2, §14.2, Definition 14.7

import Mathlib
import Definitions.Def_MinDegST_AddOne_Graph

open Classical

namespace MinDegST.AddOne

/-! # Molecules, (θ-)molecular decompositions, reducible regions, junctions, augmenting chains

Part III, §14 (pp. 36–38): Definitions 14.1, 14.2, the region procedure of §14.2 and
Definition 14.7. Throughout, `G` is the graph, `F` a forest of `G`, and `k` the degree threshold
(`k = Δ⋆` in the paper) that decides slack (`deg_F ≤ k`) and saturated (`deg_F = k + 1`) nodes. -/

variable {n : ℕ}

/-- A molecule of `F`: the normal molecule `T^F_{x←y}` of a forest edge `(x, y)` (root `y`,
outside the molecule), or the special molecule given by a component of `F` with a chosen root `r`
inside it. -/
inductive Molecule (n : ℕ) where
  | normal (x y : Fin n)
  | special (r : Fin n)
  deriving DecidableEq

/-- The molecule is a molecule of `F`: a normal molecule `T^F_{x←y}` needs `(x, y) ∈ E(F)`. -/
def Molecule.IsOf (F : SimpleGraph (Fin n)) : Molecule n → Prop
  | .normal x y => F.Adj x y
  | .special _ => True

/-- The root of a molecule: `y` for `T^F_{x←y}`, `r` for a special molecule. -/
def Molecule.root : Molecule n → Fin n
  | .normal _ y => y
  | .special r => r

/-- The node set of a molecule: `V(T^F_{x←y})` is the component of `x` after deleting the edge
`(x, y)` from `F`; a special molecule is the whole component of its root. -/
noncomputable def Molecule.verts (F : SimpleGraph (Fin n)) : Molecule n → Finset (Fin n)
  | .normal x y => Finset.univ.filter fun v => (F.deleteEdges {s(x, y)}).Reachable x v
  | .special r => Finset.univ.filter fun v => F.Reachable r v

/-- **Definition 14.1.** `M` is a molecular decomposition of `F`: its molecules are molecules of
`F`, pairwise vertex-disjoint, and the root of every normal `M`-molecule lies in no `M`-molecule. -/
def IsMolDecomp (F : SimpleGraph (Fin n)) (M : Finset (Molecule n)) : Prop :=
  (∀ μ ∈ M, μ.IsOf F) ∧
  (∀ μ ∈ M, ∀ ν ∈ M, μ ≠ ν → Disjoint (μ.verts F) (ν.verts F)) ∧
  (∀ x y, Molecule.normal x y ∈ M → ∀ ν ∈ M, y ∉ ν.verts F)

/-- `v` is `M`-covered: it lies in some `M`-molecule. -/
def Covered (F : SimpleGraph (Fin n)) (M : Finset (Molecule n)) (v : Fin n) : Prop :=
  ∃ μ ∈ M, v ∈ μ.verts F

/-- `v` is the root of some normal `M`-molecule. -/
def IsNormalRoot (M : Finset (Molecule n)) (v : Fin n) : Prop :=
  ∃ x, Molecule.normal x v ∈ M

/-- `v` is internal: `M`-free and not the root of any normal `M`-molecule. -/
def Internal (F : SimpleGraph (Fin n)) (M : Finset (Molecule n)) (v : Fin n) : Prop :=
  ¬ Covered F M v ∧ ¬ IsNormalRoot M v

/-- **Definition 14.2.** `M` is a `θ`-molecular decomposition of `F` (threshold `k`):
1. every component of `F` with at most `2θ` nodes is a special `M`-molecule, and no other
   component is;
2. the root of every special `M`-molecule is slack;
3. every normal `M`-molecule has at most `θ` nodes;
4. every normal molecule `T^F_{x←y}` of `F` that is not in `M` and contains an `M`-free node has
   at least `θ + 1` nodes. -/
def IsThetaDecomp (F : SimpleGraph (Fin n)) (k θ : ℕ) (M : Finset (Molecule n)) : Prop :=
  IsMolDecomp F M ∧
  (∀ v : Fin n, ((Molecule.special v).verts F).card ≤ 2 * θ →
      ∃ r, Molecule.special r ∈ M ∧ F.Reachable v r) ∧
  (∀ r, Molecule.special r ∈ M → ((Molecule.special r).verts F).card ≤ 2 * θ) ∧
  (∀ r, Molecule.special r ∈ M → Slack k F r) ∧
  (∀ x y, Molecule.normal x y ∈ M → ((Molecule.normal x y).verts F).card ≤ θ) ∧
  (∀ x y, F.Adj x y → Molecule.normal x y ∉ M →
      (∃ v ∈ (Molecule.normal x y).verts F, ¬ Covered F M v) →
      θ + 1 ≤ ((Molecule.normal x y).verts F).card)

/-- One merge step of the region procedure of §14.2: some edge `(x, y) ∈ E(G)` (forest or
non-forest, footnote 9) joins two different current regions `R₁ ∋ x`, `R₂ ∋ y`; all regions
meeting the forest path `P_{x,y}` are merged, together with every (bad) node of the path, into one
region. (Inside a molecule `T` the forest path between two of its nodes is the path of `T`.) -/
def RegionStep (G F : SimpleGraph (Fin n)) (𝓡 𝓡' : Finset (Finset (Fin n))) : Prop :=
  ∃ x y R₁ R₂, R₁ ∈ 𝓡 ∧ R₂ ∈ 𝓡 ∧ R₁ ≠ R₂ ∧ x ∈ R₁ ∧ y ∈ R₂ ∧ G.Adj x y ∧
    𝓡' = insert ((𝓡.filter fun R => (R ∩ pathVerts F x y).Nonempty).biUnion id ∪ pathVerts F x y)
      (𝓡.filter fun R => ¬ (R ∩ pathVerts F x y).Nonempty)

/-- Start of the region procedure on a molecule with node set `T`: every slack node of `T` is a
singleton region (the other nodes of `T` are bad). -/
noncomputable def regionInit (k : ℕ) (F : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (T.filter fun u => Slack k F u).image fun u => {u}

/-- `𝓡` is a final state of the region procedure of §14.2 run on the molecule with node set `T`:
reachable from the start by merge steps, and no merge step applies. -/
def RegionOutcome (G F : SimpleGraph (Fin n)) (k : ℕ) (T : Finset (Fin n))
    (𝓡 : Finset (Finset (Fin n))) : Prop :=
  Relation.ReflTransGen (RegionStep G F) (regionInit k F T) 𝓡 ∧ ¬ ∃ 𝓡', RegionStep G F 𝓡 𝓡'

/-- `𝓡` is the set `R_M` of all `M`-reducible regions: the union over the `M`-molecules of the final
states of the region procedure run on each of them. -/
def IsRegionsOf (G F : SimpleGraph (Fin n)) (k : ℕ) (M : Finset (Molecule n))
    (𝓡 : Finset (Finset (Fin n))) : Prop :=
  ∃ 𝓡μ : Molecule n → Finset (Finset (Fin n)),
    (∀ μ ∈ M, RegionOutcome G F k (μ.verts F) (𝓡μ μ)) ∧ 𝓡 = M.biUnion 𝓡μ

/-- `v` is covered by the region collection `𝓡`. -/
def RCovered (𝓡 : Finset (Finset (Fin n))) (v : Fin n) : Prop :=
  ∃ R ∈ 𝓡, v ∈ R

/-- A junction: an `M`-covered node lying in no region of `𝓡`. -/
def Junction (F : SimpleGraph (Fin n)) (M : Finset (Molecule n)) (𝓡 : Finset (Finset (Fin n)))
    (v : Fin n) : Prop :=
  Covered F M v ∧ ¬ RCovered 𝓡 v

/-- `v` lies below `z` in the rooted structure of the molecules: `v` is a node of an `M`-molecule
`μ`, `v ≠ z`, and `z` lies on the forest path from `v` to the root of `μ` (for the root `y` of a
normal molecule this says `v ∈ T^F_{x←y}`). -/
def Below (F : SimpleGraph (Fin n)) (M : Finset (Molecule n)) (v z : Fin n) : Prop :=
  ∃ μ ∈ M, v ∈ μ.verts F ∧ v ≠ z ∧ z ∈ pathVerts F v μ.root

/-- A chain `(w₀, z₁, w₁, z₂, …, w_{ℓ−1}, z_ℓ)`, stored as `ws = [w₀, …, w_{ℓ−1}]` and
`zs = [z₁, …, z_ℓ]`. -/
structure Chain (n : ℕ) where
  ws : List (Fin n)
  zs : List (Fin n)
  deriving DecidableEq

/-- **Definition 14.7 (augmenting chain)** with respect to `(G, F, k, M, 𝓡)`: `ℓ = |ws| = |zs| ≥ 1`
and
1. `w₀` lies in the region of `𝓡` containing the root of a special `M`-molecule;
2. for `1 ≤ i ≤ ℓ − 1`: (a) `(w_{i−1}, z_i) ∈ E`; (b) `z_i` is the root of a normal `M`-molecule or a
   junction; (c) `w_i` belongs to a region of `𝓡` below `z_i`;
3. `(w_{ℓ−1}, z_ℓ) ∈ E`, `z_ℓ` is not in the region containing `w_{ℓ−1}`, and `z_ℓ` lies in a region
   of `𝓡` or is slack.
(Index shift: `zs[i]` is `z_{i+1}`.) -/
def IsAugmentingChain (G F : SimpleGraph (Fin n)) (k : ℕ) (M : Finset (Molecule n))
    (𝓡 : Finset (Finset (Fin n))) (A : Chain n) : Prop :=
  1 ≤ A.ws.length ∧ A.ws.length = A.zs.length ∧
  (∀ w₀, A.ws[0]? = some w₀ → ∃ R ∈ 𝓡, w₀ ∈ R ∧ ∃ r, Molecule.special r ∈ M ∧ r ∈ R) ∧
  (∀ i w z w', A.ws[i]? = some w → A.zs[i]? = some z → A.ws[i + 1]? = some w' →
      G.Adj w z ∧ (IsNormalRoot M z ∨ Junction F M 𝓡 z) ∧
      ∃ R ∈ 𝓡, w' ∈ R ∧ Below F M w' z) ∧
  (∀ w z, A.ws.getLast? = some w → A.zs.getLast? = some z →
      G.Adj w z ∧ (∀ R ∈ 𝓡, w ∈ R → z ∉ R) ∧ (RCovered 𝓡 z ∨ Slack k F z))

/-- Encoding of a molecule as three integers: `[0, x, y]` for `T^F_{x←y}`, `[1, r, r]` for the
special molecule with root `r`. -/
def encMolecule : Molecule n → List ℤ
  | .normal x y => [0, (x.val : ℤ), (y.val : ℤ)]
  | .special r => [1, (r.val : ℤ), (r.val : ℤ)]

/-- Encoding of a list of molecules: `[number of molecules, molecule₁ (3 entries), …]`. -/
def encMolecules (l : List (Molecule n)) : List ℤ :=
  (l.length : ℤ) :: l.flatMap encMolecule

/-- Encoding of a chain: `[ℓ, w₀, …, w_{ℓ−1}, z₁, …, z_ℓ]`. -/
def encChain (A : Chain n) : List ℤ :=
  (A.ws.length : ℤ) :: (A.ws.map fun v => (v.val : ℤ)) ++ A.zs.map fun v => (v.val : ℤ)

/-- Encoding of a list of chains: `[number of chains, chain₁, chain₂, …]`. -/
def encChains (l : List (Chain n)) : List ℤ :=
  (l.length : ℤ) :: l.flatMap encChain

end MinDegST.AddOne


