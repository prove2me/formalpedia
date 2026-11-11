-- Prove2me | Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Graph
-- name    : FullRankSmallSetQLTC_IndependentChecks_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:55.162915+00:00
-- url     : https://prove2.me/theorems/178b3dee-abbe-4b45-947e-1818d0d2d7e4
-- title:
--   Bipartite graphs with group actions, two-sided losslessness and orbit matrices
-- statement:
--   A finite **bipartite graph** on $L\sqcup R$ is a relation $\ell\sim r$; its **binary adjacency map** $\mathbb F_2^L\to\mathbb F_2^R$ is the $R\times L$ matrix with entry $1$ exactly on edges. For $S\subseteq L$, $N(S)\subseteq R$ is its neighbourhood (and symmetrically).
--
--   1. The graph is $(\Delta_L,\Delta_R)$-**biregular** if every left vertex has $\Delta_L$ neighbours and every right vertex $\Delta_R$.
--   2. **Definition 3.2.** A $(\Delta_L,\Delta_R)$-biregular graph is **two-sided $(\alpha,\varepsilon)$-lossless** if
--   $$|N(S)|\ge(1-\varepsilon)\Delta_L|S|\ (S\subseteq L,\ |S|\le\alpha|L|),\qquad |N(T)|\ge(1-\varepsilon)\Delta_R|T|\ (T\subseteq R,\ |T|\le\alpha|R|).$$
--   No restriction on $\alpha,\varepsilon$ is built in.
--   3. A group $G$ acting on $L$ and $R$ (separately, so preserving the two classes) acts **freely** if $gv=v$ only for $g=1$, and **preserves the edges** if $g\ell\sim gr\iff\ell\sim r$.
--   4. **Orbit matrix** (§3.2). $[A]:\mathbb F_2^{L/G}\to\mathbb F_2^{R/G}$ is the adjacency map of the quotient graph $\Gamma/G$, whose vertices are the vertex orbits and whose edges are the edge orbits: its $(\rho,\lambda)$ entry is the number of edge orbits joining the vertex orbits $\lambda$ and $\rho$, modulo $2$. A general helper counts orbits of edges of any $G$-set with endpoint maps.
--   5. Vertex sets $G\times S$ with the left-translation action $k(g,s)=(kg,s)$.
--
--   **Formalization Note** The losslessness predicate includes the biregularity with the stated degrees, as in Definition 3.2. Orbit counts use representatives of orbits (`Quotient.out`); for equivariant edge data the count does not depend on them.
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Definition 3.2 (p. 13), §3.2 (p. 14), Assumption 3.1 (p. 12) (printed page = PDF page)

import Mathlib

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open MulAction

/-! # Finite bipartite graphs, group actions, losslessness and orbit matrices

A bipartite graph on `L ⊔ R` is a relation `adj : L → R → Prop` (a simple graph: an edge is a
pair `(ℓ, r)` with `adj ℓ r`). Its binary adjacency map `𝔽₂^L → 𝔽₂^R` is the matrix
`adjMatrix adj : Matrix R L 𝔽₂`. A group `G` acts on the two vertex classes separately (so the
action preserves the classes). -/

section Basic

variable {L R : Type*}

/-- An action of `G` on `X` is free: `g • x = x` only for `g = 1`. -/
def IsFreeAction (G X : Type*) [Group G] [MulAction G X] : Prop :=
  ∀ (g : G) (x : X), g • x = x → g = 1

/-- The action of `G` on `L` and `R` preserves the edges of `adj`. -/
def IsInvariantRel (G : Type*) [Group G] [MulAction G L] [MulAction G R]
    (adj : L → R → Prop) : Prop :=
  ∀ (g : G) (ℓ : L) (r : R), adj (g • ℓ) (g • r) ↔ adj ℓ r

variable [Fintype L] [Fintype R] (adj : L → R → Prop) [DecidableRel adj]

/-- The binary adjacency map `𝔽₂^L → 𝔽₂^R` of the bipartite graph, as a matrix with rows `R`
and columns `L`: the `(r, ℓ)` entry is `1` iff `ℓ ∼ r`. -/
def adjMatrix : Matrix R L (ZMod 2) :=
  Matrix.of fun r ℓ => if adj ℓ r then 1 else 0

/-- `N(S) ⊆ R` for `S ⊆ L`. -/
def nbrsL (S : Finset L) : Finset R :=
  Finset.univ.filter fun r => ∃ ℓ ∈ S, adj ℓ r

/-- `N(T) ⊆ L` for `T ⊆ R`. -/
def nbrsR (T : Finset R) : Finset L :=
  Finset.univ.filter fun ℓ => ∃ r ∈ T, adj ℓ r

/-- `(ΔL, ΔR)`-biregularity: every left vertex has exactly `ΔL` neighbours and every right
vertex exactly `ΔR`. -/
def IsBiregular (ΔL ΔR : ℕ) : Prop :=
  (∀ ℓ : L, (Finset.univ.filter fun r => adj ℓ r).card = ΔL) ∧
  (∀ r : R, (Finset.univ.filter fun ℓ => adj ℓ r).card = ΔR)

/-- **Definition 3.2** (p. 13). A `(ΔL, ΔR)`-biregular bipartite graph on `L ⊔ R` is two-sided
`(α, ε)`-lossless if `|N(S)| ≥ (1−ε)ΔL|S|` for all `S ⊆ L` with `|S| ≤ α|L|` and
`|N(T)| ≥ (1−ε)ΔR|T|` for all `T ⊆ R` with `|T| ≤ α|R|`. No restriction on `α`, `ε` is built
in. The predicate includes the biregularity with the stated degrees. -/
def IsTwoSidedLossless (ΔL ΔR : ℕ) (α ε : ℝ) : Prop :=
  IsBiregular adj ΔL ΔR ∧
  (∀ S : Finset L, (S.card : ℝ) ≤ α * Fintype.card L →
      (1 - ε) * ΔL * S.card ≤ ((nbrsL adj S).card : ℝ)) ∧
  (∀ T : Finset R, (T.card : ℝ) ≤ α * Fintype.card R →
      (1 - ε) * ΔR * T.card ≤ ((nbrsR adj T).card : ℝ))

end Basic

section Orbit

open Classical in
/-- The binary matrix of a quotient (multi)graph: `E` carries the edges (with an edge predicate
`isEdge`), `src`/`tgt` are the endpoint maps. Its `(ρ, ϑ)` entry is the number of `G`-orbits of
edges `e` whose source lies in the vertex orbit `ϑ` and whose target lies in `ρ`, reduced modulo
`2`. (For equivariant data the entry does not depend on the representative `out` chosen.) -/
noncomputable def edgeOrbitMatrix (G : Type*) [Group G] {E P Q : Type*} [MulAction G E]
    [MulAction G P] [MulAction G Q] [Fintype E] (isEdge : E → Prop) (src : E → P) (tgt : E → Q) :
    Matrix (orbitRel.Quotient G Q) (orbitRel.Quotient G P) (ZMod 2) :=
  Matrix.of fun ρ ϑ =>
    ((Finset.univ.filter fun o : orbitRel.Quotient G E =>
        isEdge o.out ∧ Quotient.mk (orbitRel G P) (src o.out) = ϑ ∧
          Quotient.mk (orbitRel G Q) (tgt o.out) = ρ).card : ZMod 2)

/-- §3.2, p. 14: the **orbit matrix** `[A] : 𝔽₂^{L/G} → 𝔽₂^{R/G}` of a bipartite graph with a
`G`-action, the adjacency map of the quotient graph `Γ/G` whose vertices are the vertex orbits
and whose edges are the edge orbits (entries counted modulo `2`). -/
noncomputable def orbitMatrix (G : Type*) [Group G] {L R : Type*} [MulAction G L]
    [MulAction G R] [Fintype L] [Fintype R] (adj : L → R → Prop) :
    Matrix (orbitRel.Quotient G R) (orbitRel.Quotient G L) (ZMod 2) :=
  edgeOrbitMatrix G (E := L × R) (fun e => adj e.1 e.2) Prod.fst Prod.snd

end Orbit

end FullRankSmallSetQLTC.IndependentChecks

namespace FullRankSmallSetQLTC.IndependentChecks

/-! ## Vertex sets of the form `G × S` with left translation (§3.1, p. 13) -/

/-- A vertex `(g, s)` of `G × S`, on which `G` acts by left translation `k • (g, s) = (kg, s)`. -/
structure Cell (G S : Type*) where
  grp : G
  lab : S
deriving DecidableEq

instance {G S : Type*} [Group G] : MulAction G (Cell G S) where
  smul k v := ⟨k * v.grp, v.lab⟩
  one_smul v := by cases v; exact congrArg₂ Cell.mk (one_mul _) rfl
  mul_smul a b v := by cases v; exact congrArg₂ Cell.mk (mul_assoc _ _ _) rfl

/-- `Cell G S ≃ G × S`. -/
def Cell.equivProd (G S : Type*) : Cell G S ≃ G × S where
  toFun v := (v.grp, v.lab)
  invFun p := ⟨p.1, p.2⟩
  left_inv v := by cases v; rfl
  right_inv p := by cases p; rfl

instance {G S : Type*} [Fintype G] [Fintype S] : Fintype (Cell G S) :=
  Fintype.ofEquiv (G × S) (Cell.equivProd G S).symm

end FullRankSmallSetQLTC.IndependentChecks


