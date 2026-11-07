-- Prove2me | Definitions.Def_DynBrooks_Auxiliary
-- name    : DynBrooks_Auxiliary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:08:06.30627+00:00
-- url     : https://prove2.me/theorems/b52dfcd5-22f3-423a-ba3f-8bcf81e74a0e
-- title:
--   §4.1 — the almost-clique decomposition, cores, representatives, the auxiliary graph $J$ and weights $f_u$
-- statement:
--   Parameters (p.15): $R=\ell^2$, $b=\ell^4$, $H=\lfloor\Delta/R\rfloor$. An **almost-clique decomposition** partitions $V=S\,\dot\cup\,C_1\,\dot\cup\dots\dot\cup\,C_k$ with, for constants $c_S,\eta,\eta_0$:
--   $\zeta_G(v)\ge c_S\Delta$ for $v\in S$; $(1-\eta)\Delta\le|C|\le(1+\eta)\Delta$; $\kappa_v\le\eta\Delta$ for $v\in C$; $|C\setminus N(x)|\ge\eta_0\Delta$ for $x\notin C$; here $\kappa_v=|C\setminus N[v]|+|N(v)\setminus C|$.
--
--   Each almost-clique has an integer **scale** $\sigma_C\ge b$ with $\mu_C\le2\sigma_C$, and $\mu_C\ge\sigma_C/2$ if $\sigma_C>b$, where $\mu_C=A_C/\Delta$ and $A_C=\sum_{v\in C}\kappa_v$; $C$ is **retained** if $\sigma_C=b$. In a retained almost-clique a vertex with $\kappa_v>32b$ is an **outlier**, and an outlier has $\kappa_v\ge16b$. A nonedge of $G[C]$ is selected exactly when $C$ is retained, $r_C=\Delta-|C|+1\le40b$, and $C$ is not complete.
--
--   **Cores**: a singleton for each vertex of $S$ or of a nonretained almost-clique; the selected pair; a singleton for each outlier not in the selected pair. An almost-clique is **eligible** if it is complete, retained, contains no core and has $r_C\le40b$. An eligible $C$ may have a **center**, a core $K$ with $m_C(K)\ge H$ edges to $C$, and then a **representative** $x_C\in C$ nonadjacent to $K$ and to the other representatives of $K$; if it has none, $m_C(K)<H$ for every core outside $C$ (2). The group of a core is $D(u)=K(u)\cup R(u)$. The **auxiliary graph** $J$ has a vertex per core, two adjacent when an edge of $G$ joins their groups. The **weight** is $f_u=\sigma_C+\sum_{x\in K(u)}\kappa_x$ if $K(u)\subseteq C$, and $f_u=2\Delta$ if $K(u)\subseteq S$.
--
--   **Formalization Note** This is a structure carrying the page's properties, not a chosen algorithm: the paper obtains the decomposition from [BRW25, HM24] with random choices, and statements about it hold for every such structure.
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), §4.1, pp.15–19 (PDF 17–21)

import Mathlib
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynBrooks_Sparsity

namespace DynBrooks

/-! # The auxiliary construction of §4.1

Mishra, Mukherjee, *Fully Dynamic Brooks Coloring* (STOC 2027 submission, sha256 6542a9f1…), §4.1,
pp.15–19 (PDF 17–21). Parameters: `R = ℓ²`, `b = ℓ⁴`, `H = ⌊∆/R⌋` (p.15).

**Formalization Note.** This is the construction as a structure with the page's properties, and not a
chosen algorithm: the paper obtains the decomposition from [BRW25, HM24] with randomized choices, and
none of those choices is fixed here. A statement about it holds for every such structure. The
almost-cliques are indexed by `Fin k`, and `part v` is the index of the almost-clique of `v`, or `none`
for `v ∈ S`, so `V = S ⊔ C₁ ⊔ ⋯ ⊔ C_k` holds by construction. `r_C = ∆ − |C| + 1` is an integer, since
`|C|` may exceed `∆ + 1`. A core is a finite set of vertices. -/

open Classical

variable {n : ℕ}

/-- `R = ℓ²`. -/
def paramR (ℓ : ℕ) : ℕ := ℓ ^ 2

/-- `b = ℓ⁴`. -/
def paramB (ℓ : ℕ) : ℕ := ℓ ^ 4

/-- `H = ⌊∆/R⌋`. -/
def paramH (Δ ℓ : ℕ) : ℕ := Δ / paramR ℓ

/-- The vertex set of the `i`-th part of a part assignment. -/
noncomputable def partSet {k : ℕ} (part : Fin n → Option (Fin k)) (i : Fin k) : Finset (Fin n) :=
  Finset.univ.filter fun v => part v = some i

/-- The defect `κ_v = |C \ N[v]| + |N(v) \ C|` of `v` with respect to `C` (p.16). -/
noncomputable def defect (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) (v : Fin n) : ℕ :=
  (C.filter fun x => x ≠ v ∧ ¬ G.Adj v x).card + ((G.neighborFinset v).filter fun x => x ∉ C).card

/-- The almost-clique decomposition, part scales, outliers and selected nonadjacent pairs (pp.15–17). -/
structure Decomposition (G : SimpleGraph (Fin n)) (Δ ℓ : ℕ) (cS η η₀ : ℝ) where
  /-- number of almost-cliques -/
  k : ℕ
  /-- the almost-clique of a vertex, `none` for `v ∈ S` -/
  part : Fin n → Option (Fin k)
  /-- `ζ_G(v) = Ω(∆)` for `v ∈ S` -/
  sparse_bound : ∀ v, part v = none → cS * Δ ≤ sparsity Δ G v
  /-- `(1 − η)∆ ≤ |C| ≤ (1 + η)∆` -/
  size_lower : ∀ i, (1 - η) * Δ ≤ ((partSet part i).card : ℝ)
  size_upper : ∀ i, ((partSet part i).card : ℝ) ≤ (1 + η) * Δ
  /-- `κ_v ≤ η∆` for `v ∈ C` -/
  defect_bound : ∀ i, ∀ v ∈ partSet part i, (defect G (partSet part i) v : ℝ) ≤ η * Δ
  /-- `|C \ N(x)| ≥ η₀∆` for `x ∉ C` -/
  separation : ∀ i, ∀ x ∉ partSet part i,
    η₀ * Δ ≤ (((partSet part i).filter fun y => ¬ G.Adj x y).card : ℝ)
  /-- the integer scale `σ_C` -/
  scale : Fin k → ℕ
  scale_ge : ∀ i, paramB ℓ ≤ scale i
  /-- `µ_C ≤ 2σ_C`, where `µ_C = A_C/∆` and `A_C = Σ_{v∈C} κ_v` -/
  scale_upper : ∀ i,
    ((∑ v ∈ partSet part i, defect G (partSet part i) v : ℕ) : ℝ) / Δ ≤ 2 * scale i
  /-- `µ_C ≥ σ_C/2` if `σ_C > b` -/
  scale_lower : ∀ i, paramB ℓ < scale i →
    (scale i : ℝ) / 2 ≤ ((∑ v ∈ partSet part i, defect G (partSet part i) v : ℕ) : ℝ) / Δ
  /-- the outliers of the retained almost-cliques -/
  outlier : Set (Fin n)
  /-- outliers lie in retained almost-cliques, where `C` is retained if `σ_C = b` -/
  outlier_retained : ∀ v ∈ outlier, ∃ i, part v = some i ∧ scale i = paramB ℓ
  /-- a vertex of a retained part with `κ_v > 32b` is an outlier -/
  outlier_of_large : ∀ i v, part v = some i → scale i = paramB ℓ →
    32 * paramB ℓ < defect G (partSet part i) v → v ∈ outlier
  /-- an outlier has `κ_v ≥ 16b` -/
  outlier_large : ∀ i, ∀ v ∈ outlier, part v = some i →
    16 * paramB ℓ ≤ defect G (partSet part i) v
  /-- the selected nonedge of an almost-clique -/
  pair : Fin k → Option (Fin n × Fin n)
  /-- a nonedge is selected exactly when `C` is retained, `r_C ≤ 40b`, and `C` is not complete -/
  pair_isSome : ∀ i, (pair i).isSome ↔
    (scale i = paramB ℓ ∧ (Δ : ℤ) - (partSet part i).card + 1 ≤ 40 * (paramB ℓ : ℤ) ∧
      ¬ G.IsClique (partSet part i : Set (Fin n)))
  /-- the selected pair is a nonedge of `G[C]` -/
  pair_spec : ∀ i x y, pair i = some (x, y) →
    x ∈ partSet part i ∧ y ∈ partSet part i ∧ x ≠ y ∧ ¬ G.Adj x y

namespace Decomposition

variable {G : SimpleGraph (Fin n)} {Δ ℓ : ℕ} {cS η η₀ : ℝ} (D : Decomposition G Δ ℓ cS η η₀)

/-- The almost-clique `C_i`. -/
noncomputable def C (i : Fin D.k) : Finset (Fin n) := partSet D.part i

/-- `r_C = ∆ − |C| + 1`. -/
noncomputable def r (i : Fin D.k) : ℤ := (Δ : ℤ) - (D.C i).card + 1

/-- `C_i` is retained: `σ_C = b`. -/
def Retained (i : Fin D.k) : Prop := D.scale i = paramB ℓ

/-- The core of the selected pair of `C_i`, as a set of vertices. -/
noncomputable def pairCore (i : Fin D.k) : Finset (Fin n) :=
  match D.pair i with
  | some (x, y) => {x, y}
  | none => ∅

/-- The cores (p.16–17): a singleton for each vertex of `S` or of a nonretained almost-clique; the
selected pair; a singleton for each outlier not in the selected pair of its part. -/
def IsCore (K : Finset (Fin n)) : Prop :=
  (∃ v, K = {v} ∧ (D.part v = none ∨ ∃ i, D.part v = some i ∧ ¬ D.Retained i)) ∨
  (∃ i, D.pair i ≠ none ∧ K = D.pairCore i) ∨
  (∃ v ∈ D.outlier, K = {v} ∧ ∀ i, D.part v = some i → v ∉ D.pairCore i)

/-- An **eligible** almost-clique (p.17): complete, retained, containing no core, with `r_C ≤ 40b`. -/
def Eligible (i : Fin D.k) : Prop :=
  G.IsClique (D.C i : Set (Fin n)) ∧ D.Retained i ∧ (∀ K, D.IsCore K → ¬ K ⊆ D.C i) ∧
    D.r i ≤ 40 * (paramB ℓ : ℤ)

/-- `m_C(u)`: the number of edges between the core `K` and `C_i`. -/
noncomputable def edgesToPart (K : Finset (Fin n)) (i : Fin D.k) : ℕ :=
  ∑ x ∈ K, ((G.neighborFinset x).filter fun y => y ∈ D.C i).card

end Decomposition

/-- The auxiliary construction: a decomposition with centers and representatives (p.17). -/
structure AuxConstruction (G : SimpleGraph (Fin n)) (Δ ℓ : ℕ) (cS η η₀ : ℝ) extends
    Decomposition G Δ ℓ cS η η₀ where
  /-- the selected center of an almost-clique -/
  center : Fin k → Option (Finset (Fin n))
  /-- the representative `x_C`, meaningful when `C` has a center -/
  rep : Fin k → Fin n
  /-- a center is selected only for an eligible almost-clique, and is a core with `m_C(u) ≥ H` -/
  center_spec : ∀ i K, center i = some K →
    toDecomposition.Eligible i ∧ toDecomposition.IsCore K ∧ paramH Δ ℓ ≤ toDecomposition.edgesToPart K i
  /-- if an eligible almost-clique has no center, then `m_C(u) < H` for every core outside it (2) -/
  center_none : ∀ i, toDecomposition.Eligible i → center i = none →
    ∀ K, toDecomposition.IsCore K → Disjoint K (toDecomposition.C i) →
      toDecomposition.edgesToPart K i < paramH Δ ℓ
  /-- the representative lies in the almost-clique -/
  rep_mem : ∀ i K, center i = some K → rep i ∈ toDecomposition.C i
  /-- the representative is nonadjacent to every vertex of the core -/
  rep_core : ∀ i K, center i = some K → ∀ x ∈ K, ¬ G.Adj (rep i) x
  /-- the representatives of one core are pairwise nonadjacent -/
  rep_rep : ∀ i j K, center i = some K → center j = some K → ¬ G.Adj (rep i) (rep j)

namespace AuxConstruction

variable {G : SimpleGraph (Fin n)} {Δ ℓ : ℕ} {cS η η₀ : ℝ} (A : AuxConstruction G Δ ℓ cS η η₀)

/-- The auxiliary vertices: one for each core. -/
abbrev Vertex : Type := {K : Finset (Fin n) // A.toDecomposition.IsCore K}

/-- The set of representatives `R(u)` of a core. -/
noncomputable def reps (K : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ.filter fun i => A.center i = some K).image A.rep

/-- The group `D(u) = K(u) ∪ R(u)`. -/
noncomputable def group (K : Finset (Fin n)) : Finset (Fin n) := K ∪ A.reps K

/-- The auxiliary graph `J`: distinct auxiliary vertices are adjacent if an edge of `G` joins their
groups. -/
def J : SimpleGraph A.Vertex where
  Adj u v := u ≠ v ∧ ∃ x ∈ A.group u.1, ∃ y ∈ A.group v.1, G.Adj x y
  symm := ⟨fun _ _ h => ⟨h.1.symm, by
    obtain ⟨_, x, hx, y, hy, hxy⟩ := h
    exact ⟨y, hy, x, hx, hxy.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The weight `f_u`: `σ_C + Σ_{x∈K(u)} κ_x` if `K(u) ⊆ C`, and `2∆` if `K(u) ⊆ S` (p.19). -/
noncomputable def weight (K : Finset (Fin n)) : ℕ :=
  if h : ∃ i, K ⊆ A.toDecomposition.C i then
    A.scale h.choose + ∑ x ∈ K, defect G (A.toDecomposition.C h.choose) x
  else 2 * Δ

/-- `v` is an **ordinary** dense vertex (p.17): in neither a core nor a representative. Vertices of `S`
and of nonretained almost-cliques are singleton cores, so an ordinary vertex lies in a retained
almost-clique. -/
def Ordinary (v : Fin n) : Prop :=
  (∀ K, A.toDecomposition.IsCore K → v ∉ K) ∧ ∀ i K, A.center i = some K → A.rep i ≠ v

end AuxConstruction

end DynBrooks


