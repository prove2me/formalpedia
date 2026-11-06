-- Prove2me | Definitions.Def_FasterSFM_BlockDAG
-- name    : FasterSFM_BlockDAG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:53.978415+00:00
-- url     : https://prove2.me/theorems/51218c27-a019-469d-b45c-a3d643d43d46
-- title:
--   Blocks, closed sets, the slided function $H_t$, calibration and certificates
-- statement:
--   The combinatorial part of the algorithm works on the **quotient DAG** $D$: the strongly connected components of the implication graph on $U$ are contracted to $N$ **blocks**, and $D$ is acyclic. A set $X$ of blocks is **closed** if $u\in X$ and $u\to v$ imply $v\in X$; its **lift** $\mathrm{lift}(X)\subseteq U$ is the union of its blocks.
--
--   For the sliding parameter $s$ (with witness value $m=h(\emptyset)+1-s$), eq. (2) defines on the blocks
--
--   $$H_s(X)=\begin{cases}0,& X=\emptyset\text{ or }X=V(D),\\ h(\mathrm{lift}(X))-h(\emptyset)-1+s,&\text{otherwise}.\end{cases}$$
--
--   $H_s$ is submodular when $h$ is and $h(\emptyset),h(U)\ge m$. For a block $z$, $\mathrm{Anc}_D(z)$ is the set of blocks that reach $z$ (including $z$), $A_z=V(D)\setminus\mathrm{Anc}_D(z)$, $B_z=A_z\cup\{z\}$ and $c_z=H_s(A_z)$. $D$ is **calibrated** at $t$ if $H_t(A_z)\ge0$ and $H_t(B_z)\ge0$ for every $z$ (3). An ordering is **descendant-first** if $v$ precedes $u$ for every arc $u\to v$.
--
--   A vector stored on old blocks is mapped to the current DAG by summing its entries over the old blocks merged into each current block. A **certificate** is a convex combination $(\alpha_i)$ of nonzero vectors $a_i$ on the blocks, each summing to $0$, with greedy terms bounded by $H_t$ on proper nonempty closed sets and graph terms non-positive on closed sets. Its quantities are
--
--   $$y=\sum_i\alpha_ia_i,\quad L=\sum_i\alpha_i\|a_i\|_1,\quad \beta=\sum_v[-y_v]_+=\tfrac12\|y\|_1,\quad \theta=\sum_{i\ \mathrm{greedy}}\alpha_i,\quad \Delta=\sum_{i\ \mathrm{greedy}}\alpha_i(t-t_i),$$
--
--   $r$, the number of positive $\alpha_i$, and the guard (6) $G=[r(n-1)-1](\beta-\Delta)$.
--
--   **Formalization Note** The ground set is `Fin n` and the blocks are `Fin N`; a block structure is a surjective map from elements to blocks with an acyclic arc relation, of which the quotient DAG is one instance. Orderings are position maps $\sigma$ (`Equiv.Perm`), the prefix $T_j$ being the blocks at positions below $j$.
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, §4, pp.8–13: blocks and closed sets p.8; eq. (2) p.9; calibration (3) and descendant-first orders p.10; mapped vectors and certificates p.12; guard (6) p.13

import Mathlib

namespace FasterSFM

open Classical

/-!
# Blocks, the quotient DAG, the slided function `H_t`, calibration and certificates

Ene & Nguyen, arXiv:2610.25403v1, §4, pp.8–13: blocks and closed sets (p.8), the sliding parameter
and `H_t` of (2) (p.9), calibration (3) and descendant-first orders (p.10), the mapping of stored
vectors to the current DAG (p.12), and the certificate quantities `y, L, β, θ, ∆, r` and the guard
`G` of (6) (pp.12–13).

**Formalization Note.**
* The ground set is `U = Fin n`; the `N` blocks of the current quotient DAG are `Fin N`. A block
  structure is the map `blk : Fin n → Fin N` sending each element to its block (every block nonempty)
  and an acyclic arc relation on the blocks. The paper's quotient DAG of the implication graph is one
  instance; the lemmas are stated for every such structure (reading R8).
* A position map `σ : Equiv.Perm (Fin N)` encodes an ordering `π = σ⁻¹`: `σ v` is the position of
  `v`, counted from `0`.
* A certificate is indexed by `Fin m`; `grd i = true` marks a greedy term and `stamp i` is its
  timestamp `t_i`.
-/

/-- A partition of `Fin n` into `N` nonempty blocks with an acyclic arc relation on the blocks: the
quotient DAG `D` of §4 (p.8). -/
structure BlockDAG (n N : ℕ) where
  /-- the block of each original element -/
  blk : Fin n → Fin N
  /-- every block is nonempty -/
  blk_surj : Function.Surjective blk
  /-- the arcs `u → v` of the quotient DAG -/
  arc : Fin N → Fin N → Prop
  /-- the quotient graph has no directed cycle -/
  acyclic : ∀ z, ¬ Relation.TransGen arc z z

namespace BlockDAG

variable {n N : ℕ} (D : BlockDAG n N)

/-- `X ⊆ V(D)` is closed: `u ∈ X` and `u → v` imply `v ∈ X` (p.8). -/
def Closed (X : Finset (Fin N)) : Prop := ∀ u ∈ X, ∀ v, D.arc u v → v ∈ X

/-- `lift(X)`: the union of the blocks in `X`, a subset of `U` (p.8). -/
noncomputable def lift (X : Finset (Fin N)) : Finset (Fin n) :=
  Finset.univ.filter fun u => D.blk u ∈ X

/-- `|C|`, the number of original elements in block `C`. -/
noncomputable def blockSize (C : Fin N) : ℕ :=
  (Finset.univ.filter fun u => D.blk u = C).card

/-- The slided function `H_s` of (2), p.9: `H_s(X) = 0` at the endpoints `X = ∅, V(D)`, and
`H_s(X) = h(lift X) − h(∅) − 1 + s` otherwise. -/
noncomputable def Hs (h : Finset (Fin n) → ℝ) (s : ℝ) (X : Finset (Fin N)) : ℝ :=
  if X = ∅ ∨ X = Finset.univ then 0 else h (D.lift X) - h ∅ - 1 + s

/-- `Anc_D(z)`: the blocks that can reach `z`, including `z` (p.10). -/
noncomputable def Anc (z : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun u => Relation.ReflTransGen D.arc u z

/-- `A_z = V(D) ∖ Anc_D(z)` (p.10). -/
noncomputable def A (z : Fin N) : Finset (Fin N) := Finset.univ \ D.Anc z

/-- `B_z = A_z ∪ {z}` (p.10). -/
noncomputable def B (z : Fin N) : Finset (Fin N) := insert z (D.A z)

/-- `c_z = H_s(A_z)` (p.10; Fact 3: "now `c_v = H_s(A_v)`"). -/
noncomputable def cz (h : Finset (Fin n) → ℝ) (s : ℝ) (z : Fin N) : ℝ := D.Hs h s (D.A z)

/-- Calibration (3), p.10: `H_t(A_z) ≥ 0` and `H_t(B_z) ≥ 0` for every block `z`. -/
def Calibrated (h : Finset (Fin n) → ℝ) (t : ℝ) : Prop :=
  ∀ z, 0 ≤ D.Hs h t (D.A z) ∧ 0 ≤ D.Hs h t (D.B z)

/-- A descendant-first ordering (p.10): for every arc `u → v`, `v` comes before `u`. -/
def DescendantFirst (σ : Equiv.Perm (Fin N)) : Prop := ∀ u v, D.arc u v → σ v < σ u

end BlockDAG

/-- The prefix `T_j` of the ordering with position map `σ`: its first `j` blocks. -/
noncomputable def prefixSet {N : ℕ} (σ : Equiv.Perm (Fin N)) (j : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun v => (σ v : ℕ) < j

/-- The witness value `m = h(∅) + 1 − t` is at most `h(∅)` and `h(U)` (p.9: the endpoints are queried
at initialization, so `h(∅), h(U) ≥ m` throughout the algorithm). This is the condition under which
`H_t` is submodular (p.9). -/
def EndpointsAbove {n : ℕ} (h : Finset (Fin n) → ℝ) (t : ℝ) : Prop :=
  h ∅ + 1 - t ≤ h ∅ ∧ h ∅ + 1 - t ≤ h Finset.univ

/-- `a(X) = Σ_{v ∈ X} a_v` for a vector on the blocks. -/
noncomputable def setSum {N : ℕ} (a : Fin N → ℝ) (X : Finset (Fin N)) : ℝ := ∑ v ∈ X, a v

/-- A vector on old blocks mapped to the current DAG "by summing the values on the vertices that were
merged during contractions" (Lemma 4, p.12): `ã_Z = Σ_{C : μ C = Z} a_C`. -/
noncomputable def pushVec {N₀ N : ℕ} (μ : Fin N₀ → Fin N) (a : Fin N₀ → ℝ) : Fin N → ℝ :=
  fun Z => ∑ C ∈ Finset.univ.filter (fun C => μ C = Z), a C

/-- The unit vector `e_u` on the blocks; the graph vector is `g_uv = e_u − e_v` (p.11). -/
noncomputable def unitVec {N : ℕ} (u : Fin N) : Fin N → ℝ := fun w => if w = u then 1 else 0

section Certificate

variable {N m : ℕ}

/-- `y = Σ_i α_i a_i` (p.12). -/
noncomputable def certY (a : Fin m → Fin N → ℝ) (α : Fin m → ℝ) : Fin N → ℝ :=
  fun v => ∑ i, α i * a i v

/-- `L = Σ_i α_i ‖a_i‖₁` (p.12). -/
noncomputable def certL (a : Fin m → Fin N → ℝ) (α : Fin m → ℝ) : ℝ :=
  ∑ i, α i * ∑ v, |a i v|

/-- `β = β_{V(D)} = Σ_v [−y_v]₊` (p.12; it equals `‖y‖₁/2` when `y` sums to `0`). -/
noncomputable def certBeta (a : Fin m → Fin N → ℝ) (α : Fin m → ℝ) : ℝ :=
  ∑ v, max (-(certY a α v)) 0

/-- `θ = Σ_{i greedy} α_i` (p.12). -/
noncomputable def certTheta (α : Fin m → ℝ) (grd : Fin m → Bool) : ℝ :=
  ∑ i, if grd i then α i else 0

/-- `∆ = Σ_{i greedy} α_i (t − t_i)` (p.12). -/
noncomputable def certDelta (α : Fin m → ℝ) (grd : Fin m → Bool) (stamp : Fin m → ℝ) (t : ℝ) :
    ℝ :=
  ∑ i, if grd i then α i * (t - stamp i) else 0

/-- `r`, the number of terms with `α_i > 0` (p.13). -/
noncomputable def certSupp (α : Fin m → ℝ) : ℕ :=
  (Finset.univ.filter fun i => 0 < α i).card

/-- The uniform historical extraction guard (6), p.13: `G = [r(n − 1) − 1](β − ∆)`, with `n` the
size of the original ground set. -/
noncomputable def guardG (n r : ℕ) (β Δ : ℝ) : ℝ := ((r : ℝ) * ((n : ℝ) - 1) - 1) * (β - Δ)

/-- A certificate on the current DAG `D` at parameter `t` (§4.3, p.12): a convex combination of
nonzero vectors on the blocks, each summing to `0`; every greedy term satisfies `a_i(X) ≤ H_t(X)` on
every proper nonempty closed `X` (what (4) and Lemma 4 give), and every graph term satisfies
`a_i(X) ≤ 0` on every closed `X` (Lemma 4). -/
def IsCertificate {n : ℕ} (D : BlockDAG n N) (h : Finset (Fin n) → ℝ) (t : ℝ)
    (a : Fin m → Fin N → ℝ) (α : Fin m → ℝ) (grd : Fin m → Bool) : Prop :=
  (∀ i, 0 ≤ α i) ∧ (∑ i, α i = 1) ∧ (∀ i, a i ≠ 0) ∧ (∀ i, ∑ v, a i v = 0) ∧
  (∀ i, grd i = true → ∀ X, D.Closed X → X.Nonempty → X ≠ Finset.univ →
    setSum (a i) X ≤ D.Hs h t X) ∧
  (∀ i, grd i = false → ∀ X, D.Closed X → setSum (a i) X ≤ 0)

end Certificate

end FasterSFM


