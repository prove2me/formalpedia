-- Prove2me | Definitions.Def_FriezeKannan_PseudoReg_Setting
-- name    : FriezeKannan_PseudoReg_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:09.805977+00:00
-- url     : https://prove2.me/theorems/2d696038-3b56-4463-9b6e-1d9ab9336700
-- title:
--   §5 and §5.1, pp. 202–204 — M(S,T), ‖·‖_F, cut matrices, Δ_P(S,T), ε-pseudo-regularity, M_Q, compatibility, and the atom partition
-- statement:
--   Throughout, $V$ is a finite vertex set with $n=|V|$, and $G=(V,E)$ is a simple graph on $V$ with adjacency matrix $\mathbf A$ (entries $1$ on adjacent pairs, $0$ elsewhere, in particular $0$ on the diagonal). Subsets of $V$ are finite sets, and partitions of $V$ have nonempty parts.
--
--   1. **Block sums and the Frobenius norm.** For a real $V\times V$ matrix $\mathbf M$ and $S,T\subseteq V$,
--   $$\mathbf M(S,T)=\sum_{i\in S}\sum_{j\in T}\mathbf M(i,j),\qquad \|\mathbf M\|_F=\Big(\sum_{i,j}\mathbf M(i,j)^2\Big)^{1/2}.$$
--   2. **Cut matrices.** For $R,C\subseteq V$ and a real $d$, the cut matrix $\mathrm{CUT}(R,C,d)$ has entry $d$ on $R\times C$ and $0$ elsewhere. Given $s$ triples $(R_t,C_t,d_t)$, $t=1,\dots,s$, their sum is $\mathbf D=\mathbf D^{(1)}+\dots+\mathbf D^{(s)}$ with $\mathbf D^{(t)}=\mathrm{CUT}(R_t,C_t,d_t)$.
--   3. **Deviation from regularity.** Let $\mathcal P=V_1,\dots,V_k$ be a partition of $V$, $K=\{1,\dots,k\}$, and write $X_i=X\cap V_i$. For $S,T\subseteq V$ let $e(S,T)$ be the number of ordered pairs $(u,v)\in S\times T$ with $u$ adjacent to $v$ (for disjoint $S,T$ this is the number of edges between $S$ and $T$), let $d_{i,j}=e(V_i,V_j)/(|V_i||V_j|)$, and
--   $$\Delta_{\mathcal P}(S,T)=e(S,T)-\sum_{i\in K}\sum_{j\in K}d_{i,j}\,|S_i|\,|T_j|.$$
--   4. **Pseudo-regularity.** $\mathcal P$ is **$\epsilon$-pseudo-regular** if $|\Delta_{\mathcal P}(S,T)|\le\epsilon n^2$ for all disjoint $S,T\subseteq V$.
--   5. **Block averages.** For a partition $\mathcal Q=W_1,\dots,W_q$ and a $V\times V$ matrix $\mathbf M$, the matrix $\mathbf M_{\mathcal Q}$ is defined by $\mathbf M_{\mathcal Q}(p,q)=\mathbf M(W_i,W_j)/(|W_i||W_j|)$ for $(p,q)\in W_i\times W_j$.
--   6. **Compatibility.** $\mathbf M$ is **compatible** with $\mathcal Q$ if $\mathbf M(p,q)$ is constant over every block $W_i\times W_j$.
--   7. **The atom partition.** Given $R_1,\dots,R_s,C_1,\dots,C_s\subseteq V$, the atom partition is the coarsest partition of $V$ in which every $R_t$ and every $C_t$ is a union of parts. Its parts are the nonempty atoms $\bigcap_t R_t^{\pm}\cap\bigcap_t C_t^{\pm}$ (each set or its complement).
--
--   These are the objects of Section 5.1 of Frieze and Kannan: $\Delta_{\mathcal P}$ measures how far the edge counts of a graph are from those predicted by the densities between the parts, and the atom partition of a cut decomposition is the partition the paper shows to be pseudo-regular.
--
--   **Formalization Note.** A partition of $V$ is a Mathlib `Finpartition` of `Finset.univ`; the index set $K$ is its set of parts. The densities are Mathlib's `SimpleGraph.edgeDensity`, cast from $\mathbb Q$ to $\mathbb R$, for all pairs of parts. For $i\ne j$ this is the paper's $d(V_i,V_j)=e(V_i,V_j)/(|V_i||V_j|)$. For $i=j$ it is the block average $2e(V_i)/|V_i|^2=\mathbf A(V_i,V_i)/|V_i|^2$, where $e(V_i)$ is the number of edges inside $V_i$; the paper's §5 preamble instead sets $d(A,A)=e(A,A)/\binom{|A|}{2}$, but with that value its identity (47) $\mathbf A(S,T)-\mathbf A_{\mathcal Q}(S,T)=\Delta_{\mathcal Q}(S,T)$ fails on diagonal blocks, and the proof of (50) uses (47); the block average is the value the argument needs. The block average $\mathbf M_{\mathcal Q}$ is written with `Finpartition.part`, the part containing a vertex, which is nonempty here, so no division by zero occurs. The atom partition is Mathlib's `Finpartition.atomise` of the family $\{R_t\}\cup\{C_t\}$. The Frobenius norm is the square root of the sum of squared entries, not Mathlib's scoped matrix norm. The same objects for rectangular matrices are re-declared in the companion mission on cut decompositions, because draft items cannot import each other.
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), pp. 177–178, §2.1 (M(S,T), ‖·‖_F, CUT(R,C,d)); p. 202, §5 (e(A,B), d(A,B)); p. 203, §5.1 (Δ_P(S,T), ε-pseudo-regular, M_Q, compatible); p. 204, §5.1 (the coarsest partition with each R_t, C_t a union of parts)

import Mathlib

namespace FriezeKannan.PseudoReg

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `M(S, T) = ∑_{i ∈ S} ∑_{j ∈ T} M i j` (§2.1, p. 178). -/
def blockSum (M : Matrix V V ℝ) (S T : Finset V) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ T, M i j

/-- The Frobenius norm `‖M‖_F = (∑_{i,j} M i j ^ 2)^{1/2}` (§2.1, p. 177). -/
noncomputable def frobNorm (M : Matrix V V ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- The cut matrix `CUT(S, T, d)`: entry `d` on `S × T`, `0` elsewhere (§2.1, p. 178). -/
def cutMatrix (S T : Finset V) (d : ℝ) : Matrix V V ℝ :=
  fun i j => if i ∈ S ∧ j ∈ T then d else 0

/-- The sum `D = D⁽¹⁾ + ⋯ + D⁽ˢ⁾` of the cut matrices `CUT(R_t, C_t, d_t)`, `t = 1, …, s`. -/
def cutSum {s : ℕ} (Rs Cs : Fin s → Finset V) (d : Fin s → ℝ) : Matrix V V ℝ :=
  ∑ t, cutMatrix (Rs t) (Cs t) (d t)

/-- `Δ_P(S, T) = e(S, T) − ∑_{i ∈ K} ∑_{j ∈ K} d_{i,j} |S_i| |T_j|` (§5.1, p. 203), where the
parts `V_i` of `P` index the sums, `S_i = S ∩ V_i`, `T_j = T ∩ V_j`, and
`d_{i,j} = G.edgeDensity V_i V_j` is the number of ordered adjacent pairs in `V_i × V_j`
divided by `|V_i| |V_j|` (for `i = j` this is the block average `2 e(V_i) / |V_i|²`). -/
noncomputable def delta (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V)) (S T : Finset V) : ℝ :=
  ((G.interedges S T).card : ℝ) -
    ∑ Vi ∈ P.parts, ∑ Vj ∈ P.parts,
      (G.edgeDensity Vi Vj : ℝ) * ((S ∩ Vi).card : ℝ) * ((T ∩ Vj).card : ℝ)

/-- A partition `P` of `V` is `ε`-pseudo-regular if `|Δ_P(S, T)| ≤ ε n²` for all disjoint
`S, T ⊆ V`, where `n = |V|` (§5.1, p. 203). -/
def IsPseudoRegular (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V)) (ε : ℝ) : Prop :=
  ∀ S T : Finset V, Disjoint S T → |delta G P S T| ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- The block-average matrix `M_Q`: `M_Q(p, q) = M(W_i, W_j) / (|W_i| |W_j|)` for
`(p, q) ∈ W_i × W_j`, where `W_i = Q.part p` and `W_j = Q.part q` (§5.1, p. 203). -/
noncomputable def blockAvg (Q : Finpartition (Finset.univ : Finset V)) (M : Matrix V V ℝ) :
    Matrix V V ℝ :=
  fun p q => blockSum M (Q.part p) (Q.part q) /
    (((Q.part p).card : ℝ) * ((Q.part q).card : ℝ))

/-- A matrix `M` is compatible with the partition `Q` if `M(p, q)` is constant over every block
`W_i × W_j` of parts of `Q` (§5.1, p. 203). -/
def Compatible (Q : Finpartition (Finset.univ : Finset V)) (M : Matrix V V ℝ) : Prop :=
  ∀ p p' q q' : V, Q.part p = Q.part p' → Q.part q = Q.part q' → M p q = M p' q'

/-- The coarsest partition of `V` in which every `R_t` and every `C_t` is a union of parts:
the nonempty atoms of the family `{R_1, …, R_s, C_1, …, C_s}` (§5.1, p. 204). -/
def atomPartition {s : ℕ} (Rs Cs : Fin s → Finset V) : Finpartition (Finset.univ : Finset V) :=
  Finpartition.atomise Finset.univ (Finset.univ.image Rs ∪ Finset.univ.image Cs)

end FriezeKannan.PseudoReg


