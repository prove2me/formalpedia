-- Prove2me | Definitions.Def_GraphSimOT_Gaps_Distances
-- name    : GraphSimOT_Gaps_Distances
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:06:04.433313+00:00
-- url     : https://prove2.me/theorems/de4b21bc-0b82-41aa-a703-77e5a271d078
-- title:
--   Edit, local edit, cut and spectral distance of graphs of the same order, and their optimal transport versions
-- statement:
--   Let $G, H$ be simple graphs on the common vertex set $[n]$ (in Lean `Fin n`) with adjacency matrices $A_G, A_H \in \{0,1\}^{n\times n}$ (`adj`). For a bijection $\pi$ of the vertex set, $A_G^\pi$ (`permAdj`) is $A_G$ with rows and columns permuted by $\pi$, so $A_G^\pi(\pi v, \pi v') = A_G(v, v')$.
--
--   **Matrix norms** (App. A). For a real matrix $A \in \mathbb R^{V\times W}$: the entrywise 1-norm $\|A\|_{ed} = \sum_{v,w}|A(v,w)|$ (`edNorm`); the cut norm $\|A\|_\square = \max_{S\subseteq V,\,T\subseteq W}\big|\sum_{s\in S,t\in T}A(s,t)\big|$ (the published `FriezeKannan.CutDecomp.cutNorm`); and the operator norm
--   $$\|A\|_{p\to q} = \sup_{x\in\mathbb R^W,\ \|x\|_p = 1}\|Ax\|_q,\qquad \|x\|_p = \Big(\sum_i |x_i|^p\Big)^{1/p}$$
--   (`opNorm p q`, `lpNorm p`), with $\|A\|_p = \|A\|_{p\to p}$: $\|\cdot\|_1$ is the maximum absolute column sum and $\|\cdot\|_2$ the spectral norm.
--
--   **Bijective distances** (p. 1). $d_\diamond(G,H) = \min_\pi \|A_G^\pi - A_H\|_\diamond$ over all bijections $\pi$ (`dEd`, `dCut`, `dOp p q`), normalised as $\delta_{ed} = d_{ed}/n^2$, $\delta_\square = d_\square/n^2$ and $\delta_{p\to q} = d_{p\to q}/n^{1/q+1-1/p}$, so $\delta_1 = d_1/n$ (local edit distance) and $\delta_2 = d_2/n$ (spectral distance).
--
--   **Fractional alignments and optimal transport distances** (pp. 2–3, Eqs. (1), (2)). $\mathrm{DS}^*(n)$ (`DSstar`) is the set of nonnegative $n\times n$ matrices with all row and column sums equal to $1/n$. With the discrepancy $D(v,w,v',w') = A_G(v,v') - A_H(w,w')$ (`disc`) and a fractional alignment $Q^*$,
--   $$B(G,H,Q^*)\big((v,w),(v',w')\big) = Q^*(v,w)\,D(v,w,v',w')\,Q^*(v',w'),$$
--   $$B_{p\to q}(G,H,Q^*)\big((v,w),(v',w')\big) = Q^*(v,w)^{1/q}\,D(v,w,v',w')\,Q^*(v',w')^{1-1/p}$$
--   **with the convention $0^0 = 0$** (`pow00`). Then $\delta^{OT}_{ed} = \min_{Q^*}\|B\|_{ed}$, $\delta^{OT}_\square = \min_{Q^*}\|B\|_\square$ and $\delta^{OT}_{p\to q} = \min_{Q^*}\|B_{p\to q}\|_{p\to q}$, with $\delta^{OT}_1 = \delta^{OT}_{1\to1}$ and $\delta^{OT}_2 = \delta^{OT}_{2\to2}$.
--
--   **Unnormalised costs** (p. 5). For $Q$ in the doubly stochastic matrices $\mathrm{DS}(n)$, $C_\diamond(Q) = \|B_\diamond(G,H,Q)\|_\diamond$ (`costEd`, `costCut`, `costOp`), and $d^{OT}_\diamond = \min_{Q\in\mathrm{DS}(n)} C_\diamond(Q)$ (`dOTEd`, `dOTCut`, `dOTOp`, `dOT1`). The local cost of a pair is $L_Q(v,w) = \sum_{(v',w')}|A_G(v,v') - A_H(w,w')|\,Q(v',w')$ (`localCost`).
--
--   **Formalization Note.** Both graphs live on `Fin n`. The convention $0^0=0$ is `pow00 x e = if x = 0 then 0 else x ^ e`; for $p = 1$ it makes column $(v',w')$ of $B_{1\to1}$ vanish off $\mathrm{supp}(Q^*)$ (Lean's own `0 ^ 0 = 1` would not). The bijective minima are `Finset.inf'` over all permutations; the optimal transport minima are `sInf` over the nonempty set of nonnegative costs (equal to the paper's attained minima). Operator norms take real exponents; only $p, q \in\{1,2\}$ occur in the mission. The entrywise norm counts ordered pairs, i.e. each undirected edge twice, on both sides alike (footnote 1, p. 1).
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 1, p. 2 Eq. (1), p. 3 Eq. (2), p. 5, p. 14 (App. A)

import Mathlib
import Definitions.Def_FriezeKannan_CutDecomp_Setting

open Matrix

namespace GraphSimOT.Gaps

/-!
# Edit, local edit, cut and spectral distance of graphs of the same order, and their
# optimal transport versions

Breitung, Gervens, Grohe, *Graph Similarity Meets Optimal Transport*, arXiv:2611.05048
(held version, sha256 1cd10e91…), pp. 1–3 (Eqs. (1), (2)), p. 5 (costs, local cost),
p. 14 (matrix norms, DS*).

* Both graphs live on the common vertex type `Fin n` (the paper's `V`, `W` with `|V| = |W| = n`).
* Matrices are real; the cut norm is the published `FriezeKannan.CutDecomp.cutNorm`.
* The paper's minima are written as a `Finset.inf'` over all permutations (bijective
  distances, a genuine minimum) and as `sInf` over the nonempty set of costs of fractional
  alignments (optimal transport distances; every cost is `≥ 0`, so the set is bounded below).
-/

open Classical in
/-- The adjacency matrix `A_G ∈ {0,1}^{V×V}` of a simple graph `G` on `Fin n`, with real
entries: `A_G v v' = 1` if `vv'` is an edge and `0` otherwise. -/
noncomputable def adj {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun v v' => if G.Adj v v' then 1 else 0

/-- `A_G^π`: the adjacency matrix of `G` with rows and columns permuted according to the
bijection `π`, so that `A_G^π (π v) (π v') = A_G v v'` (p. 1). -/
noncomputable def permAdj {n : ℕ} (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun w w' => adj G (π.symm w) (π.symm w')

/-- The entrywise 1-norm `‖A‖_ed = ∑_{v,w} |A(v, w)|` (p. 14). -/
def edNorm {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, |A i j|

/-- The `ℓ_p` norm `‖x‖_p = (∑_i |x_i|^p)^{1/p}` of a real vector, for a real exponent
`p ≥ 1` (only `p ∈ {1, 2}` are used). -/
noncomputable def lpNorm {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℝ) : ℝ :=
  (∑ i, |x i| ^ p) ^ (1 / p)

/-- The operator `p → q` norm `‖A‖_{p→q} = max_{x ∈ ℝ^W, ‖x‖_p = 1} ‖A x‖_q` of
`A ∈ ℝ^{V×W}` (p. 14), written as the supremum of the (nonempty when `W` is nonempty,
bounded) set of values; it is `0` when `W` is empty. `‖A‖_p := ‖A‖_{p→p}`. -/
noncomputable def opNorm {ι κ : Type*} [Fintype ι] [Fintype κ] (p q : ℝ)
    (A : Matrix ι κ ℝ) : ℝ :=
  sSup ((fun x : κ → ℝ => lpNorm q (A *ᵥ x)) '' {x | lpNorm p x = 1})

/-! ## Bijective distances -/

/-- The edit cost `C_ed(π) = ‖A_G^π − A_H‖_ed` of a bijection `π` (p. 5). -/
noncomputable def costEdPerm {n : ℕ} (G H : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) : ℝ :=
  edNorm (permAdj G π - adj H)

/-- The cut cost `C_□(π) = ‖A_G^π − A_H‖_□` of a bijection `π` (p. 5). -/
noncomputable def costCutPerm {n : ℕ} (G H : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) : ℝ :=
  FriezeKannan.CutDecomp.cutNorm (permAdj G π - adj H)

/-- The operator cost `C_{p→q}(π) = ‖A_G^π − A_H‖_{p→q}` of a bijection `π` (p. 5). -/
noncomputable def costOpPerm {n : ℕ} (p q : ℝ) (G H : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n)) : ℝ :=
  opNorm p q (permAdj G π - adj H)

/-- `d_ed(G, H) = min_π ‖A_G^π − A_H‖_ed` over all bijections `π` (p. 1). -/
noncomputable def dEd {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).inf' Finset.univ_nonempty (costEdPerm G H)

/-- `d_□(G, H) = min_π ‖A_G^π − A_H‖_□` (p. 1). -/
noncomputable def dCut {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).inf' Finset.univ_nonempty (costCutPerm G H)

/-- `d_{p→q}(G, H) = min_π ‖A_G^π − A_H‖_{p→q}` (p. 1). -/
noncomputable def dOp {n : ℕ} (p q : ℝ) (G H : SimpleGraph (Fin n)) : ℝ :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).inf' Finset.univ_nonempty (costOpPerm p q G H)

/-- The normalised edit distance `δ_ed = d_ed / n²` (p. 1). -/
noncomputable def deltaEd {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ :=
  dEd G H / (n : ℝ) ^ 2

/-- The normalised cut distance `δ_□ = d_□ / n²` (p. 1). -/
noncomputable def deltaCut {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ :=
  dCut G H / (n : ℝ) ^ 2

/-- The normalised operator distance `δ_{p→q} = d_{p→q} / s(n)` with
`s(n) = n^{1/q + 1 − 1/p}` (p. 3); for `p = q` this is `d_p / n`. -/
noncomputable def deltaOp {n : ℕ} (p q : ℝ) (G H : SimpleGraph (Fin n)) : ℝ :=
  dOp p q G H / (n : ℝ) ^ (1 / q + 1 - 1 / p)

/-- The local edit distance `d_1 = d_{1→1}` (operator 1-norm). -/
noncomputable def d1 {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ := dOp 1 1 G H

/-- The normalised local edit distance `δ_1 = d_1 / n`. -/
noncomputable def delta1 {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ := deltaOp 1 1 G H

/-- The normalised spectral distance `δ_2 = d_{2→2} / n`. -/
noncomputable def delta2 {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ := deltaOp 2 2 G H

/-! ## Fractional alignments and optimal transport distances -/

/-- The fractional alignments `DS*(n)`: nonnegative `n × n` matrices with all row sums and all
column sums equal to `1/n` (p. 2, p. 14), i.e. couplings of the uniform distributions. -/
def DSstar (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {Q | (∀ i j, 0 ≤ Q i j) ∧ (∀ i, ∑ j, Q i j = 1 / (n : ℝ)) ∧ (∀ j, ∑ i, Q i j = 1 / (n : ℝ))}

/-- The discrepancy matrix `D_{G,H}((v, w), (v', w')) = A_G(v, v') − A_H(w, w')` (Eq. (6)). -/
noncomputable def disc {n : ℕ} (G H : SimpleGraph (Fin n)) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  fun a b => adj G a.1 b.1 - adj H a.2 b.2

/-- `x^e` with the convention `0^0 = 0` of p. 3: the value is `0` at `x = 0` (for every
exponent `e`) and the real power `x^e` otherwise. For `e > 0` it agrees with `Real.rpow`. -/
noncomputable def pow00 (x e : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ e

/-- `B(G, H, Q) = B_□ = B_ed = B_{∞→1}`: entries
`(A_G(v, v') − A_H(w, w')) · Q(v, w) · Q(v', w')` (p. 2). -/
noncomputable def Bmat {n : ℕ} (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  fun a b => Q a.1 a.2 * disc G H a b * Q b.1 b.2

/-- `B_{p→q}(G, H, Q)`: entries `Q(v, w)^{1/q} · (A_G(v, v') − A_H(w, w')) · Q(v', w')^{1−1/p}`
with the convention `0^0 = 0` (p. 3, p. 14), implemented by `pow00`. For `p = 1` the column
factor is `1` on `supp(Q)` and `0` off it. -/
noncomputable def Bpq {n : ℕ} (p q : ℝ) (G H : SimpleGraph (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  fun a b => pow00 (Q a.1 a.2) (1 / q) * disc G H a b * pow00 (Q b.1 b.2) (1 - 1 / p)

/-- The cost `C_ed(Q) = ‖B(G, H, Q)‖_ed` (p. 5; with `Q ∈ DS*` it is the objective of Eq. (1)). -/
noncomputable def costEd {n : ℕ} (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  edNorm (Bmat G H Q)

/-- The cost `C_□(Q) = ‖B(G, H, Q)‖_□` (p. 5). -/
noncomputable def costCut {n : ℕ} (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ) :
    ℝ :=
  FriezeKannan.CutDecomp.cutNorm (Bmat G H Q)

/-- The cost `C_{p→q}(Q) = ‖B_{p→q}(G, H, Q)‖_{p→q}` (p. 5; with `Q ∈ DS*` it is the objective
of Eq. (2)). -/
noncomputable def costOp {n : ℕ} (p q : ℝ) (G H : SimpleGraph (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  opNorm p q (Bpq p q G H Q)

/-- `δ^OT_ed(G, H) = min_{Q* ∈ DS*} ‖B(G, H, Q*)‖_ed` (Eq. (1)). -/
noncomputable def deltaOTEd {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ :=
  sInf (costEd G H '' DSstar n)

/-- `δ^OT_□(G, H) = min_{Q* ∈ DS*} ‖B(G, H, Q*)‖_□` (p. 2). -/
noncomputable def deltaOTCut {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ :=
  sInf (costCut G H '' DSstar n)

/-- `δ^OT_{p→q}(G, H) = min_{Q* ∈ DS*} ‖B_{p→q}(G, H, Q*)‖_{p→q}` (Eq. (2)). -/
noncomputable def deltaOTOp {n : ℕ} (p q : ℝ) (G H : SimpleGraph (Fin n)) : ℝ :=
  sInf (costOp p q G H '' DSstar n)

/-- `δ^OT_1 = δ^OT_{1→1}`. -/
noncomputable def deltaOT1 {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ := deltaOTOp 1 1 G H

/-- `δ^OT_2 = δ^OT_{2→2}`. -/
noncomputable def deltaOT2 {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ := deltaOTOp 2 2 G H

/-- The unnormalised `d^OT_ed(G, H) = min_{Q ∈ DS(n)} C_ed(Q)` (p. 5). -/
noncomputable def dOTEd {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ :=
  sInf (costEd G H '' (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ)))

/-- The unnormalised `d^OT_□(G, H) = min_{Q ∈ DS(n)} C_□(Q)` (p. 5). -/
noncomputable def dOTCut {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ :=
  sInf (costCut G H '' (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ)))

/-- The unnormalised `d^OT_{p→q}(G, H) = min_{Q ∈ DS(n)} C_{p→q}(Q)` (p. 5). -/
noncomputable def dOTOp {n : ℕ} (p q : ℝ) (G H : SimpleGraph (Fin n)) : ℝ :=
  sInf (costOp p q G H '' (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ)))

/-- `d^OT_1 = d^OT_{1→1}` (the `L` of App. D.2). -/
noncomputable def dOT1 {n : ℕ} (G H : SimpleGraph (Fin n)) : ℝ := dOTOp 1 1 G H

/-- The local cost `L_Q(v, w) = ∑_{(v', w')} |A_G(v, v') − A_H(w, w')| · Q(v', w')` (p. 5). -/
noncomputable def localCost {n : ℕ} (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (v w : Fin n) : ℝ :=
  ∑ v', ∑ w', |adj G v v' - adj H w w'| * Q v' w'

end GraphSimOT.Gaps


