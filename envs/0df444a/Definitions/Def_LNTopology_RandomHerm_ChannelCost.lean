-- Prove2me | Definitions.Def_LNTopology_RandomHerm_ChannelCost
-- name    : LNTopology_RandomHerm_ChannelCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:35.939375+00:00
-- url     : https://prove2.me/theorems/5b7b6d2a-cad8-4b40-8d2d-717c10054f49
-- title:
--   Definitions 3.4–3.5 — the induced degree d_U(i) and channel sizes s_U(i), S_U(i), on the shared model of §2, §2.2
-- statement:
--   This file defines the degree and channel sizes of Definitions 3.4–3.5 for the model of Guasoni, Huberman and Shikhelman on a finite set $V$ of nodes. The LN, the cost axioms (MO)–(SA) and the cost $c(G)$ are the shared definitions `LNTopology.Local.Model`, and (SA+) is `LNTopology.Hermetic.Model`; they are recalled below for reference.
--
--   **Lightning Networks (§2).** A *Lightning Network* (LN) is a matrix $\Lambda=(\lambda_{i,j})_{i,j\in V}$ of real net channel flows that is anti-symmetric,
--   $$\lambda_{u,v}=-\lambda_{v,u}\qquad\text{for all } u,v\in V .$$
--   The entry $\lambda_{u,v}=0$ means that $u$ and $v$ share no channel; in particular $\lambda_{u,u}=0$.
--
--   **Channel costs (§2.2).** A cost function $c:\mathbb R\to\mathbb R_+$ is required to satisfy
--   1. (MO) $c(x)>c(y)$ whenever $x>y\ge 0$;
--   2. (SY) $c(-x)=c(x)$;
--   3. (CI) $c(0)=0$;
--   4. (SA) $c(x+y)<c(x)+c(y)$ for all $x,y>0$.
--
--   For a function $g_+:\mathbb R_+\to\mathbb R_+$ that is strictly increasing, the stronger property (SA+) reads
--   $$c(kx)<\frac{k}{g_+(k)}\,c(x)\qquad\text{for all } k>1,\ x>0 .$$
--   The cost of the LN is the sum of its channel costs,
--   $$c(G)=\sum_{i>j}c(\lambda_{i,j})=\frac12\sum_{i,j\in V}c(\lambda_{i,j}).$$
--
--   **Degrees and channel sizes (Definitions 3.4–3.5).** For a set of nodes $U\subseteq V$ and a node $i$, the degree of $i$ in the subnetwork induced on $U$ is $d_U(i)=|\{j\in U:\lambda_{i,j}\neq 0\}|$. When $i$ has at least one channel into $U$, its smallest and largest channel sizes in $U$ are
--   $$s_U(i)=\min\{|\lambda_{i,j}|: j\in U,\ \lambda_{i,j}\neq 0\},\qquad S_U(i)=\max_{j\in U}|\lambda_{i,j}| .$$
--   With $U=V$ these are the paper's $d(i)$, $s(i)$ and $S(i)$.
--
--   These objects are the vocabulary of Lemma B.1 and of the probabilistic estimates in the proof of Theorem 3.9.
--
--   **Formalization Note** The nodes form an arbitrary finite type rather than $\{1,\dots,n\}$; the LN is `Λ : V → V → ℝ`. Two printed axioms are corrected because, as printed, they cannot hold: (SA) is printed for "$x>y\ge 0$", which at $y=0$ demands $c(x)<c(x)$; the version used is the one Appendix D verifies, for all $x,y>0$. (SA+) is printed for $k\in\mathbb R_+$, which at $x=0$ demands $0<0$ and fails for $k\le 1$ for the paper's own example; the version used is $k>1$, $x>0$ ("if the flow in a channel grows $n$-fold"). (MO) is stated for $x>y\ge 0$ exactly as printed. The cost uses the form $\tfrac12\sum_{i,j}$, which needs no order on $V$. When $i$ has no channel into $U$, $s_U(i)$ and $S_U(i)$ are undefined in the paper and take the junk value $0$ in Lean; every statement that uses them excludes that case.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), pp. 4–5 (PDF 5–6), §2, §2.2 (MO), (SY), (CI), (SA), (SA+) and the display of c(G); p. 7 (PDF 8), Definitions 3.4 and 3.5

import Mathlib
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_Local_Model

namespace LNTopology.RandomHerm

/-- The channel neighbours of `i` inside the node set `U`: the `j ∈ U` with `λ_{i,j} ≠ 0`. -/
noncomputable def chanNbrs {V : Type*} [DecidableEq V] (Λ : V → V → ℝ) (U : Finset V) (i : V) : Finset V :=
  {j ∈ U | Λ i j ≠ 0}

/-- The degree of `i` in the subnetwork induced on `U` (Definition 3.4, p. 7):
`d_U(i) = |{j ∈ U : λ_{i,j} ≠ 0}|`. With `U = univ` it is the paper's `d(i)`. -/
noncomputable def degOn {V : Type*} [DecidableEq V] (Λ : V → V → ℝ) (U : Finset V) (i : V) : ℕ :=
  (chanNbrs Λ U i).card

/-- `s_U(i)` (Definition 3.5, p. 7) in the subnetwork induced on `U`: the smallest `|λ_{i,j}|`
over the channels `j ∈ U` at `i`. Undefined in the paper when `i` has no channel in `U`; the
value `0` is then a junk value, which every statement using it excludes. -/
noncomputable def minChanOn {V : Type*} [DecidableEq V] (Λ : V → V → ℝ) (U : Finset V)
    (i : V) : ℝ :=
  if h : (chanNbrs Λ U i).Nonempty then (chanNbrs Λ U i).inf' h (fun j => |Λ i j|) else 0

/-- `S_U(i)` (Definition 3.5, p. 7) in the subnetwork induced on `U`: the largest `|λ_{i,j}|`
over the channels `j ∈ U` at `i` (equal to `max_{j ∈ U} |λ_{i,j}|` whenever `i` has a channel in
`U`). The value `0` when `i` has no channel in `U` is a junk value. -/
noncomputable def maxChanOn {V : Type*} [DecidableEq V] (Λ : V → V → ℝ) (U : Finset V)
    (i : V) : ℝ :=
  if h : (chanNbrs Λ U i).Nonempty then (chanNbrs Λ U i).sup' h (fun j => |Λ i j|) else 0

end LNTopology.RandomHerm


