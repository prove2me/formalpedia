-- Prove2me | Definitions.Def_FTConnOracle_Main_Expander
-- name    : FTConnOracle_Main_Expander
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:28:28.386925+00:00
-- url     : https://prove2.me/theorems/47c05dae-6890-43b6-be71-1ea761fb173b
-- title:
--   Bipartite expanders with (4.1), expander sketches b_v and s_v, the sketched cut matrix Q(S), the sets X_i, Y_i, and Test-Cut
-- statement:
--   Let $B$ be a bipartite graph with left side $[n]$ and right side $[r]$. For $U\subseteq[n]$, $\Gamma(U)$ is the set of right vertices adjacent to a vertex of $U$; for $j\in[r]$, $T_j=\{v\in[n]:B_{jv}=1\}$ is the set of left neighbours of $j$. $B$ is **left-regular of degree $\ell$** if every left vertex has exactly $\ell$ neighbours, and it has the **expansion property (4.1) for the parameter $t$** if
--
--   $$|\Gamma(U)|\ \ge\ \tfrac34\,\ell\,|U|\qquad\text{for every }U\subseteq[n]\text{ with }|U|\le 2t.\qquad(4.1)$$
--
--   The setting of §4.1 for the parameter $t$ is: $B$ left-regular of degree $\ell\ge1$ with (4.1).
--
--   The **sketch** of $v$ is $b_v\in\{0,1\}^r\subseteq\mathbb Z^r$, the $v$-th column of the $r\times n$ incidence matrix of $B$. For a graph $G$ on $[n]$ the **neighbour sketch** of $v$ is $s_v=\sum_{(u,v)\in G}b_u\in\mathbb Z^r$, the sum of the columns of the $G$-neighbours of $v$.
--
--   For $S\subseteq[n]$, the **sketched cut matrix** (Definition 4.1) is the integer $r\times r$ matrix
--
--   $$Q(S)=\sum_{(u,v)\in\delta_G(S),\ u\in S} b_u b_v^{\mathsf T},\qquad(4.2)$$
--
--   the sum over ordered pairs $(u,v)$ with $u\in S$, $v\notin S$, $\{u,v\}\in E(G)$. $P_{i,j}$ is the set of paths $i\xrightarrow{B}x\xrightarrow{G}y\xrightarrow{B}j$ with $x\in S$, $y\notin S$. For $i\in[r]$, $X_i\subseteq S$ is the set of vertices of $S$ with a $G$-neighbour in $T_i\setminus S$, and $Y_i\subseteq S^c$ the set of vertices of $S^c$ with a $G$-neighbour in $T_i\cap S$.
--
--   **Test-Cut** (Algorithm 1) takes $S\subseteq[n]$, a failure set $F$, the sketches $\{(b_v,s_v)\}_{v\in S}$ and $\{(b_u,b_v)\}_{\{u,v\}\in F}$, computes
--
--   $$Q_F(S)=\sum_{u\in S} b_u s_u^{\mathsf T}-\sum_{\substack{u\in S,\ v\in[n]\\ (u,v)\in F}} b_u b_v^{\mathsf T},$$
--
--   and returns $1$ if $Q_F(S)$ is symmetric and $0$ otherwise. The second sum runs over the ordered pairs $(u,v)$ with $u\in S$ and $\{u,v\}\in F$, so an $F$-edge with both endpoints in $S$ contributes both orientations.
--
--   These objects carry the cut-amplification argument of §4.1 (Fact 4.1, Observation 4.1, Lemmas 4.2–4.4, Claim 4.1).
--
--   **Formalization Note.** $B$ is `B : Fin n → Finset (Fin r)` (the right neighbourhood of each left vertex); `nbhd B U` $=\Gamma(U)$, `leftNbrs B j` $=T_j$, `col B v` $=b_v$, `nbrSketch B G v` $=s_v$, `cutMatrix B G S` $=Q(S)$. A path in $P_{i,j}$ is determined by its middle edge and is recorded as the pair $(x,y)$ (`pathSet`). `testCut b sk S F` is a `Bool` (`true` = 1) computed from the arrays `b`, `sk`; it reads only the entries listed above. Symmetric means $Q^{\mathsf T}=Q$ exactly.
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), pp. 16–19 (PDF 18–21): Lemma 4.1 (4.1), 'Sketch', Definition 4.1 (4.2), Observation 4.1, the sets X_i, Y_i (p. 17), Algorithm 1 (Test-Cut)

import Mathlib
import Definitions.Def_FTConnOracle_Main_Oracle

namespace FTConnOracle.Main

/-!
# Bipartite expanders, expander sketches, the sketched cut matrix and Test-Cut

Parter, Tzalik, *Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space*,
STOC 2027 submission (manuscript sha256 168306b7…), pp. 16–19 (PDF 18–21): Lemma 4.1 (4.1),
the sketches `b_v`, `s_v`, Definition 4.1 (4.2), Observation 4.1, the sets `X_i`, `Y_i`, and
Algorithm 1 (Test-Cut).

* A bipartite graph `B` with left side `[n]` and right side `[r]` is given by the right
  neighbourhoods `B v ⊆ [r]` of the left vertices `v`. `nbhd B U` is `Γ(U)`.
* `col B v ∈ {0,1}^r ⊆ ℤ^r` is the column `b_v` of the `r × n` incidence matrix, and
  `leftNbrs B j` is `T_j = {v : B_{jv} = 1}`.
* Sketches are integer vectors and the sketched matrices integer `r × r` matrices; "symmetric"
  means `Q = Qᵀ` exactly.
-/

/-- `Γ(U)`: the set of right vertices adjacent in `B` to some vertex of `U`. -/
def nbhd {n r : ℕ} (B : Fin n → Finset (Fin r)) (U : Finset (Fin n)) : Finset (Fin r) :=
  U.biUnion B

/-- Every left vertex of `B` has degree exactly `ℓ`. -/
def IsLeftRegular {n r : ℕ} (B : Fin n → Finset (Fin r)) (ℓ : ℕ) : Prop :=
  ∀ v : Fin n, (B v).card = ℓ

/-- Property (4.1): `|Γ(U)| ≥ (3/4) ℓ |U|` for every `U ⊆ [n]` with `|U| ≤ 2t`. -/
def HasExpansion {n r : ℕ} (B : Fin n → Finset (Fin r)) (ℓ t : ℕ) : Prop :=
  ∀ U : Finset (Fin n), U.card ≤ 2 * t →
    (3 / 4 : ℝ) * (ℓ : ℝ) * (U.card : ℝ) ≤ ((nbhd B U).card : ℝ)

/-- The setting of §4.1 for the parameter `t`: all left vertices of `B` have the same degree
`ℓ ≥ 1`, and `B` satisfies (4.1). -/
def IsLosslessExpander {n r : ℕ} (B : Fin n → Finset (Fin r)) (ℓ t : ℕ) : Prop :=
  1 ≤ ℓ ∧ IsLeftRegular B ℓ ∧ HasExpansion B ℓ t

/-- `b_v`: the `v`-th column of the incidence matrix of `B`, a `0/1` vector in `ℤ^r`. -/
def col {n r : ℕ} (B : Fin n → Finset (Fin r)) (v : Fin n) : Fin r → ℤ :=
  fun j => if j ∈ B v then 1 else 0

/-- `T_j = {v ∈ [n] : B_{jv} = 1}`: the left neighbours of the right vertex `j`. -/
def leftNbrs {n r : ℕ} (B : Fin n → Finset (Fin r)) (j : Fin r) : Finset (Fin n) :=
  Finset.univ.filter fun v => j ∈ B v

open Classical in
/-- The neighbour sketch `s_v = ∑_{(u,v) ∈ G} b_u ∈ ℤ^r`: the sum of the columns of the
`G`-neighbours of `v`. -/
noncomputable def nbrSketch {n r : ℕ} (B : Fin n → Finset (Fin r)) (G : SimpleGraph (Fin n))
    (v : Fin n) : Fin r → ℤ :=
  ∑ u ∈ Finset.univ.filter (fun u => G.Adj u v), col B u

open Classical in
/-- Definition 4.1, (4.2): the sketched cut matrix `Q(S) = ∑_{(u,v) ∈ δ_G(S), u ∈ S} b_u b_vᵀ`,
the sum over the ordered pairs `(u, v)` with `u ∈ S`, `v ∉ S` and `{u, v} ∈ E(G)`. -/
noncomputable def cutMatrix {n r : ℕ} (B : Fin n → Finset (Fin r)) (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Matrix (Fin r) (Fin r) ℤ :=
  ∑ u ∈ S, ∑ v ∈ Finset.univ.filter (fun v => v ∉ S ∧ G.Adj u v),
    Matrix.vecMulVec (col B u) (col B v)

open Classical in
/-- Observation 4.1: `P_{i,j}`, the paths `i →B x →G y →B j` with `x ∈ S` and `y ∈ Sᶜ`. Such a
path is determined by its middle edge, so it is recorded as the pair `(x, y)`: `x ∈ T_i ∩ S`,
`y ∈ T_j ∖ S`, `{x, y} ∈ E(G)`. -/
noncomputable def pathSet {n r : ℕ} (B : Fin n → Finset (Fin r)) (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (i j : Fin r) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => i ∈ B p.1 ∧ p.1 ∈ S ∧ G.Adj p.1 p.2 ∧ p.2 ∉ S ∧ j ∈ B p.2

open Classical in
/-- `X_i ⊆ S`: the vertices of `S` with a `G`-neighbour in `T_i ∩ Sᶜ`. -/
noncomputable def Xset {n r : ℕ} (B : Fin n → Finset (Fin r)) (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (i : Fin r) : Finset (Fin n) :=
  S.filter fun x => ∃ y, y ∈ leftNbrs B i ∧ y ∉ S ∧ G.Adj x y

open Classical in
/-- `Y_i ⊆ Sᶜ`: the vertices of `Sᶜ` with a `G`-neighbour in `T_i ∩ S`. -/
noncomputable def Yset {n r : ℕ} (B : Fin n → Finset (Fin r)) (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (i : Fin r) : Finset (Fin n) :=
  Finset.univ.filter fun y => y ∉ S ∧ ∃ x, x ∈ leftNbrs B i ∧ x ∈ S ∧ G.Adj y x

open Classical in
/-- Algorithm 1, line 1: `Q_F(S) = ∑_{u ∈ S} b_u s_uᵀ − ∑_{u ∈ S, v ∈ [n], (u,v) ∈ F} b_u b_vᵀ`,
computed from the column sketches `b` and the neighbour sketches `sk` alone. The second sum runs
over the ordered pairs `(u, v)` with `u ∈ S` and `{u, v} ∈ F` (an `F`-edge inside `S` contributes
both orientations). Only `b u`, `sk u` for `u ∈ S` and `b v` for endpoints `v` of `F`-edges are
read. -/
noncomputable def testMatrix {n r : ℕ} (b sk : Fin n → Fin r → ℤ) (S : Finset (Fin n))
    (F : Finset (Sym2 (Fin n))) : Matrix (Fin r) (Fin r) ℤ :=
  (∑ u ∈ S, Matrix.vecMulVec (b u) (sk u)) -
    ∑ u ∈ S, ∑ v ∈ Finset.univ.filter (fun v => s(u, v) ∈ F), Matrix.vecMulVec (b u) (b v)

open Classical in
/-- Algorithm 1 (Test-Cut): returns `1` (`true`) if `Q_F(S)` is symmetric and `0` (`false`)
otherwise. -/
noncomputable def testCut {n r : ℕ} (b sk : Fin n → Fin r → ℤ) (S : Finset (Fin n))
    (F : Finset (Sym2 (Fin n))) : Bool :=
  decide ((testMatrix b sk S F).transpose = testMatrix b sk S F)

end FTConnOracle.Main


