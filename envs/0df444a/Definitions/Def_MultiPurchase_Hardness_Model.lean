-- Prove2me | Definitions.Def_MultiPurchase_Hardness_Model
-- name    : MultiPurchase_Hardness_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:25.889275+00:00
-- url     : https://prove2.me/theorems/a58ef5c1-6322-4363-9b55-e1d5eda6bfba
-- title:
--   §2–§3, eqs. (4)–(5), p. 17; App. pp. 4–5 — BundleMVL-2 instances, R₂(C), θ, r̂, the decision language, and the Max-Cut construction
-- statement:
--   This file fixes the objects of the hardness result (Theorem 1) of Tulabandhula, Sinha, Karra and Patidar on the BundleMVL-2 multi-purchase choice model.
--
--   **Instances.** The products are $W=\{1,\dots,n\}$. A BundleMVL-2 instance consists of revenues $r_i$, singleton weights $V_{\{i\}}$, pair weights $V_{\{i,j\}}$ ($i<j$) and a no-purchase weight $v_0$, all rational. It is **well formed** if
--   1. $r_i>0$ for every product $i$;
--   2. $V_{\{i\}}\ge 0$ and $V_{\{i,j\}}\ge 0$ for all $i<j$;
--   3. $v_0>0$.
--
--   A customer shown the recommendation set $C\subseteq W$ buys a nonempty bundle of at most two products of $C$, or nothing (the no-purchase option, of weight $v_0$).
--
--   **Expected revenue, eq. (4).** For $C\subseteq W$,
--   $$R_2(C)=\frac{\sum_{i\in C} r_iV_{\{i\}}+\sum_{i\in C}\sum_{j\in C,\,j>i}(r_i+r_j)V_{\{i,j\}}}{v_0+\sum_{i\in C}V_{\{i\}}+\sum_{i\in C}\sum_{j\in C,\,j>i}V_{\{i,j\}}}.$$
--   The file also defines $x^C_i=1$ if $i\in C$ and $0$ otherwise, $\theta_{ii}=V_{\{i\}}$, $\theta_{ij}=V_{\{i,j\}}/2$ ($i\ne j$), $\hat r_{ii}=r_i$ and $\hat r_{ij}=r_i+r_j$ ($i\neq j$).
--
--   **The decision problem.** The decision version of the unconstrained problem (5), $\max_{C\in 2^W}R_2(C)$, asks for a threshold $\kappa$ whether the instance is well formed and some $C\subseteq W$ has $R_2(C)\ge\kappa$. An instance with threshold is coded as a string over the alphabet $\{0,1,-,\#\}$: $n$, then $r_1,\dots,r_n$, then $V_{\{1\}},\dots,V_{\{n\}}$, then the pair weights $V_{\{i,j\}}$ with $i<j$ row by row, then $v_0$ and $\kappa$; a rational number is written as its reduced numerator and its denominator in binary. The **BundleMVL-2 language** is the set of codes of yes-instances.
--
--   **The construction of the proof of Theorem 1.** For a simple graph $G$ on the nodes $\{1,\dots,m\}$ with degree vector $\mathbf d$ and adjacency matrix $A'$, the $(m+1)\times(m+1)$ matrix
--   $$Q=\begin{pmatrix}0&\mathbf d^\top/2\\ \mathbf d/2&-A'\end{pmatrix}$$
--   is indexed from $0$, so the hub $0$ is the first row and node $i$ is row $i$. For numbers $\kappa,r_0,\dots,r_m$ the file defines $\theta_{ij}=q_{ij}/(r_i+r_j-\kappa)$, $0\le i,j\le m$. The reduction instance of a Max-Cut instance $(G,M)$ has the $m+1$ products $0,\dots,m$, threshold $\kappa=1$, revenues $r_0=2$ and $r_i=\tfrac14-\tfrac{i}{8(m+1)}$ for $1\le i\le m$ (so $r_0>\kappa$ and $\kappa/2>r_1>\dots>r_m>0$), weights $V_{\{i\}}=0$, $V_{\{i,j\}}=2\theta_{ij}$, and $v_0=M/\kappa=M$.
--
--   These are the objects of the NP-completeness proof of Theorem 1, a reduction from Max-Cut.
--
--   **Formalization Note** Products are `Fin n`, 0-based. In the reduction the hub is index `0 : Fin (m+1)` and graph node `i : Fin m` is product `i.succ`; the revenues of the reduction are written for the 0-based node index, $r_{i+1}=1/4-(i+1)/(8(m+1))$. Only the pair weights `V2 i j` with `i < j` are read (by $R_2$, by $\theta$ through `min`/`max`, and by the code), so the code determines everything the yes-predicate depends on. The model writes $V_S=\exp(\cdot)>0$; the formalization allows $V\ge 0$, as the paper does on p. 10 ($\beta_{ij}=-\infty$) and in its own reduction ($V_{\{i\}}=\theta_{ii}=0$). The empty bundle is the no-purchase option, so $R_2(\emptyset)=0$. Graphs are Mathlib simple graphs, so they have no self-loops and $G'=G$; adjacency is decided classically.
-- source:
--   Tulabandhula, Sinha, Karra & Patidar, Multi-Purchase Behavior: Modeling, Estimation and Optimization, arXiv:2006.08055v2, pp. 8–10 (PDF 8–10), §2 eqs. (1)–(2); p. 17 (PDF 17), §3 eqs. (4)–(5); Appendix p. 1 (PDF 33), A.1; proof of Theorem 1, Appendix pp. 4–5 (PDF 36–37), matrix Q and θij

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace MultiPurchase.Hardness

open CookPvsNP ProjSchedTW.Complexity

/-! # The BundleMVL-2 revenue problem and the Max-Cut construction
(Tulabandhula, Sinha, Karra & Patidar, arXiv:2006.08055v2, §2, §3 eqs. (4)–(5), Appendix B.1)

Products are `Fin n` (the paper's `W = {1, …, n}`, 0-based). A customer shown the recommendation set
`C` buys a nonempty bundle `S ⊆ C` with `|S| ≤ 2`; the empty bundle is the no-purchase option, of
weight `v0`. All parameters are rational. -/

/-- A BundleMVL-2 instance on the products `Fin n`: revenues `r i`, singleton weights `V1 i = V{i}`,
pair weights `V2 i j = V{i,j}` (only the entries with `i < j` are ever read) and the no-purchase
weight `v0`. -/
structure Instance where
  n : ℕ
  r : Fin n → ℚ
  V1 : Fin n → ℚ
  V2 : Fin n → Fin n → ℚ
  v0 : ℚ

/-- Standing conditions of the model: `rᵢ > 0` (p. 17), weights `V{i} ≥ 0` and `V{i,j} ≥ 0` for
`i < j` (a weight may be `0`, p. 10), and `v0 > 0`. -/
def Instance.WellFormed (I : Instance) : Prop :=
  (∀ i, 0 < I.r i) ∧ (∀ i, 0 ≤ I.V1 i) ∧ (∀ i j, i < j → 0 ≤ I.V2 i j) ∧ 0 < I.v0

/-- The expected revenue `R₂(C)` of the recommendation set `C`, eq. (4), first form:
`(∑_{i∈C} rᵢ V{i} + ∑_{i∈C} ∑_{j∈C, j>i} (rᵢ + rⱼ) V{i,j}) /
 (v0 + ∑_{i∈C} V{i} + ∑_{i∈C} ∑_{j∈C, j>i} V{i,j})`. -/
def Instance.R2 (I : Instance) (C : Finset (Fin I.n)) : ℚ :=
  (∑ i ∈ C, I.r i * I.V1 i +
      ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), (I.r i + I.r j) * I.V2 i j) /
    (I.v0 + ∑ i ∈ C, I.V1 i + ∑ i ∈ C, ∑ j ∈ C.filter (fun j => i < j), I.V2 i j)

/-- `θᵢⱼ` of eq. (4): `θᵢᵢ = V{i}` and `θᵢⱼ = V{i,j}/2` for `i ≠ j` (the pair weight is read as
`V2 (min i j) (max i j)`). -/
def Instance.theta (I : Instance) (i j : Fin I.n) : ℚ :=
  if i = j then I.V1 i else I.V2 (min i j) (max i j) / 2

/-- `r̂ᵢⱼ` of eq. (4): `r̂ᵢᵢ = rᵢ` and `r̂ᵢⱼ = rᵢ + rⱼ` for `i ≠ j`. -/
def Instance.rhat (I : Instance) (i j : Fin I.n) : ℚ :=
  if i = j then I.r i else I.r i + I.r j

/-- The indicator `x^C_i` of eq. (4): `1` if `i ∈ C`, else `0`. -/
def xC {n : ℕ} (C : Finset (Fin n)) (i : Fin n) : ℚ := if i ∈ C then 1 else 0

/-- The decision version of the unconstrained problem (5) with threshold `κ`: the instance is
well formed and some recommendation set `C ⊆ W` has `R₂(C) ≥ κ`. -/
def Yes (I : Instance) (kappa : ℚ) : Prop :=
  I.WellFormed ∧ ∃ C : Finset (Fin I.n), kappa ≤ I.R2 C

/-- A rational number in binary: its (normalized) numerator, then its denominator. -/
def encRat (q : ℚ) : List BSym := encInt q.num ++ encNat q.den

/-- A list of rationals, one after the other. -/
def encRats (qs : List ℚ) : List BSym := qs.flatMap encRat

/-- The code of an instance with threshold `κ`: `n`, the list `r`, the list `V{i}`, the pair
weights `V{i,j}` with `i < j` row by row, then `v0` and `κ`. -/
def code (I : Instance) (kappa : ℚ) : List BSym :=
  encNat I.n ++ encRats (List.ofFn I.r) ++ encRats (List.ofFn I.V1) ++
    encRats ((List.finRange I.n).flatMap fun i =>
      ((List.finRange I.n).filter (fun j => i < j)).map fun j => I.V2 i j) ++
    encRat I.v0 ++ encRat kappa

/-- The language of the decision version of (5): codes of yes-instances. -/
def bundleLang : Lang BSym :=
  { w | ∃ (I : Instance) (kappa : ℚ), Yes I kappa ∧ w = code I kappa }

/-! ## The construction of the proof of Theorem 1 (Appendix pp. 4–5) -/

open Classical in
/-- The degree `dᵢ` of node `i` in the simple graph `G` (a simple graph has no self-loops, so
`G′ = G`). -/
noncomputable def nodeDeg {m : ℕ} (G : SimpleGraph (Fin m)) (i : Fin m) : ℕ :=
  (Finset.univ.filter fun k => G.Adj i k).card

open Classical in
/-- The `(m+1) × (m+1)` matrix `Q = (0, d/2; d/2, −A′)` of Appendix p. 4, indexed from `0`:
`q₀₀ = 0`, `q₀,ᵢ₊₁ = qᵢ₊₁,₀ = dᵢ/2`, and `qᵢ₊₁,ⱼ₊₁ = −1` if `i, j` are adjacent in `G`, else `0`.
Node `i : Fin m` of the graph is index `i.succ`. -/
noncomputable def hubQ {m : ℕ} (G : SimpleGraph (Fin m)) (i j : Fin (m + 1)) : ℚ :=
  Fin.cases (Fin.cases 0 (fun j' => (nodeDeg G j' : ℚ) / 2) j)
    (fun i' => Fin.cases ((nodeDeg G i' : ℚ) / 2) (fun j' => if G.Adj i' j' then -1 else 0) j) i

/-- The nodes `C̃ = C ∖ {0}` of the graph selected by `C ⊆ {0, …, m}`, as a subset of `Fin m`. -/
def nodesOf {m : ℕ} (C : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter fun i => i.succ ∈ C

/-- `θᵢⱼ = qᵢⱼ / (rᵢ + rⱼ − κ)`, `0 ≤ i, j ≤ m` (Appendix p. 5). -/
noncomputable def redTheta {m : ℕ} (G : SimpleGraph (Fin m)) (kappa : ℚ) (r : Fin (m + 1) → ℚ)
    (i j : Fin (m + 1)) : ℚ :=
  hubQ G i j / (r i + r j - kappa)

/-- The revenues chosen in the reduction, for `κ = 1`: `r₀ = 2` and
`rᵢ = 1/4 − i/(8(m+1))` for the nodes `i = 1, …, m`, so that `r₀ > κ` and
`κ/2 > r₁ > ⋯ > r_m > 0`. -/
def redRev (m : ℕ) : Fin (m + 1) → ℚ :=
  Fin.cases 2 (fun i => 1 / 4 - ((i : ℚ) + 1) / (8 * ((m : ℚ) + 1)))

/-- The BundleMVL-2 instance of the reduction from the Max-Cut instance `(G, M)`, for the
threshold `κ = 1`: products `0, …, m`, revenues `redRev m`, `V{i} = θᵢᵢ = 0`, `V{i,j} = 2θᵢⱼ`,
and `v0 = M/κ = M`. -/
noncomputable def reductionInstance {m : ℕ} (G : SimpleGraph (Fin m)) (M : ℕ) : Instance where
  n := m + 1
  r := redRev m
  V1 := fun _ => 0
  V2 := fun i j => 2 * redTheta G 1 (redRev m) i j
  v0 := M

end MultiPurchase.Hardness


