-- Prove2me | Definitions.Def_HZFixp_Main_Market
-- name    : HZFixp_Main_Market
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:52:46.201172+00:00
-- url     : https://prove2.me/theorems/39b1bfb3-5525-4215-bd7f-09acd294442a
-- title:
--   §3.4.1 — the HZ market built from a Reciprocal VI instance, demand duals (50) and normalized prices
-- statement:
--   From a Reciprocal VI instance with $k$ nodes and $W$ unit edges, §3.4.1 builds an HZ market. Node $i$ has a **low-good group** for every outgoing unit edge $e$ (parameter $\lambda_e$), an auxiliary low group with parameter $a_i$, and one **high-good group**; there is one global group of **reference goods**. Writing each low parameter $\lambda_{it} = P_{it}/Q_{it}$ in lowest terms, (14) sets $\ell_0 = 2W+2$, $L_{it} = \ell_0 Q_{it}$ goods in low group $it$ and $H_i = \ell_0 \sum_t P_{it}$ high goods at $i$; with $S_i = H_i + \sum_t L_{it}$, $S^\star = \max_i S_i$:
--   $$B_0 = 3S^\star,\qquad N = kB_0 + W,\qquad S_R = N - \sum_i S_i .$$
--   There are $B_0$ **node agents** per node, one **edge agent** $w_e$ per unit edge, and $S_R$ reference goods: $N$ agents and $N$ unit-supply goods. A node-$i$ agent values its own low group $t$ at $(b_i-\lambda_{it})/(b_i+1)$, reference goods at $b_i/(b_i+1)$, its own high goods at $1$ and everything else at $0$ (Table 4). The edge agent of $e : i \to j$ values the goods of its low group at $1-\varepsilon_w$, $\varepsilon_w = [2(1+b^\star)]^{-1}$, $b^\star = \max_i b_i$, its **selected high goods** at $j$ at $1$, and everything else at $0$. High good number $0$ at each $D_j$ is **reserved** ($h^\star_j$): the designated edge's agent selects only $h^\star_j$; every other edge agent entering $D_j$ selects all of $D_j$'s high goods but $h^\star_j$; elsewhere all high goods at $j$ are selected.
--
--   The file also fixes the objects of the market lemmas: the prices (15) $\pi_R = 1$, $\pi^+_i = 1+1/r_i$, $\pi^-_{it} = 1-\lambda_{it}/r_i$; an **optimal bundle** at prices $\pi$ (a unit bundle $y \ge 0$ with $\pi\cdot y \le 1$ maximizing $v\cdot y$ among such); the **demand dual** (50) $\min\{\gamma+\mu : \gamma \ge 0,\ \mu \in \mathbb{R},\ v_j \le \gamma \pi_j + \mu\ \forall j\}$; the **normalized prices** $(\pi - m)/(1-m)$, $m = \min_g \pi_g$; $Z_i$, the quantity of other nodes' goods consumed by node-$i$ agents, and $q_i$, the quantity of node-$i$ goods consumed by edge agents.
--
--   **Formalization Note.** Agents and goods are typed (`MAgent`, `MGood`: low goods by group and copy, high goods by node and copy, reference goods), not numbered $1..N$; low groups are indexed by edges (at their tail) and nodes (the auxiliary group). The minimum price of a market without goods is taken to be $0$.
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), pp. 22–24 (PDF 24–26), §3.4.1, (14), Table 4, Figure 8; p. 24 (PDF 26), (15); p. 57 (PDF 59), (50); p. 58–59 (PDF 60–61), normalized prices, Z_i, q_i

import Mathlib
import Definitions.Def_FixpReciprocal_RealSearch
import Definitions.Def_HZFixp_Main_ReciprocalVI

namespace HZFixp.Main

open FixpReciprocal

/-! # The market of §3.4.1 built from a Reciprocal VI instance

Liu, Tao, Yan, *Settling the Complexity of Hylland–Zeckhauser Equilibria*, arXiv:2606.06317 (held
version later than v2, sha256 36e91522…af1c), pp. 22–24 (PDF 24–26): good groups, (14), the
populations `B_0, N, S_R`, Table 4, the edge-agent rows, the reserved high goods `h⋆_j`, Figure 8;
p. 57 (PDF 59): the demand dual (50); p. 58 (PDF 60): the normalized prices; p. 59 (PDF 61):
`Z_i`, `q_i`.

Low-good groups are indexed by `Fin W ⊕ Fin k`: `inl e` is the group of the unit edge `e : i → j`
at its tail `i` (parameter `λ_e`), `inr i` the auxiliary group at node `i` (parameter `a_i`). -/

/-- The number `W` of unit edges. -/
def RVIData.W (D : RVIData) : ℕ := D.edges.length

/-- The low-good groups. -/
abbrev LowGroup (D : RVIData) : Type := Fin D.W ⊕ Fin D.k

/-- The node of a low-good group. -/
def RVIData.groupNode (D : RVIData) : LowGroup D → ℕ
  | .inl e => (D.edges.getD e.val (0, 0, 0)).1
  | .inr i => i.val

/-- The parameter `λ_{it}` of a low-good group: `λ_e` for an edge group, `a_i` for the auxiliary
group. -/
def RVIData.groupParam (D : RVIData) : LowGroup D → ℚ
  | .inl e => (D.edges.getD e.val (0, 0, 0)).2.2
  | .inr i => D.lo i.val

/-- `ℓ_0 = 2W + 2` (14). -/
def RVIData.ell0 (D : RVIData) : ℕ := 2 * D.W + 2

/-- `L_{it} = ℓ_0 Q_{it}` (14), with `λ_{it} = P_{it}/Q_{it}` in lowest terms. -/
def RVIData.lowSize (D : RVIData) (g : LowGroup D) : ℕ := D.ell0 * (D.groupParam g).den

/-- `H_i = ℓ_0 ∑_t P_{it}` (14). -/
def RVIData.highSize (D : RVIData) (i : Fin D.k) : ℕ :=
  D.ell0 * ∑ g ∈ Finset.univ.filter (fun g : LowGroup D => D.groupNode g = i.val),
    (D.groupParam g).num.toNat

/-- `S_i = H_i + ∑_t L_{it}`. -/
def RVIData.nodeSupply (D : RVIData) (i : Fin D.k) : ℕ :=
  D.highSize i + ∑ g ∈ Finset.univ.filter (fun g : LowGroup D => D.groupNode g = i.val),
    D.lowSize g

/-- `B_0 = 3S⋆`, `S⋆ = max_i S_i`. -/
def RVIData.B0 (D : RVIData) : ℕ := 3 * Finset.univ.sup D.nodeSupply

/-- `N = kB_0 + W`. -/
def RVIData.N (D : RVIData) : ℕ := D.k * D.B0 + D.W

/-- `S_R = N − ∑_i S_i`. -/
def RVIData.SR (D : RVIData) : ℕ := D.N - ∑ i, D.nodeSupply i

/-- **The goods:** `L_{it}` low goods in each low group, `H_i` high goods at each node, `S_R`
reference goods, each with unit supply. -/
abbrev MGood (D : RVIData) : Type :=
  (Σ g : LowGroup D, Fin (D.lowSize g)) ⊕ (Σ i : Fin D.k, Fin (D.highSize i)) ⊕ Fin D.SR

/-- **The agents:** `B_0` node agents for each node and one edge agent `w_e` for each unit edge. -/
abbrev MAgent (D : RVIData) : Type := (Fin D.k × Fin D.B0) ⊕ Fin D.W

/-- The node agent number `c` of node `i`. -/
abbrev nodeAgent {D : RVIData} (i : Fin D.k) (c : Fin D.B0) : MAgent D := .inl (i, c)

/-- The edge agent `w_e`. -/
abbrev edgeAgent {D : RVIData} (e : Fin D.W) : MAgent D := .inr e

/-- The node a good belongs to (`none` for a reference good). -/
def RVIData.goodNode (D : RVIData) : MGood D → Option ℕ
  | .inl ⟨g, _⟩ => some (D.groupNode g)
  | .inr (.inl ⟨i, _⟩) => some i.val
  | .inr (.inr _) => none

/-- A high good at node `i`. -/
def RVIData.IsHighAt (D : RVIData) (i : ℕ) : MGood D → Prop
  | .inr (.inl ⟨i', _⟩) => i'.val = i
  | _ => False

/-- A high good. -/
def RVIData.IsHigh (D : RVIData) (g : MGood D) : Prop := ∃ i, D.IsHighAt i g

/-- A reference good. -/
def RVIData.IsRef (D : RVIData) : MGood D → Prop
  | .inr (.inr _) => True
  | _ => False

/-- A low good of node `i` (in any of its low groups). -/
def RVIData.IsLowAt (D : RVIData) (i : ℕ) : MGood D → Prop
  | .inl ⟨g, _⟩ => D.groupNode g = i
  | _ => False

/-- **The reserved high good `h⋆_j`:** high good number `0` of a node `D_j` of a designated pair. -/
def RVIData.IsReserved (D : RVIData) : MGood D → Prop
  | .inr (.inl ⟨i, c⟩) => c.val = 0 ∧ ∃ p ∈ D.pairs, p.2.1 = i.val
  | _ => False

/-- The edge `e` is the designated edge of some designated pair. -/
def RVIData.IsDesignated (D : RVIData) (e : Fin D.W) : Prop := ∃ p ∈ D.pairs, p.2.2 = e.val

/-- The low goods of the group of edge `e`. -/
def RVIData.IsEdgeLow (D : RVIData) (e : Fin D.W) : MGood D → Prop
  | .inl ⟨.inl e', _⟩ => e' = e
  | _ => False

/-- **The selected high goods of edge `e : i → j`:** among the high goods at `j`, only `h⋆` if `e`
is designated; all except a reserved good otherwise. -/
def RVIData.IsEdgeHigh (D : RVIData) (e : Fin D.W) (g : MGood D) : Prop :=
  D.IsHighAt (D.edges.getD e.val (0, 0, 0)).2.1 g ∧
    (D.IsDesignated e → D.IsReserved g) ∧ (¬ D.IsDesignated e → ¬ D.IsReserved g)

/-- `b⋆ = max_i b_i`. -/
def RVIData.bStar (D : RVIData) : ℚ := (D.intervals.map Prod.snd).foldr max 0

/-- `ε_w = [2(1 + b⋆)]^{−1}`. -/
def RVIData.epsW (D : RVIData) : ℚ := 1 / (2 * (1 + D.bStar))

open Classical in
/-- **The utility row of a node-`i` agent (Table 4):** `(b_i − λ_{it})/(b_i + 1)` for its own low
group `t`, `b_i/(b_i + 1)` for reference goods, `1` for its own high goods (reserved ones included),
`0` for goods at other nodes. -/
noncomputable def RVIData.nodeUtil (D : RVIData) (i : Fin D.k) : MGood D → ℝ
  | .inl ⟨g, _⟩ =>
      if D.groupNode g = i.val then
        (((D.hi i.val - D.groupParam g) / (D.hi i.val + 1) : ℚ) : ℝ) else 0
  | .inr (.inl ⟨i', _⟩) => if i' = i then 1 else 0
  | .inr (.inr _) => ((D.hi i.val / (D.hi i.val + 1) : ℚ) : ℝ)

open Classical in
/-- **The utility row of the edge agent `w_e`:** `1 − ε_w` for the goods of its low group, `1` for
its selected high goods, `0` for everything else (reference goods included). -/
noncomputable def RVIData.edgeUtil (D : RVIData) (e : Fin D.W) (g : MGood D) : ℝ :=
  if D.IsEdgeLow e g then ((1 - D.epsW : ℚ) : ℝ) else if D.IsEdgeHigh e g then 1 else 0

/-- **The utility matrix of the market of §3.4.1.** -/
noncomputable def RVIData.mUtil (D : RVIData) : MAgent D → MGood D → ℝ
  | .inl (i, _) => D.nodeUtil i
  | .inr e => D.edgeUtil e

/-- **The prices (15)** given node values `r`: `π_R = 1`, `π⁺_i = 1 + 1/r_i`,
`π⁻_{it} = 1 − λ_{it}/r_i`. -/
noncomputable def RVIData.price15 (D : RVIData) (r : Fin D.k → ℝ) : MGood D → ℝ
  | .inl ⟨g, _⟩ => 1 - (D.groupParam g : ℝ) / lookup r (D.groupNode g)
  | .inr (.inl ⟨i, _⟩) => 1 + 1 / r i
  | .inr (.inr _) => 1

/-- **An optimal bundle** of an agent with utility row `v` at prices `π`: a unit bundle `y ∈ Δ`
with `π · y ≤ 1` whose utility `v · y` is the largest among affordable unit bundles, `OPT(π)` of
(1). -/
def IsOptBundle {G : Type} [Fintype G] (v π y : G → ℝ) : Prop :=
  (∀ g, 0 ≤ y g) ∧ ∑ g, y g = 1 ∧ ∑ g, π g * y g ≤ 1 ∧
    ∀ y' : G → ℝ, (∀ g, 0 ≤ y' g) → ∑ g, y' g = 1 → ∑ g, π g * y' g ≤ 1 →
      ∑ g, v g * y' g ≤ ∑ g, v g * y g

/-- A feasible point `(γ, µ)` of the **demand dual (50)**: `γ ≥ 0`, `v_j ≤ γπ_j + µ` for all `j`. -/
def IsDemandDual {G : Type} [Fintype G] (v π : G → ℝ) (γ μ : ℝ) : Prop :=
  0 ≤ γ ∧ ∀ g, v g ≤ γ * π g + μ

/-- An optimum of the demand dual (50): `min {γ + µ : γ ≥ 0, µ ∈ ℝ, v_j ≤ γπ_j + µ ∀ j}`. -/
def IsOptDemandDual {G : Type} [Fintype G] (v π : G → ℝ) (γ μ : ℝ) : Prop :=
  IsDemandDual v π γ μ ∧ ∀ γ' μ', IsDemandDual v π γ' μ' → γ + μ ≤ γ' + μ'

/-- The minimum price `m = min_g π_g` (`0` when there are no goods). -/
noncomputable def minPrice {G : Type} [Fintype G] (π : G → ℝ) : ℝ :=
  if h : (Finset.univ : Finset G).Nonempty then Finset.univ.inf' h π else 0

/-- **The normalized prices** `π̂_g = (π_g − m)/(1 − m)`, `m = min_g π_g` (proof of Lemma B.5). -/
noncomputable def normPrice {G : Type} [Fintype G] (π : G → ℝ) (g : G) : ℝ :=
  (π g - minPrice π) / (1 - minPrice π)

open Classical in
/-- `Z_i`: the quantity of other nodes' goods consumed by the node-`i` agents. -/
noncomputable def RVIData.Zq (D : RVIData) (X : MAgent D → MGood D → ℝ) (i : Fin D.k) : ℝ :=
  ∑ c : Fin D.B0, ∑ g : MGood D,
    if (∃ j, D.goodNode g = some j ∧ j ≠ i.val) then X (nodeAgent i c) g else 0

open Classical in
/-- `q_i`: the quantity of node-`i` goods consumed by edge agents. -/
noncomputable def RVIData.qq (D : RVIData) (X : MAgent D → MGood D → ℝ) (i : Fin D.k) : ℝ :=
  ∑ e : Fin D.W, ∑ g : MGood D, if D.goodNode g = some i.val then X (edgeAgent e) g else 0

/-- The edge `e`, as the triple `(tail i, head j, λ_e)`. -/
def RVIData.edgeAt (D : RVIData) (e : Fin D.W) : ℕ × ℕ × ℚ := D.edges.getD e.val (0, 0, 0)

/-- The parameter `λ_{it}` of the low group of a low good (`0` for other goods). -/
def RVIData.goodParam (D : RVIData) : MGood D → ℚ
  | .inl ⟨g, _⟩ => D.groupParam g
  | _ => 0

open Classical in
/-- The quantity `∑_{g ∈ P} y_g` that the bundle `y` puts on the goods satisfying `P`. -/
noncomputable def massOn {G : Type} [Fintype G] (P : G → Prop) (y : G → ℝ) : ℝ :=
  ∑ g, if P g then y g else 0

/-- The quantity of the goods satisfying `P` consumed by the node-`i` agents together. -/
noncomputable def RVIData.classCons (D : RVIData) (X : MAgent D → MGood D → ℝ) (i : Fin D.k)
    (P : MGood D → Prop) : ℝ :=
  ∑ c : Fin D.B0, massOn P (X (nodeAgent i c))

end HZFixp.Main


