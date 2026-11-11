-- Prove2me | Definitions.Def_ExactAutobid_Equilibria_ROIPacing
-- name    : ExactAutobid_Equilibria_ROIPacing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:56:06.370617+00:00
-- url     : https://prove2.me/theorems/3ca92a5f-3cb3-404a-b06e-f1a3a540ceef
-- title:
--   Second-price ROI pacing equilibria (Definition 2.1), the search problem of Theorem 1.1(i), and the ROI gadget pattern of Table 1
-- statement:
--   Bidders $i$ have nonnegative values $v_{ij}$ for goods $j$ and bid $\alpha_i v_{ij}$ with a **pacing multiplier** $\alpha_i \in [1, A]$, $A \ge 1$. Each good is sold separately by a second-price auction: its **price** $p_j$ is the second entry of all bids on $j$ sorted nonincreasingly with repeats ($p_j = 0$ with a single bidder; the top bid when at least two bidders tie for it). An allocation $x_{ij} \in [0,1]$ is **valid** if only highest bidders receive positive shares and the shares of every good with a positive bid sum to one. With $V_i = \sum_j x_{ij} v_{ij}$ and $P_i = \sum_j x_{ij} p_j$, $(\alpha, x)$ is a **second-price ROI pacing equilibrium** (Definition 2.1) if for every bidder
--   $$1 \le \alpha_i \le A,\qquad P_i \le V_i,\qquad P_i < V_i \;\Longrightarrow\; \alpha_i = A. \tag{2.1}$$
--
--   The real search problem `roiPacingProblemOn A R` has the well-formed rational markets satisfying $R$ (with $n$ bidders and $|J|$ goods) as instances and the vectors $(\alpha, x) \in \mathbb{R}^{n + n|J|}$ of equilibria as solutions; the cap $A$ is a parameter of the problem. The **restricted class** `PacingData.Sparse V` of Theorem 1.1(i): at most two bidders with positive valuation per good, at most four goods with positive valuation per bidder, and every positive valuation in the finite set $V$.
--
--   **The gadget of Table 1** (§4.1). A market contains the common ROI gadget with $k \le 2$ inputs if it has distinct bidders $A_{\mathrm{in},i}, A_{\mathrm{out}}, A_{\mathrm{aux}}$ and distinct goods $G_{\mathrm{out}}, G_{\mathrm{in},i}, G_{\mathrm{pout}}, G_{\mathrm{paux}}$ with exactly the valuations of Table 1 on the gadget goods ($1$ and $v$ for $A_{\mathrm{out}}, A_{\mathrm{aux}}$ on $G_{\mathrm{out}}$; $d_i$ and $r_i$ on $G_{\mathrm{in},i}$; $t$ on $G_{\mathrm{pout}}$; $x$ on $G_{\mathrm{paux}}$; $0$ for everyone else), $A_{\mathrm{aux}}$ values no other good, and every other good valued by $A_{\mathrm{out}}$ is valued more than $A$ times as much by another bidder (as $A_{\mathrm{out}}$'s downstream input goods are). A **local completion** is an allocation of the gadget goods, valid there, under which the ROI conditions of $A_{\mathrm{out}}$ and $A_{\mathrm{aux}}$ counted on the gadget goods hold and the input bidders receive nothing.
--
--   **Formalization Note.** Generic statements use arbitrary finite types of bidders and goods; the search problem uses `Fin n` bidders and `Fin |J|` goods, rational data, real controls, and the solution vector $y = (\alpha, x)$ with $x_{ij} = y_{n + i|J| + j}$ (0-based).
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), §2.1, pp. 3–4, Definition 2.1; Theorem 1.1(i), p. 2; §4.1, pp. 12–17, Table 1

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_FixpReciprocal_frame
import Definitions.Def_FixpReciprocal_RealSearch

namespace ExactAutobid.Equilibria

open OnlineCRS.Combine FixpReciprocal

/-! ### Second-price ROI pacing (Definition 2.1) on arbitrary finite bidder and good types -/

section Market

variable {β γ : Type} [Fintype β] [Fintype γ]

/-- The bid `α_i v_{ij}` of bidder `i` on good `j`. -/
def pacingBid (v : β → γ → ℝ) (α : β → ℝ) (i : β) (j : γ) : ℝ := α i * v i j

/-- **The second price** of good `j`: sort all bids on `j` in nonincreasing order, retaining
repeated values, and take the second entry; `0` if there is only one bidder (§2.1, p. 3). -/
noncomputable def secondPrice (v : β → γ → ℝ) (α : β → ℝ) (j : γ) : ℝ :=
  ((Finset.univ.toList.map (fun i => pacingBid v α i j)).mergeSort
    (fun a c => decide (c ≤ a))).getD 1 0

/-- **A valid allocation on a set `S` of goods**: shares in `[0, 1]`, only highest bidders receive
a positive share, and the shares of every good with a positive bid sum to one (§2.1, p. 3). -/
def ValidAllocOn (v : β → γ → ℝ) (α : β → ℝ) (x : β → γ → ℝ) (S : Set γ) : Prop :=
  ∀ j ∈ S, (∀ i, 0 ≤ x i j ∧ x i j ≤ 1) ∧
    (∀ i, 0 < x i j → ∀ k, pacingBid v α k j ≤ pacingBid v α i j) ∧
    ((∃ i, 0 < pacingBid v α i j) → ∑ i, x i j = 1)

/-- The acquired value `Σ_{j ∈ S} x_{ij} v_{ij}` of bidder `i` on the goods of `S`. -/
noncomputable def pacingValueOn (v : β → γ → ℝ) (x : β → γ → ℝ) (S : Finset γ) (i : β) : ℝ :=
  ∑ j ∈ S, x i j * v i j

/-- The payment `Σ_{j ∈ S} x_{ij} p_j` of bidder `i` on the goods of `S`. -/
noncomputable def pacingPaymentOn (v : β → γ → ℝ) (α : β → ℝ) (x : β → γ → ℝ) (S : Finset γ)
    (i : β) : ℝ :=
  ∑ j ∈ S, x i j * secondPrice v α j

/-- The ROI condition of bidder `i` with cap `A`, counted on the goods of `S`:
`P_i ≤ V_i` and `P_i < V_i ⟹ α_i = A`. -/
def ROICondOn (A : ℝ) (v : β → γ → ℝ) (α : β → ℝ) (x : β → γ → ℝ) (S : Finset γ) (i : β) :
    Prop :=
  pacingPaymentOn v α x S i ≤ pacingValueOn v x S i ∧
    (pacingPaymentOn v α x S i < pacingValueOn v x S i → α i = A)

/-- **Second-price ROI pacing equilibrium with ROI target one and cap `A`** (Definition 2.1,
(2.1)): `α ∈ [1, A]^n`, `x` a valid allocation, and for every bidder `P_i ≤ V_i` and
`P_i < V_i ⟹ α_i = A`, with `V_i = Σ_j x_{ij} v_{ij}`, `P_i = Σ_j x_{ij} p_j`.

Huang, Liu, Yan, *On the Complexity of Exact Autobidding Equilibria*, arXiv:2611.04475
(sha256 270d1b74…), §2.1, pp. 3–4, Definition 2.1. -/
def IsROIPacingEq (A : ℝ) (v : β → γ → ℝ) (α : β → ℝ) (x : β → γ → ℝ) : Prop :=
  (∀ i, 1 ≤ α i ∧ α i ≤ A) ∧ ValidAllocOn v α x Set.univ ∧
    ∀ i, ROICondOn A v α x Finset.univ i

end Market

/-! ### The search problem -/

/-- The data of a ROI pacing market: `nb` bidders, `ng` goods, and the rational valuations, one
row per bidder. -/
structure PacingData where
  /-- the number of bidders -/
  nb : ℕ
  /-- the number of goods -/
  ng : ℕ
  /-- the valuations `v_{ij}`, row `i` for bidder `i` -/
  vals : List (List ℚ)

/-- Well-formed data: `nb` rows of length `ng`, nonnegative valuations. -/
def PacingData.WellFormed (d : PacingData) : Prop :=
  d.vals.length = d.nb ∧ ∀ row ∈ d.vals, row.length = d.ng ∧ ∀ q ∈ row, 0 ≤ q

/-- The valuation `v_{ij}` (bidders and goods `0`-based). -/
def PacingData.val (d : PacingData) (i : Fin d.nb) (j : Fin d.ng) : ℝ :=
  (((d.vals.getD i.val []).getD j.val 0 : ℚ) : ℝ)

/-- Binary encoding of the data. -/
def encPacingData (d : PacingData) : List Sym :=
  fNat d.nb ++ fNat d.ng ++ fList (fList fRat) d.vals

theorem encPacingData_injective : Function.Injective encPacingData := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [encPacingData, List.append_assoc] at h
  obtain ⟨h1, h⟩ := fNat_prefixFree h
  obtain ⟨h2, h⟩ := fNat_prefixFree h
  have h3 := fRat_prefixFree.fList.fList.injective (by simpa using h)
  subst h1 h2 h3
  rfl

/-- The multipliers `α_i = y_i` read from a solution vector `y = (α, x)`. -/
def pacingAlphaOf {n m : ℕ} (y : Fin (n + n * m) → ℝ) : Fin n → ℝ :=
  fun i => y (Fin.castAdd (n * m) i)

/-- The shares `x_{ij} = y_{n + i m + j}` read from a solution vector `y = (α, x)`. -/
def pacingShareOf {n m : ℕ} (y : Fin (n + n * m) → ℝ) : Fin n → Fin m → ℝ :=
  fun i j => y (Fin.natAdd n (finProdFinEquiv (i, j)))

/-- **Exact second-price ROI pacing with a fixed cap `A`**, restricted to the instances satisfying
`R`, as a real search problem: a solution is the vector `(α, x)` of an equilibrium (Definition 2.1),
of dimension `n + n|J|`.

Huang, Liu, Yan, arXiv:2611.04475 (sha256 270d1b74…), Theorem 1.1(i), p. 2, and Definition 2.1. -/
def roiPacingProblemOn (A : ℚ) (R : PacingData → Prop) : RealSearch where
  Inst := {d : PacingData // d.WellFormed ∧ R d}
  enc := fun I => encPacingData I.1
  enc_injective := fun _ _ h => Subtype.ext (encPacingData_injective h)
  dim := fun I => I.1.nb + I.1.nb * I.1.ng
  Sol := fun I => {y | IsROIPacingEq (A : ℝ) I.1.val (pacingAlphaOf y) (pacingShareOf y)}

/-- **Second-price ROI pacing with cap `A`** on all well-formed instances. -/
def roiPacingProblem (A : ℚ) : RealSearch := roiPacingProblemOn A (fun _ => True)

/-- **The restricted class of Theorem 1.1(i)**: every good has at most two bidders with positive
valuation, every bidder has positive valuation on at most four goods, and every positive valuation
lies in the finite set `V`. -/
def PacingData.Sparse (V : Finset ℚ) (d : PacingData) : Prop :=
  (∀ j : Fin d.ng, (Finset.univ.filter (fun i : Fin d.nb => 0 < d.val i j)).card ≤ 2) ∧
    (∀ i : Fin d.nb, (Finset.univ.filter (fun j : Fin d.ng => 0 < d.val i j)).card ≤ 4) ∧
    ∀ (i : Fin d.nb) (j : Fin d.ng), 0 < d.val i j → ∃ q ∈ V, d.val i j = (q : ℝ)

/-- The number of control coordinates (the multipliers) of a ROI pacing instance. -/
def pacingControls (A : ℚ) (R : PacingData → Prop) : (roiPacingProblemOn A R).Inst → ℕ :=
  fun I => I.1.nb

/-! ### The gadget patterns of §4.1 (Table 1) -/

section Gadgets

variable {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

/-- The goods of a gadget: `G_out`, `G_pout`, `G_paux` and the input goods `G_{in,i}`. -/
def gadgetGoods {k : ℕ} (gout gpout gpaux : γ) (gin : Fin k → γ) : Finset γ :=
  insert gout (insert gpout (insert gpaux (Finset.univ.image gin)))

/-- **A market containing the common second-price ROI gadget of Table 1** (§4.1, p. 13) with `k`
inputs: input bidders `A_{in,i}`, output bidder `A_out`, auxiliary bidder `A_aux`, all distinct;
distinct goods `G_out`, `G_{in,i}`, `G_pout`, `G_paux`; valuations exactly those of Table 1 on the
gadget goods (`1` and `vOut` for `A_out` and `A_aux` on `G_out`; `d_i` and `r_i` on `G_{in,i}`;
`t` on `G_pout`; `x` on `G_paux`; `0` for every other bidder); `A_aux` values no other good; and
every other good valued by `A_out` has a bidder valuing it more than `A` times as much (as every
downstream input good `G_{in,i}`, with `r_i > A d_i`, does), so `A_out` always loses it. -/
structure IsROIGadget (A : ℝ) (v : β → γ → ℝ) (k : ℕ) (vOut : ℝ) (d r : Fin k → ℝ) (t x : ℝ)
    (inB : Fin k → β) (outB auxB : β) (gout gpout gpaux : γ) (gin : Fin k → γ) : Prop where
  inB_injective : Function.Injective inB
  in_ne_out : ∀ i, inB i ≠ outB
  in_ne_aux : ∀ i, inB i ≠ auxB
  out_ne_aux : outB ≠ auxB
  gin_injective : Function.Injective gin
  gout_ne_gpout : gout ≠ gpout
  gout_ne_gpaux : gout ≠ gpaux
  gpout_ne_gpaux : gpout ≠ gpaux
  gin_ne : ∀ i, gin i ≠ gout ∧ gin i ≠ gpout ∧ gin i ≠ gpaux
  val_gout : ∀ b, v b gout = if b = outB then 1 else if b = auxB then vOut else 0
  val_gin : ∀ i b, v b (gin i) = if b = inB i then d i else if b = auxB then r i else 0
  val_gpout : ∀ b, v b gpout = if b = outB then t else 0
  val_gpaux : ∀ b, v b gpaux = if b = auxB then x else 0
  aux_other : ∀ g, g ∉ gadgetGoods gout gpout gpaux gin → v auxB g = 0
  out_other : ∀ g, g ∉ gadgetGoods gout gpout gpaux gin → 0 < v outB g →
    ∃ b, b ≠ outB ∧ A * v outB g < v b g

/-- **A local completion of a ROI gadget** at the multiplier profile `α` (§4.1, Lemmas 4.3, 4.5):
shares `y` on the gadget goods forming a valid allocation there, satisfying the ROI conditions of
`A_out` and `A_aux` counted on the gadget goods ("both core ROI conditions"), and giving every input
bidder share `0` of every gadget good, so that it receives no value and pays nothing there (its
upstream ROI condition is unchanged). -/
def IsLocalROICompletion (A : ℝ) (v : β → γ → ℝ) {k : ℕ} (α : β → ℝ) (y : β → γ → ℝ)
    (inB : Fin k → β) (outB auxB : β) (gout gpout gpaux : γ) (gin : Fin k → γ) : Prop :=
  ValidAllocOn v α y ↑(gadgetGoods gout gpout gpaux gin) ∧
    ROICondOn A v α y (gadgetGoods gout gpout gpaux gin) outB ∧
    ROICondOn A v α y (gadgetGoods gout gpout gpaux gin) auxB ∧
    ∀ i, ∀ g ∈ gadgetGoods gout gpout gpaux gin, y (inB i) g = 0

end Gadgets

end ExactAutobid.Equilibria


