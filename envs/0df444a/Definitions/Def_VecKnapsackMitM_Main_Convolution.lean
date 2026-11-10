-- Prove2me | Definitions.Def_VecKnapsackMitM_Main_Convolution
-- name    : VecKnapsackMitM_Main_Convolution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:34:15.390017+00:00
-- url     : https://prove2.me/theorems/3343fb06-bc0a-4420-9a46-52357423b7e9
-- title:
--   The §4.5 setting: domains $R^J$, $A$-functions, convolution (Def. 4.9), $\gamma$-approximate functions (Def. 4.10), dyadic blocks, tables
-- statement:
--   The objects of the proof of Lemma 4.8 (printed pp. 24–27). Parameters: items $I$, middle weight estimates `Wt`, $\varepsilon,\eta$; `cDelta n ε` $=\delta=\varepsilon/(10\log_2 n)$ and `cBigDelta n ε η` $=\Delta=(\varepsilon\eta/(10n))^5$.
--
--   * `PVec d`: vectors $x$ with `prof` $=x_0$ (profit) and `wt t` $=x_{t+1}$ (weight of dimension $t+1$, used for $t+1<d$); `add`, and `Dom` for $x\succeq y$: $x_0\ge y_0$ and $x_t\le y_t$ for $t\in[d-1]$.
--   * Error scales: `scaleP` $E^J_0=\Delta\max_{i\in J}p(i)$; `scaleW` $E^J_1=\Delta\max_{i\in J}\bar w_1(i)$ and $E^J_t=\Delta\bar W_t$ for $2\le t\le d-1$.
--   * `InGrid δ Δ E y`: $y\in([E,\Delta^{-2}E]\cap\{(1+\delta)^k:k\in\mathbb Z\})\cup\{0\}$; `InDom … J x`: $x\in R^J=P^J\times W^J_1\times\dots\times W^J_{d-1}$ (unused coordinate $0$).
--   * `AFun d n`: functions to `Option (Finset (Fin n))` (`none` is $\bot$, otherwise the set of the virtual item); `IsAFun … A f`: values on $R^A$ are $\bot$ or subsets of $A$.
--   * `IsConv … A B f g h` (Definition 4.9): for every $x\in R^{A\cup B}$, $h(x)=\bot$ if no $y\in R^A$, $z\in R^B$ has $y+z\succeq x$, $f(y)\ne\bot$, $g(z)\ne\bot$; otherwise $h(x)=f(y)\cup g(z)$ for such a pair minimizing $\bar w_d(f(y))+\bar w_d(g(z))$ (ties arbitrary).
--   * Approximation levels are real numbers; `IsApproxOn` includes $0\le\gamma$.
--
--   * `QSet … γ C x` (Definition 4.10): $Q^{(\gamma)}_C(x)=\{X\subseteq C: x_0\le\max\{(1+\delta)^{-\gamma}p(X)-(8^\gamma-1)E^C_0,0\},\ x_t\ge(1+\delta)^\gamma\bar w_t(X)+(8^\gamma-1)E^C_t\ \forall t\in[d-1]\}$.
--   * `IsApproxOn … γ C h` (Definition 4.10): $h$ is a $C$-function and for all $x\in R^C$: if $h(x)\ne\bot$ then $p(h(x))\ge x_0$, $\bar w_t(h(x))\le x_t$ ($t\in[d-1]$) and $\bar w_d(h(x))\le\bar w_d(X)$ for all $X\in Q^{(\gamma)}_C(x)$; and $Q^{(\gamma)}_C(x)\ne\emptyset\Rightarrow h(x)\ne\bot$. (Properties 1–3 hold at $\bot$ by $p(\bot)=\infty$, $\bar w(\bot)=-\infty$.)
--   * `block n α β` $=I_{\alpha,\beta}=[(\beta-1)2^\alpha+1,\beta2^\alpha]\cap I$ (paper indices).
--   * Tables: `keyAt`, `TableRep … s a A f` (the table at $a$ lists entries whose keys are exactly the points of $R^A$, pairwise distinct, each with value $0$ for $\bot$ or the address of a virtual item representing $f$ there), `TableWithin` (table and reachable records in an address window).
--   * Inputs: `sec45Input I Wt ε η` ($N[0]=d$, $N[1]=n$; $R[0]=\varepsilon$, $R[1]=\eta$, $R[2+t]=$ `Wt t`, then the items); `ConvInput` (the convolution step: parameters, $\max_Ap$, $\max_A\bar w_1$, $\max_Bp$, $\max_B\bar w_1$ in $R[2..5]$, `Wt` from $R[6]$, the tables of $f,g$ at the addresses in $N[2]$, $N[3]$, the first free address in $N[4]$, everything stored in the window $[6+d,F)$); `blockSlot k α β` $=2+2^{k-\alpha}+\beta-1$ (heap numbering of the blocks).
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; §4.5, printed pp. 24–28 (PDF 25–29): Definitions 4.9, 4.10, the dyadic partition and the proofs of Claims 4.13, 4.14

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Machine
import Definitions.Def_VecKnapsackMitM_Main_VirtualItem

namespace VecKnapsackMitM.Main

open MatMulTimeLP

/-! The setting of the proof of Lemma 4.8 (Bringmann, Kulik, Węgrzycki 2026, §4.5, printed
pp. 24–27, PDF 25–28): items `I = {1, …, n}` (here `Fin n`), weight estimates `W̄_2, …, W̄_{d−1}`
(here `Wt t` for the middle `t`, `1 ≤ t`, `t + 2 ≤ d`), error parameters `ε, η`, and
`δ := ε/(10 log n)`, `∆ := (εη/(10n))^5`. A virtual item is identified with the set it
represents, an `A`-function maps each `x ∈ R^A` to `none` (the paper's `⊥`) or a set `⊆ A`.
The paper's vectors `x ∈ ℝ^d_{≥0}` with `x₀` a profit and `x₁, …, x_{d−1}` weights of the
dimensions `1, …, d − 1` are `PVec d`: `prof = x₀` and `wt t = x_{t+1}` for `t + 1 < d`
(the coordinate `wt (d − 1)` is unused and fixed to `0` in the domains). -/

/-- `δ = ε / (10 log₂ n)`. -/
noncomputable def cDelta (n : ℕ) (ε : ℝ) : ℝ := ε / (10 * Real.logb 2 n)

/-- `∆ = (ε η / (10 n))^5`. -/
noncomputable def cBigDelta (n : ℕ) (ε η : ℝ) : ℝ := (ε * η / (10 * n)) ^ 5

/-- A vector `x` of §4.5: `prof = x₀` (profit), `wt t = x_{t+1}` (weight of dimension `t + 1`,
0-based `t`, for `t + 1 < d`). -/
structure PVec (d : ℕ) where
  /-- `x₀` -/
  prof : ℝ
  /-- `wt t = x_{t+1}` -/
  wt : Fin d → ℝ

/-- Coordinate-wise sum `x + y`. -/
def PVec.add {d : ℕ} (x y : PVec d) : PVec d := ⟨x.prof + y.prof, fun t => x.wt t + y.wt t⟩

/-- `x ⪰ y`: `x₀ ≥ y₀` and `x_t ≤ y_t` for `t ∈ [d − 1]`. -/
def PVec.Dom {d : ℕ} (x y : PVec d) : Prop :=
  y.prof ≤ x.prof ∧ ∀ t : Fin d, t.val + 1 < d → x.wt t ≤ y.wt t

/-- The paper's first weight `w̄₁(i)` (`w i 0`; `0` if `d = 0`). -/
def Items.w1 {d n : ℕ} (I : Items d n) (i : Fin n) : ℝ :=
  if h : 0 < d then I.w i ⟨0, h⟩ else 0

/-- Error scale `E^J_0 = ∆ · max_{i ∈ J} p(i)`. -/
noncomputable def scaleP {d n : ℕ} (I : Items d n) (ε η : ℝ) (J : Finset (Fin n)) : ℝ :=
  cBigDelta n ε η * Items.maxOver J I.p

/-- Error scales of the weights: `E^J_1 = ∆ · max_{i ∈ J} w̄₁(i)` for the first dimension
(`t = 0`) and `E^J_{t+1} = ∆ · W̄_{t+1}` for the middle dimensions (`t ≥ 1`). -/
noncomputable def scaleW {d n : ℕ} (I : Items d n) (Wt : Fin d → ℝ) (ε η : ℝ)
    (J : Finset (Fin n)) (t : Fin d) : ℝ :=
  if t.val = 0 then cBigDelta n ε η * Items.maxOver J I.w1 else cBigDelta n ε η * Wt t

/-- `y ∈ ([E, ∆^{−2} E] ∩ {(1 + δ)^k | k ∈ ℤ}) ∪ {0}`. -/
def InGrid (δ Δ E y : ℝ) : Prop :=
  y = 0 ∨ (E ≤ y ∧ y ≤ (Δ ^ 2)⁻¹ * E ∧ ∃ k : ℤ, y = (1 + δ) ^ k)

/-- `x ∈ R^J = P^J × W^J_1 × … × W^J_{d−1}`, with the unused last coordinate `0`. -/
def InDom {d n : ℕ} (I : Items d n) (Wt : Fin d → ℝ) (ε η : ℝ) (J : Finset (Fin n))
    (x : PVec d) : Prop :=
  InGrid (cDelta n ε) (cBigDelta n ε η) (scaleP I ε η J) x.prof ∧
    ∀ t : Fin d, (t.val + 1 < d → InGrid (cDelta n ε) (cBigDelta n ε η) (scaleW I Wt ε η J t)
      (x.wt t)) ∧ (t.val + 1 = d → x.wt t = 0)

/-- A function on vectors with values `⊥` (`none`) or a virtual item (its set). -/
abbrev AFun (d n : ℕ) := PVec d → Option (Finset (Fin n))

/-- `f` is an `A`-function: every `x ∈ R^A` is mapped to `⊥` or to a set `⊆ A`. -/
def IsAFun {d n : ℕ} (I : Items d n) (Wt : Fin d → ℝ) (ε η : ℝ) (A : Finset (Fin n))
    (f : AFun d n) : Prop :=
  ∀ x, InDom I Wt ε η A x → ∀ S, f x = some S → S ⊆ A

/-- Definition 4.9: `h` is a convolution `f ⊕ g` (ties broken arbitrarily). For every
`x ∈ R^{A ∪ B}`: if no `y ∈ R^A`, `z ∈ R^B` has `y + z ⪰ x`, `f(y) ≠ ⊥`, `g(z) ≠ ⊥`, then
`h(x) = ⊥`; otherwise `h(x) = f(y) ∪ g(z)` for such a pair minimizing the `d`-th weight
`w̄_d(f(y)) + w̄_d(g(z))` of the union virtual item. -/
def IsConv {d n : ℕ} (I : Items d n) (Wt : Fin d → ℝ) (ε η : ℝ) (A B : Finset (Fin n))
    (f g h : AFun d n) : Prop :=
  ∀ x, InDom I Wt ε η (A ∪ B) x →
    ((∀ y z, InDom I Wt ε η A y → InDom I Wt ε η B z → (y.add z).Dom x →
        f y = none ∨ g z = none) → h x = none) ∧
    ((∃ y z, InDom I Wt ε η A y ∧ InDom I Wt ε η B z ∧ (y.add z).Dom x ∧
        f y ≠ none ∧ g z ≠ none) →
      ∃ y z Sy Sz, InDom I Wt ε η A y ∧ InDom I Wt ε η B z ∧ (y.add z).Dom x ∧
        f y = some Sy ∧ g z = some Sz ∧ h x = some (Sy ∪ Sz) ∧
        ∀ y' z' Sy' Sz', InDom I Wt ε η A y' → InDom I Wt ε η B z' → (y'.add z').Dom x →
          f y' = some Sy' → g z' = some Sz' → ∀ t : Fin d, t.val + 1 = d →
            I.weight Sy t + I.weight Sz t ≤ I.weight Sy' t + I.weight Sz' t)

/-- Definition 4.10: `Q^{(γ)}_C(x)`, the sets `X ⊆ C` with
`x₀ ≤ max{(1 + δ)^{−γ} p(X) − (8^γ − 1) E^C_0, 0}` and
`x_t ≥ (1 + δ)^γ w̄_t(X) + (8^γ − 1) E^C_t` for `t ∈ [d − 1]`. -/
def QSet {d n : ℕ} (I : Items d n) (Wt : Fin d → ℝ) (ε η : ℝ) (γ : ℝ) (C : Finset (Fin n))
    (x : PVec d) : Set (Finset (Fin n)) :=
  {X | X ⊆ C ∧
    x.prof ≤ max ((1 + cDelta n ε) ^ (-γ) * I.profit X - ((8 : ℝ) ^ γ - 1) *
      scaleP I ε η C) 0 ∧
    ∀ t : Fin d, t.val + 1 < d →
      (1 + cDelta n ε) ^ γ * I.weight X t + ((8 : ℝ) ^ γ - 1) * scaleW I Wt ε η C t ≤ x.wt t}

/-- Definition 4.10: the `C`-function `h` is `γ`-approximate on `C`: for every `x ∈ R^C`, if
`h(x) ≠ ⊥` then `p(h(x)) ≥ x₀`, `w̄_t(h(x)) ≤ x_t` for `t ∈ [d − 1]` and
`w̄_d(h(x)) ≤ w̄_d(X)` for every `X ∈ Q^{(γ)}_C(x)` (properties 1–3; they hold trivially at `⊥`,
`p(⊥) = ∞`, `w̄(⊥) = −∞`); and if `Q^{(γ)}_C(x) ≠ ∅` then `h(x) ≠ ⊥` (property 4). -/
def IsApproxOn {d n : ℕ} (I : Items d n) (Wt : Fin d → ℝ) (ε η : ℝ) (γ : ℝ)
    (C : Finset (Fin n)) (h : AFun d n) : Prop :=
  0 ≤ γ ∧ IsAFun I Wt ε η C h ∧
  ∀ x, InDom I Wt ε η C x →
    (∀ S, h x = some S →
      x.prof ≤ I.profit S ∧ (∀ t : Fin d, t.val + 1 < d → I.weight S t ≤ x.wt t) ∧
      ∀ X ∈ QSet I Wt ε η γ C x, ∀ t : Fin d, t.val + 1 = d → I.weight S t ≤ I.weight X t) ∧
    ((QSet I Wt ε η γ C x).Nonempty → h x ≠ none)

/-- The dyadic block `I_{α,β} = [(β − 1) 2^α + 1, β 2^α] ∩ I` (paper indices; item `i + 1` of
the paper is `i : Fin n`). -/
def block (n α β : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => (β - 1) * 2 ^ α + 1 ≤ i.val + 1 ∧ i.val + 1 ≤ β * 2 ^ α

/-! Explicit tables of `A`-functions in memory. A table at address `a` is the list
`listAt s a` of entry addresses; the entry at `e` has the key `x` with `x₀ = R[e]`,
`x_{t+1} = R[e + 1 + t]` (`t + 1 < d`), and the value `N[e]`: `0` for `⊥`, otherwise the address
of a virtual item. -/

/-- The key of the table entry at address `e`. -/
def keyAt (s : State) (d e : ℕ) : PVec d :=
  ⟨s.R e, fun t => if t.val + 1 < d then s.R (e + 1 + t.val) else 0⟩

/-- The table at address `a` of state `s` represents the `A`-function `f` on `R^A`: its keys are
pairwise distinct and are exactly the points of `R^A`, and each entry's value is `⊥` exactly
when `f` is `⊥` there, and otherwise a virtual item representing the value of `f`. -/
def TableRep {d n : ℕ} (I : Items d n) (Wt : Fin d → ℝ) (ε η : ℝ) (s : State) (a : ℕ)
    (A : Finset (Fin n)) (f : AFun d n) : Prop :=
  ((listAt s a).map (keyAt s d)).Nodup ∧
  (∀ x, InDom I Wt ε η A x ↔ x ∈ (listAt s a).map (keyAt s d)) ∧
  ∀ e ∈ listAt s a,
    (s.N e = 0 ∧ f (keyAt s d e) = none) ∨
    (s.N e ≠ 0 ∧ ∃ S, f (keyAt s d e) = some S ∧ IsVItem I s (s.N e) S)

/-- The table at `a` (its list, its entries and every virtual item they point to) lies in the
address window `[lo, F)`. -/
def TableWithin (s : State) (n d a lo F : ℕ) : Prop :=
  lo ≤ a ∧ a + s.N a + 1 ≤ F ∧
    ∀ e ∈ listAt s a, lo ≤ e ∧ e + d + 1 ≤ F ∧ (s.N e ≠ 0 → NodesWithin s n d (s.N e) lo F)

/-- The standard input of the §4.5 procedures: index cells `N[0] = d`, `N[1] = n`; real cells
`R[0] = ε`, `R[1] = η`, `R[2 + t] = Wt t` (`t < d`; only the middle coordinates are used), then
the items (`itemsReals`) from `R[2 + d]` on. -/
noncomputable def sec45Input {d n : ℕ} (I : Items d n) (Wt : Fin d → ℝ) (ε η : ℝ) : State :=
  initState2 ([ε, η] ++ finVec Wt ++ itemsReals I) [d, n]

/-- Input layout of the convolution step (Claim 4.11): `N[0] = d`, `N[1] = n`, `N[2]` and `N[3]`
the addresses of the tables of `f` (on `R^A`) and `g` (on `R^B`), `N[4] = F` the first free
address; `R[0] = ε`, `R[1] = η`, `R[2] = max_{A} p`, `R[3] = max_{A} w̄₁`, `R[4] = max_{B} p`,
`R[5] = max_{B} w̄₁`, `R[6 + t] = Wt t` (`t < d`); both tables and every record they reach lie
in the window `[6 + d, F)`, clear of the parameter cells and of the output cell `N[5]`; the
program counter is `0`. -/
def ConvInput {d n : ℕ} (I : Items d n) (Wt : Fin d → ℝ) (ε η : ℝ) (A B : Finset (Fin n))
    (f g : AFun d n) (s : State) : Prop :=
  s.pc = 0 ∧ s.N 0 = d ∧ s.N 1 = n ∧ s.R 0 = ε ∧ s.R 1 = η ∧
  s.R 2 = Items.maxOver A I.p ∧ s.R 3 = Items.maxOver A I.w1 ∧
  s.R 4 = Items.maxOver B I.p ∧ s.R 5 = Items.maxOver B I.w1 ∧
  (∀ t : Fin d, s.R (6 + t.val) = Wt t) ∧ 6 + d ≤ s.N 4 ∧
  TableRep I Wt ε η s (s.N 2) A f ∧ TableWithin s n d (s.N 2) (6 + d) (s.N 4) ∧
  TableRep I Wt ε η s (s.N 3) B g ∧ TableWithin s n d (s.N 3) (6 + d) (s.N 4)

/-- The output cell of the table of `f_{α,β}` in Claim 4.13 (`n = 2^k`): `N[2 + 2^{k−α} + β − 1]`
(heap numbering of the dyadic blocks). -/
def blockSlot (k α β : ℕ) : ℕ := 2 + 2 ^ (k - α) + (β - 1)

end VecKnapsackMitM.Main


