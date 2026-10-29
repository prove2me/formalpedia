-- Prove2me | Definitions.Def_PochetWolsey_Assembly_Model
-- name    : PochetWolsey_Assembly_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:11.646904+00:00
-- url     : https://prove2.me/theorems/0508c1b5-39cc-4427-b88b-e1955b24ba91
-- title:
--   Finite-horizon assembly lot-sizing model and structural predicates
-- statement:
--   An assembly system has $m+1$ items, numbered $0,\ldots,m$, and $n$ periods numbered $0,\ldots,n-1$. Stock $s^i_t$ is held just before period $t$ and $s^i_{t+1}$ just after it; holding cost $h^i_\tau$ is charged on stock boundary $\tau$. Item $0$ is the unique end-product. Each other item $i$ has one direct successor $D(i)<i$; a dummy value $D(0)=0$ is excluded from all arcs. External demand $d_t\ge0$ occurs only at item $0$. Utilization factors are one and lead times are zero. Production, holding, and setup costs $p^i_t,h^i_t,q^i_t$ are arbitrary real numbers. A plan consists of production $x$, physical stock $s$, and binary setups $y$. Write $d^i_t=d_t$ for the end-product and $d^i_t=x^{D(i)}_t$ otherwise.
--
--   Feasibility means nonnegative production and stock, zero initial and terminal stocks, and
--   $$s^i_t+x^i_t=d^i_t+s^i_{t+1},\qquad y^i_t=0\Longrightarrow x^i_t=0.$$
--   For finite nonnegative capacities $C$, also require $x^i_t\le C^i_ty^i_t$. The option `none` means no capacity restrictions; `some C` imposes them. The objective is the sum of production, physical holding, and setup costs. An optimal plan is feasible and has cost no greater than every feasible competitor.
--
--   The echelon holding cost is $H^i_t=h^i_t-\sum_{j\ne0:D(j)=i}h^j_t$. Wagner–Whitin costs require $p^i_t+H^i_{t+1}-p^i_{t+1}\ge0$ at adjacent periods. Setup monotonicity requires $q^i_t\ge q^i_{t+1}$. Stationarity requires each of the three coefficient arrays to be constant in time for each item. A serial graph has $D(i)=i-1$. Nesting means $x^i_t>0\Rightarrow x^{D(i)}_t>0$ for nonfinal items. Zero-stock production means $s^i_tx^i_t=0$. The two batch predicates require every positive quantity to equal a sum over an interval $t\le\alpha\le\beta<n$, using dependent demand or end-product demand respectively.
--
--   These definitions specify the original feasible set independently of any structural conclusion.
--
--   **Formalization Note** Items and production periods use zero-based finite types; the stock at index $t$ precedes production period $t$, and stock at $t+1$ follows it. Stock indices include both endpoints. Thus $m$ counts nonfinal items. The definitions permit $m=0$ and $n=0$; the chapter theorems require both positive. No sign condition is imposed on costs, and an unused setup is permitted.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, pp. 397–407 (PDF 407–417), Eqs. (13.1)–(13.5), Definition 13.2 and Section 13.2; endpoint convention p. 209 (PDF 223)

import Mathlib

open scoped BigOperators

namespace PochetWolsey.Assembly

structure Model (m n : ℕ) where
  successor : Fin (m + 1) → Fin (m + 1)
  root_successor : successor 0 = 0
  successor_lt : ∀ i, i ≠ 0 → (successor i).val < i.val
  demand : Fin n → ℝ
  demand_nonneg : ∀ t, 0 ≤ demand t
  productionCost : Fin (m + 1) → Fin n → ℝ
  holdingCost : Fin (m + 1) → Fin (n + 1) → ℝ
  setupCost : Fin (m + 1) → Fin n → ℝ

structure Plan (m n : ℕ) where
  production : Fin (m + 1) → Fin n → ℝ
  stock : Fin (m + 1) → Fin (n + 1) → ℝ
  setup : Fin (m + 1) → Fin n → Bool

def Capacity (m n : ℕ) := Fin (m + 1) → Fin n → NNReal

def IsSeries {m n : ℕ} (I : Model m n) : Prop :=
  ∀ i, i ≠ 0 → (I.successor i).val + 1 = i.val

noncomputable def effectiveDemand {m n : ℕ} (I : Model m n) (a : Plan m n)
    (i : Fin (m + 1)) (t : Fin n) : ℝ :=
  if i = 0 then I.demand t else a.production (I.successor i) t

def Feasible {m n : ℕ} (I : Model m n) (c : Option (Capacity m n))
    (a : Plan m n) : Prop :=
  (∀ i t, 0 ≤ a.production i t) ∧
  (∀ i t, 0 ≤ a.stock i t) ∧
  (∀ i, a.stock i 0 = 0 ∧ a.stock i (Fin.last n) = 0) ∧
  (∀ i t, a.stock i t.castSucc + a.production i t =
    effectiveDemand I a i t + a.stock i t.succ) ∧
  (∀ i t, a.setup i t = false → a.production i t = 0) ∧
  (∀ C, c = some C → ∀ i t,
    a.production i t ≤ (C i t : ℝ) * (if a.setup i t then 1 else 0))

noncomputable def cost {m n : ℕ} (I : Model m n) (a : Plan m n) : ℝ :=
  (∑ i, ∑ t, I.productionCost i t * a.production i t) +
  (∑ i, ∑ t, I.holdingCost i t * a.stock i t) +
  (∑ i, ∑ t, I.setupCost i t * (if a.setup i t then 1 else 0))

def Optimal {m n : ℕ} (I : Model m n) (c : Option (Capacity m n))
    (a : Plan m n) : Prop :=
  Feasible I c a ∧ ∀ b, Feasible I c b → cost I a ≤ cost I b

def Nested {m n : ℕ} (I : Model m n) (a : Plan m n) : Prop :=
  ∀ i t, i ≠ 0 → 0 < a.production i t → 0 < a.production (I.successor i) t

def ZeroStock {m n : ℕ} (a : Plan m n) : Prop :=
  ∀ i t, a.stock i t.castSucc * a.production i t = 0

noncomputable def echelonHolding {m n : ℕ} (I : Model m n)
    (i : Fin (m + 1)) (t : Fin (n + 1)) : ℝ :=
  I.holdingCost i t -
    ∑ j ∈ Finset.univ.filter (fun j => j ≠ 0 ∧ I.successor j = i), I.holdingCost j t

def WagnerWhitin {m n : ℕ} (I : Model m n) : Prop :=
  ∀ i (t u : Fin n), u.val = t.val + 1 →
    0 ≤ I.productionCost i t + echelonHolding I i t.succ - I.productionCost i u

def NonincreasingSetups {m n : ℕ} (I : Model m n) : Prop :=
  ∀ i (t u : Fin n), u.val = t.val + 1 → I.setupCost i u ≤ I.setupCost i t

def StationaryCosts {m n : ℕ} (I : Model m n) : Prop :=
  (∀ i (t u : Fin n), I.productionCost i t = I.productionCost i u) ∧
  (∀ i (t u : Fin (n + 1)), I.holdingCost i t = I.holdingCost i u) ∧
  (∀ i (t u : Fin n), I.setupCost i t = I.setupCost i u)

noncomputable def demandInterval {n : ℕ} (d : Fin n → ℝ) (α β : Fin n) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => α ≤ t ∧ t ≤ β), d t

def DependentBatches {m n : ℕ} (I : Model m n) (a : Plan m n) : Prop :=
  ∀ i t, 0 < a.production i t → ∃ α β : Fin n,
    t ≤ α ∧ α ≤ β ∧ a.production i t = demandInterval (effectiveDemand I a i) α β

def FinalDemandBatches {m n : ℕ} (I : Model m n) (a : Plan m n) : Prop :=
  ∀ i t, 0 < a.production i t → ∃ α β : Fin n,
    t ≤ α ∧ α ≤ β ∧ a.production i t = demandInterval I.demand α β

end PochetWolsey.Assembly


