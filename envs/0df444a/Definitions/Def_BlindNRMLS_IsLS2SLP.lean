-- Prove2me | Definitions.Def_BlindNRMLS_IsLS2SLP
-- name    : BlindNRMLS_IsLS2SLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:12.789405+00:00
-- url     : https://prove2.me/theorems/591065f2-8462-43f9-9019-95b08538e278
-- title:
--   Algorithm 2, pp.15–16 — the LS-2SLP policy
-- statement:
--   **LS-2SLP** runs $\nu+1$ epochs. Its parameter is $\gamma=\max\{1-17\,a_{\max}\sqrt{n(d+1)\log[(d+1)KT]}\,\log T\,t_1/B_{\min},\,0\}$.
--
--   At the start of epoch $l\le\nu$ it holds confidence bounds $U^{\mathrm{rew}}_k,L^{\mathrm{rew}}_k,U^{\mathrm{cost}}_{i,k},L^{\mathrm{cost}}_{i,k}$, initially $\infty$ and $0$. It updates them from the empirical means $\bar q_{j,k}$ with radius $\|\mathbf p_k\|_2\nabla_k$ or $\|A_i\|_2\nabla_k$, where $\nabla_k=\sqrt{\log[(d+1)KT]/n_k}$. Then it:
--
--   1. solves the pessimistic LP $J^{\mathrm{PES}}_l=\max\{\sum_k L^{\mathrm{rew}}_kx_k:\sum_kU^{\mathrm{cost}}_{i,k}x_k\le B_i,\ \sum_kx_k\le T,\ x\ge0\}$;
--   2. for each $j\in[K]$, solves the exploration LP $x^{l,j}\in\arg\max\{x_j:\sum_kU^{\mathrm{rew}}_kx_k\ge J^{\mathrm{PES}}_l,\ \sum_kL^{\mathrm{cost}}_{i,k}x_k\le B_i,\ \sum_kx_k\le T,\ x\ge0\}$;
--   3. plays each arm $k$ for $\gamma N^l_k$ consecutive periods, starting from the current arm, with $N^l_k=\frac{t_l-t_{l-1}}{T}\sum_{j}\frac1K(x^{l,j})_k$.
--
--   In epoch $\nu+1$ it solves the deterministic LP with the empirical means, takes an optimal solution $x^*$ with the least number of non-zero variables, and plays each arm for $\gamma\frac{T-t_\nu}{T}x^*_k$ periods. Then it ends.
--
--   A policy **is LS-2SLP** when, for some initial arm and some valid choice of LP solutions and orders, it plays the algorithm's action deterministically at every round and history.
--
--   **Formalization Note** Upper bounds take values in $[0,\infty]$, with $\infty\cdot 0=0$: in epoch 1 the pessimistic LP has value $0$ and $T e_j$ is an exploration optimum, so $N^1_k=t_1/K$. The rounding is $\lceil\gamma N_k\rceil$. Exploration solutions have at most $d+2$ non-zeros, and are $0$ when no such optimum exists. An arm with no sample keeps its old bounds and has $\bar q=0$. When $\nu=0$ the last LP has no data, so $x^*=0$ and the policy stops at once. All selling stops are enforced by the model, not the policy.
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, Algorithm 2, pp.15–16; footnote 5, p.17; (EC.19), p.ec30

import Mathlib
import Definitions.Def_BlindNRMLS_Policy
import Definitions.Def_BlindNRMLS_nu

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

variable {d n K : ℕ}

/-- `γ = max{1 - 17 a_max √(n(d+1) log[(d+1)KT]) log T / B_min · t_1, 0}`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, Algorithm 2, p.15. -/
noncomputable def gammaLS (P : Problem d n K) (ν : ℕ) : ℝ :=
  max (1 - 17 * P.amax *
      Real.sqrt ((n : ℝ) * ((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) * K * P.T)) *
      Real.log P.T / P.Bmin * (tSched P.T K ν 1 : ℝ)) 0

/-- The confidence bounds `U^rew, L^rew, U^cost, L^cost` at the start of an epoch (line 5, p.15).

**Formalization Note.** Upper bounds live in `ℝ≥0∞` so that `⊤` is line 3's `∞`. In the LPs below
`⊤ * 0 = 0`, so an arm with an infinite upper cost is excluded by a budget constraint exactly when
it is used. -/
structure EpochBounds (d K : ℕ) where
  /-- `U^rew_k`. -/
  Urew : Fin K → ℝ≥0∞
  /-- `L^rew_k`. -/
  Lrew : Fin K → ℝ
  /-- `U^cost_{i,k}`. -/
  Ucost : Fin d → Fin K → ℝ≥0∞
  /-- `L^cost_{i,k}`. -/
  Lcost : Fin d → Fin K → ℝ

/-- Line 3, p.15: `L = 0` and `U = ∞`. -/
def initBounds : EpochBounds d K :=
  ⟨fun _ => ⊤, fun _ => 0, fun _ _ => ⊤, fun _ _ => 0⟩

/-- The feasible set of the first-stage pessimistic LP (line 7, p.15). -/
def PesFeasible (P : Problem d n K) (D : EpochBounds d K) (x : Fin K → ℝ) : Prop :=
  (∀ i, ∑ k, D.Ucost i k * ENNReal.ofReal (x k) ≤ ENNReal.ofReal (P.B i)) ∧
    ∑ k, x k ≤ (P.T : ℝ) ∧ ∀ k, 0 ≤ x k

/-- `J^PES_l`, the value of the first-stage pessimistic LP (line 7, p.15). -/
noncomputable def pesValue (P : Problem d n K) (D : EpochBounds d K) : ℝ :=
  sSup ((fun x : Fin K → ℝ => ∑ k, D.Lrew k * x k) '' {x | PesFeasible P D x})

/-- The feasible set of the second-stage exploration LP (line 8, p.16). -/
def ExploreFeasible (P : Problem d n K) (D : EpochBounds d K) (x : Fin K → ℝ) : Prop :=
  ENNReal.ofReal (pesValue P D) ≤ ∑ k, D.Urew k * ENNReal.ofReal (x k) ∧
    (∀ i, ∑ k, D.Lcost i k * x k ≤ P.B i) ∧ ∑ k, x k ≤ (P.T : ℝ) ∧ ∀ k, 0 ≤ x k

open Classical in
/-- `x` is a maximizer of `x_j` in the exploration LP with at most `d + 2` non-zero components.

**Formalization Note.** The page says "arg max". Display (EC.19) needs a basic solution; the LP has
`d + 2` constraints, so a basic solution has at most `d + 2` non-zero components (the "`d + 1`" of
(EC.19) is a slip). -/
def IsSparseExploreOpt (P : Problem d n K) (D : EpochBounds d K) (j : Fin K) (x : Fin K → ℝ) :
    Prop :=
  ExploreFeasible P D x ∧ (∀ y, ExploreFeasible P D y → y j ≤ x j) ∧
    (Finset.univ.filter fun k => x k ≠ 0).card ≤ d + 2

/-- The solution `x^{l,j}` of line 8: a sparse maximizer when there is one, and `0` otherwise.

**Formalization Note.** Off the clean event the exploration LP may be infeasible; the page does not
say what happens then. The vector `0` means the epoch plays nothing from this `j`. -/
def IsExploreChoice (P : Problem d n K) (D : EpochBounds d K) (j : Fin K) (x : Fin K → ℝ) : Prop :=
  ((∃ y, IsSparseExploreOpt P D j y) → IsSparseExploreOpt P D j x) ∧
    ((¬ ∃ y, IsSparseExploreOpt P D j y) → x = 0)

open Classical in
/-- The solution `x*` of line 12, p.16: an optimal solution of the deterministic LP with the least
number of non-zero variables, for the empirical mean matrix `q`. -/
def IsFinalChoice (P : Problem d n K) (q : Fin K → Fin n → ℝ) (x : Fin K → ℝ) : Prop :=
  DetFeasible P q x ∧ (∀ y, DetFeasible P q y → detObjective P q y ≤ detObjective P q x) ∧
    ∀ y, DetFeasible P q y → (∀ z, DetFeasible P q z → detObjective P q z ≤ detObjective P q y) →
      (Finset.univ.filter fun k => x k ≠ 0).card ≤ (Finset.univ.filter fun k => y k ≠ 0).card

/-- The choices Algorithm 2 leaves open: LP solutions and the order of the arms within an epoch.

**Formalization Note.** `explore l D j k` is `(x^{l,j})_k`, `final q k` is `(x*)_k`, and `order l m c`
is the order of the arms in epoch `l` when the plan is `m` and the current arm is `c`. -/
structure Selector (d n K : ℕ) where
  /-- The exploration LP solution. -/
  explore : ℕ → EpochBounds d K → Fin K → Fin K → ℝ
  /-- The final LP solution. -/
  final : (Fin K → Fin n → ℝ) → Fin K → ℝ
  /-- The order of the arms within an epoch. -/
  order : ℕ → (Fin K → ℕ) → Fin K → List (Fin K)

/-- Validity of the choices: the LP solutions are as in lines 8 and 12, and each order lists every
arm once starting from the current arm (lines 9 and 12: "starting from this action"). -/
structure Selector.Valid (sel : Selector d n K) (P : Problem d n K) : Prop where
  explore_spec : ∀ l D j, IsExploreChoice P D j (sel.explore l D j)
  final_spec : ∀ q, IsFinalChoice P q (sel.final q)
  order_nodup : ∀ l m c, (sel.order l m c).Nodup
  order_mem : ∀ l m c k, k ∈ sel.order l m c
  order_head : ∀ l m c, (sel.order l m c).head? = some c

open Classical in
/-- The rounds among the first `m` rounds of a history that chose price vector `k`. -/
noncomputable def pulls {t : ℕ} (h : History n K t) (m : ℕ) (k : Fin K) : Finset (Fin t) :=
  Finset.univ.filter fun u => u.val < m ∧ (h u).1 = some k

/-- `q̄_{j,k}`: the empirical mean demand of product `j` under `k` among the first `m` rounds.

**Formalization Note.** With no sample, `x / 0 = 0` gives `q̄ = 0`, the convention used on line 12
when `ν = 0`. -/
noncomputable def empMean {t : ℕ} (h : History n K t) (m : ℕ) (k : Fin K) (j : Fin n) : ℝ :=
  (∑ u ∈ pulls h m k, (h u).2 j) / ((pulls h m k).card : ℝ)

/-- `∇_k = √(log[(d+1)KT] / n_k)` for the sample size `c = n_k ≥ 1` (line 5, p.15). -/
noncomputable def confRadius (d K T c : ℕ) : ℝ :=
  Real.sqrt (Real.log (((d : ℝ) + 1) * K * T) / (c : ℝ))

/-- The Euclidean norm `‖v‖₂`. -/
noncomputable def norm2 (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ j, v j ^ 2)

/-- Line 5, p.15: the update of the confidence bounds at the end of an epoch, from the first `m`
rounds.

**Formalization Note.** An arm with no sample has `∇_k = ∞`, and its bounds keep their old values. -/
noncomputable def updateBounds (P : Problem d n K) {t : ℕ} (h : History n K t) (m : ℕ)
    (D : EpochBounds d K) : EpochBounds d K where
  Urew k :=
    if (pulls h m k).card = 0 then D.Urew k
    else min (ENNReal.ofReal (∑ j, P.p k j * empMean h m k j +
      norm2 (P.p k) * confRadius d K P.T (pulls h m k).card)) (D.Urew k)
  Lrew k :=
    if (pulls h m k).card = 0 then D.Lrew k
    else max (∑ j, P.p k j * empMean h m k j -
      norm2 (P.p k) * confRadius d K P.T (pulls h m k).card) (D.Lrew k)
  Ucost i k :=
    if (pulls h m k).card = 0 then D.Ucost i k
    else min (ENNReal.ofReal (∑ j, P.A i j * empMean h m k j +
      norm2 (P.A i) * confRadius d K P.T (pulls h m k).card)) (D.Ucost i k)
  Lcost i k :=
    if (pulls h m k).card = 0 then D.Lcost i k
    else max (∑ j, P.A i j * empMean h m k j -
      norm2 (P.A i) * confRadius d K P.T (pulls h m k).card) (D.Lcost i k)

/-- The state at the start of an epoch: the end `T_{l-1}` of the previous epoch, the current arm
`z_{T_{l-1}}`, and the confidence bounds. -/
structure EpochState (d K : ℕ) where
  /-- `T_{l-1}`. -/
  start : ℕ
  /-- The current arm. -/
  cur : Fin K
  /-- The confidence bounds. -/
  bounds : EpochBounds d K

/-- The planned amounts of epoch `l` (`1`-based) before scaling by `γ`: `N^l_k` of lines 9 and 12,
p.16. -/
noncomputable def epochWeight (P : Problem d n K) (ν : ℕ) (sel : Selector d n K) {t : ℕ}
    (h : History n K t) (l : ℕ) (st : EpochState d K) (k : Fin K) : ℝ :=
  if l ≤ ν then
    ((tSched P.T K ν l : ℝ) - (tSched P.T K ν (l - 1) : ℝ)) / (P.T : ℝ) *
      ∑ j, (1 / (K : ℝ)) * sel.explore l st.bounds j k
  else
    ((P.T : ℝ) - (tSched P.T K ν ν : ℝ)) / (P.T : ℝ) * sel.final (empMean h st.start) k

/-- The number of consecutive periods of arm `k` in epoch `l`: `⌈γ N^l_k⌉₊`.

**Formalization Note.** The page overlooks rounding ("easy to fix"). A ceiling keeps `n_k ≥ γ N_k`,
as (EC.19) needs. A negative `t_l - t_{l-1}`, possible when `T < K`, gives `0`. -/
noncomputable def epochPlan (P : Problem d n K) (ν : ℕ) (sel : Selector d n K) {t : ℕ}
    (h : History n K t) (l : ℕ) (st : EpochState d K) (k : Fin K) : ℕ :=
  ⌈gammaLS P ν * epochWeight P ν sel h l st k⌉₊

/-- The arm at offset `u` of an epoch that plays the arms of the list `L`, each `m a` times in a
row; `none` past the end. -/
def armAt (m : Fin K → ℕ) : List (Fin K) → ℕ → Action K
  | [], _ => none
  | a :: L, u => if u < m a then some a else armAt m L (u - m a)

/-- The arm in force after the epoch: the last arm of the list played a positive number of times, or
the arm `c` in force before it. -/
def lastArm (m : Fin K → ℕ) (L : List (Fin K)) (c : Fin K) : Fin K :=
  L.foldl (fun c a => if 0 < m a then a else c) c

/-- Replaying the algorithm on a history: `epochState … l` is the state after `l` epochs (so at the
start of epoch `l + 1`). The state after `l` epochs reads only the rounds before `T_l`. -/
noncomputable def epochState (P : Problem d n K) (ν : ℕ) (z₀ : Fin K) (sel : Selector d n K)
    {t : ℕ} (h : History n K t) : ℕ → EpochState d K
  | 0 => ⟨0, z₀, initBounds⟩
  | l + 1 =>
    let st := epochState P ν z₀ sel h l
    let m := epochPlan P ν sel h (l + 1) st
    let T' := st.start + ∑ k, m k
    ⟨T', lastArm m (sel.order (l + 1) m st.cur) st.cur, updateBounds P h T' st.bounds⟩

/-- The action of LS-2SLP in the round after history `h`: find the epoch containing the round, and
take its arm at that offset; after epoch `ν + 1` the algorithm has ended, and the action is `none`
(footnote 5, p.17).

**Formalization Note.** Every epoch before the one found has ended by round `t`, so the action
depends on rounds that have happened. -/
noncomputable def ls2slpAction (P : Problem d n K) (s : ℕ) (z₀ : Fin K) (sel : Selector d n K)
    {t : ℕ} (h : History n K t) : Action K :=
  let ν := nu s d K
  match (List.range (ν + 1)).find? (fun l => t < (epochState P ν z₀ sel h (l + 1)).start) with
  | none => none
  | some l =>
    let st := epochState P ν z₀ sel h l
    let m := epochPlan P ν sel h (l + 1) st
    armAt m (sel.order (l + 1) m st.cur) (t - st.start)

/-- `ϕ` is the LS-2SLP policy (Algorithm 2, pp.15–16) for switching budget `s`: for some initial arm
`z₀` and some valid choices, `ϕ` plays the algorithm's action deterministically.

**Formalization Note.** Stated for a given kernel, so that measurability is not buried in a
definition; the existence of such a `ϕ` is part of Theorem 3's statement. The page's random `z₀` is
a mixture of these policies. -/
def IsLS2SLP (P : Problem d n K) (s : ℕ) (φ : Policy n K) : Prop :=
  ∃ (z₀ : Fin K) (sel : Selector d n K), sel.Valid P ∧
    ∀ (t : ℕ) (h : History n K t), φ.select t h = Measure.dirac (ls2slpAction P s z₀ sel h)

end BlindNRMLS


