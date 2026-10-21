-- Prove2me | Definitions.Def_HochbaumShmoys_Uniform_LayeredGraph
-- name    : HochbaumShmoys_Uniform_LayeredGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:43.85098+00:00
-- url     : https://prove2.me/theorems/ce36352a-ca3c-41bc-a816-fccec7d9633c
-- title:
--   The multilayered graph of all-pack: state vectors, configuration and update arcs, traced packings (§3, pp. 544–548)
-- statement:
--   Fix $N\ge2$, $\delta=1/N$, and a normalized instance: bins $\beta_1\ge\beta_2\ge\dots\ge\beta_m>0$ with $\beta_1=1$, listed in packing order, and pieces $\pi_1,\dots,\pi_n\in(0,1]$. Intervals, rounded sizes and the $w+1=N^2-N+1$ rounding classes are those of the rounding definition; $\kappa_t$ is the interval index of bin $t$. The bins of one interval form a **stage**.
--
--   1. **State vectors** $(L;M;V_1,V_2,V)$ for a stage with bin interval $k$: $L_c$ and $M_c$ (each between $0$ and $n$) count the remaining pieces of interval $k$, resp. $k+1$, in class $c$; $V_1,V_2,V$ are the unused capacities of the enormous, huge and large bins in units $\delta^{k+2},\delta^{k+3},\delta^{k+4}$, taking values $0,1,\dots,nN^2+1$, where the top value stands for every multiple greater than $n/\delta^2=nN^2$ (larger values are **capped** to it).
--   2. **Layers and nodes.** A stage with $m_k$ bins has $m_k+1$ layers, each holding one node per state vector; the first layer of the first stage holds only the **initial** node, whose state is the distribution of the pieces of $(\delta,1]$ and $(\delta^2,\delta]$ with $V_1=V_2=V=0$. A final node **success** is added.
--   3. **Configuration arcs** (conditions (1)–(3), p. 545). Across bin $t$ of a stage with interval $k$, an arc goes from state $u$ to state $v$ in the next layer when $x=L(u)-L(v)\ge0$ and $\bar x=M(u)-M(v)\ge0$ componentwise, $V_1,V_2$ are unchanged, the configuration is feasible,
--   $$\sum_c x_c (N+c)\delta^{k+2}+\sum_c \bar x_c (N+c)\delta^{k+3}\le\beta_t ,$$
--   and $V(v)=V(u)+\lceil \mathrm{slack}_t/\delta^{k+4}\rceil$ (capped), $\mathrm{slack}_t$ being $\beta_t$ minus the left-hand side.
--   4. **Update arcs** (function *update*, p. 546) go from the final layer of a stage with interval $k$ to the first layer of the next stage, $q$ intervals away. With $W_1=V_1\delta^{k+2}-\sum_c L_c(N+c)\delta^{k+2}$, $W_2=W_1+V_2\delta^{k+3}-\sum_c M_c(N+c)\delta^{k+3}$, and $W_3=W_2+V\delta^{k+4}-R$, where $R$ is the total rounded size of the pieces of intervals $k+2,\dots,k+q-1$: the update fails if $W_1<0$, or $q\ge2$ and $W_2<0$, or $q\ge3$ and $W_3<0$. Otherwise, with $W=W_1,W_2,W_3$ for $q=1$, $q=2$, $q\ge3$ and $v_1=W/\delta^{k+q+2}$, the head has $L$ = the remaining interval-$(k+1)$ pieces if $q=1$ (all pieces of interval $k+q$ if $q\ge2$), $M$ = all pieces of interval $k+q+1$, $(V_1,V_2)=(v_1+V_2,\,V)$, $(v_1+V,\,0)$, $(v_1,\,0)$ for $q=1$, $q=2$, $q\ge3$ (capped), and $V=0$.
--   5. **Success arcs** go from the final layer of the last stage when *update* with $q=\infty$ (all three tests, $R$ summing over all intervals $\ge k+2$) does not fail.
--   6. **Traced packings** (p. 548). A packing $\sigma$ (bin indices in packing order) is traced from an initial–success path if (a) no piece goes into a bin of larger interval index than its own; (b) for each bin $t$ and class $c$, the pieces of interval $\kappa_t$ (large) and of interval $\kappa_t+1$ (medium) of class $c$ that $\sigma$ puts into bin $t$ are exactly as many as the path's configuration across bin $t$ prescribes; (c) the remaining (small) pieces are placed one at a time, update phase after update phase (the phase of a piece is the largest bin interval not exceeding its own), each into a bin whose **usable slack** $\lceil \mathrm{slack}_t/\delta^{\kappa_t+4}\rceil\,\delta^{\kappa_t+4}$, minus the rounded sizes of the small pieces placed into it before, is still positive.
--
--   Node and arc counts are those of this graph; the procedure all-pack outputs the traced packings.
--
--   **Formalization Note** States are indexed by the $w+1$ rounding classes (finding F4). Nodes are `pre t u` (layer before bin $t$), `fin t u` (final layer of the stage of $t$, present when $t$ is the last bin of its stage) and `success`; the initial node is `pre 0` with the initial state, and arcs leave the first layer only from it. The paper's double sum $\sum_{t=2}^{q-1}\sum_i n_i^{(t)}l_i^{(t)}$ is written as a sum of rounded sizes over pieces. The paper's "simpler" variant is used for the end: success arcs leave the final layer of the last stage directly when *update* with $q=\infty$ succeeds. A path is also given layer by layer (`IsLayeredPath`), which is how traced packings refer to it.
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, pp. 544–546, §3 (state vectors, layers, arcs (1)–(3), usable slack, function update, success) and p. 548, proof of Lemma 4 (converting a path to a packing)

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Rounding

namespace HochbaumShmoys.Uniform

open Finset

/-! The multilayered graph of all-pack (§3, pp. 544–546) for the parameter `δ = 1/N`, built on a
normalized instance: bins `β : Fin m → ℝ` listed in the order in which they are packed
(non-increasing size, `β 0 = 1`) and pieces `π : Fin n → ℝ` in `(0, 1]`. -/

/-- Number of rounding classes per interval: `w + 1 = N² − N + 1`. -/
abbrev numClasses (N : ℕ) : ℕ := N ^ 2 - N + 1

/-- The cap on the slack counters: one value `n · N² + 1` stands for every multiple greater
than `n/δ² = n · N²`. -/
abbrev slackCap (N n : ℕ) : ℕ := n * N ^ 2 + 1

/-- A state vector `(L; M; V₁, V₂, V)` for a stage with bin interval `k`: `L c` and `M c` count the
remaining pieces of interval `k` and of interval `k + 1` in rounding class `c`; `V₁`, `V₂`, `V`
are the unused capacities of the enormous, huge and large bins in units of `δ^(k+2)`,
`δ^(k+3)`, `δ^(k+4)`, capped at `slackCap N n`. -/
structure StateVector (N n : ℕ) where
  L : Fin (numClasses N) → Fin (n + 1)
  M : Fin (numClasses N) → Fin (n + 1)
  V₁ : Fin (slackCap N n + 1)
  V₂ : Fin (slackCap N n + 1)
  V : Fin (slackCap N n + 1)
deriving DecidableEq, Fintype

/-- Saturating conversion of a natural number to a capped slack counter. -/
def capSlack (N n : ℕ) (x : ℕ) : Fin (slackCap N n + 1) :=
  ⟨min x (slackCap N n), Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- `n^(k)_c`: the number of pieces of interval `k` in rounding class `c`. -/
noncomputable def pieceCount (N : ℕ) {n : ℕ} (π : Fin n → ℝ) (k c : ℕ) : Fin (n + 1) :=
  ⟨(univ.filter (fun j => intervalIndex N (π j) = k ∧ roundClass N (π j) = c)).card,
    Nat.lt_succ_of_le ((card_filter_le _ _).trans (by simp))⟩

/-- The state vector of the initial node: the distribution of the pieces of interval 0,
`(δ, 1]`, and of interval 1, `(δ², δ]`, with `V₁ = V₂ = V = 0`. -/
noncomputable def initialState (N : ℕ) {n : ℕ} (π : Fin n → ℝ) : StateVector N n where
  L := fun c => pieceCount N π 0 c
  M := fun c => pieceCount N π 1 c
  V₁ := 0
  V₂ := 0
  V := 0

/-- The all-zero state vector. -/
def zeroState (N n : ℕ) : StateVector N n where
  L := fun _ => 0
  M := fun _ => 0
  V₁ := 0
  V₂ := 0
  V := 0

/-- Total rounded size `Σ_c x_c l_c + Σ_c x̄_c l̄_c` of the configuration `x = L(u) − L(v)`,
`x̄ = M(u) − M(v)` leading from state `u` to state `v` in a stage with bin interval `k`. -/
noncomputable def configSize (N : ℕ) {n : ℕ} (k : ℕ) (u v : StateVector N n) : ℝ :=
  ∑ c : Fin (numClasses N), (((u.L c : ℕ) - (v.L c : ℕ) : ℕ) : ℝ) * classSize N k c +
  ∑ c : Fin (numClasses N), (((u.M c : ℕ) - (v.M c : ℕ) : ℕ) : ℝ) * classSize N (k + 1) c

/-- Conditions (1)–(3) of p. 545: in a stage with bin interval `k`, a node with state `v` in the
next layer is reachable from a node with state `u` through a bin of size `b` if
(1) `v = u − (x; x̄)` for a configuration of nonnegative integers `(x; x̄)` and `V₁`, `V₂` are
unchanged, (2) the configuration is feasible (`configSize ≤ b`), and
(3) `V = V' + ⌈slack/δ^(k+4)⌉` (capped), where `slack = b − configSize`. -/
def IsConfigArc (N : ℕ) {n : ℕ} (k : ℕ) (b : ℝ) (u v : StateVector N n) : Prop :=
  (∀ c, (v.L c : ℕ) ≤ u.L c) ∧ (∀ c, (v.M c : ℕ) ≤ u.M c) ∧
  v.V₁ = u.V₁ ∧ v.V₂ = u.V₂ ∧
  configSize N k u v ≤ b ∧
  v.V = capSlack N n ((u.V : ℕ) +
    ⌈(b - configSize N k u v) / ((N : ℝ)⁻¹) ^ (k + 4)⌉₊)

/-- The function `update` of p. 546, applied at the end of the stage for bin interval `k`, when
the next interval containing bins is `q` intervals away (`q = none` stands for `q = ∞`: there are
no more bins). It returns `none` for "failure", and otherwise the state vector of the head of
the update arc. The sum `Σ_{t=2}^{q−1} Σ_i n_i^(t) l_i^(t)` is written as the total rounded size
of the pieces whose interval lies in `[k + 2, k + q)` (in `[k + 2, ∞)` when `q = ∞`). -/
noncomputable def update (N : ℕ) {n : ℕ} (π : Fin n → ℝ) (k : ℕ) (q : Option ℕ)
    (u : StateVector N n) : Option (StateVector N n) :=
  let δ : ℝ := (N : ℝ)⁻¹
  let W₁ : ℝ := (u.V₁ : ℕ) * δ ^ (k + 2) - ∑ c, ((u.L c : ℕ) : ℝ) * classSize N k c
  let W₂ : ℝ := W₁ + (u.V₂ : ℕ) * δ ^ (k + 3) - ∑ c, ((u.M c : ℕ) : ℝ) * classSize N (k + 1) c
  let rest : ℝ := ∑ j ∈ univ.filter (fun j => k + 2 ≤ intervalIndex N (π j) ∧
      ∀ q' : ℕ, q = some q' → intervalIndex N (π j) < k + q'), roundDown N (π j)
  let W₃ : ℝ := W₂ + (u.V : ℕ) * δ ^ (k + 4) - rest
  match q with
  | none => if W₁ < 0 ∨ W₂ < 0 ∨ W₃ < 0 then none else some (zeroState N n)
  | some q =>
    if W₁ < 0 ∨ (2 ≤ q ∧ W₂ < 0) ∨ (3 ≤ q ∧ W₃ < 0) then none
    else
      let v₁ : ℕ := ⌊(if q ≤ 1 then W₁ else if q = 2 then W₂ else W₃) / δ ^ (k + q + 2)⌋₊
      some
        { L := if q ≤ 1 then u.M else fun c => pieceCount N π (k + q) c
          M := fun c => pieceCount N π (k + q + 1) c
          V₁ := capSlack N n
            (if q ≤ 1 then v₁ + (u.V₂ : ℕ) else if q = 2 then v₁ + (u.V : ℕ) else v₁)
          V₂ := capSlack N n (if q ≤ 1 then (u.V : ℕ) else 0)
          V := 0 }

/-- The interval index of the `t`-th bin; the stages are the distinct values of this index. -/
noncomputable def binInterval (N : ℕ) {m : ℕ} (β : Fin m → ℝ) (t : Fin m) : ℕ :=
  intervalIndex N (β t)

/-- Bin `t` is the last bin of its stage: the next bin (if any) lies in another interval. -/
def IsLastOfStage (N : ℕ) {m : ℕ} (β : Fin m → ℝ) (t : Fin m) : Prop :=
  ∀ h : t.val + 1 < m, binInterval N β ⟨t.val + 1, h⟩ ≠ binInterval N β t

/-- Nodes of the layered graph. `pre t u`: the node with state `u` in the layer just before bin
`t` is packed (in the stage of bin `t`); `fin t u`: the node with state `u` in the final layer of
the stage of bin `t` (used when `t` is the last bin of its stage); `success`. -/
inductive Node (m N n : ℕ)
  | pre (t : Fin m) (u : StateVector N n)
  | fin (t : Fin m) (u : StateVector N n)
  | success
deriving DecidableEq, Fintype

/-- The arcs of the layered graph: configuration arcs between consecutive layers of a stage
(only the initial state is kept in the first layer of the first stage), update arcs from the
final layer of a stage to the first layer of the next stage, `q` intervals away, and arcs into
`success` from the final layer of the last stage when `update` with `q = ∞` succeeds. -/
def Arc (N : ℕ) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ) :
    Node m N n → Node m N n → Prop
  | .pre t u, .pre t' v =>
      t'.val = t.val + 1 ∧ binInterval N β t' = binInterval N β t ∧
      (t.val = 0 → u = initialState N π) ∧ IsConfigArc N (binInterval N β t) (β t) u v
  | .pre t u, .fin t' v =>
      t' = t ∧ IsLastOfStage N β t ∧
      (t.val = 0 → u = initialState N π) ∧ IsConfigArc N (binInterval N β t) (β t) u v
  | .fin t u, .pre t' v =>
      t'.val = t.val + 1 ∧ IsLastOfStage N β t ∧
      update N π (binInterval N β t) (some (binInterval N β t' - binInterval N β t)) u = some v
  | .fin t u, .success =>
      t.val + 1 = m ∧ (update N π (binInterval N β t) none u).isSome
  | _, _ => False

/-- The initial node: the initial state in the first layer of the first stage. -/
noncomputable def initialNode (N : ℕ) {m n : ℕ} (π : Fin n → ℝ) (hm : 0 < m) : Node m N n :=
  .pre ⟨0, hm⟩ (initialState N π)

/-- The nodes of the graph: every state vector in every layer, except that the first layer
holds only the initial node, and a final layer exists only at the end of a stage. -/
def IsGraphNode (N : ℕ) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ) : Node m N n → Prop
  | .pre t u => t.val = 0 → u = initialState N π
  | .fin t _ => IsLastOfStage N β t
  | .success => True

/-- Number of nodes of the graph. -/
noncomputable def nodeCount (N : ℕ) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ) : ℕ :=
  Nat.card {v : Node m N n // IsGraphNode N β π v}

/-- Number of arcs of the graph. -/
noncomputable def arcCount (N : ℕ) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ) : ℕ :=
  Nat.card {e : Node m N n × Node m N n // Arc N β π e.1 e.2}

/-- A path from initial to success, given layer by layer: `pre t` is its state in the layer
before bin `t`, `fin t` its state in the final layer of the stage of `t` (used only when `t` is
the last bin of its stage). -/
def IsLayeredPath (N : ℕ) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ)
    (pre fin : Fin m → StateVector N n) : Prop :=
  (∀ (t : Fin m) (h : t.val + 1 < m), binInterval N β ⟨t.val + 1, h⟩ = binInterval N β t →
      Arc N β π (.pre t (pre t)) (.pre ⟨t.val + 1, h⟩ (pre ⟨t.val + 1, h⟩))) ∧
  (∀ t : Fin m, IsLastOfStage N β t → Arc N β π (.pre t (pre t)) (.fin t (fin t))) ∧
  (∀ (t : Fin m) (h : t.val + 1 < m), IsLastOfStage N β t →
      Arc N β π (.fin t (fin t)) (.pre ⟨t.val + 1, h⟩ (pre ⟨t.val + 1, h⟩))) ∧
  (∀ t : Fin m, t.val + 1 = m → Arc N β π (.fin t (fin t)) .success)

/-- The state of the path right after bin `t` has been packed. -/
noncomputable def afterBin (N : ℕ) {m n : ℕ} (β : Fin m → ℝ) (pre fin : Fin m → StateVector N n)
    (t : Fin m) : StateVector N n :=
  if h : t.val + 1 < m then
    (if binInterval N β ⟨t.val + 1, h⟩ = binInterval N β t then pre ⟨t.val + 1, h⟩ else fin t)
  else fin t

/-- Usable slack of bin `t` along the path: `⌈slack_t/δ^(k+4)⌉ · δ^(k+4)`, where `k` is the
bin's interval and `slack_t` is the bin size minus the rounded size of its configuration. -/
noncomputable def usableSlack (N : ℕ) {m n : ℕ} (β : Fin m → ℝ)
    (pre fin : Fin m → StateVector N n) (t : Fin m) : ℝ :=
  (⌈(β t - configSize N (binInterval N β t) (pre t) (afterBin N β pre fin t)) /
      ((N : ℝ)⁻¹) ^ (binInterval N β t + 4)⌉ : ℝ) * ((N : ℝ)⁻¹) ^ (binInterval N β t + 4)

/-- The update phase in which a piece of size `x` is packed as a small piece: the largest bin
interval that is at most the piece's interval. -/
noncomputable def smallPhase (N : ℕ) {m : ℕ} (β : Fin m → ℝ) (x : ℝ) : ℕ :=
  (univ.filter (fun t => binInterval N β t ≤ intervalIndex N x)).sup (binInterval N β)

/-- Piece `j` is packed by `σ` as a small piece (its interval is at least the bin's plus 2). -/
abbrev IsSmallIn (N : ℕ) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ) (σ : Fin n → Fin m)
    (j : Fin n) : Prop :=
  binInterval N β (σ j) + 2 ≤ intervalIndex N (π j)

/-- The packing `σ` is traced from the path `(pre, fin)` by the rules of p. 548:
(1) no piece is put into a bin of a larger interval index than its own;
(2) the large and medium pieces put into bin `t` realize the configuration of the path's arc
across bin `t`, class by class (pieces chosen arbitrarily within a class);
(3) the small pieces are placed one at a time (the order `ρ`), update phase by update phase, each
into a bin whose usable slack, decreased by the rounded sizes of the small pieces placed into
it earlier, is still positive. -/
def IsTracedFrom (N : ℕ) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ)
    (pre fin : Fin m → StateVector N n) (σ : Fin n → Fin m) : Prop :=
  (∀ j, binInterval N β (σ j) ≤ intervalIndex N (π j)) ∧
  (∀ (t : Fin m) (c : Fin (numClasses N)),
    (univ.filter (fun j => σ j = t ∧ intervalIndex N (π j) = binInterval N β t ∧
        roundClass N (π j) = c.val)).card =
      ((pre t).L c : ℕ) - ((afterBin N β pre fin t).L c : ℕ)) ∧
  (∀ (t : Fin m) (c : Fin (numClasses N)),
    (univ.filter (fun j => σ j = t ∧ intervalIndex N (π j) = binInterval N β t + 1 ∧
        roundClass N (π j) = c.val)).card =
      ((pre t).M c : ℕ) - ((afterBin N β pre fin t).M c : ℕ)) ∧
  ∃ ρ : Fin n → ℕ, Function.Injective ρ ∧
    (∀ j j', IsSmallIn N β π σ j → IsSmallIn N β π σ j' →
      smallPhase N β (π j) < smallPhase N β (π j') → ρ j < ρ j') ∧
    (∀ j, IsSmallIn N β π σ j →
      ∑ j' ∈ univ.filter (fun j' => IsSmallIn N β π σ j' ∧ σ j' = σ j ∧ ρ j' < ρ j),
          roundDown N (π j') < usableSlack N β pre fin (σ j))

/-- A packing of the normalized instance traced from some initial–success path. -/
def IsTracedPacking (N : ℕ) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ)
    (σ : Fin n → Fin m) : Prop :=
  ∃ pre fin : Fin m → StateVector N n,
    IsLayeredPath N β π pre fin ∧ IsTracedFrom N β π pre fin σ

end HochbaumShmoys.Uniform


