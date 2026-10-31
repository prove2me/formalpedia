-- Prove2me | Definitions.Def_PacketFlowConv_Discretization
-- name    : PacketFlowConv_Discretization
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:35.247408+00:00
-- url     : https://prove2.me/theorems/67f73ad0-54b0-4d58-8099-072e65402403
-- title:
--   §2.1–2.2, §4 — packet routing: Algorithms 1–2, $L^\pm_e(t)$, $g^\pm_{j,e}$, $G^\pm_{j,e}$, refined arrival times $\ell^D_{j,v}$, $z^D$, $q^D$, $T^D$
-- statement:
--   A **discretization** consists of a time step length $\alpha>0$, a packet size $\beta>0$, a tie-breaking rule for Algorithm 1 and a release order. It determines the **packet routing** of the instance:
--
--   1. **Packets** (§4, p.10): $N_j=\{1,\dots,\lfloor m_j/\beta\rfloor\}$ with path $P_j$; packet $i$ is released in time step $\hat r_i=r_i/\alpha$, $r_i:=\min\{\theta\in\alpha\mathbb N_0:\int_0^\theta u_j\ge i\beta\}$.
--   2. **Arcs** (§2.1–2.2, pp.3–4): $\hat\tau_e=\lceil\tau_e\rceil_\alpha/\alpha$, $\hat\nu_e=\nu_e\alpha/\beta$. The queue $Q_e(t)$ holds packets with their entrance step; the buffer $B_e(t)$ is the longest run of oldest packets that entered at step $\le t-\hat\tau_e$; the leaving packets $L^-_e(t)$ are its first $\lfloor\hat\nu_e(t)\rfloor$ packets; the current capacity follows (1): $\hat\nu_e(0)=\hat\nu_e$ and $\hat\nu_e(t)=\hat\nu_e$ if $|B_e(t-1)|\le\hat\nu_e(t-1)$, else $\hat\nu_e+\hat\nu_e(t-1)-\lfloor\hat\nu_e(t-1)\rfloor$.
--   3. **Node transition** (Algorithm 1, p.5): at node $v$, for each outgoing arc $e$ the packets moving into $e$ from each incoming arc (and the packets released at $v$, treated as one more incoming arc) are merged zipper-style by priority counters $k/y_{e'}$, ties broken by the rule.
--   4. **Network loading** (Algorithm 2, p.7): $Q_e(t+1)=Q_e(t)-L^-_e(t)+L^+_e(t)$.
--
--   From the loading (p.10): $g^\pm_{j,e}(\theta)=\frac\beta\alpha\,|\{i\in N_j: i\in L^\pm_e(\lceil\theta\rceil_\alpha/\alpha)\}|$, $G^\pm_{j,e}(\theta)=\int_0^\theta g^\pm_{j,e}$, totals over $J_e$, and the **refined arrival time** $\ell^D_{j,v}(i)=\min\{\theta\ge0:G^+_{j,vw}(\theta)\ge i\beta\}$ ($vw\in P_j$), resp. with $G^-_{j,ud_j}$ at $v=d_j$. On p.11: $z^D_{j,e}(t)=G^+_{j,e}(t-\lceil\tau_e\rceil_\alpha)-G^-_{j,e}(t)$, $z^D_e=\sum_{j\in J_e}z^D_{j,e}$,
--   $$q^D_{j,e}(\theta)=\min\Big\{q\ge0:\int_{\theta+\lceil\tau_e\rceil_\alpha}^{\theta+\lceil\tau_e\rceil_\alpha+q}g^-_{j,e}\ \ge z^D_{j,e}(\theta+\lceil\tau_e\rceil_\alpha)\Big\},\qquad T^D_{j,e}(\theta)=\theta+\lceil\tau_e\rceil_\alpha+q^D_{j,e}(\theta).$$
--   The packet of particle $\varphi$ is $\max(1,\lceil\varphi/\beta\rceil)$ (p.14).
--
--   **Formalization Note** Packets are pairs $(j,i)$ with the paper's 1-based index; the loading is a state recursion over steps $t\in\mathbb N$. The buffer is taken at the head of the queue (the paper's "suffix" refers to the same oldest packets). The tie-break may depend on the node, the arc, the step, the round of the merge loop and the set of tied sources; a valid rule picks a tied source. The release order is any order increasing in the packet index within each commodity. $g^\pm$ vanish before time $0$.
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, §2.1 p.3, §2.2 pp.3–7 (Buffer, (1), Leaving packets, Released packets, Algorithms 1–2), §4 pp.10–11

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics

open MeasureTheory

namespace PacketFlowConv

/-- The zipper merge of Algorithm 1 (node transition, p.5) for one outgoing arc. The sources are
`s ∈ S` (`some e'` for an incoming arc `e'`, `none` for the node itself, "treated as an incoming
arc"); `Y s` is the remaining list of packets of source `s`, `y s = |Y_s|` its initial length. In
each round the active sources are those with `Y s` nonempty (the set `A`); the counter of source
`s` after `c` pops is `a_s = (c + 1)/y_s`; the source `e*` with the least counter is chosen,
ties being broken by `tb n tied` (round `n`, set `tied` of minimizers); its first packet is
appended to the output. `fuel` bounds the number of rounds (it is the total number of packets).

**Formalization Note.** "ties are broken arbitrarily (but deterministically)": the rule `tb` may
depend on the round and on the set of tied sources; a valid rule returns an element of a
nonempty `tied` (`Discretization.Valid`). -/
noncomputable def mergeAux {X S' : Type} [DecidableEq S'] (tb : ℕ → Finset S' → S')
    (S : Finset S') (y : S' → ℕ) : ℕ → ℕ → (S' → List X) → List X
  | 0, _, _ => []
  | fuel + 1, n, Y =>
    let A := S.filter (fun s => (Y s).isEmpty = false)
    if hA : A.Nonempty then
      let key : S' → ℚ := fun s => (((y s - (Y s).length : ℕ) : ℚ) + 1) / (y s : ℚ)
      let m := A.inf' hA key
      let s := tb n (A.filter (fun s => key s = m))
      match Y s with
      | [] => []
      | x :: rest => x :: mergeAux tb S y fuel (n + 1) (Function.update Y s rest)
    else []

/-- Discretization data of one packet routing (§2.1 p.3, §2.2 pp.3–7): the time step length `α`,
the packet size `β`, the tie-breaking rule `tb v e t` of the node transition of Algorithm 1 at node
`v`, outgoing arc `e`, time step `t`, and the release order `σ` (packets released at one node in
one time step are processed in increasing `σ`). -/
structure Discretization (V E J : Type) where
  /-- time step length `α` -/
  α : ℝ
  /-- packet size `β` -/
  β : ℝ
  /-- tie-breaking rule of Algorithm 1 -/
  tb : V → E → ℕ → ℕ → Finset (Option E) → Option E
  /-- release order of the packets `(j, i)` -/
  σ : J × ℕ → ℕ

/-- Validity of the discretization: `α, β > 0` (p.3); the tie-break picks one of the tied
sources; the release order is increasing in the packet index within each commodity (p.4:
"the ordering is given by the packet index"). -/
structure Discretization.Valid {V E J : Type} (D : Discretization V E J) : Prop where
  α_pos : 0 < D.α
  β_pos : 0 < D.β
  tb_mem : ∀ v e t n (S : Finset (Option E)), S.Nonempty → D.tb v e t n S ∈ S
  σ_mono : ∀ (j : J) (i i' : ℕ), i < i' → D.σ (j, i) < D.σ (j, i')

/-- State of the network loading at a time step (Algorithm 2, p.7): the arc queues `Q_e(t)`
(packets with their arc-entrance time step, oldest first) and the current capacities `ν̂_e(t)`. -/
structure LoadState (E J : Type) where
  /-- arc queues, head = oldest packet -/
  queue : E → List ((J × ℕ) × ℕ)
  /-- current capacities `ν̂_e(t)` -/
  cap : E → ℝ

namespace Instance

variable {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype J] [DecidableEq J] (I : Instance V E J) (D : Discretization V E J)

/-- `|N_j| = ⌊m_j/β⌋`: the packets of commodity `j` are `(j, i)` with `i ∈ N_j = {1, …, ⌊m_j/β⌋}`
(§4, p.10). -/
noncomputable def nPk (j : J) : ℕ := ⌊I.mass j / D.β⌋₊

/-- `τ̂_e := ⌈τ_e⌉_α / α ∈ ℕ` (p.3), the number of time steps to traverse `e`. -/
noncomputable def tauHat (e : E) : ℕ := ⌈I.τ e / D.α⌉₊

/-- `ν̂_e := ν_e · α / β` (p.3), the per-step packet capacity. -/
noncomputable def nuHat (e : E) : ℝ := I.ν e * D.α / D.β

/-- The release time step `r̂_i = r_i/α` of packet `i ∈ N_j`, where
`r_i := min { θ ∈ Θ_α | ∫_0^θ u_j(ξ) dξ ≥ i · β }` (§4, p.10). -/
noncomputable def relStep (p : J × ℕ) : ℕ :=
  sInf {t : ℕ | (p.2 : ℝ) * D.β ≤ ∫ ξ in (0 : ℝ)..((t : ℝ) * D.α), I.u p.1 ξ}

/-- All packets `(j, i)`, `j ∈ J`, `1 ≤ i ≤ |N_j|`. -/
noncomputable def packets : List (J × ℕ) :=
  (Finset.univ : Finset J).toList.flatMap (fun j => (List.range' 1 (I.nPk D j)).map (fun i => (j, i)))

/-- `L⁻_v(t)`: the packets released into the network at node `v` in time step `t` (p.4, and
Algorithm 2), in increasing release order `σ`. -/
noncomputable def released (t : ℕ) (v : V) : List (J × ℕ) :=
  ((I.packets D).filter (fun p => decide (I.relStep D p = t) && decide (I.o p.1 = v))).mergeSort
    (fun a b => decide (D.σ a ≤ D.σ b))

/-- Algorithm 1 (p.5), node transition at `v` in time step `t`, for the outgoing arc `e`: given
the leaving packets `lm e'` of all arcs and the released packets `rel` at `v`, the list
`L⁺_e(t)` of packets entering `e`. `Y_{e'}` is the ordered sublist of `L⁻_{e'}` (for `e'` with head
`v`) of packets whose path continues with `e` after `e'`; `Y_v` is the ordered sublist of `rel` of
packets whose path starts with `e`. -/
noncomputable def nodeTransition (lm : E → List (J × ℕ)) (rel : List (J × ℕ)) (v : V) (t : ℕ)
    (e : E) : List (J × ℕ) :=
  let Y : Option E → List (J × ℕ) := fun s =>
    match s with
    | some e' => if I.G.head e' = v then (lm e').filter (fun p => I.nextArc p.1 e' = some e) else []
    | none => rel.filter (fun p => (I.P p.1).head? = some e)
  let S : Finset (Option E) := insert none (Finset.univ.image some)
  mergeAux (D.tb v e t) S (fun s => (Y s).length) (∑ s ∈ S, (Y s).length) 0 Y

/-- The buffer `B_e(t)` (p.3): the maximal initial segment (oldest packets) of `Q_e(t)` whose
arc-entrance time step is at most `t − τ̂_e`.

**Formalization Note.** pp.3–4 call `B_e(t)` and `L⁻_e(t)` "suffixes" of the queue while
Algorithm 2 appends entering packets at the end; the head of the queue is meant ("the first
`⌊ν̂_e(t)⌋` packets in line"). -/
noncomputable def buffer (s : LoadState E J) (t : ℕ) (e : E) : List ((J × ℕ) × ℕ) :=
  (s.queue e).takeWhile (fun x => decide (x.2 + I.tauHat D e ≤ t))

/-- The leaving packets `L⁻_e(t)` (p.4): the first `⌊ν̂_e(t)⌋` packets of the buffer. -/
noncomputable def leaving (s : LoadState E J) (t : ℕ) (e : E) : List (J × ℕ) :=
  ((I.buffer D s t e).take ⌊s.cap e⌋₊).map Prod.fst

/-- The entering packets `L⁺_e(t)` (Algorithms 1–2), computed at the tail of `e`. -/
noncomputable def entering (s : LoadState E J) (t : ℕ) (e : E) : List (J × ℕ) :=
  I.nodeTransition D (I.leaving D s t) (I.released D t (I.G.tail e)) (I.G.tail e) t e

/-- One iteration of the loop of Algorithm 2 (p.7): `Q_e(t+1) = Q_e(t) − L⁻_e(t) + L⁺_e(t)` with
arc-entrance step `t` for the entering packets, and the current capacity update (1), p.4:
`ν̂_e(t+1) = ν̂_e` if `|B_e(t)| ≤ ν̂_e(t)`, else `ν̂_e + ν̂_e(t) − ⌊ν̂_e(t)⌋`. -/
noncomputable def step (s : LoadState E J) (t : ℕ) : LoadState E J where
  queue := fun e => (s.queue e).drop (I.leaving D s t e).length ++
    (I.entering D s t e).map (fun p => (p, t))
  cap := fun e => if ((I.buffer D s t e).length : ℝ) ≤ s.cap e then I.nuHat D e
    else I.nuHat D e + s.cap e - ⌊s.cap e⌋₊

/-- The state at time step `t` of the network loading (Algorithm 2): empty queues and
`ν̂_e(0) = ν̂_e` at `t = 0`. The loop runs for every `t ∈ ℕ` (after all packets have arrived the
state no longer changes). -/
noncomputable def state : ℕ → LoadState E J
  | 0 => { queue := fun _ => [], cap := fun e => I.nuHat D e }
  | t + 1 => I.step D (state t) t

/-- `L⁻_e(t)`, the packets leaving arc `e` in time step `t`. -/
noncomputable def Lminus (t : ℕ) (e : E) : List (J × ℕ) := I.leaving D (I.state D t) t e

/-- `L⁺_e(t)`, the packets entering arc `e` in time step `t`. -/
noncomputable def Lplus (t : ℕ) (e : E) : List (J × ℕ) := I.entering D (I.state D t) t e

/-- The inflow rate `g⁺_{j,e}(θ) := β/α · |{ i ∈ N_j | i ∈ L⁺_e(⌈θ⌉_α/α) }|` for `θ ≥ 0`
(§4, p.10, extended to be constant on each time step), and `0` for `θ < 0`. -/
noncomputable def gPlus (j : J) (e : E) (θ : ℝ) : ℝ :=
  if 0 ≤ θ then D.β / D.α * ((I.Lplus D ⌈θ / D.α⌉₊ e).countP (fun p => p.1 = j) : ℝ) else 0

/-- The outflow rate `g⁻_{j,e}(θ) := β/α · |{ i ∈ N_j | i ∈ L⁻_e(⌈θ⌉_α/α) }|` for `θ ≥ 0`
(§4, p.10), and `0` for `θ < 0`. -/
noncomputable def gMinus (j : J) (e : E) (θ : ℝ) : ℝ :=
  if 0 ≤ θ then D.β / D.α * ((I.Lminus D ⌈θ / D.α⌉₊ e).countP (fun p => p.1 = j) : ℝ) else 0

/-- The cumulative inflow `G⁺_{j,e}(θ) := ∫_0^θ g⁺_{j,e}(ξ) dξ` (p.10). -/
noncomputable def Gplus (j : J) (e : E) (θ : ℝ) : ℝ := cum (I.gPlus D j e) θ

/-- The cumulative outflow `G⁻_{j,e}(θ) := ∫_0^θ g⁻_{j,e}(ξ) dξ` (p.10). -/
noncomputable def Gminus (j : J) (e : E) (θ : ℝ) : ℝ := cum (I.gMinus D j e) θ

/-- The total inflow rate `g⁺_e := Σ_{j ∈ J_e} g⁺_{j,e}` (p.10). -/
noncomputable def gPlusTot (e : E) (θ : ℝ) : ℝ := ∑ j ∈ I.Je e, I.gPlus D j e θ

/-- The total outflow rate `g⁻_e := Σ_{j ∈ J_e} g⁻_{j,e}` (p.10). -/
noncomputable def gMinusTot (e : E) (θ : ℝ) : ℝ := ∑ j ∈ I.Je e, I.gMinus D j e θ

/-- The total cumulative inflow `G⁺_e := Σ_{j ∈ J_e} G⁺_{j,e}` (p.10). -/
noncomputable def GplusTot (e : E) (θ : ℝ) : ℝ := ∑ j ∈ I.Je e, I.Gplus D j e θ

/-- The total cumulative outflow `G⁻_e := Σ_{j ∈ J_e} G⁻_{j,e}` (p.10). -/
noncomputable def GminusTot (e : E) (θ : ℝ) : ℝ := ∑ j ∈ I.Je e, I.Gminus D j e θ

/-- The refined arrival time (p.10) of packet `i ∈ N_j` at node `v` of `P_j`:
`ℓ^D_{j,v}(i) := min { θ ∈ ℝ≥0 | G⁺_{j,vw}(θ) ≥ i·β }` for the arc `vw ∈ P_j` leaving `v`
(`v ≠ d_j`), and `min { θ ∈ ℝ≥0 | G⁻_{j,ud_j}(θ) ≥ i·β }` for `v = d_j`. -/
noncomputable def ellD (j : J) (v : V) (i : ℕ) : ℝ :=
  match I.outArc j v with
  | some e => sInf {θ | 0 ≤ θ ∧ (i : ℝ) * D.β ≤ I.Gplus D j e θ}
  | none =>
    match I.lastArc j with
    | some e => sInf {θ | 0 ≤ θ ∧ (i : ℝ) * D.β ≤ I.Gminus D j e θ}
    | none => 0

/-- The commodity-specific queue size (p.11), `z^D_{j,e}(θ + ⌈τ_e⌉_α) := G⁺_{j,e}(θ) −
G⁻_{j,e}(θ + ⌈τ_e⌉_α)`, i.e. `z^D_{j,e}(t) = G⁺_{j,e}(t − ⌈τ_e⌉_α) − G⁻_{j,e}(t)`. -/
noncomputable def zD (j : J) (e : E) (t : ℝ) : ℝ :=
  I.Gplus D j e (t - ceilGrid D.α (I.τ e)) - I.Gminus D j e t

/-- The total queue size `z^D_e := Σ_{j ∈ J_e} z^D_{j,e}` (p.11). -/
noncomputable def zDTot (e : E) (t : ℝ) : ℝ := ∑ j ∈ I.Je e, I.zD D j e t

/-- The waiting time (p.11): `q^D_{j,e}(θ) := min { q ≥ 0 | ∫_{θ+⌈τ_e⌉_α}^{θ+⌈τ_e⌉_α+q}
g⁻_{j,e}(ξ) dξ ≥ z^D_{j,e}(θ + ⌈τ_e⌉_α) }`. -/
noncomputable def qD (j : J) (e : E) (θ : ℝ) : ℝ :=
  sInf {q | 0 ≤ q ∧ I.zD D j e (θ + ceilGrid D.α (I.τ e)) ≤
    ∫ ξ in (θ + ceilGrid D.α (I.τ e))..(θ + ceilGrid D.α (I.τ e) + q), I.gMinus D j e ξ}

/-- The exit time (p.11): `T^D_{j,e}(θ) := θ + ⌈τ_e⌉_α + q^D_{j,e}(θ)`. -/
noncomputable def TD (j : J) (e : E) (θ : ℝ) : ℝ := θ + ceilGrid D.α (I.τ e) + I.qD D j e θ

end Instance

/-- The packet carrying particle `φ`: `⌈φ/β⌉` (Theorem 2, Lemma 4), with particle `0` in packet
`1` (p.14: "Particle 0 is a special case for which we explicitly include it into packet 1"). -/
noncomputable def Discretization.packetOf {V E J : Type} (D : Discretization V E J) (φ : ℝ) : ℕ :=
  max 1 ⌈φ / D.β⌉₊

end PacketFlowConv


