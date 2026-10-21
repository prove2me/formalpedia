-- Prove2me | Definitions.Def_UCConvexHull_OneUC_Model
-- name    : UCConvexHull_OneUC_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:15.756553+00:00
-- url     : https://prove2.me/theorems/4d60f854-cc75-4900-afd7-e1f43cd53589
-- title:
--   §2, §4, §5, pp. 6–19 — single thermal unit, DP state-space graph G, flow system (18), scaled dispatch blocks (19) with perspective epigraph, formulation (26)
-- statement:
--   This file fixes the single-unit commitment model of Bacci, Frangioni, Gentile and Tavlaridis-Gyparakis and their formulation (26).
--
--   **The unit (§2, pp. 6–8).** The horizon is $T=\{1,\dots,n\}$, and $T(t',t'')$ denotes the periods from $t'$ to $t''$ (empty if $t'>t''$). The unit has minimum up and down times $\tau^+,\tau^-$ (numbers of consecutive periods); an initial state $\tau^0\ne 0$ (on for $\tau^0$ periods if $\tau^0>0$, off for $-\tau^0$ periods if $\tau^0<0$); minimum and maximum outputs $l,u$; start-up and shut-down limits $\bar l,\bar u$; ramp limits $\Delta^+,\Delta^-$; and a generation cost $f:\mathbb R\to\mathbb R$. The standing assumptions are
--
--   $$\tau^\pm\ge 1,\quad l\le\bar l\le u,\quad l\le\bar u\le u,\quad 0\le\Delta^\pm\le u-l,\quad f \text{ convex}.$$
--
--   **The DP graph $G=(N,A)$ (§4, pp. 12–14).** The nodes are a source $s$, a sink $d$, and $ON_t$, $OFF_t$ for $t\in T$. The arcs are:
--   1. ON arcs $(OFF_h,ON_k)$ for $h,k\in T$ with $k\ge h+\tau^+-1$; their pairs form $A_{ON}$;
--   2. OFF arcs $(ON_k,OFF_r)$ for $k,r\in T$ with $r\ge k+\tau^-+1$; their pairs form $A_{OFF}$;
--   3. if $\tau^0>0$, arcs $(s,ON_k)$ for $k\in T$ with $k+\tau^0\ge\tau^+$; if $\tau^0<0$, arcs $(s,OFF_h)$ for $h\in T$ with $h-\tau^0-1\ge\tau^-$;
--   4. $(ON_t,d)$ and $(OFF_t,d)$ for every $t\in T$, and $(s,d)$.
--
--   **The flow system (18), p. 15.** With $E$ the node–arc incidence matrix of $G$ and $\delta$ zero except $\delta_s=-1$, $\delta_d=1$, the flow polytope is $\{\,y : Ey=\delta,\ y\ge 0\,\}$: at every node, inflow minus outflow equals $\delta$.
--
--   **The dispatch block of an ON arc (19), (26), pp. 15 and 18.** For $(h,k)\in A_{ON}$, with arc variable $y=y^{hk}_+$, power variables $p_t=p^{hk}_t$ for $t\in T(h,k)$ and an epigraph variable $z=z^{hk}$, the block consists of $0\le y\le 1$ and
--
--   $$\begin{aligned}
--   &l\,y\le p_h\le\bar l\,y,\qquad l\,y\le p_t\le u\,y\ \ (t\in T(h+1,k-1)),\qquad l\,y\le p_k\le\bar u\,y,\\
--   &p_{t+1}\le p_t+y\,\Delta^+,\qquad p_t\le p_{t+1}+y\,\Delta^-\qquad (t\in T(h,k-1)),\\
--   &z\ \ge\ \sum_{t\in T(h,k)} y\,f(p_t/y).
--   \end{aligned}$$
--
--   The last line is the perspective epigraph of (26). At $y=0$ the bounds force $p=0$ and the term $y\,f(p_t/y)$ is read as $0$.
--
--   **Formulation (26), pp. 18–19.** Its constraint set (the continuous relaxation) is the set of $(y,(p^{hk},z^{hk})_{(h,k)\in A_{ON}})$ such that $y$ satisfies (18) and, for every $(h,k)\in A_{ON}$, $(y^{hk}_+,p^{hk},z^{hk})$ lies in the dispatch block of $(h,k)$. Its mixed-integer points are those whose arc variables are all $0$ or $1$. The partial compositions of the proof of Theorem 1 (p. 19) impose the dispatch blocks only for the pairs of a subset $J\subseteq A_{ON}$.
--
--   These objects state Theorem 1 and its milestones.
--
--   **Formalization Note.**
--   1. Periods are natural numbers, so the paper's indices are kept. The rule $k\ge h+\tau^+-1$ is written $h+\tau^+\le k+1$, and the source rules are evaluated in $\mathbb Z$.
--   2. Each power vector $p^{hk}$ is stored as a vector indexed by $\{0,\dots,n\}$, and its coordinates outside $T(h,k)$ are required to be $0$, so that only the paper's variables are free. Pairs outside $J$ in the partial compositions have $p^{hk}=0$ and $z^{hk}=0$.
--   3. Dispatch blocks are attached to the pairs of $A_{ON}$ only, as printed in (26). The ON-type source and sink arcs $(s,ON_k)$, $(OFF_t,d)$ and $(s,d)$ (pp. 13–14) are plain flow arcs without power variables.
--   4. (26) has one epigraph variable per arc, $z^{hk}\ge\sum_t y^{hk}_+f(p^{hk}_t/y^{hk}_+)$; (21) uses one per period. Both forms are defined: `block` is the aggregated (26) form, while `block21` is the period-wise (21) form.
--   5. Arc costs $\tilde c$ enter only the linear objective and are not modelled; the statements concern the constraint sets.
--   6. The hypotheses $\tau^\pm\ge 1$ are added: they are minimum numbers of periods, and they make $G$ acyclic.
-- source:
--   Bacci, Frangioni, Gentile, Tavlaridis-Gyparakis, New MINLP Formulations for the Unit Commitment Problems with Ramping Constraints, manuscript submitted to Operations Research (PDF sha256 eee1c5a4…e224), pp. 6–8 (§2), pp. 12–14 (§4), pp. 15–19 (§5), (18), (19), (26), proof of Theorem 1

import Mathlib

namespace UCConvexHull.OneUC

/-! # The single thermal unit, the DP graph `G` and formulation (26)

Bacci, Frangioni, Gentile, Tavlaridis-Gyparakis, *New MINLP Formulations for the Unit Commitment
Problems with Ramping Constraints* (manuscript submitted to Operations Research): the unit data of §2
(pp. 6–8), the state-space graph `G` of §4 (pp. 12–14), and the flow system (18), the scaled
dispatch constraints (19) with the perspective epigraph, and formulation (26) of §5 (pp. 15–19).
Periods are the natural numbers `T = {1, …, n}`; all values are real. -/

/-- The data of one thermal unit (§2, pp. 6–8; the unit index `i` is dropped as on p. 15). -/
structure ThermalUnit where
  /-- the horizon: `T = {1, …, n}` -/
  n : ℕ
  /-- `τ⁺`, the minimum number of consecutive periods on -/
  τup : ℕ
  /-- `τ⁻`, the minimum number of consecutive periods off -/
  τdn : ℕ
  /-- `τ⁰`, the initial state: on for `τ⁰` periods if `τ⁰ > 0`, off for `−τ⁰` periods if `τ⁰ < 0` -/
  τ0 : ℤ
  /-- minimum power output `l` -/
  l : ℝ
  /-- maximum power output `u` -/
  u : ℝ
  /-- start-up limit `l̄` -/
  lbar : ℝ
  /-- shut-down limit `ū` -/
  ubar : ℝ
  /-- ramp-up limit `Δ⁺` -/
  Δup : ℝ
  /-- ramp-down limit `Δ⁻` -/
  Δdn : ℝ
  /-- the generation cost `f` -/
  f : ℝ → ℝ

/-- The standing assumptions of §2 (pp. 7–8) and Theorem 1: `τ±` are minimum numbers of periods
(at least 1), `τ⁰ ≠ 0`, `l ≤ l̄ ≤ u`, `l ≤ ū ≤ u`, `0 ≤ Δ± ≤ u − l`, and a convex cost `f`. -/
def ThermalUnit.Standing (U : ThermalUnit) : Prop :=
  1 ≤ U.τup ∧ 1 ≤ U.τdn ∧ U.τ0 ≠ 0 ∧
  U.l ≤ U.lbar ∧ U.lbar ≤ U.u ∧ U.l ≤ U.ubar ∧ U.ubar ≤ U.u ∧
  0 ≤ U.Δup ∧ U.Δup ≤ U.u - U.l ∧ 0 ≤ U.Δdn ∧ U.Δdn ≤ U.u - U.l ∧
  ConvexOn ℝ Set.univ U.f

/-- The nodes of `G` (p. 13): the source `s`, the sink `d`, and `ON_t`, `OFF_t`. -/
inductive Node
  | src
  | snk
  | on (t : ℕ)
  | off (t : ℕ)
  deriving DecidableEq

/-- The periods `T = {1, …, n}` (p. 6). -/
def periods (U : ThermalUnit) : Finset ℕ := Finset.Icc 1 U.n

/-- `A_ON` (p. 15): the pairs `(h, k)`, `h, k ∈ T`, with `k ≥ h + τ⁺ − 1` (ON arcs `(OFF_h, ON_k)`, p. 13). -/
def onPairs (U : ThermalUnit) : Finset (ℕ × ℕ) :=
  (periods U ×ˢ periods U).filter (fun hk => hk.1 + U.τup ≤ hk.2 + 1)

/-- `A_OFF` (p. 15): the pairs `(k, r)`, `k, r ∈ T`, with `r ≥ k + τ⁻ + 1` (OFF arcs `(ON_k, OFF_r)`, p. 13). -/
def offPairs (U : ThermalUnit) : Finset (ℕ × ℕ) :=
  (periods U ×ˢ periods U).filter (fun kr => kr.1 + U.τdn + 1 ≤ kr.2)

/-- The arcs leaving the source (pp. 13–14): if `τ⁰ > 0`, `(s, ON_k)` for `k ∈ T` with
`k + τ⁰ ≥ τ⁺`; otherwise (`τ⁰ < 0`), `(s, OFF_h)` for `h ∈ T` with `h − τ⁰ − 1 ≥ τ⁻`. -/
def srcArcs (U : ThermalUnit) : Finset (Node × Node) :=
  if 0 < U.τ0 then
    ((periods U).filter (fun k : ℕ => (U.τup : ℤ) ≤ (k : ℤ) + U.τ0)).image (fun k => (Node.src, Node.on k))
  else
    ((periods U).filter (fun h : ℕ => (U.τdn : ℤ) ≤ (h : ℤ) - U.τ0 - 1)).image (fun h => (Node.src, Node.off h))

/-- The arc set `A` of `G` (pp. 13–14): ON arcs, OFF arcs, source arcs, `(ON_t, d)` and `(OFF_t, d)`
for every `t ∈ T`, and `(s, d)`. -/
def arcs (U : ThermalUnit) : Finset (Node × Node) :=
  (onPairs U).image (fun hk => (Node.off hk.1, Node.on hk.2)) ∪
  (offPairs U).image (fun kr => (Node.on kr.1, Node.off kr.2)) ∪
  srcArcs U ∪
  (periods U).image (fun t => (Node.on t, Node.snk)) ∪
  (periods U).image (fun t => (Node.off t, Node.snk)) ∪
  {(Node.src, Node.snk)}

/-- The node set `N` of `G` (p. 13). -/
def nodes (U : ThermalUnit) : Finset Node :=
  {Node.src, Node.snk} ∪ (periods U).image Node.on ∪ (periods U).image Node.off

/-- The right-hand side `δ` of (18) (p. 15): `δ_s = −1`, `δ_d = 1`, zero elsewhere. -/
def demand : Node → ℝ
  | .src => -1
  | .snk => 1
  | _ => 0

/-- Flow conservation `Ey = δ` of (18): at every node, inflow minus outflow equals `δ`. -/
def FlowCons (U : ThermalUnit) (y : arcs U → ℝ) : Prop :=
  ∀ v ∈ nodes U,
    (∑ e : arcs U with e.1.2 = v, y e) - (∑ e : arcs U with e.1.1 = v, y e) = demand v

/-- The flow polytope `{ y : Ey = δ, y ≥ 0 }` of (18) (p. 15). -/
def flowPoly (U : ThermalUnit) : Set (arcs U → ℝ) :=
  {y | FlowCons U y ∧ ∀ e, 0 ≤ y e}

/-- The ON arc `(OFF_h, ON_k)` of a pair `(h, k) ∈ A_ON`. -/
def onArc (U : ThermalUnit) (a : onPairs U) : arcs U :=
  ⟨(Node.off a.1.1, Node.on a.1.2), by
    unfold arcs
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Finset.mem_image_of_mem _ a.2)))))⟩

/-- Reads the power vector `p ∈ ℝ^{0,…,n}` at period `t` (zero beyond `n`). -/
def pAt (U : ThermalUnit) (p : Fin (U.n + 1) → ℝ) (t : ℕ) : ℝ :=
  if ht : t < U.n + 1 then p ⟨t, ht⟩ else 0

/-- The dispatch block of the ON arc `(h, k)` in (26): points `(y, p, z)` with `y = y^{hk}_+ ∈ [0, 1]`,
the constraints (19) multiplied by `y` (p. 15), `p_t = 0` for `t ∉ T(h, k)`, and the perspective
epigraph `z ≥ Σ_{t ∈ T(h,k)} y f(p_t / y)` of (26) (p. 18). -/
def block (U : ThermalUnit) (h k : ℕ) : Set (ℝ × (Fin (U.n + 1) → ℝ) × ℝ) :=
  {q |
    0 ≤ q.1 ∧ q.1 ≤ 1 ∧
    U.l * q.1 ≤ pAt U q.2.1 h ∧ pAt U q.2.1 h ≤ U.lbar * q.1 ∧
    (∀ t ∈ Finset.Icc (h + 1) (k - 1), U.l * q.1 ≤ pAt U q.2.1 t ∧ pAt U q.2.1 t ≤ U.u * q.1) ∧
    U.l * q.1 ≤ pAt U q.2.1 k ∧ pAt U q.2.1 k ≤ U.ubar * q.1 ∧
    (∀ t ∈ Finset.Ico h k, pAt U q.2.1 (t + 1) ≤ pAt U q.2.1 t + q.1 * U.Δup) ∧
    (∀ t ∈ Finset.Ico h k, pAt U q.2.1 t ≤ pAt U q.2.1 (t + 1) + q.1 * U.Δdn) ∧
    (∀ t : Fin (U.n + 1), ((t : ℕ) < h ∨ k < (t : ℕ)) → q.2.1 t = 0) ∧
    (∑ t ∈ Finset.Icc h k, q.1 * U.f (pAt U q.2.1 t / q.1)) ≤ q.2.2}

/-- The per-period perspective epigraph in (21), p. 16. The aggregate epigraph inequality
from `block` is redundant here: summing the per-period inequalities yields it. Coordinates of
`z` outside `T(h,k)` are set to zero to embed the paper's finite vector in `Fin (n+1) → ℝ`. -/
def block21 (U : ThermalUnit) (h k : ℕ) :
    Set (ℝ × (Fin (U.n + 1) → ℝ) × (Fin (U.n + 1) → ℝ)) :=
  {q | (q.1, q.2.1, ∑ t ∈ Finset.Icc h k, pAt U q.2.2 t) ∈ block U h k ∧
    (∀ t ∈ Finset.Icc h k,
      q.1 * U.f (pAt U q.2.1 t / q.1) ≤ pAt U q.2.2 t) ∧
    (∀ t : Fin (U.n + 1), ((t : ℕ) < h ∨ k < (t : ℕ)) → q.2.2 t = 0)}

/-- The ambient space of (26): arc flows `y`, and for each `(h, k) ∈ A_ON` a power vector `p^{hk}`
and an epigraph variable `z^{hk}`. -/
abbrev Space (U : ThermalUnit) : Type :=
  (arcs U → ℝ) × (onPairs U → Fin (U.n + 1) → ℝ) × (onPairs U → ℝ)

/-- The constraint set of (26) with `y^{hk}_+ ∈ [0, 1]` (the continuous relaxation): (18), and the
dispatch block of every `(h, k) ∈ A_ON` on the variables `(y^{hk}_+, p^{hk}, z^{hk})`. -/
def relax (U : ThermalUnit) : Set (Space U) :=
  {x | x.1 ∈ flowPoly U ∧ ∀ a : onPairs U, (x.1 (onArc U a), x.2.1 a, x.2.2 a) ∈ block U a.1.1 a.1.2}

/-- The mixed-integer points of (26): the points of `relax` whose arc variables are all `0` or `1`. -/
def mixedInt (U : ThermalUnit) : Set (Space U) :=
  {x | x ∈ relax U ∧ ∀ e, x.1 e = 0 ∨ x.1 e = 1}

/-- The partial composition `S₀ ⊕ S^{h₁k₁} ⊕ ⋯` of the proof of Theorem 1 (p. 19), relaxed: (18),
the dispatch blocks of the pairs in `J`, and the variables `p^{hk}`, `z^{hk}` of pairs outside `J`
set to zero. -/
def relaxJ (U : ThermalUnit) (J : Finset (onPairs U)) : Set (Space U) :=
  {x | x.1 ∈ flowPoly U ∧
    (∀ a ∈ J, (x.1 (onArc U a), x.2.1 a, x.2.2 a) ∈ block U a.1.1 a.1.2) ∧
    (∀ a ∉ J, x.2.1 a = 0 ∧ x.2.2 a = 0)}

/-- The mixed-integer points of `relaxJ U J`: all arc variables `0` or `1` (the set `S_j`, p. 19). -/
def mixedIntJ (U : ThermalUnit) (J : Finset (onPairs U)) : Set (Space U) :=
  {x | x ∈ relaxJ U J ∧ ∀ e, x.1 e = 0 ∨ x.1 e = 1}

end UCConvexHull.OneUC


