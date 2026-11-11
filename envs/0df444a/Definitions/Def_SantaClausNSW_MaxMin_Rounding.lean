-- Prove2me | Definitions.Def_SantaClausNSW_MaxMin_Rounding
-- name    : SantaClausNSW_MaxMin_Rounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:35:54.497835+00:00
-- url     : https://prove2.me/theorems/5cbd7e5a-1928-4c2d-85ad-1efdb311c89a
-- title:
--   The configuration setting of §3.1, GKPS dependent rounding and the Shmoys–Tardos assignment of §3.2
-- statement:
--   The **setting of §3.1** is an explicit configuration solution $y$ (rational masses; the configurations $C_i$ of agent $i$ are those of positive mass), rational coefficients $a^{i,S}_j\ge0$ for $j\in S$, a threshold $\tau>0$ and sets $L_i\subseteq C_i$ of large configurations, such that every $S\in L_i$ is a singleton $\{j\}$ with $a^{i,S}_j\ge\tau$ and every small configuration $S\in S_i=C_i\setminus L_i$ has $a^{i,S}_j<\tau$ for all $j\in S$. With $b_j=\sum_{i:\{j\}\in L_i}y_{i,\{j\}}$, $f_j=1-b_j$ and $\mu_{i,S}=\sum_{j\in S}a^{i,S}_jf_j$, condition (7) with bound $B$ is
--   $$\sum_i\sum_{S\in S_i}y_{i,S}\min\{1,(32\tau/\mu_{i,S})^3\}\le B,$$
--   the minimum read as $1$ when $\mu_{i,S}=0$.
--
--   **The bipartite graph of §3.2** has the agents on the left and on the right a vertex per item and a private vertex $u_{i,S}$ per small configuration; edge $(i,j)$ has mass $y_{i,\{j\}}$ for $\{j\}\in L_i$ and edge $(i,u_{i,S})$ has mass $y_{i,S}$. **GKPS dependent rounding**: while some edge is fractional, a rule picks a cycle or a maximal path of the fractional edges, splits it into alternate edge sets $M_1,M_2$, sets $\alpha=\min(\min_{M_1}(1-x),\min_{M_2}x)$, $\beta=\min(\min_{M_1}x,\min_{M_2}(1-x))$, and with probability $\beta/(\alpha+\beta)$ adds $\alpha$ on $M_1$ and subtracts it on $M_2$, otherwise subtracts $\beta$ on $M_1$ and adds it on $M_2$.
--
--   From the final matching: agent $i$ selects $S_i=\{j\}$ (happy) if matched to item $j$ and $S_i=S$ (unhappy) if matched to $u_{i,S}$; $F_j=1$ if item $j$ was not taken as a singleton; $C_j$ counts the unhappy agents with $j\in S_i$; $X_i=\sum_{j\in S_i}a^{i,S_i}_jF_j/C_j$. **Shmoys–Tardos**: each unhappy agent lists its remaining items in nonincreasing order of $a^{i,S_i}_j$, packs the fractions $1/C_j$ into unit slots, and a matching in the support of this slot assignment covering every full slot assigns the items; $A_i$ is $\{j\}$ for a happy agent and the items matched to its slots otherwise.
--
--   The module also fixes the input encodings of Lemma 3.1 (records $i,y_{i,S},1_S,(a^{i,S}_j)_j,1_{S\in L_i}$), Theorem 3.5 (records with a clause) and Lemma 3.10 (records $i,y_{i,S},1_S$), each listing every configuration of positive mass once, in any order.
--
--   **Formalization Note.** The right vertices are all items and all pairs $(k,S)$; those the paper does not create have only zero-mass edges and are isolated. The rule is any deterministic function of the current masses that returns a cycle (at least four distinct vertices) or a path with distinct vertices whose two ends have exactly one fractional edge each. The order and slot matching are any functions of the final masses satisfying `STValid`.
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), pp. 11–13 §3.1–3.2; p. 17; p. 25

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Valuations
import Definitions.Def_SantaClausNSW_MaxMin_Machine
import Definitions.Def_SantaClausNSW_MaxMin_Oracles

namespace SantaClausNSW.MaxMin

/-!
# The configuration setting of §3.1 and the rounding algorithm of §3.2

Chen, Feng, Hu, Li, Zhang, *Santa Claus and Weighted Nash Social Welfare with Subadditive
Valuations*, arXiv:2611.05229 (held version, sha256 98a235d3…), pp. 11–13 (§3.1, §3.2), p. 17
(Theorem 3.5's input), p. 25 (Lemma 3.10's input).

* `Setting`: an explicit configuration solution with configuration-dependent coefficients
  `a^{i,S}_j`, a threshold `τ` and the large configurations `L_i`; `b_j`, `f_j` (5), the baseline
  `µ_{i,S}` (6) and the term `min{1, (32τ/µ)^3}` of (7), read as `1` when `µ = 0`.
* `gkpsLaw`: the bipartite dependent rounding of Gandhi–Khuller–Parthasarathy–Srinivasan on the
  graph of §3.2, for an arbitrary deterministic rule choosing the cycle or maximal path.
* `STValid`, `stAlloc`: the Shmoys–Tardos slot assignment of §3.2, for an arbitrary sorted order
  and an arbitrary matching covering the full slots.
* input encodings of the explicit inputs of Lemma 3.1, Theorem 3.5 and Lemma 3.10.
-/

/-- The data of the setting of §3.1 (p. 11): masses `y_{i,S}` (the configurations `C_i` are the
support), coefficients `a^{i,S}_j`, the threshold `τ` and the large configurations `L_i`. -/
structure Setting (n m : ℕ) where
  /-- The masses `y_{i,S}`. -/
  y : Fin n → Finset (Fin m) → ℚ
  /-- The coefficients `a^{i,S}_j` (used for `j ∈ S`). -/
  a : Fin n → Finset (Fin m) → Fin m → ℚ
  /-- The threshold `τ`. -/
  τ : ℚ
  /-- The large configurations `L_i`. -/
  L : Fin n → Finset (Finset (Fin m))

namespace Setting

variable {n m : ℕ} (st : Setting n m)

/-- The configurations `C_i` of agent `i`: those of positive mass (zero-mass configurations are
omitted, p. 11). -/
def C (i : Fin n) : Finset (Finset (Fin m)) := Finset.univ.filter (fun S => 0 < st.y i S)

/-- The small configurations `S_i = C_i \ L_i`. -/
def Sm (i : Fin n) : Finset (Finset (Fin m)) := st.C i \ st.L i

/-- The additive function `a^{i,S}(Q) = ∑_{j ∈ Q} a^{i,S}_j`. -/
def coef (i : Fin n) (S Q : Finset (Fin m)) : ℚ := ∑ j ∈ Q, st.a i S j

/-- The assumptions of §3.1 (pp. 11–12): `y` is a feasible configuration solution ((2), (3));
`τ > 0`; the coefficients are nonnegative; `C_i = L_i ⊎ S_i` where every `S ∈ L_i` is a
singleton `{j}` with `a^{i,S}(S) ≥ τ` and every `S ∈ S_i` has `a^{i,S}_j < τ` for all `j ∈ S`. -/
def Valid : Prop :=
  IsConfigSolution (fun i S => (st.y i S : ℝ)) ∧
  0 < st.τ ∧
  (∀ i S, S ∈ st.C i → ∀ j ∈ S, 0 ≤ st.a i S j) ∧
  (∀ i, st.L i ⊆ st.C i) ∧
  (∀ i, ∀ S ∈ st.L i, ∃ j, S = {j} ∧ st.τ ≤ st.coef i S S) ∧
  (∀ i, ∀ S ∈ st.Sm i, ∀ j ∈ S, st.a i S j < st.τ)

/-- `b_j = ∑_{i : {j} ∈ L_i} y_{i,{j}}`, (5). -/
def b (j : Fin m) : ℚ := ∑ i : Fin n, if ({j} : Finset (Fin m)) ∈ st.L i then st.y i {j} else 0

/-- `f_j = 1 − b_j`, (5). -/
def f (j : Fin m) : ℚ := 1 - st.b j

/-- The baseline value `µ_{i,S} = ∑_{j ∈ S} a^{i,S}_j f_j`, (6). -/
def μ (i : Fin n) (S : Finset (Fin m)) : ℚ := ∑ j ∈ S, st.a i S j * st.f j

/-- `min{1, (32τ/µ_{i,S})^3}`, interpreted as `1` when `µ_{i,S} = 0` (p. 12). -/
def failTerm (i : Fin n) (S : Finset (Fin m)) : ℚ :=
  if st.μ i S = 0 then 1 else min 1 ((32 * st.τ / st.μ i S) ^ 3)

/-- The left side of (7) is at most `B`: `∑_i ∑_{S ∈ S_i} y_{i,S} min{1, (32τ/µ_{i,S})^3} ≤ B`. -/
def Budget (B : ℚ) : Prop :=
  ∑ i : Fin n, ∑ S ∈ st.Sm i, st.y i S * st.failTerm i S ≤ B

end Setting

/-! ## The bipartite graph of §3.2 and dependent rounding -/

/-- Right vertices: an item vertex `j` and a private vertex `u_{k,S}` for every agent `k` and
set `S`. Vertices the paper does not create (items with `b_j = 0`, pairs `(k, S)` that are not
small configurations of `k`) are isolated: every edge at them has mass `0`. -/
abbrev RV (n m : ℕ) := Fin m ⊕ (Fin n × Finset (Fin m))

/-- An edge between agent `i` and a right vertex. -/
abbrev Edge (n m : ℕ) := Fin n × RV n m

/-- A vertex: an agent (left) or a right vertex. -/
abbrev Vtx (n m : ℕ) := Fin n ⊕ RV n m

/-- The initial edge masses (p. 12): `y_{i,{j}}` on `(i, j)` for `{j} ∈ L_i`, `y_{i,S}` on
`(i, u_{i,S})` for `S ∈ S_i`, and `0` elsewhere. -/
def Setting.x0 {n m : ℕ} (st : Setting n m) : Edge n m → ℝ := fun e =>
  match e with
  | (i, .inl j) => if ({j} : Finset (Fin m)) ∈ st.L i then (st.y i {j} : ℝ) else 0
  | (i, .inr (k, S)) => if k = i ∧ S ∈ st.Sm i then (st.y i S : ℝ) else 0

/-- The fractional degree `d_v = ∑_i x(i, v)` of a right vertex. -/
def degree {n m : ℕ} (x : Edge n m → ℝ) (r : RV n m) : ℝ := ∑ i : Fin n, x (i, r)

/-- The edge between two vertices, if they lie on different sides. -/
def edgeBetween {n m : ℕ} : Vtx n m → Vtx n m → Option (Edge n m)
  | .inl i, .inr r => some (i, r)
  | .inr r, .inl i => some (i, r)
  | _, _ => none

/-- A fractional edge: `0 < x_e < 1`. -/
def IsFrac {n m : ℕ} (x : Edge n m → ℝ) (e : Edge n m) : Prop := 0 < x e ∧ x e < 1

/-- `w` is an endpoint of `e`. -/
def Incident {n m : ℕ} (w : Vtx n m) (e : Edge n m) : Prop := w = .inl e.1 ∨ w = .inr e.2

/-- The consecutive vertex pairs of a walk; a closed walk also pairs the last vertex with the
first. -/
def walkPairs {n m : ℕ} (vs : List (Vtx n m)) (closed : Bool) : List (Vtx n m × Vtx n m) :=
  if closed then vs.zip (vs.tail ++ vs.take 1) else vs.zip vs.tail

/-- The edges of a walk, in order. -/
def walkEdges {n m : ℕ} (vs : List (Vtx n m)) (closed : Bool) : List (Edge n m) :=
  (walkPairs vs closed).filterMap (fun p => edgeBetween p.1 p.2)

/-- `w` has exactly one incident fractional edge (a leaf of the fractional subgraph). -/
def IsLeaf {n m : ℕ} (x : Edge n m → ℝ) (w : Vtx n m) : Prop :=
  ∃! e : Edge n m, Incident w e ∧ IsFrac x e

/-- `(vs, closed)` is a cycle (`closed = true`) or a maximal path (`closed = false`) of the
fractional subgraph: distinct vertices, consecutive vertices joined by fractional edges; a cycle
has at least `4` vertices, a maximal path at least `2` and ends at leaves of the fractional
subgraph (so it cannot be extended). -/
def IsCycleOrMaxPath {n m : ℕ} (x : Edge n m → ℝ) (vs : List (Vtx n m)) (closed : Bool) :
    Prop :=
  vs.Nodup ∧
  (∀ p ∈ walkPairs vs closed, ∃ e, edgeBetween p.1 p.2 = some e ∧ IsFrac x e) ∧
  ((closed = true ∧ 4 ≤ vs.length) ∨
   (closed = false ∧ 2 ≤ vs.length ∧ (∀ w ∈ vs.head?, IsLeaf x w) ∧
     (∀ w ∈ vs.getLast?, IsLeaf x w)))

/-- A deterministic rule choosing, from the current masses, the cycle or maximal path to round
on. -/
def GKPSRule (n m : ℕ) := (Edge n m → ℝ) → List (Vtx n m) × Bool

/-- The rule returns a cycle or maximal path of the fractional subgraph whenever some edge is
fractional. -/
def GKPSRule.Valid {n m : ℕ} (rule : GKPSRule n m) : Prop :=
  ∀ x : Edge n m → ℝ, (∃ e, IsFrac x e) → IsCycleOrMaxPath x (rule x).1 (rule x).2

/-- Split a list into its elements at even positions and at odd positions. -/
def splitAlt {α : Type*} : List α → List α × List α
  | [] => ([], [])
  | a :: rest => (a :: (splitAlt rest).2, (splitAlt rest).1)

/-- The minimum of a list of reals in `[0, 1]`, `1` for the empty list. -/
def minD (l : List ℝ) : ℝ := l.foldr min 1

open Classical in
/-- Add `δ` on the edges of `M1` and subtract it on the edges of `M2`. -/
noncomputable def shift {n m : ℕ} (x : Edge n m → ℝ) (M1 M2 : List (Edge n m)) (δ : ℝ) : Edge n m → ℝ :=
  fun e => if e ∈ M1 then x e + δ else if e ∈ M2 then x e - δ else x e

open Classical in
/-- A coin showing `true` with probability `p ∈ [0, 1]`. -/
noncomputable def coinWith (p : ℝ) : PMF Bool :=
  if h : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 then
    PMF.ofFintype (fun b => if b then ENNReal.ofReal p else ENNReal.ofReal (1 - p))
      (by simpa [Fintype.sum_bool] using h)
  else PMF.pure true

open Classical in
/-- One step of GKPS dependent rounding: if some edge is fractional, split the chosen cycle or
maximal path into its alternate edge sets `M1, M2`, let
`α = min(min_{M1}(1 − x), min_{M2} x)`, `β = min(min_{M1} x, min_{M2}(1 − x))`, and with
probability `β/(α + β)` add `α` on `M1` and subtract it on `M2`, otherwise subtract `β` on `M1`
and add it on `M2`. -/
noncomputable def gkpsStep {n m : ℕ} (rule : GKPSRule n m) (x : Edge n m → ℝ) :
    PMF (Edge n m → ℝ) :=
  if (∃ e, IsFrac x e) ∧ IsCycleOrMaxPath x (rule x).1 (rule x).2 then
    let es := walkEdges (rule x).1 (rule x).2
    let M1 := (splitAlt es).1
    let M2 := (splitAlt es).2
    let α := min (minD (M1.map fun e => 1 - x e)) (minD (M2.map fun e => x e))
    let β := min (minD (M1.map fun e => x e)) (minD (M2.map fun e => 1 - x e))
    (coinWith (β / (α + β))).map (fun c => if c then shift x M1 M2 α else shift x M1 M2 (-β))
  else PMF.pure x

/-- Iterate a random map `k` times. -/
noncomputable def iterPMF {α : Type*} (g : α → PMF α) : ℕ → α → PMF α
  | 0, a => PMF.pure a
  | k + 1, a => (g a).bind (iterPMF g k)

/-- The law of the final masses of GKPS dependent rounding from the graph of §3.2. Every step
makes at least one fractional edge integral and none fractional, so after
`|Edge n m|` steps no edge is fractional. -/
noncomputable def gkpsLaw {n m : ℕ} (st : Setting n m) (rule : GKPSRule n m) :
    PMF (Edge n m → ℝ) :=
  iterPMF (gkpsStep rule) (Fintype.card (Edge n m)) st.x0

/-- `χ_v = 1`: the right vertex `v` is matched in the final (integral) masses. -/
def Matched {n m : ℕ} (x : Edge n m → ℝ) (r : RV n m) : Prop := ∃ i, x (i, r) = 1

/-! ## The outcome of the §3.2 procedure, read from the final masses -/

open Classical in
/-- The right vertex agent `i` is matched to (if any). -/
noncomputable def matchedTo {n m : ℕ} (x : Edge n m → ℝ) (i : Fin n) : Option (RV n m) :=
  if h : ∃ r, x (i, r) = 1 then some h.choose else none

/-- The selected configuration `S_i`: `{j}` if `i` is matched to item `j`, `S` if `i` is
matched to `u_{i,S}`. -/
noncomputable def selConfig {n m : ℕ} (x : Edge n m → ℝ) (i : Fin n) : Finset (Fin m) :=
  match matchedTo x i with
  | some (.inl j) => {j}
  | some (.inr (_, S)) => S
  | none => ∅

/-- Agent `i` is happy: matched to an item. -/
def Happy {n m : ℕ} (x : Edge n m → ℝ) (i : Fin n) : Prop := ∃ j, matchedTo x i = some (.inl j)

open Classical in
/-- `F_j`: `1` if item `j` was not taken as a singleton, `0` otherwise. -/
noncomputable def Fv {n m : ℕ} (x : Edge n m → ℝ) (j : Fin m) : ℝ :=
  if ∃ i, x (i, .inl j) = 1 then 0 else 1

open Classical in
/-- `C_j`: the number of unhappy agents whose selected configuration contains `j`. -/
noncomputable def Cnt {n m : ℕ} (x : Edge n m → ℝ) (j : Fin m) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => ¬ Happy x i ∧ j ∈ selConfig x i)).card

/-- The fractional value `X_i = ∑_{j ∈ S_i} a^{i,S_i}_j F_j / C_j` (p. 13). -/
noncomputable def Setting.Xval {n m : ℕ} (st : Setting n m) (x : Edge n m → ℝ) (i : Fin n) :
    ℝ :=
  ∑ j ∈ selConfig x i, (st.a i (selConfig x i) j : ℝ) * Fv x j / (Cnt x j : ℝ)

open Classical in
/-- The fractional support of agent `i`: the items of `S_i` not taken as singletons. -/
noncomputable def fracSupport {n m : ℕ} (x : Edge n m → ℝ) (i : Fin n) : Finset (Fin m) :=
  (selConfig x i).filter (fun j => Fv x j = 1)

/-- The cumulative fraction `∑_{u < t} 1/C_{ord_u}` of the first `t` items of the order `ord`. -/
noncomputable def cum {n m : ℕ} (x : Edge n m → ℝ) (ord : List (Fin m)) (t : ℕ) : ℝ :=
  ((ord.take t).map (fun j => 1 / (Cnt x j : ℝ))).sum

/-- The `t`-th item of `ord` has a positive fraction in slot `s` (slot `s` is `[s, s + 1)`). -/
def SlotAdj {n m : ℕ} (x : Edge n m → ℝ) (ord : List (Fin m)) (t s : ℕ) : Prop :=
  max (cum x ord t) (s : ℝ) < min (cum x ord (t + 1)) ((s : ℝ) + 1)

/-- A valid Shmoys–Tardos assignment at the final masses `x` (p. 13): for every unhappy agent
`i`, `ord i` lists its fractional support in nonincreasing order of `a^{i,S_i}_j` (ties in any
order), and `M` (item ↦ (agent, slot)) is a matching in the support of the slot assignment that
covers every full slot `s` (`s + 1 ≤` total fraction) of every unhappy agent. -/
def Setting.STValid {n m : ℕ} (st : Setting n m) (x : Edge n m → ℝ)
    (ord : Fin n → List (Fin m)) (M : Fin m → Option (Fin n × ℕ)) : Prop :=
  (∀ i, ¬ Happy x i → (ord i).Perm (fracSupport x i).toList ∧
    (ord i).Pairwise (fun j j' => st.a i (selConfig x i) j' ≤ st.a i (selConfig x i) j)) ∧
  (∀ j j' p, M j = some p → M j' = some p → j = j') ∧
  (∀ j i s, M j = some (i, s) → ¬ Happy x i ∧
    ∃ t, (ord i)[t]? = some j ∧ SlotAdj x (ord i) t s) ∧
  (∀ i, ¬ Happy x i → ∀ s : ℕ, (s : ℝ) + 1 ≤ cum x (ord i) (ord i).length →
    ∃ j, M j = some (i, s))

/-- A rule choosing the sorted orders and the slot matching from the final masses. -/
def STRule (n m : ℕ) := (Edge n m → ℝ) → (Fin n → List (Fin m)) × (Fin m → Option (Fin n × ℕ))

open Classical in
/-- The bundles `A_i` of the §3.2 procedure: `{j}` for a happy agent matched to `j`, the items
matched to its slots for an unhappy agent. -/
noncomputable def stAlloc {n m : ℕ} (x : Edge n m → ℝ) (M : Fin m → Option (Fin n × ℕ))
    (i : Fin n) : Finset (Fin m) :=
  if Happy x i then selConfig x i else Finset.univ.filter (fun j => ∃ s, M j = some (i, s))

/-! ## Explicit inputs -/

/-- The record of configuration `(i, S)` in the input of Lemma 3.1: `i, y_{i,S}, 1_S`, the
coefficients `a^{i,S}_j` (`0` for `j ∉ S`) and the flag `1_{S ∈ L_i}`. -/
def Setting.record {n m : ℕ} (st : Setting n m) (p : Fin n × Finset (Fin m)) : List ℚ :=
  [((p.1 : ℕ) : ℚ), st.y p.1 p.2] ++ encSet p.2 ++
    List.ofFn (fun j : Fin m => if j ∈ p.2 then st.a p.1 p.2 j else 0) ++
    [if p.2 ∈ st.L p.1 then 1 else 0]

/-- `input` encodes the setting: `n, m, τ, K` followed by the records of the `K` configurations of
positive mass, each once, in any order. -/
def Setting.Encodes {n m : ℕ} (st : Setting n m) (input : List ℚ) : Prop :=
  ∃ recs : List (Fin n × Finset (Fin m)), recs.Nodup ∧
    (∀ p, p ∈ recs ↔ 0 < st.y p.1 p.2) ∧
    input = [(n : ℚ), (m : ℚ), st.τ, (recs.length : ℚ)] ++ recs.flatMap st.record

/-- `input` encodes the configuration solution `y` with objective value `T` and the clauses `w`
(Theorem 3.5): `n, m, T, K` followed by the records `i, y_{i,S}, 1_S, (w^{i,S}_j)_j` (`0` for
`j ∉ S`) of the `K` configurations of positive mass, each once, in any order. -/
def EncodesClauses {n m : ℕ} (y : Fin n → Finset (Fin m) → ℚ)
    (w : Fin n → Finset (Fin m) → Fin m → ℚ) (T : ℚ) (input : List ℚ) : Prop :=
  ∃ recs : List (Fin n × Finset (Fin m)), recs.Nodup ∧
    (∀ p, p ∈ recs ↔ 0 < y p.1 p.2) ∧
    input = [(n : ℚ), (m : ℚ), T, (recs.length : ℚ)] ++
      recs.flatMap (fun p => [((p.1 : ℕ) : ℚ), y p.1 p.2] ++ encSet p.2 ++
        List.ofFn (fun j : Fin m => if j ∈ p.2 then w p.1 p.2 j else 0))

/-- `input` encodes the explicit distributions `y` over configurations (Lemma 3.10): `n, m, K`
followed by the triples `i, y_{i,S}, 1_S` of the `K` configurations of positive mass, each once,
in any order. -/
def EncodesDistributions {n m : ℕ} (y : Fin n → Finset (Fin m) → ℚ) (input : List ℚ) : Prop :=
  ∃ recs : List (Fin n × Finset (Fin m)), recs.Nodup ∧
    (∀ p, p ∈ recs ↔ 0 < y p.1 p.2) ∧
    input = [(n : ℚ), (m : ℚ), (recs.length : ℚ)] ++
      recs.flatMap (fun p => [((p.1 : ℕ) : ℚ), y p.1 p.2] ++ encSet p.2)

end SantaClausNSW.MaxMin


