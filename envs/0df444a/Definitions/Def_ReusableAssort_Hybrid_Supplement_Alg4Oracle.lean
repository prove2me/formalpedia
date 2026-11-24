-- Prove2me | Definitions.Def_ReusableAssort_Hybrid_Supplement_Alg4Oracle
-- name    : ReusableAssort_Hybrid_Supplement_Alg4Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:19:07.834651+00:00
-- url     : https://prove2.me/theorems/a05c48e8-0bdc-4c95-9358-6e4895ff860f
-- title:
--   Assumption 3 (p. 9) and the online world of §EC.7 with oracle access — rational data, encoding length, observable law of Algorithm 4
-- statement:
--   These are the objects in which the running-time clause of Theorem EC.2 is stated. The instance has type space $\mathcal Z = \{0, \dots, m-1\}$ (the disjoint union of the paper's $\mathcal Z_t$, so $m = \sum_t |\mathcal Z_t|$) and products $0, \dots, n-1$.
--
--   1. **Rational data and encoding length.** A computation reads numbers, so the data are rational: $\phi^z(S,i)$ for $S \in \mathcal S$, $r^z_i$, $g^z_i(d)$ for $d \le T$ and $F_t(z)$ for $1 \le t \le T$ are given by rationals equal to the instance's values. The instance has **encoding length at most $L$** when each of these rationals, and each inventory $c_i$, has binary length at most $L$.
--   2. **Offline oracle (Assumption 3).** An oracle is a map $(z, \hat R) \mapsto \hat S$ that, for every type $z$ and every nonnegative rational vector $\hat R \in \mathbb Q^n_{+}$, returns
--   $$\hat S \in \mathcal S, \qquad \sum_{i} \hat R_i\,\phi^z(\hat S, i) = \max_{S \in \mathcal S} \sum_i \hat R_i\,\phi^z(S, i).$$
--   3. **The world.** A machine (see the OracleRAM definition) interacts with this world by calls: it can read $n$, $T$, $m$, $L$; the inventories $c_i$; membership in $\mathcal S$; $\phi^z(S,i)$ for $S\in\mathcal S$; $r^z_i$; $g^z_i(d)$; $F_t(z)$; and the offline oracle. Assortments are passed as bit masks $\sum_{i\in S}2^i$. The online part has two calls. An **arrival** reveals the type $z_t \sim F_t$ of the $t$-th consumer, with $t$ one more than the number of earlier arrivals. An **offer** of a set $S$ to the pending consumer of type $z$ returns $i$ (encoded as $i+1$) with probability $\phi^z(S,i)$ for $i \in S$, and "no rental" (encoded $0$) with the remaining probability $1 - \sum_{i\in S}\phi^z(S,i)$. Rental durations are not revealed: in the setting of §EC.7 a rented unit never returns.
--   4. **Observable law.** The record of a run is the list, over its offers, of (type of the consumer, offered set, choice). The law of Algorithm 4 on the same record is the image of Algorithm 4's path law (the Alg4 definition, from full inventory at time $1$) under $(z_t, \hat S_t, \bar S_t, \tilde S_t, \text{choice}_t, d_t)_{t=1}^T \mapsto (z_t, \tilde S_t, \text{choice}_t)_{t=1}^T$.
--
--   **Formalization Note** The oracle is a function of the type and of $\hat R$; its answers on vectors with a negative entry are unconstrained, as Assumption 3 only covers $\hat R \in \mathbb R^n_{+}$. Choice probabilities are served only on $\mathcal S$, where the model constrains them; the answer is $0$ for an infeasible set. Malformed calls are answered $0$.
--   `ValidOnlineTrace` requires exactly $T$ arrival/offer pairs, each arrival followed by its offer before the next arrival, feasible offered sets, and a remaining unit of every offered product. Data and offline-oracle calls may occur between these pairs. An infeasible offer query returns the point mass at no rental, so unconstrained choice values outside $\mathcal S$ never become signed world weights. The implementation theorem requires this protocol on every positive-weight halted branch.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. 9 (PDF 9), Assumption 3; p. ec7 (PDF 33), Theorem EC.2; p. ec8 (PDF 34), Algorithm 4; §EC.7, p. ec16 (PDF 42)

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Supplement_Alg4
import Definitions.Def_ReusableAssort_Hybrid_Supplement_OracleRAM

namespace ReusableAssort.Hybrid.Supplement

/-- The natural number denoted by a rational, if it is a nonnegative integer. -/
def decodeNat (q : ℚ) : Option ℕ :=
  if q.den = 1 ∧ 0 ≤ q.num then some q.num.toNat else none

/-- An element of `Fin m` given by its index. -/
def decodeFin (m : ℕ) (q : ℚ) : Option (Fin m) :=
  match decodeNat q with
  | some k => if h : k < m then some ⟨k, h⟩ else none
  | none => none

/-- The bit-mask code `∑_{i ∈ S} 2^i` of a set of products. -/
def maskQ {n : ℕ} (S : Finset (Fin n)) : ℚ := ∑ i ∈ S, (2 : ℚ) ^ (i : ℕ)

/-- The set of products whose bit is set in the code `q < 2^n`. -/
def decodeSet (n : ℕ) (q : ℚ) : Option (Finset (Fin n)) :=
  match decodeNat q with
  | some k => if k < 2 ^ n then some (Finset.univ.filter fun i : Fin n => k.testBit i) else none
  | none => none

/-- The code of a consumer's choice: `0` for no rental, `i + 1` for product `i`. -/
def choiceQ {n : ℕ} : Option (Fin n) → ℚ
  | none => 0
  | some i => (i : ℕ) + 1

/-- Rational data of an instance with type space `Fin m`: the numbers a computation reads. -/
structure RatData (n T m : ℕ) where
  phi : Fin m → Finset (Fin n) → Fin n → ℚ
  r : Fin m → Fin n → ℚ
  g : Fin m → Fin n → ℕ → ℚ
  F : ℕ → Fin m → ℚ

/-- `D` gives the instance's data exactly: choice probabilities on feasible assortments, fees,
duration probabilities and type probabilities at times `1, …, T`. -/
def RatData.Represents {n T m : ℕ} (D : RatData n T m) (I : Instance n T (Fin m)) : Prop :=
  (∀ z, ∀ S ∈ I.feas, ∀ i, I.phi z S i = D.phi z S i) ∧
  (∀ z i, I.r z i = D.r z i) ∧
  (∀ z i, ∀ d ≤ T, I.g z i d = D.g z i d) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ z, I.F t z = D.F t z)

/-- Every number of the instance has binary encoding length at most `L`. -/
def RatData.SizeLE {n T m : ℕ} (D : RatData n T m) (I : Instance n T (Fin m)) (L : ℕ) : Prop :=
  (∀ z, ∀ S ∈ I.feas, ∀ i, qsize (D.phi z S i) ≤ L) ∧
  (∀ z i, qsize (D.r z i) ≤ L) ∧
  (∀ z i, ∀ d ≤ T, qsize (D.g z i d) ≤ L) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ z, qsize (D.F t z) ≤ L) ∧
  (∀ i, Nat.size (I.c i) ≤ L)

/-- Assumption 3 (p. 9): for every type `z` and every nonnegative weight vector `R̂`, the offline
oracle returns a feasible assortment maximizing `∑_i R̂_i ϕ^z(S, i)` over `S ∈ 𝒮`. -/
def IsOfflineOracle {n T m : ℕ} (I : Instance n T (Fin m))
    (orc : Fin m → (Fin n → ℚ) → Finset (Fin n)) : Prop :=
  ∀ z (R : Fin n → ℚ), (∀ i, 0 ≤ R i) →
    orc z R ∈ I.feas ∧
    ∀ S ∈ I.feas, ∑ i, (R i : ℝ) * I.phi z S i ≤ ∑ i, (R i : ℝ) * I.phi z (orc z R) i

/-- The type revealed by the last arrival, if no offer has been made to it yet. -/
def pendingType (h : List Event) : Option ℚ :=
  match h.reverse.find? (fun e => e.1 = 9 ∨ e.1 = 10) with
  | some e => if e.1 = 9 then some e.2.2 else none
  | none => none

/-- The world of the online problem of §EC.7 with oracle access (Assumption 3). Calls:
* code `1`, `[j]`: the parameter `n`, `T`, `m`, `L` for `j = 0, 1, 2, 3`;
* code `2`, `[i]`: the inventory `c_i`;
* code `3`, `[S]`: `1` if `S ∈ 𝒮`, else `0`;
* code `4`, `[z, S, i]`: `ϕ^z(S, i)` for `S ∈ 𝒮` (`0` otherwise);
* code `5`, `[z, i]`: `r^z_i`; code `6`, `[z, i, d]`: `g^z_i(d)` for `d ≤ T` (`0` otherwise);
* code `7`, `[t, z]`: `F_t(z)` for `1 ≤ t ≤ T` (`0` otherwise);
* code `8`, `[z, R̂_0, …, R̂_{n−1}]`: the offline oracle's answer, as a bit mask;
* code `9`, `[]`: the next consumer arrives; its type `z_t ∼ F_t`, `t` = one more than the
  number of earlier arrivals, is revealed (`−1` once `t > T`);
* code `10`, `[S]`: offer `S` to the pending consumer of type `z`; the answer is `i + 1` with
  probability `ϕ^z(S, i)` for `i ∈ S`, and `0` (no rental) with probability `1 − ∑_{i∈S} ϕ^z(S, i)`.
Malformed calls are answered `0`. -/
noncomputable def alg4World {n T m : ℕ} (I : Instance n T (Fin m)) (D : RatData n T m) (L : ℕ)
    (orc : Fin m → (Fin n → ℚ) → Finset (Fin n)) : World := fun h code args =>
  if code = 1 then
    match args with
    | [j] => Dist.pure (if j = 0 then (n : ℚ) else if j = 1 then (T : ℚ)
                        else if j = 2 then (m : ℚ) else if j = 3 then (L : ℚ) else 0)
    | _ => Dist.pure 0
  else if code = 2 then
    match args with
    | [i] => Dist.pure (match decodeFin n i with | some i => (I.c i : ℚ) | none => 0)
    | _ => Dist.pure 0
  else if code = 3 then
    match args with
    | [S] => Dist.pure (match decodeSet n S with
                        | some S => if S ∈ I.feas then 1 else 0
                        | none => 0)
    | _ => Dist.pure 0
  else if code = 4 then
    match args with
    | [z, S, i] => Dist.pure (match decodeFin m z, decodeSet n S, decodeFin n i with
                              | some z, some S, some i => if S ∈ I.feas then D.phi z S i else 0
                              | _, _, _ => 0)
    | _ => Dist.pure 0
  else if code = 5 then
    match args with
    | [z, i] => Dist.pure (match decodeFin m z, decodeFin n i with
                           | some z, some i => D.r z i
                           | _, _ => 0)
    | _ => Dist.pure 0
  else if code = 6 then
    match args with
    | [z, i, d] => Dist.pure (match decodeFin m z, decodeFin n i, decodeNat d with
                              | some z, some i, some d => if d ≤ T then D.g z i d else 0
                              | _, _, _ => 0)
    | _ => Dist.pure 0
  else if code = 7 then
    match args with
    | [t, z] => Dist.pure (match decodeNat t, decodeFin m z with
                           | some t, some z => if 1 ≤ t ∧ t ≤ T then D.F t z else 0
                           | _, _ => 0)
    | _ => Dist.pure 0
  else if code = 8 then
    match args with
    | z :: R =>
        match decodeFin m z with
        | some z =>
            if hR : R.length = n then
              Dist.pure (maskQ (orc z (fun i => R.get ⟨i.1, hR ▸ i.2⟩)))
            else Dist.pure 0
        | none => Dist.pure 0
    | [] => Dist.pure 0
  else if code = 9 then
    let t := (h.filter (fun e => e.1 = 9)).length + 1
    if t ≤ T then (List.finRange m).map fun z => (I.F t z, ((z : ℕ) : ℚ))
    else Dist.pure (-1)
  else if code = 10 then
    match args with
    | [S] =>
        match decodeSet n S, (pendingType h).bind (decodeFin m) with
        | some S, some z =>
            if S ∈ I.feas then
              ((List.finRange n).filter (· ∈ S)).map (fun i => (I.phi z S i, ((i : ℕ) : ℚ) + 1))
                ++ [(1 - ∑ i ∈ S, I.phi z S i, 0)]
            else Dist.pure 0
        | _, _ => Dist.pure 0
    | _ => Dist.pure 0
  else Dist.pure 0

/-- The observable record of a run: for each offer, the type of the consumer it was made to,
the offered set's code and the consumer's choice code. -/
def obsOf : List Event → ℚ → List (ℚ × ℚ × ℚ)
  | [], _ => []
  | e :: es, z =>
      if e.1 = 9 then obsOf es e.2.2
      else if e.1 = 10 then (z, e.2.1.headD 0, e.2.2) :: obsOf es z
      else obsOf es z

/-- The observable record of a run's history (types, offered assortments, choices). -/
def obs (h : List Event) : List (ℚ × ℚ × ℚ) := obsOf h 0

/-- A complete online interaction in the non-reusable setting: exactly one arrival followed
by one feasible offer per period, before the next arrival. All offered products have inventory
remaining. Data and offline-oracle queries may occur between these interactions. -/
def ValidOnlineTrace {n T m : ℕ} (I : Instance n T (Fin m)) (h : List Event) : Prop :=
  ∃ v : Fin T → Fin m × Finset (Fin n) × Option (Fin n),
    h.filter (fun e => e.1 = 9 ∨ e.1 = 10) =
      (List.ofFn fun k : Fin T =>
        [(9, [], (((v k).1 : ℕ) : ℚ)), (10, [maskQ (v k).2.1], choiceQ (v k).2.2)]).flatten ∧
    ∀ k, (v k).2.1 ∈ I.feas ∧
      (∀ i ∈ (v k).2.1,
        (Finset.univ.filter (fun j : Fin T => j < k ∧ (v j).2.2 = some i)).card < I.c i) ∧
      (∀ i, (v k).2.2 = some i → i ∈ (v k).2.1)

/-- The same record along a sample path of Algorithm 4's process: at each time `t = 1, …, T`, the
type `z_t`, the offered assortment `S̃_t` and the consumer's choice. -/
def obsPath {n T m : ℕ} (v : Fin (T + 1 - 1) → Step n T (Fin m)) : List (ℚ × ℚ × ℚ) :=
  List.ofFn fun k => ((((v k).1 : ℕ) : ℚ), maskQ (v k).2.2.2.1, choiceQ (v k).2.2.2.2.1)

/-- The probability that Algorithm 4, run with the LP solution `y` from full inventory, produces
the observable record `o`. -/
noncomputable def alg4ObsProb {n T m : ℕ} (I : Instance n T (Fin m))
    (y : ℕ → Fin m → Finset (Fin n) → ℝ) (o : List (ℚ × ℚ × ℚ)) : ℝ :=
  ∑ v, if obsPath v = o then pathProbA I y 1 (alg4Keep I y 1 (fun _ _ => 0)) v else 0

/-- The probability that a run's halted record is `o`. -/
noncomputable def runObsProb (R : Dist (Option Config)) (o : List (ℚ × ℚ × ℚ)) : ℝ :=
  R.prob fun r => match r with
    | some c => decide (obs c.hist = o)
    | none => false

end ReusableAssort.Hybrid.Supplement


