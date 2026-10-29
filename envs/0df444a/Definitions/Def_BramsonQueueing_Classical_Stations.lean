-- Prove2me | Definitions.Def_BramsonQueueing_Classical_Stations
-- name    : BramsonQueueing_Classical_Stations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:20:59.824163+00:00
-- url     : https://prove2.me/theorems/cdd30e7f-d949-4f90-be15-3c85098022bb
-- title:
--   Homogeneous Kelly and symmetric Erlang-mixture stations
-- statement:
--   Each station has an unbounded ordered queue, total service rate $\phi(n)>0$ for $n>0$, and nonnegative positional insertion and service proportions $\beta(i,n)$ and $\delta(i,n)$, each summing to one. A Kelly station uses a common positive exponential mean $m^s$. A symmetric station has $\delta=\beta$, and class $k$ selects $s\ge1$ stages with probability $p_k(s)$, each of positive finite mean $m_k(s)$ on the mixture support. Its finite class mean is
--   $$m_k=\sum_{s\ge1}s p_k(s)m_k(s).$$
--   Jobs carry $(k,s,v)$ with $1\le v\le s$ and positive mixture weight. Kelly jobs use exactly $(k,1,1)$. Arrivals insert $(k,s,s)$; service either decrements $v$ or removes the job when $v=1$. The transition rates are explicitly constructed from these operations.
--
--   For input rates $a_k$, set $\rho=\sum_km_ka_k$, $B=\sum_{n\ge0}\rho^n/\prod_{i=1}^n\phi(i)$, and
--   $$\pi(x)=B^{-1}\prod_{i=1}^{n}\frac{p_{x(i)}(s(i))m_{x(i)}(s(i))a_{x(i)}}{\phi(i)}.$$
--   At a Kelly station the extra mixture factor is one and the mean is $m^s$. The formulas are candidate masses, not assumed invariant measures. Single-node admissibility and mixed-network validity only impose primitive conditions and the standing countable-process hypotheses.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; Sections 2.3-2.5, printed pp. 27-36, 46-47 / PDF pp. 35-44, 54-55; Eqs. (2.19)-(2.21), (2.30)-(2.35), (2.55)

import Definitions.Def_BramsonQueueing_Classical_Network

namespace BramsonQueueing.Classical
noncomputable section
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The primitive data for either eligible station type. Kelly stations have
common exponential mean; symmetric stations have countably many Erlang components. -/
structure Station (C : Type*) where
  classes : Finset C
  kelly : Bool
  phi : ℕ → ℝ≥0
  beta : ℕ → ℕ → ℝ≥0
  delta : ℕ → ℕ → ℝ≥0
  commonMean : ℝ≥0
  mixture : C → ℕ → ℝ≥0
  stageMean : C → ℕ → ℝ≥0

def Station.prob {C : Type*} (D : Station C) (k : C) (s : ℕ) : ℝ≥0∞ :=
  if D.kelly then (if s = 1 then 1 else 0) else (D.mixture k s : ℝ≥0∞)

def Station.meanStage {C : Type*} (D : Station C) (k : C) (s : ℕ) : ℝ≥0∞ :=
  if D.kelly then (D.commonMean : ℝ≥0∞) else (D.stageMean k s : ℝ≥0∞)

def Station.mean {C : Type*} (D : Station C) (k : C) : ℝ≥0∞ :=
  ∑' s : ℕ, (s : ℝ≥0∞) * D.prob k s * D.meanStage k s

def Station.Valid {C : Type*} (D : Station C) : Prop :=
  D.phi 0 = 0 ∧ (∀ n, 0 < n → 0 < D.phi n) ∧
  (∀ n, 0 < n → ∑ i ∈ Finset.range n, D.beta (i+1) n = 1) ∧
  (∀ n, 0 < n → ∑ i ∈ Finset.range n, D.delta (i+1) n = 1) ∧
  (D.kelly = true → 0 < D.commonMean) ∧
  (D.kelly = false → D.delta = D.beta) ∧
  (∀ k ∈ D.classes, D.prob k 0 = 0 ∧ (∑' s, D.prob k s) = 1 ∧
    (∀ s, 0 < D.prob k s → 0 < D.meanStage k s) ∧ D.mean k ≠ ⊤)

/-- (class, total stages, remaining stages); in the Kelly case s=v=1.
Only positive-mixture states occur; queue lengths and stage counts are unbounded. -/
def Station.jobValid {C : Type*} (D : Station C) (a : C × ℕ × ℕ) : Prop :=
  a.1 ∈ D.classes ∧ 0 < D.prob a.1 a.2.1 ∧ 1 ≤ a.2.2 ∧ a.2.2 ≤ a.2.1

def Station.State {C : Type*} (D : Station C) :=
  {x : List (C × ℕ × ℕ) // ∀ a ∈ x, D.jobValid a}

/-- Insertion before zero-based position i. -/
def insertAt {A : Type*} (x : List A) (i : ℕ) (a : A) : List A :=
  x.take i ++ [a] ++ x.drop i

def Station.node {C : Type*} [Fintype C] (D : Station C) : Node D.State C where
  classes := D.classes
  count x k := (x.val.filter (fun a => a.1 = k)).length
  insert k x y := ∑' s : ℕ, D.prob k s *
    ∑ i ∈ Finset.range (x.val.length + 1),
      if y.val = insertAt x.val i (k, s, s)
      then (D.beta (i+1) (x.val.length+1) : ℝ≥0∞) else 0
  remove k x y := ∑ i : Fin x.val.length,
    let a := x.val.get i
    if a.1 = k ∧ a.2.2 = 1 ∧ y.val = x.val.eraseIdx i then
      (D.delta (i.val+1) x.val.length : ℝ≥0∞) * (D.phi x.val.length : ℝ≥0∞) /
        D.meanStage a.1 a.2.1 else 0
  internal x y := ∑ i : Fin x.val.length,
    let a := x.val.get i
    if 1 < a.2.2 ∧ y.val = x.val.set i (a.1, a.2.1, a.2.2-1) then
      (D.delta (i.val+1) x.val.length : ℝ≥0∞) * (D.phi x.val.length : ℝ≥0∞) /
        D.meanStage a.1 a.2.1 else 0

def Station.load {C : Type*} [Fintype C] (D : Station C) (α : C → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ k ∈ D.classes, D.mean k * α k

def Station.normalizer {C : Type*} [Fintype C] (D : Station C)
    (α : C → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n : ℕ, D.load α ^ n /
    ∏ i ∈ Finset.range n, (D.phi (i+1) : ℝ≥0∞)

/-- Equations (2.20)/(2.32), with the empty product equal to one. -/
def Station.mass {C : Type*} [Fintype C] (D : Station C)
    (α : C → ℝ≥0∞) (x : D.State) : ℝ≥0∞ :=
  (D.normalizer α)⁻¹ * ∏ i : Fin x.val.length,
    let a := x.val.get i
    D.prob a.1 a.2.1 * D.meanStage a.1 a.2.1 * α a.1 /
      (D.phi (i.val+1) : ℝ≥0∞)

/-- Single-node standing countable-process assumptions, independent of the
candidate law. Unused outside classes have zero external intensity. -/
def Station.Admissible {C : Type*} [Fintype C] (D : Station C)
    (α : C → ℝ≥0) : Prop :=
  D.Valid ∧ (∀ k, k ∉ D.classes → α k = 0) ∧
  Regular (D.node.queue (fun k => (α k : ℝ≥0∞))).rate ∧
  Communicates (D.node.queue (fun k => (α k : ℝ≥0∞))).rate

/-- Mixed-network assumptions are stated directly from primitive data; node
stationarity and quasi-reversibility are conclusions, never fields of the model. -/
def MixedValid {J C : Type*} [Fintype J] [Fintype C]
    (station : C → J) (D : J → Station C) (R : Routing C) : Prop :=
  R.Valid ∧ (∀ j, (D j).Valid) ∧
  (∀ j k, k ∈ (D j).classes ↔ station k = j) ∧
  Regular (network station (fun j => (D j).node) R).rate ∧
  Communicates (network station (fun j => (D j).node) R).rate

end
end BramsonQueueing.Classical


