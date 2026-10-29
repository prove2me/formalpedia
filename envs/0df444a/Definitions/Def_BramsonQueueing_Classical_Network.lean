-- Prove2me | Definitions.Def_BramsonQueueing_Classical_Network
-- name    : BramsonQueueing_Classical_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:49.027984+00:00
-- url     : https://prove2.me/theorems/ba3fed8a-5dec-472d-90b8-110ed5eb457a
-- title:
--   Open random-routing networks assembled from isolated nodes
-- statement:
--   An open routing system consists of finite external rates $\alpha_k$ and a substochastic matrix $P_{k\ell}$. Its path sums satisfy $\sum_{n\ge0}(P^n)_{k\ell}<\infty$. Define the total arrival rates by
--   $$\lambda_\ell=\sum_k\alpha_k\sum_{n\ge0}(P^n)_{k\ell}.$$
--   The network state is the product of its countable station state spaces. An external arrival inserts a job at its station; a completed job exits with probability $1-\sum_\ell P_{k\ell}$ or is removed and reinserted at class $\ell$ with probability $P_{k\ell}$. Internal node changes are lifted without changing other station coordinates. The rates sum over all permitted intermediate states, including same-class and same-station returns. These are the mechanisms of (2.48)-(2.52), in the insertion-probability forms (2.48′) and (2.50′).
--
--   Validity includes open routing, the partition of classes among stations, the isolated-node structural conditions, and the source's regularity and communication assumptions. It contains no product law or quasi-reversibility conclusion.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; Sections 2.1 and 2.5, printed pp. 18, 43-45 / PDF pp. 26, 51-53; Eqs. (2.48)-(2.52)

import Definitions.Def_BramsonQueueing_Classical_MarkedQueue

namespace BramsonQueueing.Classical
noncomputable section
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Open Markov routing, with substochastic routing matrix and external intensities.
The transposed fundamental matrix is represented by its nonnegative path series. -/
structure Routing (C : Type*) where
  external : C → ℝ≥0
  probability : C → C → ℝ≥0

def Routing.paths {C : Type*} [Fintype C] (R : Routing C) : ℕ → C → C → ℝ≥0∞
  | 0, k, l => if k = l then 1 else 0
  | n + 1, k, l => ∑ h, R.paths n k h * (R.probability h l : ℝ≥0∞)

def Routing.Valid {C : Type*} [Fintype C] (R : Routing C) : Prop :=
  (∀ k, ∑ l, R.probability k l ≤ 1) ∧
  ∀ k l, (∑' n, R.paths n k l) ≠ ⊤

def Routing.traffic {C : Type*} [Fintype C] (R : Routing C) (l : C) : ℝ≥0∞ :=
  ∑ k, (R.external k : ℝ≥0∞) * ∑' n, R.paths n k l

def Routing.escape {C : Type*} [Fintype C] (R : Routing C) (k : C) : ℝ≥0∞ :=
  ((1 - ∑ l, R.probability k l : ℝ≥0) : ℝ≥0∞)

/-- Lift a station transition while fixing every other coordinate. -/
def liftRate {J : Type*} {S : J → Type*} (j : J)
    (r : S j → S j → ℝ≥0∞) (x y : ∀ j, S j) : ℝ≥0∞ :=
  if ∀ h, h ≠ j → x h = y h then r (x j) (y j) else 0

/-- A general network is assembled from isolated-node insertion and removal
mechanisms. Routed transitions include a sum over intermediate states, including
returns to the same station or the same class. -/
def network {J C : Type*} [Fintype J] [Fintype C] {S : J → Type*}
    (station : C → J) (N : ∀ j, Node (S j) C) (R : Routing C) :
    MarkedQueue (∀ j, S j) C where
  arrival k x y := (R.external k : ℝ≥0∞) * liftRate (station k) ((N (station k)).insert k) x y
  departure k x y := liftRate (station k) ((N (station k)).remove k) x y * R.escape k
  internal x y :=
    (∑ j, liftRate j (N j).internal x y) +
    ∑ k, ∑ l, ∑' z : ∀ j, S j,
      liftRate (station k) ((N (station k)).remove k) x z *
        (R.probability k l : ℝ≥0∞) * liftRate (station l) ((N (station l)).insert l) z y

/-- Structural and standing assumptions of Sections 2.2 and 2.5; no invariant
measure, reversed-rate identity or product formula is assumed. -/
def NetworkValid {J C : Type*} [Fintype J] [Fintype C] {S : J → Type*}
    (station : C → J) (N : ∀ j, Node (S j) C) (R : Routing C) : Prop :=
  R.Valid ∧ (∀ j, (N j).Valid) ∧
  (∀ j k, k ∈ (N j).classes ↔ station k = j) ∧
  Regular (network station N R).rate ∧ Communicates (network station N R).rate ∧
  ∀ j, Regular ((N j).queue R.traffic).rate ∧ Communicates ((N j).queue R.traffic).rate

end
end BramsonQueueing.Classical


