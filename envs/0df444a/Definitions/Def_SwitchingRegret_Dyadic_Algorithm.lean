-- Prove2me | Definitions.Def_SwitchingRegret_Dyadic_Algorithm
-- name    : SwitchingRegret_Dyadic_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:03.131338+00:00
-- url     : https://prove2.me/theorems/c13d77a4-420f-48dd-8fb0-50a172b9e4b2
-- title:
--   Algorithm 1 with bandit feedback, rollout and epoch accounting
-- statement:
--   The state stores the epoch, accumulated credit, main distribution, active intervals, their weights and their rates. The choice step first launches every canonical interval starting at the current round, then chooses the routing bit, sampling distribution and arm. The update step receives that choice and just the observed real loss.
--
--   On main rounds, EXP3.S updates the main weights and mixes in $1/(KT)$ on every arm. On challenge rounds, the main distribution is frozen and each active interval uses its own implicit-exploration estimate. The credit increment is zero on main rounds and $\ell_{t,i_t}(q_{t,i_t}/p_{t,i_t}-1)$ on challenge rounds. A threshold crossing restarts at twice the learning rate only when $t<T$; otherwise intervals ending at $t$ are removed after their last update.
--
--   The actual run recursively supplies $\ell_{t,i_t}$ to this update. The fresh continuation uses the same recurrence with restarts suppressed. Epoch membership, starts, ends, lengths, credits and distributional regret are extracted from that concrete trajectory. In particular,
--   $$\operatorname{Reg}_I^a(u)=\sum_{t\in I}(\langle a_t,\ell_t\rangle-\ell_{t,u_t}).$$
--   These definitions expose the bandit information restriction and supply the random quantities used by the theorem statements. No bound, coupling or independence assertion is assumed as a field.
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Algorithm 1, Eqs (3), (5), (12), PDF pp. 4, 6–7, 10–11 (printed pp. 3, 5–6, 9–10)

import Definitions.Def_SwitchingRegret_Dyadic_Model

noncomputable section

namespace SwitchingRegret.Dyadic
open Classical MeasureTheory

/-- Algorithm 1, line 2. Fields contain data only, no statistical or regret claims. -/
structure State (K T : ℕ) where
  epoch : ℕ
  credit : ℝ
  q : Vec K
  active : Finset (Dyad T)
  x : Dyad T → Vec K
  rates : Dyad T → ℝ

def initial (K T j : ℕ) : State K T :=
  ⟨j, 0, fun _ => 1 / (K : ℝ), ∅, fun _ => initialX K T, fun _ => 0⟩

/-- Lines 4–6 happen before the routing bit is read. -/
def launch {K T : ℕ} (s : State K T) (t : ℕ) (xi : EpochSeed T) : State K T :=
  let new := (dyadics T).filter fun J => first J = t
  { s with active := s.active ∪ new
           x := fun J => if J ∈ new then initialX K T else s.x J
           rates := fun J => if J ∈ new then intervalRate K T s.epoch xi J else s.rates J }

structure Choice (K T : ℕ) where
  state : State K T
  main : Bool
  p : Vec K
  arm : Fin K

/-- Lines 4–10. Its type accepts neither the loss table nor a comparator nor S. -/
def choose {K T : ℕ} [NeZero K] (s : State K T) (t : ℕ) (xi : EpochSeed T) : Choice K T :=
  let s' := launch s t xi
  let b := mainRound xi t
  let p := if b then s'.q else fun i =>
    (1 - alpha T * ∑ J ∈ s'.active, mass (s'.x J)) * s'.q i +
      alpha T * ∑ J ∈ s'.active, s'.x J i
  ⟨s', b, p, sample p (if b then mainSeed xi t else chalSeed xi t)⟩

def mainEstimate {K T : ℕ} (c : Choice K T) (observed : ℝ) : Vec K :=
  fun i => if i = c.arm then 2 * observed / c.state.q c.arm else 0

def estimate {K T : ℕ} (c : Choice K T) (observed : ℝ) (J : Dyad T) : Vec K :=
  fun i => if i = c.arm then observed / (c.p c.arm + c.state.rates J) else 0

def centered {K T : ℕ} (c : Choice K T) (observed : ℝ) (J : Dyad T) : Vec K :=
  fun i => estimate c observed J i - dot c.state.q (estimate c observed J)

def creditSample {K T : ℕ} (c : Choice K T) (observed : ℝ) : ℝ :=
  if c.main then 0 else observed * (c.state.q c.arm / c.p c.arm - 1)

/-- Lines 11–25. The only loss input is the one observed real number.
The Boolean is true in the actual run, false in the fixed-rate continuation. -/
def update {K T : ℕ} (restart : Bool) (t : ℕ) (c : Choice K T) (observed : ℝ) : State K T :=
  let s := c.state
  let newCredit := s.credit + creditSample c observed
  let q := if c.main then mainUpdate T s.q (mainEstimate c observed) (eta K T s.epoch)
    else s.q
  let x := if c.main then s.x else fun J =>
    if J ∈ s.active then intervalUpdate (s.x J) s.q (estimate c observed J) (s.rates J)
    else s.x J
  if restart ∧ 4 * (K : ℝ) * T * eta K T s.epoch ≤ newCredit ∧ t < T then
    initial K T (s.epoch + 1)
  else { s with credit := newCredit, q := q, x := x,
                active := s.active.filter fun J => last J ≠ t }

/-- State after the first n global rounds; rounds before tau do nothing.
The rollout supplies precisely ell(t,i_t), after `choose` has selected i_t. -/
def stateAfter {K T : ℕ} [NeZero K] (ell : LossTable K) (seeds : ℕ → EpochSeed T)
    (restart : Bool) (tau j : ℕ) : ℕ → State K T
  | 0 => initial K T j
  | n + 1 =>
    let s := stateAfter ell seeds restart tau j n
    if n + 1 < tau then s else
      let c := choose s (n + 1) (seeds s.epoch)
      update restart (n + 1) c (ell (n + 1) c.arm)

abbrev Trajectory (K T : ℕ) := ℕ → Choice K T

def trajectory {K T : ℕ} [NeZero K] (ell : LossTable K) (seeds : ℕ → EpochSeed T)
    (restart : Bool) (tau j : ℕ) : Trajectory K T :=
  fun t =>
    let s := stateAfter ell seeds restart tau j (t - 1)
    choose s t (seeds s.epoch)

def run {K T : ℕ} [NeZero K] (ell : LossTable K) (omega : RunSeed T) : Trajectory K T :=
  trajectory ell (fun j => omega (timeKey T j)) true 1 1

/-- Appendix A.1: fresh deterministic (j,tau) continuation. No coupling is assumed. -/
def cont {K T : ℕ} [NeZero K] (ell : LossTable K) (j tau : ℕ)
    (xi : EpochSeed T) : Trajectory K T := trajectory ell (fun _ => xi) false tau j

/-- Every round carries its epoch label before that round's possible restart. -/
def epochRounds {K T : ℕ} (R : Trajectory K T) (j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 T).filter fun t => (R t).state.epoch = j

def numEpochs {K T : ℕ} (R : Trajectory K T) : ℕ := (R T).state.epoch

def epochStart {K T : ℕ} (R : Trajectory K T) (j : ℕ) : ℕ :=
  if h : (epochRounds R j).Nonempty then (epochRounds R j).min' h else T + 1

def epochEnd {K T : ℕ} (R : Trajectory K T) (j : ℕ) : ℕ :=
  if h : (epochRounds R j).Nonempty then (epochRounds R j).max' h else 0

def epochCredit {K T : ℕ} (R : Trajectory K T) (ell : LossTable K) (j : ℕ) : ℝ :=
  ∑ t ∈ epochRounds R j, creditSample (R t) (ell t (R t).arm)

def regretOn {K T : ℕ} (R : Trajectory K T) (ell : LossTable K) (u : ℕ → Fin K)
    (I : Finset ℕ) (main : Bool) : ℝ :=
  ∑ t ∈ I, (dot (if main then (R t).state.q else (R t).p) (ell t) - ell t (u t))

/-- The two random variables on the right of (12) and in Lemma 4.8. -/
def decomposition {K T : ℕ} (R : Trajectory K T) (ell : LossTable K) (u : ℕ → Fin K) : ℝ :=
  (∑ j ∈ Finset.Icc 1 (numEpochs R), regretOn R ell u (epochRounds R j) true) -
    ∑ j ∈ Finset.Icc 1 (numEpochs R), epochCredit R ell j

def stabilityMinusCredit {K T : ℕ} (R : Trajectory K T) (ell : LossTable K) : ℝ :=
  (∑ j ∈ Finset.Icc 1 (numEpochs R), eta K T j * K * (epochRounds R j).card) -
    ∑ j ∈ Finset.Icc 1 (numEpochs R), epochCredit R ell j

end SwitchingRegret.Dyadic


