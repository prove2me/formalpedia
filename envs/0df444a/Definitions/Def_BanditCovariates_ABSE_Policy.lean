-- Prove2me | Definitions.Def_BanditCovariates_ABSE_Policy
-- name    : BanditCovariates_ABSE_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:08:35.145645+00:00
-- url     : https://prove2.me/theorems/de5f2b16-cf05-4df1-a20b-36e5c9f46fc8
-- title:
--   Policy 3 — adaptively binned successive elimination and regret
-- statement:
--   Adaptively binned successive elimination starts with the whole cube and every arm. In each live cell it pulls each active arm once per round, in index order, then retains arms whose empirical means are within $2U(s,n|B|^d)$ of the largest. After the $\ell_B$-th full round, a cell below depth $k_0$ bursts into its dyadic children if at least two arms remain. Each child inherits the surviving arms.
--
--   The policy receives only $d,\beta,L,K,n$, the current covariate, and rewards observed on earlier chosen pulls. Its expected pseudoregret is
--
--   $$R_n=\sum_{t=1}^n\mathbb E\left[f^*(X_t)-f^{(\widetilde\pi_t)}(X_t)\right].$$
--
--   Under the machine assumptions this equals the paper's expected reward regret. The policy is defined after the nominal horizon for the paper's random cell events.
--
--   **Formalization Note** Time begins at zero in Lean. Elimination and bursting happen after a full round, as in the text and proof where the pseudocode differs. The fallback for a malformed internal state is never reached on a valid run.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, pp. 5–6, 21–22, Policy 1 and Policy 3

import Mathlib
import Definitions.Def_BanditCovariates_ABSE_Cells

noncomputable section

namespace BanditCovariates.ABSE

open MeasureTheory

/-- Successive elimination on the stream of rewards observed in one cell. -/
structure SEState (K : ℕ) where
  active : Finset (Fin K)
  pending : Finset (Fin K)
  rounds : ℕ
  sum : Fin K → ℝ

/-- A fresh SE instance inherits the parent's active arms. -/
def initSE {K : ℕ} (arms : Finset (Fin K)) : SEState K :=
  ⟨arms, arms, 0, fun _ => 0⟩

def nextArm {K : ℕ} (hK : 0 < K) (S : SEState K) : Fin K :=
  let available := if S.pending.Nonempty then S.pending else S.active
  if h : available.Nonempty then available.min' h else ⟨0, hK⟩

/-- One pull, followed by elimination exactly when the current round ends.
The `pending` set makes each active arm appear once per round, in increasing order. -/
def stepSE {K : ℕ} (hK : 0 < K) (T : ℝ) (γ : ℝ)
    (S : SEState K) (reward : ℝ) : SEState K :=
  let available := if S.pending.Nonempty then S.pending else S.active
  let i := nextArm hK S
  let sums : Fin K → ℝ := fun j => S.sum j + if j = i then reward else 0
  let remaining := available.erase i
  if remaining.Nonempty then
    { S with pending := remaining, sum := sums }
  else
    let round := S.rounds + 1
    let avg : Fin K → ℝ := fun j => sums j / (round : ℝ)
    let best := (S.active.toList.map avg).foldl max 0
    let kept := S.active.filter (fun j => avg j ≥ best - γ * U round T)
    ⟨kept, kept, round, sums⟩

abbrev ABSEState (d K : ℕ) := Cell d → Option (SEState K)

def initialState (d K : ℕ) : ABSEState d K :=
  fun B => if B = root d then some (initSE Finset.univ) else none

/-- At a valid path, exactly one active cell contains x. This chooses its
finest active depth; the zero fallback concerns malformed states only. -/
def liveDepth {d K : ℕ} (maxDepth : ℕ) (S : ABSEState d K)
    (x : Covariate d) : ℕ :=
  (Finset.range (maxDepth + 1)).sup
    (fun k => if (S (cellAt d k x)).isSome then k else 0)

def liveCell {d K : ℕ} (maxDepth : ℕ) (S : ABSEState d K)
    (x : Covariate d) : Cell d :=
  cellAt d (liveDepth maxDepth S x) x

/-- Policy 3's arm choice uses the current covariate and past state. -/
def choose {d K : ℕ} (hK : 0 < K) (maxDepth : ℕ)
    (S : ABSEState d K) (x : Covariate d) : Fin K :=
  nextArm hK ((S (liveCell maxDepth S x)).getD (initSE Finset.univ))

/-- One ABSE transition. Only the scalar reward of the chosen arm is supplied.
A cell bursts after its `ell`-th full round if at least two arms remain. -/
def step {d K n : ℕ} (hK : 0 < K) (β L : ℝ)
    (S : ABSEState d K) (x : Covariate d) (reward : ℝ) : ABSEState d K :=
  let maxDepth := k0 d K n β
  let B := liveCell maxDepth S x
  let current := (S B).getD (initSE Finset.univ)
  let updated := stepSE hK ((n : ℝ) * side B ^ d) 2 current reward
  let shouldBurst := current.rounds < updated.rounds ∧
    ell d n β L B ≤ updated.rounds ∧ B.depth < maxDepth ∧
    2 ≤ updated.active.card
  if shouldBurst then
    fun C => if C = B then none
      else if C ∈ burst B then some (initSE updated.active)
      else S C
  else
    fun C => if C = B then some updated else S C

/-- State before pull t. The update reads X_t and then Y_t of the chosen arm. -/
def stateAt {d K n : ℕ} {Ω : Type*} (hK : 0 < K) (β L : ℝ)
    (X : ℕ → Ω → Covariate d) (Y : ℕ → Ω → Fin K → ℝ)
    (t : ℕ) (ω : Ω) : ABSEState d K :=
  Nat.rec (initialState d K)
    (fun s S => step (n := n) hK β L S (X s ω)
      (Y s ω (choose hK (k0 d K n β) S (X s ω)))) t

/-- Policy 3, extended past horizon n so its random stopping events are defined. -/
def abse {d K n : ℕ} {Ω : Type*} (hK : 0 < K) (β L : ℝ)
    (X : ℕ → Ω → Covariate d) (Y : ℕ → Ω → Fin K → ℝ)
    (t : ℕ) (ω : Ω) : Fin K :=
  choose hK (k0 d K n β) (stateAt (n := n) hK β L X Y t ω) (X t ω)

/-- Expected pseudoregret of Policy 3, equal to the paper's reward regret
under the machine's conditional-mean and nonanticipation assumptions. -/
def regret {d K n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Machine d K Ω) (hK : 0 < K) (β L : ℝ) : ℝ :=
  ∑ t ∈ Finset.range n,
    ∫ ω, (fStar M (M.X t ω) -
      M.f (abse (n := n) hK β L M.X M.Y t ω) (M.X t ω)) ∂M.P

end BanditCovariates.ABSE


