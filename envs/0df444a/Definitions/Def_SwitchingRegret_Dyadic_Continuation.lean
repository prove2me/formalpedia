-- Prove2me | Definitions.Def_SwitchingRegret_Dyadic_Continuation
-- name    : SwitchingRegret_Dyadic_Continuation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:38.811004+00:00
-- url     : https://prove2.me/theorems/165611b9-ef70-4674-9eb7-a83757370f55
-- title:
--   Continuation endpoint, dyadic advantages and estimation costs
-- statement:
--   For a deterministic epoch index $j$ and start round $\tau$, the continuation starts from the reset state, holds rate $\eta_j$ and uses the epoch's independent seeds through $T$. Its cumulative credit is $C^{\rm cont}_{j,n}$, and $\rho$ is its first crossing of $4KT\eta_j$, or $T$ when no crossing occurs. Stopped regret and length include round $\rho$.
--
--   For an interval $J$ on which the comparator is constant, write $a_J=u_{\min J}$. Its advantage $A_J(n)$ sums $\langle q_t,\ell_t\rangle-\ell_{t,a_J}$ over challenge rounds of $J$ through $n$. The definitions also give
--   $$W_j(n)=\alpha\sum_{J\in D_j(n)} A_J(n)\mathbf1\{\eta_J A_J(n)\ge4L\},\quad \Gamma_j=\sum_{J\in\mathcal J_j}|J|\min\{K\eta_J,\alpha\},$$
--   and $F_j=\max_{\tau\le n\le T}(-C^{\rm cont}_{j,n})_+$. The denominator correction $D_t$ is exactly Eq. (48), including its factor $1/2$; it is zero on main rounds. Disjoint interval families, estimated advantages, arm penalties and the two OMD sums provide the remaining notation of Lemmas A.1–A.4.
--
--   These are computed quantities of the concrete continuation. The finite maximum includes zero explicitly and returns zero on an empty range; the theorems require $1\le\tau\le T$.
-- source:
--   Mengxiao Zhang, Toward Optimal Switching Regret for Multi-Armed Bandits with Oblivious Adversary, 2026 preprint, STOC 2027 submission #99, SHA-256 70dc03d632eeb5878823d984fc755157b34301d8189bbd7a6087570a8f8a7fee, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/99.pdf, Eqs (14), (17), (19), (48), Section 4 and Appendix A.7, PDF pp. 11–15, 25–30 (printed pp. 10–14, 24–29)

import Definitions.Def_SwitchingRegret_Dyadic_Algorithm

noncomputable section

namespace SwitchingRegret.Dyadic
open Classical MeasureTheory

def continuationCredit {K T : ℕ} [NeZero K] (ell : LossTable K) (j tau : ℕ)
    (xi : EpochSeed T) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc tau n, creditSample (cont ell j tau xi t) (ell t (cont ell j tau xi t).arm)

/-- First threshold crossing, including the crossing round; T if none. -/
def rho {K T : ℕ} [NeZero K] (ell : LossTable K) (j tau : ℕ) (xi : EpochSeed T) : ℕ :=
  let crossings := (Finset.Icc tau T).filter fun n =>
    4 * (K : ℝ) * T * eta K T j ≤ continuationCredit ell j tau xi n
  if h : crossings.Nonempty then crossings.min' h else T

def stoppedRegret {K T : ℕ} [NeZero K] (ell : LossTable K) (u : ℕ → Fin K)
    (j tau : ℕ) (xi : EpochSeed T) : ℝ :=
  regretOn (cont ell j tau xi) ell u (Finset.Icc tau (rho ell j tau xi)) true

def stoppedLength {K T : ℕ} [NeZero K] (ell : LossTable K) (j tau : ℕ) (xi : EpochSeed T) : ℝ :=
  ((Finset.Icc tau (rho ell j tau xi)).card : ℝ)

/-- Equation (14), all quantities from the continuation, with a_J = u(first J). -/
def advantage {K T : ℕ} [NeZero K] (ell : LossTable K) (u : ℕ → Fin K)
    (j tau : ℕ) (xi : EpochSeed T) (J : Dyad T) (n : ℕ) : ℝ :=
  ∑ t ∈ (rounds J).filter (fun t => t ≤ n ∧ (cont ell j tau xi t).main = false),
    (dot (cont ell j tau xi t).state.q (ell t) - ell t (u (first J)))

def advantageSum {K T : ℕ} [NeZero K] (ell : LossTable K) (u : ℕ → Fin K)
    (j tau : ℕ) (xi : EpochSeed T) (n : ℕ) : ℝ :=
  ∑ J ∈ cover T tau n u, advantage ell u j tau xi J n

def stoppedAdvantage {K T : ℕ} [NeZero K] (ell : LossTable K) (u : ℕ → Fin K)
    (j tau : ℕ) (xi : EpochSeed T) : ℝ := advantageSum ell u j tau xi (rho ell j tau xi)

def d (K T j : ℕ) : ℝ := 4 * (L T : ℝ) / eta K T j
def delta0 (T : ℕ) : ℝ := (T : ℝ) ^ (-3 : ℤ)

def W {K T : ℕ} [NeZero K] (ell : LossTable K) (u : ℕ → Fin K)
    (j tau : ℕ) (xi : EpochSeed T) (n : ℕ) : ℝ :=
  alpha T * ∑ J ∈ cover T tau n u,
    if 4 * (L T : ℝ) ≤ intervalRate K T j xi J * advantage ell u j tau xi J n
    then advantage ell u j tau xi J n else 0

/-- Equation (19), truncated rates over the entire continuation family. -/
def Gamma (K T j tau : ℕ) (xi : EpochSeed T) : ℝ :=
  ∑ J ∈ future T tau, ((rounds J).card : ℝ) * min ((K : ℝ) * intervalRate K T j xi J) (alpha T)

/-- The finite maximum also includes zero, so it has its intended value on an empty prefix. -/
def negativeCredit {K T : ℕ} [NeZero K] (ell : LossTable K) (j tau : ℕ) (xi : EpochSeed T) : ℝ :=
  let values := insert 0 ((Finset.Icc tau T).image fun n => max 0 (-continuationCredit ell j tau xi n))
  values.max' (Finset.insert_nonempty _ _)

/-- Equation (48), evaluated using only the realized arm and the pre-update state. -/
def denominatorTerm {K T : ℕ} (c : Choice K T) : ℝ :=
  if c.main then 0 else
    alpha T * ∑ J ∈ c.state.active,
      c.state.rates J *
        (c.state.x J c.arm / (c.p c.arm * (c.p c.arm + c.state.rates J)) +
          ((1 - mass (c.state.x J)) * c.state.q c.arm + c.state.x J c.arm) /
            (2 * (c.p c.arm + c.state.rates J) ^ 2))

def denominatorSum {K T : ℕ} [NeZero K] (ell : LossTable K) (j tau : ℕ)
    (xi : EpochSeed T) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc tau n, denominatorTerm (cont ell j tau xi t)

/-- A rate-history-measurable disjoint family is fixed before challenge seeds. -/
def admissibleFamily {K T : ℕ} (tau : ℕ) (u : ℕ → Fin K) (family : Finset (Dyad T)) : Prop :=
  family ⊆ future T tau ∧
    (∀ J ∈ family, constantOn u J) ∧
    ∀ J ∈ family, ∀ J' ∈ family, J ≠ J' → Disjoint (rounds J) (rounds J')

def familyAdvantage {K T : ℕ} [NeZero K] (ell : LossTable K) (u : ℕ → Fin K)
    (j tau : ℕ) (xi : EpochSeed T) (family : Finset (Dyad T)) (n : ℕ) : ℝ :=
  alpha T * ∑ J ∈ family, advantage ell u j tau xi J n

def estimatedAdvantage {K T : ℕ} [NeZero K] (ell : LossTable K) (u : ℕ → Fin K)
    (j tau : ℕ) (xi : EpochSeed T) (family : Finset (Dyad T)) (n : ℕ) : ℝ :=
  alpha T * ∑ J ∈ family,
    ∑ t ∈ (rounds J).filter (fun t => t ≤ n ∧ (cont ell j tau xi t).main = false),
      let c := cont ell j tau xi t
      let est := estimate c (ell t c.arm) J
      dot c.state.q est - est (u (first J))

def armPenalty {K T : ℕ} (j : ℕ) (xi : EpochSeed T) (family : Finset (Dyad T))
    (logArg : Dyad T → ℝ) : ℝ :=
  ∑ J ∈ family, alpha T / intervalRate K T j xi J * Real.log (logArg J)

/-- Left and second-order sums in (40), with no restriction to interior comparators. -/
def omdRegret {K T : ℕ} [NeZero K] (ell : LossTable K) (j tau : ℕ)
    (xi : EpochSeed T) (J : Dyad T) (n : ℕ) (u : Vec K) : ℝ :=
  ∑ t ∈ (rounds J).filter (fun t => t ≤ n ∧ (cont ell j tau xi t).main = false),
    let c := cont ell j tau xi t
    dot (fun i => c.state.x J i - u i) (centered c (ell t c.arm) J)

def omdSecondOrder {K T : ℕ} [NeZero K] (ell : LossTable K) (j tau : ℕ)
    (xi : EpochSeed T) (J : Dyad T) (n : ℕ) : ℝ :=
  ∑ t ∈ (rounds J).filter (fun t => t ≤ n ∧ (cont ell j tau xi t).main = false),
    let c := cont ell j tau xi t
    let est := estimate c (ell t c.arm) J
    let y : Option (Fin K) → ℝ := fun a => match a with
      | none => dot c.state.q est
      | some i => est i
    ∑ a, complete (c.state.x J) a * (y a) ^ 2

end SwitchingRegret.Dyadic


