-- Prove2me | Definitions.Def_PeriodicMAB_Upper_Policy
-- name    : PeriodicMAB_Upper_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:47.526991+00:00
-- url     : https://prove2.me/theorems/94884f98-0a47-4ea0-8b19-7f1671fdb715
-- title:
--   Algorithm 2, pp. 14–15, 21 — nested confidence-bound tournament, the two-stage policy and the weak oracle, event $\mathcal E$
-- statement:
--   Stage two of the two-stage policy (§3.2, Algorithm 2), the two-stage policy itself, and the weak oracle of §4.2.
--
--   Let $\hat T_1,\dots,\hat T_K$ be the periods the stage-two algorithm uses and $\hat d=\sum_k\hat T_k$. Let $\bar\Psi=\{1,\dots,nK\}$ be the stage-one epochs, $S=\lfloor\log_2T\rfloor$, and let $\Psi^{(s)}(t)$ be the stage-two epochs before $t$ at which an arm was pulled in Step 9 of round $s$. The **counting function** (8) is
--   $$
--   C_{k,t}(\Psi)=\big|\{j\in\Psi:\ \pi_j=k,\ j\equiv t \ (\mathrm{mod}\ \hat T_k)\}\big| ,
--   $$
--   the **estimated mean** (9) is the average of the rewards $Y_{k,j}$ over $j\in\Psi^{(s)}(t)\cup\bar\Psi$ with $\pi_j=k$ and $j\equiv t$ (mod $\hat T_k$), and the **confidence width** (10) is
--   $$
--   w^{(s)}_{k,t}=\frac{C_{k,t}(\bar\Psi)}{C_{k,t}(\Psi^{(s)}(t)\cup\bar\Psi)}\sqrt{\frac{4\sigma^2}{C_{k,t}(\bar\Psi)}\log\frac{8\hat dC_{k,t}(\bar\Psi)}{\delta}}
--   +\frac{C_{k,t}(\Psi^{(s)}(t))}{C_{k,t}(\Psi^{(s)}(t)\cup\bar\Psi)}\sqrt{\frac{4\sigma^2}{C_{k,t}(\Psi^{(s)}(t))}\log\frac{8\hat dC_{k,t}(\Psi^{(s)}(t))}{\delta}} .
--   $$
--
--   **Algorithm 2** (p. 15). At every epoch $t=nK+1,\dots,T$ a tournament starts with $s=1$ and $\mathcal A_1=\{1,\dots,K\}$. In round $s$:
--
--   1. if $w^{(s)}_{k,t}>2^{-s}\sigma$ for some $k\in\mathcal A_s$, pull such a $k$ and add $t$ to $\Psi^{(s)}$ (Steps 8–10);
--   2. else if $w^{(s)}_{k,t}\le\sigma/\sqrt T$ for all $k\in\mathcal A_s$, pull $\arg\max_{k\in\mathcal A_s}m^{(s)}_{k,t}$ (Steps 11–13);
--   3. else keep $\mathcal A_{s+1}=\{k\in\mathcal A_s: m^{(s)}_{k,t}\ge\max_{k'\in\mathcal A_s}m^{(s)}_{k',t}-2^{1-s}\sigma\}$ and go to round $s+1$ (Steps 14–16).
--
--   The **two-stage policy** pulls each arm $n$ times (stage one), estimates the periods with Algorithm 1, and runs Algorithm 2 with the estimated periods. The **weak oracle** (p. 21) is the same policy, except that Algorithm 2 uses the true periods $T_k$ and $d=\sum_kT_k$; its quantities (15)–(17) are written $\tilde C$, $\tilde m^{(s)}_{k,t}$, $\tilde w^{(s)}_{k,t}$. For the oracle, the event of Lemma 9 is
--   $$
--   \mathcal E=\big\{|\tilde m^{(s)}_{k,t}-\mu_{k,t}|\le\tilde w^{(s)}_{k,t}\ \ \forall k,\ t\in\{nK+1,\dots,T\},\ s\in\{1,\dots,S\}\big\}.
--   $$
--
--   **Formalization Note** The stage-two algorithm takes the period vector as an argument, so the oracle is literally the two-stage policy's stage two run on the true periods, and on the event $\Lambda$ the two policies coincide. Each epoch's decision is recorded as (arm, round, pulled-in-Step-9). Ties are broken by the smallest arm index (Step 8's "some $k$" and Step 12's argmax). An empty count gives a zero contribution in (9)–(10) (Lean's $0/0=0$). Step 14's test is the plain "else": when Steps 8 and 11 fail, every width is at most $2^{-s}\sigma$. The tournament has $S$ rounds; if it ever reached round $S+1$ it would pull the smallest maximizer of $m^{(S)}$ over $\mathcal A_S$, but for $T\ge4$ this cannot happen, because $2^{-S}\sigma\le\sigma/\sqrt T$. In (8) the printed "$j\in\Psi(t)$" is read as "$j\in\Psi$". The reward table is read only at pulled (arm, epoch) pairs.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, pp. 14–15, 21–22, Algorithm 2, (8)–(10), (15)–(17), Lemma 9 (event ℰ)

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral

open MeasureTheory ProbabilityTheory Finset

namespace PeriodicMAB.Upper

/-! Chen, Wang and Wang, *Learning and Optimization with Seasonal Patterns*,
arXiv:2005.08088v4: Algorithm 2 (p. 15) with the counting function (8) and the estimates
(9)–(10) (pp. 14–15), the two-stage policy of §3, and the weak oracle of p. 21 with (15)–(17).

The stage-two algorithm takes the period vector it uses as an argument `Phat`: the two-stage
policy runs it with the periods estimated by Algorithm 1, the oracle with the true periods.
It also takes the full reward table `Y k t` but reads `Y k j` only at epochs `j` where arm `k`
was pulled.

Every epoch's decision is recorded as `(arm, round, step9)`: stage-one epochs carry round `0`;
a stage-two epoch carries the round `s` of the tournament in which the arm was chosen and
whether it was chosen in Step 9 (`true`, the epoch joins `Ψ^(s)`) or in Step 12 (`false`). -/

/-- The record of one epoch: arm pulled, tournament round, pulled in Step 9. -/
abbrev Decision (K : ℕ) := Fin K × ℕ × Bool

variable {K : ℕ}

/-- The arm pulled at epoch `j ≥ 1` according to the history `h` (whose entry `j − 1` is
epoch `j`); `none` if epoch `j` is not yet in the history. -/
def armAt (h : List (Decision K)) (j : ℕ) : Option (Fin K) := (h[j - 1]?).map (·.1)

/-- The (round, step9) tag of epoch `j ≥ 1` in the history `h`. -/
def tagAt (h : List (Decision K)) (j : ℕ) : Option (ℕ × Bool) := (h[j - 1]?).map (·.2)

/-- `Ψ̄ = {1, …, nK}`, the stage-one epochs (Algorithm 2, Step 2). -/
def psiBar (n K : ℕ) : Finset ℕ := Icc 1 (n * K)

/-- `Ψ^(s)(t)`: the stage-two epochs `j ∈ {nK + 1, …, t − 1}` at which an arm was pulled in
Step 9 of round `s` (Steps 3, 10, 13). -/
def psiSet (h : List (Decision K)) (n s t : ℕ) : Finset ℕ :=
  (Icc (n * K + 1) (t - 1)).filter (fun j => tagAt h j = some (s, true))

/-- The counting function `C_{k,t}(Ψ) = |{ j ∈ Ψ : π_j = k, j ≡ t (mod T̂_k) }|` of (8). -/
def count (Phat : Fin K → ℕ) (h : List (Decision K)) (k : Fin K) (t : ℕ) (Ψ : Finset ℕ) : ℕ :=
  (Ψ.filter (fun j => armAt h j = some k ∧ j ≡ t [MOD Phat k])).card

/-- The estimated mean `m^(s)_{k,t}` of (9): the average of the rewards `Y_{k,j}` over the
epochs `j ∈ Ψ^(s)(t) ∪ Ψ̄` with `π_j = k` and `j ≡ t (mod T̂_k)` (`0` if there is none). -/
noncomputable def mHat (Phat : Fin K → ℕ) (Y : Fin K → ℕ → ℝ) (h : List (Decision K))
    (n s : ℕ) (k : Fin K) (t : ℕ) : ℝ :=
  (1 / (count Phat h k t (psiSet h n s t ∪ psiBar n K) : ℝ)) *
    ∑ j ∈ (psiSet h n s t ∪ psiBar n K).filter
        (fun j => armAt h j = some k ∧ j ≡ t [MOD Phat k]), Y k j

/-- The confidence width `w^(s)_{k,t}` of (10), with `d̂ = ∑_k T̂_k`:
`(C(Ψ̄)/C(Ψ^(s)(t) ∪ Ψ̄)) √((4σ²/C(Ψ̄)) log(8 d̂ C(Ψ̄)/δ))
 + (C(Ψ^(s)(t))/C(Ψ^(s)(t) ∪ Ψ̄)) √((4σ²/C(Ψ^(s)(t))) log(8 d̂ C(Ψ^(s)(t))/δ))`.
A term whose count `C` is `0` contributes `0`. -/
noncomputable def wHat (σ δ : ℝ) (Phat : Fin K → ℕ) (h : List (Decision K)) (n s : ℕ)
    (k : Fin K) (t : ℕ) : ℝ :=
  let dhat : ℝ := ∑ k', (Phat k' : ℝ)
  let cb : ℝ := count Phat h k t (psiBar n K)
  let cs : ℝ := count Phat h k t (psiSet h n s t)
  let cu : ℝ := count Phat h k t (psiSet h n s t ∪ psiBar n K)
  cb / cu * Real.sqrt (4 * σ ^ 2 / cb * Real.log (8 * dhat * cb / δ)) +
    cs / cu * Real.sqrt (4 * σ ^ 2 / cs * Real.log (8 * dhat * cs / δ))

variable [NeZero K]

/-- The smallest arm of a nonempty set of arms (arm `0` for the empty set). -/
def firstOf (A : Finset (Fin K)) : Fin K := if h : A.Nonempty then A.min' h else 0

/-- `max_{k ∈ A} f k` (value `0` for the empty set). -/
noncomputable def maxOver (A : Finset (Fin K)) (f : Fin K → ℝ) : ℝ :=
  if h : A.Nonempty then A.sup' h f else 0

open Classical in
/-- The smallest maximizer of `f` on `A`. -/
noncomputable def argmaxOver (A : Finset (Fin K)) (f : Fin K → ℝ) : Fin K :=
  firstOf (A.filter (fun k => ∀ k' ∈ A, f k' ≤ f k))

section Stage2

variable (σ δ : ℝ) (T n : ℕ) (Phat : Fin K → ℕ) (Y : Fin K → ℕ → ℝ)

open Classical in
/-- The candidate sets `𝒜_s` of the screening tournament at epoch `t` with history `h`:
`𝒜₁ = 𝒦` (Step 5) and
`𝒜_{s+1} = { k ∈ 𝒜_s : m^(s)_{k,t} ≥ max_{k' ∈ 𝒜_s} m^(s)_{k',t} − 2^{1−s}σ }` (Step 15).
(`𝒜₀ = 𝒦` is a placeholder.) -/
noncomputable def activeSet (h : List (Decision K)) (t : ℕ) : ℕ → Finset (Fin K)
  | 0 => univ
  | s + 1 =>
    if s = 0 then univ
    else (activeSet h t s).filter (fun k =>
      maxOver (activeSet h t s) (fun k' => mHat Phat Y h n s k' t) - 2 * σ / 2 ^ s ≤
        mHat Phat Y h n s k t)

open Classical in
/-- The repeat-loop of Algorithm 2 (Steps 6–18) at epoch `t`, starting in round `s` with
`fuel` rounds left. In round `s`:
* Step 8: if `w^(s)_{k,t} > 2^{−s}σ` for some `k ∈ 𝒜_s`, pull the smallest such `k`
  (record `(k, s, true)`);
* Step 11: else if `w^(s)_{k,t} ≤ σ/√T` for all `k ∈ 𝒜_s`, pull the smallest maximizer of
  `m^(s)_{·,t}` over `𝒜_s` (record `(k, s, false)`);
* Step 14: else (then `w^(s)_{k,t} ≤ 2^{−s}σ` for all `k ∈ 𝒜_s`) go to round `s + 1`.
With no fuel left (round `S + 1`; this cannot happen when `T ≥ 4`, because then
`2^{−S}σ ≤ σ/√T`), pull the smallest maximizer of `m^(s−1)_{·,t}` over `𝒜_{s−1}`. -/
noncomputable def tourney (h : List (Decision K)) (t : ℕ) : ℕ → ℕ → Decision K
  | 0, s => (argmaxOver (activeSet σ n Phat Y h t (s - 1)) (fun k => mHat Phat Y h n (s - 1) k t),
      s - 1, false)
  | f + 1, s =>
    if ∃ k ∈ activeSet σ n Phat Y h t s, σ / 2 ^ s < wHat σ δ Phat h n s k t then
      (firstOf ((activeSet σ n Phat Y h t s).filter (fun k => σ / 2 ^ s < wHat σ δ Phat h n s k t)),
        s, true)
    else if ∀ k ∈ activeSet σ n Phat Y h t s, wHat σ δ Phat h n s k t ≤ σ / Real.sqrt T then
      (argmaxOver (activeSet σ n Phat Y h t s) (fun k => mHat Phat Y h n s k t), s, false)
    else tourney h t f (s + 1)

/-- Stage one (Algorithm 1, Steps 3–6): at epoch `t ∈ {1, …, nK}` the arm with 0-based index
`⌊(t − 1)/n⌋` is pulled. -/
def stageOneArm (t : ℕ) : Fin K := if hk : (t - 1) / n < K then ⟨(t - 1) / n, hk⟩ else 0

/-- The decision at epoch `t` given the history `h` of epochs `1, …, t − 1`: the stage-one arm
if `t ≤ nK`, otherwise the tournament of Algorithm 2 with `S = ⌊log₂ T⌋` rounds, from round 1. -/
noncomputable def decision (h : List (Decision K)) (t : ℕ) : Decision K :=
  if t ≤ n * K then (stageOneArm n t, 0, false)
  else tourney σ δ T n Phat Y h t (Nat.log 2 T) 1

/-- The history of epochs `1, …, t` (entry `j − 1` is epoch `j`). -/
noncomputable def runHist : ℕ → List (Decision K)
  | 0 => []
  | t + 1 => runHist t ++ [decision σ δ T n Phat Y (runHist t) (t + 1)]

/-- The record of epoch `t ≥ 1`. -/
noncomputable def decisionAt (t : ℕ) : Decision K :=
  decision σ δ T n Phat Y (runHist σ δ T n Phat Y (t - 1)) t

/-- The policy: the arm `π_t` pulled at epoch `t ≥ 1`. -/
noncomputable def policy (t : ℕ) : Fin K := (decisionAt σ δ T n Phat Y t).1

/-- `Ψ^(s)(t)` along the run. -/
noncomputable def psiAt (s t : ℕ) : Finset ℕ := psiSet (runHist σ δ T n Phat Y (t - 1)) n s t

/-- `m^(s)_{k,t}` along the run. -/
noncomputable def mAt (s : ℕ) (k : Fin K) (t : ℕ) : ℝ :=
  mHat Phat Y (runHist σ δ T n Phat Y (t - 1)) n s k t

/-- `w^(s)_{k,t}` along the run. -/
noncomputable def wAt (s : ℕ) (k : Fin K) (t : ℕ) : ℝ :=
  wHat σ δ Phat (runHist σ δ T n Phat Y (t - 1)) n s k t

/-- `𝒜_s` at epoch `t` along the run. -/
noncomputable def activeAt (s t : ℕ) : Finset (Fin K) :=
  activeSet σ n Phat Y (runHist σ δ T n Phat Y (t - 1)) t s

end Stage2

section TwoStage

variable {Ω : Type*} (μ : Fin K → ℕ → ℝ) (ε : ℕ → Ω → ℝ) (σ δ H : ℝ) (T n g : ℕ)

/-- **The two-stage policy of §3** on the sample point `ω`: Algorithm 1 with parameters
`n, g, H` estimates the periods `T̂_k = estPeriod … k ω` from the stage-one rewards, and
Algorithm 2 with `σ, δ` runs on the estimated periods; rewards are `Y_{k,t} = µ_{k,t} + ε_t(ω)`. -/
noncomputable def twoStage (ω : Ω) : ℕ → Fin K :=
  policy σ δ T n (fun k => estPeriod μ ε σ H n g k ω) (reward μ ε ω)

/-- **The weak oracle of p. 21** on the sample point `ω`: the same two-stage policy, except
that Algorithm 2 uses the true periods `Tper` (so `C̃`, `m̃`, `w̃` of (15)–(17) with `d`). -/
noncomputable def oracle (Tper : Fin K → ℕ) (ω : Ω) : ℕ → Fin K :=
  policy σ δ T n Tper (reward μ ε ω)

/-- The event `ℰ` of Lemma 9, p. 22, for the oracle:
`|m̃^(s)_{k,t} − µ_{k,t}| ≤ w̃^(s)_{k,t}` for all arms `k`, epochs `t ∈ {nK + 1, …, T}` and
rounds `s ∈ 𝒮 = {1, …, ⌊log₂ T⌋}`. -/
noncomputable def eventE (Tper : Fin K → ℕ) : Set Ω :=
  {ω | ∀ k, ∀ t ∈ Icc (n * K + 1) T, ∀ s ∈ Icc 1 (Nat.log 2 T),
    |mAt σ δ T n Tper (reward μ ε ω) s k t - μ k t| ≤ wAt σ δ T n Tper (reward μ ε ω) s k t}

end TwoStage

end PeriodicMAB.Upper


