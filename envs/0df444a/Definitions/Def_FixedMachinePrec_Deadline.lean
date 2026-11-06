-- Prove2me | Definitions.Def_FixedMachinePrec_Deadline
-- name    : FixedMachinePrec_Deadline
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:53.72657+00:00
-- url     : https://prove2.me/theorems/215f3c47-a5e2-472f-bbe1-ed55f65be6d4
-- title:
--   Algorithms 6 and 7: Deadline$(G,m,T)$ and Optimum$(G,m)$
-- statement:
--   **Algorithm 6, Deadline$(G,m,T)$.** Let $n=|V|$.
--
--   1. If $n=0$, return the empty schedule. If $T<\lceil n/m\rceil$, return NO. If $T\ge n$, return the **serial topological schedule** (one job per slot in the smallest-identifier topological order).
--   2. Otherwise add $mT-n$ isolated dummy jobs with fresh consecutive labels; let $J$ be the padded set, $N=mT$.
--   3. Compute the smallest-identifier topological rank of the padded order, generate $\mathcal F=\mathcal F_{4m+5}$ by Algorithm 1, retain $\mathcal F_{\mathrm{cut}}=\mathcal F_{m+3}$, and run Algorithm 4.
--   4. If $a(J)=0$, return NO. Otherwise delete the dummies from $\sigma(J)$ and return the slot schedule of the original jobs, assigning within each slot machines $1,2,\dots$ in increasing label order.
--
--   **Algorithm 7, Optimum$(G,m)$.** If $n=0$, return makespan $0$ and the empty schedule. Otherwise set $\ell=\lceil n/m\rceil-1$, $u=n$ and $\sigma_{\mathrm{best}}$ the serial schedule; while $u-\ell>1$, call Deadline with $T=\lfloor(\ell+u)/2\rfloor$, setting $\ell=T$ on NO and $u=T$, $\sigma_{\mathrm{best}}=\sigma$ on a schedule $\sigma$. Return $u$ and $\sigma_{\mathrm{best}}$.
--
--   **Formalization Note** Original jobs keep labels $0,\dots,n-1$ and dummies are $n,\dots,mT-1$. The transitive precedence is decided classically, a decision of a proposition rather than a choice of an object. The loop of Algorithm 7 runs with $n+1$ iterations of fuel, more than it can use.
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), §3.2, Algorithms 6 and 7, p.10

import Mathlib
import Definitions.Def_FixedMachinePrec_Instance
import Definitions.Def_FixedMachinePrec_GenerateFamily
import Definitions.Def_FixedMachinePrec_EvaluateFamily

namespace FixedMachinePrec

/-- `⌈n/m⌉` for natural numbers (`m ≥ 1`). -/
def ceilDiv (n m : ℕ) : ℕ := (n + m - 1) / m

/-- **The padded global order** on `J = Fin N` (Jansen §2.1, p.4; Lemma 5.2, p.12): the original
jobs keep their labels `0, …, n − 1` and their transitive precedence; the jobs `n, …, N − 1` are
isolated dummies ("fresh consecutive labels", Algorithm 6, p.10). -/
def paddedPrec (G : Instance) (N : ℕ) (x y : Fin N) : Prop :=
  ∃ (hx : x.val < G.n) (hy : y.val < G.n), G.Prec ⟨x.val, hx⟩ ⟨y.val, hy⟩

/-- The empty schedule (used when `n = 0`). -/
def emptySchedule (G : Instance) : SlotSchedule G :=
  ⟨fun _ => 0, fun _ => 0⟩

open Classical in
/-- **The serial topological schedule** (p.10): one job per slot, in the smallest-label
topological order, all on the first machine: `slot x = rank(x)`. -/
noncomputable def serialSchedule (G : Instance) : SlotSchedule G :=
  ⟨fun x => topoRank G.Prec x, fun _ => 0⟩

/-- Algorithm 6, Step 4: delete the dummy jobs from the stored full schedule `S = σ(J)` of
`J = Fin N` and read off the slot schedule of the original jobs; within each slot the original jobs
get machines `1, 2, …` in increasing label order. Discarding trailing empty slots does not change
any job's slot. -/
def extractSchedule (G : Instance) {N : ℕ} (S : List (Finset (Fin N))) : SlotSchedule G where
  slot x := S.findIdx (fun A => decide (x.val ∈ A.image Fin.val)) + 1
  machine x :=
    ((S.getD (S.findIdx fun A => decide (x.val ∈ A.image Fin.val)) ∅).filter
      fun y => y.val < G.n ∧ y.val < x.val).card

open Classical in
/-- **Algorithm 6, Deadline(G, m, T)** (Jansen, *Precedence Constraint Scheduling on a Fixed Number
of Machines*, manuscript, sha256 08cdf3e1…, Algorithm 6, p.10). Returns `none` for NO, or a
schedule of all original jobs. If `n = 0`, the empty schedule; if `T < ⌈n/m⌉`, NO; if `T ≥ n`, the
serial topological schedule. Otherwise pad with `mT − n` isolated dummies (`N = mT`), take the
smallest-label topological rank of the padded order, generate `F = F_{4m+5}` by Algorithm 1 and
retain `F_cut = F_{m+3}`, run Algorithm 4; if `a(J) = 0` answer NO, else delete the dummies.

**Formalization Note** The transitive precedence is decided classically; this is a decision of a
proposition, not a choice of an object, so the value is determined. -/
noncomputable def deadline (G : Instance) (m T : ℕ) : Option (SlotSchedule G) :=
  if G.n = 0 then some (emptySchedule G)
  else if T < ceilDiv G.n m then none
  else if G.n ≤ T then some (serialSchedule G)
  else
    let N := m * T
    let prec := paddedPrec G N
    let rank := topoRank prec
    let F := (generateFamily prec rank m (4 * m + 5)).toFinset
    let Fcut := (generateFamily prec rank m (m + 3)).toFinset
    match evaluateFamily prec m F Fcut Finset.univ with
    | none => none
    | some S => some (extractSchedule G S)

/-- The binary search loop of Algorithm 7, Step 2, with at most `fuel` iterations: while
`u − ℓ > 1`, set `T = ⌊(ℓ + u)/2⌋`; on NO set `ℓ = T`, on a schedule `σ` set `u = T`,
`σ_best = σ`. -/
noncomputable def optimumLoop (G : Instance) (m : ℕ) :
    ℕ → ℕ → ℕ → SlotSchedule G → ℕ × SlotSchedule G
  | 0, _, u, σ => (u, σ)
  | fuel + 1, l, u, σ =>
    if 1 < u - l then
      match deadline G m ((l + u) / 2) with
      | none => optimumLoop G m fuel ((l + u) / 2) u σ
      | some σ' => optimumLoop G m fuel l ((l + u) / 2) σ'
    else (u, σ)

/-- **Algorithm 7, Optimum(G, m)** (Jansen, manuscript, sha256 08cdf3e1…, Algorithm 7, p.10):
if `n = 0`, makespan `0` and the empty schedule; otherwise `ℓ = ⌈n/m⌉ − 1`, `u = n`,
`σ_best` = the serial schedule, then binary search. Returns `(u, σ_best)`.

**Formalization Note** The loop is given `n + 1` iterations of fuel; since `u − ℓ ≤ n + 1` and each
iteration decreases `u − ℓ`, the fuel never runs out before `u − ℓ ≤ 1`. -/
noncomputable def optimum (G : Instance) (m : ℕ) : ℕ × SlotSchedule G :=
  if G.n = 0 then (0, emptySchedule G)
  else optimumLoop G m (G.n + 1) (ceilDiv G.n m - 1) G.n (serialSchedule G)

end FixedMachinePrec


