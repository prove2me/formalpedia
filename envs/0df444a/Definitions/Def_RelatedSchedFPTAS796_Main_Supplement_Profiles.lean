-- Prove2me | Definitions.Def_RelatedSchedFPTAS796_Main_Supplement_Profiles
-- name    : RelatedSchedFPTAS796_Main_Supplement_Profiles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:58:06.894245+00:00
-- url     : https://prove2.me/theorems/3ce4622b-e9f5-4afa-99cf-1fb9dead1602
-- title:
--   Arbitrary-job two-sided profiles with charged schedule recovery
-- statement:
--   Fix $m$. A general profile solver is one pair of finite programs $P,R$ with natural constants $b,C,c$, chosen before arbitrary positive rational jobs $p_1,\ldots,p_n$, nonnegative rational targets $t$, and rational $\varepsilon,q\in(0,1)$. Its input words are $n$, then the numerator/denominator pairs of the jobs, targets, $\varepsilon$ and $q$. At every width $w\ge b(\lfloor\log_2(n+M+2)\rfloor+1)$, where $M$ includes every target word, every run of $P$ halts within $T=C(n+(1/\varepsilon)^{m-1})H_c$ and reports at most $C(1/\varepsilon)^{m-1}H_c$ vectors using the published set encoding. Here $H_c=(\log_2(n+2)\log_2(2/\varepsilon)\log_2(2/q))^c$.
--
--   With probability at least $1-q$, the entire reported set $\widetilde S$ simultaneously satisfies the published two-sided approximation of $\mathcal P(J)\cap[0,t]$, with
--   $$
--   \delta_i=C\varepsilon t_iH_c.
--   $$
--   Every target profile has a reported representative within $\delta$, and every reported vector has an original feasible profile within $\delta$; the latter profile may be outside the target box. Both sets are finite and nonnegative. Zero targets force exact zero error in those coordinates.
--
--   The same successful memory stores sufficient predecessor information for the fixed recovery program $R$. Given a selected output row $r$ in reserved cell $-1$, it runs on that memory using the same RAM instructions, and within $T$ additional steps returns a schedule of the original jobs whose work profile differs from that row by at most $\delta$ in every coordinate. This holds for every selected row and every recovery coin sequence. Only one selected schedule is recovered; the representation need not write a full schedule for each stored vector. This is the recovery convention of Remark 2.6 and preserves the same asymptotic bound for construction plus recovery.
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.32, Lemma D.3; Remark 2.6 p.9

import Mathlib
import Definitions.Def_RelatedSchedFPTAS796_Main_Problems

set_option autoImplicit false

namespace RelatedSchedFPTAS796.Main.Supplement

open MatroidSensOracle

/-- General profile input: n, positive rational sizes, nonnegative rational targets, ε,q.
Unlike completeInput, the jobs are arbitrary and external accuracy is not dyadic. -/
def generalInput {n m : ℕ} (p : Fin n → ℚ) (t : Fin m → ℚ) (ε q : ℚ) : List ℤ :=
  (n : ℤ) :: (ratVecWords p ++ ratVecWords t ++ ratWords ε ++ ratWords q)

/-- Recovery is a second fixed finite RAM program operating on the stored output memory.
A caller selects one row by placing its index in reserved cell −1; every run then writes an
original n-job schedule, whose profile is within the same coordinate error of that row.
This is one selected schedule, not n output words per stored vector (Remark 2.6, p.9).
The new entry program uses the very same exec instruction semantics and fuel accounting. -/
def RecoversProfiles {n m w : ℕ} (R : List Instr) (mem : ℤ → BitVec w)
    (p : Fin n → ℚ) (δ : Fin m → ℝ) (T : ℝ) : Prop :=
  ∀ r : ℕ, r < outCount mem → ∀ ω : Coins,
    ∃ (mem' : ℤ → BitVec w) (σ : Fin n → Fin m),
      exec R ω ⌊T⌋₊ 0 0 (Function.update mem (-1) (BitVec.ofNat w r)) = some mem' ∧
      OutputsSchedule mem' σ ∧
      (∀ i, |workProfile (ratToReal p) σ i - outRatVec m mem r i| ≤ δ i)

/-- A general-job, simultaneous two-sided profile solver with stored recovery information.
P and R, width/time/size/error constants precede all jobs, targets, accuracies and widths.
On every run output size is bounded; on one event of probability ≥1−q the entire set
approximates the target box and every selected row recovers an original schedule.
The time T bounds set construction and separately one recovery, hence their sum is ≤2T.
The target enters maxWord; a zero target gives exactly zero coordinate error. -/
def GeneralProfileSolvable (m : ℕ) : Prop :=
  ∃ (P R : List Instr) (b C c : ℕ), ∀ (n : ℕ) (p : Fin n → ℚ)
    (t : Fin m → ℚ) (ε q : ℚ),
    (∀ j, 0 < p j) → (∀ i, 0 ≤ t i) → 0 < ε → ε < 1 → 0 < q → q < 1 →
    ∀ w : ℕ, widthMin b n (maxWord (generalInput p t ε q)) ≤ w →
      (∀ ω : Coins, ∃ mem, runFor P w (generalInput p t ε q)
          (fptasTime C c n m ε q) ω = some mem ∧
          (outCount mem : ℝ) ≤ C * (1 / (ε : ℝ)) ^ (m - 1) * polylog3 n ε q c) ∧
      FailsAtMost P w (generalInput p t ε q) (fptasTime C c n m ε q)
        (fun mem =>
          ApproxAdd (workProfiles m (ratToReal p)) (outRatSet m mem)
            (Set.Icc 0 (ratToReal t))
            (fun i => C * (ε : ℝ) * (t i : ℝ) * polylog3 n ε q c) ∧
          RecoversProfiles R mem p
            (fun i => C * (ε : ℝ) * (t i : ℝ) * polylog3 n ε q c)
            (fptasTime C c n m ε q)) q

end RelatedSchedFPTAS796.Main.Supplement


