-- Prove2me | Definitions.Def_GhadimiLanAudit_TwoPhase_Execution
-- name    : GhadimiLanAudit_TwoPhase_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:49:09.584093+00:00
-- url     : https://prove2.me/theorems/36186140-f834-4709-9654-cec436e67437
-- title:
--   Counted full-run RSG and two-phase selection with cached zero-noise replies
-- statement:
--   An execution returns a value and a finite ordered trace. An oracle query records its point, sample and returned vector. Deterministic arithmetic and memory lookup emit no records; sequencing concatenates traces. The cost is
--
--   $$\operatorname{calls}(a)=\operatorname{length}(\operatorname{trace}(a)).$$
--
--   A full RSG run makes $N$ successive queries from $x_1$ using $x_{k+1}=x_k-\gamma G(x_k,\xi_k)$, with indices starting at one. It returns the stored point $x_R$ and the stored oracle reply from query $R$. The optimization phase sequences $S$ such runs in increasing candidate order. For positive noise, validation makes $T$ queries at each stored candidate and computes
--
--   $$\widehat g_s=\frac1T\sum_{k=1}^T G(\bar x_s,\eta_{s,k}).$$
--
--   Selection scans this ordered list, retaining the first candidate in every tie for minimum estimated-gradient norm. It uses the same scan on cached replies when $\sigma=0$, with no validation queries. If $N=0$, the algorithm returns $x_1$ and the empty trace before requesting active-run data.
--
--   These definitions connect the returned point to every query in the operational cost. Reusing a validation sample across candidates still records each oracle evaluation separately.
--
--   **Formalization Note** A fallback lookup value is defined for invalid indices, but the run law excludes such indices whenever a run is executed. The empty candidate-list fallback is unused under the prescribed positive $S$. The zero-noise and zero-iteration branches complete undefined source operations without changing $S,N,T$. No success probability or budget is a field of an execution.
-- source:
--   Ghadimi and Lan, Stochastic First- and Zeroth-Order Methods for Nonconvex Stochastic Programming, arXiv:1309.5549v1, https://arxiv.org/abs/1309.5549v1, pp. 5–6, (2.2) and full-run variant; p. 11, two-phase algorithm, (2.21), and its oracle counts; p. 12, (2.27)

import Definitions.Def_GhadimiLanAudit_TwoPhase_Problem

open MeasureTheory ProbabilityTheory

namespace GhadimiLanAudit.TwoPhase

/-- One oracle invocation records its input, sample and returned vector. -/
structure Query (n : ℕ) (Ξ : Type*) where
  point : GhadimiLan.RSG.E n
  sample : Ξ
  answer : GhadimiLan.RSG.E n

/-- A returned value together with the finite ordered oracle-call trace. -/
structure Execution (n : ℕ) (Ξ α : Type*) where
  value : α
  trace : List (Query n Ξ)

/-- Memory and deterministic arithmetic are free. -/
def pureExec {n : ℕ} {Ξ α : Type*} (a : α) : Execution n Ξ α := ⟨a, []⟩

/-- Sequencing concatenates the actual traces. -/
def bindExec {n : ℕ} {Ξ α β : Type*} (a : Execution n Ξ α)
    (f : α → Execution n Ξ β) : Execution n Ξ β :=
  let b := f a.value
  ⟨b.value, a.trace ++ b.trace⟩

/-- Every oracle query emits exactly one record, including repeated samples. -/
def queryExec {n : ℕ} {Ξ : Type*} (G : GhadimiLan.RSG.E n → Ξ → GhadimiLan.RSG.E n)
    (x : GhadimiLan.RSG.E n) (ξ : Ξ) : Execution n Ξ (GhadimiLan.RSG.E n) :=
  let y := G x ξ
  ⟨y, [⟨x, ξ, y⟩]⟩

/-- Finite sequencing in list order. -/
def collectExec {n : ℕ} {Ξ α : Type*} : List (Execution n Ξ α) → Execution n Ξ (List α)
  | [] => pureExec []
  | a :: as => bindExec a (fun x => bindExec (collectExec as) (fun xs => pureExec (x :: xs)))

/-- Operational cost is trace length; no target budget occurs in this definition. -/
def calls {n : ℕ} {Ξ α : Type*} (a : Execution n Ξ α) : ℕ := a.trace.length

/-- The first m steps of (2.2), p. 5, in the full-run implementation of p. 6.
Samples start at one; the terminal value after m steps is x_(m+1). -/
noncomputable def rsgPrefix {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) (γ : ℝ) (ξ : ℕ → Ξ) : ℕ → Execution n Ξ (GhadimiLan.RSG.E n)
  | 0 => pureExec P.x1
  | m + 1 => bindExec (rsgPrefix P γ ξ m) (fun x =>
      bindExec (queryExec P.G x (ξ (m + 1))) (fun y => pureExec (x - γ • y)))

/-- One-based trajectory, x_0 unused. This is determined by the oracle recursion. -/
noncomputable def trajectory {n : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) (N : ℕ) (ξ : ℕ → Ω → Ξ) (k : ℕ) (ω : Ω) : GhadimiLan.RSG.E n :=
  (rsgPrefix P (completedStep P N) (fun j => ξ j ω) (k - 1)).value

/-- Free lookup of the already-stored query at R. The fallback is unreachable
under the active run's index law, and does not query a gradient oracle. -/
def cachedCandidate {n : ℕ} {Ξ : Type*} (x1 : GhadimiLan.RSG.E n)
    (records : List (Query n Ξ)) (R : ℕ) : GhadimiLan.RSG.E n × GhadimiLan.RSG.E n :=
  match records[R - 1]? with
  | some q => (q.point, q.answer)
  | none => (x1, 0)

/-- One N-query run returns x_R and its stored reply, without any extra call. -/
noncomputable def candidateExec {n : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) (N : ℕ) (ξ : ℕ → Ω → Ξ) (R : Ω → ℕ) (ω : Ω) :
    Execution n Ξ (GhadimiLan.RSG.E n × GhadimiLan.RSG.E n) :=
  let a := rsgPrefix P (completedStep P N) (fun k => ξ k ω) N
  ⟨cachedCandidate P.x1 a.trace (R ω), a.trace⟩

/-- T actual calls at a fixed candidate, accumulated in order. -/
noncomputable def validationSum {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) (x : GhadimiLan.RSG.E n) (η : ℕ → Ξ) :
    ℕ → Execution n Ξ (GhadimiLan.RSG.E n)
  | 0 => pureExec 0
  | k + 1 => bindExec (validationSum P x η k) (fun v =>
      bindExec (queryExec P.G x (η (k + 1))) (fun y => pureExec (v + y)))

/-- The sample average in (2.21), called only on the positive-noise branch,
where the prescribed T is positive. -/
noncomputable def validationExec {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) (T : ℕ) (x : GhadimiLan.RSG.E n) (η : ℕ → Ξ) :
    Execution n Ξ (GhadimiLan.RSG.E n × GhadimiLan.RSG.E n) :=
  bindExec (validationSum P x η T) (fun v => pureExec (x, (T : ℝ)⁻¹ • v))

/-- Samples/indices for an active execution. Validation randomness is not even
requested at zero noise. These are raw inputs, with laws specified separately. -/
structure ActiveInput {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) (S : ℕ) (Ω : Type*) where
  ξ : Fin S → ℕ → Ω → Ξ
  R : Fin S → Ω → ℕ
  η : P.σ ≠ 0 → Fin S → ℕ → Ω → Ξ

/-- No random index or candidate list is required when N = 0. -/
def Input {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) (S N : ℕ) (Ω : Type*) := N ≠ 0 → ActiveInput P S Ω

/-- Candidate s is the point read from its own full-run trace. -/
noncomputable def candidate {n S N : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) (A : ActiveInput P S Ω) (s : Fin S) (ω : Ω) : GhadimiLan.RSG.E n :=
  (candidateExec P N (A.ξ s) (A.R s) ω).value.1

/-- Scan in increasing candidate order, replacing the incumbent only on a
strict improvement. Equal minima therefore keep the least index. -/
noncomputable def selectCandidate {n : ℕ} (x1 : GhadimiLan.RSG.E n)
    (xs : List (GhadimiLan.RSG.E n × GhadimiLan.RSG.E n)) : GhadimiLan.RSG.E n :=
  match xs with
  | [] => x1
  | a :: as => (as.foldl (fun best x => if ‖x.2‖ < ‖best.2‖ then x else best) a).1

/-- Optimization, post-optimization and selection from p. 11. The zero-noise
branch reuses stored replies and makes no validation calls. The N=0 branch
returns x1 immediately, without constructing an index or list. -/
noncomputable def twoPhaseExec {n S N T : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) (A : Input P S N Ω) (ω : Ω) : Execution n Ξ (GhadimiLan.RSG.E n) := by
  classical
  exact if hN : N = 0 then pureExec P.x1 else
    let B := A hN
    bindExec (collectExec ((List.finRange S).map (fun s =>
      let c := candidateExec P N (B.ξ s) (B.R s) ω
      ⟨(s, c.value), c.trace⟩))) (fun cs =>
      bindExec (collectExec (cs.map (fun sc =>
        if hσ : P.σ = 0 then pureExec sc.2 else
          validationExec P T sc.2.1 (fun k => B.η hσ sc.1 k ω))))
        (fun es => pureExec (selectCandidate P.x1 es)))

end GhadimiLanAudit.TwoPhase


