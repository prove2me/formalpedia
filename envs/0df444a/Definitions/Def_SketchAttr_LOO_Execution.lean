-- Prove2me | Definitions.Def_SketchAttr_LOO_Execution
-- name    : SketchAttr_LOO_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:30:16.555266+00:00
-- url     : https://prove2.me/theorems/1d8b3493-a712-492a-b7db-6b165ce03407
-- title:
--   Theorem 5.1 — parameters, oracle correctness and execution bounds
-- statement:
--   The input parameters are read using
--   $$N=\lceil\log_4(1/\varepsilon)\rceil,\quad K=\lceil1/\varepsilon\rceil,\quad m=\left\lceil\frac{256}{\varepsilon}\log\frac{32nN}{\delta}\right\rceil,\quad k=\left\lfloor\log\frac{32nN}{\delta}\right\rfloor.$$
--   The main program receives only the five natural cells $n,N,m,K,k$ and the two complex cells $\varepsilon,\delta$. The call program alone receives the circuit's two encoding streams. Shared natural cell zero gives the requested derivative degree $d\ge1$; shared complex cells $[0,n)$ and $[n,2n)$ hold $w,g$. The answer segment holds $f(w)$ followed by $\nabla f(w),D_g\nabla f(w),\ldots,D_g^d\nabla f(w)$ in degree-major order.
--
--   Every completed call is compared with this answer computed mathematically at the query recorded on entry; the definition does not execute an oracle. The run is observed after the integer part of its real instruction budget. The scales for work and auxiliary space are
--   $$\operatorname{size}(c)(mN\log(N+1)+K),\qquad\operatorname{size}(c)N+nmN.$$
--
--   The failure set contains tapes with any coordinate error exceeding $\varepsilon\alpha(4)$. Its measure is outer measure, and finiteness of $\alpha(4)$ is required by every accuracy use. The output occupies the first $n$ cells of main private complex work memory. These definitions expose all conventions used in the single three-clause goal.
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), p. 14, Theorem 5.1; p. 18, parameter choice and complexity; p. 19, oracle access; canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib
import Definitions.Def_SketchAttr_LOO_Algorithm
import Definitions.Def_SketchAttr_LOO_Stability
import Definitions.Def_SketchAttr_LOO_Machine
open scoped ENNReal

namespace SketchAttr.LOO

/-- Integer reading of the parameter choice on p.18. -/
noncomputable def degreeParameter (ε : ℝ) : ℕ := ⌈Real.log (1/ε) / Real.log 4⌉₊
noncomputable def exactParameter (ε : ℝ) : ℕ := ⌈1/ε⌉₊
noncomputable def sampleParameter (n : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈(256/ε) * Real.log (32*n*degreeParameter ε/δ)⌉₊
noncomputable def trimParameter (n : ℕ) (ε δ : ℝ) : ℕ :=
  ⌊Real.log (32*n*degreeParameter ε/δ)⌋₊

/-- Main input is exactly [n,N,m,K,k] and [epsilon,delta].
The call program alone receives the encoded circuit as read-only input.
Shared natural cell 0 is the query degree. Shared complex cells [0,n)
and [n,2n) contain w and g. Responses start at 2n: value, then gradients
and their directional derivatives in degree-major order. -/
noncomputable def executionInput {n : ℕ} (c : Circuit n 1) (ε δ : ℝ) : MachineInput where
  naturals b := if b then fun a => c.natEncoding[a]?.getD 0 else
    fun a => [n, degreeParameter ε, sampleParameter n ε δ,
      exactParameter ε, trimParameter n ε δ][a]?.getD 0
  complexes b := if b then fun a => c.complexEncoding[a]?.getD 0 else
    fun a => [(ε : ℂ), (δ : ℂ)][a]?.getD 0

noncomputable def queryW (n : ℕ) (s : MachineState) : Vec n :=
  WithLp.toLp 2 fun i => s.cm 2 i.val
noncomputable def queryG (n : ℕ) (s : MachineState) : Vec n :=
  WithLp.toLp 2 fun i => s.cm 2 (n+i.val)

def oracleAnswer {n : ℕ} (c : Circuit n 1) (query answer : MachineState) : Prop :=
  1 ≤ query.nm 2 0 ∧
  answer.cm 2 (2*n) = circuitFunction c (queryW n query) ∧
  ∀ r : ℕ, r ≤ query.nm 2 0 → ∀ i : Fin n,
    answer.cm 2 (2*n+1+r*n+i.val) =
      iteratedFDeriv ℂ r (gradient (circuitFunction c)) (queryW n query)
        (fun _ => queryG n query) i

/-- Each actual completed call is checked against the query at entry. This
predicate observes an instruction trace; it gives the machine no oracle. -/
def CorrectCalls {n : ℕ} (c : Circuit n 1) (M S : Program) (input : MachineInput)
    (tape : ℕ → ℂ) (fuel : ℕ) : Prop :=
  let run := machineRun M S input tape
  ∀ a b : ℕ, a < b → b < fuel →
    (run a).halted = false → (run a).inCall = false →
    M[(run a).pc false]? = some .call →
    (∀ j : ℕ, a < j → j ≤ b → (run j).inCall = true) →
    S[(run b).pc true]? = some .halt → oracleAnswer c (run a) (run b)

noncomputable def operationScale {n : ℕ} (c : Circuit n 1) (ε δ : ℝ) : ℝ :=
  let N := degreeParameter ε
  let m := sampleParameter n ε δ
  let K := exactParameter ε
  c.size * ((m : ℝ)*N*Real.log (N+1) + K)

noncomputable def spaceScale {n : ℕ} (c : Circuit n 1) (ε δ : ℝ) : ℝ :=
  let N := degreeParameter ε
  let m := sampleParameter n ε δ
  (c.size : ℝ)*N + (n : ℝ)*m*N

noncomputable def executionFuel {n : ℕ} (C : ℝ) (c : Circuit n 1) (ε δ : ℝ) : ℕ :=
  ⌊C * operationScale c ε δ⌋₊

/-- Outputs occupy the first n complex cells of main private work memory. -/
noncomputable def executionResult {n : ℕ} (M S : Program) (C : ℝ) (c : Circuit n 1)
    (ε δ : ℝ) (tape : ℕ → ℂ) : MachineState :=
  machineRun M S (executionInput c ε δ) tape (executionFuel C c ε δ)

noncomputable def failureSet {n : ℕ} (M S : Program) (C : ℝ) (c : Circuit n 1)
    (ε δ : ℝ) (α : StabilityProfile) : Set (ℕ → ℂ) :=
  {tape | ∃ i : Fin n,
    ε * (α ⟨4, by norm_num⟩).toReal <
      ‖(executionResult M S C c ε δ tape).cm 0 i.val - circuitFunction c (basis i)‖}

end SketchAttr.LOO


