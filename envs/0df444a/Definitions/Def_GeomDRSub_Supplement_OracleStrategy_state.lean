-- Prove2me | Definitions.Def_GeomDRSub_Supplement_OracleStrategy_state
-- name    : GeomDRSub_Supplement_OracleStrategy_state
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:38:48.739324+00:00
-- url     : https://prove2.me/theorems/41eee28f-596d-4abb-b7eb-0b04a7748f5b
-- title:
--   Execution of an oracle algorithm: responses so far and number of emitted points
-- statement:
--   Fix an oracle algorithm $A$, a dimension $d$, inputs $x$, a seed $\omega$, and an answering rule $\mathrm{ans}(n,c)$ that gives the response to the call $c$ when $n$ points have been emitted before it. The execution is defined recursively. After $k$ calls the state is the pair consisting of the responses $(r_0,\dots,r_{k-1})$ and the number $n_k$ of emissions among $c_0,\dots,c_{k-1}$. The next call is $c_k=\mathrm{step}(d,x,k,\omega,r_0,\dots,r_{k-1})$, its response is $r_k=\mathrm{ans}(n_k,c_k)$, and $n_{k+1}=n_k+[c_k\text{ is an emission}]$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Definition 6.1, p.33, and Section 7.2, p.52

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_OracleStrategy

namespace GeomDRSub.Supplement

/-- **Execution of an oracle algorithm.** Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Definition 6.1 (p.33) and Section 7.2
(p.52). Given an answering rule `ans : ℕ → OCall d → OResp d` (the response to a call, as a function
of the number of marks emitted before it, see `offlineAns`, `onlineAns`), `A.state d x ans ω k` is
the pair (responses to the first `k` calls, number of marks among the first `k` calls). It is
defined by recursion: the `k`-th call is `A.step d x k ω` applied to the first `k` responses, and
its response is `ans n c`, where `n` is the number of marks emitted before it. -/
noncomputable def OracleStrategy.state {Ω : Type} [MeasurableSpace Ω] {m : ℕ}
    (A : OracleStrategy Ω m) (d : ℕ) (x : Fin m → ℝ) (ans : ℕ → OCall d → OResp d) (ω : Ω) :
    (k : ℕ) → (Fin k → OResp d) × ℕ
  | 0 => (Fin.elim0, 0)
  | k + 1 =>
      ((Fin.snoc (α := fun _ => OResp d) (OracleStrategy.state A d x ans ω k).1
          (ans (OracleStrategy.state A d x ans ω k).2
            (A.step d x k ω (OracleStrategy.state A d x ans ω k).1))),
        (OracleStrategy.state A d x ans ω k).2 +
          (if (A.step d x k ω (OracleStrategy.state A d x ans ω k).1).elim (fun _ => false)
              Sum.isRight then 1 else 0))

end GeomDRSub.Supplement


