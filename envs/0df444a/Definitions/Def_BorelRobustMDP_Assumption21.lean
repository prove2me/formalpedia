-- Prove2me | Definitions.Def_BorelRobustMDP_Assumption21
-- name    : BorelRobustMDP_Assumption21
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:54.783128+00:00
-- url     : https://prove2.me/theorems/5e3cef0f-4465-4b50-b10c-9cde48f12227
-- title:
--   Assumption 2.1: compactness and continuity of the model
-- statement:
--   Assumption 2.1 asks for: (i) each $D_n(x)$ is compact and $x\mapsto D_n(x)$ is upper semicontinuous, i.e. if $x_k\to x$ and $a_k\in D_n(x_k)$, then $(a_k)$ has an accumulation point in $D_n(x)$; (ii) $T_n(x,a,z)$ is continuous in $(x,a)$ for every $z$; (iii) the costs $c_n$ and $c_N$ are lower semicontinuous.
--
--   It gives the Bellman operator the semicontinuity from which minimizers exist.
--
--   **Formalization Note.** The upper semicontinuity is the platform's sequential `USCSetValued`. Since $T_n$ and $c_n$ are total extensions, (ii) and (iii) are stated on $D_n$ and $D_n\times E$.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, Assumption 2.1, p.3

import Mathlib
import Definitions.Def_BorelRobustMDP_DecisionModel
import Definitions.Def_MDPFinance_Semicontinuous_SetValued

open Set
open MDPFinance.Semicontinuous (USCSetValued)

namespace BorelRobustMDP

universe u v

/-- Assumption 2.1 (Bäuerle & Glauner, arXiv:2007.13103v1, p.3): (i) each `D_n(x)` is compact and
`x ↦ D_n(x)` is upper semicontinuous, (ii) `T_n(x, a, z)` is continuous in `(x, a)` for every `z`,
(iii) the costs `c_n` and `c_N` are lower semicontinuous.

**Formalization Note.** Upper semicontinuity is the paper's sequential condition, the platform's
`USCSetValued`. Since `T n`, `c n` are total extensions, (ii) and (iii) hold on `D_n` and `D_n × E`
only: an extension off `D_n` need not be continuous. -/
structure Assumption21 {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] [TopologicalSpace E] [TopologicalSpace A] {N : ℕ}
    (M : DecisionModel E A Z N) : Prop where
  isCompact_sec : ∀ n < N, ∀ x, IsCompact (M.sec n x)
  usc_sec : ∀ n < N, USCSetValued (M.sec n)
  continuousOn_T : ∀ n < N, ∀ z, ContinuousOn (fun y => M.T n y z) (M.D n)
  lsc_c : ∀ n < N, LowerSemicontinuousOn (fun w : (E × A) × E => M.c n w.1 w.2) (M.D n ×ˢ univ)
  lsc_cN : LowerSemicontinuous M.cN

end BorelRobustMDP


