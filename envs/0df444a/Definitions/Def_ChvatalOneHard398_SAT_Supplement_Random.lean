-- Prove2me | Definitions.Def_ChvatalOneHard398_SAT_Supplement_Random
-- name    : ChvatalOneHard398_SAT_Supplement_Random
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:19:25.353558+00:00
-- url     : https://prove2.me/theorems/bc54a408-0b27-4ba6-a570-7a85ba3b2965
-- title:
--   General randomized computation with finite fair-coin tapes
-- statement:
--   A randomized computation from encoded inputs $I$ to ordinary encoded outputs $O$ consists of a deterministic map on an input and a finite bit tape, and a polynomial specifying the tape length. It is polynomial-time when the deterministic map has a published TM2 polynomial-time realization. All time bounds hold on every raw input and every tape.
--
--   For input $x$, the tape is uniform on $\{0,1\}^{p(|x|)}$. Its image gives the output probability law. An instance law and an independently drawn tape define the success probability
--   $$\Pr_{x,r}[A(x,r)=1\ \Longleftrightarrow\ P(x)].$$
--   All probabilities use nonnegative mass sums of genuine PMFs, followed by conversion to real numbers. This general interface has arbitrary encoded outputs, permitting both decision algorithms and distribution samplers. It contains no semantic correctness fields and no exact-real sampling operation.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.8–9, §2, promise problems and decision-LWE. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Oracle

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators

noncomputable def prob {A : Type} (μ : PMF A) (P : A → Prop) : ℝ := by
  classical
  exact (∑' x, if P x then μ x else 0).toReal

/-- General finite-random-tape computation. The machine stores no correctness conditions. -/
structure RandomAlg (I O : Type) where
  run : I × List Bool → O
  coins : Polynomial ℕ

def IsPolyRandom {I O : Type} (ei : I → List OnlineCRS.Combine.Sym)
    (eo : O → List OnlineCRS.Combine.Sym) (A : RandomAlg I O) : Prop :=
  PolyTime (encStepIn ei) eo A.run

noncomputable def randomLaw {I O : Type} (ei : I → List OnlineCRS.Combine.Sym)
    (A : RandomAlg I O) (x : I) : PMF O :=
  (PMF.uniformOfFintype (Fin (A.coins.eval (ei x).length) → Bool)).map
    (fun r => A.run (x,List.ofFn r))

noncomputable def outputOne {I : Type} (ei : I → List OnlineCRS.Combine.Sym)
    (A : RandomAlg I Bool) (μ : PMF I) : ℝ :=
  prob (μ.bind (randomLaw ei A)) (· = true)

noncomputable def success {I : Type} (ei : I → List OnlineCRS.Combine.Sym)
    (A : RandomAlg I Bool) (μ : PMF I) (P : I → Prop) : ℝ :=
  prob (μ.bind fun x => (randomLaw ei A x).map fun b => (x,b))
    (fun xb => xb.2 = true ↔ P xb.1)

end ChvatalOneHard398.SAT.Supplement


