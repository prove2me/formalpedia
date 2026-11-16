-- Prove2me | Definitions.Def_SketchAttr_LOO_Supplement_Forward
-- name    : SketchAttr_LOO_Supplement_Forward
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:50:59.615033+00:00
-- url     : https://prove2.me/theorems/9e0c32db-fa89-42b9-8404-228b04675551
-- title:
--   Forward-only estimator and charged execution
-- statement:
--   Let $\phi$ be the function computed by a scalar arithmetic circuit. Set
--
--   $$N=\lceil\log_4(1/\varepsilon)\rceil,\quad \ell=\log(16nN/\delta),\quad m=\lceil256\ell/\varepsilon^2\rceil,\quad k=\lfloor\ell\rfloor.$$
--
--   Direction $g_j$ uses tape entries $jn,\ldots,(j+1)n-1$, and the same direction serves every coordinate and degree. The full forward coefficient is $a_{j,r}=T^{(r)}[g_j^{\otimes r}]$. Define
--
--   $$Y_{i,r,j}=\operatorname{Re}\frac{a_{j,r}\overline{g_{j,i}}^{\,r}}{r!},\qquad \widehat L_i=\phi(0)+\sum_{r=1}^{N}\operatorname{Trim}_k(Y_{i,r,0},\ldots,Y_{i,r,m-1}).$$
--
--   The execution wrapper uses the published finite complex RAM, input encoding, Gaussian tape and written-cell space measure. Its main natural input is $[n,N,m,k]$ followed by the circuit's natural encoding. Its main complex input is $[\varepsilon,\delta]$ followed by the circuit's constants. The unused second program receives zeros. Output cells are the first $n$ complex cells of main work memory. The operation and space scales are respectively $\operatorname{size}(\phi)mN\log(N+1)$ and $\operatorname{size}(\phi)N+nmN$; the fuel is the floor of a universal constant times the operation scale.
--
--   This is a specification and execution wrapper, not a new machine instruction. The theorem must supply a finite program that computes these coefficients, observations, selections and sums within the charged bounds.
-- source:
--   Chris Liaw, Aranyak Mehta, Grigoris Velegkas, Felix Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (October 2026), PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2, Section 2.1, pp. 4–5; Proposition 4.4, p. 12; Theorem A.1, p. 28

import Mathlib
import Definitions.Def_SketchAttr_LOO_Taylor
import Definitions.Def_SketchAttr_LOO_Sampling
import Definitions.Def_SketchAttr_LOO_Trim
import Definitions.Def_SketchAttr_LOO_Execution

namespace SketchAttr.LOO.Supplement

noncomputable def forwardLog (n : ℕ) (ε δ : ℝ) : ℝ :=
  Real.log (16 * n * degreeParameter ε / δ)

noncomputable def forwardSamples (n : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈256 * forwardLog n ε δ / ε^2⌉₊

noncomputable def forwardTrim (n : ℕ) (ε δ : ℝ) : ℕ :=
  ⌊forwardLog n ε δ⌋₊

/-- Direction j uses tape positions j*n,...,(j+1)*n-1. One direction is
reused across every coordinate and degree; distinct j have disjoint blocks. -/
noncomputable def forwardDirection (n j : ℕ) (tape : ℕ → ℂ) : Vec n :=
  WithLp.toLp 2 fun i => tape (j*n+i.val)

/-- Full scalar forward sketch: coefficient of z^r in phi(zg), not a slice.
For a circuit this is exactly evaluation over C[z]/(z^(N+1)) up to degree N. -/
noncomputable def forwardCoefficient {n : ℕ} (c : Circuit n 1)
    (r : ℕ) (g : Vec n) : ℂ :=
  diagonal (taylorTensor (circuitFunction c) r) g

noncomputable def forwardObservation {n : ℕ} (c : Circuit n 1)
    (r : ℕ) (i : Fin n) (g : Vec n) : ℝ :=
  (forwardCoefficient c r g * starRingEnd ℂ (g i)^r / (Nat.factorial r : ℂ)).re

noncomputable def forwardEstimate {n : ℕ} (c : Circuit n 1)
    (ε δ : ℝ) (tape : ℕ → ℂ) (i : Fin n) : ℂ :=
  circuitFunction c 0 +
    ((∑ r ∈ Finset.Icc 1 (degreeParameter ε),
      trim (forwardTrim n ε δ) (fun j : Fin (forwardSamples n ε δ) =>
        forwardObservation c r i (forwardDirection n j.val tape))) : ℝ)

/-- Main natural input: [n,N,m,k], followed by the unchanged circuit encoding.
Main complex input: [epsilon,delta], followed by the unchanged constant stream.
The second program's input is all zero: no call implementation is needed. -/
noncomputable def forwardInput {n : ℕ} (c : Circuit n 1) (ε δ : ℝ) : MachineInput where
  naturals b := if b then fun _ => 0 else fun a =>
    ([n, degreeParameter ε, forwardSamples n ε δ, forwardTrim n ε δ] ++
      c.natEncoding)[a]?.getD 0
  complexes b := if b then fun _ => 0 else fun a =>
    ([(ε : ℂ), (δ : ℂ)] ++ c.complexEncoding)[a]?.getD 0

noncomputable def forwardWorkScale {n : ℕ} (c : Circuit n 1) (ε δ : ℝ) : ℝ :=
  (c.size : ℝ) * forwardSamples n ε δ * degreeParameter ε *
    Real.log (degreeParameter ε + 1)

noncomputable def forwardSpaceScale {n : ℕ} (c : Circuit n 1) (ε δ : ℝ) : ℝ :=
  (c.size : ℝ) * degreeParameter ε +
    (n : ℝ) * forwardSamples n ε δ * degreeParameter ε

noncomputable def forwardFuel {n : ℕ} (C : ℝ) (c : Circuit n 1) (ε δ : ℝ) : ℕ :=
  ⌊C * forwardWorkScale c ε δ⌋₊

noncomputable def forwardRun {n : ℕ} (M : Program) (c : Circuit n 1)
    (ε δ : ℝ) (tape : ℕ → ℂ) (t : ℕ) : MachineState :=
  machineRun M [] (forwardInput c ε δ) tape t

/-- Outputs occupy complex cells 0,...,n-1 of main work memory. -/
noncomputable def forwardFailure {n : ℕ} (M : Program) (C : ℝ) (c : Circuit n 1)
    (ε δ : ℝ) (α : StabilityProfile) : Set (ℕ → ℂ) :=
  {tape | ∃ i : Fin n, ε * (α ⟨4, by norm_num⟩).toReal <
    ‖(forwardRun M c ε δ tape (forwardFuel C c ε δ)).cm 0 i.val -
      circuitFunction c (basis i)‖}

end SketchAttr.LOO.Supplement


