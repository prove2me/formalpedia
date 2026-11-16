-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_Supplement_TraceGeometry
-- name    : QuantumSepPoly_Frobenius_Supplement_TraceGeometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:46:09.92819+00:00
-- url     : https://prove2.me/theorems/a1d2fbee-7700-4f6e-baae-87e1ae22aa26
-- title:
--   Trace norm and explicit matrix output
-- statement:
--   For every finite complex square matrix $A$, define the unnormalized trace norm by
--   $$\|A\|_1=\sum_i\sqrt{\lambda_i(A^*A)}.$$
--   For two bipartite matrices, trace distance is $\frac12\|R-S\|_1$. The separable distance is its infimum over the published pure-product convex hull; the strict-gap predicate additionally records an attained minimum and its lower-bound property. Thus no unbounded or empty real-infimum default supplies the theorem's conclusion.
--
--   The output port takes its dimension from a natural register; Theorem 6.1 guarantees positivity. It serializes all $2d^4$ real/imaginary scalars. Matrix termination charges this serialization in addition to every executed RAM instruction. These definitions distinguish the trace norm from the inherited Frobenius norm.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Section 6, p. 24, 29, 35 (PDF p. 24, 29, 35); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_SeparableStates
import Definitions.Def_QuantumSepPoly_Frobenius_RealRAM

noncomputable section
open scoped BigOperators

namespace QuantumSepPoly.Frobenius.Supplement
/-- Unnormalized Schatten 1 norm: singular values are square roots of the
nonnegative eigenvalues of A* A. No Hermitian-input default is used. -/
def traceNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

def traceDistance {d : ℕ} (R S : Bip d) : ℝ := traceNorm (R-S) / 2

def traceDistanceSep {d : ℕ} (R : Bip d) : ℝ :=
  sInf ((fun S => traceDistance R S) '' Sep d)

/-- An attained strict gap, equivalent to the printed minimum; prevents an
unjustified replacement of a minimum by a default-valued infimum. -/
def TraceGap {d : ℕ} (η : ℝ) (R : Bip d) : Prop :=
  ∃ S ∈ Sep d, traceDistanceSep R = traceDistance R S ∧
    (∀ T ∈ Sep d, traceDistance R S ≤ traceDistance R T) ∧ η < traceDistance R S

/-- The output port serializes every real and imaginary entry, including zeros;
this is a finite list, not a lazy matrix or an oracle. -/
def matrixScalars (s : RAMState) : List ℝ :=
  List.ofFn (fun i : Fin (2*(s.nat 0)^4) => s.real i.val)

/-- Output dimension is n[0]; all complex entries are consecutive scalar pairs. -/
def matrixOutput (s : RAMState) : Bip (s.nat 0) := fun i j =>
  let d := s.nat 0
  let a := 2 * ((i.1.val*d+i.2.val)*d^2+j.1.val*d+j.2.val)
  let entries := matrixScalars s
  ((entries[a]?.getD 0 : ℝ) : ℂ) + Complex.I * ((entries[a+1]?.getD 0 : ℝ) : ℂ)

/-- Charged output serialization is included in the all-run operation bound. -/
def MatrixTerminates (P : RAMProgram) (initial : RAMState) (bound : ℝ) (r : RandomTape) : Prop :=
  ∃ steps, (ramRun P r initial steps).stopped = true ∧
    (((ramRun P r initial steps).cost + (matrixScalars (ramRun P r initial steps)).length : ℕ) : ℝ) ≤ bound
end QuantumSepPoly.Frobenius.Supplement


