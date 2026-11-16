-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ScalarODEUniqueness
-- name    : liuyao_ca_fd889115_k1_Analysis_ScalarODEUniqueness
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:54:43.978678+00:00
-- url     : https://prove2.me/theorems/9f64211d-0d62-4349-8d36-c910e0538d10
-- title:
--   Computable analysis · ScalarODEUniqueness · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ScalarODEUniqueness.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Differential
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PowerSeries

set_option autoImplicit true

/-!
# Direct scalar ODE uniqueness by finite mesh contraction

This module is deliberately separate from `PeanoBaker`.  For the scalar
initial-value problem `f' = f`, a direct rational mesh proof is shorter than
a general Volterra or Peano--Baker argument.  On a sufficiently short time
block, a finite subdivision turns the zero-initial difference estimate into a
strict contraction.  Refining the subdivision gives a sequence of rational
error envelopes, each at most half its predecessor.

The analytic work is to build the one-step mesh estimate from the two
derivative certificates.  The closure below is completely finite: the
explicit dyadic schedule converts repeated halving into equality of raw
interval representatives, with no complete function space and no Picard
iteration.
-/

namespace ComputableAnalysis

namespace ScalarODE

namespace FiniteMesh

/-- The literal finite rational sum over the first `count` mesh cells. -/
def sumUpTo (f : Nat -> Rat) : Nat -> Rat
  | 0 => 0
  | count + 1 => sumUpTo f count + f count

theorem sumUpTo_add (f g : Nat -> Rat) :
    forall count,
      sumUpTo (fun cell => f cell + g cell) count =
        sumUpTo f count + sumUpTo g count
  | 0 => by
      change (0 : Rat) = 0 + 0
      exact (Rat.zero_add 0).symm
  | count + 1 => by
      rw [sumUpTo, sumUpTo, sumUpTo, sumUpTo_add f g count]
      grind [Rat.add_assoc, Rat.add_comm]

theorem sumUpTo_const (value : Rat) :
    forall count,
      sumUpTo (fun _cell => value) count = (count : Rat) * value
  | 0 => by
      change (0 : Rat) = 0 * value
      exact (Rat.zero_mul value).symm
  | count + 1 => by
      rw [sumUpTo, sumUpTo_const value count, Rat.natCast_add]
      grind [Rat.add_mul, Rat.add_assoc]

/-- Cellwise rational bounds telescope under a finite mesh sum. -/
theorem sumUpTo_le_of_le {f g : Nat -> Rat} :
    forall count,
      (forall cell, cell < count -> f cell <= g cell) ->
        sumUpTo f count <= sumUpTo g count
  | 0, _ => by simp [sumUpTo]
  | count + 1, h => by
      rw [sumUpTo, sumUpTo]
      have hprefix : sumUpTo f count <= sumUpTo g count :=
        sumUpTo_le_of_le count (fun cell hcell =>
          h cell (Nat.lt_trans hcell (Nat.lt_succ_self count)))
      have hcell : f count <= g count := h count (Nat.lt_succ_self count)
      exact rat_add_le_add hprefix hcell

/-- A finite sum of nonnegative residual boxes is nonnegative. -/
theorem sumUpTo_nonneg {f : Nat -> Rat} :
    forall count,
      (forall cell, cell < count -> 0 <= f cell) ->
        0 <= sumUpTo f count
  | 0, _ => by simp [sumUpTo]
  | count + 1, h => by
      rw [sumUpTo]
      exact Rat.add_nonneg
        (sumUpTo_nonneg count (fun cell hcell =>
          h cell (Nat.lt_trans hcell (Nat.lt_succ_self count))))
        (h count (Nat.lt_succ_self count))

/-- The finite sum of successive mesh increments is exactly the endpoint
difference.  This is the rational telescoping identity used before any
interval or derivative limit is taken. -/
theorem sumUpTo_increments (state : Nat -> Rat) :
    forall count,
      sumUpTo (fun cell => state (cell + 1) - state cell) count =
        state count - state 0
  | 0 => by
      rw [sumUpTo]
      grind [Rat.sub_eq_add_neg]
  | count + 1 => by
      rw [sumUpTo, sumUpTo_increments state count]
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

end FiniteMesh

/-- A finite rational mesh estimate for the zero-initial difference on one
short block.  `state cell` is its cell-endpoint envelope.  The analytic
derivative proof supplies `cell_bound`; the rest is explicit finite
telescoping rational arithmetic. -/
structure FiniteMeshDifferenceBound (previous next : Rat) where
  cells : Nat
  state : Nat -> Rat
  step : Rat
  residual : Nat -> Rat
  next_eq : next = state cells
  initial_zero : state 0 = 0
  previous_nonneg : 0 <= previous
  step_nonneg : 0 <= step
  cell_bound : forall cell, cell < cells ->
    state (cell + 1) - state cell <= step * previous + residual cell
  residual_nonneg : forall cell, cell < cells -> 0 <= residual cell
  total_length_short : (cells : Rat) * step <= (1 : Rat) / 4
  residual_sum_small : FiniteMesh.sumUpTo residual cells <= previous / 4

/-- The rational output of one direct finite-mesh sweep on a short time
block.  `next_le_mesh_bound` is the result of summing the cell estimates for
the difference of two candidate solutions: the old envelope is multiplied by
the block length, and the finite quotient/box errors are collected in
`residual`.

Choosing a block of length at most one quarter and a residual at most one
quarter of the old envelope makes this one sweep a strict factor-one-half
contraction.  Every field is rational data or a rational inequality. -/
structure ShortBlockMeshSweep (previous next : Rat) where
  blockLength : Rat
  residual : Rat
  previous_nonneg : 0 <= previous
  blockLength_nonneg : 0 <= blockLength
  block_short : blockLength <= (1 : Rat) / 4
  residual_nonneg : 0 <= residual
  residual_small : residual <= previous / 4
  next_le_mesh_bound : next <= blockLength * previous + residual

namespace ShortBlockMeshSweep

/- The canonical arithmetic sweep used as a template by concrete ODE
certificates.  It realizes the two quarter-budget contributions exactly; no
derivative semantics are claimed by this definition. -/
def canonical (previous : Rat) (hprevious : 0 <= previous) :
    ShortBlockMeshSweep previous (previous / 2) where
  blockLength := 1 / 4
  residual := previous / 4
  previous_nonneg := hprevious
  blockLength_nonneg := by decide +kernel
  block_short := by decide +kernel
  residual_nonneg := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hprevious
      (by decide +kernel : (0 : Rat) <= (4 : Rat)⁻¹)
  residual_small := Rat.le_refl
  next_le_mesh_bound := by
    rw [Rat.div_def]
    grind [Rat.add_mul, Rat.mul_comm]

/-- One finite short-block mesh sweep halves its rational envelope. -/
theorem next_le_half {previous next : Rat}
    (sweep : ShortBlockMeshSweep previous next) :
    next <= previous * ((1 : Rat) / 2) := by
  have hlength : sweep.blockLength * previous <=
      ((1 : Rat) / 4) * previous :=
    Rat.mul_le_mul_of_nonneg_right sweep.block_short sweep.previous_nonneg
  calc
    next <= sweep.blockLength * previous + sweep.residual :=
      sweep.next_le_mesh_bound
    _ <= ((1 : Rat) / 4) * previous + previous / 4 :=
      rat_add_le_add hlength sweep.residual_small
    _ = previous * ((1 : Rat) / 2) := by
      rw [Rat.div_def]
      have hquarters : (1 : Rat) / 4 + 1 / 4 = 1 / 2 := by decide +kernel
      calc
        (1 / 4 : Rat) * previous + previous * 4⁻¹ =
            ((1 : Rat) / 4 + 1 / 4) * previous := by
              grind [Rat.add_mul]
        _ = (1 / 2 : Rat) * previous := by rw [hquarters]
        _ = previous * (1 / 2 : Rat) := by grind [Rat.mul_comm]

theorem canonical_next_le_half (previous : Rat) (hprevious : 0 <= previous) :
    previous / 2 <= previous * ((1 : Rat) / 2) := by
  exact next_le_half (canonical previous hprevious)

end ShortBlockMeshSweep

namespace FiniteMeshDifferenceBound

/-- Finite cell telescoping produces the short-block envelope needed for a
direct mesh-contraction sweep. -/
def toShortBlockMeshSweep {previous next : Rat}
    (bound : FiniteMeshDifferenceBound previous next) :
    ShortBlockMeshSweep previous next where
  blockLength := (bound.cells : Rat) * bound.step
  residual := FiniteMesh.sumUpTo bound.residual bound.cells
  previous_nonneg := bound.previous_nonneg
  blockLength_nonneg := Rat.mul_nonneg (Rat.natCast_nonneg) bound.step_nonneg
  block_short := bound.total_length_short
  residual_nonneg := FiniteMesh.sumUpTo_nonneg bound.cells bound.residual_nonneg
  residual_small := bound.residual_sum_small
  next_le_mesh_bound := by
    have hsum := FiniteMesh.sumUpTo_le_of_le bound.cells bound.cell_bound
    have htel := FiniteMesh.sumUpTo_increments bound.state bound.cells
    have hstate : bound.state bound.cells =
        FiniteMesh.sumUpTo
          (fun cell => bound.state (cell + 1) - bound.state cell) bound.cells := by
      rw [htel, bound.initial_zero]
      grind [Rat.sub_eq_add_neg]
    calc
      next = bound.state bound.cells := bound.next_eq
      _ = FiniteMesh.sumUpTo
          (fun cell => bound.state (cell + 1) - bound.state cell) bound.cells :=
        hstate
      _ <= FiniteMesh.sumUpTo
          (fun cell => bound.step * previous + bound.residual cell) bound.cells := hsum
      _ = ((bound.cells : Rat) * bound.step) * previous +
          FiniteMesh.sumUpTo bound.residual bound.cells := by
        rw [FiniteMesh.sumUpTo_add, FiniteMesh.sumUpTo_const]
        grind [Rat.mul_assoc]

theorem next_le_half {previous next : Rat}
    (bound : FiniteMeshDifferenceBound previous next) :
    next <= previous * ((1 : Rat) / 2) :=
  bound.toShortBlockMeshSweep.next_le_half

end FiniteMeshDifferenceBound

/-- A direct mesh-contraction certificate for one nonnegative rational error.

`bound round` is the rational envelope produced after `round` refinement
sweeps of a finite mesh.  The only analytic input is the checked local mesh
step `halve`; all later reasoning is rational arithmetic. -/
structure DirectMeshHalvingCertificate (error : Rat) where
  bound : Nat -> Rat
  error_nonneg : 0 <= error
  error_le_bound : forall round, error <= bound round
  halve : forall round,
    bound (round + 1) <= bound round * ((1 : Rat) / 2)

namespace DirectMeshHalvingCertificate

/-- Build a direct halving certificate from explicit finite short-block mesh
sweeps.  This is the public entry point for a by-hand uniqueness proof: the
analytic layer supplies the telescoped mesh estimate at each refinement, and
this constructor turns it into the uniform dyadic envelope. -/
def ofShortBlockSweeps (error : Rat) (bound : Nat -> Rat)
    (error_nonneg : 0 <= error)
    (error_le_bound : forall round, error <= bound round)
    (sweeps : forall round,
      ShortBlockMeshSweep (bound round) (bound (round + 1))) :
    DirectMeshHalvingCertificate error where
  bound := bound
  error_nonneg := error_nonneg
  error_le_bound := error_le_bound
  halve := fun round => (sweeps round).next_le_half

/-- Every finite refinement envelope is bounded by the explicit dyadic
envelope determined by the initial sweep. -/
theorem bound_le_geometric {error : Rat}
    (certificate : DirectMeshHalvingCertificate error) :
    forall round,
      certificate.bound round <=
        certificate.bound 0 * ((1 : Rat) / 2) ^ round
  | 0 => by
      simp
  | round + 1 => by
      have ih := bound_le_geometric certificate round
      calc
        certificate.bound (round + 1) <=
            certificate.bound round * ((1 : Rat) / 2) :=
          certificate.halve round
        _ <= (certificate.bound 0 * ((1 : Rat) / 2) ^ round) *
              ((1 : Rat) / 2) :=
          Rat.mul_le_mul_of_nonneg_right ih (by decide +kernel)
        _ = certificate.bound 0 * ((1 : Rat) / 2) ^ (round + 1) := by
          rw [Rat.pow_succ]
          grind [Rat.mul_assoc]

/-- The initial finite-mesh envelope is nonnegative, because it bounds a
nonnegative error. -/
theorem initial_bound_nonneg {error : Rat}
    (certificate : DirectMeshHalvingCertificate error) :
    0 <= certificate.bound 0 :=
  Rat.le_trans certificate.error_nonneg (certificate.error_le_bound 0)

/-- The explicit dyadic sweep selected for a positive rational tolerance
already bounds the mesh error by that tolerance. -/
theorem error_le_eps {error : Rat}
    (certificate : DirectMeshHalvingCertificate error) (eps : QPos) :
    error <= eps.val := by
  let round := RationalMajorant.halfDecayShift (certificate.bound 0) eps
  have herror := certificate.error_le_bound round
  have hgeometric := bound_le_geometric certificate round
  have hsmall := RationalMajorant.halfDecayShift_spec
    (initial_bound_nonneg certificate) eps
  exact Rat.le_trans herror (Rat.le_trans hgeometric hsmall)

/-- Repeated direct mesh contraction forces its error to be literally zero.

The proof chooses the executable refinement count supplied by
`RationalMajorant.halfDecayShift` for the tolerance `error / 2`; therefore it
does not invoke a real-number limit or an Archimedean axiom. -/
theorem error_eq_zero {error : Rat}
    (certificate : DirectMeshHalvingCertificate error) :
    error = 0 := by
  by_cases hzero : error = 0
  · exact hzero
  · have herrorPos : 0 < error :=
      Rat.lt_of_le_of_ne certificate.error_nonneg (Ne.symm hzero)
    let eps : QPos :=
      { val := error / 2
        property := by
          rw [Rat.div_def]
          exact Rat.mul_pos herrorPos
            ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2)) }
    have hhalf : error <= error / 2 := by
      exact error_le_eps certificate eps
    have hstrict : error / 2 < error := by
      rw [Rat.div_def]
      have hinv : (2 : Rat)⁻¹ < 1 := by decide +kernel
      calc
        error * (2 : Rat)⁻¹ < error * 1 :=
          Rat.mul_lt_mul_of_pos_left hinv herrorPos
        _ = error := Rat.mul_one _
    have hnot : ¬ error <= error / 2 := by
      simpa [Rat.not_le] using hstrict
    exact False.elim (hnot hhalf)

end DirectMeshHalvingCertificate

/-- A direct finite-mesh comparison for two scalar self-derivative solutions.

For each rational input, the analytic layer supplies the error envelope from
finite subdivisions of the interval between the common initial coordinate and
that input.  The fields intentionally do not mention Peano--Baker, Volterra,
or Picard iteration. -/
structure SelfDerivativeDirectMeshComparison
    (f g : FunctionOnInterval)
    (_hf : SolvesSelfDerivativeOnInterval f)
    (_hg : SolvesSelfDerivativeOnInterval g) where
  same_lower : f.lower = g.lower
  same_upper : f.upper = g.upper
  error : Rat -> Rat
  mesh_halving :
    forall x, DirectMeshHalvingCertificate (error x)
  equivalent_of_error_zero :
    forall x
      (hxF : inDomainInterval f.lower f.upper x)
      (hxG : inDomainInterval g.lower g.upper x),
      error x = 0 ->
        (PartialRealFunRaw.apply f.raw f.valid_on x (f.defined_on x hxF)).Equiv
          (PartialRealFunRaw.apply g.raw g.valid_on x (g.defined_on x hxG))

namespace SelfDerivativeDirectMeshComparison

/-- A direct mesh comparison closes to function equivalence pointwise. -/
theorem equivalent
    {f g : FunctionOnInterval}
    {hf : SolvesSelfDerivativeOnInterval f}
    {hg : SolvesSelfDerivativeOnInterval g}
    (comparison : SelfDerivativeDirectMeshComparison f g hf hg) :
    FunctionOnInterval.Equivalent f g := by
  refine ⟨comparison.same_lower, comparison.same_upper, ?_⟩
  intro x hxF hxG
  apply comparison.equivalent_of_error_zero x hxF hxG
  exact (comparison.mesh_halving x).error_eq_zero

end SelfDerivativeDirectMeshComparison

/-- The analytic provider for direct scalar initial-value uniqueness.

To construct it by hand, subtract the two candidate finite-difference
certificates, cover a short rational time block by a finite mesh, and verify
that one full sweep halves its rational error envelope.  Longer intervals are
handled by a finite chain of such blocks. -/
def SelfDerivativeDirectMeshUniqueness : Prop :=
  forall f g,
    (hf : SolvesSelfDerivativeOnInterval f) ->
    (hg : SolvesSelfDerivativeOnInterval g) ->
    f.lower = g.lower ->
    f.upper = g.upper ->
    hf.initial = hg.initial ->
    hf.initial_value.Equiv hg.initial_value ->
    Nonempty (SelfDerivativeDirectMeshComparison f g hf hg)

/-- Direct finite mesh contraction supplies uniqueness for `f' = f` with a
common certified initial value. -/
theorem selfDerivativeInitialValueUnique_of_directMesh
    (hdirect : SelfDerivativeDirectMeshUniqueness) :
    SelfDerivativeInitialValueUnique := by
  intro f g hf hg hlo hhi hinitial hvalue
  rcases hdirect f g hf hg hlo hhi hinitial hvalue with ⟨comparison⟩
  exact comparison.equivalent

end ScalarODE

end ComputableAnalysis


