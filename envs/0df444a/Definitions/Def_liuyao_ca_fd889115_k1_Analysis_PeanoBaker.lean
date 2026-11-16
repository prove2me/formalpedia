-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PeanoBaker
-- name    : liuyao_ca_fd889115_k1_Analysis_PeanoBaker
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:54:32.120197+00:00
-- url     : https://prove2.me/theorems/f745de3d-42df-4ae7-8e47-8e6794ae0e0a
-- title:
--   Computable analysis · PeanoBaker · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/PeanoBaker.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Differential
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PowerSeries

set_option autoImplicit true

/-!
# Finite Peano--Baker algebra

This module deliberately begins before a general continuous ODE theorem.  It
contains only finite rational data: matrices, sampled linear recurrences, and
the noncommutative word expansion underlying the Peano--Baker series.

For a continuous system, the words will be evaluated by iterated *certified*
integrals over ordered rational simplexes.  That analytic layer must provide
its own interval-enclosure, nesting, and tail certificates; this file does
not invoke a limit, an ambient matrix library, or completeness of the reals.
-/

namespace ComputableAnalysis

theorem rat_sub_add_sub_eq (a b c d : Rat) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

namespace LinearODE

/-- A finite-dimensional rational state vector.  The dimension is explicit so
that every later finite sum is an executable traversal of `Fin dimension`. -/
abbrev RatVector (dimension : Nat) := Fin dimension -> Rat

/-- A finite-dimensional rational matrix.  This is intentionally a local
definition, rather than an import of a general matrix theory. -/
abbrev RatMatrix (dimension : Nat) := Fin dimension -> Fin dimension -> Rat

def vectorZero (dimension : Nat) : RatVector dimension := fun _ => 0

def matrixZero (dimension : Nat) : RatMatrix dimension := fun _ _ => 0

def matrixIdentity (dimension : Nat) : RatMatrix dimension :=
  fun i j => if i = j then 1 else 0

def vectorAdd {dimension : Nat} (x y : RatVector dimension) : RatVector dimension :=
  fun i => x i + y i

def vectorSub {dimension : Nat} (x y : RatVector dimension) : RatVector dimension :=
  fun i => x i - y i

def vectorScale {dimension : Nat} (r : Rat) (x : RatVector dimension) :
    RatVector dimension :=
  fun i => r * x i

def matrixAdd {dimension : Nat} (A B : RatMatrix dimension) : RatMatrix dimension :=
  fun i j => A i j + B i j

def matrixScale {dimension : Nat} (r : Rat) (A : RatMatrix dimension) :
    RatMatrix dimension :=
  fun i j => r * A i j

/-- The finite rational sum used by matrix multiplication and matrix action.
No infinite sum is hidden in this definition.  The recursive form keeps the
additivity proofs entirely in Lean's finite `Fin` layer. -/
def finiteSum : {dimension : Nat} -> (Fin dimension -> Rat) -> Rat
  | 0, _ => 0
  | _ + 1, f => f 0 + finiteSum (fun i => f i.succ)

theorem finiteSum_zero (dimension : Nat) :
    finiteSum (fun _ : Fin dimension => 0) = 0 := by
  induction dimension with
  | zero => simp [finiteSum]
  | succ dimension ih =>
      simp [finiteSum, ih]
      grind [Rat.add_assoc, Rat.add_comm]

/-- Finite sum of a constant over the explicit coordinate index. -/
theorem finiteSum_const {dimension : Nat} (c : Rat) :
    finiteSum (fun _ : Fin dimension => c) = (dimension : Rat) * c := by
  induction dimension with
  | zero => simp [finiteSum]
  | succ dimension ih =>
      simp only [finiteSum, ih]
      have hcast : ((Nat.succ dimension : Nat) : Rat) =
          (dimension : Rat) + 1 := by
        rw [show Nat.succ dimension = dimension + 1 by omega, Rat.natCast_add]
        simp
      rw [hcast]
      grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
        Rat.add_left_comm, Rat.mul_comm]

theorem finiteSum_add {dimension : Nat} (f g : Fin dimension -> Rat) :
    finiteSum (fun i => f i + g i) = finiteSum f + finiteSum g := by
  induction dimension with
  | zero =>
      simp [finiteSum]
      grind [Rat.add_assoc, Rat.add_comm]
  | succ dimension ih =>
      simp [finiteSum, ih]
      grind [Rat.add_assoc, Rat.add_comm]

theorem finiteSum_le {dimension : Nat} {f g : Fin dimension -> Rat}
    (h : forall i, f i <= g i) : finiteSum f <= finiteSum g := by
  induction dimension with
  | zero =>
      simp [finiteSum]
  | succ dimension ih =>
      simp only [finiteSum]
      exact rat_add_le_add (h 0) (ih (fun i => h i.succ))

theorem finiteSum_nonneg {dimension : Nat} {f : Fin dimension -> Rat}
    (hf : forall i, 0 <= f i) : 0 <= finiteSum f := by
  induction dimension with
  | zero => simp [finiteSum]
  | succ dimension ih =>
      simp only [finiteSum]
      exact Rat.add_nonneg (hf 0) (ih (fun i => hf i.succ))

/-- A nonnegative finite sum dominates each of its entries.  This small
lemma is the bridge from the independently evaluated interval boxes of a
linear system to one executable rational coefficient bound. -/
theorem finiteSum_term_le {dimension : Nat} (f : Fin dimension -> Rat)
    (hf : forall i, 0 <= f i) (j : Fin dimension) :
    f j <= finiteSum f := by
  induction dimension with
  | zero => exact Fin.elim0 j
  | succ dimension ih =>
      refine Fin.cases ?_ ?_ j
      · simp only [finiteSum]
        have htail : 0 <= finiteSum (fun i : Fin dimension => f i.succ) :=
          finiteSum_nonneg (fun i => hf i.succ)
        calc
          f 0 = f 0 + 0 := (Rat.add_zero _).symm
          _ <= f 0 + finiteSum (fun i : Fin dimension => f i.succ) :=
            rat_add_le_add Rat.le_refl htail
      · intro j
        simp only [finiteSum]
        have hfirst : 0 <= f 0 := hf 0
        have htail := ih (fun i => f i.succ) (fun i => hf i.succ) j
        exact Rat.le_trans htail
          (calc
            finiteSum (fun i : Fin dimension => f i.succ) =
                0 + finiteSum (fun i : Fin dimension => f i.succ) :=
              (Rat.zero_add _).symm
            _ <= f 0 + finiteSum (fun i : Fin dimension => f i.succ) :=
              (Rat.add_le_add_right).2 hfirst)

theorem finiteSum_mul_left {dimension : Nat} (a : Rat) (f : Fin dimension -> Rat) :
    a * finiteSum f = finiteSum (fun i => a * f i) := by
  induction dimension with
  | zero =>
      simp [finiteSum]
  | succ dimension ih =>
      simp [finiteSum, ih, Rat.mul_add]

theorem finiteSum_mul_right {dimension : Nat} (a : Rat) (f : Fin dimension -> Rat) :
    finiteSum f * a = finiteSum (fun i => f i * a) := by
  induction dimension with
  | zero =>
      simp [finiteSum]
  | succ dimension ih =>
      simp [finiteSum, ih, Rat.add_mul]

theorem finiteSum_mul_le_of_nonneg {dimension : Nat}
    (f g : Fin dimension -> Rat) (c : Rat)
    (hf : forall i, 0 <= f i) (hg : forall i, g i <= c) :
    finiteSum (fun i => f i * g i) <= c * finiteSum f := by
  calc
    finiteSum (fun i => f i * g i) <=
        finiteSum (fun i => f i * c) := by
      exact finiteSum_le (fun i =>
        Rat.mul_le_mul_of_nonneg_left (hg i) (hf i))
    _ = finiteSum f * c := (finiteSum_mul_right c f).symm
    _ = c * finiteSum f := Rat.mul_comm _ _

theorem finiteSum_mul_le_of_le_left {dimension : Nat}
    (f g : Fin dimension -> Rat) (c : Rat)
    (hf : forall i, f i <= c) (hg : forall i, 0 <= g i) :
    finiteSum (fun i => f i * g i) <= c * finiteSum g := by
  calc
    finiteSum (fun i => f i * g i) <=
        finiteSum (fun i => c * g i) := by
      exact finiteSum_le (fun i =>
        Rat.mul_le_mul_of_nonneg_right (hf i) (hg i))
    _ = c * finiteSum g := (finiteSum_mul_left c g).symm

/-- Finite rational sums may be enumerated in either order.  This is the
local Fubini calculation used to prove associativity of the project-local
matrix product; it is only a double traversal of finite index types. -/
theorem finiteSum_swap :
    forall (m n : Nat) (f : Fin m -> Fin n -> Rat),
      finiteSum (fun i => finiteSum (f i)) =
        finiteSum (fun j => finiteSum (fun i => f i j))
  | 0, n, _ => by
      change 0 = finiteSum (fun _ : Fin n => 0)
      exact (finiteSum_zero n).symm
  | m + 1, n, f => by
      simp only [finiteSum]
      rw [finiteSum_swap m n (fun i j => f i.succ j)]
      rw [← finiteSum_add]

theorem finiteSum_ite_eq {dimension : Nat} (j : Fin dimension) (f : Fin dimension -> Rat) :
    finiteSum (fun i => if i = j then f i else 0) = f j := by
  induction dimension with
  | zero => exact Fin.elim0 j
  | succ dimension ih =>
      refine Fin.cases ?_ ?_ j
      · have htail :
          finiteSum (fun i : Fin dimension => if i.succ = 0 then f i.succ else 0) = 0 := by
            rw [show (fun i : Fin dimension => if i.succ = 0 then f i.succ else 0) =
              (fun _ => 0) by
                funext i
                split
                · rename_i h
                  exact False.elim ((Fin.succ_ne_zero i) h)
                · rfl]
            exact finiteSum_zero dimension
        rw [finiteSum, htail]
        grind [Rat.add_assoc, Rat.add_comm]
      · intro j
        have hzero : ¬ ((0 : Fin (dimension + 1)) = j.succ) := by
          intro h
          exact (Fin.succ_ne_zero j) h.symm
        simp [finiteSum, ih, hzero]
        exact Rat.zero_add _

def matrixMul {dimension : Nat} (A B : RatMatrix dimension) : RatMatrix dimension :=
  fun i j => finiteSum (fun k => A i k * B k j)

/-- Rational scaling is compatible with the local matrix product on the
right.  This finite distributivity calculation is the scalar algebra behind
the constant-coefficient Peano--Baker simplex terms. -/
theorem matrixMul_matrixScale_right {dimension : Nat}
    (A B : RatMatrix dimension) (r : Rat) :
    matrixMul A (matrixScale r B) = matrixScale r (matrixMul A B) := by
  funext i j
  unfold matrixMul matrixScale
  calc
    finiteSum (fun k => A i k * (r * B k j)) =
        finiteSum (fun k => r * (A i k * B k j)) := by
          congr 1
          funext k
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ = r * finiteSum (fun k => A i k * B k j) :=
      (finiteSum_mul_left r (fun k => A i k * B k j)).symm

theorem matrixMul_matrixScale_left {dimension : Nat}
    (A B : RatMatrix dimension) (r : Rat) :
    matrixMul (matrixScale r A) B = matrixScale r (matrixMul A B) := by
  funext i j
  unfold matrixMul matrixScale
  calc
    finiteSum (fun k => (r * A i k) * B k j) =
        finiteSum (fun k => r * (A i k * B k j)) := by
          congr 1
          funext k
          exact Rat.mul_assoc _ _ _
    _ = r * finiteSum (fun k => A i k * B k j) :=
      (finiteSum_mul_left r (fun k => A i k * B k j)).symm

theorem matrixScale_comp {dimension : Nat} (r s : Rat)
    (A : RatMatrix dimension) :
    matrixScale r (matrixScale s A) = matrixScale (r * s) A := by
  funext i j
  unfold matrixScale
  exact (Rat.mul_assoc _ _ _).symm

theorem matrixScale_one {dimension : Nat} (A : RatMatrix dimension) :
    matrixScale 1 A = A := by
  funext i j
  unfold matrixScale
  exact Rat.one_mul _

/-- Two scalar multiples of one finite rational matrix combine by addition of
their rational coefficients. -/
theorem matrixAdd_scale_same {dimension : Nat} (r s : Rat)
    (A : RatMatrix dimension) :
    matrixAdd (matrixScale r A) (matrixScale s A) = matrixScale (r + s) A := by
  funext i j
  exact (Rat.add_mul _ _ _).symm

/-- Associativity of the local rational matrix product.  This is proved from
finite distributivity and the finite-sum interchange above, without importing
a general matrix library. -/
theorem matrixMul_assoc {dimension : Nat} (A B C : RatMatrix dimension) :
    matrixMul (matrixMul A B) C = matrixMul A (matrixMul B C) := by
  funext i j
  unfold matrixMul
  calc
    finiteSum (fun k =>
        finiteSum (fun l => A i l * B l k) * C k j) =
        finiteSum (fun k =>
          finiteSum (fun l => (A i l * B l k) * C k j)) := by
            congr 1
            funext k
            exact finiteSum_mul_right (C k j) (fun l => A i l * B l k)
    _ = finiteSum (fun l =>
          finiteSum (fun k => (A i l * B l k) * C k j)) :=
        finiteSum_swap dimension dimension
          (fun k l => (A i l * B l k) * C k j)
    _ = finiteSum (fun k =>
          A i k * finiteSum (fun l => B k l * C l j)) := by
            congr 1
            funext k
            calc
              finiteSum (fun l => (A i k * B k l) * C l j) =
                  finiteSum (fun l => A i k * (B k l * C l j)) := by
                    congr 1
                    funext l
                    exact Rat.mul_assoc _ _ _
              _ = A i k * finiteSum (fun l => B k l * C l j) :=
                (finiteSum_mul_left (A i k) (fun l => B k l * C l j)).symm

def matrixApply {dimension : Nat} (A : RatMatrix dimension) (x : RatVector dimension) :
    RatVector dimension :=
  fun i => finiteSum (fun j => A i j * x j)

/-! Absolute-value estimates are kept at the finite-sum level.  They are the
entrywise substitute for importing a normed matrix space: every bound below
is an executable rational traversal of a finite index type. -/
theorem finiteSum_qabs_mul_le {dimension : Nat} (f g : Fin dimension -> Rat) :
    qabs (finiteSum (fun i => f i * g i)) <=
      finiteSum (fun i => qabs (f i) * qabs (g i)) := by
  induction dimension with
  | zero =>
      simp [finiteSum, qabs]
  | succ dimension ih =>
      simp only [finiteSum]
      calc
        qabs (f 0 * g 0 + finiteSum (fun i : Fin dimension =>
          f i.succ * g i.succ)) <=
            qabs (f 0 * g 0) +
              qabs (finiteSum (fun i : Fin dimension =>
                f i.succ * g i.succ)) := qabs_add_le _ _
        _ <= qabs (f 0) * qabs (g 0) +
              finiteSum (fun i : Fin dimension =>
                qabs (f i.succ) * qabs (g i.succ)) := by
          apply rat_add_le_add
          · rw [qabs_mul]
            exact Rat.le_refl
          · exact ih (fun i => f i.succ) (fun i => g i.succ)

theorem matrixApply_qabs_le {dimension : Nat}
    (A : RatMatrix dimension) (x : RatVector dimension) (i : Fin dimension) :
    qabs (matrixApply A x i) <=
      finiteSum (fun j => qabs (A i j) * qabs (x j)) := by
  unfold matrixApply
  exact finiteSum_qabs_mul_le (fun j => A i j) x

theorem matrixMul_qabs_le {dimension : Nat}
    (A B : RatMatrix dimension) (i j : Fin dimension) :
    qabs (matrixMul A B i j) <=
      finiteSum (fun k => qabs (A i k) * qabs (B k j)) := by
  unfold matrixMul
  exact finiteSum_qabs_mul_le (fun k => A i k) (fun k => B k j)

def matrixRowAbsSum {dimension : Nat} (A : RatMatrix dimension) (i : Fin dimension) : Rat :=
  finiteSum (fun j => qabs (A i j))

def vectorAbsSum {dimension : Nat} (x : RatVector dimension) : Rat :=
  finiteSum (fun i => qabs (x i))

theorem vectorAbsSum_nonneg {dimension : Nat} (x : RatVector dimension) :
    0 <= vectorAbsSum x := by
  unfold vectorAbsSum
  exact finiteSum_nonneg (fun i => qabs_nonneg (x i))

/-- Each coordinate absolute value is bounded by the finite `l1` sum. This
lets an endpoint vector comparison yield componentwise rational error bounds
for the represented scalar outputs. -/
theorem vectorAbsSum_component_le {dimension : Nat}
    (x : RatVector dimension) (i : Fin dimension) :
    qabs (x i) <= vectorAbsSum x := by
  unfold vectorAbsSum
  induction dimension with
  | zero => exact Fin.elim0 i
  | succ dimension ih =>
      refine Fin.cases ?_ ?_ i
      · simp only [finiteSum]
        have htail : 0 <= finiteSum (fun j : Fin dimension => qabs (x j.succ)) :=
          finiteSum_nonneg (fun _ => qabs_nonneg _)
        grind [Rat.add_assoc, Rat.add_comm]
      · intro j
        simp only [finiteSum]
        have hrec := ih (fun k => x k.succ) j
        have hfirst : 0 <= qabs (x 0) := qabs_nonneg _
        grind [Rat.add_assoc, Rat.add_comm]

/-- A vector difference estimate immediately supplies each rational
coordinate error. This is the form needed to turn the finite ODE envelope
into cofinal lower-endpoint closeness for scalar represented components. -/
theorem vectorDifference_component_le {dimension : Nat}
    (x y : RatVector dimension) (i : Fin dimension) :
    qabs (x i - y i) <= vectorAbsSum (vectorSub x y) := by
  exact vectorAbsSum_component_le (vectorSub x y) i

theorem qabs_le_of_bounds {x radius : Rat}
    (hlower : -radius <= x) (hupper : x <= radius) :
    qabs x <= radius := by
  unfold qabs
  split
  · simpa using Rat.neg_le_neg hlower
  · exact hupper

/-- A symmetric rational bound can be recovered from a `qabs` inequality
when its radius is nonnegative. -/
theorem qabs_bounds_of_le {x radius : Rat}
    (hradius : 0 <= radius) (h : qabs x <= radius) :
    -radius <= x /\ x <= radius := by
  by_cases hx : x < 0
  · have hneg : -x <= radius := by
      simpa [qabs, hx] using h
    constructor
    · have := Rat.neg_le_neg hneg
      simpa using this
    · exact Rat.le_trans (Rat.le_of_lt hx) hradius
  · have hxnonneg : 0 <= x := Rat.not_lt.mp hx
    have hpos : x <= radius := by
      simpa [qabs, hx] using h
    constructor
    · have hnegRadius : -radius <= 0 := by
        have := Rat.neg_le_neg hradius
        simpa using this
      exact Rat.le_trans hnegRadius hxnonneg
    · exact hpos

theorem qabs_sub_le_add_of_intermediate {x y z leftBound rightBound : Rat}
    (hleft : qabs (x - y) <= leftBound)
    (hright : qabs (y - z) <= rightBound) :
    qabs (x - z) <= leftBound + rightBound := by
  have hdecomp : x - z = (x - y) + (y - z) := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  calc
    qabs (x - z) = qabs ((x - y) + (y - z)) := by rw [hdecomp]
    _ <= qabs (x - y) + qabs (y - z) := qabs_add_le _ _
    _ <= leftBound + rightBound := rat_add_le_add hleft hright

theorem vectorAbsSum_le_of_component_bounds {dimension : Nat}
    (x : RatVector dimension) (bound : Fin dimension -> Rat)
    (hbound : forall i, qabs (x i) <= bound i) :
    vectorAbsSum x <= finiteSum bound := by
  unfold vectorAbsSum
  exact finiteSum_le hbound

theorem vectorAbsSum_sub_le {dimension : Nat}
    (x y : RatVector dimension) :
    vectorAbsSum (vectorSub x y) <= vectorAbsSum x + vectorAbsSum y := by
  unfold vectorAbsSum vectorSub
  calc
    finiteSum (fun i => qabs (x i - y i)) <=
        finiteSum (fun i => qabs (x i) + qabs (y i)) :=
      finiteSum_le (fun i => qabs_sub_le (x i) (y i))
    _ = finiteSum (fun i => qabs (x i)) +
        finiteSum (fun i => qabs (y i)) := finiteSum_add _ _


def matrixColumnAbsSum {dimension : Nat} (A : RatMatrix dimension) (j : Fin dimension) : Rat :=
  finiteSum (fun i => qabs (A i j))

/-- A uniform rational bound on every matrix entry induces an explicit
column-sum bound. This turns independently certified coefficient enclosures
for a finite-dimensional linear ODE into the operator growth constant used
by the Euler comparison. The finite sum is left explicit, so its value is
computable for each dimension. -/
theorem matrixColumnAbsSum_le_of_entry_bound {dimension : Nat}
    (A : RatMatrix dimension) (entryBound : Rat)
    (hentry : forall i j, qabs (A i j) <= entryBound) (j : Fin dimension) :
    matrixColumnAbsSum A j <=
      finiteSum (fun _ : Fin dimension => entryBound) := by
  unfold matrixColumnAbsSum
  exact finiteSum_le (fun i => hentry i j)

theorem matrixColumnAbsSum_identity {dimension : Nat} (j : Fin dimension) :
    matrixColumnAbsSum (matrixIdentity dimension) j = 1 := by
  unfold matrixColumnAbsSum matrixIdentity
  rw [show (fun i => qabs (if i = j then 1 else 0)) =
      (fun i => if i = j then 1 else 0) by
        funext i
        by_cases h : i = j
        · rw [if_pos h]
          change qabs 1 = 1
          unfold qabs
          simp only [if_neg (by decide : ¬ (1 : Rat) < 0)]
        · rw [if_neg h]
          change qabs 0 = 0
          unfold qabs
          simp only [if_neg (by decide : ¬ (0 : Rat) < 0)]]
  change finiteSum (fun i => if i = j then (1 : Rat) else 0) =
    (fun _ => (1 : Rat)) j
  exact finiteSum_ite_eq j (fun _ => (1 : Rat))

theorem matrixColumnAbsSum_matrixScale {dimension : Nat}
    (r : Rat) (A : RatMatrix dimension) (j : Fin dimension) :
    matrixColumnAbsSum (matrixScale r A) j =
      qabs r * matrixColumnAbsSum A j := by
  unfold matrixColumnAbsSum matrixScale
  rw [show (fun i => qabs (r * A i j)) =
      (fun i => qabs r * qabs (A i j)) by
        funext i
        exact qabs_mul r (A i j)]
  exact (finiteSum_mul_left (qabs r) (fun i => qabs (A i j))).symm

theorem matrixColumnAbsSum_matrixAdd_le {dimension : Nat}
    (A B : RatMatrix dimension) (j : Fin dimension) :
    matrixColumnAbsSum (matrixAdd A B) j <=
      matrixColumnAbsSum A j + matrixColumnAbsSum B j := by
  unfold matrixColumnAbsSum matrixAdd
  calc
    finiteSum (fun i => qabs (A i j + B i j)) <=
        finiteSum (fun i => qabs (A i j) + qabs (B i j)) := by
      exact finiteSum_le (fun i => qabs_add_le _ _)
    _ = finiteSum (fun i => qabs (A i j)) +
        finiteSum (fun i => qabs (B i j)) := finiteSum_add _ _

theorem matrixColumnAbsSum_affineStep_le {dimension : Nat}
    (B : RatMatrix dimension) (j : Fin dimension) :
    matrixColumnAbsSum (matrixAdd (matrixIdentity dimension) B) j <=
      1 + matrixColumnAbsSum B j := by
  have h := matrixColumnAbsSum_matrixAdd_le (matrixIdentity dimension) B j
  rw [matrixColumnAbsSum_identity] at h
  exact h

/-- The rational Euler matrix `I + h A` has column growth at most
`1 + |h| M` whenever the coefficient matrix has column-sum norm at most
`M`. This is the coefficient-to-recurrence bridge needed before applying
the finite residual propagation theorem. -/
theorem matrixColumnAbsSum_eulerStep_le {dimension : Nat}
    (A : RatMatrix dimension) (h M : Rat)
    (hcolumn : forall j, matrixColumnAbsSum A j <= M)
    (j : Fin dimension) :
    matrixColumnAbsSum
        (matrixAdd (matrixIdentity dimension) (matrixScale h A)) j <=
      1 + qabs h * M := by
  calc
    matrixColumnAbsSum
        (matrixAdd (matrixIdentity dimension) (matrixScale h A)) j <=
        1 + matrixColumnAbsSum (matrixScale h A) j :=
      matrixColumnAbsSum_affineStep_le (matrixScale h A) j
    _ = 1 + qabs h * matrixColumnAbsSum A j := by
      rw [matrixColumnAbsSum_matrixScale]
    _ <= 1 + qabs h * M := by
      exact (Rat.add_le_add_left).2
        (Rat.mul_le_mul_of_nonneg_left (hcolumn j) (qabs_nonneg h))

/-- Fully explicit Euler growth bound from a uniform entrywise certificate.
For a dimension `d` system with every coefficient entry bounded by `B`, the
matrix step `I + h A` has column-sum growth at most
`1 + |h| * sum_{i < d} B`. -/
theorem matrixColumnAbsSum_eulerStep_le_of_entry_bound {dimension : Nat}
    (A : RatMatrix dimension) (h entryBound : Rat)
    (hentry : forall i j, qabs (A i j) <= entryBound) (j : Fin dimension) :
    matrixColumnAbsSum
        (matrixAdd (matrixIdentity dimension) (matrixScale h A)) j <=
      1 + qabs h * finiteSum (fun _ : Fin dimension => entryBound) := by
  apply matrixColumnAbsSum_eulerStep_le A h
    (finiteSum (fun _ : Fin dimension => entryBound))
  intro k
  exact matrixColumnAbsSum_le_of_entry_bound A entryBound hentry k

/-- For a positive-width mesh cell, the same coefficient estimate takes the
usual Euler form `1 + h M` without an absolute value on the step. -/
theorem matrixColumnAbsSum_eulerStep_le_of_nonneg_entry_bound
    {dimension : Nat} (A : RatMatrix dimension) (h entryBound : Rat)
    (hstep : 0 <= h)
    (hentry : forall i j, qabs (A i j) <= entryBound) (j : Fin dimension) :
    matrixColumnAbsSum
        (matrixAdd (matrixIdentity dimension) (matrixScale h A)) j <=
      1 + h * finiteSum (fun _ : Fin dimension => entryBound) := by
  have habsolute := matrixColumnAbsSum_eulerStep_le_of_entry_bound
    A h entryBound hentry j
  rw [qabs_eq_self_of_nonneg hstep] at habsolute
  exact habsolute

theorem matrixApply_vectorAbsSum_le {dimension : Nat}
    (A : RatMatrix dimension) (x : RatVector dimension) :
    vectorAbsSum (matrixApply A x) <=
      finiteSum (fun j => matrixColumnAbsSum A j * qabs (x j)) := by
  unfold vectorAbsSum
  calc
    finiteSum (fun i => qabs (matrixApply A x i)) <=
        finiteSum (fun i => finiteSum (fun j =>
          qabs (A i j) * qabs (x j))) := by
      exact finiteSum_le (fun i => matrixApply_qabs_le A x i)
    _ = finiteSum (fun j => finiteSum (fun i =>
          qabs (A i j) * qabs (x j))) := by
      exact finiteSum_swap dimension dimension
        (fun i j => qabs (A i j) * qabs (x j))
    _ = finiteSum (fun j => matrixColumnAbsSum A j * qabs (x j)) := by
      congr 1
      funext j
      unfold matrixColumnAbsSum
      exact (finiteSum_mul_right (qabs (x j))
        (fun i => qabs (A i j))).symm

theorem matrixApply_vectorAbsSum_le_of_column_bound {dimension : Nat}
    (A : RatMatrix dimension) (x : RatVector dimension) (c : Rat)
    (hcolumn : forall j, matrixColumnAbsSum A j <= c) :
    vectorAbsSum (matrixApply A x) <= c * vectorAbsSum x := by
  calc
    vectorAbsSum (matrixApply A x) <=
        finiteSum (fun j => matrixColumnAbsSum A j * qabs (x j)) :=
      matrixApply_vectorAbsSum_le A x
    _ <= c * finiteSum (fun j => qabs (x j)) :=
      finiteSum_mul_le_of_le_left
        (fun j => matrixColumnAbsSum A j) (fun j => qabs (x j)) c
        hcolumn (fun j => qabs_nonneg _)
    _ = c * vectorAbsSum x := rfl

theorem matrixMul_columnAbsSum_le {dimension : Nat}
    (A B : RatMatrix dimension) (j : Fin dimension) :
    matrixColumnAbsSum (matrixMul A B) j <=
      finiteSum (fun k => matrixColumnAbsSum A k * qabs (B k j)) := by
  unfold matrixColumnAbsSum
  calc
    finiteSum (fun i => qabs (matrixMul A B i j)) <=
        finiteSum (fun i => finiteSum (fun k =>
          qabs (A i k) * qabs (B k j))) := by
      exact finiteSum_le (fun i => matrixMul_qabs_le A B i j)
    _ = finiteSum (fun k => finiteSum (fun i =>
          qabs (A i k) * qabs (B k j))) := by
      exact finiteSum_swap dimension dimension
        (fun i k => qabs (A i k) * qabs (B k j))
    _ = finiteSum (fun k => matrixColumnAbsSum A k * qabs (B k j)) := by
      congr 1
      funext k
      unfold matrixColumnAbsSum
      exact (finiteSum_mul_right (qabs (B k j))
        (fun i => qabs (A i k))).symm

theorem matrixMul_columnAbsSum_le_of_column_bound {dimension : Nat}
    (A B : RatMatrix dimension) (c : Rat)
    (hcolumn : forall k, matrixColumnAbsSum A k <= c) (j : Fin dimension) :
    matrixColumnAbsSum (matrixMul A B) j <=
      c * matrixColumnAbsSum B j := by
  calc
    matrixColumnAbsSum (matrixMul A B) j <=
        finiteSum (fun k => matrixColumnAbsSum A k * qabs (B k j)) :=
      matrixMul_columnAbsSum_le A B j
    _ <= c * finiteSum (fun k => qabs (B k j)) :=
      finiteSum_mul_le_of_le_left
        (fun k => matrixColumnAbsSum A k) (fun k => qabs (B k j)) c
        hcolumn (fun k => qabs_nonneg _)
    _ = c * matrixColumnAbsSum B j := rfl

theorem matrixRowAbsSum_identity {dimension : Nat} (i : Fin dimension) :
    matrixRowAbsSum (matrixIdentity dimension) i = 1 := by
  unfold matrixRowAbsSum matrixIdentity
  rw [show (fun j => qabs (if i = j then 1 else 0)) =
      (fun j => if j = i then 1 else 0) by
        funext j
        by_cases h : i = j
        · rw [if_pos h, if_pos h.symm]
          decide +kernel
        · have h' : ¬ j = i := by
            intro hji
            exact h hji.symm
          rw [if_neg h, if_neg h']
          decide +kernel
      ]
  change finiteSum (fun j => if j = i then (1 : Rat) else 0) =
    (fun _ => (1 : Rat)) i
  exact finiteSum_ite_eq i (fun _ => (1 : Rat))

theorem matrixRowAbsSum_matrixScale {dimension : Nat}
    (r : Rat) (A : RatMatrix dimension) (i : Fin dimension) :
    matrixRowAbsSum (matrixScale r A) i =
      qabs r * matrixRowAbsSum A i := by
  unfold matrixRowAbsSum matrixScale
  rw [show (fun j => qabs (r * A i j)) =
      (fun j => qabs r * qabs (A i j)) by
        funext j
        exact qabs_mul r (A i j)]
  exact (finiteSum_mul_left (qabs r) (fun j => qabs (A i j))).symm

theorem matrixRowAbsSum_matrixAdd_le {dimension : Nat}
    (A B : RatMatrix dimension) (i : Fin dimension) :
    matrixRowAbsSum (matrixAdd A B) i <=
      matrixRowAbsSum A i + matrixRowAbsSum B i := by
  unfold matrixRowAbsSum matrixAdd
  calc
    finiteSum (fun j => qabs (A i j + B i j)) <=
        finiteSum (fun j => qabs (A i j) + qabs (B i j)) := by
      exact finiteSum_le (fun j => qabs_add_le _ _)
    _ = finiteSum (fun j => qabs (A i j)) +
        finiteSum (fun j => qabs (B i j)) := finiteSum_add _ _

theorem matrixRowAbsSum_affineStep_le {dimension : Nat}
    (B : RatMatrix dimension) (i : Fin dimension) :
    matrixRowAbsSum (matrixAdd (matrixIdentity dimension) B) i <=
      1 + matrixRowAbsSum B i := by
  have h := matrixRowAbsSum_matrixAdd_le (matrixIdentity dimension) B i
  rw [matrixRowAbsSum_identity] at h
  exact h

theorem matrixMul_rowAbsSum_le {dimension : Nat}
    (A B : RatMatrix dimension) (i : Fin dimension) :
    matrixRowAbsSum (matrixMul A B) i <=
      finiteSum (fun k => qabs (A i k) * matrixRowAbsSum B k) := by
  calc
    matrixRowAbsSum (matrixMul A B) i =
        finiteSum (fun j => qabs (matrixMul A B i j)) := rfl
    _ <= finiteSum (fun j =>
        finiteSum (fun k => qabs (A i k) * qabs (B k j))) := by
      exact finiteSum_le (fun j => matrixMul_qabs_le A B i j)
    _ = finiteSum (fun k =>
        finiteSum (fun j => qabs (A i k) * qabs (B k j))) := by
      exact finiteSum_swap dimension dimension
        (fun j k => qabs (A i k) * qabs (B k j))
    _ = finiteSum (fun k => qabs (A i k) * matrixRowAbsSum B k) := by
      congr 1
      funext k
      unfold matrixRowAbsSum
      exact (finiteSum_mul_left (qabs (A i k))
        (fun j => qabs (B k j))).symm

theorem vectorAdd_zero_right {dimension : Nat} (x : RatVector dimension) :
    vectorAdd x (vectorZero dimension) = x := by
  funext i
  exact Rat.add_zero _

theorem vectorAdd_assoc {dimension : Nat} (x y z : RatVector dimension) :
    vectorAdd (vectorAdd x y) z = vectorAdd x (vectorAdd y z) := by
  funext i
  exact Rat.add_assoc _ _ _

theorem matrixApply_zero {dimension : Nat} (A : RatMatrix dimension) :
    matrixApply A (vectorZero dimension) = vectorZero dimension := by
  funext i
  unfold matrixApply vectorZero
  rw [show (fun j => A i j * 0) = (fun _ => 0) by
    funext j
    exact Rat.mul_zero _]
  exact finiteSum_zero dimension

theorem matrixApply_vectorAdd {dimension : Nat}
    (A : RatMatrix dimension) (x y : RatVector dimension) :
    matrixApply A (vectorAdd x y) =
      vectorAdd (matrixApply A x) (matrixApply A y) := by
  funext i
  unfold matrixApply vectorAdd
  calc
    finiteSum (fun j => A i j * (x j + y j)) =
        finiteSum (fun j => A i j * x j + A i j * y j) := by
          congr 1
          funext j
          exact Rat.mul_add _ _ _
    _ = finiteSum (fun j => A i j * x j) +
        finiteSum (fun j => A i j * y j) :=
      finiteSum_add _ _

theorem matrixApply_vectorScale {dimension : Nat}
    (A : RatMatrix dimension) (r : Rat) (x : RatVector dimension) :
    matrixApply A (vectorScale r x) =
      vectorScale r (matrixApply A x) := by
  funext i
  unfold matrixApply vectorScale
  rw [show (fun j => A i j * (r * x j)) =
      (fun j => r * (A i j * x j)) by
        funext j
        grind [Rat.mul_assoc, Rat.mul_comm]]
  exact (finiteSum_mul_left r (fun j => A i j * x j)).symm

theorem matrixApply_matrixAdd {dimension : Nat}
    (A B : RatMatrix dimension) (x : RatVector dimension) :
    matrixApply (matrixAdd A B) x =
      vectorAdd (matrixApply A x) (matrixApply B x) := by
  funext i
  unfold matrixApply matrixAdd vectorAdd
  rw [show (fun j => (A i j + B i j) * x j) =
      (fun j => A i j * x j + B i j * x j) by
        funext j
        exact Rat.add_mul _ _ _]
  exact finiteSum_add _ _

theorem matrixApply_matrixScale {dimension : Nat}
    (A : RatMatrix dimension) (r : Rat) (x : RatVector dimension) :
    matrixApply (matrixScale r A) x =
      vectorScale r (matrixApply A x) := by
  funext i
  unfold matrixApply matrixScale vectorScale
  rw [show (fun j => (r * A i j) * x j) =
      (fun j => r * (A i j * x j)) by
        funext j
        exact Rat.mul_assoc _ _ _]
  exact (finiteSum_mul_left r (fun j => A i j * x j)).symm

/-- The identity matrix acts as the identity on a finite rational vector. -/
theorem matrixApply_identity {dimension : Nat} (x : RatVector dimension) :
    matrixApply (matrixIdentity dimension) x = x := by
  funext i
  unfold matrixApply matrixIdentity
  calc
    finiteSum (fun j => (if i = j then 1 else 0) * x j) =
        finiteSum (fun j => if j = i then x j else 0) := by
          congr 1
          funext j
          by_cases h : j = i
          · subst j
            simp
          · have h' : ¬ i = j := by
              intro hij
              exact h hij.symm
            simp [h, h']
    _ = x i :=
      finiteSum_ite_eq i x

/-- The finite matrix action of a forward Euler step is the state plus the
step-scaled coefficient action. -/
theorem matrixApply_eulerStep_decomposition {dimension : Nat}
    (A : RatMatrix dimension) (h : Rat) (x : RatVector dimension) :
    matrixApply (matrixAdd (matrixIdentity dimension) (matrixScale h A)) x =
      vectorAdd x (vectorScale h (matrixApply A x)) := by
  rw [matrixApply_matrixAdd, matrixApply_identity, matrixApply_matrixScale]

theorem matrixApply_vectorSub {dimension : Nat}
    (A : RatMatrix dimension) (x y : RatVector dimension) :
    matrixApply A (vectorSub x y) =
      vectorSub (matrixApply A x) (matrixApply A y) := by
  calc
    matrixApply A (vectorSub x y) =
        matrixApply A (vectorAdd x (vectorScale (-1) y)) := by
          congr 1
          funext i
          simp [vectorSub, vectorAdd, vectorScale, Rat.sub_eq_add_neg,
            Rat.neg_mul]
    _ = vectorAdd (matrixApply A x)
          (matrixApply A (vectorScale (-1) y)) :=
        matrixApply_vectorAdd A x (vectorScale (-1) y)
    _ = vectorAdd (matrixApply A x)
          (vectorScale (-1) (matrixApply A y)) := by
        rw [matrixApply_vectorScale]
    _ = vectorSub (matrixApply A x) (matrixApply A y) := by
      funext i
      simp [vectorAdd, vectorSub, vectorScale, Rat.sub_eq_add_neg,
        Rat.neg_mul]

/-- Coordinatewise Euler residual certificates induce a finite vector-norm
residual bound. The hypothesis is exactly the rational form produced by
`HasDerivativeOnInterval.lowerEndpoint_eulerResidual`. -/
theorem eulerResidual_vectorAbsSum_le {dimension : Nat}
    (A : RatMatrix dimension) (h : Rat)
    (x y : RatVector dimension) (bound : Fin dimension -> Rat)
    (hcomponent : forall i,
      -bound i <= y i - (x i + h * matrixApply A x i) /\
        y i - (x i + h * matrixApply A x i) <= bound i) :
    vectorAbsSum
      (vectorSub y
        (matrixApply (matrixAdd (matrixIdentity dimension)
          (matrixScale h A)) x)) <= finiteSum bound := by
  apply vectorAbsSum_le_of_component_bounds
  intro i
  apply qabs_le_of_bounds
  · simpa [vectorSub, matrixApply_eulerStep_decomposition,
      vectorAdd, vectorScale] using (hcomponent i).1
  · simpa [vectorSub, matrixApply_eulerStep_decomposition,
      vectorAdd, vectorScale] using (hcomponent i).2

/-- Norm bound for the affine Euler defect of `x' = A x + b`. The sampled
forcing is shared by compared trajectories; its value affects each Euler
step but does not enter the difference estimate. -/
theorem forcedEulerResidual_vectorAbsSum_le {dimension : Nat}
    (A : RatMatrix dimension) (h : Rat)
    (x y forcing : RatVector dimension) (bound : Fin dimension -> Rat)
    (hcomponent : forall i,
      -bound i <= y i - (x i + h * (matrixApply A x i + forcing i)) /\
        y i - (x i + h * (matrixApply A x i + forcing i)) <= bound i) :
    vectorAbsSum
      (vectorSub y
        (vectorAdd
          (matrixApply (matrixAdd (matrixIdentity dimension)
            (matrixScale h A)) x)
          (vectorScale h forcing))) <= finiteSum bound := by
  apply vectorAbsSum_le_of_component_bounds
  intro i
  apply qabs_le_of_bounds
  · simpa [vectorSub, vectorAdd, vectorScale,
      matrixApply_eulerStep_decomposition, Rat.mul_add,
      Rat.add_assoc, Rat.add_comm, Rat.add_left_comm] using (hcomponent i).1
  · simpa [vectorSub, vectorAdd, vectorScale,
      matrixApply_eulerStep_decomposition, Rat.mul_add,
      Rat.add_assoc, Rat.add_comm, Rat.add_left_comm] using (hcomponent i).2

/-- Lower-endpoint samples of one valid raw real computation are compatible
across arbitrary precision schedules. Both interval widths are the explicit
cost of comparing computations made at different stages; this is the mesh
alignment estimate needed when adjacent derivative certificates choose
different evaluator precisions at their shared rational endpoint. -/
theorem QInterval.lowerEndpoints_close_of_valid_compute
    (compute : Nat -> QInterval) (valid : RealCompute.ValidCompute compute)
    (m n : Nat) :
    qabs ((compute m).lo - (compute n).lo) <=
      (compute m).width + (compute n).width := by
  let k := max m n
  have hmk := valid.2.1 m k (Nat.le_max_left m n)
  have hnk := valid.2.1 n k (Nat.le_max_right m n)
  have hmn : (compute m).lo <= (compute n).hi :=
    Rat.le_trans hmk.1 (Rat.le_trans hmk.2.1 hnk.2.2)
  have hnm : (compute n).lo <= (compute m).hi :=
    Rat.le_trans hnk.1 (Rat.le_trans hnk.2.1 hmk.2.2)
  have hwm : 0 <= (compute m).width := valid.1 m
  have hwn : 0 <= (compute n).width := valid.1 n
  apply qabs_le_of_bounds
  · have h := hnm
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  · have h := hmn
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- Lower endpoint samples from two equivalent represented computations can
be compared across independent stages. A shared-stage overlap at `k`, plus
validity nesting, bounds their discrepancy by the sum of the two requested
stage widths. -/
theorem QInterval.lowerEndpoints_close_of_common_overlap
    (left right : Nat -> QInterval)
    (leftValid : RealCompute.ValidCompute left)
    (rightValid : RealCompute.ValidCompute right)
    (m n k : Nat) (hmk : m <= k) (hnk : n <= k)
    (hoverlap : (left k).lo <= (right k).hi /\
      (right k).lo <= (left k).hi) :
    qabs ((left m).lo - (right n).lo) <=
      (left m).width + (right n).width := by
  have hleft := leftValid.2.1 m k hmk
  have hright := rightValid.2.1 n k hnk
  have hforward : (left m).lo <= (right n).hi :=
    Rat.le_trans hleft.1 (Rat.le_trans hoverlap.1 hright.2.2)
  have hbackward : (right n).lo <= (left m).hi :=
    Rat.le_trans hright.1 (Rat.le_trans hoverlap.2 hleft.2.2)
  have hleftWidth : 0 <= (left m).width := leftValid.1 m
  have hrightWidth : 0 <= (right n).width := rightValid.1 n
  apply qabs_le_of_bounds
  · have h := hbackward
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  · have h := hforward
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- Equivalent valid raw reals have lower endpoint samples that are close at
arbitrary (possibly different) evaluator stages. This supplies the rational
initial-discrepancy bound for comparing two represented ODE solutions whose
initial raw values are equivalent. -/
theorem RealCompute.lowerEndpoints_close_of_equiv
    (x y : RealCompute) (xvalid : RealCompute.ValidCompute x.compute)
    (yvalid : RealCompute.ValidCompute y.compute)
    (m n k : Nat) (hmk : m <= k) (hnk : n <= k)
    (hequiv : x.Equiv y) :
    qabs ((x.compute m).lo - (y.compute n).lo) <=
      (x.compute m).width + (y.compute n).width := by
  apply QInterval.lowerEndpoints_close_of_common_overlap
    x.compute y.compute xvalid yvalid m n k hmk hnk
  exact (RealCompute.compareAt_overlap_iff x y k k).1 (hequiv k)

/-- The previous alignment estimate specialized to the public evaluator of a
represented function on its declared rational domain. -/
theorem FunctionOnInterval.lowerComputeEndpoints_close
    (f : FunctionOnInterval) (x : Rat)
    (hx : inDomainInterval f.lower f.upper x) (m n : Nat) :
    qabs ((f.compute x hx m).lo - (f.compute x hx n).lo) <=
      (f.compute x hx m).width + (f.compute x hx n).width := by
  exact QInterval.lowerEndpoints_close_of_valid_compute
    (f.compute x hx) (f.valid_on x (f.defined_on x hx)) m n

/-- The evaluator validity proof supplies a computable tail stage after
which every requested value box at a fixed rational input has width at most
the given positive rational tolerance. -/
theorem FunctionOnInterval.compute_width_eventually_small
    (f : FunctionOnInterval) (x : Rat)
    (hx : inDomainInterval f.lower f.upper x) (eps : QPos) :
    exists N, forall n, N <= n -> (f.compute x hx n).width <= eps.val := by
  exact (f.valid_on x (f.defined_on x hx)).2.2 eps

/-- Two evaluator schedules at one rational input agree to twice a chosen
width tolerance as soon as both stages pass the validity modulus. -/
theorem FunctionOnInterval.lowerComputeEndpoints_close_after
    (f : FunctionOnInterval) (x : Rat)
    (hx : inDomainInterval f.lower f.upper x) (eps : QPos)
    (m n : Nat)
    (hsmall : forall k, m <= k -> (f.compute x hx k).width <= eps.val)
    (hlarge : forall k, n <= k -> (f.compute x hx k).width <= eps.val) :
    qabs ((f.compute x hx m).lo - (f.compute x hx n).lo) <=
      eps.val + eps.val := by
  calc
    qabs ((f.compute x hx m).lo - (f.compute x hx n).lo) <=
        (f.compute x hx m).width + (f.compute x hx n).width :=
      FunctionOnInterval.lowerComputeEndpoints_close f x hx m n
    _ <= eps.val + eps.val :=
      rat_add_le_add (hsmall m (Nat.le_refl m))
        (hlarge n (Nat.le_refl n))

/-- Reconcile a one-cell Euler estimate with independently chosen precision
schedules at its two mesh endpoints. The start and end schedule changes are
added explicitly to the derivative residual, so adjacent cells need not use
the same evaluator stage. -/
theorem qabs_euler_residual_across_schedules
    {currentSample currentCell nextCell nextSample h center : Rat}
    {startError cellError endError : Rat}
    (hstart : qabs (currentCell - currentSample) <= startError)
    (hcell : qabs (nextCell - (currentCell + h * center)) <= cellError)
    (hend : qabs (nextSample - nextCell) <= endError) :
    qabs (nextSample - (currentSample + h * center)) <=
      endError + cellError + startError := by
  have hmiddle :
      qabs (nextCell - (currentSample + h * center)) <=
        cellError + startError := by
    have hshift :
        qabs ((currentCell + h * center) - (currentSample + h * center)) <=
          startError := by
      have hcancel :
          (currentCell + h * center) - (currentSample + h * center) =
            currentCell - currentSample := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      rw [hcancel]
      exact hstart
    exact qabs_sub_le_add_of_intermediate hcell hshift
  calc
    qabs (nextSample - (currentSample + h * center)) <=
        endError + (cellError + startError) :=
      qabs_sub_le_add_of_intermediate hend hmiddle
    _ = endError + cellError + startError := (Rat.add_assoc _ _ _).symm

/-- Matrix action respects the project-local finite matrix product.  This is
the finite reassociation used to turn a homogeneous recurrence into one
chronological transition matrix. -/
theorem matrixApply_matrixMul {dimension : Nat}
    (A B : RatMatrix dimension) (x : RatVector dimension) :
    matrixApply (matrixMul A B) x =
      matrixApply A (matrixApply B x) := by
  funext i
  unfold matrixApply matrixMul
  calc
    finiteSum (fun j => finiteSum (fun k => A i k * B k j) * x j) =
        finiteSum (fun j => finiteSum (fun k => (A i k * B k j) * x j)) := by
          congr 1
          funext j
          rw [finiteSum_mul_right]
    _ = finiteSum (fun k => finiteSum (fun j => (A i k * B k j) * x j)) :=
      finiteSum_swap dimension dimension
        (fun j k => (A i k * B k j) * x j)
    _ = finiteSum (fun k => A i k * finiteSum (fun j => B k j * x j)) := by
          congr 1
          funext k
          calc
            finiteSum (fun j => (A i k * B k j) * x j) =
                finiteSum (fun j => A i k * (B k j * x j)) := by
                  congr 1
                  funext j
                  exact Rat.mul_assoc _ _ _
            _ = A i k * finiteSum (fun j => B k j * x j) :=
              (finiteSum_mul_left (A i k) (fun j => B k j * x j)).symm

theorem matrixAdd_zero_left {dimension : Nat} (A : RatMatrix dimension) :
    matrixAdd (matrixZero dimension) A = A := by
  funext i j
  exact Rat.zero_add _

theorem matrixAdd_zero_right {dimension : Nat} (A : RatMatrix dimension) :
    matrixAdd A (matrixZero dimension) = A := by
  funext i j
  exact Rat.add_zero _

theorem matrixAdd_assoc {dimension : Nat} (A B C : RatMatrix dimension) :
    matrixAdd (matrixAdd A B) C = matrixAdd A (matrixAdd B C) := by
  funext i j
  exact Rat.add_assoc _ _ _

/-- Regroup four finite matrix summands into their first-and-third and
second-and-fourth pairs. -/
theorem matrixAdd_group_even_odd {dimension : Nat}
    (A B C D : RatMatrix dimension) :
    matrixAdd (matrixAdd (matrixAdd A B) C) D =
      matrixAdd (matrixAdd A C) (matrixAdd B D) := by
  funext i j
  change ((A i j + B i j) + C i j) + D i j =
    (A i j + C i j) + (B i j + D i j)
  ac_rfl

theorem matrixMul_zero_right {dimension : Nat} (A : RatMatrix dimension) :
    matrixMul A (matrixZero dimension) = matrixZero dimension := by
  funext i j
  unfold matrixMul matrixZero
  rw [show (fun k => A i k * 0) = (fun _ => 0) by
    funext k
    exact Rat.mul_zero _]
  exact finiteSum_zero dimension

theorem matrixMul_add_left {dimension : Nat} (A B C : RatMatrix dimension) :
    matrixMul (matrixAdd A B) C = matrixAdd (matrixMul A C) (matrixMul B C) := by
  funext i j
  unfold matrixMul matrixAdd
  calc
    finiteSum (fun k => (A i k + B i k) * C k j) =
        finiteSum (fun k => A i k * C k j + B i k * C k j) := by
          congr 1
          funext k
          exact Rat.add_mul _ _ _
    _ = finiteSum (fun k => A i k * C k j) +
        finiteSum (fun k => B i k * C k j) :=
          finiteSum_add _ _

theorem matrixMul_add_right {dimension : Nat} (A B C : RatMatrix dimension) :
    matrixMul A (matrixAdd B C) = matrixAdd (matrixMul A B) (matrixMul A C) := by
  funext i j
  unfold matrixMul matrixAdd
  calc
    finiteSum (fun k => A i k * (B k j + C k j)) =
        finiteSum (fun k => A i k * B k j + A i k * C k j) := by
          congr 1
          funext k
          exact Rat.mul_add _ _ _
    _ = finiteSum (fun k => A i k * B k j) +
        finiteSum (fun k => A i k * C k j) :=
          finiteSum_add _ _

theorem finiteSum_ite_eq_left {dimension : Nat} (j : Fin dimension)
    (f : Fin dimension -> Rat) :
    finiteSum (fun i => if j = i then f i else 0) = f j := by
  calc
    finiteSum (fun i => if j = i then f i else 0) =
        finiteSum (fun i => if i = j then f i else 0) := by
          congr 1
          funext i
          split
          · rename_i h
            have h' : i = j := h.symm
            exact (if_pos h').symm
          · rename_i h
            have h' : ¬ i = j := by
              intro h'
              exact h h'.symm
            exact (if_neg h').symm
    _ = f j := finiteSum_ite_eq j f

theorem matrixMul_identity_left {dimension : Nat} (A : RatMatrix dimension) :
    matrixMul (matrixIdentity dimension) A = A := by
  funext i j
  unfold matrixMul matrixIdentity
  calc
    finiteSum (fun k => (if i = k then 1 else 0) * A k j) =
        finiteSum (fun k => if i = k then A k j else 0) := by
          congr 1
          funext k
          split
          · rename_i h
            exact Rat.one_mul _
          · rename_i h
            exact Rat.zero_mul _
    _ = A i j := finiteSum_ite_eq_left i (fun k => A k j)

theorem matrixMul_identity_right {dimension : Nat} (A : RatMatrix dimension) :
    matrixMul A (matrixIdentity dimension) = A := by
  funext i j
  unfold matrixMul matrixIdentity
  calc
    finiteSum (fun k => A i k * (if k = j then 1 else 0)) =
        finiteSum (fun k => if k = j then A i k else 0) := by
          congr 1
          funext k
          split
          · rename_i h
            exact Rat.mul_one _
          · rename_i h
            exact Rat.mul_zero _
    _ = A i j := finiteSum_ite_eq j (fun k => A i k)

theorem matrixMul_zero_left {dimension : Nat} (A : RatMatrix dimension) :
    matrixMul (matrixZero dimension) A = matrixZero dimension := by
  funext i j
  unfold matrixMul matrixZero
  rw [show (fun k => 0 * A k j) = (fun _ => 0) by
    funext k
    exact Rat.zero_mul _]
  exact finiteSum_zero dimension

/-- The exact transition matrix of a sampled linear recurrence, starting at a
given index and taking a prescribed number of chronological updates.  The
newest sample occurs on the left, so this convention agrees with the
Peano--Baker word order. -/
def chronologicalStepProduct {dimension : Nat} (S : Nat -> RatMatrix dimension)
    (start : Nat) : Nat -> RatMatrix dimension
  | 0 => matrixIdentity dimension
  | steps + 1 =>
      matrixMul (S (start + steps))
        (chronologicalStepProduct S start steps)

@[simp] theorem chronologicalStepProduct_zero {dimension : Nat}
    (S : Nat -> RatMatrix dimension) (start : Nat) :
    chronologicalStepProduct S start 0 = matrixIdentity dimension := rfl

@[simp] theorem chronologicalStepProduct_succ {dimension : Nat}
    (S : Nat -> RatMatrix dimension) (start steps : Nat) :
    chronologicalStepProduct S start (steps + 1) =
      matrixMul (S (start + steps))
        (chronologicalStepProduct S start steps) := rfl

/-- Exact composition of time-shifted sampled transitions.  The transition
over the later block occurs on the left, as required by chronological time
ordering.  This is the finite semigroup law behind the future continuous
identity `Phi(t,r) * Phi(r,s) = Phi(t,s)`. -/
theorem chronologicalStepProduct_split {dimension : Nat}
    (S : Nat -> RatMatrix dimension) (start first second : Nat) :
    chronologicalStepProduct S start (first + second) =
      matrixMul
        (chronologicalStepProduct S (start + first) second)
        (chronologicalStepProduct S start first) := by
  induction second with
  | zero =>
      change chronologicalStepProduct S start first =
        matrixMul (matrixIdentity dimension) (chronologicalStepProduct S start first)
      exact (matrixMul_identity_left _).symm
  | succ second ih =>
      rw [show first + (second + 1) = (first + second) + 1 by omega]
      rw [chronologicalStepProduct_succ, ih]
      change
        matrixMul (S (start + (first + second)))
          (matrixMul (chronologicalStepProduct S (start + first) second)
            (chronologicalStepProduct S start first)) =
          matrixMul
            (matrixMul (S ((start + first) + second))
              (chronologicalStepProduct S (start + first) second))
            (chronologicalStepProduct S start first)
      rw [show start + (first + second) = (start + first) + second by omega]
      exact (matrixMul_assoc _ _ _).symm

/-- A sampled, possibly inhomogeneous, linear recurrence
`x_(k+1) = step(k) * x_k + forcing(k)`.  For an Euler discretization of
`x' = A(t)x+b(t)`, use `step(k) = I + h A(t_k)` and
`forcing(k) = h b(t_k)`. -/
structure DiscreteLinearSystem (dimension : Nat) where
  step : Nat -> RatMatrix dimension
  forcing : Nat -> RatVector dimension

namespace DiscreteLinearSystem

def trajectory (system : DiscreteLinearSystem dimension) (initial : RatVector dimension) :
    Nat -> RatVector dimension
  | 0 => initial
  | n + 1 => vectorAdd
      (matrixApply (system.step n) (trajectory system initial n))
      (system.forcing n)

theorem trajectory_zero (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) :
    system.trajectory initial 0 = initial := rfl

theorem trajectory_succ (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) (n : Nat) :
    system.trajectory initial (n + 1) =
      vectorAdd (matrixApply (system.step n) (system.trajectory initial n))
        (system.forcing n) := rfl

/-- The homogeneous part of a sampled linear system, retaining the literal
time order of the successive matrix actions. -/
def homogeneousTrajectory (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) : Nat -> RatVector dimension
  | 0 => initial
  | n + 1 => matrixApply (system.step n)
      (homogeneousTrajectory system initial n)

theorem homogeneousTrajectory_zero (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) :
    system.homogeneousTrajectory initial 0 = initial := rfl

theorem homogeneousTrajectory_succ (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) (n : Nat) :
    system.homogeneousTrajectory initial (n + 1) =
      matrixApply (system.step n) (system.homogeneousTrajectory initial n) := rfl

/-! The finite homogeneous trajectory already has the linearity expected of
the solution operator.  This is an induction over sampled matrix updates, not
an appeal to a completed vector-valued function space. -/
theorem homogeneousTrajectory_vectorAdd
    (system : DiscreteLinearSystem dimension)
    (x y : RatVector dimension) :
    forall n,
      system.homogeneousTrajectory (vectorAdd x y) n =
        vectorAdd (system.homogeneousTrajectory x n)
          (system.homogeneousTrajectory y n)
  | 0 => rfl
  | n + 1 => by
      rw [homogeneousTrajectory_succ, homogeneousTrajectory_succ,
        homogeneousTrajectory_succ,
        homogeneousTrajectory_vectorAdd system x y n,
        matrixApply_vectorAdd]

theorem homogeneousTrajectory_vectorScale
    (system : DiscreteLinearSystem dimension)
    (r : Rat) (x : RatVector dimension) :
    forall n,
      system.homogeneousTrajectory (vectorScale r x) n =
        vectorScale r (system.homogeneousTrajectory x n)
  | 0 => rfl
  | n + 1 => by
      rw [homogeneousTrajectory_succ, homogeneousTrajectory_succ,
        homogeneousTrajectory_vectorScale system r x n,
        matrixApply_vectorScale]

/-- A candidate solution of the sampled inhomogeneous recurrence.  Stating the
recurrence separately from the recursive evaluator makes finite uniqueness a
checked theorem rather than a property of one chosen implementation. -/
structure SolvesRecurrence (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) (candidate : Nat -> RatVector dimension) : Prop where
  initial_eq : candidate 0 = initial
  step_eq : forall n,
    candidate (n + 1) =
      vectorAdd (matrixApply (system.step n) (candidate n))
        (system.forcing n)

/-- A candidate solution of the homogeneous sampled recurrence.  This is the
finite rational core of the zero-initial uniqueness argument used later for
linear Peano--Baker systems. -/
structure SolvesHomogeneousRecurrence (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) (candidate : Nat -> RatVector dimension) : Prop where
  initial_eq : candidate 0 = initial
  step_eq : forall n,
    candidate (n + 1) =
      matrixApply (system.step n) (candidate n)

/-- The recursive evaluator is a solution of its sampled recurrence. -/
theorem trajectory_solvesRecurrence
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension) :
    system.SolvesRecurrence initial (system.trajectory initial) :=
  { initial_eq := rfl
    step_eq := fun _ => rfl }

/-- The recursive homogeneous evaluator is a solution of the homogeneous
sampled recurrence. -/
theorem homogeneousTrajectory_solvesHomogeneousRecurrence
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension) :
    system.SolvesHomogeneousRecurrence initial
      (system.homogeneousTrajectory initial) :=
  { initial_eq := rfl
    step_eq := fun _ => rfl }

/-- Finite uniqueness for a sampled inhomogeneous linear system.  The proof is
induction over a finite list of rational matrix updates; it invokes neither a
limit nor an inverse transition matrix. -/
theorem solvesRecurrence_eq_trajectory
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension)
    (candidate : Nat -> RatVector dimension)
    (hsolution : system.SolvesRecurrence initial candidate) :
    forall n, candidate n = system.trajectory initial n
  | 0 => hsolution.initial_eq
  | n + 1 => by
      rw [hsolution.step_eq n, trajectory_succ,
        solvesRecurrence_eq_trajectory system initial candidate hsolution n]

/-- Finite uniqueness for the homogeneous sampled recurrence. -/
theorem solvesHomogeneousRecurrence_eq_homogeneousTrajectory
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension)
    (candidate : Nat -> RatVector dimension)
    (hsolution : system.SolvesHomogeneousRecurrence initial candidate) :
    forall n, candidate n = system.homogeneousTrajectory initial n
  | 0 => hsolution.initial_eq
  | n + 1 => by
      rw [hsolution.step_eq n, homogeneousTrajectory_succ,
        solvesHomogeneousRecurrence_eq_homogeneousTrajectory
          system initial candidate hsolution n]

/-- The exact zero-initial homogeneous uniqueness certificate.  This is the
finite form of the comparison step for two candidate continuous solutions:
their difference has zero initial data, and a later enclosure argument must
pass this finite conclusion through refining sampled systems. -/
theorem solvesHomogeneousRecurrence_zero
    (system : DiscreteLinearSystem dimension) (candidate : Nat -> RatVector dimension)
    (hsolution : system.SolvesHomogeneousRecurrence
      (vectorZero dimension) candidate) :
    forall n, candidate n = vectorZero dimension
  | 0 => hsolution.initial_eq
  | n + 1 => by
      rw [hsolution.step_eq n,
        solvesHomogeneousRecurrence_zero system candidate hsolution n,
        matrixApply_zero]

/-- Explicit scalar error envelope for a finite perturbed Euler recurrence.
The growth factor bounds the homogeneous update on one mesh cell and each
residual records the certified derivative/evaluation error on that cell. -/
def eulerErrorEnvelope (growth initial : Rat) (residual : Nat -> Rat) :
    Nat -> Rat
  | 0 => initial
  | n + 1 => growth * eulerErrorEnvelope growth initial residual n + residual n

/-- Finite geometric sum used to make the accumulated mesh residual
explicit. -/
def geometricWeightSum (growth : Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => growth * geometricWeightSum growth n + 1

/-- A rational maximum used for finite mesh envelopes. -/
def ratMax (a b : Rat) : Rat := if a <= b then b else a

theorem rat_le_max_left (a b : Rat) : a <= ratMax a b := by
  unfold ratMax
  split
  · assumption
  · exact Rat.le_refl

theorem rat_le_max_right (a b : Rat) : b <= ratMax a b := by
  unfold ratMax
  split
  · exact Rat.le_refl
  · have htotal : a <= b \/ b <= a := Rat.le_total
    grind

theorem ratMax_le {a b c : Rat} (ha : a <= c) (hb : b <= c) :
    ratMax a b <= c := by
  unfold ratMax
  split
  · exact hb
  · exact ha

/-- Maximum value of a rational sequence on the finite prefix `0,...,n`. -/
def sequenceMaxUpTo (f : Nat -> Rat) : Nat -> Rat
  | 0 => f 0
  | n + 1 => ratMax (sequenceMaxUpTo f n) (f (n + 1))

theorem sequenceMaxUpTo_ge {f : Nat -> Rat} :
    forall n k, k <= n -> f k <= sequenceMaxUpTo f n
  | 0, 0, _ => Rat.le_refl
  | 0, k + 1, h => by omega
  | n + 1, 0, _ =>
      Rat.le_trans (sequenceMaxUpTo_ge (f := f) n 0 (by omega))
        (rat_le_max_left _ _)
  | n + 1, k + 1, hk => by
      by_cases hkn : k + 1 <= n
      · exact Rat.le_trans (sequenceMaxUpTo_ge (f := f) n (k + 1) hkn)
          (rat_le_max_left _ _)
      · have heq : k + 1 = n + 1 := by omega
        have hk : k = n := by omega
        subst k
        exact rat_le_max_right _ _

theorem sequenceMaxUpTo_le_of_all {f : Nat -> Rat} :
    forall n bound, (forall k, k <= n -> f k <= bound) ->
      sequenceMaxUpTo f n <= bound
  | 0, bound, h => h 0 (Nat.le_refl _)
  | n + 1, bound, h => by
      apply ratMax_le
      · exact sequenceMaxUpTo_le_of_all n bound
          (fun k hk => h k (by omega))
      · exact h (n + 1) (Nat.le_refl _)

/-- Finite short-block Gronwall estimate for rational mesh errors. If the
total coefficient contribution is at most one half, the largest endpoint
discrepancy is bounded by twice the total residual budget. This avoids a
real exponential bound and is the key local estimate for constructive ODE
uniqueness. -/
theorem finite_mesh_error_short_block_with_initial
    (error : Nat -> Rat) (cells : Nat) (coefficient residual initial : Rat)
    (hcoefficient : 0 <= coefficient) (hresidual : 0 <= residual)
    (hinitial : error 0 <= initial)
    (hnonneg : forall n, n <= cells -> 0 <= error n)
    (hstep : forall n, n < cells ->
      error (n + 1) <= (1 + coefficient) * error n + residual)
    (hshort : (cells : Rat) * coefficient <= (1 : Rat) / 2) :
    error cells <= 2 * (initial + (cells : Rat) * residual) := by
  let maximum := sequenceMaxUpTo error cells
  have hmaximum_nonneg : 0 <= maximum := by
    have hmax := sequenceMaxUpTo_ge (f := error) cells 0 (by omega)
    exact Rat.le_trans (hnonneg 0 (by omega)) hmax
  have hlinear : forall n, n <= cells ->
      error n <= initial + (n : Rat) * (coefficient * maximum + residual) := by
    intro n hn
    induction n with
    | zero =>
        simpa [Rat.add_zero] using hinitial
    | succ n ih =>
        have hnlt : n < cells := by omega
        have hem : error n <= maximum :=
          sequenceMaxUpTo_ge (f := error) cells n (by omega)
        have hcoef := Rat.mul_le_mul_of_nonneg_left hem hcoefficient
        have hstepn := hstep n hnlt
        calc
          error (n + 1) <= (1 + coefficient) * error n + residual := hstepn
          _ = error n + coefficient * error n + residual := by
            rw [Rat.add_mul, Rat.one_mul]
          _ <= (initial + (n : Rat) * (coefficient * maximum + residual)) +
              coefficient * maximum + residual := by
            have hsum := rat_add_le_add (ih (by omega)) hcoef
            exact rat_add_le_add hsum Rat.le_refl
          _ = initial + ((n + 1 : Nat) : Rat) *
              (coefficient * maximum + residual) := by
            rw [Rat.natCast_add]
            grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
              Rat.add_left_comm, Rat.mul_assoc, Rat.mul_comm]
  have hall : forall n, n <= cells ->
      error n <= initial + (cells : Rat) * (coefficient * maximum + residual) := by
    intro n hn
    apply Rat.le_trans (hlinear n hn)
    apply (Rat.add_le_add_left (c := initial)).2
    exact Rat.mul_le_mul_of_nonneg_right
      (by exact_mod_cast hn)
      (Rat.add_nonneg (Rat.mul_nonneg hcoefficient hmaximum_nonneg) hresidual)
  have hmaxle := sequenceMaxUpTo_le_of_all (f := error) cells
    (initial + (cells : Rat) * (coefficient * maximum + residual)) hall
  have hcoefbound : (cells : Rat) * coefficient * maximum <=
      (1 / 2 : Rat) * maximum :=
    Rat.mul_le_mul_of_nonneg_right hshort hmaximum_nonneg
  have hmaxineq : maximum <= initial +
      (cells : Rat) * coefficient * maximum + (cells : Rat) * residual := by
    simpa [Rat.mul_add, Rat.mul_assoc, Rat.add_assoc] using hmaxle
  have hhalf : maximum <= initial + (1 / 2 : Rat) * maximum +
      (cells : Rat) * residual := by
    calc
      maximum <= initial + (cells : Rat) * coefficient * maximum +
          (cells : Rat) * residual := hmaxineq
      _ <= initial + (1 / 2 : Rat) * maximum +
          (cells : Rat) * residual :=
        rat_add_le_add (rat_add_le_add Rat.le_refl hcoefbound) Rat.le_refl
  have htwice := Rat.mul_le_mul_of_nonneg_left hhalf
    (by decide : (0 : Rat) <= 2)
  have hbudget : maximum <= 2 * (initial + (cells : Rat) * residual) := by
    rw [Rat.mul_add] at htwice
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
      Rat.add_mul, Rat.add_assoc, Rat.add_comm, Rat.sub_eq_add_neg]
  exact Rat.le_trans
    (sequenceMaxUpTo_ge (f := error) cells cells (Nat.le_refl _)) hbudget

/-- Short-block estimate specialized to the explicit ODE error envelope.
When `cells * coefficient ≤ 1/2`, a nonnegative initial discrepancy and
stage-dependent residuals bounded by `residual` yield the linear bound
`2 * (initial + cells * residual)`, avoiding a power of the Euler growth
factor. -/
theorem eulerErrorEnvelope_short_block_with_initial
    (coefficient initial residual : Rat) (cells : Nat)
    (varying : Nat -> Rat)
    (hcoefficient : 0 <= coefficient)
    (hinitial : 0 <= initial)
    (hresidual : 0 <= residual)
    (hvarying_nonneg : forall n, n < cells -> 0 <= varying n)
    (hvarying_le : forall n, n < cells -> varying n <= residual)
    (hshort : (cells : Rat) * coefficient <= (1 : Rat) / 2) :
    eulerErrorEnvelope (1 + coefficient) initial varying cells <=
      2 * (initial + (cells : Rat) * residual) := by
  have hgrowth : 0 <= 1 + coefficient := Rat.add_nonneg
    (by decide) hcoefficient
  have herrorNonneg : forall n, n <= cells ->
      0 <= eulerErrorEnvelope (1 + coefficient) initial varying n := by
    intro n hn
    induction n with
    | zero =>
        change 0 <= initial
        exact hinitial
    | succ n ih =>
        have hnlt : n < cells := by omega
        rw [eulerErrorEnvelope]
        exact Rat.add_nonneg
          (Rat.mul_nonneg hgrowth (ih (by omega)))
          (hvarying_nonneg n hnlt)
  have hstep : forall n, n < cells ->
      eulerErrorEnvelope (1 + coefficient) initial varying (n + 1) <=
        (1 + coefficient) *
          eulerErrorEnvelope (1 + coefficient) initial varying n + residual := by
    intro n hn
    rw [eulerErrorEnvelope]
    have hvar := hvarying_le n hn
    exact (Rat.add_le_add_left
      (c := (1 + coefficient) *
        eulerErrorEnvelope (1 + coefficient) initial varying n)).2 hvar
  exact finite_mesh_error_short_block_with_initial
    (fun n => eulerErrorEnvelope (1 + coefficient) initial varying n)
    cells coefficient residual initial hcoefficient hresidual
    (by rw [eulerErrorEnvelope]; exact Rat.le_refl)
    herrorNonneg hstep hshort

/-- A short-block error bound expressed using a per-unit local defect. If
each residual is at most `step * defect` and the block length is at most
`length`, the endpoint error is at most `2 * (initial + length * defect)`.
Thus driving the initial discrepancy and local defect to zero is sufficient
for exact represented-value comparison on that block. -/
theorem eulerErrorEnvelope_short_block_scaled_defect
    {coefficient initial step defect length : Rat} (cells : Nat)
    (varying : Nat -> Rat)
    (hcoefficient : 0 <= coefficient)
    (hinitial : 0 <= initial)
    (hstep : 0 <= step)
    (hdefect : 0 <= defect)
    (htotal : (cells : Rat) * step <= length)
    (hvarying_nonneg : forall n, n < cells -> 0 <= varying n)
    (hvarying_le : forall n, n < cells -> varying n <= step * defect)
    (hshort : (cells : Rat) * coefficient <= (1 : Rat) / 2) :
    eulerErrorEnvelope (1 + coefficient) initial varying cells <=
      2 * (initial + length * defect) := by
  have hresidual : 0 <= step * defect := Rat.mul_nonneg hstep hdefect
  have hlocal := eulerErrorEnvelope_short_block_with_initial
    coefficient initial (step * defect) cells varying hcoefficient hinitial
    hresidual hvarying_nonneg hvarying_le hshort
  have htotalDefect : (cells : Rat) * (step * defect) <= length * defect := by
    calc
      (cells : Rat) * (step * defect) = ((cells : Rat) * step) * defect := by
        exact (Rat.mul_assoc _ _ _).symm
      _ <= length * defect := Rat.mul_le_mul_of_nonneg_right htotal hdefect
  calc
    eulerErrorEnvelope (1 + coefficient) initial varying cells <=
        2 * (initial + (cells : Rat) * (step * defect)) := hlocal
    _ <= 2 * (initial + length * defect) :=
      Rat.mul_le_mul_of_nonneg_left
        ((Rat.add_le_add_left (c := initial)).2 htotalDefect)
        (by decide : (0 : Rat) <= (2 : Rat))

/-- Transfer the explicit short-block envelope bound to any finite vector
comparison already controlled by that envelope. In particular, this composes
directly with `linearODE_solution_mesh_compare` after its coefficient and
residual data have been bounded on a short rational block. -/
theorem vectorDifference_le_short_block_of_eulerEnvelope
    {dimension : Nat} (left right : RatVector dimension)
    (coefficient initial residual : Rat) (cells : Nat)
    (varying : Nat -> Rat)
    (hcoefficient : 0 <= coefficient)
    (hinitial : 0 <= initial)
    (hresidual : 0 <= residual)
    (hvarying_nonneg : forall n, n < cells -> 0 <= varying n)
    (hvarying_le : forall n, n < cells -> varying n <= residual)
    (hshort : (cells : Rat) * coefficient <= (1 : Rat) / 2)
    (hcompare : vectorAbsSum (vectorSub left right) <=
      eulerErrorEnvelope (1 + coefficient) initial varying cells) :
    vectorAbsSum (vectorSub left right) <=
      2 * (initial + (cells : Rat) * residual) :=
  Rat.le_trans hcompare
    (eulerErrorEnvelope_short_block_with_initial coefficient initial residual
      cells varying hcoefficient hinitial hresidual hvarying_nonneg hvarying_le
      hshort)

/-- Zero-initial specialization of the short-block finite mesh estimate. -/
theorem finite_mesh_error_short_block
    (error : Nat -> Rat) (cells : Nat) (coefficient residual : Rat)
    (hcoefficient : 0 <= coefficient) (hresidual : 0 <= residual)
    (hinitial : error 0 = 0)
    (hnonneg : forall n, n <= cells -> 0 <= error n)
    (hstep : forall n, n < cells ->
      error (n + 1) <= (1 + coefficient) * error n + residual)
    (hshort : (cells : Rat) * coefficient <= (1 : Rat) / 2) :
    error cells <= 2 * ((cells : Rat) * residual) := by
  have h := finite_mesh_error_short_block_with_initial error cells
    coefficient residual 0 hcoefficient hresidual
    (by rw [hinitial]; exact Rat.le_refl) hnonneg hstep hshort
  simpa [Rat.zero_add] using h

/-- A growth factor at least one has a finite geometric weight no larger
than the number of cells times its largest power.  This deliberately keeps
the bound elementary and rational: callers can combine it with any
effective estimate on `growth ^ cells`, without invoking an analytic
exponential or a real-number limit. -/
theorem geometricWeightSum_le_cells_mul_pow {growth : Rat}
    (hgrowth : 1 <= growth) :
    forall cells,
      geometricWeightSum growth cells <=
        (cells : Rat) * growth ^ cells
  | 0 => by
      simp [geometricWeightSum]
  | cells + 1 => by
      rw [geometricWeightSum, Rat.natCast_add]
      have hpow : 1 <= growth ^ (cells + 1) := by
        induction cells with
        | zero => simpa using hgrowth
        | succ cells ih =>
            rw [Rat.pow_succ]
            have hgrowth_nonneg : 0 <= growth :=
              Rat.le_trans (by decide : (0 : Rat) <= 1) hgrowth
            calc
              1 <= growth := hgrowth
              _ = 1 * growth := (Rat.one_mul _).symm
              _ <= growth ^ (cells + 1) * growth :=
                Rat.mul_le_mul_of_nonneg_right ih hgrowth_nonneg
      have hgrowth_nonneg : 0 <= growth :=
        Rat.le_trans (by decide : (0 : Rat) <= 1) hgrowth
      have hmul := Rat.mul_le_mul_of_nonneg_left
        (geometricWeightSum_le_cells_mul_pow hgrowth cells) hgrowth_nonneg
      calc
        growth * geometricWeightSum growth cells + 1 <=
            growth * ((cells : Rat) * growth ^ cells) + growth ^ (cells + 1) :=
          rat_add_le_add hmul hpow
        _ = ((cells : Rat) + 1) * growth ^ (cells + 1) := by
          rw [Rat.pow_succ]
          grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
            Rat.add_left_comm, Rat.mul_assoc, Rat.mul_comm]

/-- With a constant per-cell residual, the error envelope is the initial
error transported through all cells plus the finite geometric sum of
transported residuals. -/
theorem eulerErrorEnvelope_const_residual
    (growth initial residual : Rat) :
    forall n,
      eulerErrorEnvelope growth initial (fun _ => residual) n =
        growth ^ n * initial + residual * geometricWeightSum growth n
  | 0 => by
      simp [eulerErrorEnvelope, geometricWeightSum, Rat.add_zero]
  | n + 1 => by
      rw [eulerErrorEnvelope, eulerErrorEnvelope_const_residual,
        geometricWeightSum]
      rw [Rat.pow_succ]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
        Rat.add_assoc]

/-- Dominate a stage-dependent residual sequence by one uniform rational
budget. This isolates the precision-schedule work from the finite recurrence:
once every local defect is at most `residual`, the comparison envelope is
bounded by the constant-residual closed form. -/
theorem eulerErrorEnvelope_le_const_residual
    {growth initial residual : Rat} (cells : Nat)
    (varying : Nat -> Rat)
    (hgrowth : 0 <= growth)
    (hvarying : forall n, n < cells -> varying n <= residual) :
    eulerErrorEnvelope growth initial varying cells <=
      growth ^ cells * initial + residual * geometricWeightSum growth cells := by
  induction cells with
  | zero =>
      change initial <= growth ^ 0 * initial + residual * 0
      simp only [Rat.pow_zero, Rat.one_mul, Rat.mul_zero, Rat.add_zero]
      exact Rat.le_refl
  | succ cells ih =>
      rw [eulerErrorEnvelope]
      have hprefix := ih (fun n hn =>
        hvarying n (Nat.lt_trans hn (Nat.lt_succ_self cells)))
      have hcell := hvarying cells (Nat.lt_succ_self cells)
      have hscaled := Rat.mul_le_mul_of_nonneg_left hprefix hgrowth
      calc
        growth * eulerErrorEnvelope growth initial varying cells + varying cells <=
            growth * (growth ^ cells * initial +
              residual * geometricWeightSum growth cells) + residual :=
          rat_add_le_add hscaled hcell
        _ = growth ^ (cells + 1) * initial +
            residual * geometricWeightSum growth (cells + 1) := by
          rw [Rat.pow_succ, geometricWeightSum]
          grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
            Rat.add_assoc, Rat.add_comm]

/-- A convenient growth-majorant form of the varying-residual estimate.
For `growth ≥ 1`, each unit-weight term is bounded by `growth^cells`, so the
entire mesh error is controlled by the initial discrepancy plus `cells`
copies of the uniform local residual. -/
theorem eulerErrorEnvelope_le_growth_pow_mul_initial_add_cells_residual
    {growth initial residual : Rat} (cells : Nat)
    (varying : Nat -> Rat)
    (hgrowth : 1 <= growth)
    (hresidual : 0 <= residual)
    (hvarying : forall n, n < cells -> varying n <= residual) :
    eulerErrorEnvelope growth initial varying cells <=
      growth ^ cells * (initial + (cells : Rat) * residual) := by
  have hgrowthNonneg : 0 <= growth :=
    Rat.le_trans (by decide : (0 : Rat) <= 1) hgrowth
  have hconstant := eulerErrorEnvelope_le_const_residual
    (initial := initial) (residual := residual) cells varying
    hgrowthNonneg hvarying
  have hweight := geometricWeightSum_le_cells_mul_pow hgrowth cells
  calc
    eulerErrorEnvelope growth initial varying cells <=
        growth ^ cells * initial + residual * geometricWeightSum growth cells :=
      hconstant
    _ <= growth ^ cells * initial +
        residual * ((cells : Rat) * growth ^ cells) := by
      exact (Rat.add_le_add_left
        (c := growth ^ cells * initial)).2
        (Rat.mul_le_mul_of_nonneg_left hweight hresidual)
    _ = growth ^ cells * (initial + (cells : Rat) * residual) := by
      grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]

/-- Mesh-scaled form of the varying-residual estimate. If every cell defect
is at most `step * defect`, then a total mesh length at most `length` bounds
the accumulated local contribution by `length * defect`, multiplied by the
Euler growth power. -/
theorem eulerErrorEnvelope_le_growth_pow_mul_initial_add_length_defect
    {growth initial step defect length : Rat} (cells : Nat)
    (varying : Nat -> Rat)
    (hgrowth : 1 <= growth)
    (hstep : 0 <= step)
    (hdefect : 0 <= defect)
    (htotal : (cells : Rat) * step <= length)
    (hvarying : forall n, n < cells -> varying n <= step * defect) :
    eulerErrorEnvelope growth initial varying cells <=
      growth ^ cells * (initial + length * defect) := by
  have hresidual : 0 <= step * defect := Rat.mul_nonneg hstep hdefect
  have hbase := eulerErrorEnvelope_le_growth_pow_mul_initial_add_cells_residual
    (initial := initial) (residual := step * defect)
    cells varying hgrowth hresidual hvarying
  have hcells : (cells : Rat) * (step * defect) <= length * defect := by
    calc
      (cells : Rat) * (step * defect) = ((cells : Rat) * step) * defect := by
        exact (Rat.mul_assoc _ _ _).symm
      _ <= length * defect := Rat.mul_le_mul_of_nonneg_right htotal hdefect
  have hgrowthPos : 0 < growth := by grind
  have hpowNonneg : 0 <= growth ^ cells :=
    Rat.le_of_lt (Rat.pow_pos hgrowthPos)
  calc
    eulerErrorEnvelope growth initial varying cells <=
        growth ^ cells * (initial + (cells : Rat) * (step * defect)) := hbase
    _ <= growth ^ cells * (initial + length * defect) :=
      Rat.mul_le_mul_of_nonneg_left
        ((Rat.add_le_add_left (c := initial)).2 hcells) hpowNonneg

/-- With zero initial discrepancy, a uniform per-cell error budget is
accumulated by exactly the finite geometric weight sum. -/
theorem eulerErrorEnvelope_zero_initial_const_residual
    (growth residual : Rat) (cells : Nat) :
    eulerErrorEnvelope growth 0 (fun _ => residual) cells =
      residual * geometricWeightSum growth cells := by
  rw [eulerErrorEnvelope_const_residual]
  rw [Rat.mul_zero]
  exact Rat.zero_add _

/-- A uniform residual on each cell propagates to a closed finite bound.
The theorem packages the exact recurrence estimate and its simple
`cells * growth^cells` majorant, so a later rational error schedule need only
make the displayed product small. -/
theorem eulerErrorEnvelope_zero_initial_const_residual_le
    {growth residual : Rat} (hgrowth : 1 <= growth)
    (hresidual : 0 <= residual) (cells : Nat) :
    eulerErrorEnvelope growth 0 (fun _ => residual) cells <=
      residual * ((cells : Rat) * growth ^ cells) := by
  rw [eulerErrorEnvelope_zero_initial_const_residual]
  exact Rat.mul_le_mul_of_nonneg_left
    (geometricWeightSum_le_cells_mul_pow hgrowth cells) hresidual

/-- A rational budget on each cell propagates to the requested global error
on a fixed finite mesh. The accumulated weight is explicit and computable
from the mesh growth factors. -/
theorem eulerErrorEnvelope_zero_initial_with_budget
    (growth residual tolerance : Rat) (cells : Nat)
    (hbudget :
      residual * geometricWeightSum growth cells <= tolerance) :
    eulerErrorEnvelope growth 0 (fun _ => residual) cells <= tolerance := by
  rw [eulerErrorEnvelope_zero_initial_const_residual]
  exact hbudget

/-- Nonnegative initial error and cell residuals produce a nonnegative
finite-mesh envelope whenever the Euler growth factor is nonnegative. -/
theorem eulerErrorEnvelope_nonneg
    (growth initial : Rat) (residual : Nat -> Rat)
    (hgrowth : 0 <= growth) (hinitial : 0 <= initial)
    (hresidual : forall n, 0 <= residual n) :
    forall n, 0 <= eulerErrorEnvelope growth initial residual n
  | 0 => hinitial
  | n + 1 => by
      rw [eulerErrorEnvelope]
      exact Rat.add_nonneg
        (Rat.mul_nonneg hgrowth
          (eulerErrorEnvelope_nonneg growth initial residual hgrowth
            hinitial hresidual n))
        (hresidual n)

/-- A cell-by-cell rational comparison propagates to the explicit error
envelope. This is the finite estimate used after a derivative certificate
has been converted into Euler-step residual bounds; it does not assume a
completed-function ODE theorem or pass a comparison object as input. -/
theorem error_le_eulerErrorEnvelope
    (growth initial : Rat) (residual : Nat -> Rat) (error : Nat -> Rat)
    (hgrowth : 0 <= growth)
    (initial_bound : error 0 <= initial)
    (step_bound : forall n,
      error (n + 1) <= growth * error n + residual n) :
    forall n, error n <= eulerErrorEnvelope growth initial residual n
  | 0 => initial_bound
  | n + 1 => by
      rw [eulerErrorEnvelope]
      calc
        error (n + 1) <= growth * error n + residual n := step_bound n
        _ <= growth * eulerErrorEnvelope growth initial residual n +
              residual n :=
          (Rat.add_le_add_right).2
            (Rat.mul_le_mul_of_nonneg_left
              (error_le_eulerErrorEnvelope growth initial residual error
                hgrowth initial_bound step_bound n) hgrowth)

/-- Triangle inequality for the finite entrywise absolute-sum vector norm. -/
theorem vectorAbsSum_add_le {dimension : Nat}
    (x y : RatVector dimension) :
    vectorAbsSum (vectorAdd x y) <= vectorAbsSum x + vectorAbsSum y := by
  unfold vectorAbsSum vectorAdd
  calc
    finiteSum (fun i => qabs (x i + y i)) <=
        finiteSum (fun i => qabs (x i) + qabs (y i)) :=
      finiteSum_le (fun i => qabs_add_le (x i) (y i))
    _ = finiteSum (fun i => qabs (x i)) +
          finiteSum (fun i => qabs (y i)) := finiteSum_add _ _

/-- One perturbed rational matrix step grows the vector error by at most the
column-sum bound, plus the finite residual norm. -/
theorem vector_step_error_le
    {dimension : Nat} (step : RatMatrix dimension)
    (error residual : RatVector dimension) (growth residualBound : Rat)
    (hcolumns : forall j, matrixColumnAbsSum step j <= growth)
    (hresidual : vectorAbsSum residual <= residualBound) :
    vectorAbsSum (vectorAdd (matrixApply step error) residual) <=
      growth * vectorAbsSum error + residualBound := by
  calc
    vectorAbsSum (vectorAdd (matrixApply step error) residual) <=
        vectorAbsSum (matrixApply step error) + vectorAbsSum residual :=
      vectorAbsSum_add_le _ _
    _ <= growth * vectorAbsSum error + residualBound := by
      exact (rat_add_le_add (matrixApply_vectorAbsSum_le_of_column_bound
        step error growth hcolumns) hresidual)

/-- Finite matrix recurrences with certified cell residuals stay inside the
scalar envelope obtained from their column-sum growth bounds. Thus an
analytic argument only needs to derive one residual bound per rational cell;
the induction over the finite mesh is handled uniformly here. -/
theorem vector_error_le_eulerErrorEnvelope
    {dimension : Nat} (growth initial : Rat) (residualBound : Nat -> Rat)
    (residual : Nat -> RatVector dimension) (step : Nat -> RatMatrix dimension)
    (trajectory : Nat -> RatVector dimension)
    (hgrowth : 0 <= growth)
    (hinitial : vectorAbsSum (trajectory 0) <= initial)
    (hcolumns : forall n j, matrixColumnAbsSum (step n) j <= growth)
    (hresidual : forall n, vectorAbsSum (residual n) <= residualBound n)
    (hstep : forall n,
      trajectory (n + 1) =
        vectorAdd (matrixApply (step n) (trajectory n)) (residual n)) :
    forall n,
      vectorAbsSum (trajectory n) <=
        eulerErrorEnvelope growth initial residualBound n := by
  apply error_le_eulerErrorEnvelope growth initial residualBound
    (fun n => vectorAbsSum (trajectory n))
  · exact hgrowth
  · exact hinitial
  · intro n
    rw [hstep n]
    exact vector_step_error_le (step n) (trajectory n) (residual n)
      growth (residualBound n) (hcolumns n) (hresidual n)

/-- Compare two finite-dimensional trajectories that solve the same Euler
steps up to certified residual vectors. Their discrepancy obeys the same
matrix growth bound, with the two residual budgets added. This is the
pairwise finite uniqueness estimate to be fed by derivative-to-step
certificates. -/
theorem difference_of_two_euler_trajectories_le_envelope
    {dimension : Nat} (growth initial : Rat)
    (residualBound : Nat -> Rat)
    (step : Nat -> RatMatrix dimension)
    (left right : Nat -> RatVector dimension)
    (leftResidual rightResidual : Nat -> RatVector dimension)
    (hgrowth : 0 <= growth)
    (hinitial : vectorAbsSum (vectorSub (left 0) (right 0)) <= initial)
    (hcolumns : forall n j, matrixColumnAbsSum (step n) j <= growth)
    (hresidual : forall n,
      vectorAbsSum (leftResidual n) + vectorAbsSum (rightResidual n) <=
        residualBound n)
    (hleft : forall n,
      left (n + 1) = vectorAdd (matrixApply (step n) (left n))
        (leftResidual n))
    (hright : forall n,
      right (n + 1) = vectorAdd (matrixApply (step n) (right n))
        (rightResidual n)) :
    forall n,
      vectorAbsSum (vectorSub (left n) (right n)) <=
        eulerErrorEnvelope growth initial residualBound n := by
  let residual := fun n => vectorSub (leftResidual n) (rightResidual n)
  have hresidual' : forall n, vectorAbsSum (residual n) <= residualBound n := by
    intro n
    exact Rat.le_trans (vectorAbsSum_sub_le (leftResidual n) (rightResidual n))
      (hresidual n)
  have hstep : forall n,
      vectorSub (left (n + 1)) (right (n + 1)) =
        vectorAdd (matrixApply (step n) (vectorSub (left n) (right n)))
          (residual n) := by
    intro n
    rw [hleft n, hright n, matrixApply_vectorSub]
    funext i
    simpa [residual, vectorSub, vectorAdd] using
      rat_sub_add_sub_eq (matrixApply (step n) (left n) i)
        (leftResidual n i) (matrixApply (step n) (right n) i)
        (rightResidual n i)
  intro n
  exact vector_error_le_eulerErrorEnvelope growth initial residualBound
    residual step (fun n => vectorSub (left n) (right n)) hgrowth hinitial
    hcolumns hresidual' hstep n

/-- Pairwise finite uniqueness also covers an inhomogeneous system. The
same sampled forcing vector is added to both Euler steps and cancels from
their difference; only the two solution-specific derivative residuals
contribute to the comparison budget. -/
theorem difference_of_two_forced_euler_trajectories_le_envelope
    {dimension : Nat} (growth initial : Rat)
    (residualBound : Nat -> Rat)
    (step : Nat -> RatMatrix dimension)
    (forcing : Nat -> RatVector dimension)
    (left right : Nat -> RatVector dimension)
    (leftResidual rightResidual : Nat -> RatVector dimension)
    (hgrowth : 0 <= growth)
    (hinitial : vectorAbsSum (vectorSub (left 0) (right 0)) <= initial)
    (hcolumns : forall n j, matrixColumnAbsSum (step n) j <= growth)
    (hresidual : forall n,
      vectorAbsSum (leftResidual n) + vectorAbsSum (rightResidual n) <=
        residualBound n)
    (hleft : forall n,
      left (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (left n)) (forcing n))
        (leftResidual n))
    (hright : forall n,
      right (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (right n)) (forcing n))
        (rightResidual n)) :
    forall n,
      vectorAbsSum (vectorSub (left n) (right n)) <=
        eulerErrorEnvelope growth initial residualBound n := by
  let residual := fun n => vectorSub (leftResidual n) (rightResidual n)
  have hcombined : forall n,
      vectorAbsSum (residual n) <= residualBound n := by
    intro n
    change vectorAbsSum (vectorSub (leftResidual n) (rightResidual n)) <= residualBound n
    exact Rat.le_trans (vectorAbsSum_sub_le (leftResidual n) (rightResidual n))
      (hresidual n)
  have hstep : forall n,
      vectorSub (left (n + 1)) (right (n + 1)) =
        vectorAdd (matrixApply (step n) (vectorSub (left n) (right n)))
          (residual n) := by
    intro n
    rw [hleft n, hright n, matrixApply_vectorSub]
    funext i
    simp [residual, vectorSub, vectorAdd]
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
  intro n
  exact vector_error_le_eulerErrorEnvelope growth initial residualBound
    residual step (fun n => vectorSub (left n) (right n)) hgrowth hinitial
    hcolumns hcombined hstep n

/-- Cellwise coordinate error bounds are enough to invoke the forced
trajectory comparison. This is the form used when derivative boxes provide
one rational defect bound per component and the finite sums have a common
budget. -/
theorem difference_of_two_forced_euler_trajectories_le_envelope_of_component_bounds
    {dimension : Nat} (growth initial : Rat)
    (residualBound : Nat -> Rat)
    (step : Nat -> RatMatrix dimension)
    (forcing : Nat -> RatVector dimension)
    (left right : Nat -> RatVector dimension)
    (leftResidual rightResidual : Nat -> RatVector dimension)
    (leftBound rightBound : Nat -> Fin dimension -> Rat)
    (hgrowth : 0 <= growth)
    (hinitial : vectorAbsSum (vectorSub (left 0) (right 0)) <= initial)
    (hcolumns : forall n j, matrixColumnAbsSum (step n) j <= growth)
    (hleftBound : forall n i, qabs (leftResidual n i) <= leftBound n i)
    (hrightBound : forall n i, qabs (rightResidual n i) <= rightBound n i)
    (hbudget : forall n,
      finiteSum (leftBound n) + finiteSum (rightBound n) <= residualBound n)
    (hleft : forall n,
      left (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (left n)) (forcing n))
        (leftResidual n))
    (hright : forall n,
      right (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (right n)) (forcing n))
        (rightResidual n)) :
    forall n,
      vectorAbsSum (vectorSub (left n) (right n)) <=
        eulerErrorEnvelope growth initial residualBound n := by
  apply difference_of_two_forced_euler_trajectories_le_envelope
    growth initial residualBound step forcing left right leftResidual rightResidual
  · exact hgrowth
  · exact hinitial
  · exact hcolumns
  · intro n
    calc
      vectorAbsSum (leftResidual n) + vectorAbsSum (rightResidual n) <=
          finiteSum (leftBound n) + finiteSum (rightBound n) :=
        rat_add_le_add
          (vectorAbsSum_le_of_component_bounds (leftResidual n) (leftBound n)
            (hleftBound n))
          (vectorAbsSum_le_of_component_bounds (rightResidual n) (rightBound n)
            (hrightBound n))
      _ <= residualBound n := hbudget n
  · exact hleft
  · exact hright

/-- Finite interval version of the forced trajectory comparison. Recurrence,
coefficient, and residual evidence is required only on the selected cells;
the conclusion covers every mesh node through the requested endpoint. -/
theorem difference_of_two_forced_euler_trajectories_le_envelope_up_to
    {dimension : Nat} (growth initial : Rat) (cells : Nat)
    (residualBound : Nat -> Rat)
    (step : Nat -> RatMatrix dimension)
    (forcing : Nat -> RatVector dimension)
    (left right : Nat -> RatVector dimension)
    (leftResidual rightResidual : Nat -> RatVector dimension)
    (hgrowth : 0 <= growth)
    (hinitial : vectorAbsSum (vectorSub (left 0) (right 0)) <= initial)
    (hcolumns : forall n, n < cells -> forall j,
      matrixColumnAbsSum (step n) j <= growth)
    (hresidual : forall n, n < cells ->
      vectorAbsSum (leftResidual n) + vectorAbsSum (rightResidual n) <=
        residualBound n)
    (hleft : forall n, n < cells ->
      left (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (left n)) (forcing n))
        (leftResidual n))
    (hright : forall n, n < cells ->
      right (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (right n)) (forcing n))
        (rightResidual n)) :
    forall n, n <= cells ->
      vectorAbsSum (vectorSub (left n) (right n)) <=
        eulerErrorEnvelope growth initial residualBound n := by
  let residual := fun n => vectorSub (leftResidual n) (rightResidual n)
  have hcombined : forall n, n < cells ->
      vectorAbsSum (residual n) <= residualBound n := by
    intro n hn
    change vectorAbsSum (vectorSub (leftResidual n) (rightResidual n)) <= residualBound n
    exact Rat.le_trans (vectorAbsSum_sub_le (leftResidual n) (rightResidual n))
      (hresidual n hn)
  have hstep : forall n, n < cells ->
      vectorSub (left (n + 1)) (right (n + 1)) =
        vectorAdd (matrixApply (step n) (vectorSub (left n) (right n)))
          (residual n) := by
    intro n hn
    rw [hleft n hn, hright n hn, matrixApply_vectorSub]
    funext i
    simp [residual, vectorSub, vectorAdd]
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
  have herrorStep : forall n, n < cells ->
      vectorAbsSum (vectorSub (left (n + 1)) (right (n + 1))) <=
        growth * vectorAbsSum (vectorSub (left n) (right n)) + residualBound n := by
    intro n hn
    rw [hstep n hn]
    exact vector_step_error_le (step n)
      (vectorSub (left n) (right n)) (residual n) growth (residualBound n)
      (hcolumns n hn) (hcombined n hn)
  intro n hn
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      have hnlt : n < cells := by omega
      rw [eulerErrorEnvelope]
      calc
        vectorAbsSum (vectorSub (left (n + 1)) (right (n + 1))) <=
            growth * vectorAbsSum (vectorSub (left n) (right n)) +
              residualBound n := herrorStep n hnlt
        _ <= growth * eulerErrorEnvelope growth initial residualBound n +
              residualBound n :=
          (Rat.add_le_add_right).2
            (Rat.mul_le_mul_of_nonneg_left (ih (by omega)) hgrowth)

/-- Pairwise finite comparison with a zero initial discrepancy and one
uniform residual budget.  This is the reusable uniqueness estimate for two
solution samplers: equal initial values and common Euler data cancel, while
the two independently certified local defects add. -/
theorem difference_of_two_forced_euler_trajectories_zero_initial_uniform_bound
    {dimension : Nat} (growth residualBound : Rat) (cells : Nat)
    (step : Nat -> RatMatrix dimension)
    (forcing : Nat -> RatVector dimension)
    (left right : Nat -> RatVector dimension)
    (leftResidual rightResidual : Nat -> RatVector dimension)
    (hgrowth : 1 <= growth)
    (hresidualBound_nonneg : 0 <= residualBound)
    (hinitial : left 0 = right 0)
    (hcolumns : forall n, n < cells -> forall j,
      matrixColumnAbsSum (step n) j <= growth)
    (hresidual : forall n, n < cells ->
      vectorAbsSum (leftResidual n) + vectorAbsSum (rightResidual n) <=
        residualBound)
    (hleft : forall n, n < cells ->
      left (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (left n)) (forcing n))
        (leftResidual n))
    (hright : forall n, n < cells ->
      right (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (right n)) (forcing n))
        (rightResidual n)) :
    vectorAbsSum (vectorSub (left cells) (right cells)) <=
      residualBound * ((cells : Rat) * growth ^ cells) := by
  have hgrowth_nonneg : 0 <= growth :=
    Rat.le_trans (by decide : (0 : Rat) <= 1) hgrowth
  have hcompare := difference_of_two_forced_euler_trajectories_le_envelope_up_to
    growth 0 cells (fun _ => residualBound) step forcing left right
    leftResidual rightResidual hgrowth_nonneg
    (by rw [hinitial]; simp [vectorSub, vectorAbsSum, qabs, Rat.sub_self, finiteSum_zero])
    hcolumns
    hresidual
    hleft hright cells (Nat.le_refl _)
  calc
    vectorAbsSum (vectorSub (left cells) (right cells)) <=
        eulerErrorEnvelope growth 0 (fun _ => residualBound) cells := hcompare
    _ <= residualBound * ((cells : Rat) * growth ^ cells) :=
      eulerErrorEnvelope_zero_initial_const_residual_le hgrowth
        hresidualBound_nonneg cells

/-- Short-block pairwise comparison for two forced Euler paths.  If the
coefficient contribution over the whole block is at most one half, the
endpoint discrepancy is at most twice the number of cells times the
per-cell residual budget. -/
theorem difference_of_two_forced_euler_trajectories_short_block
    {dimension : Nat} (coefficient residualBound : Rat) (cells : Nat)
    (step : Nat -> RatMatrix dimension)
    (forcing : Nat -> RatVector dimension)
    (left right : Nat -> RatVector dimension)
    (leftResidual rightResidual : Nat -> RatVector dimension)
    (hcoefficient : 0 <= coefficient) (hresidualBound : 0 <= residualBound)
    (hinitial : left 0 = right 0)
    (hcolumns : forall n, n < cells -> forall j,
      matrixColumnAbsSum (step n) j <= 1 + coefficient)
    (hresidual : forall n, n < cells ->
      vectorAbsSum (leftResidual n) + vectorAbsSum (rightResidual n) <=
        residualBound)
    (hleft : forall n, n < cells ->
      left (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (left n)) (forcing n))
        (leftResidual n))
    (hright : forall n, n < cells ->
      right (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (right n)) (forcing n))
        (rightResidual n))
    (hshort : (cells : Rat) * coefficient <= (1 : Rat) / 2) :
    vectorAbsSum (vectorSub (left cells) (right cells)) <=
      2 * ((cells : Rat) * residualBound) := by
  have hgrowth : 1 <= 1 + coefficient := by
    have h := (Rat.add_le_add_left (c := (1 : Rat))).2 hcoefficient
    simpa [Rat.add_zero] using h
  have hgrowthNonneg : 0 <= 1 + coefficient :=
    Rat.le_trans (by decide : (0 : Rat) <= 1) hgrowth
  have hcompare := difference_of_two_forced_euler_trajectories_le_envelope_up_to
    (1 + coefficient) 0 cells (fun _ => residualBound) step forcing left right
    leftResidual rightResidual hgrowthNonneg
    (by rw [hinitial]; simp [vectorSub, vectorAbsSum, qabs, Rat.sub_self, finiteSum_zero])
    hcolumns hresidual hleft hright
  have henvelope_nonneg : forall n, n <= cells ->
      0 <= eulerErrorEnvelope (1 + coefficient) 0
        (fun _ => residualBound) n := by
    intro n hn
    exact eulerErrorEnvelope_nonneg (1 + coefficient) 0
      (fun _ => residualBound) hgrowthNonneg (by decide) (fun _ => hresidualBound) n
  have henvelope_step : forall n, n < cells ->
      eulerErrorEnvelope (1 + coefficient) 0
        (fun _ => residualBound) (n + 1) <=
          (1 + coefficient) *
            eulerErrorEnvelope (1 + coefficient) 0
              (fun _ => residualBound) n + residualBound := by
    intro n hn
    rw [eulerErrorEnvelope]
    exact Rat.le_refl
  have hsmall := finite_mesh_error_short_block
    (fun n => eulerErrorEnvelope (1 + coefficient) 0
      (fun _ => residualBound) n) cells coefficient residualBound
    hcoefficient hresidualBound
    (by simp [eulerErrorEnvelope]) henvelope_nonneg henvelope_step hshort
  exact Rat.le_trans (hcompare cells (Nat.le_refl _)) hsmall

/-- Pairwise short-block estimate with a certified initial discrepancy. This
is the form needed when the two rational evaluators name the same represented
initial value but have different lower endpoints at the selected precision. -/
theorem difference_of_two_forced_euler_trajectories_short_block_with_initial
    {dimension : Nat} (coefficient residualBound initial : Rat) (cells : Nat)
    (step : Nat -> RatMatrix dimension)
    (forcing : Nat -> RatVector dimension)
    (left right : Nat -> RatVector dimension)
    (leftResidual rightResidual : Nat -> RatVector dimension)
    (hcoefficient : 0 <= coefficient) (hresidualBound : 0 <= residualBound)
    (hinitial_nonneg : 0 <= initial)
    (hinitial : vectorAbsSum (vectorSub (left 0) (right 0)) <= initial)
    (hcolumns : forall n, n < cells -> forall j,
      matrixColumnAbsSum (step n) j <= 1 + coefficient)
    (hresidual : forall n, n < cells ->
      vectorAbsSum (leftResidual n) + vectorAbsSum (rightResidual n) <=
        residualBound)
    (hleft : forall n, n < cells ->
      left (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (left n)) (forcing n))
        (leftResidual n))
    (hright : forall n, n < cells ->
      right (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (right n)) (forcing n))
        (rightResidual n))
    (hshort : (cells : Rat) * coefficient <= (1 : Rat) / 2) :
    vectorAbsSum (vectorSub (left cells) (right cells)) <=
      2 * (initial + (cells : Rat) * residualBound) := by
  have hgrowth : 1 <= 1 + coefficient := by
    have h := (Rat.add_le_add_left (c := (1 : Rat))).2 hcoefficient
    simpa [Rat.add_zero] using h
  have hgrowthNonneg : 0 <= 1 + coefficient :=
    Rat.le_trans (by decide : (0 : Rat) <= 1) hgrowth
  have hcompare := difference_of_two_forced_euler_trajectories_le_envelope_up_to
    (1 + coefficient) initial cells (fun _ => residualBound) step forcing
    left right leftResidual rightResidual hgrowthNonneg hinitial hcolumns
    hresidual hleft hright
  have henvelope_nonneg : forall n, n <= cells ->
      0 <= eulerErrorEnvelope (1 + coefficient) initial
        (fun _ => residualBound) n := by
    intro n hn
    exact eulerErrorEnvelope_nonneg (1 + coefficient) initial
      (fun _ => residualBound) hgrowthNonneg hinitial_nonneg
      (fun _ => hresidualBound) n
  have henvelope_step : forall n, n < cells ->
      eulerErrorEnvelope (1 + coefficient) initial
        (fun _ => residualBound) (n + 1) <=
          (1 + coefficient) *
            eulerErrorEnvelope (1 + coefficient) initial
              (fun _ => residualBound) n + residualBound := by
    intro n hn
    rw [eulerErrorEnvelope]
    exact Rat.le_refl
  have hsmall := finite_mesh_error_short_block_with_initial
    (fun n => eulerErrorEnvelope (1 + coefficient) initial
      (fun _ => residualBound) n) cells coefficient residualBound initial
    hcoefficient hresidualBound
    (by simp [eulerErrorEnvelope]) henvelope_nonneg henvelope_step hshort
  exact Rat.le_trans (hcompare cells (Nat.le_refl _)) hsmall

/-- End-to-end finite comparison theorem for a zero-initial discrepancy in a
finite-dimensional linear recurrence. A uniform rational budget for every
cell residual yields the displayed global error budget at the requested
mesh node. This is the reusable finite core of the ODE comparison argument:
only the derivation of the per-cell residuals from continuous derivative
evidence remains specific to the equation and its solutions. -/
theorem vector_error_zero_initial_with_uniform_budget
    {dimension : Nat} (growth residualBound tolerance : Rat) (cells : Nat)
    (residual : Nat -> RatVector dimension) (step : Nat -> RatMatrix dimension)
    (trajectory : Nat -> RatVector dimension)
    (hgrowth : 0 <= growth)
    (hinitial : trajectory 0 = vectorZero dimension)
    (hcolumns : forall n j, matrixColumnAbsSum (step n) j <= growth)
    (hresidual : forall n, vectorAbsSum (residual n) <= residualBound)
    (hstep : forall n,
      trajectory (n + 1) =
        vectorAdd (matrixApply (step n) (trajectory n)) (residual n))
    (hbudget : residualBound * geometricWeightSum growth cells <= tolerance) :
    vectorAbsSum (trajectory cells) <= tolerance := by
  have htrajectory := vector_error_le_eulerErrorEnvelope
    growth 0 (fun _ => residualBound) residual step trajectory hgrowth
    (by rw [hinitial]; simp [vectorAbsSum, vectorZero, qabs, finiteSum_zero])
    hcolumns (fun n => hresidual n) hstep
  calc
    vectorAbsSum (trajectory cells) <=
        eulerErrorEnvelope growth 0 (fun _ => residualBound) cells :=
      htrajectory cells
    _ = residualBound * geometricWeightSum growth cells :=
      eulerErrorEnvelope_zero_initial_const_residual growth residualBound cells
    _ <= tolerance := hbudget

/-- A closed-form version of the finite vector estimate.  When the Euler
growth factor is at least one, a per-cell residual `r` leaves the endpoint
error at most `r * cells * growth^cells`.  This bound is intentionally
finite; the later analytic argument supplies a schedule making it small. -/
theorem vector_error_zero_initial_with_uniform_budget_le
    {dimension : Nat} (growth residualBound tolerance : Rat) (cells : Nat)
    (residual : Nat -> RatVector dimension) (step : Nat -> RatMatrix dimension)
    (trajectory : Nat -> RatVector dimension)
    (hgrowth : 1 <= growth) (hresidualBound : 0 <= residualBound)
    (hinitial : trajectory 0 = vectorZero dimension)
    (hcolumns : forall n j, matrixColumnAbsSum (step n) j <= growth)
    (hresidual : forall n, vectorAbsSum (residual n) <= residualBound)
    (hstep : forall n,
      trajectory (n + 1) =
        vectorAdd (matrixApply (step n) (trajectory n)) (residual n))
    (hbudget : residualBound * ((cells : Rat) * growth ^ cells) <= tolerance) :
    vectorAbsSum (trajectory cells) <= tolerance := by
  apply vector_error_zero_initial_with_uniform_budget
    growth residualBound tolerance cells residual step trajectory
  · exact Rat.le_trans (by decide : (0 : Rat) <= 1) hgrowth
  · exact hinitial
  · exact hcolumns
  · exact hresidual
  · exact hstep
  · apply Rat.le_trans _ hbudget
    exact Rat.mul_le_mul_of_nonneg_left
      (geometricWeightSum_le_cells_mul_pow hgrowth cells) hresidualBound

/-- A uniform entrywise coefficient bound gives a complete finite-mesh
comparison theorem for a nonautonomous rational Euler system. At every cell,
the coefficient matrix may vary, but its entries obey the same explicit
bound. Once the ODE-specific derivative argument supplies the residual
budget, this theorem computes the resulting global error directly. -/
theorem vector_error_zero_initial_for_euler_system
    {dimension : Nat} (h entryBound residualBound tolerance : Rat)
    (cells : Nat) (coefficient : Nat -> RatMatrix dimension)
    (residual : Nat -> RatVector dimension)
    (trajectory : Nat -> RatVector dimension)
    (hentryBound : 0 <= entryBound)
    (hentry : forall n i j, qabs (coefficient n i j) <= entryBound)
    (hinitial : trajectory 0 = vectorZero dimension)
    (hresidual : forall n, vectorAbsSum (residual n) <= residualBound)
    (hstep : forall n,
      trajectory (n + 1) = vectorAdd
        (matrixApply
          (matrixAdd (matrixIdentity dimension)
            (matrixScale h (coefficient n))) (trajectory n))
        (residual n))
    (hbudget :
      residualBound * geometricWeightSum
        (1 + qabs h * finiteSum (fun _ : Fin dimension => entryBound)) cells <=
        tolerance) :
    vectorAbsSum (trajectory cells) <= tolerance := by
  let growth :=
    1 + qabs h * finiteSum (fun _ : Fin dimension => entryBound)
  have hsum : 0 <= finiteSum (fun _ : Fin dimension => entryBound) :=
    finiteSum_nonneg (fun _ => hentryBound)
  have hgrowth : 0 <= growth := by
    dsimp [growth]
    exact Rat.add_nonneg (Rat.le_of_lt (by decide))
      (Rat.mul_nonneg (qabs_nonneg h) hsum)
  have hcolumns : forall n j,
      matrixColumnAbsSum
        (matrixAdd (matrixIdentity dimension)
          (matrixScale h (coefficient n))) j <= growth := by
    intro n j
    dsimp [growth]
    exact matrixColumnAbsSum_eulerStep_le_of_entry_bound
      (coefficient n) h entryBound (fun i k => hentry n i k) j
  exact vector_error_zero_initial_with_uniform_budget
    growth residualBound tolerance cells residual
    (fun n => matrixAdd (matrixIdentity dimension)
      (matrixScale h (coefficient n))) trajectory hgrowth hinitial
    hcolumns hresidual hstep (by simpa [growth] using hbudget)

/-- Positive-step specialization of the finite Euler-system comparison.
The growth factor is the familiar `1 + h * sum(entry bounds)`, suitable for
uniform rational partitions of a forward interval. -/
theorem vector_error_zero_initial_for_positive_euler_system
    {dimension : Nat} (h entryBound residualBound tolerance : Rat)
    (cells : Nat) (coefficient : Nat -> RatMatrix dimension)
    (residual : Nat -> RatVector dimension)
    (trajectory : Nat -> RatVector dimension)
    (hstepNonneg : 0 <= h) (hentryBound : 0 <= entryBound)
    (hentry : forall n i j, qabs (coefficient n i j) <= entryBound)
    (hinitial : trajectory 0 = vectorZero dimension)
    (hresidual : forall n, vectorAbsSum (residual n) <= residualBound)
    (hstep : forall n,
      trajectory (n + 1) = vectorAdd
        (matrixApply
          (matrixAdd (matrixIdentity dimension)
            (matrixScale h (coefficient n))) (trajectory n))
        (residual n))
    (hbudget :
      residualBound * geometricWeightSum
        (1 + h * finiteSum (fun _ : Fin dimension => entryBound)) cells <=
        tolerance) :
    vectorAbsSum (trajectory cells) <= tolerance := by
  apply vector_error_zero_initial_for_euler_system
    h entryBound residualBound tolerance cells coefficient residual trajectory
    hentryBound hentry hinitial hresidual hstep
  simpa [qabs_eq_self_of_nonneg hstepNonneg] using hbudget

/-- Fully composed finite comparison theorem from coordinatewise Euler
residual enclosures. Its hypotheses are local rational inequalities, while
its conclusion is a global finite-mesh error bound for a variable-coefficient
linear system. Derivative certificates can supply each coordinate
inequality via `HasDerivativeOnInterval.lowerEndpoint_eulerResidual`. -/
theorem vector_error_zero_initial_for_positive_euler_system_of_component_residuals
    {dimension : Nat} (h entryBound residualBound tolerance : Rat)
    (cells : Nat) (coefficient : Nat -> RatMatrix dimension)
    (trajectory : Nat -> RatVector dimension)
    (cellBound : Nat -> Fin dimension -> Rat)
    (hstepNonneg : 0 <= h) (hentryBound : 0 <= entryBound)
    (hentry : forall n i j, qabs (coefficient n i j) <= entryBound)
    (hinitial : trajectory 0 = vectorZero dimension)
    (hcomponent : forall n i,
      -cellBound n i <=
          trajectory (n + 1) i -
            (trajectory n i + h * matrixApply (coefficient n) (trajectory n) i) /\
        trajectory (n + 1) i -
          (trajectory n i + h * matrixApply (coefficient n) (trajectory n) i) <=
            cellBound n i)
    (hcellBudget : forall n, finiteSum (cellBound n) <= residualBound)
    (hbudget :
      residualBound * geometricWeightSum
        (1 + h * finiteSum (fun _ : Fin dimension => entryBound)) cells <=
        tolerance) :
    vectorAbsSum (trajectory cells) <= tolerance := by
  let step := fun n =>
    matrixAdd (matrixIdentity dimension) (matrixScale h (coefficient n))
  let residual := fun n =>
    vectorSub (trajectory (n + 1)) (matrixApply (step n) (trajectory n))
  have hresidual : forall n, vectorAbsSum (residual n) <= residualBound := by
    intro n
    calc
      vectorAbsSum (residual n) <= finiteSum (cellBound n) := by
        dsimp [residual, step]
        exact eulerResidual_vectorAbsSum_le (coefficient n) h
          (trajectory n) (trajectory (n + 1)) (cellBound n)
          (hcomponent n)
      _ <= residualBound := hcellBudget n
  have hstep : forall n,
      trajectory (n + 1) =
        vectorAdd (matrixApply (step n) (trajectory n)) (residual n) := by
    intro n
    funext i
    simp only [residual, step, vectorAdd, vectorSub]
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  exact vector_error_zero_initial_for_positive_euler_system
    h entryBound residualBound tolerance cells coefficient residual trajectory
    hstepNonneg hentryBound hentry hinitial hresidual hstep hbudget

/-- A homogeneous sampled trajectory is the action of its exact
chronological transition matrix on the initial state. -/
theorem homogeneousTrajectory_eq_chronologicalStepProduct
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension) :
    forall n,
      system.homogeneousTrajectory initial n =
        matrixApply (chronologicalStepProduct system.step 0 n) initial
  | 0 => by
      exact (matrixApply_identity initial).symm
  | n + 1 => by
      rw [homogeneousTrajectory_succ, chronologicalStepProduct_succ]
      simp only [Nat.zero_add]
      rw [homogeneousTrajectory_eq_chronologicalStepProduct system initial n]
      exact (matrixApply_matrixMul _ _ _).symm

/-- Exact finite variation of constants for a sampled linear system.

The second summand is the trajectory from zero initial data, so its recursion
is the chronological finite Duhamel sum of the forcing samples.  This proof
uses only finite rational matrix actions; no limiting ODE theorem is hidden in
the statement. -/
theorem trajectory_eq_homogeneous_add_zeroInitial
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension) :
    forall n,
      system.trajectory initial n =
        vectorAdd (system.homogeneousTrajectory initial n)
          (system.trajectory (vectorZero dimension) n)
  | 0 => by
      unfold trajectory homogeneousTrajectory vectorAdd vectorZero
      funext i
      exact (Rat.add_zero _).symm
  | n + 1 => by
      change
        vectorAdd (matrixApply (system.step n) (system.trajectory initial n))
            (system.forcing n) =
          vectorAdd
            (matrixApply (system.step n)
              (system.homogeneousTrajectory initial n))
            (vectorAdd
              (matrixApply (system.step n)
                (system.trajectory (vectorZero dimension) n))
              (system.forcing n))
      rw [trajectory_eq_homogeneous_add_zeroInitial system initial n]
      rw [matrixApply_vectorAdd]
      exact vectorAdd_assoc _ _ _

/-- Exact finite variation of constants with the homogeneous term displayed
as its chronological transition matrix. -/
theorem trajectory_eq_transition_add_zeroInitial
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension)
    (n : Nat) :
    system.trajectory initial n =
      vectorAdd
        (matrixApply (chronologicalStepProduct system.step 0 n) initial)
        (system.trajectory (vectorZero dimension) n) := by
  rw [trajectory_eq_homogeneous_add_zeroInitial]
  rw [homogeneousTrajectory_eq_chronologicalStepProduct system initial n]

/-- The literal finite sum of a vector-valued sequence.  It is kept separate
from matrix sums because the inhomogeneous Peano--Baker formula transports
forcing *vectors*, not additional matrices. -/
def vectorSequenceSum {dimension : Nat} (f : Nat -> RatVector dimension) :
    Nat -> RatVector dimension
  | 0 => vectorZero dimension
  | n + 1 => vectorAdd (vectorSequenceSum f n) (f n)

theorem vectorSequenceSum_congr_on {dimension : Nat}
    (f g : Nat -> RatVector dimension) :
    forall n, (forall k, k < n -> f k = g k) ->
      vectorSequenceSum f n = vectorSequenceSum g n
  | 0, _ => rfl
  | n + 1, h => by
      rw [vectorSequenceSum, vectorSequenceSum,
        vectorSequenceSum_congr_on f g n (fun k hk => h k (by omega)),
        h n (by omega)]

theorem matrixApply_vectorSequenceSum {dimension : Nat}
    (A : RatMatrix dimension) (f : Nat -> RatVector dimension) :
    forall n,
      matrixApply A (vectorSequenceSum f n) =
        vectorSequenceSum (fun k => matrixApply A (f k)) n
  | 0 => by
      change matrixApply A (vectorZero dimension) = vectorZero dimension
      exact matrixApply_zero A
  | n + 1 => by
      change matrixApply A (vectorAdd (vectorSequenceSum f n) (f n)) =
        vectorAdd (vectorSequenceSum (fun k => matrixApply A (f k)) n)
          (matrixApply A (f n))
      rw [matrixApply_vectorAdd, matrixApply_vectorSequenceSum A f n]

/-- The transition carrying the forcing sample at time `k` to the final
sample time `final`.  The first step after the force is `k + 1`; hence a
force applied at the final step itself is transported by the identity. -/
def forcingTransition (system : DiscreteLinearSystem dimension)
    (final k : Nat) : RatMatrix dimension :=
  chronologicalStepProduct system.step (k + 1) (final - (k + 1))

/-- The `k`th time-ordered forcing contribution to the state at `final`. -/
def duhamelTerm (system : DiscreteLinearSystem dimension)
    (final k : Nat) : RatVector dimension :=
  matrixApply (forcingTransition system final k) (system.forcing k)

/-- The finite Duhamel sum for the zero-initial sampled system:
`∑_{k < N} S_{N-1} ⋯ S_{k+1} g_k`.  Every factor is a literal
rational transition product; no continuous integral or limiting argument is
hidden in this definition. -/
def duhamelSum (system : DiscreteLinearSystem dimension) (final : Nat) :
    RatVector dimension :=
  vectorSequenceSum (duhamelTerm system final) final

private theorem forcingTransition_succ
    (system : DiscreteLinearSystem dimension) (n k : Nat) (hk : k < n) :
    forcingTransition system (n + 1) k =
      matrixMul (system.step n) (forcingTransition system n k) := by
  unfold forcingTransition
  have hlength : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by
    omega
  have hindex : k + 1 + (n - (k + 1)) = n := by
    exact Nat.add_sub_of_le (by omega)
  rw [hlength, chronologicalStepProduct_succ]
  rw [hindex]

private theorem duhamelTerm_succ
    (system : DiscreteLinearSystem dimension) (n k : Nat) (hk : k < n) :
    duhamelTerm system (n + 1) k =
      matrixApply (system.step n) (duhamelTerm system n k) := by
  unfold duhamelTerm
  rw [forcingTransition_succ system n k hk, matrixApply_matrixMul]

private theorem duhamelTerm_latest
    (system : DiscreteLinearSystem dimension) (n : Nat) :
    duhamelTerm system (n + 1) n = system.forcing n := by
  unfold duhamelTerm forcingTransition
  simp [matrixApply_identity]

private theorem duhamelSum_prefix_succ
    (system : DiscreteLinearSystem dimension) (n : Nat) :
    vectorSequenceSum (duhamelTerm system (n + 1)) n =
      matrixApply (system.step n) (duhamelSum system n) := by
  calc
    vectorSequenceSum (duhamelTerm system (n + 1)) n =
        vectorSequenceSum
          (fun k => matrixApply (system.step n) (duhamelTerm system n k)) n :=
      vectorSequenceSum_congr_on _ _ n
        (fun k hk => duhamelTerm_succ system n k hk)
    _ = matrixApply (system.step n) (duhamelSum system n) := by
      unfold duhamelSum
      exact (matrixApply_vectorSequenceSum (system.step n)
        (duhamelTerm system n) n).symm

/-- Exact finite variation of constants for the zero-initial sampled system.
The recursive forcing response is the explicit chronological Duhamel sum. -/
theorem trajectory_zeroInitial_eq_duhamelSum
    (system : DiscreteLinearSystem dimension) :
    forall n, system.trajectory (vectorZero dimension) n = duhamelSum system n
  | 0 => rfl
  | n + 1 => by
      rw [trajectory_succ,
        trajectory_zeroInitial_eq_duhamelSum system n]
      unfold duhamelSum
      rw [vectorSequenceSum, duhamelSum_prefix_succ,
        duhamelTerm_latest]
      rfl

/-- Exact finite variation of constants with both the homogeneous state
transition and the explicit time-ordered Duhamel sum displayed. -/
theorem trajectory_eq_transition_add_duhamelSum
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension)
    (n : Nat) :
    system.trajectory initial n =
      vectorAdd
        (matrixApply (chronologicalStepProduct system.step 0 n) initial)
        (duhamelSum system n) := by
  rw [trajectory_eq_transition_add_zeroInitial,
    trajectory_zeroInitial_eq_duhamelSum]

/-- A sampled system has no inhomogeneous contribution when every forcing
sample is the zero vector. -/
def ForcingZero (system : DiscreteLinearSystem dimension) : Prop :=
  forall k, system.forcing k = vectorZero dimension

theorem trajectory_zeroInitial_of_forcingZero
    (system : DiscreteLinearSystem dimension) (hzero : system.ForcingZero) :
    forall n, system.trajectory (vectorZero dimension) n = vectorZero dimension
  | 0 => rfl
  | n + 1 => by
      change
        vectorAdd (matrixApply (system.step n)
            (system.trajectory (vectorZero dimension) n))
          (system.forcing n) = vectorZero dimension
      rw [trajectory_zeroInitial_of_forcingZero system hzero n, hzero n,
        matrixApply_zero]
      funext i
      exact Rat.zero_add _

theorem trajectory_eq_homogeneous_of_forcingZero
    (system : DiscreteLinearSystem dimension) (hzero : system.ForcingZero)
    (initial : RatVector dimension) (n : Nat) :
    system.trajectory initial n = system.homogeneousTrajectory initial n := by
  rw [trajectory_eq_homogeneous_add_zeroInitial]
  rw [trajectory_zeroInitial_of_forcingZero system hzero n]
  exact vectorAdd_zero_right _

/-- The constant-coefficient discrete specialization. -/
def ConstantStep (system : DiscreteLinearSystem dimension) : Prop :=
  forall k, system.step k = system.step 0

/-- The commuting-coefficient discrete specialization.  This is the exact
finite hypothesis behind collapsing a time-ordered product to an ordinary
exponential later on. -/
def PairwiseCommutingSteps (system : DiscreteLinearSystem dimension) : Prop :=
  forall i j, matrixMul (system.step i) (system.step j) =
    matrixMul (system.step j) (system.step i)

end DiscreteLinearSystem

/- The familiar forced harmonic oscillator, represented as the two-dimensional
Euler system that the finite Peano--Baker layer actually computes.  This is a
finite rational seed for the later continuous rotation and exponential
identifications; it does not presuppose sine, cosine, or a completed real
line. -/
namespace HarmonicOscillator

/-- Position/velocity state vector. -/
def state (position velocity : Rat) : RatVector 2 :=
  fun i => if i = 0 then position else velocity

/-- Position coordinate of a two-dimensional state. -/
def position (x : RatVector 2) : Rat := x 0

/-- Velocity coordinate of a two-dimensional state. -/
def velocity (x : RatVector 2) : Rat := x 1

theorem state_position (q v : Rat) :
    position (state q v) = q := by
  simp [position, state]

theorem state_velocity (q v : Rat) :
    velocity (state q v) = v := by
  simp [state, velocity]

private theorem finiteSum_two (f : Fin 2 -> Rat) :
    finiteSum f = f 0 + f 1 := by
  change f 0 + (f 1 + 0) = f 0 + f 1
  rw [Rat.add_zero]

/-! ## A finite Cayley--Hamilton core -/

/-- An explicit rational `2 x 2` matrix, used for small linear-algebra
certificates without importing an ambient matrix library. -/
def twoByTwoMatrix (a b c d : Rat) : RatMatrix 2 :=
  fun i =>
    Fin.cases
      (fun j => Fin.cases a (fun _ => b) j)
      (fun _ j => Fin.cases c (fun _ => d) j)
      i

@[simp] theorem twoByTwoMatrix_00 (a b c d : Rat) :
    twoByTwoMatrix a b c d 0 0 = a := by rfl

@[simp] theorem twoByTwoMatrix_01 (a b c d : Rat) :
    twoByTwoMatrix a b c d 0 1 = b := by rfl

@[simp] theorem twoByTwoMatrix_10 (a b c d : Rat) :
    twoByTwoMatrix a b c d 1 0 = c := by rfl

@[simp] theorem twoByTwoMatrix_11 (a b c d : Rat) :
    twoByTwoMatrix a b c d 1 1 = d := by rfl

def twoByTwoTrace (a _b _c d : Rat) : Rat := a + d

def twoByTwoDeterminant (a b c d : Rat) : Rat := a * d - b * c

/-- The adjugate of an explicit rational `2 x 2` matrix.  Keeping this
construction at the concrete dimension two makes the inverse certificate
executable and avoids importing a general determinant or inverse theory. -/
def twoByTwoAdjugate (a b c d : Rat) : RatMatrix 2 :=
  twoByTwoMatrix d (-b) (-c) a

/-- The finite adjugate identity on the right.  This is the algebraic
certificate behind reversing a nonsingular sampled transition. -/
theorem twoByTwo_mul_adjugate (a b c d : Rat) :
    matrixMul (twoByTwoMatrix a b c d) (twoByTwoAdjugate a b c d) =
      matrixScale (twoByTwoDeterminant a b c d) (matrixIdentity 2) := by
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp [twoByTwoAdjugate, twoByTwoDeterminant,
        matrixMul, matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      · simp [twoByTwoAdjugate, twoByTwoDeterminant, matrixMul, matrixScale, matrixIdentity,
          finiteSum_two]
        grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
          Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · simp [twoByTwoAdjugate, twoByTwoDeterminant, matrixMul, matrixScale, matrixIdentity,
        finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simp [twoByTwoAdjugate, twoByTwoDeterminant, matrixMul, matrixScale, matrixIdentity,
          finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

/-- The finite adjugate identity on the left. -/
theorem twoByTwo_adjugate_mul (a b c d : Rat) :
    matrixMul (twoByTwoAdjugate a b c d) (twoByTwoMatrix a b c d) =
      matrixScale (twoByTwoDeterminant a b c d) (matrixIdentity 2) := by
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp [twoByTwoAdjugate, twoByTwoDeterminant,
        matrixMul, matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      · simp [twoByTwoAdjugate, twoByTwoDeterminant, matrixMul, matrixScale, matrixIdentity,
          finiteSum_two]
        grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
          Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · simp [twoByTwoAdjugate, twoByTwoDeterminant, matrixMul, matrixScale, matrixIdentity,
        finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simp [twoByTwoAdjugate, twoByTwoDeterminant, matrixMul, matrixScale, matrixIdentity,
          finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

/-- The exact rational inverse of a nonsingular concrete `2 x 2` matrix. -/
def twoByTwoInverse (a b c d : Rat) : RatMatrix 2 :=
  matrixScale (twoByTwoDeterminant a b c d)⁻¹
    (twoByTwoAdjugate a b c d)

theorem twoByTwo_mul_inverse {a b c d : Rat}
    (hdet : twoByTwoDeterminant a b c d ≠ 0) :
    matrixMul (twoByTwoMatrix a b c d) (twoByTwoInverse a b c d) =
      matrixIdentity 2 := by
  unfold twoByTwoInverse
  rw [matrixMul_matrixScale_right, twoByTwo_mul_adjugate,
    matrixScale_comp]
  have hcancel :
      (twoByTwoDeterminant a b c d)⁻¹ * twoByTwoDeterminant a b c d = 1 := by
    rw [Rat.mul_comm]
    exact Rat.mul_inv_cancel _ hdet
  rw [hcancel, matrixScale_one]

theorem twoByTwo_inverse_mul {a b c d : Rat}
    (hdet : twoByTwoDeterminant a b c d ≠ 0) :
    matrixMul (twoByTwoInverse a b c d) (twoByTwoMatrix a b c d) =
      matrixIdentity 2 := by
  unfold twoByTwoInverse
  rw [matrixMul_matrixScale_left, twoByTwo_adjugate_mul,
    matrixScale_comp]
  have hcancel :
      (twoByTwoDeterminant a b c d)⁻¹ * twoByTwoDeterminant a b c d = 1 := by
    rw [Rat.mul_comm]
    exact Rat.mul_inv_cancel _ hdet
  rw [hcancel, matrixScale_one]

theorem twoByTwo_inverse_unique_right {a b c d : Rat}
    (hdet : twoByTwoDeterminant a b c d ≠ 0)
    (B : RatMatrix 2)
    (hB : matrixMul (twoByTwoMatrix a b c d) B = matrixIdentity 2) :
    B = twoByTwoInverse a b c d := by
  calc
    B = matrixMul (matrixIdentity 2) B :=
      (matrixMul_identity_left B).symm
    _ = matrixMul
        (matrixMul (twoByTwoInverse a b c d)
          (twoByTwoMatrix a b c d)) B := by
      exact (congrArg (fun M => matrixMul M B)
        (twoByTwo_inverse_mul hdet)).symm
    _ = matrixMul (twoByTwoInverse a b c d)
        (matrixMul (twoByTwoMatrix a b c d) B) :=
      matrixMul_assoc _ _ _
    _ = matrixMul (twoByTwoInverse a b c d) (matrixIdentity 2) := by
      rw [hB]
    _ = twoByTwoInverse a b c d := matrixMul_identity_right _

theorem twoByTwo_inverse_unique_left {a b c d : Rat}
    (hdet : twoByTwoDeterminant a b c d ≠ 0)
    (B : RatMatrix 2)
    (hB : matrixMul B (twoByTwoMatrix a b c d) = matrixIdentity 2) :
    B = twoByTwoInverse a b c d := by
  calc
    B = matrixMul B (matrixIdentity 2) :=
      (matrixMul_identity_right B).symm
    _ = matrixMul B
        (matrixMul (twoByTwoMatrix a b c d)
          (twoByTwoInverse a b c d)) := by
      exact (congrArg (fun M => matrixMul B M)
        (twoByTwo_mul_inverse hdet)).symm
    _ = matrixMul (matrixMul B (twoByTwoMatrix a b c d))
        (twoByTwoInverse a b c d) :=
      (matrixMul_assoc _ _ _).symm
    _ = matrixMul (matrixIdentity 2) (twoByTwoInverse a b c d) := by
      rw [hB]
    _ = twoByTwoInverse a b c d := matrixMul_identity_left _

theorem twoByTwo_inverse_solves {a b c d : Rat}
    (hdet : twoByTwoDeterminant a b c d ≠ 0)
    (x : RatVector 2) :
    matrixApply (twoByTwoMatrix a b c d)
        (matrixApply (twoByTwoInverse a b c d) x) = x := by
  calc
    matrixApply (twoByTwoMatrix a b c d)
        (matrixApply (twoByTwoInverse a b c d) x) =
        matrixApply
          (matrixMul (twoByTwoMatrix a b c d)
            (twoByTwoInverse a b c d)) x :=
      (matrixApply_matrixMul _ _ _).symm
    _ = matrixApply (matrixIdentity 2) x := by
      rw [twoByTwo_mul_inverse hdet]
    _ = x := matrixApply_identity x

theorem twoByTwo_solution_unique {a b c d : Rat}
    (hdet : twoByTwoDeterminant a b c d ≠ 0)
    (rhs u v : RatVector 2)
    (hu : matrixApply (twoByTwoMatrix a b c d) u = rhs)
    (hv : matrixApply (twoByTwoMatrix a b c d) v = rhs) :
    u = v := by
  have huv : matrixApply (twoByTwoMatrix a b c d) u =
      matrixApply (twoByTwoMatrix a b c d) v := hu.trans hv.symm
  calc
    u = matrixApply (matrixIdentity 2) u := (matrixApply_identity u).symm
    _ = matrixApply
        (matrixMul (twoByTwoInverse a b c d)
          (twoByTwoMatrix a b c d)) u := by
      rw [twoByTwo_inverse_mul hdet]
    _ = matrixApply (twoByTwoInverse a b c d)
        (matrixApply (twoByTwoMatrix a b c d) u) :=
      matrixApply_matrixMul _ _ _
    _ = matrixApply (twoByTwoInverse a b c d)
        (matrixApply (twoByTwoMatrix a b c d) v) :=
      congrArg (matrixApply (twoByTwoInverse a b c d)) huv
    _ = matrixApply
        (matrixMul (twoByTwoInverse a b c d)
          (twoByTwoMatrix a b c d)) v :=
      (matrixApply_matrixMul _ _ _).symm
    _ = matrixApply (matrixIdentity 2) v := by
      rw [twoByTwo_inverse_mul hdet]
    _ = v := matrixApply_identity v

/-- The Cayley--Hamilton identity for an explicit rational `2 x 2` matrix.
This is the finite matrix core of benchmark item 49; arbitrary dimensions and
an abstract characteristic-polynomial interface remain outside the project
boundary. -/
theorem twoByTwo_cayley_hamilton (a b c d : Rat) :
    let A := twoByTwoMatrix a b c d
    matrixAdd (matrixMul A A)
        (matrixAdd
          (matrixScale (-(twoByTwoTrace a b c d)) A)
          (matrixScale (twoByTwoDeterminant a b c d)
            (matrixIdentity 2))) =
      matrixZero 2 := by
  dsimp [twoByTwoTrace, twoByTwoDeterminant]
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp [matrixAdd, matrixMul, matrixScale, matrixIdentity, matrixZero,
        finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      · simp [matrixAdd, matrixMul, matrixScale, matrixIdentity, matrixZero,
          finiteSum_two]
        grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
          Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · simp [matrixAdd, matrixMul, matrixScale, matrixIdentity, matrixZero,
        finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simp [matrixAdd, matrixMul, matrixScale, matrixIdentity, matrixZero,
          finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

/-- The trace read directly from an arbitrary rational `2 x 2` matrix. -/
def ratMatrixTwoTrace (A : RatMatrix 2) : Rat := A 0 0 + A 1 1

/-- The determinant read directly from an arbitrary rational `2 x 2` matrix.
This is a finite four-entry formula, not an imported determinant API. -/
def ratMatrixTwoDeterminant (A : RatMatrix 2) : Rat :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0

/-- Every rational `2 x 2` matrix is extensionally its explicit four-entry
presentation.  This finite extensionality bridge makes the concrete
Cayley--Hamilton certificate reusable for arbitrary matrix data. -/
theorem ratMatrix_twoByTwo_eq_explicit (A : RatMatrix 2) :
    A = twoByTwoMatrix (A 0 0) (A 0 1) (A 1 0) (A 1 1) := by
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · rfl
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      rfl
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · rfl
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      rfl

/-- General rational `2 x 2` Cayley--Hamilton certificate.  For arbitrary
matrix data `A`, the finite characteristic polynomial identity is
`A² - trace(A) A + det(A) I = 0`; no completed reals, limits, or continuous
ODE theorem are involved. -/
theorem ratMatrix_twoByTwo_cayley_hamilton (A : RatMatrix 2) :
    matrixAdd (matrixMul A A)
        (matrixAdd
          (matrixScale (-(ratMatrixTwoTrace A)) A)
          (matrixScale (ratMatrixTwoDeterminant A)
            (matrixIdentity 2))) =
      matrixZero 2 := by
  have hA := ratMatrix_twoByTwo_eq_explicit A
  unfold ratMatrixTwoTrace ratMatrixTwoDeterminant
  rw [hA]
  simpa only [twoByTwoMatrix_00, twoByTwoMatrix_01, twoByTwoMatrix_10,
    twoByTwoMatrix_11, twoByTwoTrace, twoByTwoDeterminant] using
    (twoByTwo_cayley_hamilton (A 0 0) (A 0 1) (A 1 0) (A 1 1))

private theorem finiteSum_three (f : Fin 3 -> Rat) :
    finiteSum f = f 0 + f 1 + f 2 := by
  change f 0 + (f 1 + (f 2 + 0)) = f 0 + f 1 + f 2
  grind [Rat.add_assoc]

/-- An explicit rational `3 x 3` matrix for the next finite
characteristic-polynomial certificate. -/
def threeByThreeMatrix
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) : RatMatrix 3 :=
  fun i =>
    Fin.cases
      (fun j => Fin.cases a00 (fun j => Fin.cases a01 (fun _ => a02) j) j)
      (fun i => Fin.cases
        (fun j => Fin.cases a10 (fun j => Fin.cases a11 (fun _ => a12) j) j)
        (fun i => Fin.cases
          (fun j => Fin.cases a20 (fun j => Fin.cases a21 (fun _ => a22) j) j)
          (fun i => Fin.elim0 i) i) i) i

@[simp] theorem threeByThreeMatrix_00 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 0 0 = a00 := by rfl
@[simp] theorem threeByThreeMatrix_01 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 0 1 = a01 := by rfl
@[simp] theorem threeByThreeMatrix_02 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 0 2 = a02 := by rfl
@[simp] theorem threeByThreeMatrix_10 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 1 0 = a10 := by rfl
@[simp] theorem threeByThreeMatrix_11 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 1 1 = a11 := by rfl
@[simp] theorem threeByThreeMatrix_12 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 1 2 = a12 := by rfl
@[simp] theorem threeByThreeMatrix_20 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 2 0 = a20 := by rfl
@[simp] theorem threeByThreeMatrix_21 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 2 1 = a21 := by rfl
@[simp] theorem threeByThreeMatrix_22 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 2 2 = a22 := by rfl

def threeByThreeTrace (a00 _a01 _a02 _a10 a11 _a12 _a20 _a21 a22 : Rat) : Rat :=
  a00 + a11 + a22

def threeByThreeSecondCoeff
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) : Rat :=
  a00 * a11 + a00 * a22 + a11 * a22 - a01 * a10 - a02 * a20 - a12 * a21

def threeByThreeDeterminant
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) : Rat :=
  a00 * (a11 * a22 - a12 * a21) -
    a01 * (a10 * a22 - a12 * a20) +
    a02 * (a10 * a21 - a11 * a20)

/-- The finite rational `3 x 3` Cayley--Hamilton identity
`A^3 - tr(A) A^2 + s₂(A) A - det(A) I = 0`, where `s₂` is the second
elementary characteristic coefficient.  This is a higher-dimensional
certificate-level extension of the project's general `2 x 2` result; it
still uses only explicit finite sums and rational ring identities. -/
theorem threeByThree_cayley_hamilton
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    let A := threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22
    matrixAdd (matrixMul A (matrixMul A A))
        (matrixAdd
          (matrixScale (-(threeByThreeTrace a00 a01 a02 a10 a11 a12 a20 a21 a22))
            (matrixMul A A))
          (matrixAdd
            (matrixScale
              (threeByThreeSecondCoeff a00 a01 a02 a10 a11 a12 a20 a21 a22) A)
            (matrixScale
              (-(threeByThreeDeterminant a00 a01 a02 a10 a11 a12 a20 a21 a22))
              (matrixIdentity 3)))) =
      matrixZero 3 := by
  dsimp [threeByThreeTrace, threeByThreeSecondCoeff,
    threeByThreeDeterminant]
  funext i j
  have hi : i = 0 \/ i = 1 \/ i = 2 := by omega
  have hj : j = 0 \/ j = 1 \/ j = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl <;>
      simp [matrixAdd, matrixMul, matrixScale,
        matrixIdentity, matrixZero, finiteSum_three,
        threeByThreeMatrix_00, threeByThreeMatrix_01,
        threeByThreeMatrix_02, threeByThreeMatrix_10,
        threeByThreeMatrix_11, threeByThreeMatrix_12,
        threeByThreeMatrix_20, threeByThreeMatrix_21,
        threeByThreeMatrix_22] <;>
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

/-- The generator with rows `(0, 1)` and `(-omega^2, 0)`. -/
def generator (omega : Rat) : RatMatrix 2 :=
  fun i =>
    Fin.cases
      (fun j => Fin.cases 0 (fun _ => 1) j)
      (fun _ j => Fin.cases (-(omega * omega)) (fun _ => 0) j)
      i

/-- One forward Euler step for the oscillator generator. -/
def eulerStep (step omega : Rat) : RatMatrix 2 :=
  fun i =>
    Fin.cases
      (fun j => Fin.cases 1 (fun _ => step) j)
      (fun _ j => Fin.cases (-(step * omega * omega)) (fun _ => 1) j)
      i

@[simp] theorem eulerStep_00 (step omega : Rat) :
    eulerStep step omega 0 0 = 1 := by rfl

@[simp] theorem eulerStep_01 (step omega : Rat) :
    eulerStep step omega 0 1 = step := by rfl

@[simp] theorem eulerStep_10 (step omega : Rat) :
    eulerStep step omega 1 0 = -(step * omega * omega) := by rfl

@[simp] theorem eulerStep_11 (step omega : Rat) :
    eulerStep step omega 1 1 = 1 := by rfl

/-- Applying the oscillator Euler step produces the familiar position update. -/
theorem eulerStep_position (step omega : Rat) (x : RatVector 2) :
    position (matrixApply (eulerStep step omega) x) =
      position x + step * velocity x := by
  unfold position velocity matrixApply
  rw [finiteSum_two]
  rw [eulerStep_00, eulerStep_01]
  simp

/-- Applying the oscillator Euler step produces the familiar velocity update. -/
theorem eulerStep_velocity (step omega : Rat) (x : RatVector 2) :
    velocity (matrixApply (eulerStep step omega) x) =
      velocity x - step * omega * omega * position x := by
  unfold position velocity matrixApply
  rw [finiteSum_two]
  rw [eulerStep_10, eulerStep_11]
  simp
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.mul_assoc,
    Rat.mul_comm]

/-- Force samples enter only the velocity coordinate. -/
def forcing (step : Rat) (drive : Nat -> Rat) : Nat -> RatVector 2 :=
  fun n => state 0 (step * drive n)

/-- The sampled inhomogeneous oscillator system. -/
def eulerSystem (step omega : Rat) (drive : Nat -> Rat) :
    DiscreteLinearSystem 2 where
  step := fun _ => eulerStep step omega
  forcing := forcing step drive

theorem forcing_position (step : Rat) (drive : Nat -> Rat) (n : Nat) :
    position (forcing step drive n) = 0 := by
  simp [forcing, state_position]

theorem forcing_velocity (step : Rat) (drive : Nat -> Rat) (n : Nat) :
    velocity (forcing step drive n) = step * drive n := by
  simp [forcing, state_velocity]

/-- The vector Euler system has exactly the expected discrete position update. -/
theorem trajectory_position_succ
    (step omega : Rat) (drive : Nat -> Rat) (initial : RatVector 2) (n : Nat) :
    position ((eulerSystem step omega drive).trajectory initial (n + 1)) =
      position ((eulerSystem step omega drive).trajectory initial n) +
        step * velocity ((eulerSystem step omega drive).trajectory initial n) := by
  rw [DiscreteLinearSystem.trajectory_succ]
  change
    position
      (vectorAdd
        (matrixApply (eulerStep step omega)
          ((eulerSystem step omega drive).trajectory initial n))
        (forcing step drive n)) = _
  change
    position
        (matrixApply (eulerStep step omega)
          ((eulerSystem step omega drive).trajectory initial n)) +
      position (forcing step drive n) = _
  rw [eulerStep_position]
  rw [forcing_position, Rat.add_zero]

/-- The vector Euler system has exactly the expected discrete velocity update. -/
theorem trajectory_velocity_succ
    (step omega : Rat) (drive : Nat -> Rat) (initial : RatVector 2) (n : Nat) :
    velocity ((eulerSystem step omega drive).trajectory initial (n + 1)) =
      velocity ((eulerSystem step omega drive).trajectory initial n) -
          step * omega * omega *
            position ((eulerSystem step omega drive).trajectory initial n) +
        step * drive n := by
  rw [DiscreteLinearSystem.trajectory_succ]
  change
    velocity
      (vectorAdd
        (matrixApply (eulerStep step omega)
          ((eulerSystem step omega drive).trajectory initial n))
        (forcing step drive n)) = _
  change
    velocity
        (matrixApply (eulerStep step omega)
          ((eulerSystem step omega drive).trajectory initial n)) +
      velocity (forcing step drive n) = _
  rw [eulerStep_velocity]
  rw [forcing_velocity]

/-- Eliminating velocity gives the exact second-order finite Euler recurrence.
It is the discrete counterpart of the forced oscillator equation, with no
limiting argument hidden in the statement. -/
theorem trajectory_position_secondDifference
    (step omega : Rat) (drive : Nat -> Rat) (initial : RatVector 2) (n : Nat) :
    position ((eulerSystem step omega drive).trajectory initial (n + 2)) -
        2 * position ((eulerSystem step omega drive).trajectory initial (n + 1)) +
        position ((eulerSystem step omega drive).trajectory initial n) =
      -(step * step * omega * omega *
          position ((eulerSystem step omega drive).trajectory initial n)) +
        step * step * drive n := by
  have hq0 := trajectory_position_succ step omega drive initial n
  have hv0 := trajectory_velocity_succ step omega drive initial n
  have hq1 := trajectory_position_succ step omega drive initial (n + 1)
  rw [show n + 2 = (n + 1) + 1 by omega, hq1, hv0, hq0]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.mul_add,
    Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

end HarmonicOscillator

/-- All strictly time-ordered selections from the first `steps` sample times.

The newest selected time is put on the left.  Thus `[3, 1, 0]` denotes the
ordered product `B_3 * B_1 * B_0`, the order required for a noncommuting
linear system. -/
def orderedIndexWords : Nat -> List (List Nat)
  | 0 => [[]]
  | n + 1 => orderedIndexWords n ++
    (orderedIndexWords n).map (fun word => n :: word)

/-- Finite addition of matrices, kept recursive so it is visibly executable. -/
def matrixListSum {dimension : Nat} : List (RatMatrix dimension) -> RatMatrix dimension
  | [] => matrixZero dimension
  | A :: rest => matrixAdd A (matrixListSum rest)

theorem matrixListSum_append {dimension : Nat} (xs ys : List (RatMatrix dimension)) :
    matrixListSum (xs ++ ys) = matrixAdd (matrixListSum xs) (matrixListSum ys) := by
  induction xs with
  | nil =>
      simp only [List.nil_append, matrixListSum]
      exact (matrixAdd_zero_left _).symm
  | cons A xs ih =>
      simp only [List.cons_append, matrixListSum]
      rw [ih, matrixAdd_assoc]

theorem matrixMul_matrixListSum {dimension : Nat} (B : RatMatrix dimension) :
    forall xs : List (RatMatrix dimension),
      matrixMul B (matrixListSum xs) = matrixListSum (xs.map (matrixMul B)) := by
  intro xs
  induction xs with
  | nil =>
      simp [matrixListSum, matrixMul_zero_right]
  | cons A xs ih =>
      simp only [matrixListSum, List.map_cons]
      rw [matrixMul_add_right, ih]

/-- Evaluate one time-ordered word in a rational matrix sequence. -/
def timeOrderedProduct {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    List Nat -> RatMatrix dimension
  | [] => matrixIdentity dimension
  | k :: rest => matrixMul (B k) (timeOrderedProduct B rest)

/-- The finite, noncommutative Peano--Baker expansion.  It has one term for
every ordered subset of the sampled times.  A continuous Peano--Baker series
will replace each word by an iterated simplex integral. -/
def peanoBakerDiscreteSum {dimension : Nat} (B : Nat -> RatMatrix dimension) (steps : Nat) :
    RatMatrix dimension :=
  matrixListSum ((orderedIndexWords steps).map (timeOrderedProduct B))

/-- The corresponding chronological product of Euler step matrices. -/
def chronologicalProduct {dimension : Nat} (B : Nat -> RatMatrix dimension) : Nat ->
    RatMatrix dimension
  | 0 => matrixIdentity dimension
  | n + 1 => matrixMul (matrixAdd (matrixIdentity dimension) (B n))
      (chronologicalProduct B n)

theorem chronologicalProduct_columnAbsSum_le_pow {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (c : Rat)
    (hbound : forall n j,
      matrixColumnAbsSum (matrixAdd (matrixIdentity dimension) (B n)) j <= c)
    (hc : 0 <= c) :
    forall steps j,
      matrixColumnAbsSum (chronologicalProduct B steps) j <= c ^ steps
  | 0, j => by
      rw [chronologicalProduct, matrixColumnAbsSum_identity, Rat.pow_zero]
      decide +kernel
  | steps + 1, j => by
      rw [chronologicalProduct]
      have hmul := matrixMul_columnAbsSum_le_of_column_bound
        (matrixAdd (matrixIdentity dimension) (B steps))
        (chronologicalProduct B steps) c
        (fun k => hbound steps k) j
      have hprevious :
          matrixColumnAbsSum (chronologicalProduct B steps) j <= c ^ steps :=
        chronologicalProduct_columnAbsSum_le_pow B c hbound hc steps j
      calc
        matrixColumnAbsSum (matrixMul
            (matrixAdd (matrixIdentity dimension) (B steps))
            (chronologicalProduct B steps)) j <=
            c * matrixColumnAbsSum (chronologicalProduct B steps) j := hmul
        _ <= c * c ^ steps :=
          Rat.mul_le_mul_of_nonneg_left hprevious hc
        _ = c ^ (steps + 1) := by
          rw [Rat.pow_succ]
          exact Rat.mul_comm _ _

theorem chronologicalProduct_stateAbsSum_le {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (c : Rat)
    (hbound : forall n j,
      matrixColumnAbsSum (matrixAdd (matrixIdentity dimension) (B n)) j <= c)
    (hc : 0 <= c) (steps : Nat) (x : RatVector dimension) :
    vectorAbsSum (matrixApply (chronologicalProduct B steps) x) <=
      c ^ steps * vectorAbsSum x := by
  apply matrixApply_vectorAbsSum_le_of_column_bound
    (chronologicalProduct B steps) x (c ^ steps)
  intro j
  exact chronologicalProduct_columnAbsSum_le_pow B c hbound hc steps j

def ratProduct (f : Nat -> Rat) : Nat -> Rat
  | 0 => 1
  | n + 1 => ratProduct f n * f n

theorem ratProduct_nonneg (f : Nat -> Rat) (hf : forall n, 0 <= f n) :
    forall n, 0 <= ratProduct f n
  | 0 => by
      change (0 : Rat) <= 1
      decide +kernel
  | n + 1 => by
      rw [ratProduct]
      exact Rat.mul_nonneg (ratProduct_nonneg f hf n) (hf n)

theorem ratProduct_const_eq_pow (c : Rat) :
    forall n, ratProduct (fun _ => c) n = c ^ n
  | 0 => by
      rw [ratProduct, Rat.pow_zero]
  | n + 1 => by
      rw [ratProduct, ratProduct_const_eq_pow c n, Rat.pow_succ]

theorem chronologicalProduct_rowAbsSum_le {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (bound : Nat -> Rat)
    (hbound : forall n i,
      matrixRowAbsSum (matrixAdd (matrixIdentity dimension) (B n)) i <= bound n)
    (hbound_nonneg : forall n, 0 <= bound n) :
    forall steps i,
      matrixRowAbsSum (chronologicalProduct B steps) i <= ratProduct bound steps
  | 0, i => by
      rw [chronologicalProduct, matrixRowAbsSum_identity, ratProduct]
      decide +kernel
  | steps + 1, i => by
      rw [chronologicalProduct]
      have hmul := matrixMul_rowAbsSum_le
        (matrixAdd (matrixIdentity dimension) (B steps))
        (chronologicalProduct B steps) i
      have hprevious : forall k,
          matrixRowAbsSum (chronologicalProduct B steps) k <=
            ratProduct bound steps :=
        fun k => chronologicalProduct_rowAbsSum_le B bound hbound
          hbound_nonneg steps k
      have hweighted := finiteSum_mul_le_of_nonneg
        (fun k => qabs ((matrixAdd (matrixIdentity dimension) (B steps)) i k))
        (fun k => matrixRowAbsSum (chronologicalProduct B steps) k)
        (ratProduct bound steps)
        (fun k => qabs_nonneg _)
        hprevious
      calc
        matrixRowAbsSum (matrixMul
            (matrixAdd (matrixIdentity dimension) (B steps))
            (chronologicalProduct B steps)) i <=
            finiteSum (fun k =>
              qabs ((matrixAdd (matrixIdentity dimension) (B steps)) i k) *
                matrixRowAbsSum (chronologicalProduct B steps) k) :=
          hmul
        _ <= ratProduct bound steps *
              finiteSum (fun k =>
                qabs ((matrixAdd (matrixIdentity dimension) (B steps)) i k)) :=
          hweighted
        _ = ratProduct bound steps *
            matrixRowAbsSum (matrixAdd (matrixIdentity dimension) (B steps)) i := rfl
        _ <= ratProduct bound steps * bound steps := by
          exact Rat.mul_le_mul_of_nonneg_left (hbound steps i)
            (ratProduct_nonneg bound hbound_nonneg steps)
        _ = ratProduct bound (steps + 1) := by
          rw [ratProduct]

theorem chronologicalProduct_rowAbsSum_le_pow {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (c : Rat)
    (hbound : forall n i,
      matrixRowAbsSum (matrixAdd (matrixIdentity dimension) (B n)) i <= c)
    (hc : 0 <= c) :
    forall steps i,
      matrixRowAbsSum (chronologicalProduct B steps) i <= c ^ steps := by
  intro steps i
  have hgeneral := chronologicalProduct_rowAbsSum_le B (fun _ => c)
    (fun n j => hbound n j) (fun _ => hc) steps i
  rw [ratProduct_const_eq_pow c steps] at hgeneral
  exact hgeneral

/-- The general sampled transition specializes exactly to the
Peano--Baker chronological product for Euler increments. -/
theorem chronologicalStepProduct_eulerIncrement {dimension : Nat}
    (B : Nat -> RatMatrix dimension) :
    forall steps,
      chronologicalStepProduct
        (fun k => matrixAdd (matrixIdentity dimension) (B k)) 0 steps =
        chronologicalProduct B steps
  | 0 => rfl
  | steps + 1 => by
      rw [chronologicalStepProduct_succ, chronologicalProduct]
      simp only [Nat.zero_add]
      rw [chronologicalStepProduct_eulerIncrement B steps]

/-- Splitting a sampled time interval preserves chronological order: increments
from the later subinterval occur on the left of the earlier transition. -/
theorem chronologicalProduct_split {dimension : Nat} (B : Nat -> RatMatrix dimension)
    (first second : Nat) :
    chronologicalProduct B (first + second) =
      matrixMul (chronologicalProduct (fun k => B (first + k)) second)
        (chronologicalProduct B first) := by
  induction second with
  | zero =>
      simp [chronologicalProduct, matrixMul_identity_left]
  | succ second ih =>
      rw [show first + (second + 1) = (first + second) + 1 by omega]
      rw [chronologicalProduct, ih]
      change matrixMul (matrixAdd (matrixIdentity dimension) (B (first + second)))
          (matrixMul (chronologicalProduct (fun k => B (first + k)) second)
            (chronologicalProduct B first)) =
        matrixMul
          (matrixMul (matrixAdd (matrixIdentity dimension) (B (first + second)))
            (chronologicalProduct (fun k => B (first + k)) second))
          (chronologicalProduct B first)
      exact (matrixMul_assoc _ _ _).symm

/-- Natural powers of a matrix, with the newest factor on the left.  This is
the exact constant-step specialization of a chronological product. -/
def matrixPow {dimension : Nat} (A : RatMatrix dimension) : Nat -> RatMatrix dimension
  | 0 => matrixIdentity dimension
  | n + 1 => matrixMul A (matrixPow A n)

theorem matrixPow_identity {dimension : Nat} :
    forall n, matrixPow (matrixIdentity dimension) n = matrixIdentity dimension
  | 0 => rfl
  | n + 1 => by
      rw [matrixPow, matrixPow_identity n, matrixMul_identity_left]

/-- Matrix powers split at a finite degree.  This is the local algebra used
to group constant Peano--Baker terms into their even and odd parts. -/
theorem matrixPow_add {dimension : Nat} (A : RatMatrix dimension) :
    forall m n, matrixPow A (m + n) = matrixMul (matrixPow A m) (matrixPow A n)
  | 0, n => by
      simp [matrixPow, matrixMul_identity_left]
  | m + 1, n => by
      rw [show (m + 1) + n = (m + n) + 1 by omega]
      rw [matrixPow, matrixPow, matrixPow_add A m n]
      exact (matrixMul_assoc _ _ _).symm

/-- Every finite power of an arbitrary rational `2 x 2` matrix reduces by its
characteristic polynomial.  This is the executable Cayley--Hamilton power
recurrence

`A^(n+2) = trace(A) A^(n+1) - det(A) A^n`.

The statement is entirely finite: powers are natural recursive products and
the coefficients are the four-entry rational trace and determinant above.
It is a certificate for discrete matrix algebra, not a continuous ODE
theorem or a convergence assertion. -/
theorem ratMatrix_twoByTwo_matrixPow_succ_succ_recurrence (A : RatMatrix 2) :
    forall n,
      matrixPow A (n + 2) =
        matrixAdd
          (matrixScale (HarmonicOscillator.ratMatrixTwoTrace A)
            (matrixPow A (n + 1)))
          (matrixScale (-(HarmonicOscillator.ratMatrixTwoDeterminant A))
            (matrixPow A n)) := by
  have hbase :
      matrixMul A A =
        matrixAdd
          (matrixScale (HarmonicOscillator.ratMatrixTwoTrace A) A)
          (matrixScale (-(HarmonicOscillator.ratMatrixTwoDeterminant A))
            (matrixIdentity 2)) := by
    have hCH := HarmonicOscillator.ratMatrix_twoByTwo_cayley_hamilton A
    funext i j
    have hij := congrFun (congrFun hCH i) j
    dsimp [matrixAdd, matrixScale, matrixZero] at hij ⊢
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]
  intro n
  rw [show n + 2 = 2 + n by omega, matrixPow_add A 2 n]
  change matrixMul (matrixMul A (matrixMul A (matrixIdentity 2)))
      (matrixPow A n) = _
  rw [matrixMul_identity_right, hbase, matrixMul_add_left,
    matrixMul_matrixScale_left, matrixMul_matrixScale_left,
    matrixMul_identity_left]
  rw [show n + 1 = 1 + n by omega, matrixPow_add A 1 n]
  simp only [matrixPow, matrixMul_identity_right]

/-- Any rational matrix sequence with the same first two values and the
characteristic recurrence is the corresponding finite matrix-power sequence.
This is a bounded induction certificate for the Cayley--Hamilton reduction:
it compares only finitely many rational matrices at any requested stage. -/
theorem ratMatrix_twoByTwo_matrixPow_recurrence_unique (A : RatMatrix 2)
    (X : Nat -> RatMatrix 2)
    (h0 : X 0 = matrixIdentity 2)
    (h1 : X 1 = A)
    (hrec : forall n,
      X (n + 2) =
        matrixAdd
          (matrixScale (HarmonicOscillator.ratMatrixTwoTrace A) (X (n + 1)))
          (matrixScale (-(HarmonicOscillator.ratMatrixTwoDeterminant A))
            (X n))) :
    forall n, X n = matrixPow A n
  | 0 => h0
  | 1 => by
      change X 1 = matrixMul A (matrixIdentity 2)
      rw [matrixMul_identity_right]
      exact h1
  | n + 2 => by
      rw [hrec n, ratMatrix_twoByTwo_matrixPow_succ_succ_recurrence A n]
      rw [ratMatrix_twoByTwo_matrixPow_recurrence_unique A X h0 h1 hrec (n + 1),
        ratMatrix_twoByTwo_matrixPow_recurrence_unique A X h0 h1 hrec n]

namespace HarmonicOscillator

/-- The first nontrivial power reduction supplied by the explicit
Cayley--Hamilton certificate.  This is a finite rational evaluation identity:
the third power of a `2 x 2` matrix is reduced to the matrix itself and the
identity, with coefficients given by its trace and determinant. -/
theorem twoByTwo_matrixPow_three (a b c d : Rat) :
    matrixPow (twoByTwoMatrix a b c d) 3 =
      matrixAdd
        (matrixScale
          ((twoByTwoTrace a b c d) ^ 2 - twoByTwoDeterminant a b c d)
          (twoByTwoMatrix a b c d))
        (matrixScale
          (-(twoByTwoTrace a b c d * twoByTwoDeterminant a b c d))
          (matrixIdentity 2)) := by
  change matrixMul (twoByTwoMatrix a b c d)
      (matrixMul (twoByTwoMatrix a b c d)
        (matrixMul (twoByTwoMatrix a b c d) (matrixIdentity 2))) = _
  rw [matrixMul_identity_right]
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
        matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      · simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
          matrixScale, matrixIdentity, finiteSum_two]
        grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
          Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
        matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
          matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

/-! The next finite Cayley--Hamilton reduction, still entirely rational. -/

theorem twoByTwo_matrixPow_four (a b c d : Rat) :
    matrixPow (twoByTwoMatrix a b c d) 4 =
      matrixAdd
        (matrixScale
          ((twoByTwoTrace a b c d) ^ 3 -
            2 * twoByTwoTrace a b c d * twoByTwoDeterminant a b c d)
          (twoByTwoMatrix a b c d))
        (matrixScale
          (twoByTwoDeterminant a b c d ^ 2 -
            twoByTwoTrace a b c d ^ 2 * twoByTwoDeterminant a b c d)
          (matrixIdentity 2)) := by
  change matrixMul (twoByTwoMatrix a b c d)
      (matrixMul (twoByTwoMatrix a b c d)
        (matrixMul (twoByTwoMatrix a b c d)
          (matrixMul (twoByTwoMatrix a b c d) (matrixIdentity 2)))) = _
  rw [matrixMul_identity_right]
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
        matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      · simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
          matrixScale, matrixIdentity, finiteSum_two]
        grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
          Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
        matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
          matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

end HarmonicOscillator

/-- The degree-`r` ordered-simplex term for a constant coefficient matrix.
The scalar factor `T^r/r!` is the exact rational volume of the ordered
simplex of duration `T`; the matrix factor keeps the chronological order
visible.  This is a finite term, not yet an infinite matrix series. -/
def orderedSimplexVolume (T : Rat) : Nat -> Rat
  | 0 => 1
  | degree + 1 =>
      T / ((degree + 1 : Nat) : Rat) * orderedSimplexVolume T degree

theorem orderedSimplexVolume_eq_closed (T : Rat) (degree : Nat) :
    orderedSimplexVolume T degree = T ^ degree / factorialRat degree := by
  induction degree with
  | zero =>
      unfold orderedSimplexVolume factorialRat factorial
      rw [Rat.pow_zero]
      decide +kernel
  | succ degree ih =>
      rw [orderedSimplexVolume, ih, Rat.pow_succ,
        FormalPowerSeries.factorialRat_succ]
      rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm]

def constantPeanoBakerSimplexTerm {dimension : Nat}
    (A : RatMatrix dimension) (T : Rat) (degree : Nat) : RatMatrix dimension :=
  matrixScale (T ^ degree / factorialRat degree) (matrixPow A degree)

theorem constantPeanoBakerSimplexTerm_eq_orderedSimplexVolume
    {dimension : Nat} (A : RatMatrix dimension) (T : Rat) (degree : Nat) :
    constantPeanoBakerSimplexTerm A T degree =
      matrixScale (orderedSimplexVolume T degree) (matrixPow A degree) := by
  rw [orderedSimplexVolume_eq_closed]
  rfl

/-- A finite constant-coefficient Peano--Baker polynomial, assembled in
increasing degree order from its explicit ordered-simplex terms. -/
def constantPeanoBakerSimplexPartial {dimension : Nat}
    (A : RatMatrix dimension) (T : Rat) : Nat -> RatMatrix dimension
  | 0 => matrixZero dimension
  | terms + 1 => matrixAdd
      (constantPeanoBakerSimplexPartial A T terms)
      (constantPeanoBakerSimplexTerm A T terms)

theorem constantPeanoBakerSimplexTerm_zero {dimension : Nat}
    (A : RatMatrix dimension) (T : Rat) :
    constantPeanoBakerSimplexTerm A T 0 = matrixIdentity dimension := by
  unfold constantPeanoBakerSimplexTerm
  have hscalar : T ^ 0 / factorialRat 0 = (1 : Rat) := by
    rw [Rat.pow_zero]
    unfold factorialRat factorial
    decide +kernel
  change matrixScale (T ^ 0 / factorialRat 0) (matrixIdentity dimension) =
    matrixIdentity dimension
  rw [hscalar, matrixScale_one]

/-- Adjacent constant-coefficient simplex terms satisfy the expected
Peano--Baker recurrence: prepend the coefficient matrix and multiply by the
next time-volume factor `T/(r+1)`. -/
theorem constantPeanoBakerSimplexTerm_succ {dimension : Nat}
    (A : RatMatrix dimension) (T : Rat) (degree : Nat) :
    constantPeanoBakerSimplexTerm A T (degree + 1) =
      matrixScale (T / ((degree + 1 : Nat) : Rat))
        (matrixMul A (constantPeanoBakerSimplexTerm A T degree)) := by
  unfold constantPeanoBakerSimplexTerm
  rw [matrixMul_matrixScale_right, matrixScale_comp]
  rw [Rat.pow_succ, FormalPowerSeries.factorialRat_succ]
  congr 1
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem constantPeanoBakerSimplexPartial_succ {dimension : Nat}
    (A : RatMatrix dimension) (T : Rat) (terms : Nat) :
    constantPeanoBakerSimplexPartial A T (terms + 1) = matrixAdd
      (constantPeanoBakerSimplexPartial A T terms)
      (constantPeanoBakerSimplexTerm A T terms) := rfl

/-! A square-zero constant generator is the first exact terminating ODE
case.  Its ordered-simplex expansion has no terms of degree two or higher,
so the finite transition is already the closed form `I + T A`. -/
theorem matrixPow_add_two_eq_zero_of_mul_self_eq_zero
    {dimension : Nat} (A : RatMatrix dimension)
    (hAA : matrixMul A A = matrixZero dimension) :
    forall n, matrixPow A (n + 2) = matrixZero dimension
  | 0 => by
      simp only [matrixPow]
      rw [matrixMul_identity_right, hAA]
  | n + 1 => by
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, matrixPow,
        matrixPow_add_two_eq_zero_of_mul_self_eq_zero A hAA n,
        matrixMul_zero_right]

theorem constantPeanoBakerSimplexPartial_add_two_eq_identity_add_scale_of_mul_self_eq_zero
    {dimension : Nat} (A : RatMatrix dimension) (T : Rat)
    (hAA : matrixMul A A = matrixZero dimension) :
    forall terms,
      constantPeanoBakerSimplexPartial A T (terms + 2) =
        matrixAdd (matrixIdentity dimension) (matrixScale T A)
  | 0 => by
      simp [constantPeanoBakerSimplexPartial,
        constantPeanoBakerSimplexTerm, matrixPow,
        matrixMul_identity_right, factorialRat, factorial]
      have hone : (1 : Rat) / 1 = 1 := by decide +kernel
      have hT : T / 1 = T := by
        have hinv : (1 : Rat)⁻¹ = 1 :=
          Rat.inv_eq_of_mul_eq_one (by decide +kernel)
        rw [Rat.div_def, hinv, Rat.mul_one]
      rw [hone, hT, matrixAdd_zero_left, matrixScale_one]
  | terms + 1 => by
      rw [constantPeanoBakerSimplexPartial_succ,
        constantPeanoBakerSimplexPartial_add_two_eq_identity_add_scale_of_mul_self_eq_zero
          A T hAA terms]
      have hpow := matrixPow_add_two_eq_zero_of_mul_self_eq_zero A hAA terms
      have hterm : constantPeanoBakerSimplexTerm A T (terms + 2) =
          matrixZero dimension := by
        unfold constantPeanoBakerSimplexTerm
        rw [hpow]
        funext i j
        simp [matrixScale, matrixZero]
      rw [hterm, matrixAdd_zero_right]

/-! ## Finite rotation-series core

The continuous rotation system is a later analytic construction.  Its
constant-coefficient Peano--Baker coefficients already have the familiar
finite even/odd split, which is the exact algebraic core of the eventual
comparison with cosine and sine. -/

namespace RotationSystem

/-- The counter-clockwise quarter-turn generator. -/
def generator : RatMatrix 2 :=
  fun i =>
    Fin.cases
      (fun j => Fin.cases 0 (fun _ => -1) j)
      (fun _ j => Fin.cases 1 (fun _ => 0) j)
      i

theorem generator_rowAbsSum (i : Fin 2) :
    matrixRowAbsSum generator i = 1 := by
  refine Fin.cases ?_ ?_ i
  · decide +kernel
  · intro j
    refine Fin.cases ?_ ?_ j
    · decide +kernel
    · intro k
      exact Fin.elim0 k

theorem affineGenerator_rowAbsSum_le (step : Rat) (i : Fin 2) :
    matrixRowAbsSum
        (matrixAdd (matrixIdentity 2) (matrixScale step generator)) i <=
      1 + qabs step := by
  have h := matrixRowAbsSum_affineStep_le (matrixScale step generator) i
  rw [matrixRowAbsSum_matrixScale, generator_rowAbsSum] at h
  simpa using h

theorem generator_columnAbsSum (j : Fin 2) :
    matrixColumnAbsSum generator j = 1 := by
  refine Fin.cases ?_ ?_ j
  · decide +kernel
  · intro i
    refine Fin.cases ?_ ?_ i
    · decide +kernel
    · intro k
      exact Fin.elim0 k

theorem affineGenerator_columnAbsSum_le (step : Rat) (j : Fin 2) :
    matrixColumnAbsSum
        (matrixAdd (matrixIdentity 2) (matrixScale step generator)) j <=
      1 + qabs step := by
  have h := matrixColumnAbsSum_affineStep_le (matrixScale step generator) j
  rw [matrixColumnAbsSum_matrixScale, generator_columnAbsSum] at h
  simpa using h

theorem rotationChronologicalProduct_rowAbsSum_le (step : Rat) :
    forall steps i,
      matrixRowAbsSum
          (chronologicalProduct (fun _ => matrixScale step generator) steps) i <=
        (1 + qabs step) ^ steps := by
  intro steps i
  apply chronologicalProduct_rowAbsSum_le_pow
    (fun _ => matrixScale step generator) (1 + qabs step)
  · intro n j
    exact affineGenerator_rowAbsSum_le step j
  · exact Rat.add_nonneg (by decide +kernel) (qabs_nonneg step)

theorem rotationChronologicalProduct_columnAbsSum_le (step : Rat) :
    forall steps j,
      matrixColumnAbsSum
          (chronologicalProduct (fun _ => matrixScale step generator) steps) j <=
        (1 + qabs step) ^ steps := by
  intro steps j
  apply chronologicalProduct_columnAbsSum_le_pow
    (fun _ => matrixScale step generator) (1 + qabs step)
  · intro n i
    exact affineGenerator_columnAbsSum_le step i
  · exact Rat.add_nonneg (by decide +kernel) (qabs_nonneg step)

theorem rotationChronologicalProduct_stateAbsSum_le (step : Rat)
    (steps : Nat) (x : RatVector 2) :
    vectorAbsSum
        (matrixApply
          (chronologicalProduct (fun _ => matrixScale step generator) steps) x) <=
      (1 + qabs step) ^ steps * vectorAbsSum x := by
  apply chronologicalProduct_stateAbsSum_le
    (fun _ => matrixScale step generator) (1 + qabs step)
  · intro n j
    exact affineGenerator_columnAbsSum_le step j
  · exact Rat.add_nonneg (by decide +kernel) (qabs_nonneg step)

/-- Squaring the rotation generator is minus the identity.  This is a closed
finite rational matrix calculation. -/
theorem generator_square :
    matrixMul generator generator = matrixScale (-1) (matrixIdentity 2) := by
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · decide +kernel
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      decide +kernel
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · decide +kernel
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      decide +kernel

/-- The matrix-power normalization of the preceding square identity. -/
theorem generator_pow_two :
    matrixPow generator 2 = matrixScale (-1) (matrixIdentity 2) := by
  change matrixMul generator (matrixMul generator (matrixIdentity 2)) =
    matrixScale (-1) (matrixIdentity 2)
  rw [matrixMul_identity_right]
  exact generator_square

/-- Even powers of the rotation generator are alternating scalar identities. -/
theorem generator_pow_even (k : Nat) :
    matrixPow generator (2 * k) =
      matrixScale ((-1 : Rat) ^ k) (matrixIdentity 2) := by
  induction k with
  | zero =>
      simp [matrixPow, matrixScale_one]
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 + 2 * k by omega]
      rw [matrixPow_add, generator_pow_two, ih]
      rw [matrixMul_matrixScale_right, matrixMul_identity_right,
        matrixScale_comp, Rat.pow_succ]

/-- Odd powers of the rotation generator are the same alternating scalar
times one quarter turn. -/
theorem generator_pow_odd (k : Nat) :
    matrixPow generator (2 * k + 1) =
      matrixScale ((-1 : Rat) ^ k) generator := by
  rw [matrixPow]
  rw [generator_pow_even]
  rw [matrixMul_matrixScale_right, matrixMul_identity_right]

/-- The even constant Peano--Baker coefficient for rotation has exactly the
alternating cosine-series matrix form. -/
theorem simplexTerm_even (T : Rat) (k : Nat) :
    constantPeanoBakerSimplexTerm generator T (2 * k) =
      matrixScale
        (T ^ (2 * k) / factorialRat (2 * k) * ((-1 : Rat) ^ k))
        (matrixIdentity 2) := by
  unfold constantPeanoBakerSimplexTerm
  rw [generator_pow_even, matrixScale_comp]

/-- The odd constant Peano--Baker coefficient for rotation has exactly the
alternating sine-series matrix form. -/
theorem simplexTerm_odd (T : Rat) (k : Nat) :
    constantPeanoBakerSimplexTerm generator T (2 * k + 1) =
      matrixScale
        (T ^ (2 * k + 1) / factorialRat (2 * k + 1) * ((-1 : Rat) ^ k))
        generator := by
  unfold constantPeanoBakerSimplexTerm
  rw [generator_pow_odd, matrixScale_comp]

/-- The degree-`2k` coefficient of the finite rotation polynomial. -/
def cosineCoefficient (T : Rat) (k : Nat) : Rat :=
  T ^ (2 * k) / factorialRat (2 * k) * ((-1 : Rat) ^ k)

/-- The degree-`2k+1` coefficient of the finite rotation polynomial. -/
def sineCoefficient (T : Rat) (k : Nat) : Rat :=
  T ^ (2 * k + 1) / factorialRat (2 * k + 1) * ((-1 : Rat) ^ k)

/-- An executable finite cosine-type prefix. -/
def cosinePrefix (T : Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => cosinePrefix T n + cosineCoefficient T n

/-- An executable finite sine-type prefix. -/
def sinePrefix (T : Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => sinePrefix T n + sineCoefficient T n

/-- The first `2n` constant Peano--Baker terms for the rotation system split
exactly into their cosine- and sine-type rational prefixes.  This is finite
matrix algebra only; it does not yet sum a continuous ODE or a complex raw
exponential. -/
theorem simplexPartial_even_split (T : Rat) (n : Nat) :
    constantPeanoBakerSimplexPartial generator T (2 * n) =
      matrixAdd
        (matrixScale (cosinePrefix T n) (matrixIdentity 2))
        (matrixScale (sinePrefix T n) generator) := by
  induction n with
  | zero =>
      simp only [constantPeanoBakerSimplexPartial, cosinePrefix, sinePrefix]
      funext i j
      unfold matrixZero matrixAdd matrixScale
      rw [Rat.zero_mul, Rat.zero_mul, Rat.zero_add]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      rw [constantPeanoBakerSimplexPartial_succ]
      rw [show 2 * n + 1 = (2 * n) + 1 by omega]
      rw [constantPeanoBakerSimplexPartial_succ, ih]
      rw [simplexTerm_even, simplexTerm_odd, matrixAdd_group_even_odd]
      rw [matrixAdd_scale_same, matrixAdd_scale_same]
      rfl

/-! The neighboring odd prefix is the same finite parity decomposition with
one additional even (cosine) coefficient.  Exposing both parities keeps the
finite ODE algebra aligned with the truncation index used by the power-series
and rotation evaluators. -/
theorem simplexPartial_odd_split (T : Rat) (n : Nat) :
    constantPeanoBakerSimplexPartial generator T (2 * n + 1) =
      matrixAdd
        (matrixScale (cosinePrefix T (n + 1)) (matrixIdentity 2))
        (matrixScale (sinePrefix T n) generator) := by
  rw [show 2 * n + 1 = (2 * n) + 1 by omega]
  rw [constantPeanoBakerSimplexPartial_succ]
  rw [simplexPartial_even_split, simplexTerm_even]
  have hcomm (A B : RatMatrix 2) : matrixAdd A B = matrixAdd B A := by
    funext i j
    unfold matrixAdd
    exact Rat.add_comm _ _
  rw [matrixAdd_assoc, hcomm
    (matrixScale (sinePrefix T n) generator)
    (matrixScale (T ^ (2 * n) / factorialRat (2 * n) * ((-1 : Rat) ^ n))
      (matrixIdentity 2)), ← matrixAdd_assoc, matrixAdd_scale_same]
  rfl

end RotationSystem

/-- The finite sum of a sampled matrix family over the first `steps` times. -/
def matrixSequenceSum {dimension : Nat} (B : Nat -> RatMatrix dimension) : Nat ->
    RatMatrix dimension
  | 0 => matrixZero dimension
  | n + 1 => matrixAdd (matrixSequenceSum B n) (B n)

theorem matrixSequenceSum_zero {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    matrixSequenceSum B 0 = matrixZero dimension := rfl

theorem matrixSequenceSum_succ {dimension : Nat} (B : Nat -> RatMatrix dimension)
    (steps : Nat) :
    matrixSequenceSum B (steps + 1) =
      matrixAdd (matrixSequenceSum B steps) (B steps) := rfl

/-- A sampled coefficient family whose every product of two samples vanishes.

This is the finite square-zero (and hence nilpotent) special case of the
Peano--Baker expansion.  It is intentionally stronger than mere pairwise
commutation: the strength makes all words of length at least two vanish by a
direct finite calculation. -/
def PairwiseProductZero {dimension : Nat} (B : Nat -> RatMatrix dimension) : Prop :=
  forall i j, matrixMul (B i) (B j) = matrixZero dimension

/-- Pairwise commutation of the sampled increments.  Unlike the square-zero
condition, this does not make higher Peano--Baker words vanish; it is the
finite algebra hypothesis behind the later commuting-coefficient formula. -/
def PairwiseCommuting {dimension : Nat} (B : Nat -> RatMatrix dimension) : Prop :=
  forall i j, matrixMul (B i) (B j) = matrixMul (B j) (B i)

theorem matrixMul_commutes_identity_add {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (hcomm : PairwiseCommuting B) (i j : Nat) :
    matrixMul (B i) (matrixAdd (matrixIdentity dimension) (B j)) =
      matrixMul (matrixAdd (matrixIdentity dimension) (B j)) (B i) := by
  rw [matrixMul_add_right, matrixMul_add_left, matrixMul_identity_right,
    matrixMul_identity_left, hcomm]

/-- Under pairwise commuting increments, each sample commutes with the finite
chronological transition accumulated from any number of earlier samples. -/
theorem matrixMul_commutes_chronologicalProduct {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (hcomm : PairwiseCommuting B) (i : Nat) :
    forall steps,
      matrixMul (B i) (chronologicalProduct B steps) =
        matrixMul (chronologicalProduct B steps) (B i)
  | 0 => by
      rw [chronologicalProduct, matrixMul_identity_right, matrixMul_identity_left]
  | steps + 1 => by
      rw [chronologicalProduct]
      rw [← matrixMul_assoc, matrixMul_commutes_identity_add B hcomm]
      rw [matrixMul_assoc]
      rw [matrixMul_commutes_chronologicalProduct B hcomm i steps]
      rw [← matrixMul_assoc]

theorem matrixMul_sequenceSum_eq_zero {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (hzero : PairwiseProductZero B) :
    forall i steps,
      matrixMul (B i) (matrixSequenceSum B steps) = matrixZero dimension
  | i, 0 => by
      rw [matrixSequenceSum_zero, matrixMul_zero_right]
  | i, steps + 1 => by
      rw [matrixSequenceSum_succ, matrixMul_add_right,
        matrixMul_sequenceSum_eq_zero B hzero i steps, hzero i steps,
        matrixAdd_zero_right]

/-- When all Euler increments are the same matrix `B`, time ordering reduces
to the finite power `(I + B)^N`. -/
theorem chronologicalProduct_constant {dimension : Nat} (B : RatMatrix dimension) :
    forall steps,
      chronologicalProduct (fun _ => B) steps =
        matrixPow (matrixAdd (matrixIdentity dimension) B) steps
  | 0 => rfl
  | steps + 1 => by
      change
        matrixMul (matrixAdd (matrixIdentity dimension) B)
            (chronologicalProduct (fun _ => B) steps) =
          matrixMul (matrixAdd (matrixIdentity dimension) B)
            (matrixPow (matrixAdd (matrixIdentity dimension) B) steps)
      rw [chronologicalProduct_constant B steps]

theorem peanoBakerDiscreteSum_succ {dimension : Nat} (B : Nat -> RatMatrix dimension)
    (steps : Nat) :
    peanoBakerDiscreteSum B (steps + 1) =
      matrixAdd (peanoBakerDiscreteSum B steps)
        (matrixMul (B steps) (peanoBakerDiscreteSum B steps)) := by
  unfold peanoBakerDiscreteSum
  rw [orderedIndexWords, List.map_append, matrixListSum_append]
  have hmap :
      ((orderedIndexWords steps).map (fun word => steps :: word)).map (timeOrderedProduct B) =
        ((orderedIndexWords steps).map (timeOrderedProduct B)).map (matrixMul (B steps)) := by
    rw [List.map_map, List.map_map]
    rfl
  rw [hmap]
  rw [← matrixMul_matrixListSum]

theorem chronologicalProduct_succ {dimension : Nat} (B : Nat -> RatMatrix dimension)
    (steps : Nat) :
    chronologicalProduct B (steps + 1) =
      matrixAdd (chronologicalProduct B steps)
        (matrixMul (B steps) (chronologicalProduct B steps)) := by
  change matrixMul (matrixAdd (matrixIdentity dimension) (B steps))
      (chronologicalProduct B steps) = _
  rw [matrixMul_add_left, matrixMul_identity_left]

/-- The finite Peano--Baker identity, kept as a named proposition so that
continuous constructions can depend on the algebraic result separately. -/
def DiscretePeanoBakerExpansion {dimension : Nat} (B : Nat -> RatMatrix dimension) : Prop :=
  forall steps, chronologicalProduct B steps = peanoBakerDiscreteSum B steps

theorem discretePeanoBakerExpansion {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    DiscretePeanoBakerExpansion B := by
  intro steps
  induction steps with
  | zero =>
      change matrixIdentity dimension = matrixAdd (matrixIdentity dimension) (matrixZero dimension)
      funext i j
      exact (Rat.add_zero _).symm
  | succ steps ih =>
      rw [chronologicalProduct_succ, ih, peanoBakerDiscreteSum_succ]

/-- Constant Euler increments give the familiar finite constant-coefficient
Peano--Baker formula `(I + B)^N`. -/
theorem peanoBakerDiscreteSum_constant {dimension : Nat} (B : RatMatrix dimension)
    (steps : Nat) :
    peanoBakerDiscreteSum (fun _ => B) steps =
      matrixPow (matrixAdd (matrixIdentity dimension) B) steps := by
  rw [← discretePeanoBakerExpansion]
  exact chronologicalProduct_constant B steps

/-- The zero coefficient has the identity as its finite Peano--Baker state
transition at every number of sample steps. -/
theorem peanoBakerDiscreteSum_zeroCoefficient {dimension : Nat} (steps : Nat) :
    peanoBakerDiscreteSum (fun _ => matrixZero dimension) steps =
      matrixIdentity dimension := by
  rw [peanoBakerDiscreteSum_constant]
  rw [matrixAdd_zero_right, matrixPow_identity]

/-- In the square-zero specialization, every Peano--Baker word of length at
least two is zero, so the finite state transition is exactly the identity plus
the finite sum of the sampled increments. -/
theorem chronologicalProduct_pairwiseProductZero {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (hzero : PairwiseProductZero B) :
    forall steps,
      chronologicalProduct B steps =
        matrixAdd (matrixIdentity dimension) (matrixSequenceSum B steps)
  | 0 => by
      exact (matrixAdd_zero_right _).symm
  | steps + 1 => by
      rw [chronologicalProduct_succ,
        chronologicalProduct_pairwiseProductZero B hzero steps,
        matrixMul_add_right, matrixMul_identity_right,
        matrixMul_sequenceSum_eq_zero B hzero, matrixAdd_zero_right]
      exact matrixAdd_assoc _ _ _

theorem peanoBakerDiscreteSum_pairwiseProductZero {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (hzero : PairwiseProductZero B)
    (steps : Nat) :
    peanoBakerDiscreteSum B steps =
      matrixAdd (matrixIdentity dimension) (matrixSequenceSum B steps) := by
  rw [← discretePeanoBakerExpansion]
  exact chronologicalProduct_pairwiseProductZero B hzero steps

/-! A constant square-zero increment is the discrete analogue of the exact
constant nilpotent flow above.  The finite sum keeps the mesh count and step
size visible, rather than hiding them in a limiting exponential. -/
theorem matrixSequenceSum_constant_scale {dimension : Nat}
    (A : RatMatrix dimension) (step : Rat) (steps : Nat) :
    matrixSequenceSum (fun _ => matrixScale step A) steps =
      matrixScale ((steps : Rat) * step) A := by
  induction steps with
  | zero =>
      funext i j
      simp [matrixSequenceSum, matrixScale, matrixZero]
  | succ steps ih =>
      rw [matrixSequenceSum_succ, ih, matrixAdd_scale_same]
      congr 1
      push_cast
      grind [Rat.add_mul]

theorem chronologicalProduct_constant_square_zero
    {dimension : Nat} (A : RatMatrix dimension) (step : Rat)
    (hAA : matrixMul A A = matrixZero dimension) (steps : Nat) :
    chronologicalProduct (fun _ => matrixScale step A) steps =
      matrixAdd (matrixIdentity dimension)
        (matrixScale ((steps : Rat) * step) A) := by
  rw [chronologicalProduct_pairwiseProductZero]
  · rw [matrixSequenceSum_constant_scale]
  · intro i j
    rw [matrixMul_matrixScale_left, matrixMul_matrixScale_right, hAA]
    funext i j
    simp [matrixScale, matrixZero]

/-! With a uniform mesh, the square-zero flow is already exact at every
positive finite mesh size.  This is the finite ODE analogue of the fact that
the exponential truncates after its linear term; no mesh limit is involved. -/
theorem chronologicalProduct_constant_square_zero_uniform_step
    {dimension : Nat} (A : RatMatrix dimension) (T : Rat) (steps : Nat)
    (hsteps : 0 < steps) (hAA : matrixMul A A = matrixZero dimension) :
    chronologicalProduct
        (fun _ => matrixScale (T / ((steps : Nat) : Rat)) A) steps =
      matrixAdd (matrixIdentity dimension) (matrixScale T A) := by
  rw [chronologicalProduct_constant_square_zero A
    (T / ((steps : Nat) : Rat)) hAA steps]
  have hs : ((steps : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hsteps)
  have hscale : ((steps : Nat) : Rat) *
      (T / ((steps : Nat) : Rat)) = T := by
    rw [Rat.div_def]
    have hcancel := Rat.mul_inv_cancel ((steps : Nat) : Rat) hs
    grind [Rat.mul_assoc, Rat.mul_comm]
  rw [hscale]

@[simp] theorem orderedIndexWords_zero : orderedIndexWords 0 = [[]] := rfl

@[simp] theorem orderedIndexWords_one : orderedIndexWords 1 = [[], [0]] := rfl

@[simp] theorem orderedIndexWords_two :
    orderedIndexWords 2 = [[], [0], [1], [1, 0]] := rfl

@[simp] theorem timeOrderedProduct_nil {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    timeOrderedProduct B [] = matrixIdentity dimension := rfl

/-- The enumerator has exactly `2^steps` finite terms. -/
theorem orderedIndexWords_length (steps : Nat) :
    (orderedIndexWords steps).length = 2 ^ steps := by
  induction steps with
  | zero => decide +kernel
  | succ steps ih =>
      rw [orderedIndexWords, List.length_append, List.length_map, ih]
      omega

/-- The first three Peano--Baker expansions are executable definitions. They
exhibit the necessary noncommutative order used by the general theorem. -/
@[simp] theorem peanoBakerDiscreteSum_zero {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    peanoBakerDiscreteSum B 0 =
      matrixAdd (matrixIdentity dimension) (matrixZero dimension) := rfl

@[simp] theorem peanoBakerDiscreteSum_one {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    peanoBakerDiscreteSum B 1 = matrixAdd (matrixIdentity dimension)
      (matrixAdd (matrixMul (B 0) (matrixIdentity dimension)) (matrixZero dimension)) := rfl

@[simp] theorem peanoBakerDiscreteSum_two {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    peanoBakerDiscreteSum B 2 =
      matrixAdd (matrixIdentity dimension)
        (matrixAdd (matrixMul (B 0) (matrixIdentity dimension))
          (matrixAdd (matrixMul (B 1) (matrixIdentity dimension))
            (matrixAdd (matrixMul (B 1)
              (matrixMul (B 0) (matrixIdentity dimension))) (matrixZero dimension)))) := rfl

/-- A finite vector of interval functions sharing one rational domain. This
keeps the represented component computations explicit while giving linear
systems a common input interval. -/
structure FunctionVectorOnInterval (dimension : Nat) (lower upper : Rat) where
  component : Fin dimension -> FunctionOnInterval
  component_lower : forall i, (component i).lower = lower
  component_upper : forall i, (component i).upper = upper

namespace FunctionVectorOnInterval

/-- Embed a scalar interval function as a one-coordinate vector function.
This is the standard bridge from scalar ODE certificates, including
`f' = f`, to the finite-dimensional linear-system comparison theorem. -/
def ofScalar (f : FunctionOnInterval) :
    FunctionVectorOnInterval 1 f.lower f.upper where
  component := Fin.cases f (fun i => Fin.elim0 i)
  component_lower := by
    intro i
    refine Fin.cases rfl ?_ i
    intro j
    exact Fin.elim0 j
  component_upper := by
    intro i
    refine Fin.cases rfl ?_ i
    intro j
    exact Fin.elim0 j

/-- Embed a scalar evaluator onto an explicitly chosen common domain. This is
useful when a comparison theorem carries endpoint equalities as hypotheses
rather than definitional equalities. -/
def ofScalarOnDomain (f : FunctionOnInterval) (lower upper : Rat)
    (hlower : f.lower = lower) (hupper : f.upper = upper) :
    FunctionVectorOnInterval 1 lower upper where
  component := Fin.cases f (fun i => Fin.elim0 i)
  component_lower := by
    intro i
    refine Fin.cases hlower ?_ i
    intro j
    exact Fin.elim0 j
  component_upper := by
    intro i
    refine Fin.cases hupper ?_ i
    intro j
    exact Fin.elim0 j

/-- A scalar represented derivative certificate lifts coordinatewise to the
one-dimensional vector interface. -/
def derivativeEvidenceOfScalar
    {f df : FunctionOnInterval}
    (D : HasDerivativeOnInterval f df) :
    forall i : Fin 1,
      HasDerivativeOnInterval
        ((ofScalar f).component i) ((ofScalar df).component i) := by
  intro i
  refine Fin.cases D ?_ i
  intro j
  exact Fin.elim0 j

/-- Lift a scalar derivative certificate when the vector domain is expressed
using explicit endpoint equalities. -/
def derivativeEvidenceOfScalarOnDomain
    {f df : FunctionOnInterval} {lower upper : Rat}
    (hfLower : f.lower = lower) (hfUpper : f.upper = upper)
    (hdfLower : df.lower = lower) (hdfUpper : df.upper = upper)
    (D : HasDerivativeOnInterval f df) :
    forall i : Fin 1,
      HasDerivativeOnInterval
        ((ofScalarOnDomain f lower upper hfLower hfUpper).component i)
        ((ofScalarOnDomain df lower upper hdfLower hdfUpper).component i) := by
  intro i
  refine Fin.cases D ?_ i
  intro j
  exact Fin.elim0 j

/-- Restrict every coordinate of a represented vector function to the same
closed rational subinterval. -/
def restrict {dimension : Nat} {lower upper : Rat}
    (F : FunctionVectorOnInterval dimension lower upper)
    (a b : Rat) (hlo : lower <= a) (hab : a <= b)
    (hhi : b <= upper) : FunctionVectorOnInterval dimension a b where
  component := fun i => FunctionOnInterval.restrict (F.component i) a b
    (by rw [F.component_lower i]; exact hlo) hab
    (by rw [F.component_upper i]; exact hhi)
  component_lower := fun _ => rfl
  component_upper := fun _ => rfl

/-- Restrict a family of coordinate derivative certificates together with
their vector functions. The rational computations are preserved coordinate
by coordinate, so local ODE comparison can reuse the global derivative
evidence on each partition cell. -/
def restrictDerivatives
    {dimension : Nat} {lower upper : Rat}
    {F DF : FunctionVectorOnInterval dimension lower upper}
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (a b : Rat) (hlo : lower <= a) (hab : a <= b)
    (hhi : b <= upper) :
    forall i, HasDerivativeOnInterval
      ((FunctionVectorOnInterval.restrict F a b hlo hab hhi).component i)
      ((FunctionVectorOnInterval.restrict DF a b hlo hab hhi).component i) := by
  intro i
  have hflo : (F.component i).lower <= a := by
    rw [F.component_lower i]
    exact hlo
  have fhhi : b <= (F.component i).upper := by
    rw [F.component_upper i]
    exact hhi
  exact (D i).restrict a b hflo hab fhhi

theorem domainAt {dimension : Nat} {lower upper : Rat}
    (F : FunctionVectorOnInterval dimension lower upper)
    (i : Fin dimension) (x : Rat)
    (hx : inDomainInterval lower upper x) :
    inDomainInterval (F.component i).lower (F.component i).upper x := by
  rw [F.component_lower i, F.component_upper i]
  exact hx

def computeBoxes {dimension : Nat} {lower upper : Rat}
    (F : FunctionVectorOnInterval dimension lower upper)
    (x : Rat) (hx : inDomainInterval lower upper x)
    (stage : Fin dimension -> Nat) : Fin dimension -> QInterval :=
  fun i => (F.component i).compute x (F.domainAt i x hx) (stage i)

def lowerSample {dimension : Nat} {lower upper : Rat}
    (F : FunctionVectorOnInterval dimension lower upper)
    (x : Rat) (hx : inDomainInterval lower upper x)
    (stage : Fin dimension -> Nat) : RatVector dimension :=
  fun i => (F.computeBoxes x hx stage i).lo

/-- Unfold a vector sample to the actual lower endpoint of the component's
represented raw value. This is the bridge used when a finite ODE estimate is
fed into the cofinal-lower-endpoint equality theorem. -/
theorem lowerSample_eq_component_raw_lower
    {dimension : Nat} {lower upper : Rat}
    (F : FunctionVectorOnInterval dimension lower upper)
    (x : Rat) (hx : inDomainInterval lower upper x)
    (stage : Fin dimension -> Nat) (i : Fin dimension) :
    F.lowerSample x hx stage i =
      ((PartialRealFunRaw.apply (F.component i).raw
        (F.component i).valid_on x
        ((F.component i).defined_on x (F.domainAt i x hx))).compute
          (stage i)).lo := by
  rfl

/-- The lower sample is invariant under replacing its rational input by an
equal one, even when the two interval-membership proofs were constructed by
different mesh arguments. -/
theorem lowerSample_congr_input
    {dimension : Nat} {lower upper : Rat}
    (F : FunctionVectorOnInterval dimension lower upper)
    (x y : Rat)
    (hx : inDomainInterval lower upper x)
    (hy : inDomainInterval lower upper y)
    (stage : Fin dimension -> Nat)
    (hxy : x = y) :
    F.lowerSample x hx stage = F.lowerSample y hy stage := by
  cases hxy
  rfl

end FunctionVectorOnInterval

/-- A cofinal family of finite vector comparisons between two represented
vector functions. `stageF` and `stageG` expose the actual raw interval stages
of each endpoint sample; `finite_comparison` is the quantitative vector
bound obtained from an ODE mesh estimate. The refinement field is the
function-specific schedule that simultaneously makes those stages cofinal
and the finite error smaller than any requested rational tolerance. -/
structure CofinalMeshLowerComparison
    {dimension : Nat} {lower upper : Rat}
    (F G : FunctionVectorOnInterval dimension lower upper) where
  stageF : (x : Rat) -> inDomainInterval lower upper x -> Nat -> Fin dimension -> Nat
  stageG : (x : Rat) -> inDomainInterval lower upper x -> Nat -> Fin dimension -> Nat
  error : (x : Rat) -> inDomainInterval lower upper x -> Nat -> Rat
  finite_comparison : forall x (hx : inDomainInterval lower upper x) k,
    vectorAbsSum (vectorSub
      (F.lowerSample x hx (fun i => stageF x hx k i))
      (G.lowerSample x hx (fun i => stageG x hx k i))) <= error x hx k
  refine : forall x (hx : inDomainInterval lower upper x)
      (i : Fin dimension) n m (eps : QPos),
    exists k, n <= stageF x hx k i /\ m <= stageG x hx k i /\
      error x hx k <= eps.val

namespace CofinalMeshLowerComparison

/-- Cofinal finite vector mesh comparisons prove represented equality of
every coordinate function. The proof uses only the vector error estimate,
the actual raw stages sampled by each mesh, and validity of the raw values;
all differential and coefficient analysis is isolated in the construction
of the certificate. -/
theorem componentwise_equivalent
    {dimension : Nat} {lower upper : Rat}
    {F G : FunctionVectorOnInterval dimension lower upper}
    (comparison : CofinalMeshLowerComparison F G) :
    forall i, FunctionOnInterval.Equivalent (F.component i) (G.component i) := by
  intro i
  apply FunctionOnInterval.equivalent_of_cofinal_lower_endpoint_closeness
  · rw [F.component_lower, G.component_lower]
  · rw [F.component_upper, G.component_upper]
  · intro x hxF hxG n m eps
    have hx : inDomainInterval lower upper x := by
      change (F.component i).lower <= x /\ x <= (F.component i).upper at hxF
      change lower <= x /\ x <= upper
      rw [F.component_lower i, F.component_upper i] at hxF
      exact hxF
    obtain ⟨k, hn, hm, herr⟩ := comparison.refine x hx i n m eps
    have hFsample := FunctionVectorOnInterval.lowerSample_eq_component_raw_lower
      F x hx (fun j => comparison.stageF x hx k j) i
    have hGsample := FunctionVectorOnInterval.lowerSample_eq_component_raw_lower
      G x hx (fun j => comparison.stageG x hx k j) i
    have hcomponent := vectorDifference_component_le
      (F.lowerSample x hx (fun j => comparison.stageF x hx k j))
      (G.lowerSample x hx (fun j => comparison.stageG x hx k j)) i
    have hmesh := comparison.finite_comparison x hx k
    refine ⟨comparison.stageF x hx k i, comparison.stageG x hx k i, hn, hm, ?_⟩
    rw [← hFsample, ← hGsample]
    exact Rat.le_trans (Rat.le_trans hcomponent hmesh) herr

end CofinalMeshLowerComparison

/-- Common-domain input data for the continuous linear system
`x' = A(t)x+b(t)`.  Entries are the existing interval-certified scalar
functions, so no completed real-valued function space is assumed. -/
structure IntervalLinearSystem (dimension : Nat) (lower upper : Rat) where
  coefficient : Fin dimension -> Fin dimension -> FunctionOnInterval
  forcing : Fin dimension -> FunctionOnInterval
  coefficient_interval : forall i j,
    (coefficient i j).lower = lower /\ (coefficient i j).upper = upper
  forcing_interval : forall i,
    (forcing i).lower = lower /\ (forcing i).upper = upper

/-! Computable regularity data for the entries of a continuous linear system.
Keep the evaluators as data, rather than hiding them under `Nonempty`: the
continuous Peano--Baker construction must run those interval evaluators to
obtain rational enclosures on each simplex cell. -/
structure IntervalLinearSystem.CoefficientsRegular
    (system : IntervalLinearSystem dimension lower upper) where
  coefficient : forall i j, IntervalRegularOn (system.coefficient i j)
  forcing : forall i, IntervalRegularOn (system.forcing i)

namespace IntervalLinearSystem.CoefficientsRegular

/-- A whole-domain rational enclosure for one coefficient entry.  The box is
computed by the supplied regularity evaluator on the full rational interval;
it is therefore available before constructing any Picard or Peano--Baker
term. -/
def coefficientEnclosure
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (i j : Fin dimension) : QInterval :=
  let F := system.coefficient i j
  let I : QInterval := {lo := lower, hi := upper}
  regular.coefficient i j |>.evalInterval I (by
    dsimp [I]
    rw [(system.coefficient_interval i j).1,
      (system.coefficient_interval i j).2]
    exact ⟨Rat.le_refl, hab, Rat.le_refl⟩) 0

/-- Every represented sample of a coefficient is contained in its computed
whole-domain box, at every value precision. -/
theorem coefficientEnclosure_contains
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (i j : Fin dimension) {x : Rat} (hx : lower <= x /\ x <= upper)
    (n : Nat) :
    QInterval.ContainsInterval (regular.coefficientEnclosure hab i j)
      ((system.coefficient i j).compute x
        (by
          rw [(system.coefficient_interval i j).1,
            (system.coefficient_interval i j).2]
          exact hx) n) := by
  have hI : subintervalOf {lo := lower, hi := upper}
      (system.coefficient i j).lower (system.coefficient i j).upper := by
    rcases system.coefficient_interval i j with ⟨hl, hu⟩
    exact ⟨by rw [hl]; exact Rat.le_refl, hab, by rw [hu]; exact Rat.le_refl⟩
  have hxF : inDomainInterval (system.coefficient i j).lower
      (system.coefficient i j).upper x := by
    rw [(system.coefficient_interval i j).1,
      (system.coefficient_interval i j).2]
    exact hx
  have hbox := (regular.coefficient i j).contains_point_values
    {lo := lower, hi := upper} hI x hxF 0 hx.1 hx.2
  have hvalid := (system.coefficient i j).valid_on x
    ((system.coefficient i j).defined_on x hxF)
  have hnest := hvalid.2.1 0 n (Nat.zero_le n)
  refine ⟨?_, ?_⟩
  · exact Rat.le_trans hbox.1 hnest.1
  · exact Rat.le_trans hnest.2.2 hbox.2

/-- The same full-domain enclosure for a forcing coordinate. -/
def forcingEnclosure
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (i : Fin dimension) : QInterval :=
  let F := system.forcing i
  let I : QInterval := {lo := lower, hi := upper}
  regular.forcing i |>.evalInterval I (by
    dsimp [I]
    rw [(system.forcing_interval i).1,
      (system.forcing_interval i).2]
    exact ⟨Rat.le_refl, hab, Rat.le_refl⟩) 0

/-- A symmetric rational magnitude bound derived from a whole-domain interval
box. Using the sum of endpoint magnitudes avoids deciding whether the box
crosses zero. -/
def intervalMagnitudeBound (I : QInterval) : Rat :=
  qabs I.lo + qabs I.hi

theorem intervalMagnitudeBound_nonneg (I : QInterval) :
    0 <= intervalMagnitudeBound I :=
  Rat.add_nonneg (qabs_nonneg I.lo) (qabs_nonneg I.hi)

theorem intervalMagnitudeBound_contains {I J : QInterval}
    (h : QInterval.ContainsInterval I J) (hJ : J.lo <= J.hi) :
    -intervalMagnitudeBound I <= J.lo /\
      J.lo <= intervalMagnitudeBound I /\
      -intervalMagnitudeBound I <= J.hi /\
      J.hi <= intervalMagnitudeBound I := by
  rcases h with ⟨hlo, hhi⟩
  have hIlo : -intervalMagnitudeBound I <= I.lo := by
    dsimp [intervalMagnitudeBound]
    have hnonneg := qabs_nonneg I.hi
    have htriangle := neg_qabs_le_self I.lo
    grind only [Rat.sub_eq_add_neg]
  have hIhi : I.hi <= intervalMagnitudeBound I := by
    dsimp [intervalMagnitudeBound]
    have hnonneg := qabs_nonneg I.lo
    have htriangle := self_le_qabs I.hi
    grind only [Rat.sub_eq_add_neg]
  have hJlo : -intervalMagnitudeBound I <= J.lo :=
    Rat.le_trans hIlo hlo
  have hJhi : J.hi <= intervalMagnitudeBound I :=
    Rat.le_trans hhi hIhi
  exact ⟨hJlo,
    Rat.le_trans hJ hJhi,
    Rat.le_trans hJlo hJ,
    hJhi⟩

theorem forcingEnclosure_contains
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (i : Fin dimension) {x : Rat} (hx : lower <= x /\ x <= upper)
    (n : Nat) :
    QInterval.ContainsInterval (regular.forcingEnclosure hab i)
      ((system.forcing i).compute x
        (by
          rw [(system.forcing_interval i).1,
            (system.forcing_interval i).2]
          exact hx) n) := by
  have hI : subintervalOf {lo := lower, hi := upper}
      (system.forcing i).lower (system.forcing i).upper := by
    rcases system.forcing_interval i with ⟨hl, hu⟩
    exact ⟨by rw [hl]; exact Rat.le_refl, hab, by rw [hu]; exact Rat.le_refl⟩
  have hxF : inDomainInterval (system.forcing i).lower
      (system.forcing i).upper x := by
    rw [(system.forcing_interval i).1,
      (system.forcing_interval i).2]
    exact hx
  have hbox := (regular.forcing i).contains_point_values
    {lo := lower, hi := upper} hI x hxF 0 hx.1 hx.2
  have hvalid := (system.forcing i).valid_on x
    ((system.forcing i).defined_on x hxF)
  have hnest := hvalid.2.1 0 n (Nat.zero_le n)
  refine ⟨?_, ?_⟩
  · exact Rat.le_trans hbox.1 hnest.1
  · exact Rat.le_trans hnest.2.2 hbox.2

theorem coefficient_sample_endpoints_bounded
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (i j : Fin dimension) {x : Rat} (hx : lower <= x /\ x <= upper)
    (n : Nat) :
    -intervalMagnitudeBound (regular.coefficientEnclosure hab i j) <=
        ((system.coefficient i j).compute x
          (by
            rw [(system.coefficient_interval i j).1,
              (system.coefficient_interval i j).2]
            exact hx) n).lo /\
      qabs (((system.coefficient i j).compute x
          (by
            rw [(system.coefficient_interval i j).1,
              (system.coefficient_interval i j).2]
            exact hx) n).lo) <=
        intervalMagnitudeBound (regular.coefficientEnclosure hab i j) /\
      -intervalMagnitudeBound (regular.coefficientEnclosure hab i j) <=
        ((system.coefficient i j).compute x
          (by
            rw [(system.coefficient_interval i j).1,
              (system.coefficient_interval i j).2]
            exact hx) n).hi /\
      qabs (((system.coefficient i j).compute x
          (by
            rw [(system.coefficient_interval i j).1,
              (system.coefficient_interval i j).2]
            exact hx) n).hi) <=
        intervalMagnitudeBound (regular.coefficientEnclosure hab i j) := by
  let hdomain : inDomainInterval (system.coefficient i j).lower
      (system.coefficient i j).upper x := by
    rw [(system.coefficient_interval i j).1,
      (system.coefficient_interval i j).2]
    exact hx
  have hbox := regular.coefficientEnclosure_contains hab i j hx n
  have hvalid := (system.coefficient i j).valid_on x
    ((system.coefficient i j).defined_on x hdomain)
  have hordered : ((system.coefficient i j).compute x
      (by
        rw [(system.coefficient_interval i j).1,
          (system.coefficient_interval i j).2]
        exact hx) n).lo <= ((system.coefficient i j).compute x
      (by
        rw [(system.coefficient_interval i j).1,
          (system.coefficient_interval i j).2]
        exact hx) n).hi :=
    (hvalid.2.1 n n (Nat.le_refl n)).2.1
  have hbounds := intervalMagnitudeBound_contains hbox hordered
  refine ⟨hbounds.1, ?_⟩
  constructor
  · exact qabs_le_of_bounds hbounds.1 hbounds.2.1
  · constructor
    · exact hbounds.2.2.1
    · exact qabs_le_of_bounds hbounds.2.2.1 hbounds.2.2.2

/-- A single computable rational bound for every coefficient entry, obtained
by summing the magnitude bounds of the whole-domain interval enclosures. The
sum is deliberately used in place of a finite maximum so the definition
works constructively and needs no comparison decision on represented reals. -/
def coefficientEntryBound
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper) : Rat :=
  finiteSum (fun i => finiteSum (fun j =>
    intervalMagnitudeBound (regular.coefficientEnclosure hab i j)))

theorem coefficientEnclosure_magnitude_le_entryBound
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (i j : Fin dimension) :
    intervalMagnitudeBound (regular.coefficientEnclosure hab i j) <=
      regular.coefficientEntryBound hab := by
  unfold coefficientEntryBound
  exact Rat.le_trans
    (finiteSum_term_le _
      (fun j => intervalMagnitudeBound_nonneg
        (regular.coefficientEnclosure hab i j)) j)
    (finiteSum_term_le _
      (fun i => finiteSum_nonneg (fun j => intervalMagnitudeBound_nonneg
        (regular.coefficientEnclosure hab i j))) i)

/-- Every endpoint of every represented coefficient sample is bounded by the
single rational coefficient constant. This is the entrywise hypothesis used
by the finite matrix growth and Euler comparison estimates. -/
theorem coefficient_sample_endpoints_le_entryBound
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (i j : Fin dimension) {x : Rat} (hx : lower <= x /\ x <= upper)
    (n : Nat) :
    qabs (((system.coefficient i j).compute x
      (by
        rw [(system.coefficient_interval i j).1,
          (system.coefficient_interval i j).2]
        exact hx) n).lo) <= regular.coefficientEntryBound hab /\
    qabs (((system.coefficient i j).compute x
      (by
        rw [(system.coefficient_interval i j).1,
          (system.coefficient_interval i j).2]
        exact hx) n).hi) <= regular.coefficientEntryBound hab := by
  have h := regular.coefficient_sample_endpoints_bounded hab i j hx n
  have hbound := regular.coefficientEnclosure_magnitude_le_entryBound hab i j
  exact ⟨Rat.le_trans h.2.1 hbound, Rat.le_trans h.2.2.2 hbound⟩

/-- A computable global bound for the forcing vector, again obtained by
summing the magnitude bounds of its whole-domain interval boxes. -/
def forcingVectorBound
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper) : Rat :=
  finiteSum (fun i => intervalMagnitudeBound (regular.forcingEnclosure hab i))

theorem forcingEnclosure_magnitude_le_vectorBound
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (i : Fin dimension) :
    intervalMagnitudeBound (regular.forcingEnclosure hab i) <=
      regular.forcingVectorBound hab := by
  unfold forcingVectorBound
  exact finiteSum_term_le _
    (fun i => intervalMagnitudeBound_nonneg
      (regular.forcingEnclosure hab i)) i

/-- Every endpoint of a represented forcing sample is bounded by the
computed global forcing constant. -/
theorem forcing_sample_endpoints_le_vectorBound
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (i : Fin dimension) {x : Rat} (hx : lower <= x /\ x <= upper)
    (n : Nat) :
    qabs (((system.forcing i).compute x
      (by
        rw [(system.forcing_interval i).1,
          (system.forcing_interval i).2]
        exact hx) n).lo) <= regular.forcingVectorBound hab /\
    qabs (((system.forcing i).compute x
      (by
        rw [(system.forcing_interval i).1,
          (system.forcing_interval i).2]
        exact hx) n).hi) <= regular.forcingVectorBound hab := by
  have hbox := regular.forcingEnclosure_contains hab i hx n
  let sample := (system.forcing i).compute x
    (by
      rw [(system.forcing_interval i).1,
        (system.forcing_interval i).2]
      exact hx) n
  have hvalid := (system.forcing i).valid_on x
    ((system.forcing i).defined_on x (by
      rw [(system.forcing_interval i).1,
        (system.forcing_interval i).2]
      exact hx))
  have hordered : sample.lo <= sample.hi :=
    (hvalid.2.1 n n (Nat.le_refl n)).2.1
  have hbounds := intervalMagnitudeBound_contains hbox hordered
  have hbound := regular.forcingEnclosure_magnitude_le_vectorBound hab i
  refine ⟨?_, ?_⟩
  · exact Rat.le_trans
      (qabs_le_of_bounds hbounds.1 hbounds.2.1) hbound
  · exact Rat.le_trans
      (qabs_le_of_bounds hbounds.2.2.1 hbounds.2.2.2) hbound

/-- The finite rational matrix sampled from a continuous coefficient system
at a rational time. Each entry is the lower endpoint of its certified raw
value at the requested precision. -/
def sampleCoefficientMatrix
    {dimension : Nat} {lower upper : Rat}
    (system : IntervalLinearSystem dimension lower upper)
    (x : Rat) (hx : lower <= x /\ x <= upper) (stage : Nat) :
    RatMatrix dimension :=
  fun i j => (system.coefficient i j).compute x
    (by
      rw [(system.coefficient_interval i j).1,
        (system.coefficient_interval i j).2]
      exact hx) stage |>.lo

/-- The finite rational forcing vector sampled at a rational time. -/
def sampleForcingVector
    {dimension : Nat} {lower upper : Rat}
    (system : IntervalLinearSystem dimension lower upper)
    (x : Rat) (hx : lower <= x /\ x <= upper) (stage : Nat) :
    RatVector dimension :=
  fun i => (system.forcing i).compute x
    (by
      rw [(system.forcing_interval i).1,
        (system.forcing_interval i).2]
      exact hx) stage |>.lo

/-- Every entry of the sampled coefficient matrix obeys the executable
whole-domain coefficient bound. -/
theorem sampleCoefficientMatrix_entryBound
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (x : Rat) (hx : lower <= x /\ x <= upper) (stage : Nat)
    (i j : Fin dimension) :
    qabs (sampleCoefficientMatrix system x hx stage i j) <=
      regular.coefficientEntryBound hab := by
  exact (regular.coefficient_sample_endpoints_le_entryBound hab i j hx stage).1

/-- Every coordinate of the sampled forcing vector obeys the executable
whole-domain forcing bound. -/
theorem sampleForcingVector_componentBound
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (x : Rat) (hx : lower <= x /\ x <= upper) (stage : Nat)
    (i : Fin dimension) :
    qabs (sampleForcingVector system x hx stage i) <=
      regular.forcingVectorBound hab := by
  exact (regular.forcing_sample_endpoints_le_vectorBound hab i hx stage).1

/-- Whole-domain column growth bound for every sampled coefficient matrix.
It is explicit in the dimension and the interval-evaluated coefficient data,
and is ready to use in the Euler/Peano--Baker factorial estimates. -/
theorem sampleCoefficientMatrix_columnBound
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (x : Rat) (hx : lower <= x /\ x <= upper) (stage : Nat)
    (j : Fin dimension) :
    matrixColumnAbsSum (sampleCoefficientMatrix system x hx stage) j <=
      finiteSum (fun _ : Fin dimension => regular.coefficientEntryBound hab) := by
  exact matrixColumnAbsSum_le_of_entry_bound
    (sampleCoefficientMatrix system x hx stage)
    (regular.coefficientEntryBound hab)
    (fun i j => regular.sampleCoefficientMatrix_entryBound hab x hx stage i j) j

/-- The computable finite Euler discretization of a regular linear system on
an explicitly supplied rational node sequence. This is a genuine solver for
each finite mesh: its state at every node is a rational vector obtained by
the project-local recurrence, and its coefficients come directly from the
system's interval-certified rational samplers. -/
def eulerDiscretization
    {dimension : Nat} {lower upper : Rat}
    (system : IntervalLinearSystem dimension lower upper)
    (nodes : Nat -> Rat)
    (nodeMem : forall n, lower <= nodes n /\ nodes n <= upper)
    (step : Rat) (stage : Nat) : DiscreteLinearSystem dimension where
  step := fun n => matrixAdd (matrixIdentity dimension)
    (matrixScale step (sampleCoefficientMatrix system (nodes n)
      (nodeMem n) stage))
  forcing := fun n => vectorScale step
    (sampleForcingVector system (nodes n) (nodeMem n) stage)

/-- The finite Euler state is defined by the expected rational update. -/
theorem eulerDiscretization_trajectory_succ
    {dimension : Nat} {lower upper : Rat}
    (system : IntervalLinearSystem dimension lower upper)
    (nodes : Nat -> Rat)
    (nodeMem : forall n, lower <= nodes n /\ nodes n <= upper)
    (step : Rat) (stage : Nat) (initial : RatVector dimension) (n : Nat) :
    (eulerDiscretization system nodes nodeMem step stage).trajectory initial (n + 1) =
      vectorAdd
        (matrixApply
          (matrixAdd (matrixIdentity dimension)
            (matrixScale step (sampleCoefficientMatrix system (nodes n)
              (nodeMem n) stage)))
          ((eulerDiscretization system nodes nodeMem step stage).trajectory initial n))
        (vectorScale step
          (sampleForcingVector system (nodes n) (nodeMem n) stage)) := by
  rfl

/-- Coefficient regularity supplies a uniform, explicit column-growth bound
for every step in the finite Euler solver. -/
theorem eulerDiscretization_step_columnBound
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (nodes : Nat -> Rat)
    (nodeMem : forall n, lower <= nodes n /\ nodes n <= upper)
    (step : Rat) (stage : Nat) (n : Nat) (j : Fin dimension) :
    matrixColumnAbsSum
      (matrixAdd (matrixIdentity dimension)
        (matrixScale step (sampleCoefficientMatrix system (nodes n)
          (nodeMem n) stage))) j <=
      1 + qabs step * finiteSum
        (fun _ : Fin dimension => regular.coefficientEntryBound hab) := by
  exact matrixColumnAbsSum_eulerStep_le_of_entry_bound
    (sampleCoefficientMatrix system (nodes n) (nodeMem n) stage)
    step (regular.coefficientEntryBound hab)
    (fun i k => regular.sampleCoefficientMatrix_entryBound hab
      (nodes n) (nodeMem n) stage i k) j

/-- The forcing samples used at each finite Euler update stay within the
whole-domain bound computed from the supplied interval regularity data. -/
theorem eulerDiscretization_forcing_componentBound
    {dimension : Nat} {lower upper : Rat}
    {system : IntervalLinearSystem dimension lower upper}
    (regular : system.CoefficientsRegular) (hab : lower <= upper)
    (nodes : Nat -> Rat)
    (nodeMem : forall n, lower <= nodes n /\ nodes n <= upper)
    (_step : Rat) (stage : Nat) (n : Nat) (i : Fin dimension) :
    qabs (sampleForcingVector system (nodes n) (nodeMem n) stage i) <=
      regular.forcingVectorBound hab := by
  exact regular.sampleForcingVector_componentBound hab
    (nodes n) (nodeMem n) stage i

end IntervalLinearSystem.CoefficientsRegular

/-- The scalar majorant for the terms omitted from a Peano--Baker transition
series.  If a submultiplicative matrix norm bounds `A` by `M` on an interval
of length `T`, its degree-`r` simplex contribution is bounded by
`(M*T)^r/r!`; this definition is the literal finite rational prefix of that
tail. -/
theorem halfPow_eq_inverse_twoPow (n : Nat) :
    ((1 : Rat) / 2) ^ n = 1 / ((2 ^ n : Nat) : Rat) := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [Rat.pow_succ, Nat.pow_succ, Rat.natCast_mul, ih]
      rw [Rat.div_def, Rat.div_def]
      simp only [Rat.one_mul, Rat.div_def]
      have hpowpos : 0 < ((2 ^ n : Nat) : Rat) := by
        exact Rat.pow_pos (show 0 < (2 : Rat) by decide +kernel)
      have hpowne : ((2 ^ n : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hpowpos
      have hproduct :
          (((2 ^ n : Nat) : Rat) * 2) *
              ((((2 ^ n : Nat) : Rat)⁻¹) * (2 : Rat)⁻¹) = 1 := by
        calc
          (((2 ^ n : Nat) : Rat) * 2) *
              ((((2 ^ n : Nat) : Rat)⁻¹) * (2 : Rat)⁻¹) =
            ((((2 ^ n : Nat) : Rat) * (((2 ^ n : Nat) : Rat)⁻¹)) *
              (2 * (2 : Rat)⁻¹)) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
          _ = 1 := by
            rw [Rat.mul_inv_cancel _ hpowne,
              Rat.mul_inv_cancel 2 (by decide +kernel)]
            exact Rat.one_mul _
      exact (Rat.inv_eq_of_mul_eq_one hproduct).symm

/-- Computable number of equal dyadic cells on an interval of length `T`
that makes the positive rational mesh step fit the derivative's step scale.
The half-decay selector chooses the exponent; raising two to it gives the
finite subdivision count. -/
def derivativeMeshCells (T : Rat) (stepPrecision : Nat)
    (hprecision : 0 < stepPrecision) : Nat :=
  let eps : QPos := ⟨1 / (stepPrecision : Rat),
    by
      rw [Rat.div_def, Rat.one_mul]
      exact Rat.inv_pos.mpr (Rat.natCast_pos.mpr hprecision)⟩
  2 ^ RationalMajorant.halfDecayShift T eps

/-- Rational step size for the canonical dyadic derivative mesh. -/
def derivativeMeshStep (T : Rat) (stepPrecision : Nat)
    (hprecision : 0 < stepPrecision) : Rat :=
  T / (derivativeMeshCells T stepPrecision hprecision : Rat)

/-- The rational nodes of an equal-step mesh starting at `lower`. -/
def uniformRationalMeshNode (lower step : Rat) (n : Nat) : Rat :=
  lower + (n : Rat) * step

/-- Successive affine mesh nodes differ by exactly the rational mesh step. -/
theorem uniformRationalMeshNode_succ (lower step : Rat) (n : Nat) :
    uniformRationalMeshNode lower step (n + 1) =
      uniformRationalMeshNode lower step n + step := by
  unfold uniformRationalMeshNode
  rw [Rat.natCast_add]
  norm_cast
  grind [Rat.add_mul, Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]

/-- If the total mesh length is `upper - lower`, its last node is the
specified endpoint. -/
theorem uniformRationalMeshNode_endpoint
    (lower upper step : Rat) (cells : Nat)
    (htotal : (cells : Rat) * step = upper - lower) :
    uniformRationalMeshNode lower step cells = upper := by
  unfold uniformRationalMeshNode
  calc
    lower + (cells : Rat) * step = lower + (upper - lower) := by rw [htotal]
    _ = upper := by grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- Every affine mesh node through `cells` lies in the closed interval when
the step is nonnegative and the total mesh length reaches the upper endpoint. -/
theorem uniformRationalMeshNode_mem
    {lower upper step : Rat} {cells n : Nat}
    (hstep : 0 <= step)
    (htotal : (cells : Rat) * step = upper - lower)
    (hn : n <= cells) :
    inDomainInterval lower upper (uniformRationalMeshNode lower step n) := by
  have hnat : (n : Rat) <= (cells : Rat) := Rat.natCast_le_natCast.mpr hn
  have hscaled := Rat.mul_le_mul_of_nonneg_right hnat hstep
  constructor
  · change lower <= lower + (n : Rat) * step
    simpa [Rat.add_zero] using (Rat.add_le_add_left (c := lower)).2
      (Rat.mul_nonneg (Rat.natCast_nonneg) hstep)
  · change lower + (n : Rat) * step <= upper
    calc
      lower + (n : Rat) * step <= lower + (cells : Rat) * step :=
        (Rat.add_le_add_left (c := lower)).2 hscaled
      _ = upper := by
        rw [htotal]
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- The dyadic mesh step is positive when the interval length and derivative
step precision are positive. -/
theorem derivativeMeshStep_pos {T : Rat} {stepPrecision : Nat}
    (hT : 0 < T) (hprecision : 0 < stepPrecision) :
    0 < derivativeMeshStep T stepPrecision hprecision := by
  unfold derivativeMeshStep
  apply Rat.mul_pos hT
  apply Rat.inv_pos.mpr
  exact Rat.natCast_pos.mpr
    (Nat.pow_pos (by decide : 0 < 2))

/-- Every cell of the canonical dyadic mesh is small enough for the effective
derivative estimate at the requested precision. -/
theorem derivativeMeshStep_le_inverse_precision {T : Rat}
    {stepPrecision : Nat} (hT : 0 <= T) (hprecision : 0 < stepPrecision) :
    derivativeMeshStep T stepPrecision hprecision <= 1 / (stepPrecision : Rat) := by
  let eps : QPos :=
    ⟨1 / (stepPrecision : Rat),
      by
        rw [Rat.div_def, Rat.one_mul]
        exact Rat.inv_pos.mpr (Rat.natCast_pos.mpr hprecision)⟩
  have hdecay := RationalMajorant.halfDecayShift_spec hT eps
  have hpow := halfPow_eq_inverse_twoPow
    (RationalMajorant.halfDecayShift T eps)
  have hcells : derivativeMeshCells T stepPrecision hprecision =
      2 ^ RationalMajorant.halfDecayShift T eps := by
    simp [derivativeMeshCells, eps]
  have hpowInv :
      ((2 ^ RationalMajorant.halfDecayShift T eps : Nat) : Rat)⁻¹ =
        (1 / 2) ^ RationalMajorant.halfDecayShift T eps := by
    rw [Rat.div_def, Rat.one_mul]
    simpa [Rat.div_def] using hpow.symm
  change T * ((derivativeMeshCells T stepPrecision hprecision : Nat) : Rat)⁻¹ <=
    1 / (stepPrecision : Rat)
  rw [hcells, hpowInv]
  simpa [eps] using hdecay

/-- The computed mesh step is a legal small step for any interval derivative
whose requested step precision is positive. This is the direct handoff from
the mesh algorithm to `HasDerivativeOnInterval.close`. -/
theorem derivativeMeshStep_satisfies
    {T : Rat} {stepPrecision : Nat}
    (hT : 0 <= T) (hprecision : 0 < stepPrecision) :
    qabs (derivativeMeshStep T stepPrecision hprecision) <=
      1 / (stepPrecision : Rat) := by
  have hstepNonneg : 0 <= derivativeMeshStep T stepPrecision hprecision := by
    unfold derivativeMeshStep
    apply Rat.mul_nonneg hT
    apply Rat.le_of_lt
    apply Rat.inv_pos.mpr
    exact Rat.natCast_pos.mpr
      (Nat.pow_pos (by decide : 0 < 2))
  rw [qabs_eq_self_of_nonneg hstepNonneg]
  exact derivativeMeshStep_le_inverse_precision hT hprecision

/-- The reciprocal of a positive natural precision is at most one. -/
theorem one_div_nat_le_one {n : Nat} (hn : 0 < n) :
    1 / (n : Rat) <= 1 := by
  have hnRat : 0 < (n : Rat) := Rat.natCast_pos.mpr hn
  have hge : (1 : Rat) <= (n : Rat) :=
    Rat.natCast_le_natCast.mpr (Nat.succ_le_of_lt hn)
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat))
  · calc
      (1 / (n : Rat)) * (n : Rat) = 1 := by
        rw [Rat.div_def, Rat.one_mul, Rat.mul_comm]
        exact Rat.mul_inv_cancel _ (Rat.ne_of_gt hnRat)
      _ <= 1 * (n : Rat) := by
        rw [Rat.one_mul]
        exact hge
  · exact hnRat

/-- Increasing a positive natural denominator can only decrease its
reciprocal. This supports a shared mesh chosen from the maximum of several
solution step requirements. -/
theorem one_div_nat_le_one_div_nat {a b : Nat} (ha : 0 < a) (hab : a <= b) :
    1 / (b : Rat) <= 1 / (a : Rat) := by
  have haRat : 0 < (a : Rat) := Rat.natCast_pos.mpr ha
  have hbRat : 0 < (b : Rat) := Rat.natCast_pos.mpr (Nat.lt_of_lt_of_le ha hab)
  have hprod : 0 < (a : Rat) * (b : Rat) := Rat.mul_pos haRat hbRat
  apply Rat.le_of_mul_le_mul_right (c := (a : Rat) * (b : Rat))
  · calc
      (1 / (b : Rat)) * ((a : Rat) * (b : Rat)) = a := by
        rw [Rat.div_def]
        have hcancel := Rat.mul_inv_cancel (b : Rat) (Rat.ne_of_gt hbRat)
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= b := Rat.natCast_le_natCast.mpr hab
      _ = (1 / (a : Rat)) * ((a : Rat) * (b : Rat)) := by
        rw [Rat.div_def]
        have hcancel := Rat.mul_inv_cancel (a : Rat) (Rat.ne_of_gt haRat)
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hprod

/-- Number of equal rational blocks chosen so a supplied nonnegative
coefficient majorant `B` has product at most one half with each block length.
The construction uses the existing half-decay selector on the total growth
budget `T * B`; it therefore works for rational bounds that are not integers.
-/
def coefficientShortBlockCells (T B : Rat) : Nat :=
  2 ^ RationalMajorant.halfDecayShift (T * B)
    { val := (1 : Rat) / 2
      property := by
        rw [Rat.div_def, Rat.one_mul]
        exact Rat.inv_pos.mpr (by decide +kernel : (0 : Rat) < 2) }

/-- The selected short-block partition has a positive number of cells. -/
theorem coefficientShortBlockCells_pos (T B : Rat) :
    0 < coefficientShortBlockCells T B := by
  unfold coefficientShortBlockCells
  exact Nat.pow_pos (by decide : 0 < 2)

/-- Rational step size for the equal partition selected from the total
coefficient budget. -/
def coefficientShortBlockStep (T B : Rat) : Rat :=
  T / (coefficientShortBlockCells T B : Rat)

/-- The selected block step is positive for a positive interval length. -/
theorem coefficientShortBlockStep_pos {T B : Rat} (hT : 0 < T) :
    0 < coefficientShortBlockStep T B := by
  unfold coefficientShortBlockStep
  apply Rat.mul_pos hT
  apply Rat.inv_pos.mpr
  exact Rat.natCast_pos.mpr (coefficientShortBlockCells_pos T B)

/-- The equal rational blocks add up to the original interval length. -/
theorem coefficientShortBlock_totalLength (T B : Rat) :
    (coefficientShortBlockCells T B : Rat) *
      coefficientShortBlockStep T B = T := by
  have hcellsPos : 0 < (coefficientShortBlockCells T B : Rat) :=
    Rat.natCast_pos.mpr (coefficientShortBlockCells_pos T B)
  have hcellsNe : (coefficientShortBlockCells T B : Rat) ≠ 0 :=
    Rat.ne_of_gt hcellsPos
  unfold coefficientShortBlockStep
  calc
    (coefficientShortBlockCells T B : Rat) *
        (T / (coefficientShortBlockCells T B : Rat)) =
        (T / (coefficientShortBlockCells T B : Rat)) *
          (coefficientShortBlockCells T B : Rat) := Rat.mul_comm _ _
    _ = T := Rat.div_mul_cancel hcellsNe

/-- The total coefficient budget divided by the selected block count is at
most one half. This is the computable rational estimate used to ensure that
the Euler comparison on each block is a contraction. -/
theorem coefficientShortBlockCells_budget {T B : Rat}
    (hT : 0 <= T) (hB : 0 <= B) :
    (T * B) / (coefficientShortBlockCells T B : Rat) <= (1 : Rat) / 2 := by
  let eps : QPos :=
    { val := (1 : Rat) / 2
      property := by
        rw [Rat.div_def, Rat.one_mul]
        exact Rat.inv_pos.mpr (by decide +kernel : (0 : Rat) < 2) }
  let shift := RationalMajorant.halfDecayShift (T * B) eps
  have hdecay := RationalMajorant.halfDecayShift_spec
    (Rat.mul_nonneg hT hB) eps
  have hpow := halfPow_eq_inverse_twoPow shift
  have hcells : coefficientShortBlockCells T B = 2 ^ shift := by
    simp [coefficientShortBlockCells, shift, eps]
  have hpowInv : ((2 ^ shift : Nat) : Rat)⁻¹ =
      ((1 : Rat) / 2) ^ shift := by
    rw [Rat.div_def, Rat.one_mul]
    simpa [Rat.div_def] using hpow.symm
  change T * B * ((coefficientShortBlockCells T B : Nat) : Rat)⁻¹ <=
    (1 : Rat) / 2
  rw [hcells, hpowInv]
  simpa [eps, shift] using hdecay

/-- A block in the selected equal partition has coefficient growth at most
one half. -/
theorem coefficientShortBlockStep_budget {T B : Rat}
    (hT : 0 <= T) (hB : 0 <= B) :
    coefficientShortBlockStep T B * B <= (1 : Rat) / 2 := by
  have hbudget := coefficientShortBlockCells_budget hT hB
  have hidentity :
      coefficientShortBlockStep T B * B =
        (T * B) / (coefficientShortBlockCells T B : Rat) := by
    unfold coefficientShortBlockStep
    rw [Rat.div_def, Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm]
  rw [hidentity]
  exact hbudget

/-- The generic half-decay selector's verified partition count for unit length
and scalar coefficient bound one. -/
theorem coefficientShortBlockCells_unit_scalar :
    coefficientShortBlockCells 1 1 = 64 := by
  decide +kernel

/-- The generic half-decay selector's verified partition count for unit
length and two-coordinate entry-sum bound four. -/
theorem coefficientShortBlockCells_unit_rotation :
    coefficientShortBlockCells 1 4 = 32768 := by
  decide +kernel

theorem coefficientShortBlockStep_unit_scalar :
    coefficientShortBlockStep 1 1 = (1 : Rat) / 64 := by
  decide +kernel

theorem coefficientShortBlockStep_unit_rotation :
    coefficientShortBlockStep 1 4 = (1 : Rat) / 32768 := by
  decide +kernel

/-- The selected equal-cell mesh has exactly the requested total length.
This is the bookkeeping identity needed to sum local residuals across its
finite partition. -/
theorem derivativeMesh_totalLength {T : Rat} {stepPrecision : Nat}
    (hprecision : 0 < stepPrecision) :
    (derivativeMeshCells T stepPrecision hprecision : Rat) *
        derivativeMeshStep T stepPrecision hprecision = T := by
  have hcellsPos :
      0 < (derivativeMeshCells T stepPrecision hprecision : Rat) :=
    Rat.natCast_pos.mpr
      (Nat.pow_pos (by decide : 0 < 2))
  have hcellsNe :
      (derivativeMeshCells T stepPrecision hprecision : Rat) ≠ 0 :=
    Rat.ne_of_gt hcellsPos
  unfold derivativeMeshStep
  calc
    (derivativeMeshCells T stepPrecision hprecision : Rat) *
        (T / (derivativeMeshCells T stepPrecision hprecision : Rat)) =
        (T / (derivativeMeshCells T stepPrecision hprecision : Rat)) *
          (derivativeMeshCells T stepPrecision hprecision : Rat) := Rat.mul_comm _ _
    _ = T := Rat.div_mul_cancel hcellsNe

/-- The `n`th node of a uniform rational mesh starting at `lower`. -/
def uniformMeshPoint (lower step : Rat) (n : Nat) : Rat :=
  lower + (n : Rat) * step

theorem uniformMeshPoint_succ (lower step : Rat) (n : Nat) :
    uniformMeshPoint lower step (n + 1) =
      uniformMeshPoint lower step n + step := by
  unfold uniformMeshPoint
  rw [Rat.natCast_add]
  grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
    Rat.add_left_comm, Rat.mul_assoc, Rat.mul_comm]

/-- Exact rational total length puts every uniform mesh node in the closed
interval. This includes the final node and requires no point outside the
declared domain. -/
theorem uniformMeshPoint_mem {lower upper step : Rat} {cells n : Nat}
    (hstep : 0 <= step)
    (htotal : (cells : Rat) * step = upper - lower)
    (hn : n <= cells) :
    inDomainInterval lower upper (uniformMeshPoint lower step n) := by
  constructor
  · have hnnonneg : 0 <= (n : Rat) := Rat.natCast_nonneg
    have hprod : 0 <= (n : Rat) * step := Rat.mul_nonneg hnnonneg hstep
    unfold uniformMeshPoint
    have h := (Rat.add_le_add_left (c := lower)).2 hprod
    simpa [Rat.add_zero] using h
  · have hnle : (n : Rat) <= (cells : Rat) := by exact_mod_cast hn
    have hprod := Rat.mul_le_mul_of_nonneg_right hnle hstep
    have hsum := (Rat.add_le_add_left (c := lower)).2 hprod
    unfold uniformMeshPoint
    calc
      lower + (n : Rat) * step <= lower + (cells : Rat) * step := by
        exact hsum
      _ = upper := by rw [htotal]; grind [Rat.sub_eq_add_neg, Rat.add_assoc]

/-- Rational boundary points for the equal partition selected from an
effective coefficient bound. -/
def coefficientShortBlockPoint (lower T B : Rat) (n : Nat) : Rat :=
  uniformMeshPoint lower (coefficientShortBlockStep T B) n

/-- Successive selected partition points differ by the selected rational
short-block step. -/
theorem coefficientShortBlockPoint_succ (lower T B : Rat) (n : Nat) :
    coefficientShortBlockPoint lower T B (n + 1) =
      coefficientShortBlockPoint lower T B n +
        coefficientShortBlockStep T B := by
  exact uniformMeshPoint_succ lower (coefficientShortBlockStep T B) n

/-- Every selected partition boundary stays in the closed rational interval. -/
theorem coefficientShortBlockPoint_mem {lower upper B : Rat}
    (hlength : 0 <= upper - lower)
    {n : Nat} (hn : n <= coefficientShortBlockCells (upper - lower) B) :
    inDomainInterval lower upper
      (coefficientShortBlockPoint lower (upper - lower) B n) := by
  have hstep : 0 <= coefficientShortBlockStep (upper - lower) B := by
    unfold coefficientShortBlockStep
    apply Rat.mul_nonneg hlength
    apply Rat.le_of_lt
    apply Rat.inv_pos.mpr
    exact Rat.natCast_pos.mpr
      (coefficientShortBlockCells_pos (upper - lower) B)
  have htotal :
      (coefficientShortBlockCells (upper - lower) B : Rat) *
        coefficientShortBlockStep (upper - lower) B = upper - lower :=
    coefficientShortBlock_totalLength (upper - lower) B
  exact uniformMeshPoint_mem hstep htotal hn

/-- The final selected partition boundary is the original upper endpoint. -/
theorem coefficientShortBlockPoint_last {lower upper B : Rat} :
    coefficientShortBlockPoint lower (upper - lower) B
      (coefficientShortBlockCells (upper - lower) B) = upper := by
  have htotal := coefficientShortBlock_totalLength (upper - lower) B
  have htotal' :
      (coefficientShortBlockCells (upper - lower) B : Rat) *
        coefficientShortBlockStep (upper - lower) B = upper - lower := by
    exact htotal
  unfold coefficientShortBlockPoint uniformMeshPoint
  change lower + (coefficientShortBlockCells (upper - lower) B : Rat) *
      coefficientShortBlockStep (upper - lower) B = upper
  rw [htotal']
  grind [Rat.sub_eq_add_neg, Rat.add_assoc]

/-- A vector-valued interval function sampled at the start nodes of a uniform
mesh. The last state uses the preceding cell's quotient schedule, so a closed
interval needs no evaluator call beyond its endpoint. -/
def uniformMeshLowerSample {dimension : Nat} {lower upper : Rat}
    (F DF : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (nodes : Nat -> Rat)
    (cells : Nat)
    (nodeMem : forall n, n <= cells -> inDomainInterval lower upper (nodes n))
    (step : Rat) (stage : Fin dimension -> Nat) (n : Nat) :
    RatVector dimension := by
  by_cases hn : n < cells
  · exact F.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
      (fun i => (D i).evalPrecision (nodes n) step (stage i))
  · exact F.lowerSample (nodes cells) (nodeMem cells (Nat.le_refl _))
      (fun i => (D i).evalPrecision (nodes (cells - 1)) step (stage i))

theorem uniformMeshLowerSample_at_start
    {dimension : Nat} {lower upper : Rat}
    (F DF : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (nodes : Nat -> Rat)
    (cells : Nat)
    (nodeMem : forall n, n <= cells -> inDomainInterval lower upper (nodes n))
    (step : Rat) (stage : Fin dimension -> Nat) (n : Nat)
    (hn : n < cells) :
    uniformMeshLowerSample F DF D nodes cells nodeMem step stage n =
      F.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun i => (D i).evalPrecision (nodes n) step (stage i)) := by
  simp [uniformMeshLowerSample, hn]

/-- The initial mesh sample is evaluated at the initial node even when the
interval has zero length and the mesh therefore has no cells. -/
theorem uniformMeshLowerSample_at_zero_of_zero_node
    {dimension : Nat} {lower upper : Rat}
    (F DF : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (nodes : Nat -> Rat) (cells : Nat)
    (nodeMem : forall n, n <= cells -> inDomainInterval lower upper (nodes n))
    (step : Rat) (stage : Fin dimension -> Nat) :
    uniformMeshLowerSample F DF D nodes cells nodeMem step stage 0 =
      F.lowerSample (nodes 0) (nodeMem 0 (Nat.zero_le _))
        (fun i => (D i).evalPrecision (nodes 0) step (stage i)) := by
  by_cases hcells : cells = 0
  · subst cells
    simp [uniformMeshLowerSample]
  · have hpos : 0 < cells := Nat.pos_of_ne_zero hcells
    rw [uniformMeshLowerSample_at_start F DF D nodes cells nodeMem step stage
      0 hpos]

/-- The final mesh state is sampled at the actual endpoint using the last
cell's derivative precision schedule. -/
theorem uniformMeshLowerSample_at_final
    {dimension : Nat} {lower upper : Rat}
    (F DF : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (nodes : Nat -> Rat)
    (cells : Nat)
    (nodeMem : forall n, n <= cells -> inDomainInterval lower upper (nodes n))
    (step : Rat) (stage : Fin dimension -> Nat) :
    uniformMeshLowerSample F DF D nodes cells nodeMem step stage cells =
      F.lowerSample (nodes cells) (nodeMem cells (Nat.le_refl _))
        (fun i => (D i).evalPrecision (nodes (cells - 1)) step (stage i)) := by
  simp [uniformMeshLowerSample]

/-- Coordinate form of the final mesh sample, exposing its raw interval
lower endpoint and the precise derivative-selected stage. -/
theorem uniformMeshLowerSample_component_at_final_eq_raw_lower
    {dimension : Nat} {lower upper : Rat}
    (F DF : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (nodes : Nat -> Rat) (cells : Nat)
    (nodeMem : forall n, n <= cells -> inDomainInterval lower upper (nodes n))
    (step : Rat) (stage : Fin dimension -> Nat) (i : Fin dimension) :
    uniformMeshLowerSample F DF D nodes cells nodeMem step stage cells i =
      ((PartialRealFunRaw.apply (F.component i).raw
        (F.component i).valid_on (nodes cells)
        ((F.component i).defined_on (nodes cells)
          (F.domainAt i (nodes cells) (nodeMem cells (Nat.le_refl _))))).compute
          ((D i).evalPrecision (nodes (cells - 1)) step (stage i))).lo := by
  calc
    uniformMeshLowerSample F DF D nodes cells nodeMem step stage cells i =
        F.lowerSample (nodes cells) (nodeMem cells (Nat.le_refl _))
          (fun j => (D j).evalPrecision (nodes (cells - 1)) step (stage j)) i :=
      congrArg (fun v => v i)
        (uniformMeshLowerSample_at_final F DF D nodes cells nodeMem step stage)
    _ = _ := FunctionVectorOnInterval.lowerSample_eq_component_raw_lower
      F (nodes cells) (nodeMem cells (Nat.le_refl _))
      (fun j => (D j).evalPrecision (nodes (cells - 1)) step (stage j)) i

/-- A finite vector comparison gives the exact componentwise bound on the
raw lower endpoints sampled at the common terminal node. This is the
endpoint form consumed by the cofinal raw-real equality bridge. -/
theorem uniformMeshRawLower_component_error_of_vector_error
    {dimension : Nat} {lower upper : Rat}
    (F DF G DG : FunctionVectorOnInterval dimension lower upper)
    (D : forall j, HasDerivativeOnInterval (F.component j) (DF.component j))
    (E : forall j, HasDerivativeOnInterval (G.component j) (DG.component j))
    (nodes : Nat -> Rat) (cells : Nat)
    (nodeMem : forall n, n <= cells -> inDomainInterval lower upper (nodes n))
    (step : Rat) (stage : Fin dimension -> Nat) (i : Fin dimension)
    (error : Rat)
    (hvector : vectorAbsSum (vectorSub
      (uniformMeshLowerSample F DF D nodes cells nodeMem step stage cells)
      (uniformMeshLowerSample G DG E nodes cells nodeMem step stage cells)) <= error) :
    qabs
      ((((PartialRealFunRaw.apply
          (F.component i).raw
          (F.component i).valid_on
          (nodes cells)
          ((F.component i).defined_on (nodes cells)
            (F.domainAt i (nodes cells) (nodeMem cells (Nat.le_refl _))))).compute
          ((D i).evalPrecision (nodes (cells - 1)) step (stage i))).lo) -
        (((PartialRealFunRaw.apply
          (G.component i).raw
          (G.component i).valid_on
          (nodes cells)
          ((G.component i).defined_on (nodes cells)
            (G.domainAt i (nodes cells) (nodeMem cells (Nat.le_refl _))))).compute
          ((E i).evalPrecision (nodes (cells - 1)) step (stage i))).lo)) <= error := by
  calc
    _ = qabs
        (uniformMeshLowerSample F DF D nodes cells nodeMem step stage cells i -
          uniformMeshLowerSample G DG E nodes cells nodeMem step stage cells i) := by
      rw [← uniformMeshLowerSample_component_at_final_eq_raw_lower
        F DF D nodes cells nodeMem step stage i,
        ← uniformMeshLowerSample_component_at_final_eq_raw_lower
          G DG E nodes cells nodeMem step stage i]
    _ <= vectorAbsSum (vectorSub
          (uniformMeshLowerSample F DF D nodes cells nodeMem step stage cells)
          (uniformMeshLowerSample G DG E nodes cells nodeMem step stage cells)) :=
      vectorDifference_component_le _ _ i
    _ <= error := hvector

/-- Residual vector for one forced Euler step of a sampled mesh path. -/
def sampledEulerResidual {dimension : Nat}
    (state : Nat -> RatVector dimension) (step : Nat -> RatMatrix dimension)
    (forcing : Nat -> RatVector dimension) (n : Nat) : RatVector dimension :=
  vectorSub (state (n + 1))
    (vectorAdd (matrixApply (step n) (state n)) (forcing n))

theorem sampledEulerResidual_step {dimension : Nat}
    (state : Nat -> RatVector dimension) (step : Nat -> RatMatrix dimension)
    (forcing : Nat -> RatVector dimension) (n : Nat) :
    state (n + 1) = vectorAdd
      (vectorAdd (matrixApply (step n) (state n)) (forcing n))
      (sampledEulerResidual state step forcing n) := by
  funext i
  simp [sampledEulerResidual, vectorSub, vectorAdd]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

/-- Dyadic mesh selected for an arbitrary positive rational tolerance. -/
def dyadicCellsForTolerance (T : Rat) (eps : QPos) : Nat :=
  2 ^ RationalMajorant.halfDecayShift T eps

/-- Rational cell length for `dyadicCellsForTolerance`. -/
def dyadicStepForTolerance (T : Rat) (eps : QPos) : Rat :=
  T / (dyadicCellsForTolerance T eps : Rat)

/-- The general tolerance based dyadic mesh meets its requested step bound. -/
theorem dyadicStepForTolerance_le {T : Rat} (hT : 0 <= T) (eps : QPos) :
    dyadicStepForTolerance T eps <= eps.val := by
  have hdecay := RationalMajorant.halfDecayShift_spec hT eps
  have hpow := halfPow_eq_inverse_twoPow
    (RationalMajorant.halfDecayShift T eps)
  have hpowInv :
      ((2 ^ RationalMajorant.halfDecayShift T eps : Nat) : Rat)⁻¹ =
        (1 / 2) ^ RationalMajorant.halfDecayShift T eps := by
    rw [Rat.div_def, Rat.one_mul]
    simpa [Rat.div_def] using hpow.symm
  change T * ((dyadicCellsForTolerance T eps : Nat) : Rat)⁻¹ <= eps.val
  rw [dyadicCellsForTolerance, hpowInv]
  exact hdecay

/-- The arbitrary-tolerance dyadic partition has exactly the interval's
total length. -/
theorem dyadicMesh_totalLength (T : Rat) (eps : QPos) :
    (dyadicCellsForTolerance T eps : Rat) *
      dyadicStepForTolerance T eps = T := by
  have hcellsPos : 0 < (dyadicCellsForTolerance T eps : Rat) :=
    Rat.natCast_pos.mpr (Nat.pow_pos (by decide : 0 < 2))
  have hcellsNe : (dyadicCellsForTolerance T eps : Rat) ≠ 0 :=
    Rat.ne_of_gt hcellsPos
  unfold dyadicStepForTolerance
  calc
    (dyadicCellsForTolerance T eps : Rat) *
        (T / (dyadicCellsForTolerance T eps : Rat)) =
        (T / (dyadicCellsForTolerance T eps : Rat)) *
          (dyadicCellsForTolerance T eps : Rat) := Rat.mul_comm _ _
    _ = T := Rat.div_mul_cancel hcellsNe

/-- Reciprocal natural meshes shrink when their denominator grows. -/
theorem one_div_nat_succ_antitone {n m : Nat} (hnm : n <= m) :
    1 / (((m + 1 : Nat) : Rat)) <= 1 / (((n + 1 : Nat) : Rat)) := by
  have hnpos : 0 < (n + 1 : Nat) := Nat.succ_pos n
  have hmpos : 0 < (m + 1 : Nat) := Nat.succ_pos m
  apply Rat.le_of_mul_le_mul_right
    (c := ((n + 1 : Nat) : Rat) * ((m + 1 : Nat) : Rat))
  · calc
      (1 / (((m + 1 : Nat) : Rat))) *
          (((n + 1 : Nat) : Rat) * ((m + 1 : Nat) : Rat)) =
          ((n + 1 : Nat) : Rat) := by
        have hmne : ((m + 1 : Nat) : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 hmpos)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= ((m + 1 : Nat) : Rat) := by exact_mod_cast (Nat.succ_le_succ hnm)
      _ = (1 / (((n + 1 : Nat) : Rat))) *
          (((n + 1 : Nat) : Rat) * ((m + 1 : Nat) : Rat)) := by
        have hnne : ((n + 1 : Nat) : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 hnpos)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact Rat.mul_pos ((Rat.natCast_pos).2 hnpos)
      ((Rat.natCast_pos).2 hmpos)

/-- At stage `n`, refine the derivative mesh enough for both its step
schedule and an independent `1/(n+1)` vanishing bound. -/
def derivativePrecisionMeshTolerance (stepPrecision n : Nat) : QPos :=
  ⟨1 / (((stepPrecision + n + 1 : Nat) : Rat)), by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.inv_pos.mpr
      (Rat.natCast_pos.mpr (Nat.succ_pos (stepPrecision + n)))⟩

def derivativePrecisionMeshCells (T : Rat) (stepPrecision n : Nat) : Nat :=
  dyadicCellsForTolerance T (derivativePrecisionMeshTolerance stepPrecision n)

def derivativePrecisionMeshStep (T : Rat) (stepPrecision n : Nat) : Rat :=
  dyadicStepForTolerance T (derivativePrecisionMeshTolerance stepPrecision n)

/-- The precision-refined mesh meets the derivative's positive step scale. -/
theorem derivativePrecisionMeshStep_small {T : Rat} {stepPrecision n : Nat}
    (hT : 0 <= T) (hprecision : 0 < stepPrecision) :
    derivativePrecisionMeshStep T stepPrecision n <= 1 / (stepPrecision : Rat) := by
  have hmesh := dyadicStepForTolerance_le hT
    (derivativePrecisionMeshTolerance stepPrecision n)
  have hanti := one_div_nat_succ_antitone
    (n := stepPrecision - 1) (m := stepPrecision + n) (by omega)
  have hsub : stepPrecision - 1 + 1 = stepPrecision := by omega
  simpa [derivativePrecisionMeshStep, derivativePrecisionMeshTolerance, hsub] using
    Rat.le_trans hmesh hanti

/-- The precision-refined mesh step has an explicit bound tending to zero
with its natural stage index. -/
theorem derivativePrecisionMeshStep_le_stage {T : Rat} {stepPrecision n : Nat}
    (hT : 0 <= T) :
    derivativePrecisionMeshStep T stepPrecision n <= 1 / ((n + 1 : Nat) : Rat) := by
  have hmesh := dyadicStepForTolerance_le hT
    (derivativePrecisionMeshTolerance stepPrecision n)
  have hanti := one_div_nat_succ_antitone
    (n := n) (m := stepPrecision + n) (by omega)
  simpa [derivativePrecisionMeshStep, derivativePrecisionMeshTolerance,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Rat.le_trans hmesh hanti

def peanoBakerFactorialTail (M T : Rat) (start : Nat) : Nat -> Rat :=
  RationalMajorant.factorialTailPartial (M * T) start

/-- A computable Peano--Baker factorial-tail prefix is bounded by twice its
first omitted term.  This is an all-finite statement: `terms` is arbitrary,
so it can be used to enclose every finite truncation before a raw matrix
algorithm is constructed. -/
theorem peanoBakerFactorialTail_bound {M T : Rat}
    (hM : 0 <= M) (hT : 0 <= T) (terms : Nat) :
    peanoBakerFactorialTail M T (RationalMajorant.factorialTailStart (M * T)) terms <=
      2 * RationalMajorant.factorialTailTerm (M * T)
        (RationalMajorant.factorialTailStart (M * T)) := by
  unfold peanoBakerFactorialTail
  apply RationalMajorant.factorialTailPartial_bound_at_start
  exact Rat.mul_nonneg hM hT

/-- The same tail certificate records its explicit geometric decay after the
computable start.  This is the modulus needed for the eventual continuous
Peano--Baker raw-matrix construction. -/
theorem peanoBakerFactorialTail_shifted_bound {M T : Rat}
    (hM : 0 <= M) (hT : 0 <= T) (shift terms : Nat) :
    peanoBakerFactorialTail M T
        (RationalMajorant.factorialTailStart (M * T) + shift) terms <=
      2 * RationalMajorant.factorialTailTerm (M * T)
        (RationalMajorant.factorialTailStart (M * T)) * ((1 : Rat) / 2) ^ shift := by
  unfold peanoBakerFactorialTail
  exact RationalMajorant.factorialTailPartial_shifted_bound
    (Rat.mul_nonneg hM hT)
    (RationalMajorant.factorialTailStart_satisfies (M * T)) shift terms

/-- The executable shift which turns the Peano--Baker factorial majorant
into a requested positive rational error budget. -/
def peanoBakerFactorialTailShift (M T : Rat) (eps : QPos) : Nat :=
  RationalMajorant.halfDecayShift
    (2 * RationalMajorant.factorialTailTerm (M * T)
      (RationalMajorant.factorialTailStart (M * T))) eps

/-- After the displayed computable shift, every finite prefix of the omitted
Peano--Baker factorial tail is within the requested rational tolerance.  This
is the tail-modulus component needed for constructive matrix-series
uniqueness, independent of a completed function space. -/
theorem peanoBakerFactorialTail_shifted_le_eps {M T : Rat}
    (hM : 0 <= M) (hT : 0 <= T) (eps : QPos) (terms : Nat) :
    peanoBakerFactorialTail M T
      (RationalMajorant.factorialTailStart (M * T) +
        peanoBakerFactorialTailShift M T eps) terms <= eps.val := by
  unfold peanoBakerFactorialTail peanoBakerFactorialTailShift
  exact RationalMajorant.factorialTailPartial_shifted_le_eps
    (Rat.mul_nonneg hM hT) eps terms

/- A downstream matrix-transition construction should consume the tail bound
   as data, not reconstruct the shift arithmetic at every call site. -/
structure PeanoBakerFactorialRemainderCertificate
    (M T : Rat) (eps : QPos) where
  start : Nat
  tail_le_eps : forall terms,
    peanoBakerFactorialTail M T start terms <= eps.val

def peanoBakerFactorialRemainderCertificate
    {M T : Rat} (hM : 0 <= M) (hT : 0 <= T) (eps : QPos) :
    PeanoBakerFactorialRemainderCertificate M T eps := by
  refine {
    start := RationalMajorant.factorialTailStart (M * T) +
      peanoBakerFactorialTailShift M T eps
    tail_le_eps := ?_ }
  intro terms
  exact peanoBakerFactorialTail_shifted_le_eps hM hT eps terms

theorem peanoBakerFactorialTail_nonneg
    {M T : Rat} (hM : 0 <= M) (hT : 0 <= T)
    (start terms : Nat) :
    0 <= peanoBakerFactorialTail M T start terms := by
  unfold peanoBakerFactorialTail
  induction terms with
  | zero =>
      simp [RationalMajorant.factorialTailPartial]
  | succ terms ih =>
      rw [RationalMajorant.factorialTailPartial]
      exact Rat.add_nonneg ih
        (RationalMajorant.factorialTailTerm_nonneg
          (Rat.mul_nonneg hM hT) (start + terms))

def PeanoBakerFactorialRemainderCertificate.interval
    {M T : Rat} {eps : QPos}
    (certificate : PeanoBakerFactorialRemainderCertificate M T eps)
    (terms : Nat) : QInterval :=
  { lo := 0
    hi := peanoBakerFactorialTail M T certificate.start terms }

theorem PeanoBakerFactorialRemainderCertificate.tail_mem_interval
    {M T : Rat} {eps : QPos}
    (certificate : PeanoBakerFactorialRemainderCertificate M T eps)
    (hM : 0 <= M) (hT : 0 <= T) (terms : Nat) :
    (PeanoBakerFactorialRemainderCertificate.interval certificate terms).lo <=
        peanoBakerFactorialTail M T certificate.start terms /\
      peanoBakerFactorialTail M T certificate.start terms <=
        (PeanoBakerFactorialRemainderCertificate.interval certificate terms).hi := by
  exact ⟨peanoBakerFactorialTail_nonneg hM hT certificate.start terms,
    Rat.le_refl⟩

/-- The computable iteration count used in the zero-initial Volterra
uniqueness argument.  The factor B is a rational enclosure bound for a
candidate difference, while the remaining factor is the usual Peano--Baker
factorial-tail radius. -/
def zeroInitialVolterraIterationShift (M T B : Rat) (eps : QPos) : Nat :=
  RationalMajorant.halfDecayShift
    (B * (2 * RationalMajorant.factorialTailTerm (M * T)
      (RationalMajorant.factorialTailStart (M * T)))) eps

/-- After this many ordered substitutions, a zero-initial Volterra estimate
of the form B * (M*T)^n / n! is below any requested positive rational
tolerance.  This is a finite rational estimate, not an appeal to a complete
space of functions. -/
theorem zeroInitialVolterra_iteration_le_eps {M T B : Rat}
    (hM : 0 <= M) (hT : 0 <= T) (hB : 0 <= B) (eps : QPos) :
    B * RationalMajorant.factorialTailTerm (M * T)
      (RationalMajorant.factorialTailStart (M * T) +
        zeroInitialVolterraIterationShift M T B eps) <= eps.val := by
  let shift := zeroInitialVolterraIterationShift M T B eps
  have htail := peanoBakerFactorialTail_shifted_bound hM hT shift 1
  have htailTerm :
      RationalMajorant.factorialTailTerm (M * T)
        (RationalMajorant.factorialTailStart (M * T) + shift) <=
        2 * RationalMajorant.factorialTailTerm (M * T)
          (RationalMajorant.factorialTailStart (M * T)) *
            ((1 : Rat) / 2) ^ shift := by
    simpa [peanoBakerFactorialTail,
      RationalMajorant.factorialTailPartial, Rat.zero_add] using htail
  have hscaled := Rat.mul_le_mul_of_nonneg_left htailTerm hB
  have htermNonneg : 0 <= RationalMajorant.factorialTailTerm (M * T)
      (RationalMajorant.factorialTailStart (M * T)) :=
    RationalMajorant.factorialTailTerm_nonneg (Rat.mul_nonneg hM hT) _
  have hradiusNonneg :
      0 <= B * (2 * RationalMajorant.factorialTailTerm (M * T)
        (RationalMajorant.factorialTailStart (M * T))) := by
    exact Rat.mul_nonneg hB (Rat.mul_nonneg (by decide +kernel) htermNonneg)
  calc
    B * RationalMajorant.factorialTailTerm (M * T)
        (RationalMajorant.factorialTailStart (M * T) + shift) <=
        B * (2 * RationalMajorant.factorialTailTerm (M * T)
          (RationalMajorant.factorialTailStart (M * T)) *
            ((1 : Rat) / 2) ^ shift) := hscaled
    _ = (B * (2 * RationalMajorant.factorialTailTerm (M * T)
          (RationalMajorant.factorialTailStart (M * T)))) *
            ((1 : Rat) / 2) ^ shift := by
      grind [Rat.mul_assoc]
    _ <= eps.val := by
      simpa [zeroInitialVolterraIterationShift, shift] using
        RationalMajorant.halfDecayShift_spec hradiusNonneg eps

/-- A scalar error satisfying the repeated zero-initial Volterra estimate is
literally zero.  A continuous uniqueness proof need only establish this
finite bound for the norm of the difference of two candidate solutions; the
factorial-tail kernel below then closes the equality without a supremum or a
completeness argument. -/
def ZeroInitialVolterraIterationBound (M T B error : Rat) : Prop :=
  0 <= error /\
  forall iterations : Nat,
    error <= B * RationalMajorant.factorialTailTerm (M * T)
      (RationalMajorant.factorialTailStart (M * T) + iterations)

theorem zeroInitialVolterraIterationBound_eq_zero {M T B error : Rat}
    (hM : 0 <= M) (hT : 0 <= T) (hB : 0 <= B)
    (herror : ZeroInitialVolterraIterationBound M T B error) :
    error = 0 := by
  rcases herror with ⟨herrorNonneg, hiterations⟩
  by_cases hzero : error = 0
  · exact hzero
  · have herrorPos : 0 < error :=
      Rat.lt_of_le_of_ne herrorNonneg (Ne.symm hzero)
    let eps : QPos :=
      ⟨error / 2, by
        rw [Rat.div_def]
        exact Rat.mul_pos herrorPos
          ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
    have hiteration := hiterations
      (zeroInitialVolterraIterationShift M T B eps)
    have hsmall := zeroInitialVolterra_iteration_le_eps hM hT hB eps
    have hhalf : error <= error / 2 := by
      exact Rat.le_trans hiteration hsmall
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

/-- A constructive uniqueness certificate for two interval-valued solutions
of `f' = f`.

The analytic layer supplies a nonnegative rational error at every rational
input and proves the iterated Volterra bound for that error.  This finite
Peano--Baker module then turns the factorial-tail estimate into pointwise
function agreement.  No norm completion, supremum, or completed real line is
part of this interface. -/
structure SelfDerivativeVolterraComparison
    (f g : FunctionOnInterval)
    (_hf : SolvesSelfDerivativeOnInterval f)
    (_hg : SolvesSelfDerivativeOnInterval g) where
  same_lower : f.lower = g.lower
  same_upper : f.upper = g.upper
  matrix_bound : Rat
  time_bound : Rat
  initial_error_bound : Rat
  matrix_bound_nonneg : 0 <= matrix_bound
  time_bound_nonneg : 0 <= time_bound
  initial_error_bound_nonneg : 0 <= initial_error_bound
  error : Rat -> Rat
  error_iterated :
    forall x,
      ZeroInitialVolterraIterationBound
        matrix_bound time_bound initial_error_bound (error x)
  equivalent_of_error_zero :
    forall x
      (hxF : inDomainInterval f.lower f.upper x)
      (hxG : inDomainInterval g.lower g.upper x),
      error x = 0 ->
        (PartialRealFunRaw.apply f.raw f.valid_on x (f.defined_on x hxF)).Equiv
          (PartialRealFunRaw.apply g.raw g.valid_on x (g.defined_on x hxG))

namespace SelfDerivativeVolterraComparison

/-- The factorial-tail comparison closes the requested pointwise agreement. -/
theorem equivalent
    {f g : FunctionOnInterval}
    {hf : SolvesSelfDerivativeOnInterval f}
    {hg : SolvesSelfDerivativeOnInterval g}
    (comparison : SelfDerivativeVolterraComparison f g hf hg) :
    FunctionOnInterval.Equivalent f g := by
  refine ⟨comparison.same_lower, comparison.same_upper, ?_⟩
  intro x hxF hxG
  apply comparison.equivalent_of_error_zero x hxF hxG
  exact zeroInitialVolterraIterationBound_eq_zero
    comparison.matrix_bound_nonneg
    comparison.time_bound_nonneg
    comparison.initial_error_bound_nonneg
    (comparison.error_iterated x)

end SelfDerivativeVolterraComparison

/-- The remaining analytic task for continuous Peano--Baker uniqueness,
stated as a reusable finite-certificate provider.  It is invoked only after
the two candidates have been shown to share both their rational initial point
and their certified raw-real initial value. -/
def SelfDerivativeVolterraUniqueness : Prop :=
  forall f g,
    (hf : SolvesSelfDerivativeOnInterval f) ->
    (hg : SolvesSelfDerivativeOnInterval g) ->
    f.lower = g.lower ->
    f.upper = g.upper ->
    hf.initial = hg.initial ->
    hf.initial_value.Equiv hg.initial_value ->
    Nonempty (SelfDerivativeVolterraComparison f g hf hg)

/-- A supply of finite Volterra comparison certificates proves the project's
topology-free uniqueness principle for `f' = f` with a common initial value. -/
theorem selfDerivativeInitialValueUnique_of_volterra
    (hvolterra : SelfDerivativeVolterraUniqueness) :
    SelfDerivativeInitialValueUnique := by
  intro f g hf hg hlo hhi hinitial hvalue
  rcases hvolterra f g hf hg hlo hhi hinitial hvalue with ⟨comparison⟩
  exact comparison.equivalent

/-- Glue local function identities across a finite rational interval
partition.  This isolates the local-to-global step needed by ODE uniqueness:
the analytic argument may establish equivalence cell by cell, while this
lemma propagates those identities to the complete represented interval.

The cells are required to cover every rational input.  No completeness or
topological compactness principle is used; the coverage evidence is finite
partition data. -/
theorem equivalent_of_finite_partition
    (f g : FunctionOnInterval) (cells : Nat)
    (point : Nat -> Rat)
    (same_lower : f.lower = g.lower)
    (same_upper : f.upper = g.upper)
    (cell_bounds : forall i, i < cells ->
      f.lower <= point i /\
      point i <= point (i + 1) /\
      point (i + 1) <= f.upper)
    (other_cell_bounds : forall i, i < cells ->
      g.lower <= point i /\
      point i <= point (i + 1) /\
      point (i + 1) <= g.upper)
    (covers : forall x, inDomainInterval f.lower f.upper x ->
      exists i, i < cells /\ point i <= x /\ x <= point (i + 1))
    (cell_equiv : forall i (hi : i < cells),
      FunctionOnInterval.Equivalent
        (FunctionOnInterval.restrict f (point i) (point (i + 1))
          (cell_bounds i hi).1
          (cell_bounds i hi).2.1 (cell_bounds i hi).2.2)
        (FunctionOnInterval.restrict g (point i) (point (i + 1))
          (other_cell_bounds i hi).1
          (other_cell_bounds i hi).2.1 (other_cell_bounds i hi).2.2)) :
    FunctionOnInterval.Equivalent f g := by
  refine ⟨same_lower, same_upper, ?_⟩
  intro x hxF hxG
  obtain ⟨i, hi, hixLower, hixUpper⟩ := covers x hxF
  have hb := cell_bounds i hi
  let Fcell := FunctionOnInterval.restrict f (point i) (point (i + 1))
    hb.1 hb.2.1 hb.2.2
  let Gcell := FunctionOnInterval.restrict g (point i) (point (i + 1))
    (other_cell_bounds i hi).1 (other_cell_bounds i hi).2.1
    (other_cell_bounds i hi).2.2
  have hxFcell : inDomainInterval Fcell.lower Fcell.upper x := by
    exact ⟨hixLower, hixUpper⟩
  have hxGcell : inDomainInterval Gcell.lower Gcell.upper x := by
    exact ⟨hixLower, hixUpper⟩
  exact (cell_equiv i hi).2.2 x hxFcell hxGcell

/-- Propagate local vector-function identities across a finite rational
cover. This is the local-to-global step for system uniqueness proofs: each
piece may use its own coefficient bounds and mesh construction, while the
conclusion is equality on the full shared interval. The proof only needs the
pieces to cover each rational input and the local represented-value
identities on those pieces. -/
theorem FunctionVectorOnInterval.componentwise_equivalent_of_finite_cover
    {dimension : Nat} {lower upper : Rat}
    (F G : FunctionVectorOnInterval dimension lower upper)
    (cells : Nat) (point : Nat -> Rat)
    (covers : forall x, inDomainInterval lower upper x ->
      exists i, i < cells /\ point i <= x /\ x <= point (i + 1))
    (local_agree : forall (j : Fin dimension) i
      (x : Rat) (hx : inDomainInterval lower upper x),
      point i <= x -> x <= point (i + 1) ->
      (PartialRealFunRaw.apply (F.component j).raw (F.component j).valid_on x
        ((F.component j).defined_on x (F.domainAt j x hx))).Equiv
      (PartialRealFunRaw.apply (G.component j).raw (G.component j).valid_on x
        ((G.component j).defined_on x (G.domainAt j x hx)))) :
    forall j, FunctionOnInterval.Equivalent (F.component j) (G.component j) := by
  intro j
  refine ⟨?_, ?_, ?_⟩
  · calc
      (F.component j).lower = lower := F.component_lower j
      _ = (G.component j).lower := (G.component_lower j).symm
  · calc
      (F.component j).upper = upper := F.component_upper j
      _ = (G.component j).upper := (G.component_upper j).symm
  · intro x hxF hxG
    have hx : inDomainInterval lower upper x := by
      change (F.component j).lower <= x /\ x <= (F.component j).upper at hxF
      rw [F.component_lower j, F.component_upper j] at hxF
      exact hxF
    obtain ⟨i, _hi, hixLower, hixUpper⟩ := covers x hx
    exact local_agree j i x hx hixLower hixUpper

/-- Equality of the represented vector values at one rational input. -/
def FunctionVectorOnInterval.ValuesAgreeAt
    {dimension : Nat} {lower upper : Rat}
    (F G : FunctionVectorOnInterval dimension lower upper)
    (x : Rat) (hx : inDomainInterval lower upper x) : Prop :=
  forall j : Fin dimension,
    (PartialRealFunRaw.apply (F.component j).raw
      (F.component j).valid_on x
      ((F.component j).defined_on x (F.domainAt j x hx))).Equiv
    (PartialRealFunRaw.apply (G.component j).raw
      (G.component j).valid_on x
      ((G.component j).defined_on x (G.domainAt j x hx)))

/-- Propagate a common initial vector through finitely many rational local
uniqueness intervals. Each local argument may use its own coefficient bounds
and short-block mesh schedule. The only information passed from one interval
to the next is equality of the represented endpoint vector. -/
theorem FunctionVectorOnInterval.componentwise_equivalent_of_finite_local_uniqueness
    {dimension : Nat} {lower upper : Rat}
    (F G : FunctionVectorOnInterval dimension lower upper)
    (cells : Nat) (point : Nat -> Rat)
    (cell_bounds : forall i, i < cells ->
      lower <= point i /\ point i <= point (i + 1) /\
        point (i + 1) <= upper)
    (covers : forall x, inDomainInterval lower upper x ->
      exists i, i < cells /\ point i <= x /\ x <= point (i + 1))
    (initial_mem : inDomainInterval lower upper (point 0))
    (initial_agree : FunctionVectorOnInterval.ValuesAgreeAt F G
      (point 0) initial_mem)
    (local_unique : forall i (hi : i < cells),
      FunctionVectorOnInterval.ValuesAgreeAt F G (point i)
        ⟨(cell_bounds i hi).1,
          Rat.le_trans (cell_bounds i hi).2.1 (cell_bounds i hi).2.2⟩ ->
      forall j : Fin dimension, forall x,
        (hx : inDomainInterval lower upper x) ->
        point i <= x -> x <= point (i + 1) ->
        (PartialRealFunRaw.apply (F.component j).raw
          (F.component j).valid_on x
          ((F.component j).defined_on x (F.domainAt j x hx))).Equiv
        (PartialRealFunRaw.apply (G.component j).raw
          (G.component j).valid_on x
          ((G.component j).defined_on x (G.domainAt j x hx)))) :
    forall j, FunctionOnInterval.Equivalent (F.component j) (G.component j) := by
  let nodeMem : forall i, i <= cells -> inDomainInterval lower upper (point i) :=
    fun i hi => by
      by_cases hzero : i = 0
      · subst i
        exact initial_mem
      · have hprev : i - 1 < cells := by omega
        have hb := cell_bounds (i - 1) hprev
        have hindex : (i - 1) + 1 = i := by omega
        rw [← hindex]
        exact ⟨Rat.le_trans hb.1 hb.2.1, hb.2.2⟩
  have boundary : forall i (hi : i <= cells),
      FunctionVectorOnInterval.ValuesAgreeAt F G (point i) (nodeMem i hi) := by
    intro i hi
    induction i with
    | zero =>
        simpa [FunctionVectorOnInterval.ValuesAgreeAt] using initial_agree
    | succ i ih =>
        have hcell : i < cells := by omega
        have hprev := ih (by omega)
        have hlocal := local_unique i hcell hprev
        have hb := cell_bounds i hcell
        have hnext : inDomainInterval lower upper (point (i + 1)) :=
          ⟨Rat.le_trans hb.1 hb.2.1, hb.2.2⟩
        intro j
        exact hlocal j (point (i + 1)) hnext hb.2.1 (Rat.le_refl)
  intro j
  refine ⟨?_, ?_, ?_⟩
  · calc
      (F.component j).lower = lower := F.component_lower j
      _ = (G.component j).lower := (G.component_lower j).symm
  · calc
      (F.component j).upper = upper := F.component_upper j
      _ = (G.component j).upper := (G.component_upper j).symm
  · intro x hxF hxG
    have hx : inDomainInterval lower upper x := by
      change (F.component j).lower <= x /\ x <= (F.component j).upper at hxF
      rw [F.component_lower j, F.component_upper j] at hxF
      exact hxF
    obtain ⟨i, hi, hleft, hright⟩ := covers x hx
    exact local_unique i hi (boundary i (Nat.le_of_lt hi)) j x hx hleft hright

/-- A bounded derivative enclosure gives an explicit symmetric bound for the
function change on one positive rational mesh cell. The only error is twice
the requested derivative precision, scaled by the cell width. -/
theorem HasDerivativeOnInterval.endpointDifference_contains_bounded
    {f df : FunctionOnInterval} (D : HasDerivativeOnInterval f df)
    {x h : Rat} {n : Nat}
    (hx : inDomainInterval f.lower f.upper x)
    (hxh : inDomainInterval f.lower f.upper (x + h))
    (hdx : inDomainInterval df.lower df.upper x)
    (hpos : 0 < h)
    (hsmall : qabs h <= 1 / ((D.stepPrecision n : Nat) : Rat))
    (bound : Rat) (hbound : 0 <= bound)
    (hderivLo : -bound <=
      (df.compute x hdx (D.evalPrecision x h n)).lo)
    (hderivHi :
      (df.compute x hdx (D.evalPrecision x h n)).hi <= bound) :
    ({ lo := -(h * (bound + 2 * (precisionAtStage n).val)
        )
       hi := h * (bound + 2 * (precisionAtStage n).val) } : QInterval).ContainsInterval
      (QInterval.subInterval
        (f.compute (x + h) hxh (D.evalPrecision x h n))
        (f.compute x hx (D.evalPrecision x h n))) := by
  let radius := bound + 2 * (precisionAtStage n).val
  let derivativeBox := df.compute x hdx (D.evalPrecision x h n)
  have hradius : 0 <= radius := by
    dsimp [radius]
    exact Rat.add_nonneg hbound
      (Rat.mul_nonneg (by decide)
        (Rat.le_of_lt (precisionAtStage n).property))
  have hexpand :
      ({ lo := -radius, hi := radius } : QInterval).ContainsInterval
        (QInterval.expand derivativeBox (2 * (precisionAtStage n).val)) := by
    unfold QInterval.ContainsInterval QInterval.expand
    dsimp [radius, derivativeBox]
    constructor
    · have hδ : 0 <= 2 * (precisionAtStage n).val :=
        Rat.mul_nonneg (by decide)
          (Rat.le_of_lt (precisionAtStage n).property)
      calc
        -(bound + 2 * (precisionAtStage n).val) <=
            (-bound) - 2 * (precisionAtStage n).val := by
              grind [Rat.neg_add, Rat.sub_eq_add_neg]
        _ <= (df.compute x hdx (D.evalPrecision x h n)).lo -
              2 * (precisionAtStage n).val := by
          simpa [Rat.sub_eq_add_neg] using
            (Rat.add_le_add_right).2 hderivLo
    · simpa [radius] using (Rat.add_le_add_right).2 hderivHi
  have hscaled := QInterval.scaleByRat_contains_of_nonneg
    (Rat.le_of_lt hpos) hexpand
  have hscaledBounds :
      ({ lo := -(h * radius), hi := h * radius } : QInterval).ContainsInterval
        (QInterval.scaleByRat h
          (QInterval.expand derivativeBox (2 * (precisionAtStage n).val))) := by
    simpa [QInterval.ContainsInterval, QInterval.scaleByRat,
      if_pos (Rat.le_of_lt hpos), Rat.mul_neg] using hscaled
  have hendpoint := D.endpointDifference_contains_of_pos
    hx hxh hdx hpos hsmall
  have hcompose := hscaledBounds.trans hendpoint
  simpa [radius, derivativeBox] using hcompose

/-- A derivative box close to a rational center gives an Euler increment
enclosure centered at `h * center`, with a fully explicit accumulated radius.
This is the local bridge from derivative evidence to the per-cell residual
for a linear ODE comparison. -/
theorem HasDerivativeOnInterval.endpointDifference_contains_centered
    {f df : FunctionOnInterval} (D : HasDerivativeOnInterval f df)
    {x h center err : Rat} {n : Nat}
    (hx : inDomainInterval f.lower f.upper x)
    (hxh : inDomainInterval f.lower f.upper (x + h))
    (hdx : inDomainInterval df.lower df.upper x)
    (hpos : 0 < h)
    (hsmall : qabs h <= 1 / ((D.stepPrecision n : Nat) : Rat))
    (_herr : 0 <= err)
    (hderivLo : center - err <=
      (df.compute x hdx (D.evalPrecision x h n)).lo)
    (hderivHi :
      (df.compute x hdx (D.evalPrecision x h n)).hi <= center + err) :
    QInterval.scaleByRat h
        ({ lo := center - (err + 2 * (precisionAtStage n).val)
           hi := center + (err + 2 * (precisionAtStage n).val) } : QInterval)
      |>.ContainsInterval
      (QInterval.subInterval
        (f.compute (x + h) hxh (D.evalPrecision x h n))
        (f.compute x hx (D.evalPrecision x h n))) := by
  let δ := 2 * (precisionAtStage n).val
  let derivativeBox := df.compute x hdx (D.evalPrecision x h n)
  have hexpand :
      (({ lo := center - (err + δ), hi := center + (err + δ) } : QInterval)
        ).ContainsInterval (QInterval.expand derivativeBox δ) := by
    unfold QInterval.ContainsInterval QInterval.expand
    dsimp [derivativeBox]
    constructor
    · calc
        center - (err + δ) <= (center - err) - δ := by
          grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
        _ <= (df.compute x hdx (D.evalPrecision x h n)).lo - δ := by
          simpa [Rat.sub_eq_add_neg] using (Rat.add_le_add_right).2 hderivLo
    · calc
        (df.compute x hdx (D.evalPrecision x h n)).hi + δ <=
            (center + err) + δ := (Rat.add_le_add_right).2 hderivHi
        _ <= center + (err + δ) := by
          grind [Rat.add_assoc, Rat.add_comm]
  have hscaled := QInterval.scaleByRat_contains_of_nonneg
    (Rat.le_of_lt hpos) hexpand
  have hendpoint := D.endpointDifference_contains_of_pos
    hx hxh hdx hpos hsmall
  have hcompose := hscaled.trans hendpoint
  simpa [δ, derivativeBox] using hcompose

/-- Interval addition cancels a subtracted interval when the first interval
is ordered. This is the enclosure algebra that turns an increment estimate
into an enclosure of the next solution value. -/
theorem QInterval.add_subInterval_contains_of_ordered
    (I J : QInterval) (hI : I.lo <= I.hi) :
    (I.addInterval (J.subInterval I)).ContainsInterval J := by
  unfold QInterval.ContainsInterval QInterval.addInterval QInterval.subInterval
  constructor
  · have hdiff : I.lo - I.hi <= 0 := by
      simpa [Rat.sub_eq_add_neg, Rat.add_neg_cancel] using
        (Rat.add_le_add_right (c := -I.hi)).2 hI
    calc
      I.lo + (J.lo - I.hi) = (I.lo - I.hi) + J.lo := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      _ <= 0 + J.lo := (Rat.add_le_add_right).2 hdiff
      _ = J.lo := Rat.zero_add _
  · have hdiff : 0 <= I.hi - I.lo := by
      have h := (Rat.add_le_add_right (c := -I.lo)).2 hI
      simpa [Rat.sub_eq_add_neg, Rat.add_neg_cancel] using h
    calc
      J.hi = 0 + J.hi := (Rat.zero_add _).symm
      _ <= (I.hi - I.lo) + J.hi := (Rat.add_le_add_right).2 hdiff
      _ = I.hi + (J.hi - I.lo) := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- If a new interval lies in the old interval plus an increment box centered
at `center`, then its lower endpoint follows the rational Euler step with a
residual bounded by the old interval width plus the increment radius. -/
theorem QInterval.lowerEndpoint_eulerResidual
    (I S J : QInterval) (center radius : Rat)
    (hI : I.lo <= I.hi) (hJ : J.lo <= J.hi)
    (hSlo : center - radius <= S.lo)
    (hShi : S.hi <= center + radius)
    (hcontains : (I.addInterval S).ContainsInterval J) :
    -(I.width + radius) <= J.lo - (I.lo + center) /\
      J.lo - (I.lo + center) <= I.width + radius := by
  unfold QInterval.ContainsInterval QInterval.addInterval at hcontains
  unfold QInterval.width
  constructor
  · have hlower : I.lo + (center - radius) <= J.lo :=
      Rat.le_trans (by
        have h := (Rat.add_le_add_left (c := I.lo)).2 hSlo
        simpa [Rat.sub_eq_add_neg, Rat.add_assoc] using h) hcontains.1
    have hwidth : 0 <= I.hi - I.lo := (Rat.le_iff_sub_nonneg I.lo I.hi).1 hI
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
  · have hupperStep : I.hi + S.hi <= I.hi + (center + radius) :=
      (Rat.add_le_add_left (c := I.hi)).2 hShi
    have hupper : J.lo <= I.hi + (center + radius) :=
      Rat.le_trans (Rat.le_trans hJ hcontains.2) hupperStep
    have hwidth : 0 <= I.hi - I.lo := (Rat.le_iff_sub_nonneg I.lo I.hi).1 hI
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

/-- The centered derivative enclosure yields an explicit one-cell Euler
enclosure for the endpoint value itself. All raw interval evaluation errors
remain visible in the radius supplied to the derivative certificate. -/
theorem HasDerivativeOnInterval.endpointValue_contains_euler
    {f df : FunctionOnInterval} (D : HasDerivativeOnInterval f df)
    {x h center err : Rat} {n : Nat}
    (hx : inDomainInterval f.lower f.upper x)
    (hxh : inDomainInterval f.lower f.upper (x + h))
    (hdx : inDomainInterval df.lower df.upper x)
    (hpos : 0 < h)
    (hsmall : qabs h <= 1 / ((D.stepPrecision n : Nat) : Rat))
    (herr : 0 <= err)
    (hderivLo : center - err <=
      (df.compute x hdx (D.evalPrecision x h n)).lo)
    (hderivHi :
      (df.compute x hdx (D.evalPrecision x h n)).hi <= center + err)
    (hcurrent :
      (f.compute x hx (D.evalPrecision x h n)).lo <=
        (f.compute x hx (D.evalPrecision x h n)).hi) :
    QInterval.ContainsInterval
      ((f.compute x hx (D.evalPrecision x h n)).addInterval
        (QInterval.scaleByRat h
          ({ lo := center - (err + 2 * (precisionAtStage n).val)
             hi := center + (err + 2 * (precisionAtStage n).val) } : QInterval)))
      (f.compute (x + h) hxh (D.evalPrecision x h n)) := by
  let current := f.compute x hx (D.evalPrecision x h n)
  let next := f.compute (x + h) hxh (D.evalPrecision x h n)
  have hstep := HasDerivativeOnInterval.endpointDifference_contains_centered D
    hx hxh hdx hpos hsmall herr hderivLo hderivHi
  have hshift := QInterval.addInterval_contains
    (⟨Rat.le_refl, Rat.le_refl⟩ : current.ContainsInterval current)
    hstep
  have hcancel := QInterval.add_subInterval_contains_of_ordered
    current next (by simpa [current] using hcurrent)
  have hfinal := hshift.trans hcancel
  simpa [current, next] using hfinal

/-- Choosing the lower endpoints of valid represented values turns the
interval-valued Euler enclosure into a rational Euler recurrence with an
explicit per-cell residual. The residual consists of the current input-box
width and the derivative/evaluation uncertainty scaled by the step. -/
theorem HasDerivativeOnInterval.lowerEndpoint_eulerResidual
    {f df : FunctionOnInterval} (D : HasDerivativeOnInterval f df)
    {x h center err : Rat} {n : Nat}
    (hx : inDomainInterval f.lower f.upper x)
    (hxh : inDomainInterval f.lower f.upper (x + h))
    (hdx : inDomainInterval df.lower df.upper x)
    (hpos : 0 < h)
    (hsmall : qabs h <= 1 / ((D.stepPrecision n : Nat) : Rat))
    (herr : 0 <= err)
    (hderivLo : center - err <=
      (df.compute x hdx (D.evalPrecision x h n)).lo)
    (hderivHi :
      (df.compute x hdx (D.evalPrecision x h n)).hi <= center + err)
    (hcurrent :
      (f.compute x hx (D.evalPrecision x h n)).lo <=
        (f.compute x hx (D.evalPrecision x h n)).hi)
    (hnext :
      (f.compute (x + h) hxh (D.evalPrecision x h n)).lo <=
        (f.compute (x + h) hxh (D.evalPrecision x h n)).hi) :
    -( (f.compute x hx (D.evalPrecision x h n)).width +
        h * (err + 2 * (precisionAtStage n).val)) <=
        (f.compute (x + h) hxh (D.evalPrecision x h n)).lo -
          ((f.compute x hx (D.evalPrecision x h n)).lo + h * center) /\
      (f.compute (x + h) hxh (D.evalPrecision x h n)).lo -
          ((f.compute x hx (D.evalPrecision x h n)).lo + h * center) <=
        (f.compute x hx (D.evalPrecision x h n)).width +
          h * (err + 2 * (precisionAtStage n).val) := by
  let current := f.compute x hx (D.evalPrecision x h n)
  let next := f.compute (x + h) hxh (D.evalPrecision x h n)
  let derivativeError := err + 2 * (precisionAtStage n).val
  let increment := QInterval.scaleByRat h
    ({ lo := center - derivativeError, hi := center + derivativeError } : QInterval)
  have hvalue := HasDerivativeOnInterval.endpointValue_contains_euler D
    hx hxh hdx hpos hsmall herr hderivLo hderivHi hcurrent
  have hincrementLo : h * center - h * derivativeError <= increment.lo := by
    dsimp [increment, QInterval.scaleByRat]
    simp only [if_pos (Rat.le_of_lt hpos)]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg,
      Rat.add_assoc, Rat.add_comm]
  have hincrementHi : increment.hi <= h * center + h * derivativeError := by
    dsimp [increment, QInterval.scaleByRat]
    simp only [if_pos (Rat.le_of_lt hpos)]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg,
      Rat.add_assoc, Rat.add_comm]
  have hres := QInterval.lowerEndpoint_eulerResidual
    current increment next (h * center) (h * derivativeError)
    (by simpa [current] using hcurrent)
    (by simpa [next] using hnext)
    (by simpa [increment] using hincrementLo)
    (by simpa [increment] using hincrementHi)
    (by simpa [current, increment, derivativeError] using hvalue)
  simpa [current, next, derivativeError, QInterval.width] using hres

/-- The derivative certificate forces the two endpoint value boxes used at
its evaluator schedule to be narrow: their widths are at most the mesh size
times the requested derivative precision. This follows from the width of its
certified difference-quotient box, and is what controls inter-cell schedule
mismatches. -/
theorem HasDerivativeOnInterval.endpointValue_widths_le
    {f df : FunctionOnInterval} (D : HasDerivativeOnInterval f df)
    {x h : Rat} {n : Nat}
    (hx : inDomainInterval f.lower f.upper x)
    (hxh : inDomainInterval f.lower f.upper (x + h))
    (hdx : inDomainInterval df.lower df.upper x)
    (hpos : 0 < h)
    (hsmall : qabs h <= 1 / ((D.stepPrecision n : Nat) : Rat)) :
    (f.compute x hx (D.evalPrecision x h n)).width <=
        h * (precisionAtStage n).val /\
      (f.compute (x + h) hxh (D.evalPrecision x h n)).width <=
        h * (precisionAtStage n).val := by
  let current := f.compute x hx (D.evalPrecision x h n)
  let next := f.compute (x + h) hxh (D.evalPrecision x h n)
  have hclose := D.close x h n hx hxh hdx (Rat.ne_of_gt hpos) hsmall
  rcases hclose with ⟨_, _, hquotWidth, _⟩
  have hrecipPos : 0 < 1 / h := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.inv_pos.mpr hpos
  have hrecipNonneg : 0 <= 1 / h := Rat.le_of_lt hrecipPos
  have hwidthEq : (QInterval.differenceQuotient next current h).width =
      (1 / h) * (next.width + current.width) := by
    unfold QInterval.differenceQuotient QInterval.divRat
    rw [QInterval.scaleRat_width_of_nonneg hrecipNonneg,
      QInterval.sub_width]
  have hquotWidth' :
      (1 / h) * (next.width + current.width) <= (precisionAtStage n).val := by
    rw [← hwidthEq]
    exact hquotWidth
  have hrecipCancel : h * (1 / h) = 1 := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.mul_inv_cancel h (Rat.ne_of_gt hpos)
  have hsumWidth : next.width + current.width <=
      h * (precisionAtStage n).val := by
    have hscaled := Rat.mul_le_mul_of_nonneg_left hquotWidth'
      (Rat.le_of_lt hpos)
    calc
      next.width + current.width =
          h * ((1 / h) * (next.width + current.width)) := by
            rw [← Rat.mul_assoc, hrecipCancel, Rat.one_mul]
      _ <= h * (precisionAtStage n).val := hscaled
  have hcurrentNonneg : 0 <= current.width :=
    (f.valid_on x (f.defined_on x hx)).1 (D.evalPrecision x h n)
  have hnextNonneg : 0 <= next.width :=
    (f.valid_on (x + h) (f.defined_on (x + h) hxh)).1
      (D.evalPrecision x h n)
  constructor
  · have hle : current.width <= current.width + next.width := by
      have h := (Rat.add_le_add_left (c := current.width)).2 hnextNonneg
      simpa [Rat.add_zero] using h
    exact Rat.le_trans hle (by simpa [Rat.add_comm] using hsumWidth)
  · have hle : next.width <= next.width + current.width := by
      have h := (Rat.add_le_add_left (c := next.width)).2 hcurrentNonneg
      simpa [Rat.add_zero] using h
    exact Rat.le_trans hle hsumWidth

/-- Adjacent cells of one certified derivative may choose different
evaluator stages at their common rational endpoint. Their lower endpoint
samples differ by at most twice the cell width times the requested
derivative precision. This makes the stage change an explicit mesh residual
rather than an implicit alignment assumption. -/
theorem HasDerivativeOnInterval.adjacentMesh_lowerSamples_close
    {f df : FunctionOnInterval} (D : HasDerivativeOnInterval f df)
    {x h : Rat} {n : Nat}
    (hx : inDomainInterval f.lower f.upper x)
    (hxh : inDomainInterval f.lower f.upper (x + h))
    (hx2h : inDomainInterval f.lower f.upper (x + h + h))
    (hdx : inDomainInterval df.lower df.upper x)
    (hdxh : inDomainInterval df.lower df.upper (x + h))
    (hpos : 0 < h)
    (hsmall : qabs h <= 1 / ((D.stepPrecision n : Nat) : Rat)) :
    qabs
      ((f.compute (x + h) hxh (D.evalPrecision x h n)).lo -
        (f.compute (x + h) hxh (D.evalPrecision (x + h) h n)).lo) <=
      2 * h * (precisionAtStage n).val := by
  have hleft := HasDerivativeOnInterval.endpointValue_widths_le D
    hx hxh hdx hpos hsmall
  have hright := HasDerivativeOnInterval.endpointValue_widths_le D
    hxh hx2h hdxh hpos hsmall
  have hclose := FunctionOnInterval.lowerComputeEndpoints_close f
    (x + h) hxh (D.evalPrecision x h n) (D.evalPrecision (x + h) h n)
  calc
    qabs
        ((f.compute (x + h) hxh (D.evalPrecision x h n)).lo -
          (f.compute (x + h) hxh (D.evalPrecision (x + h) h n)).lo) <=
        (f.compute (x + h) hxh (D.evalPrecision x h n)).width +
          (f.compute (x + h) hxh (D.evalPrecision (x + h) h n)).width := hclose
    _ <= h * (precisionAtStage n).val + h * (precisionAtStage n).val :=
      rat_add_le_add hleft.2 hright.1
    _ = 2 * h * (precisionAtStage n).val := by
      grind [Rat.mul_assoc, Rat.add_comm]

/-- For the scalar equation `f' = f`, a represented derivative certificate
itself supplies the one-cell Euler residual: its derivative box is the same
valid value box as the current state. -/
theorem HasDerivativeOnInterval.selfLowerEndpoint_eulerResidual
    {f : FunctionOnInterval} (D : HasDerivativeOnInterval f f)
    {x h : Rat} {n : Nat}
    (hx : inDomainInterval f.lower f.upper x)
    (hxh : inDomainInterval f.lower f.upper (x + h))
    (hpos : 0 < h)
    (hsmall : qabs h <= 1 / ((D.stepPrecision n : Nat) : Rat)) :
    qabs
      ((f.compute (x + h) hxh (D.evalPrecision x h n)).lo -
        ((f.compute x hx (D.evalPrecision x h n)).lo +
          h * (f.compute x hx (D.evalPrecision x h n)).lo)) <=
      (f.compute x hx (D.evalPrecision x h n)).width +
        h * ((f.compute x hx (D.evalPrecision x h n)).width +
          2 * (precisionAtStage n).val) := by
  let current := f.compute x hx (D.evalPrecision x h n)
  let next := f.compute (x + h) hxh (D.evalPrecision x h n)
  have hcurrent : current.lo <= current.hi := by
    have hw := (f.valid_on x (f.defined_on x hx)).1
      (D.evalPrecision x h n)
    unfold QInterval.width at hw
    exact (Rat.le_iff_sub_nonneg current.lo current.hi).2 hw
  have hnext : next.lo <= next.hi := by
    have hw := (f.valid_on (x + h) (f.defined_on (x + h) hxh)).1
      (D.evalPrecision x h n)
    unfold QInterval.width at hw
    exact (Rat.le_iff_sub_nonneg next.lo next.hi).2 hw
  have hwidth : 0 <= current.width :=
    (f.valid_on x (f.defined_on x hx)).1 (D.evalPrecision x h n)
  have hres := HasDerivativeOnInterval.lowerEndpoint_eulerResidual D
    hx hxh hx hpos hsmall hwidth
    (by
      unfold QInterval.width
      have hdiff : current.lo - current.hi <= 0 := by
        have h := (Rat.add_le_add_right (c := -current.hi)).2 hcurrent
        simpa [Rat.sub_eq_add_neg, Rat.add_neg_cancel] using h
      calc
        current.lo - (current.hi - current.lo) =
            (current.lo - current.hi) + current.lo := by
          grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
        _ <= 0 + current.lo := (Rat.add_le_add_right).2 hdiff
        _ = current.lo := Rat.zero_add _)
    (by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm])
    hcurrent hnext
  rcases hres with ⟨hlo, hhi⟩
  exact qabs_le_of_bounds (by simpa [current, next] using hlo)
    (by simpa [current, next] using hhi)

/-- Componentwise derivative evidence gives a finite Euler residual bound
for a represented vector function. The center and error are supplied per
coordinate, so callers can instantiate them with certified enclosures of
`A(t) x + b(t)` without baking in a particular coefficient evaluator. -/
theorem FunctionVectorOnInterval.lowerEulerResidual
    {dimension : Nat} {lower upper : Rat}
    (F DF : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    {x h : Rat} (hx : inDomainInterval lower upper x)
    (hxh : inDomainInterval lower upper (x + h))
    (stage : Fin dimension -> Nat)
    (center err : RatVector dimension)
    (hpos : 0 < h)
    (hsmall : forall i,
      qabs h <= 1 / ((D i).stepPrecision (stage i) : Nat))
    (herr : forall i, 0 <= err i)
    (hderivLo : forall i,
      center i - err i <=
        (DF.computeBoxes x hx
          (fun j => (D j).evalPrecision x h (stage j)) i).lo)
    (hderivHi : forall i,
      (DF.computeBoxes x hx
        (fun j => (D j).evalPrecision x h (stage j)) i).hi <=
          center i + err i) :
    forall i,
      qabs ((F.lowerSample (x + h) hxh
          (fun j => (D j).evalPrecision x h (stage j)) i) -
        (F.lowerSample x hx
          (fun j => (D j).evalPrecision x h (stage j)) i + h * center i)) <=
        (F.computeBoxes x hx
          (fun j => (D j).evalPrecision x h (stage j)) i).width +
          h * (err i + 2 * (precisionAtStage (stage i)).val) := by
  intro i
  let component := F.component i
  let p := (D i).evalPrecision x h (stage i)
  have hcurrent :
      (component.compute x (F.domainAt i x hx) p).lo <=
        (component.compute x (F.domainAt i x hx) p).hi := by
    have hv := (component.valid_on x
      (component.defined_on x (F.domainAt i x hx))).1 p
    unfold QInterval.width at hv
    exact (Rat.le_iff_sub_nonneg _ _).2 hv
  have hnext :
      (component.compute (x + h) (F.domainAt i (x + h) hxh) p).lo <=
        (component.compute (x + h) (F.domainAt i (x + h) hxh) p).hi := by
    have hv := (component.valid_on (x + h)
      (component.defined_on (x + h) (F.domainAt i (x + h) hxh))).1 p
    unfold QInterval.width at hv
    exact (Rat.le_iff_sub_nonneg _ _).2 hv
  have hcomponent := HasDerivativeOnInterval.lowerEndpoint_eulerResidual (D i)
    (F.domainAt i x hx) (F.domainAt i (x + h) hxh)
    (DF.domainAt i x hx) hpos (hsmall i) (herr i)
    (by simpa [p, FunctionVectorOnInterval.computeBoxes] using hderivLo i)
    (by simpa [p, FunctionVectorOnInterval.computeBoxes] using hderivHi i)
    hcurrent hnext
  have habsolute := qabs_le_of_bounds hcomponent.1 hcomponent.2
  simpa [p, FunctionVectorOnInterval.computeBoxes,
    FunctionVectorOnInterval.lowerSample] using habsolute

/-- A rational sample of the inhomogeneous linear field `A(x)u+b(x)` can be
inserted directly into the componentwise derivative-to-Euler estimate. The
only analytic inputs are the certified derivative boxes; the state sample,
matrix action, and forcing term remain explicit rational data. -/
theorem FunctionVectorOnInterval.lowerEulerResidual_forced
    {dimension : Nat} {lower upper : Rat}
    (F DF : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    {x h : Rat} (hx : inDomainInterval lower upper x)
    (hxh : inDomainInterval lower upper (x + h))
    (stage : Fin dimension -> Nat)
    (A : RatMatrix dimension) (forcing err : RatVector dimension)
    (hpos : 0 < h)
    (hsmall : forall i,
      qabs h <= 1 / ((D i).stepPrecision (stage i) : Nat))
    (herr : forall i, 0 <= err i)
    (hderivLo : forall i,
      matrixApply A (F.lowerSample x hx
        (fun j => (D j).evalPrecision x h (stage j))) i + forcing i - err i <=
        (DF.computeBoxes x hx
          (fun j => (D j).evalPrecision x h (stage j)) i).lo)
    (hderivHi : forall i,
      (DF.computeBoxes x hx
        (fun j => (D j).evalPrecision x h (stage j)) i).hi <=
        matrixApply A (F.lowerSample x hx
          (fun j => (D j).evalPrecision x h (stage j))) i + forcing i + err i) :
    forall i,
      qabs ((F.lowerSample (x + h) hxh
          (fun j => (D j).evalPrecision x h (stage j)) i) -
        (F.lowerSample x hx (fun j => (D j).evalPrecision x h (stage j)) i +
          h * (matrixApply A (F.lowerSample x hx
            (fun j => (D j).evalPrecision x h (stage j))) i + forcing i))) <=
        (F.computeBoxes x hx
          (fun j => (D j).evalPrecision x h (stage j)) i).width +
          h * (err i + 2 * (precisionAtStage (stage i)).val) := by
  let center := fun i => matrixApply A (F.lowerSample x hx
    (fun j => (D j).evalPrecision x h (stage j))) i + forcing i
  have hres := FunctionVectorOnInterval.lowerEulerResidual F DF D hx hxh
    stage center err hpos hsmall herr
    (by simpa [center] using hderivLo)
    (by simpa [center] using hderivHi)
  simpa [center] using hres

/-- Vector-norm form of the represented-function Euler estimate for
`u'=A(x)u+b(x)`. The bound is the finite sum of each input box width and
its scaled derivative/evaluation uncertainty, exactly the residual budget
used by the finite trajectory comparison theorem. -/
theorem FunctionVectorOnInterval.lowerEulerResidual_forced_norm
    {dimension : Nat} {lower upper : Rat}
    (F DF : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    {x h : Rat} (hx : inDomainInterval lower upper x)
    (hxh : inDomainInterval lower upper (x + h))
    (stage : Fin dimension -> Nat)
    (A : RatMatrix dimension) (forcing err : RatVector dimension)
    (hpos : 0 < h)
    (hsmall : forall i,
      qabs h <= 1 / ((D i).stepPrecision (stage i) : Nat))
    (herr : forall i, 0 <= err i)
    (hderivLo : forall i,
      matrixApply A (F.lowerSample x hx
        (fun j => (D j).evalPrecision x h (stage j))) i + forcing i - err i <=
        (DF.computeBoxes x hx
          (fun j => (D j).evalPrecision x h (stage j)) i).lo)
    (hderivHi : forall i,
      (DF.computeBoxes x hx
        (fun j => (D j).evalPrecision x h (stage j)) i).hi <=
        matrixApply A (F.lowerSample x hx
          (fun j => (D j).evalPrecision x h (stage j))) i + forcing i + err i) :
    vectorAbsSum
      (vectorSub
        (F.lowerSample (x + h) hxh
          (fun j => (D j).evalPrecision x h (stage j)))
        (vectorAdd
          (matrixApply
            (matrixAdd (matrixIdentity dimension) (matrixScale h A))
            (F.lowerSample x hx
              (fun j => (D j).evalPrecision x h (stage j))))
          (vectorScale h forcing))) <=
      finiteSum (fun i =>
        (F.computeBoxes x hx
          (fun j => (D j).evalPrecision x h (stage j)) i).width +
          h * (err i + 2 * (precisionAtStage (stage i)).val)) := by
  let evalStage := fun j => (D j).evalPrecision x h (stage j)
  let bound := fun i =>
    (F.computeBoxes x hx evalStage i).width +
      h * (err i + 2 * (precisionAtStage (stage i)).val)
  have hcomponent : forall i,
      -bound i <=
          F.lowerSample (x + h) hxh evalStage i -
            (F.lowerSample x hx evalStage i +
              h * (matrixApply A (F.lowerSample x hx evalStage) i + forcing i)) /\
        F.lowerSample (x + h) hxh evalStage i -
            (F.lowerSample x hx evalStage i +
              h * (matrixApply A (F.lowerSample x hx evalStage) i + forcing i)) <=
          bound i := by
    intro i
    have hres := FunctionVectorOnInterval.lowerEulerResidual_forced
      F DF D hx hxh stage A forcing err hpos hsmall herr hderivLo hderivHi i
    have hboundNonneg : 0 <= bound i := by
      dsimp [bound]
      have hwidth : 0 <= (F.computeBoxes x hx evalStage i).width := by
        have hv := ((F.component i).valid_on x
          ((F.component i).defined_on x (F.domainAt i x hx))).1 (evalStage i)
        exact hv
      have herrPrecision : 0 <=
          err i + 2 * (precisionAtStage (stage i)).val :=
        Rat.add_nonneg (herr i)
          (Rat.mul_nonneg (by decide)
            (Rat.le_of_lt (precisionAtStage (stage i)).property))
      exact Rat.add_nonneg hwidth (Rat.mul_nonneg (Rat.le_of_lt hpos) herrPrecision)
    have hlowerUpper := qabs_bounds_of_le hboundNonneg hres
    simpa [evalStage, bound, vectorAdd, vectorScale,
      matrixApply_eulerStep_decomposition] using hlowerUpper
  apply forcedEulerResidual_vectorAbsSum_le A h
    (F.lowerSample x hx evalStage)
    (F.lowerSample (x + h) hxh evalStage) forcing bound hcomponent

/-- The Euler residual for successive mesh states also pays the certified
change between the endpoint evaluator used by one cell and the start
evaluator used by the next. This makes the estimate usable as an actual
trajectory recurrence when component schedules depend on the rational
evaluation point. -/
theorem FunctionVectorOnInterval.lowerEulerResidual_forced_norm_adjacent
    {dimension : Nat} {lower upper : Rat}
    (F DF : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    {x h : Rat} (hx : inDomainInterval lower upper x)
    (hxh : inDomainInterval lower upper (x + h))
    (hx2h : inDomainInterval lower upper (x + h + h))
    (stage : Fin dimension -> Nat)
    (A : RatMatrix dimension) (forcing err : RatVector dimension)
    (hpos : 0 < h)
    (hsmall : forall i,
      qabs h <= 1 / ((D i).stepPrecision (stage i) : Nat))
    (herr : forall i, 0 <= err i)
    (hderivLo : forall i,
      matrixApply A (F.lowerSample x hx
        (fun j => (D j).evalPrecision x h (stage j))) i + forcing i - err i <=
        (DF.computeBoxes x hx
          (fun j => (D j).evalPrecision x h (stage j)) i).lo)
    (hderivHi : forall i,
      (DF.computeBoxes x hx
        (fun j => (D j).evalPrecision x h (stage j)) i).hi <=
        matrixApply A (F.lowerSample x hx
          (fun j => (D j).evalPrecision x h (stage j))) i + forcing i + err i) :
    vectorAbsSum
      (vectorSub
        (F.lowerSample (x + h) hxh
          (fun j => (D j).evalPrecision (x + h) h (stage j)))
        (vectorAdd
          (matrixApply
            (matrixAdd (matrixIdentity dimension) (matrixScale h A))
            (F.lowerSample x hx
              (fun j => (D j).evalPrecision x h (stage j))))
          (vectorScale h forcing))) <=
      finiteSum (fun i =>
        ((F.component i).compute x (F.domainAt i x hx)
          ((D i).evalPrecision x h (stage i))).width +
          h * (err i + 4 * (precisionAtStage (stage i)).val)) := by
  let currentStage := fun j => (D j).evalPrecision x h (stage j)
  let endpointStage := fun j => (D j).evalPrecision (x + h) h (stage j)
  let current := F.lowerSample x hx currentStage
  let oldEndpoint := F.lowerSample (x + h) hxh currentStage
  let newStart := F.lowerSample (x + h) hxh endpointStage
  let target := vectorAdd
    (matrixApply (matrixAdd (matrixIdentity dimension) (matrixScale h A)) current)
    (vectorScale h forcing)
  let localBound := fun i =>
    (F.computeBoxes x hx currentStage i).width +
      h * (err i + 2 * (precisionAtStage (stage i)).val)
  let scheduleBound := fun i => 2 * h * (precisionAtStage (stage i)).val
  have hlocal := FunctionVectorOnInterval.lowerEulerResidual_forced_norm
    F DF D hx hxh stage A forcing err hpos hsmall herr hderivLo hderivHi
  have hschedule : vectorAbsSum (vectorSub newStart oldEndpoint) <=
      finiteSum scheduleBound := by
    apply vectorAbsSum_le_of_component_bounds
    intro i
    have hclose := HasDerivativeOnInterval.adjacentMesh_lowerSamples_close
      (D i) (F.domainAt i x hx) (F.domainAt i (x + h) hxh)
      (F.domainAt i (x + h + h) hx2h)
      (DF.domainAt i x hx) (DF.domainAt i (x + h) hxh)
      hpos (hsmall i)
    have hclose' : qabs (newStart i - oldEndpoint i) <= scheduleBound i := by
      have hneg : newStart i - oldEndpoint i =
          - (oldEndpoint i - newStart i) := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      rw [hneg, qabs_neg]
      simpa [newStart, oldEndpoint, scheduleBound, currentStage, endpointStage,
        FunctionVectorOnInterval.lowerSample,
        FunctionVectorOnInterval.computeBoxes] using hclose
    simpa [vectorSub] using hclose'
  have hdecomp : vectorSub newStart target =
      vectorAdd (vectorSub newStart oldEndpoint)
        (vectorSub oldEndpoint target) := by
    funext i
    grind [vectorSub, vectorAdd, Rat.sub_eq_add_neg,
      Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
  have htotal : vectorAbsSum (vectorSub newStart target) <=
      finiteSum scheduleBound + finiteSum localBound := by
    calc
      vectorAbsSum (vectorSub newStart target) =
          vectorAbsSum
            (vectorAdd (vectorSub newStart oldEndpoint)
              (vectorSub oldEndpoint target)) := by rw [hdecomp]
      _ <= vectorAbsSum (vectorSub newStart oldEndpoint) +
            vectorAbsSum (vectorSub oldEndpoint target) :=
          DiscreteLinearSystem.vectorAbsSum_add_le _ _
      _ <= finiteSum scheduleBound + finiteSum localBound :=
          rat_add_le_add hschedule hlocal
  calc
    vectorAbsSum
        (vectorSub
          (F.lowerSample (x + h) hxh endpointStage)
          (vectorAdd
            (matrixApply
              (matrixAdd (matrixIdentity dimension) (matrixScale h A))
              (F.lowerSample x hx currentStage))
            (vectorScale h forcing))) =
        vectorAbsSum (vectorSub newStart target) := by
          simp [newStart, target, current]
    _ <= finiteSum scheduleBound + finiteSum localBound := htotal
    _ = finiteSum (fun i => scheduleBound i + localBound i) :=
      (finiteSum_add scheduleBound localBound).symm
    _ = finiteSum (fun i =>
          (F.computeBoxes x hx currentStage i).width +
            h * (err i + 4 * (precisionAtStage (stage i)).val)) := by
          congr 1
          funext i
          dsimp [scheduleBound, localBound]
          grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
            Rat.mul_assoc, Rat.mul_comm]

/-- Refinement-sized version of the adjacent-cell residual. The current
value-box width is at most `h * precisionAtStage n`, so each component's
Euler defect is at most `h * (fieldError + 5 * precisionAtStage n)`. -/
theorem FunctionVectorOnInterval.lowerEulerResidual_forced_norm_adjacent_refined
    {dimension : Nat} {lower upper : Rat}
    (F DF : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    {x h : Rat} (hx : inDomainInterval lower upper x)
    (hxh : inDomainInterval lower upper (x + h))
    (hx2h : inDomainInterval lower upper (x + h + h))
    (stage : Fin dimension -> Nat)
    (A : RatMatrix dimension) (forcing err : RatVector dimension)
    (hpos : 0 < h)
    (hsmall : forall i,
      qabs h <= 1 / ((D i).stepPrecision (stage i) : Nat))
    (herr : forall i, 0 <= err i)
    (hderivLo : forall i,
      matrixApply A (F.lowerSample x hx
        (fun j => (D j).evalPrecision x h (stage j))) i + forcing i - err i <=
        (DF.computeBoxes x hx
          (fun j => (D j).evalPrecision x h (stage j)) i).lo)
    (hderivHi : forall i,
      (DF.computeBoxes x hx
        (fun j => (D j).evalPrecision x h (stage j)) i).hi <=
        matrixApply A (F.lowerSample x hx
          (fun j => (D j).evalPrecision x h (stage j))) i + forcing i + err i) :
    vectorAbsSum
      (vectorSub
        (F.lowerSample (x + h) hxh
          (fun j => (D j).evalPrecision (x + h) h (stage j)))
        (vectorAdd
          (matrixApply
            (matrixAdd (matrixIdentity dimension) (matrixScale h A))
            (F.lowerSample x hx
              (fun j => (D j).evalPrecision x h (stage j))))
          (vectorScale h forcing))) <=
      finiteSum (fun i =>
        h * (err i + 5 * (precisionAtStage (stage i)).val)) := by
  have hcoarse := FunctionVectorOnInterval.lowerEulerResidual_forced_norm_adjacent
    F DF D hx hxh hx2h stage A forcing err hpos hsmall herr hderivLo hderivHi
  apply Rat.le_trans hcoarse
  apply finiteSum_le
  intro i
  have hwidth := HasDerivativeOnInterval.endpointValue_widths_le (D i)
    (F.domainAt i x hx) (F.domainAt i (x + h) hxh)
    (DF.domainAt i x hx) hpos (hsmall i)
  calc
    (F.computeBoxes x hx
        (fun j => (D j).evalPrecision x h (stage j)) i).width +
        h * (err i + 4 * (precisionAtStage (stage i)).val) <=
        h * (precisionAtStage (stage i)).val +
          h * (err i + 4 * (precisionAtStage (stage i)).val) := by
            exact (Rat.add_le_add_right
              (c := h * (err i + 4 * (precisionAtStage (stage i)).val))).2 hwidth.1
    _ = h * (err i + 5 * (precisionAtStage (stage i)).val) := by
      grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
        Rat.mul_assoc, Rat.mul_comm]

/-- Refined one-cell residual when no following cell is available for the
evaluator-schedule comparison. This endpoint form is used on the final cell
of a closed rational mesh, so it does not require an evaluation beyond the
declared domain. -/
theorem FunctionVectorOnInterval.lowerEulerResidual_forced_norm_refined
    {dimension : Nat} {lower upper : Rat}
    (F DF : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    {x h : Rat} (hx : inDomainInterval lower upper x)
    (hxh : inDomainInterval lower upper (x + h))
    (stage : Fin dimension -> Nat)
    (A : RatMatrix dimension) (forcing err : RatVector dimension)
    (hpos : 0 < h)
    (hsmall : forall i,
      qabs h <= 1 / ((D i).stepPrecision (stage i) : Nat))
    (herr : forall i, 0 <= err i)
    (hderivLo : forall i,
      matrixApply A (F.lowerSample x hx
        (fun j => (D j).evalPrecision x h (stage j))) i + forcing i - err i <=
        (DF.computeBoxes x hx
          (fun j => (D j).evalPrecision x h (stage j)) i).lo)
    (hderivHi : forall i,
      (DF.computeBoxes x hx
        (fun j => (D j).evalPrecision x h (stage j)) i).hi <=
        matrixApply A (F.lowerSample x hx
          (fun j => (D j).evalPrecision x h (stage j))) i + forcing i + err i) :
    vectorAbsSum
      (vectorSub
        (F.lowerSample (x + h) hxh
          (fun j => (D j).evalPrecision x h (stage j)))
        (vectorAdd
          (matrixApply
            (matrixAdd (matrixIdentity dimension) (matrixScale h A))
            (F.lowerSample x hx
              (fun j => (D j).evalPrecision x h (stage j))))
          (vectorScale h forcing))) <=
      finiteSum (fun i =>
        h * (err i + 3 * (precisionAtStage (stage i)).val)) := by
  have hcoarse := FunctionVectorOnInterval.lowerEulerResidual_forced_norm
    F DF D hx hxh stage A forcing err hpos hsmall herr hderivLo hderivHi
  apply Rat.le_trans hcoarse
  apply finiteSum_le
  intro i
  have hwidth := HasDerivativeOnInterval.endpointValue_widths_le (D i)
    (F.domainAt i x hx) (F.domainAt i (x + h) hxh)
    (DF.domainAt i x hx) hpos (hsmall i)
  calc
    (F.computeBoxes x hx (fun j => (D j).evalPrecision x h (stage j)) i).width +
        h * (err i + 2 * (precisionAtStage (stage i)).val) <=
        h * (precisionAtStage (stage i)).val +
          h * (err i + 2 * (precisionAtStage (stage i)).val) := by
            exact (Rat.add_le_add_right).2 hwidth.1
    _ = h * (err i + 3 * (precisionAtStage (stage i)).val) := by
      grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
        Rat.mul_assoc, Rat.mul_comm]

/-- Two represented vector solutions of the same rational linear field have
jointly bounded one-cell Euler defects. This is the analytic input consumed
by the finite pairwise recurrence theorem: each defect is derived from its
own derivative boxes, while the coefficient matrix and forcing are shared. -/
theorem pairwiseLowerEulerResidual_forced_norm_adjacent_refined
    {dimension : Nat} {lower upper : Rat}
    (F DF G DG : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i))
    {x h : Rat} (hx : inDomainInterval lower upper x)
    (hxh : inDomainInterval lower upper (x + h))
    (hx2h : inDomainInterval lower upper (x + h + h))
    (stage : Fin dimension -> Nat)
    (A : RatMatrix dimension) (forcing errF errG : RatVector dimension)
    (hpos : 0 < h)
    (hsmallF : forall i,
      qabs h <= 1 / ((D i).stepPrecision (stage i) : Nat))
    (hsmallG : forall i,
      qabs h <= 1 / ((E i).stepPrecision (stage i) : Nat))
    (herrF : forall i, 0 <= errF i)
    (herrG : forall i, 0 <= errG i)
    (hderivLoF : forall i,
      matrixApply A (F.lowerSample x hx
        (fun j => (D j).evalPrecision x h (stage j))) i + forcing i - errF i <=
        (DF.computeBoxes x hx
          (fun j => (D j).evalPrecision x h (stage j)) i).lo)
    (hderivHiF : forall i,
      (DF.computeBoxes x hx
        (fun j => (D j).evalPrecision x h (stage j)) i).hi <=
        matrixApply A (F.lowerSample x hx
          (fun j => (D j).evalPrecision x h (stage j))) i + forcing i + errF i)
    (hderivLoG : forall i,
      matrixApply A (G.lowerSample x hx
        (fun j => (E j).evalPrecision x h (stage j))) i + forcing i - errG i <=
        (DG.computeBoxes x hx
          (fun j => (E j).evalPrecision x h (stage j)) i).lo)
    (hderivHiG : forall i,
      (DG.computeBoxes x hx
        (fun j => (E j).evalPrecision x h (stage j)) i).hi <=
        matrixApply A (G.lowerSample x hx
          (fun j => (E j).evalPrecision x h (stage j))) i + forcing i + errG i) :
    vectorAbsSum
        (vectorSub
          (F.lowerSample (x + h) hxh
            (fun j => (D j).evalPrecision (x + h) h (stage j)))
          (vectorAdd
            (matrixApply
              (matrixAdd (matrixIdentity dimension) (matrixScale h A))
              (F.lowerSample x hx
                (fun j => (D j).evalPrecision x h (stage j))))
            (vectorScale h forcing))) +
      vectorAbsSum
        (vectorSub
          (G.lowerSample (x + h) hxh
            (fun j => (E j).evalPrecision (x + h) h (stage j)))
          (vectorAdd
            (matrixApply
              (matrixAdd (matrixIdentity dimension) (matrixScale h A))
              (G.lowerSample x hx
                (fun j => (E j).evalPrecision x h (stage j))))
            (vectorScale h forcing))) <=
      finiteSum (fun i => h * (errF i + 5 * (precisionAtStage (stage i)).val)) +
        finiteSum (fun i => h * (errG i + 5 * (precisionAtStage (stage i)).val)) := by
  have hF := FunctionVectorOnInterval.lowerEulerResidual_forced_norm_adjacent_refined
    F DF D hx hxh hx2h stage A forcing errF hpos hsmallF herrF
    hderivLoF hderivHiF
  have hG := FunctionVectorOnInterval.lowerEulerResidual_forced_norm_adjacent_refined
    G DG E hx hxh hx2h stage A forcing errG hpos hsmallG herrG
    hderivLoG hderivHiG
  exact rat_add_le_add hF hG

/-- Paired endpoint residual estimate for the final cell of a closed mesh.
It uses only the interval endpoints themselves and therefore supports
functions whose declared domains do not extend past the target interval. -/
theorem pairwiseLowerEulerResidual_forced_norm_refined
    {dimension : Nat} {lower upper : Rat}
    (F DF G DG : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i))
    {x h : Rat} (hx : inDomainInterval lower upper x)
    (hxh : inDomainInterval lower upper (x + h))
    (stage : Fin dimension -> Nat)
    (A : RatMatrix dimension) (forcing errF errG : RatVector dimension)
    (hpos : 0 < h)
    (hsmallF : forall i,
      qabs h <= 1 / ((D i).stepPrecision (stage i) : Nat))
    (hsmallG : forall i,
      qabs h <= 1 / ((E i).stepPrecision (stage i) : Nat))
    (herrF : forall i, 0 <= errF i)
    (herrG : forall i, 0 <= errG i)
    (hderivLoF : forall i,
      matrixApply A (F.lowerSample x hx
        (fun j => (D j).evalPrecision x h (stage j))) i + forcing i - errF i <=
        (DF.computeBoxes x hx
          (fun j => (D j).evalPrecision x h (stage j)) i).lo)
    (hderivHiF : forall i,
      (DF.computeBoxes x hx
        (fun j => (D j).evalPrecision x h (stage j)) i).hi <=
        matrixApply A (F.lowerSample x hx
          (fun j => (D j).evalPrecision x h (stage j))) i + forcing i + errF i)
    (hderivLoG : forall i,
      matrixApply A (G.lowerSample x hx
        (fun j => (E j).evalPrecision x h (stage j))) i + forcing i - errG i <=
        (DG.computeBoxes x hx
          (fun j => (E j).evalPrecision x h (stage j)) i).lo)
    (hderivHiG : forall i,
      (DG.computeBoxes x hx
        (fun j => (E j).evalPrecision x h (stage j)) i).hi <=
        matrixApply A (G.lowerSample x hx
          (fun j => (E j).evalPrecision x h (stage j))) i + forcing i + errG i) :
    vectorAbsSum
        (vectorSub
          (F.lowerSample (x + h) hxh
            (fun j => (D j).evalPrecision x h (stage j)))
          (vectorAdd
            (matrixApply
              (matrixAdd (matrixIdentity dimension) (matrixScale h A))
              (F.lowerSample x hx
                (fun j => (D j).evalPrecision x h (stage j))))
            (vectorScale h forcing))) +
      vectorAbsSum
        (vectorSub
          (G.lowerSample (x + h) hxh
            (fun j => (E j).evalPrecision x h (stage j)))
          (vectorAdd
            (matrixApply
              (matrixAdd (matrixIdentity dimension) (matrixScale h A))
              (G.lowerSample x hx
                (fun j => (E j).evalPrecision x h (stage j))))
            (vectorScale h forcing))) <=
      finiteSum (fun i => h * (errF i + 3 * (precisionAtStage (stage i)).val)) +
        finiteSum (fun i => h * (errG i + 3 * (precisionAtStage (stage i)).val)) := by
  have hF := FunctionVectorOnInterval.lowerEulerResidual_forced_norm_refined
    F DF D hx hxh stage A forcing errF hpos hsmallF herrF
    hderivLoF hderivHiF
  have hG := FunctionVectorOnInterval.lowerEulerResidual_forced_norm_refined
    G DG E hx hxh stage A forcing errG hpos hsmallG herrG
    hderivLoG hderivHiG
  exact rat_add_le_add hF hG

/-- End-to-end constructive comparison on a finite rational mesh. The
sample paths are built from the supplied interval functions and derivative
evaluators; per-cell Euler residuals are derived from derivative-box
inclusions, with the final cell handled one-sidedly at the closed endpoint.
The result applies on an interval of any length and returns the explicit
finite growth envelope. The only numerical inputs are explicit coefficient
and field-error bounds, together with an initial sample discrepancy. -/
theorem linearODE_solution_mesh_compare
    {dimension : Nat} {lower upper : Rat} (cells : Nat)
    (F DF G DG : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i))
    (nodes : Nat -> Rat) (nodeMem : forall n, n <= cells ->
      inDomainInterval lower upper (nodes n))
    (meshStep : Rat) (stage : Fin dimension -> Nat)
    (coefficient : Nat -> RatMatrix dimension)
    (forcing : Nat -> RatVector dimension)
    (errF errG : RatVector dimension)
    (entryBound initialBound : Rat)
    (hmeshStep : 0 < meshStep)
    (hnodes : forall n, n < cells ->
      nodes (n + 1) = nodes n + meshStep)
    (hentryBound : 0 <= entryBound)
    (hentry : forall n, n < cells -> forall i j,
      qabs (coefficient n i j) <= entryBound)
    (hinitial : vectorAbsSum (vectorSub
      (uniformMeshLowerSample F DF D nodes cells nodeMem meshStep stage 0)
      (uniformMeshLowerSample G DG E nodes cells nodeMem meshStep stage 0)) <=
        initialBound)
    (hsmallF : forall n, n < cells -> forall i,
      qabs meshStep <= 1 / ((D i).stepPrecision (stage i) : Nat))
    (hsmallG : forall n, n < cells -> forall i,
      qabs meshStep <= 1 / ((E i).stepPrecision (stage i) : Nat))
    (herrF : forall i, 0 <= errF i)
    (herrG : forall i, 0 <= errG i)
    (hderivLoF : forall n, (hn : n < cells) -> forall i,
      matrixApply (coefficient n)
          (F.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (D j).evalPrecision (nodes n) meshStep (stage j))) i +
        forcing n i - errF i <=
        (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).lo)
    (hderivHiF : forall n, (hn : n < cells) -> forall i,
      (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).hi <=
        matrixApply (coefficient n)
          (F.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (D j).evalPrecision (nodes n) meshStep (stage j))) i +
          forcing n i + errF i)
    (hderivLoG : forall n, (hn : n < cells) -> forall i,
      matrixApply (coefficient n)
          (G.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (E j).evalPrecision (nodes n) meshStep (stage j))) i +
        forcing n i - errG i <=
        (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).lo)
    (hderivHiG : forall n, (hn : n < cells) -> forall i,
      (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).hi <=
        matrixApply (coefficient n)
          (G.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (E j).evalPrecision (nodes n) meshStep (stage j))) i +
          forcing n i + errG i) :
    vectorAbsSum (vectorSub
      (uniformMeshLowerSample F DF D nodes cells nodeMem meshStep stage cells)
      (uniformMeshLowerSample G DG E nodes cells nodeMem meshStep stage cells)) <=
      ComputableAnalysis.LinearODE.DiscreteLinearSystem.eulerErrorEnvelope
        (1 + meshStep * finiteSum (fun _ : Fin dimension => entryBound))
        initialBound
        (fun _ =>
          finiteSum (fun i => meshStep *
            (errF i + 5 * (precisionAtStage (stage i)).val)) +
          finiteSum (fun i => meshStep *
            (errG i + 5 * (precisionAtStage (stage i)).val))) cells := by
  let left := uniformMeshLowerSample F DF D nodes cells nodeMem meshStep stage
  let right := uniformMeshLowerSample G DG E nodes cells nodeMem meshStep stage
  let step := fun n => matrixAdd (matrixIdentity dimension)
    (matrixScale meshStep (coefficient n))
  let scaledForcing := fun n => vectorScale meshStep (forcing n)
  let leftResidual := sampledEulerResidual left step scaledForcing
  let rightResidual := sampledEulerResidual right step scaledForcing
  let coefficientStep := meshStep *
    finiteSum (fun _ : Fin dimension => entryBound)
  let residualBound :=
    finiteSum (fun i => meshStep *
      (errF i + 5 * (precisionAtStage (stage i)).val)) +
    finiteSum (fun i => meshStep *
      (errG i + 5 * (precisionAtStage (stage i)).val))
  have hentryNonneg : 0 <= finiteSum (fun _ : Fin dimension => entryBound) :=
    finiteSum_nonneg (fun _ => hentryBound)
  have hcoefficientNonneg : 0 <= coefficientStep :=
    Rat.mul_nonneg (Rat.le_of_lt hmeshStep) hentryNonneg
  have hresidualNonneg : 0 <= residualBound := by
    dsimp [residualBound]
    apply Rat.add_nonneg
    · apply finiteSum_nonneg
      intro i
      exact Rat.mul_nonneg (Rat.le_of_lt hmeshStep)
        (Rat.add_nonneg (herrF i)
          (Rat.mul_nonneg (by decide)
            (Rat.le_of_lt (precisionAtStage (stage i)).property)))
    · apply finiteSum_nonneg
      intro i
      exact Rat.mul_nonneg (Rat.le_of_lt hmeshStep)
        (Rat.add_nonneg (herrG i)
          (Rat.mul_nonneg (by decide)
            (Rat.le_of_lt (precisionAtStage (stage i)).property)))
  have hleftStep : forall n, n < cells ->
      left (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (left n)) (scaledForcing n))
        (leftResidual n) := by
    intro n hn
    exact sampledEulerResidual_step left step scaledForcing n
  have hrightStep : forall n, n < cells ->
      right (n + 1) = vectorAdd
        (vectorAdd (matrixApply (step n) (right n)) (scaledForcing n))
        (rightResidual n) := by
    intro n hn
    exact sampledEulerResidual_step right step scaledForcing n
  have hcolumns : forall n, n < cells -> forall j,
      matrixColumnAbsSum (step n) j <= 1 + coefficientStep := by
    intro n hn j
    exact matrixColumnAbsSum_eulerStep_le_of_nonneg_entry_bound
      (coefficient n) meshStep entryBound (Rat.le_of_lt hmeshStep)
      (hentry n hn) j
  have hresidual : forall n, n < cells ->
      vectorAbsSum (leftResidual n) + vectorAbsSum (rightResidual n) <=
        residualBound := by
    intro n hn
    by_cases hInterior : n + 1 < cells
    · have hn1 : n + 1 <= cells := by omega
      have hn2 : n + 2 <= cells := by omega
      have hnode1 : nodes (n + 1) = nodes n + meshStep := hnodes n hn
      have hnode2 : nodes (n + 2) = nodes (n + 1) + meshStep := hnodes (n + 1) hInterior
      have hx : inDomainInterval lower upper (nodes n) := nodeMem n (by omega)
      have hxh : inDomainInterval lower upper (nodes n + meshStep) := by
        rw [← hnode1]
        exact nodeMem (n + 1) hn1
      have hx2h : inDomainInterval lower upper
          (nodes n + meshStep + meshStep) := by
        rw [← hnode1, ← hnode2]
        exact nodeMem (n + 2) hn2
      have hpair := pairwiseLowerEulerResidual_forced_norm_adjacent_refined
        F DF G DG D E hx hxh hx2h stage (coefficient n) (forcing n)
        errF errG hmeshStep (hsmallF n hn) (hsmallG n hn)
        herrF herrG (hderivLoF n hn) (hderivHiF n hn)
        (hderivLoG n hn) (hderivHiG n hn)
      have hsampleF :
          F.lowerSample (nodes (n + 1)) (nodeMem (n + 1) hn1)
            (fun i => (D i).evalPrecision (nodes (n + 1)) meshStep (stage i)) =
          F.lowerSample (nodes n + meshStep) hxh
            (fun i => (D i).evalPrecision (nodes n + meshStep) meshStep (stage i)) := by
        congr 1
        funext i
        simp [hnode1]
      have hsampleG :
          G.lowerSample (nodes (n + 1)) (nodeMem (n + 1) hn1)
            (fun i => (E i).evalPrecision (nodes (n + 1)) meshStep (stage i)) =
          G.lowerSample (nodes n + meshStep) hxh
            (fun i => (E i).evalPrecision (nodes n + meshStep) meshStep (stage i)) := by
        congr 1
        funext i
        simp [hnode1]
      simpa [leftResidual, rightResidual, sampledEulerResidual, left, right,
        step, scaledForcing, uniformMeshLowerSample, hn, hInterior,
        hsampleF, hsampleG,
        residualBound] using hpair
    · have hlast : n + 1 = cells := by omega
      have hprev : cells - 1 = n := by omega
      have hnode1 : nodes (n + 1) = nodes n + meshStep := hnodes n hn
      have hx : inDomainInterval lower upper (nodes n) := nodeMem n (by omega)
      have hxh : inDomainInterval lower upper (nodes n + meshStep) := by
        rw [← hnode1]
        exact nodeMem (n + 1) (by omega)
      have hnodeFinal : nodes cells = nodes n + meshStep := by
        rw [← hlast, hnode1]
      have hpair := pairwiseLowerEulerResidual_forced_norm_refined
        F DF G DG D E hx hxh stage (coefficient n) (forcing n) errF errG
        hmeshStep (hsmallF n hn) (hsmallG n hn) herrF herrG
        (hderivLoF n hn) (hderivHiF n hn)
        (hderivLoG n hn) (hderivHiG n hn)
      have hsampleF :
          F.lowerSample (nodes cells) (nodeMem cells (Nat.le_refl _))
            (fun i => (D i).evalPrecision (nodes (cells - 1)) meshStep (stage i)) =
          F.lowerSample (nodes n + meshStep) hxh
            (fun i => (D i).evalPrecision (nodes n) meshStep (stage i)) := by
        rw [hprev]
        congr 1
      have hsampleG :
          G.lowerSample (nodes cells) (nodeMem cells (Nat.le_refl _))
            (fun i => (E i).evalPrecision (nodes (cells - 1)) meshStep (stage i)) =
          G.lowerSample (nodes n + meshStep) hxh
            (fun i => (E i).evalPrecision (nodes n) meshStep (stage i)) := by
        rw [hprev]
        congr 1
      have hpairResidual : vectorAbsSum (leftResidual n) +
          vectorAbsSum (rightResidual n) <=
          finiteSum (fun i => meshStep * (errF i +
            3 * (precisionAtStage (stage i)).val)) +
          finiteSum (fun i => meshStep * (errG i +
            3 * (precisionAtStage (stage i)).val)) := by
        rw [← hsampleF, ← hsampleG] at hpair
        simpa [leftResidual, rightResidual, sampledEulerResidual, left, right,
          step, scaledForcing, uniformMeshLowerSample, hn, hlast, hprev,
          hnodeFinal,
          hsampleF, hsampleG]
          using hpair
      calc
        vectorAbsSum (leftResidual n) + vectorAbsSum (rightResidual n) <=
            finiteSum (fun i => meshStep * (errF i +
              3 * (precisionAtStage (stage i)).val)) +
            finiteSum (fun i => meshStep * (errG i +
              3 * (precisionAtStage (stage i)).val)) := hpairResidual
        _ <= residualBound := by
          dsimp [residualBound]
          apply rat_add_le_add
          · apply finiteSum_le
            intro i
            have heps := Rat.le_of_lt (precisionAtStage (stage i)).property
            apply Rat.mul_le_mul_of_nonneg_left _ (Rat.le_of_lt hmeshStep)
            grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]
          · apply finiteSum_le
            intro i
            have heps := Rat.le_of_lt (precisionAtStage (stage i)).property
            apply Rat.mul_le_mul_of_nonneg_left _ (Rat.le_of_lt hmeshStep)
            grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]
  have hgrowth : 0 <= 1 + coefficientStep := by
    exact Rat.add_nonneg (by decide : (0 : Rat) <= 1) hcoefficientNonneg
  have hcompare :=
    ComputableAnalysis.LinearODE.DiscreteLinearSystem.difference_of_two_forced_euler_trajectories_le_envelope_up_to
      (1 + coefficientStep) initialBound cells (fun _ => residualBound)
      step scaledForcing left right leftResidual rightResidual hgrowth
      (by simpa [left, right] using hinitial) hcolumns hresidual hleftStep hrightStep
  simpa [left, right, coefficientStep, residualBound] using
    hcompare cells (Nat.le_refl _)

/-- The same scalar one-cell residual has a uniform schedule-only bound. The
endpoint box width is controlled by the quotient certificate, so the whole
Euler defect is at most `h p + h (h p + 2 p)` where `p` is the requested
derivative precision. -/
theorem HasDerivativeOnInterval.selfLowerEndpoint_eulerResidual_le
    {f : FunctionOnInterval} (D : HasDerivativeOnInterval f f)
    {x h : Rat} {n : Nat}
    (hx : inDomainInterval f.lower f.upper x)
    (hxh : inDomainInterval f.lower f.upper (x + h))
    (hpos : 0 < h)
    (hsmall : qabs h <= 1 / ((D.stepPrecision n : Nat) : Rat)) :
    qabs
      ((f.compute (x + h) hxh (D.evalPrecision x h n)).lo -
        ((f.compute x hx (D.evalPrecision x h n)).lo +
          h * (f.compute x hx (D.evalPrecision x h n)).lo)) <=
      h * (precisionAtStage n).val +
        h * (h * (precisionAtStage n).val +
          2 * (precisionAtStage n).val) := by
  have hwidth := HasDerivativeOnInterval.endpointValue_widths_le D
    hx hxh hx hpos hsmall
  have hnonneg : 0 <= h := Rat.le_of_lt hpos
  calc
    qabs
        ((f.compute (x + h) hxh (D.evalPrecision x h n)).lo -
          ((f.compute x hx (D.evalPrecision x h n)).lo +
            h * (f.compute x hx (D.evalPrecision x h n)).lo)) <=
        (f.compute x hx (D.evalPrecision x h n)).width +
          h * ((f.compute x hx (D.evalPrecision x h n)).width +
            2 * (precisionAtStage n).val) :=
      HasDerivativeOnInterval.selfLowerEndpoint_eulerResidual D
        hx hxh hpos hsmall
    _ <= h * (precisionAtStage n).val +
        h * (h * (precisionAtStage n).val +
          2 * (precisionAtStage n).val) := by
      apply rat_add_le_add
      · exact hwidth.1
      · apply Rat.mul_le_mul_of_nonneg_left _ hnonneg
        exact rat_add_le_add hwidth.1 Rat.le_refl

/-! A bundled single-mesh input for the preceding end-to-end comparison. -/

structure LinearODESolutionMeshData
    {dimension : Nat} {lower upper : Rat}
    (F DF G DG : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)) where
  cells : Nat
  nodes : Nat -> Rat
  nodeMem : forall n, n <= cells -> inDomainInterval lower upper (nodes n)
  meshStep : Rat
  stage : Fin dimension -> Nat
  coefficient : Nat -> RatMatrix dimension
  forcing : Nat -> RatVector dimension
  errF : RatVector dimension
  errG : RatVector dimension
  entryBound : Rat
  initialBound : Rat
  meshStep_pos : 0 < meshStep
  nodes_step : forall n, n < cells -> nodes (n + 1) = nodes n + meshStep
  entryBound_nonneg : 0 <= entryBound
  entry_abs_bound : forall n, n < cells -> forall i j,
    qabs (coefficient n i j) <= entryBound
  initial_error_bound : vectorAbsSum (vectorSub
    (uniformMeshLowerSample F DF D nodes cells nodeMem meshStep stage 0)
    (uniformMeshLowerSample G DG E nodes cells nodeMem meshStep stage 0)) <=
      initialBound
  step_small_F : forall n, n < cells -> forall i,
    qabs meshStep <= 1 / ((D i).stepPrecision (stage i) : Nat)
  step_small_G : forall n, n < cells -> forall i,
    qabs meshStep <= 1 / ((E i).stepPrecision (stage i) : Nat)
  errF_nonneg : forall i, 0 <= errF i
  errG_nonneg : forall i, 0 <= errG i
  derivative_lower_F : forall n, (hn : n < cells) -> forall i,
    matrixApply (coefficient n)
        (F.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (D j).evalPrecision (nodes n) meshStep (stage j))) i +
      forcing n i - errF i <=
    (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
      (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).lo
  derivative_upper_F : forall n, (hn : n < cells) -> forall i,
    (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
      (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).hi <=
      matrixApply (coefficient n)
        (F.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (D j).evalPrecision (nodes n) meshStep (stage j))) i +
        forcing n i + errF i
  derivative_lower_G : forall n, (hn : n < cells) -> forall i,
    matrixApply (coefficient n)
        (G.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (E j).evalPrecision (nodes n) meshStep (stage j))) i +
      forcing n i - errG i <=
    (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
      (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).lo
  derivative_upper_G : forall n, (hn : n < cells) -> forall i,
    (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
      (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).hi <=
      matrixApply (coefficient n)
        (G.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (E j).evalPrecision (nodes n) meshStep (stage j))) i +
        forcing n i + errG i

/-- Construct the derivative-box obligations for a linear-system mesh from
exact rational sample equations and explicit derivative-box width budgets.
The lower endpoint of each derivative box is the chosen rational sample;
the width estimate then supplies its upper endpoint.  This turns the
pointwise equations into the two-sided affine bounds required by the finite
trajectory comparison, for arbitrary finite dimension and forcing. -/
def LinearODESolutionMeshData.ofSampledSystemBoxes
    {dimension : Nat} {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval dimension lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (cells : Nat) (nodes : Nat -> Rat)
    (nodeMem : forall n, n <= cells -> inDomainInterval lower upper (nodes n))
    (meshStep : Rat) (stage : Fin dimension -> Nat)
    (coefficient : Nat -> RatMatrix dimension)
    (forcing : Nat -> RatVector dimension)
    (errF errG : RatVector dimension)
    (entryBound initialBound : Rat)
    (meshStep_pos : 0 < meshStep)
    (nodes_step : forall n, n < cells ->
      nodes (n + 1) = nodes n + meshStep)
    (entryBound_nonneg : 0 <= entryBound)
    (entry_abs_bound : forall n, n < cells -> forall i j,
      qabs (coefficient n i j) <= entryBound)
    (initial_error_bound : vectorAbsSum (vectorSub
      (uniformMeshLowerSample F DF D nodes cells nodeMem meshStep stage 0)
      (uniformMeshLowerSample G DG E nodes cells nodeMem meshStep stage 0)) <=
        initialBound)
    (step_small_F : forall n, n < cells -> forall i,
      qabs meshStep <= 1 / ((D i).stepPrecision (stage i) : Nat))
    (step_small_G : forall n, n < cells -> forall i,
      qabs meshStep <= 1 / ((E i).stepPrecision (stage i) : Nat))
    (errF_nonneg : forall i, 0 <= errF i)
    (errG_nonneg : forall i, 0 <= errG i)
    (sampled_equation_F : forall n (hn : n < cells) i,
      (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).lo =
      matrixApply (coefficient n)
        (F.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (D j).evalPrecision (nodes n) meshStep (stage j))) i +
        forcing n i)
    (derivative_width_F : forall n (hn : n < cells) i,
      (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).width <=
          errF i)
    (sampled_equation_G : forall n (hn : n < cells) i,
      (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).lo =
      matrixApply (coefficient n)
        (G.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (E j).evalPrecision (nodes n) meshStep (stage j))) i +
        forcing n i)
    (derivative_width_G : forall n (hn : n < cells) i,
      (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).width <=
          errG i) :
    LinearODESolutionMeshData F DF G DG D E where
  cells := cells
  nodes := nodes
  nodeMem := nodeMem
  meshStep := meshStep
  stage := stage
  coefficient := coefficient
  forcing := forcing
  errF := errF
  errG := errG
  entryBound := entryBound
  initialBound := initialBound
  meshStep_pos := meshStep_pos
  nodes_step := nodes_step
  entryBound_nonneg := entryBound_nonneg
  entry_abs_bound := entry_abs_bound
  initial_error_bound := initial_error_bound
  step_small_F := step_small_F
  step_small_G := step_small_G
  errF_nonneg := errF_nonneg
  errG_nonneg := errG_nonneg
  derivative_lower_F := by
    intro n hn i
    rw [sampled_equation_F n hn i]
    grind [Rat.sub_eq_add_neg]
  derivative_upper_F := by
    intro n hn i
    have heq := sampled_equation_F n hn i
    have hwidth := derivative_width_F n hn i
    have hbox : (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).hi =
      (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).lo +
      (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    rw [hbox, heq]
    exact (Rat.add_le_add_left
      (c := (matrixApply (coefficient n)
        (F.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (D j).evalPrecision (nodes n) meshStep (stage j))) i +
        forcing n i))).2 hwidth
  derivative_lower_G := by
    intro n hn i
    rw [sampled_equation_G n hn i]
    grind [Rat.sub_eq_add_neg]
  derivative_upper_G := by
    intro n hn i
    have heq := sampled_equation_G n hn i
    have hwidth := derivative_width_G n hn i
    have hbox : (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).hi =
      (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).lo +
      (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    rw [hbox, heq]
    exact (Rat.add_le_add_left
      (c := (matrixApply (coefficient n)
        (G.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (E j).evalPrecision (nodes n) meshStep (stage j))) i +
        forcing n i))).2 hwidth

/-- Build finite linear-system mesh data when derivative boxes only
approximately match the sampled right-hand side.  `lowerError` measures the
distance from the box's lower endpoint to the sampled affine equation, and
`widthError` bounds the full derivative box.  Their sum is the certified
two-sided residual used by the mesh comparison.  This is the general route
for derivative computations whose rational interval is not centered exactly
at the sampled ODE value. -/
def LinearODESolutionMeshData.ofApproximateSampledSystemBoxes
    {dimension : Nat} {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval dimension lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (cells : Nat) (nodes : Nat -> Rat)
    (nodeMem : forall n, n <= cells -> inDomainInterval lower upper (nodes n))
    (meshStep : Rat) (stage : Fin dimension -> Nat)
    (coefficient : Nat -> RatMatrix dimension)
    (forcing : Nat -> RatVector dimension)
    (lowerErrorF lowerErrorG widthErrorF widthErrorG : RatVector dimension)
    (entryBound initialBound : Rat)
    (meshStep_pos : 0 < meshStep)
    (nodes_step : forall n, n < cells ->
      nodes (n + 1) = nodes n + meshStep)
    (entryBound_nonneg : 0 <= entryBound)
    (entry_abs_bound : forall n, n < cells -> forall i j,
      qabs (coefficient n i j) <= entryBound)
    (initial_error_bound : vectorAbsSum (vectorSub
      (uniformMeshLowerSample F DF D nodes cells nodeMem meshStep stage 0)
      (uniformMeshLowerSample G DG E nodes cells nodeMem meshStep stage 0)) <=
        initialBound)
    (step_small_F : forall n, n < cells -> forall i,
      qabs meshStep <= 1 / ((D i).stepPrecision (stage i) : Nat))
    (step_small_G : forall n, n < cells -> forall i,
      qabs meshStep <= 1 / ((E i).stepPrecision (stage i) : Nat))
    (lowerErrorF_nonneg : forall i, 0 <= lowerErrorF i)
    (lowerErrorG_nonneg : forall i, 0 <= lowerErrorG i)
    (widthErrorF_nonneg : forall i, 0 <= widthErrorF i)
    (widthErrorG_nonneg : forall i, 0 <= widthErrorG i)
    (sampled_lower_F : forall n (hn : n < cells) i,
      qabs ((DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).lo -
        (matrixApply (coefficient n)
          (F.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (D j).evalPrecision (nodes n) meshStep (stage j))) i +
          forcing n i)) <= lowerErrorF i)
    (sampled_width_F : forall n (hn : n < cells) i,
      (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).width <=
          widthErrorF i)
    (sampled_lower_G : forall n (hn : n < cells) i,
      qabs ((DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).lo -
        (matrixApply (coefficient n)
          (G.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (E j).evalPrecision (nodes n) meshStep (stage j))) i +
          forcing n i)) <= lowerErrorG i)
    (sampled_width_G : forall n (hn : n < cells) i,
      (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).width <=
          widthErrorG i) :
    LinearODESolutionMeshData F DF G DG D E where
  cells := cells
  nodes := nodes
  nodeMem := nodeMem
  meshStep := meshStep
  stage := stage
  coefficient := coefficient
  forcing := forcing
  errF := fun i => lowerErrorF i + widthErrorF i
  errG := fun i => lowerErrorG i + widthErrorG i
  entryBound := entryBound
  initialBound := initialBound
  meshStep_pos := meshStep_pos
  nodes_step := nodes_step
  entryBound_nonneg := entryBound_nonneg
  entry_abs_bound := entry_abs_bound
  initial_error_bound := initial_error_bound
  step_small_F := step_small_F
  step_small_G := step_small_G
  errF_nonneg := fun i => Rat.add_nonneg (lowerErrorF_nonneg i)
    (widthErrorF_nonneg i)
  errG_nonneg := fun i => Rat.add_nonneg (lowerErrorG_nonneg i)
    (widthErrorG_nonneg i)
  derivative_lower_F := by
    intro n hn i
    have h := qabs_bounds_of_le (lowerErrorF_nonneg i)
      (sampled_lower_F n hn i)
    have hw := widthErrorF_nonneg i
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  derivative_upper_F := by
    intro n hn i
    have hbox : (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).hi =
      (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).lo +
      (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    rw [hbox]
    have hlo := qabs_bounds_of_le (lowerErrorF_nonneg i)
      (sampled_lower_F n hn i)
    have hfirst :
        (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).lo +
          (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).width <=
        (matrixApply (coefficient n)
          (F.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (D j).evalPrecision (nodes n) meshStep (stage j))) i +
          forcing n i + lowerErrorF i) +
          (DF.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (D j).evalPrecision (nodes n) meshStep (stage j)) i).width := by
      have h := hlo.2
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    have hsecond := (Rat.add_le_add_left
      (c := matrixApply (coefficient n)
        (F.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (D j).evalPrecision (nodes n) meshStep (stage j))) i +
        forcing n i + lowerErrorF i)).2 (sampled_width_F n hn i)
    calc
      _ <= (matrixApply (coefficient n)
          (F.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (D j).evalPrecision (nodes n) meshStep (stage j))) i +
          forcing n i + lowerErrorF i) + widthErrorF i := by
        exact Rat.le_trans hfirst hsecond
      _ = matrixApply (coefficient n)
          (F.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (D j).evalPrecision (nodes n) meshStep (stage j))) i +
          forcing n i + (lowerErrorF i + widthErrorF i) := by
        grind [Rat.add_assoc]
      _ = _ := by rfl
  derivative_lower_G := by
    intro n hn i
    have h := qabs_bounds_of_le (lowerErrorG_nonneg i)
      (sampled_lower_G n hn i)
    have hw := widthErrorG_nonneg i
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  derivative_upper_G := by
    intro n hn i
    have hbox : (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).hi =
      (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).lo +
      (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
        (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    rw [hbox]
    have hlo := qabs_bounds_of_le (lowerErrorG_nonneg i)
      (sampled_lower_G n hn i)
    have hfirst :
        (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).lo +
          (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).width <=
        (matrixApply (coefficient n)
          (G.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (E j).evalPrecision (nodes n) meshStep (stage j))) i +
          forcing n i + lowerErrorG i) +
          (DG.computeBoxes (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (E j).evalPrecision (nodes n) meshStep (stage j)) i).width := by
      have h := hlo.2
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    have hsecond := (Rat.add_le_add_left
      (c := matrixApply (coefficient n)
        (G.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
          (fun j => (E j).evalPrecision (nodes n) meshStep (stage j))) i +
        forcing n i + lowerErrorG i)).2 (sampled_width_G n hn i)
    calc
      _ <= (matrixApply (coefficient n)
          (G.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (E j).evalPrecision (nodes n) meshStep (stage j))) i +
          forcing n i + lowerErrorG i) + widthErrorG i := by
        exact Rat.le_trans hfirst hsecond
      _ = matrixApply (coefficient n)
          (G.lowerSample (nodes n) (nodeMem n (Nat.le_of_lt hn))
            (fun j => (E j).evalPrecision (nodes n) meshStep (stage j))) i +
          forcing n i + (lowerErrorG i + widthErrorG i) := by
        grind [Rat.add_assoc]
      _ = _ := by rfl

/-- Build the linear-system mesh evidence for two vector solutions of the
coordinatewise self-derivative equation (F_i'=F_i), (G_i'=G_i). The
identity matrix is the shared coefficient. The endpoint-width theorem for
each derivative certificate supplies a uniform per-coordinate residual of
`meshStep * precisionAtStage(stage i)`; all remaining mesh geometry and the
initial discrepancy are supplied explicitly. -/
def LinearODESolutionMeshData.ofSelfDerivative
    {dimension : Nat} {lower upper : Rat}
    (F G : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (F.component i))
    (E : forall i, HasDerivativeOnInterval (G.component i) (G.component i))
    (cells : Nat) (nodes : Nat -> Rat)
    (nodeMem : forall n, n <= cells -> inDomainInterval lower upper (nodes n))
    (meshStep : Rat) (stage : Fin dimension -> Nat)
    (initialBound : Rat)
    (meshStep_pos : 0 < meshStep)
    (nodes_step : forall n, n < cells ->
      nodes (n + 1) = nodes n + meshStep)
    (initial_error_bound : vectorAbsSum (vectorSub
      (uniformMeshLowerSample F F D nodes cells nodeMem meshStep stage 0)
      (uniformMeshLowerSample G G E nodes cells nodeMem meshStep stage 0)) <=
        initialBound)
    (step_small_F : forall n, n < cells -> forall i,
      qabs meshStep <= 1 / ((D i).stepPrecision (stage i) : Nat))
    (step_small_G : forall n, n < cells -> forall i,
      qabs meshStep <= 1 / ((E i).stepPrecision (stage i) : Nat)) :
    LinearODESolutionMeshData F F G G D E where
  cells := cells
  nodes := nodes
  nodeMem := nodeMem
  meshStep := meshStep
  stage := stage
  coefficient := fun _ => matrixIdentity dimension
  forcing := fun _ => vectorZero dimension
  errF := fun i => meshStep * (precisionAtStage (stage i)).val
  errG := fun i => meshStep * (precisionAtStage (stage i)).val
  entryBound := 1
  initialBound := initialBound
  meshStep_pos := meshStep_pos
  nodes_step := nodes_step
  entryBound_nonneg := by decide +kernel
  entry_abs_bound := by
    intro n hn i j
    unfold matrixIdentity
    split <;> decide +kernel
  initial_error_bound := initial_error_bound
  step_small_F := step_small_F
  step_small_G := step_small_G
  errF_nonneg := by
    intro i
    exact Rat.mul_nonneg (Rat.le_of_lt meshStep_pos)
      (Rat.le_of_lt (precisionAtStage (stage i)).property)
  errG_nonneg := by
    intro i
    exact Rat.mul_nonneg (Rat.le_of_lt meshStep_pos)
      (Rat.le_of_lt (precisionAtStage (stage i)).property)
  derivative_lower_F := by
    intro n hn i
    let x := nodes n
    let hx := nodeMem n (Nat.le_of_lt hn)
    have hxnext : inDomainInterval lower upper (x + meshStep) := by
      rw [← nodes_step n hn]
      exact nodeMem (n + 1) (Nat.succ_le_of_lt hn)
    let sampleStages := fun j => (D j).evalPrecision x meshStep (stage j)
    have hwidth := LinearODE.HasDerivativeOnInterval.endpointValue_widths_le (D i)
      (F.domainAt i x hx)
      (F.domainAt i (x + meshStep) hxnext)
      (F.domainAt i x hx) meshStep_pos
      (step_small_F n hn i)
    have hsample :
        F.lowerSample x hx sampleStages i =
          (F.computeBoxes x hx sampleStages i).lo := rfl
    simp only [matrixApply_identity, vectorZero]
    change F.lowerSample x hx sampleStages i + 0 -
        meshStep * (precisionAtStage (stage i)).val <=
      (F.computeBoxes x hx sampleStages i).lo
    rw [Rat.add_zero, hsample]
    have hnonneg := Rat.le_of_lt
      (Rat.mul_pos meshStep_pos (precisionAtStage (stage i)).property)
    grind [Rat.sub_eq_add_neg]
  derivative_upper_F := by
    intro n hn i
    let x := nodes n
    let hx := nodeMem n (Nat.le_of_lt hn)
    have hxnext : inDomainInterval lower upper (x + meshStep) := by
      rw [← nodes_step n hn]
      exact nodeMem (n + 1) (Nat.succ_le_of_lt hn)
    let sampleStages := fun j => (D j).evalPrecision x meshStep (stage j)
    have hwidth := LinearODE.HasDerivativeOnInterval.endpointValue_widths_le (D i)
      (F.domainAt i x hx)
      (F.domainAt i (x + meshStep) hxnext)
      (F.domainAt i x hx) meshStep_pos
      (step_small_F n hn i)
    have hsample :
        F.lowerSample x hx sampleStages i =
          (F.computeBoxes x hx sampleStages i).lo := rfl
    simp only [matrixApply_identity, vectorZero]
    change (F.computeBoxes x hx sampleStages i).hi <=
      F.lowerSample x hx sampleStages i + 0 +
        meshStep * (precisionAtStage (stage i)).val
    rw [Rat.add_zero, hsample]
    have h := hwidth.1
    change (F.computeBoxes x hx sampleStages i).width <= _ at h
    unfold QInterval.width at h
    grind [QInterval.width, Rat.sub_eq_add_neg]
  derivative_lower_G := by
    intro n hn i
    let x := nodes n
    let hx := nodeMem n (Nat.le_of_lt hn)
    have hxnext : inDomainInterval lower upper (x + meshStep) := by
      rw [← nodes_step n hn]
      exact nodeMem (n + 1) (Nat.succ_le_of_lt hn)
    let sampleStages := fun j => (E j).evalPrecision x meshStep (stage j)
    have hwidth := LinearODE.HasDerivativeOnInterval.endpointValue_widths_le (E i)
      (G.domainAt i x hx)
      (G.domainAt i (x + meshStep) hxnext)
      (G.domainAt i x hx) meshStep_pos
      (step_small_G n hn i)
    have hsample :
        G.lowerSample x hx sampleStages i =
          (G.computeBoxes x hx sampleStages i).lo := rfl
    simp only [matrixApply_identity, vectorZero]
    change G.lowerSample x hx sampleStages i + 0 -
        meshStep * (precisionAtStage (stage i)).val <=
      (G.computeBoxes x hx sampleStages i).lo
    rw [Rat.add_zero, hsample]
    have hnonneg := Rat.le_of_lt
      (Rat.mul_pos meshStep_pos (precisionAtStage (stage i)).property)
    grind [Rat.sub_eq_add_neg]
  derivative_upper_G := by
    intro n hn i
    let x := nodes n
    let hx := nodeMem n (Nat.le_of_lt hn)
    have hxnext : inDomainInterval lower upper (x + meshStep) := by
      rw [← nodes_step n hn]
      exact nodeMem (n + 1) (Nat.succ_le_of_lt hn)
    let sampleStages := fun j => (E j).evalPrecision x meshStep (stage j)
    have hwidth := LinearODE.HasDerivativeOnInterval.endpointValue_widths_le (E i)
      (G.domainAt i x hx)
      (G.domainAt i (x + meshStep) hxnext)
      (G.domainAt i x hx) meshStep_pos
      (step_small_G n hn i)
    have hsample :
        G.lowerSample x hx sampleStages i =
          (G.computeBoxes x hx sampleStages i).lo := rfl
    simp only [matrixApply_identity, vectorZero]
    change (G.computeBoxes x hx sampleStages i).hi <=
      G.lowerSample x hx sampleStages i + 0 +
        meshStep * (precisionAtStage (stage i)).val
    rw [Rat.add_zero, hsample]
    have h := hwidth.1
    change (G.computeBoxes x hx sampleStages i).width <= _ at h
    unfold QInterval.width at h
    grind [QInterval.width, Rat.sub_eq_add_neg]

/-- The coordinatewise self-derivative mesh constructor, factored through
the general approximate sampled-box adapter.  This is the scalar-matrix
specialization used for exponential uniqueness: the sampled equation error
is zero, while the derivative box width supplies the full local residual. -/
def LinearODESolutionMeshData.ofSelfDerivativeViaApproximateBoxes
    {dimension : Nat} {lower upper : Rat}
    (F G : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (F.component i))
    (E : forall i, HasDerivativeOnInterval (G.component i) (G.component i))
    (cells : Nat) (nodes : Nat -> Rat)
    (nodeMem : forall n, n <= cells -> inDomainInterval lower upper (nodes n))
    (meshStep : Rat) (stage : Fin dimension -> Nat)
    (initialBound : Rat)
    (meshStep_pos : 0 < meshStep)
    (nodes_step : forall n, n < cells ->
      nodes (n + 1) = nodes n + meshStep)
    (initial_error_bound : vectorAbsSum (vectorSub
      (uniformMeshLowerSample F F D nodes cells nodeMem meshStep stage 0)
      (uniformMeshLowerSample G G E nodes cells nodeMem meshStep stage 0)) <=
        initialBound)
    (step_small_F : forall n, n < cells -> forall i,
      qabs meshStep <= 1 / ((D i).stepPrecision (stage i) : Nat))
    (step_small_G : forall n, n < cells -> forall i,
      qabs meshStep <= 1 / ((E i).stepPrecision (stage i) : Nat)) :
    LinearODESolutionMeshData F F G G D E := by
  let zero : RatVector dimension := fun _ => 0
  let width : RatVector dimension := fun i =>
    meshStep * (precisionAtStage (stage i)).val
  refine LinearODESolutionMeshData.ofApproximateSampledSystemBoxes
    cells nodes nodeMem meshStep stage
    (fun _ => matrixIdentity dimension) (fun _ => vectorZero dimension)
    zero zero width width 1 initialBound meshStep_pos nodes_step ?_ ?_
    initial_error_bound step_small_F step_small_G ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Rat.le_refl
  · intro n hn i j
    unfold matrixIdentity
    split <;> decide +kernel
  · intro i
    change 0 <= 0
    exact Rat.le_refl
  · intro i
    change 0 <= 0
    exact Rat.le_refl
  · intro i
    dsimp [width]
    exact Rat.mul_nonneg (Rat.le_of_lt meshStep_pos)
      (Rat.le_of_lt (precisionAtStage (stage i)).property)
  · intro i
    dsimp [width]
    exact Rat.mul_nonneg (Rat.le_of_lt meshStep_pos)
      (Rat.le_of_lt (precisionAtStage (stage i)).property)
  · intro n hn i
    let x := nodes n
    let hx := nodeMem n (Nat.le_of_lt hn)
    let sampleStages := fun j => (D j).evalPrecision x meshStep (stage j)
    have hsample :
        (F.computeBoxes x hx sampleStages i).lo =
          F.lowerSample x hx sampleStages i := by rfl
    have hequation := congrArg (fun v : RatVector dimension => v i)
      (LinearODE.matrixApply_identity (F.lowerSample x hx sampleStages))
    change qabs ((F.computeBoxes x hx sampleStages i).lo -
      (matrixApply (matrixIdentity dimension)
        (F.lowerSample x hx sampleStages) i + 0)) <= 0
    rw [hsample, hequation, Rat.add_zero, Rat.sub_self]
    decide +kernel
  · intro n hn i
    let x := nodes n
    let hx := nodeMem n (Nat.le_of_lt hn)
    let hxnext : inDomainInterval lower upper (x + meshStep) := by
      rw [← nodes_step n hn]
      exact nodeMem (n + 1) (Nat.succ_le_of_lt hn)
    let sampleStages := fun j => (D j).evalPrecision x meshStep (stage j)
    have hwidth := LinearODE.HasDerivativeOnInterval.endpointValue_widths_le
      (D i) (F.domainAt i x hx) (F.domainAt i (x + meshStep) hxnext)
      (F.domainAt i x hx) meshStep_pos (step_small_F n hn i)
    change (F.computeBoxes x hx sampleStages i).width <= width i
    dsimp [width]
    exact hwidth.1
  · intro n hn i
    let x := nodes n
    let hx := nodeMem n (Nat.le_of_lt hn)
    let sampleStages := fun j => (E j).evalPrecision x meshStep (stage j)
    have hsample :
        (G.computeBoxes x hx sampleStages i).lo =
          G.lowerSample x hx sampleStages i := by rfl
    have hequation := congrArg (fun v : RatVector dimension => v i)
      (LinearODE.matrixApply_identity (G.lowerSample x hx sampleStages))
    change qabs ((G.computeBoxes x hx sampleStages i).lo -
      (matrixApply (matrixIdentity dimension)
        (G.lowerSample x hx sampleStages) i + 0)) <= 0
    rw [hsample, hequation, Rat.add_zero, Rat.sub_self]
    decide +kernel
  · intro n hn i
    let x := nodes n
    let hx := nodeMem n (Nat.le_of_lt hn)
    let hxnext : inDomainInterval lower upper (x + meshStep) := by
      rw [← nodes_step n hn]
      exact nodeMem (n + 1) (Nat.succ_le_of_lt hn)
    let sampleStages := fun j => (E j).evalPrecision x meshStep (stage j)
    have hwidth := LinearODE.HasDerivativeOnInterval.endpointValue_widths_le
      (E i) (G.domainAt i x hx) (G.domainAt i (x + meshStep) hxnext)
      (G.domainAt i x hx) meshStep_pos (step_small_G n hn i)
    change (G.computeBoxes x hx sampleStages i).width <= width i
    dsimp [width]
    exact hwidth.1

namespace LinearODESolutionMeshData

def leftEndpointSample
    {dimension : Nat} {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval dimension lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (data : LinearODESolutionMeshData F DF G DG D E) : RatVector dimension :=
  uniformMeshLowerSample F DF D data.nodes data.cells data.nodeMem
    data.meshStep data.stage data.cells

def rightEndpointSample
    {dimension : Nat} {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval dimension lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (data : LinearODESolutionMeshData F DF G DG D E) : RatVector dimension :=
  uniformMeshLowerSample G DG E data.nodes data.cells data.nodeMem
    data.meshStep data.stage data.cells

def errorBound
    {dimension : Nat} {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval dimension lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (data : LinearODESolutionMeshData F DF G DG D E) : Rat :=
  DiscreteLinearSystem.eulerErrorEnvelope
    (1 + data.meshStep * finiteSum (fun _ : Fin dimension => data.entryBound))
    data.initialBound
    (fun _ =>
      finiteSum (fun i => data.meshStep *
        (data.errF i + 5 * (precisionAtStage (data.stage i)).val)) +
      finiteSum (fun i => data.meshStep *
        (data.errG i + 5 * (precisionAtStage (data.stage i)).val)))
    data.cells

def localDefectBound
    {dimension : Nat} {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval dimension lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (data : LinearODESolutionMeshData F DF G DG D E) : Rat :=
  finiteSum (fun i => data.meshStep *
    (data.errF i + 5 * (precisionAtStage (data.stage i)).val)) +
  finiteSum (fun i => data.meshStep *
    (data.errG i + 5 * (precisionAtStage (data.stage i)).val))

/-- The global mesh error is bounded by an explicit Euler growth power times
the initial discrepancy plus the total local defect. This form is useful for
whole-interval refinements: once a coefficient estimate controls the finite
growth power, only the shrinking initial and derivative-box errors remain. -/
theorem errorBound_le_growthPower
    {dimension : Nat} {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval dimension lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (data : LinearODESolutionMeshData F DF G DG D E) :
    data.errorBound <=
      (1 + data.meshStep * finiteSum (fun _ : Fin dimension => data.entryBound)) ^
        data.cells *
        (data.initialBound + (data.cells : Rat) * data.localDefectBound) := by
  let growth := 1 + data.meshStep *
    finiteSum (fun _ : Fin dimension => data.entryBound)
  have hsum : 0 <= finiteSum (fun _ : Fin dimension => data.entryBound) :=
    finiteSum_nonneg (fun _ => data.entryBound_nonneg)
  have hgrowth : 1 <= growth := by
    dsimp [growth]
    have hterm : 0 <= data.meshStep *
        finiteSum (fun _ : Fin dimension => data.entryBound) :=
      Rat.mul_nonneg (Rat.le_of_lt data.meshStep_pos) hsum
    grind
  have hlocal : 0 <= data.localDefectBound := by
    dsimp [localDefectBound]
    apply Rat.add_nonneg
    · apply finiteSum_nonneg
      intro i
      apply Rat.mul_nonneg (Rat.le_of_lt data.meshStep_pos)
      exact Rat.add_nonneg (data.errF_nonneg i)
        (Rat.mul_nonneg (by decide)
          (Rat.le_of_lt (precisionAtStage (data.stage i)).property))
    · apply finiteSum_nonneg
      intro i
      apply Rat.mul_nonneg (Rat.le_of_lt data.meshStep_pos)
      exact Rat.add_nonneg (data.errG_nonneg i)
        (Rat.mul_nonneg (by decide)
          (Rat.le_of_lt (precisionAtStage (data.stage i)).property))
  have hbound :=
    DiscreteLinearSystem.eulerErrorEnvelope_le_growth_pow_mul_initial_add_cells_residual
      (initial := data.initialBound) (residual := data.localDefectBound)
      data.cells (fun _ => data.localDefectBound) hgrowth hlocal
      (by intro n hn; exact Rat.le_refl)
  simpa [errorBound, localDefectBound, growth] using hbound

/-- A scalar whole-interval estimate with an explicit derivative-box error
budget. If both derivative boxes and their represented precision are bounded
by `eps`, the two candidates contribute at most `12 * meshStep * eps` per
mesh cell. Over total length at most one, this gives an effective global
bound once the finite Euler growth factor is controlled. -/
theorem errorBound_le_three_initial_add_precision
    {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval 1 lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (data : LinearODESolutionMeshData F DF G DG D E)
    (eps : Rat) (heps : 0 <= eps)
    (hinit : 0 <= data.initialBound)
    (hlength : (data.cells : Rat) * data.meshStep <= 1)
    (herrF : forall i, data.errF i <= eps)
    (herrG : forall i, data.errG i <= eps)
    (hprecision : forall i,
      (precisionAtStage (data.stage i)).val <= eps)
    (hgrowth : (1 + data.meshStep *
      finiteSum (fun _ : Fin 1 => data.entryBound)) ^ data.cells <= 3) :
    data.errorBound <= 3 * (data.initialBound + 12 * eps) := by
  have hFinner : forall i : Fin 1,
      data.errF i + 5 * (precisionAtStage (data.stage i)).val <= 6 * eps := by
    intro i
    calc
      data.errF i + 5 * (precisionAtStage (data.stage i)).val <=
          eps + 5 * eps := by
            exact rat_add_le_add (herrF i)
              (Rat.mul_le_mul_of_nonneg_left (hprecision i) (by decide))
      _ = 6 * eps := by grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
  have hGinner : forall i : Fin 1,
      data.errG i + 5 * (precisionAtStage (data.stage i)).val <= 6 * eps := by
    intro i
    calc
      data.errG i + 5 * (precisionAtStage (data.stage i)).val <=
          eps + 5 * eps := by
            exact rat_add_le_add (herrG i)
              (Rat.mul_le_mul_of_nonneg_left (hprecision i) (by decide))
      _ = 6 * eps := by grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
  have hFsum : finiteSum (fun i : Fin 1 => data.meshStep *
      (data.errF i + 5 * (precisionAtStage (data.stage i)).val)) <=
      6 * (data.meshStep * eps) := by
    calc
      finiteSum (fun i : Fin 1 => data.meshStep *
          (data.errF i + 5 * (precisionAtStage (data.stage i)).val)) <=
          finiteSum (fun _ : Fin 1 => data.meshStep * (6 * eps)) :=
        finiteSum_le (by
          intro i
          exact Rat.mul_le_mul_of_nonneg_left (hFinner i)
            (Rat.le_of_lt data.meshStep_pos))
      _ = 6 * (data.meshStep * eps) := by
        rw [finiteSum_const]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hGsum : finiteSum (fun i : Fin 1 => data.meshStep *
      (data.errG i + 5 * (precisionAtStage (data.stage i)).val)) <=
      6 * (data.meshStep * eps) := by
    calc
      finiteSum (fun i : Fin 1 => data.meshStep *
          (data.errG i + 5 * (precisionAtStage (data.stage i)).val)) <=
          finiteSum (fun _ : Fin 1 => data.meshStep * (6 * eps)) :=
        finiteSum_le (by
          intro i
          exact Rat.mul_le_mul_of_nonneg_left (hGinner i)
            (Rat.le_of_lt data.meshStep_pos))
      _ = 6 * (data.meshStep * eps) := by
        rw [finiteSum_const]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hlocal : data.localDefectBound <= 12 *
      (data.meshStep * eps) := by
    dsimp [localDefectBound]
    exact Rat.le_trans (rat_add_le_add hFsum hGsum) (by
      grind [Rat.mul_assoc, Rat.mul_comm])
  have htotal : (data.cells : Rat) * data.localDefectBound <= 12 * eps := by
    have hcells : 0 <= (data.cells : Rat) := Rat.natCast_nonneg
    have hleft := Rat.mul_le_mul_of_nonneg_left hlocal hcells
    have hright := Rat.mul_le_mul_of_nonneg_right hlength heps
    calc
      (data.cells : Rat) * data.localDefectBound <=
          (data.cells : Rat) * (12 * (data.meshStep * eps)) := hleft
      _ = 12 * ((data.cells : Rat) * data.meshStep * eps) := by
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= 12 * eps := by
        have hright' : (data.cells : Rat) * data.meshStep * eps <= eps := by
          simpa only [Rat.one_mul] using hright
        exact Rat.mul_le_mul_of_nonneg_left hright' (by decide : (0 : Rat) <= 12)
  have hsum_nonneg : 0 <= data.initialBound +
      (data.cells : Rat) * data.localDefectBound := by
    have hcells : 0 <= (data.cells : Rat) := Rat.natCast_nonneg
    have hlocal_nonneg : 0 <= data.localDefectBound := by
      dsimp [localDefectBound]
      apply Rat.add_nonneg
      · apply finiteSum_nonneg
        intro i
        exact Rat.mul_nonneg (Rat.le_of_lt data.meshStep_pos)
          (Rat.add_nonneg (data.errF_nonneg i)
            (Rat.mul_nonneg (by decide)
              (Rat.le_of_lt (precisionAtStage (data.stage i)).property)))
      · apply finiteSum_nonneg
        intro i
        exact Rat.mul_nonneg (Rat.le_of_lt data.meshStep_pos)
          (Rat.add_nonneg (data.errG_nonneg i)
            (Rat.mul_nonneg (by decide)
              (Rat.le_of_lt (precisionAtStage (data.stage i)).property)))
    exact Rat.add_nonneg hinit (Rat.mul_nonneg hcells hlocal_nonneg)
  have hinner : data.initialBound +
      (data.cells : Rat) * data.localDefectBound <=
        data.initialBound + 12 * eps := by
    exact (Rat.add_le_add_left (c := data.initialBound)).2 htotal
  calc
    data.errorBound <=
        (1 + data.meshStep * finiteSum (fun _ : Fin 1 => data.entryBound)) ^
          data.cells * (data.initialBound +
            (data.cells : Rat) * data.localDefectBound) :=
      errorBound_le_growthPower data
    _ <= 3 * (data.initialBound + 12 * eps) := by
      have hbase_nonneg : 0 <= 1 + data.meshStep *
          finiteSum (fun _ : Fin 1 => data.entryBound) := by
        apply Rat.add_nonneg (by decide)
        exact Rat.mul_nonneg (Rat.le_of_lt data.meshStep_pos)
          (finiteSum_nonneg (fun _ => data.entryBound_nonneg))
      have hgrowth_nonneg : 0 <=
          (1 + data.meshStep * finiteSum (fun _ : Fin 1 => data.entryBound)) ^
            data.cells := Rat.pow_nonneg hbase_nonneg
      have hupper_nonneg : 0 <= data.initialBound + 12 * eps := by
        exact Rat.add_nonneg hinit (Rat.mul_nonneg (by decide) heps)
      calc
        _ <= (1 + data.meshStep * finiteSum
              (fun _ : Fin 1 => data.entryBound)) ^ data.cells *
              (data.initialBound + 12 * eps) :=
          Rat.mul_le_mul_of_nonneg_left hinner hgrowth_nonneg
        _ <= 3 * (data.initialBound + 12 * eps) :=
          Rat.mul_le_mul_of_nonneg_right hgrowth hupper_nonneg

/-- Derivative-box and coefficient evidence in the mesh record proves the
finite endpoint error bound. -/
theorem endpoint_error
    {dimension : Nat} {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval dimension lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (data : LinearODESolutionMeshData F DF G DG D E) :
    vectorAbsSum (vectorSub data.leftEndpointSample data.rightEndpointSample) <=
      data.errorBound := by
  exact linearODE_solution_mesh_compare data.cells F DF G DG D E
    data.nodes data.nodeMem data.meshStep data.stage data.coefficient
    data.forcing data.errF data.errG data.entryBound data.initialBound
    data.meshStep_pos data.nodes_step data.entryBound_nonneg data.entry_abs_bound
    data.initial_error_bound data.step_small_F data.step_small_G
    data.errF_nonneg data.errG_nonneg data.derivative_lower_F
    data.derivative_upper_F data.derivative_lower_G data.derivative_upper_G

/-- The general finite-dimensional endpoint estimate, with the coefficient
growth and local derivative-box defects still explicit. This is the reusable
comparison theorem for an arbitrary rational mesh; concrete ODE uniqueness
proofs supply schedules that make the right-hand side shrink. -/
theorem endpoint_error_le_growthPower
    {dimension : Nat} {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval dimension lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (data : LinearODESolutionMeshData F DF G DG D E) :
    vectorAbsSum (vectorSub data.leftEndpointSample data.rightEndpointSample) <=
      (1 + data.meshStep *
        finiteSum (fun _ : Fin dimension => data.entryBound)) ^ data.cells *
        (data.initialBound + (data.cells : Rat) * data.localDefectBound) := by
  exact Rat.le_trans (endpoint_error data) (errorBound_le_growthPower data)

/-- Scalar endpoint comparison with all error terms exposed. This is the
form used by a global refinement: the mesh construction supplies a vanishing
initial error and derivative precision, while a separate growth estimate
controls the coefficient factor. -/
theorem endpoint_error_le_three_initial_add_precision
    {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval 1 lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (data : LinearODESolutionMeshData F DF G DG D E)
    (eps : Rat) (heps : 0 <= eps)
    (hinit : 0 <= data.initialBound)
    (hlength : (data.cells : Rat) * data.meshStep <= 1)
    (herrF : forall i, data.errF i <= eps)
    (herrG : forall i, data.errG i <= eps)
    (hprecision : forall i,
      (precisionAtStage (data.stage i)).val <= eps)
    (hgrowth : (1 + data.meshStep *
      finiteSum (fun _ : Fin 1 => data.entryBound)) ^ data.cells <= 3) :
    vectorAbsSum (vectorSub data.leftEndpointSample data.rightEndpointSample) <=
      3 * (data.initialBound + 12 * eps) := by
  exact Rat.le_trans (endpoint_error data)
    (errorBound_le_three_initial_add_precision data eps heps hinit hlength
      herrF herrG hprecision hgrowth)

/-- A short-block comparison extracted from one mesh record. Its residual
budget is the actual per-cell defect used by the end-to-end theorem, so the
result is sharper than the unrestricted growth envelope. -/
theorem endpoint_error_short_block
    {dimension : Nat} {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval dimension lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (data : LinearODESolutionMeshData F DF G DG D E)
    (hshort : (data.cells : Rat) *
      (data.meshStep * finiteSum (fun _ : Fin dimension => data.entryBound)) <=
        (1 : Rat) / 2) :
    vectorAbsSum (vectorSub data.leftEndpointSample data.rightEndpointSample) <=
      2 * (data.initialBound + (data.cells : Rat) * data.localDefectBound) := by
  let coefficient := data.meshStep *
    finiteSum (fun _ : Fin dimension => data.entryBound)
  let residual := data.localDefectBound
  have hentrySum : 0 <= finiteSum (fun _ : Fin dimension => data.entryBound) :=
    finiteSum_nonneg (fun _ => data.entryBound_nonneg)
  have hcoefficient : 0 <= coefficient :=
    Rat.mul_nonneg (Rat.le_of_lt data.meshStep_pos) hentrySum
  have hinitial : 0 <= data.initialBound :=
    Rat.le_trans (vectorAbsSum_nonneg
      (vectorSub
        (uniformMeshLowerSample F DF D data.nodes data.cells data.nodeMem
          data.meshStep data.stage 0)
        (uniformMeshLowerSample G DG E data.nodes data.cells data.nodeMem
          data.meshStep data.stage 0))) data.initial_error_bound
  have hresidual : 0 <= residual := by
    dsimp [residual, localDefectBound]
    apply Rat.add_nonneg
    · apply finiteSum_nonneg
      intro i
      exact Rat.mul_nonneg (Rat.le_of_lt data.meshStep_pos)
        (Rat.add_nonneg (data.errF_nonneg i)
          (Rat.mul_nonneg (by decide)
            (Rat.le_of_lt (precisionAtStage (data.stage i)).property)))
    · apply finiteSum_nonneg
      intro i
      exact Rat.mul_nonneg (Rat.le_of_lt data.meshStep_pos)
        (Rat.add_nonneg (data.errG_nonneg i)
          (Rat.mul_nonneg (by decide)
            (Rat.le_of_lt (precisionAtStage (data.stage i)).property)))
  have hcompare : vectorAbsSum
      (vectorSub data.leftEndpointSample data.rightEndpointSample) <=
      DiscreteLinearSystem.eulerErrorEnvelope (1 + coefficient) data.initialBound
        (fun _ => residual) data.cells := by
    simpa [errorBound, localDefectBound, coefficient, residual] using
      data.endpoint_error
  exact ComputableAnalysis.LinearODE.DiscreteLinearSystem.vectorDifference_le_short_block_of_eulerEnvelope
    data.leftEndpointSample data.rightEndpointSample coefficient data.initialBound
    residual data.cells (fun _ => residual) hcoefficient hinitial hresidual
    (fun _ _ => hresidual) (fun _ _ => Rat.le_refl) hshort hcompare

end LinearODESolutionMeshData

namespace CofinalMeshLowerComparison

/-- Build the exact cofinal comparison certificate from a family of concrete
ODE mesh records. Each record's finite bound is proved from its derivative
boxes by `LinearODESolutionMeshData.endpoint_error`; the caller supplies only
the endpoint condition and the quantitative refinement schedule. -/
def ofLinearODERefinement
    {dimension : Nat} {lower upper : Rat}
    (F DF G DG : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i))
    (meshes : (x : Rat) -> inDomainInterval lower upper x -> Nat ->
      LinearODESolutionMeshData F DF G DG D E)
    (endpoint : forall x hx k,
      (meshes x hx k).nodes (meshes x hx k).cells = x)
    (refine : forall x (hx : inDomainInterval lower upper x)
      (i : Fin dimension) n m (eps : QPos),
      exists k,
        n <= (D i).evalPrecision
          ((meshes x hx k).nodes ((meshes x hx k).cells - 1))
          (meshes x hx k).meshStep ((meshes x hx k).stage i) /\
        m <= (E i).evalPrecision
          ((meshes x hx k).nodes ((meshes x hx k).cells - 1))
          (meshes x hx k).meshStep ((meshes x hx k).stage i) /\
        (meshes x hx k).errorBound <= eps.val) :
    CofinalMeshLowerComparison F G where
  stageF := fun x hx k i =>
    (D i).evalPrecision ((meshes x hx k).nodes ((meshes x hx k).cells - 1))
      (meshes x hx k).meshStep ((meshes x hx k).stage i)
  stageG := fun x hx k i =>
    (E i).evalPrecision ((meshes x hx k).nodes ((meshes x hx k).cells - 1))
      (meshes x hx k).meshStep ((meshes x hx k).stage i)
  error := fun x hx k => (meshes x hx k).errorBound
  finite_comparison := by
    intro x hx k
    let data := meshes x hx k
    have hleft : F.lowerSample x hx
        (fun i => (D i).evalPrecision (data.nodes (data.cells - 1))
          data.meshStep (data.stage i)) = data.leftEndpointSample := by
      calc
        F.lowerSample x hx
            (fun i => (D i).evalPrecision (data.nodes (data.cells - 1))
              data.meshStep (data.stage i)) =
          F.lowerSample (data.nodes data.cells)
            (data.nodeMem data.cells (Nat.le_refl _))
            (fun i => (D i).evalPrecision (data.nodes (data.cells - 1))
              data.meshStep (data.stage i)) :=
          FunctionVectorOnInterval.lowerSample_congr_input F x
            (data.nodes data.cells) hx
            (data.nodeMem data.cells (Nat.le_refl _))
            (fun i => (D i).evalPrecision (data.nodes (data.cells - 1))
              data.meshStep (data.stage i)) (endpoint x hx k).symm
        _ = data.leftEndpointSample := by
          dsimp [data, LinearODESolutionMeshData.leftEndpointSample]
          exact (uniformMeshLowerSample_at_final F DF D
            (meshes x hx k).nodes (meshes x hx k).cells
            (meshes x hx k).nodeMem (meshes x hx k).meshStep
            (meshes x hx k).stage).symm
    have hright : G.lowerSample x hx
        (fun i => (E i).evalPrecision (data.nodes (data.cells - 1))
          data.meshStep (data.stage i)) = data.rightEndpointSample := by
      calc
        G.lowerSample x hx
            (fun i => (E i).evalPrecision (data.nodes (data.cells - 1))
              data.meshStep (data.stage i)) =
          G.lowerSample (data.nodes data.cells)
            (data.nodeMem data.cells (Nat.le_refl _))
            (fun i => (E i).evalPrecision (data.nodes (data.cells - 1))
              data.meshStep (data.stage i)) :=
          FunctionVectorOnInterval.lowerSample_congr_input G x
            (data.nodes data.cells) hx
            (data.nodeMem data.cells (Nat.le_refl _))
            (fun i => (E i).evalPrecision (data.nodes (data.cells - 1))
              data.meshStep (data.stage i)) (endpoint x hx k).symm
        _ = data.rightEndpointSample := by
          dsimp [data, LinearODESolutionMeshData.rightEndpointSample]
          exact (uniformMeshLowerSample_at_final G DG E
            (meshes x hx k).nodes (meshes x hx k).cells
            (meshes x hx k).nodeMem (meshes x hx k).meshStep
            (meshes x hx k).stage).symm
    rw [hleft, hright]
    exact LinearODESolutionMeshData.endpoint_error (meshes x hx k)
  refine := refine

/-- Short-block constructor for the cofinal uniqueness certificate. Its
refinement obligation is expressed directly in the shrinking initial error
and local defect budget; each finite comparison is proved by the packaged
short-block mesh estimate. -/
def ofLinearODEShortBlockRefinement
    {dimension : Nat} {lower upper : Rat}
    (F DF G DG : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i))
    (meshes : (x : Rat) -> inDomainInterval lower upper x -> Nat ->
      LinearODESolutionMeshData F DF G DG D E)
    (endpoint : forall x hx k,
      (meshes x hx k).nodes (meshes x hx k).cells = x)
    (shortBlock : forall x hx k,
      (meshes x hx k).cells *
          ((meshes x hx k).meshStep *
            finiteSum (fun _ : Fin dimension => (meshes x hx k).entryBound)) <=
        (1 : Rat) / 2)
    (refine : forall x (hx : inDomainInterval lower upper x)
      (i : Fin dimension) n m (eps : QPos),
      exists k,
        n <= (D i).evalPrecision
          ((meshes x hx k).nodes ((meshes x hx k).cells - 1))
          (meshes x hx k).meshStep ((meshes x hx k).stage i) /\
        m <= (E i).evalPrecision
          ((meshes x hx k).nodes ((meshes x hx k).cells - 1))
          (meshes x hx k).meshStep ((meshes x hx k).stage i) /\
        2 * ((meshes x hx k).initialBound +
          (meshes x hx k).cells * (meshes x hx k).localDefectBound) <= eps.val) :
    CofinalMeshLowerComparison F G where
  stageF := fun x hx k i =>
    (D i).evalPrecision ((meshes x hx k).nodes ((meshes x hx k).cells - 1))
      (meshes x hx k).meshStep ((meshes x hx k).stage i)
  stageG := fun x hx k i =>
    (E i).evalPrecision ((meshes x hx k).nodes ((meshes x hx k).cells - 1))
      (meshes x hx k).meshStep ((meshes x hx k).stage i)
  error := fun x hx k => 2 * ((meshes x hx k).initialBound +
    (meshes x hx k).cells * (meshes x hx k).localDefectBound)
  finite_comparison := by
    intro x hx k
    let data := meshes x hx k
    have hleft : F.lowerSample x hx
        (fun i => (D i).evalPrecision (data.nodes (data.cells - 1))
          data.meshStep (data.stage i)) = data.leftEndpointSample := by
      calc
        F.lowerSample x hx
            (fun i => (D i).evalPrecision (data.nodes (data.cells - 1))
              data.meshStep (data.stage i)) =
          F.lowerSample (data.nodes data.cells)
            (data.nodeMem data.cells (Nat.le_refl _))
            (fun i => (D i).evalPrecision (data.nodes (data.cells - 1))
              data.meshStep (data.stage i)) :=
          FunctionVectorOnInterval.lowerSample_congr_input F x
            (data.nodes data.cells) hx
            (data.nodeMem data.cells (Nat.le_refl _))
            (fun i => (D i).evalPrecision (data.nodes (data.cells - 1))
              data.meshStep (data.stage i)) (endpoint x hx k).symm
        _ = data.leftEndpointSample := by
          dsimp [data, LinearODESolutionMeshData.leftEndpointSample]
          exact (uniformMeshLowerSample_at_final F DF D
            (meshes x hx k).nodes (meshes x hx k).cells
            (meshes x hx k).nodeMem (meshes x hx k).meshStep
            (meshes x hx k).stage).symm
    have hright : G.lowerSample x hx
        (fun i => (E i).evalPrecision (data.nodes (data.cells - 1))
          data.meshStep (data.stage i)) = data.rightEndpointSample := by
      calc
        G.lowerSample x hx
            (fun i => (E i).evalPrecision (data.nodes (data.cells - 1))
              data.meshStep (data.stage i)) =
          G.lowerSample (data.nodes data.cells)
            (data.nodeMem data.cells (Nat.le_refl _))
            (fun i => (E i).evalPrecision (data.nodes (data.cells - 1))
              data.meshStep (data.stage i)) :=
          FunctionVectorOnInterval.lowerSample_congr_input G x
            (data.nodes data.cells) hx
            (data.nodeMem data.cells (Nat.le_refl _))
            (fun i => (E i).evalPrecision (data.nodes (data.cells - 1))
              data.meshStep (data.stage i)) (endpoint x hx k).symm
        _ = data.rightEndpointSample := by
          dsimp [data, LinearODESolutionMeshData.rightEndpointSample]
          exact (uniformMeshLowerSample_at_final G DG E
            (meshes x hx k).nodes (meshes x hx k).cells
            (meshes x hx k).nodeMem (meshes x hx k).meshStep
            (meshes x hx k).stage).symm
    rw [hleft, hright]
    exact data.endpoint_error_short_block (shortBlock x hx k)
  refine := by
    intro x hx i n m eps
    obtain ⟨k, hn, hm, herror⟩ := refine x hx i n m eps
    exact ⟨k, hn, hm, herror⟩

end CofinalMeshLowerComparison

/-- A reusable finite-certificate interface for uniqueness of a linear
system. For each rational target and refinement index, it packages a finite
mesh whose derivative boxes satisfy the same affine system, whose total
coefficient action is short, and whose initial discrepancy plus local defect
shrinks effectively. No global partition or completeness principle is
assumed; callers may use different meshes for different targets. -/
structure LinearODEShortBlockRefinementFamily
    {dimension : Nat} {lower upper : Rat}
    (F DF G DG : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)) where
  meshes : (x : Rat) -> inDomainInterval lower upper x -> Nat ->
    LinearODESolutionMeshData F DF G DG D E
  endpoint : forall x hx k,
    (meshes x hx k).nodes (meshes x hx k).cells = x
  shortBlock : forall x hx k,
    (meshes x hx k).cells *
        ((meshes x hx k).meshStep *
          finiteSum (fun _ : Fin dimension => (meshes x hx k).entryBound)) <=
      (1 : Rat) / 2
  refine : forall x (hx : inDomainInterval lower upper x)
      (i : Fin dimension) n m (eps : QPos),
    exists k,
      n <= (D i).evalPrecision
        ((meshes x hx k).nodes ((meshes x hx k).cells - 1))
        (meshes x hx k).meshStep ((meshes x hx k).stage i) /\
      m <= (E i).evalPrecision
        ((meshes x hx k).nodes ((meshes x hx k).cells - 1))
        (meshes x hx k).meshStep ((meshes x hx k).stage i) /\
      2 * ((meshes x hx k).initialBound +
        (meshes x hx k).cells * (meshes x hx k).localDefectBound) <= eps.val

namespace LinearODEShortBlockRefinementFamily

/-- The packaged finite evidence proves represented equality of every
component on the complete interval. -/
theorem componentwise_equivalent
    {dimension : Nat} {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval dimension lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (family : LinearODEShortBlockRefinementFamily F DF G DG D E) :
    forall i, FunctionOnInterval.Equivalent (F.component i) (G.component i) := by
  have comparison := CofinalMeshLowerComparison.ofLinearODEShortBlockRefinement
    F DF G DG D E family.meshes family.endpoint family.shortBlock family.refine
  exact comparison.componentwise_equivalent

end LinearODEShortBlockRefinementFamily

/-- A whole-interval refinement family driven by the global finite Euler
error envelope. Unlike the short-block interface, it needs no contraction
condition on the total coefficient action; it applies when the finite growth
estimate itself is shown to shrink along the meshes. -/
structure LinearODEGlobalRefinementFamily
    {dimension : Nat} {lower upper : Rat}
    (F DF G DG : FunctionVectorOnInterval dimension lower upper)
    (D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i))
    (E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)) where
  meshes : (x : Rat) -> inDomainInterval lower upper x -> Nat ->
    LinearODESolutionMeshData F DF G DG D E
  endpoint : forall x hx k,
    (meshes x hx k).nodes (meshes x hx k).cells = x
  refine : forall x (hx : inDomainInterval lower upper x)
      (i : Fin dimension) n m (eps : QPos),
    exists k,
      n <= (D i).evalPrecision
        ((meshes x hx k).nodes ((meshes x hx k).cells - 1))
        (meshes x hx k).meshStep ((meshes x hx k).stage i) /\
      m <= (E i).evalPrecision
        ((meshes x hx k).nodes ((meshes x hx k).cells - 1))
        (meshes x hx k).meshStep ((meshes x hx k).stage i) /\
      (meshes x hx k).errorBound <= eps.val

namespace LinearODEGlobalRefinementFamily

/-- The global finite-error envelope and its effective refinement schedule
prove componentwise represented equality on the full rational interval. -/
theorem componentwise_equivalent
    {dimension : Nat} {lower upper : Rat}
    {F DF G DG : FunctionVectorOnInterval dimension lower upper}
    {D : forall i, HasDerivativeOnInterval (F.component i) (DF.component i)}
    {E : forall i, HasDerivativeOnInterval (G.component i) (DG.component i)}
    (family : LinearODEGlobalRefinementFamily F DF G DG D E) :
    forall i, FunctionOnInterval.Equivalent (F.component i) (G.component i) := by
  exact (CofinalMeshLowerComparison.ofLinearODERefinement
    F DF G DG D E family.meshes family.endpoint family.refine).componentwise_equivalent

end LinearODEGlobalRefinementFamily

/-- Scalar uniqueness is a direct instance of the one-dimensional linear
system theorem. The caller supplies the finite mesh family; endpoint
equalities align the two independently declared scalar domains with the
common vector interval. -/
theorem scalar_equivalent_of_linearODE_refinement
    {lower upper : Rat}
    (f df g dg : FunctionOnInterval)
    (hfLower : f.lower = lower) (hfUpper : f.upper = upper)
    (hdfLower : df.lower = lower) (hdfUpper : df.upper = upper)
    (hgLower : g.lower = lower) (hgUpper : g.upper = upper)
    (hdgLower : dg.lower = lower) (hdgUpper : dg.upper = upper)
    (D : HasDerivativeOnInterval f df)
    (E : HasDerivativeOnInterval g dg)
    (family : LinearODEShortBlockRefinementFamily
      (FunctionVectorOnInterval.ofScalarOnDomain f lower upper hfLower hfUpper)
      (FunctionVectorOnInterval.ofScalarOnDomain df lower upper hdfLower hdfUpper)
      (FunctionVectorOnInterval.ofScalarOnDomain g lower upper hgLower hgUpper)
      (FunctionVectorOnInterval.ofScalarOnDomain dg lower upper hdgLower hdgUpper)
      (FunctionVectorOnInterval.derivativeEvidenceOfScalarOnDomain
        hfLower hfUpper hdfLower hdfUpper D)
      (FunctionVectorOnInterval.derivativeEvidenceOfScalarOnDomain
        hgLower hgUpper hdgLower hdgUpper E)) :
    FunctionOnInterval.Equivalent f g := by
  have hcomponent := family.componentwise_equivalent (0 : Fin 1)
  change FunctionOnInterval.Equivalent f g at hcomponent
  exact hcomponent

/-- Scalar projection for a full-interval refinement family using the global
finite error envelope. This is the adapter for exponential comparisons whose
target interval is longer than a single short contraction block. -/
theorem scalar_equivalent_of_global_linearODE_refinement
    {lower upper : Rat}
    (f df g dg : FunctionOnInterval)
    (hfLower : f.lower = lower) (hfUpper : f.upper = upper)
    (hdfLower : df.lower = lower) (hdfUpper : df.upper = upper)
    (hgLower : g.lower = lower) (hgUpper : g.upper = upper)
    (hdgLower : dg.lower = lower) (hdgUpper : dg.upper = upper)
    (D : HasDerivativeOnInterval f df)
    (E : HasDerivativeOnInterval g dg)
    (family : LinearODEGlobalRefinementFamily
      (FunctionVectorOnInterval.ofScalarOnDomain f lower upper hfLower hfUpper)
      (FunctionVectorOnInterval.ofScalarOnDomain df lower upper hdfLower hdfUpper)
      (FunctionVectorOnInterval.ofScalarOnDomain g lower upper hgLower hgUpper)
      (FunctionVectorOnInterval.ofScalarOnDomain dg lower upper hdgLower hdgUpper)
      (FunctionVectorOnInterval.derivativeEvidenceOfScalarOnDomain
        hfLower hfUpper hdfLower hdfUpper D)
      (FunctionVectorOnInterval.derivativeEvidenceOfScalarOnDomain
        hgLower hgUpper hdgLower hdgUpper E)) :
    FunctionOnInterval.Equivalent f g := by
  have hcomponent := family.componentwise_equivalent (0 : Fin 1)
  change FunctionOnInterval.Equivalent f g at hcomponent
  exact hcomponent

end LinearODE

end ComputableAnalysis


