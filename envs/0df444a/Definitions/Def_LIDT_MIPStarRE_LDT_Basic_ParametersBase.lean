-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
-- name    : LIDT_MIPStarRE_LDT_Basic_ParametersBase
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:46:23.194416+00:00
-- url     : https://prove2.me/theorems/a34d532a-5d53-402e-848a-1aa2625db0ed
-- title:
--   LIDT definitions: LDT / Basic / ParametersBase
-- statement:
--   This bundle defines the central parameters and finite carriers for the low individual degree test. It packages the dimension, field-size, and degree data, successor and predecessor structure, coded point spaces, and the prime-power witness behind the field model.
--
--   Principal definitions:
--   - `Error`: the real-valued scalar type used for test errors and bounds.
--   - `Role`: the two verifier roles, Alice and Bob.
--   - `Parameters`: the positive `(m,q,d)` test parameters together with the prime-power witness for `q`.
--   - `SuccessorDecomposition`: a predecessor parameter bundle whose successor is the given parameter set.
--   - `Fq`: the repository's finite carrier of size `q`.
--   - `Point`: the affine point space represented by functions from the `m` coordinates to `Fq`.
--   - `PointTuple`: a finite tuple of field values indexed by a sample length.
--   - `PrimePowerFieldSpec`: the prime and exponent data exposing the honest finite field underlying the coded carrier.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/ParametersBase.lean#L22-L426

-- Generated from MIPStarRE/LDT/Basic/ParametersBase.lean by skeleton subtraction.
import Mathlib

namespace LIDT

/-!
# Basic parameters and scalar infrastructure for the low individual degree test

Core parameter data, finite-field models, and coordinate arithmetic.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

abbrev Error := ℝ

inductive Role where
  | A
  | B
  deriving DecidableEq, Repr, Inhabited

/-- The two roles form a finite type, enumerated by the two constructors `A` and `B`. -/
instance instFintypeRole : Fintype Role := ⟨{.A, .B}, by intro x; cases x <;> simp⟩

def Role.other : Role → Role
  | .A => .B
  | .B => .A

@[simp] theorem Role.other_other (r : Role) : r.other.other = r := by
  cases r <;> rfl

/-- Parameters for the `(m,q,d)` low individual degree test.

Besides the usual positivity assumptions, we bundle the paper-faithful witness
that `q = p^n` is a prime power. -/
structure Parameters where
  m : ℕ
  q : ℕ
  d : ℕ
  hm : 0 < m
  /-- Kept as a compatibility field so existing positivity proofs can continue
  to use `params.hq`; it is derivable from `hqPrimePower`. -/
  hq : 0 < q
  /-- Paper-faithful witness that `q` is a prime power. -/
  hqPrimePower : ∃ p n, Nat.Prime p ∧ 0 < n ∧ q = p ^ n

deriving instance DecidableEq for Parameters

namespace Parameters



/-- Prime numbers are prime powers of exponent `1`. -/
theorem prime_primePower {q : ℕ} (hqPrime : Nat.Prime q) :
    ∃ p n, Nat.Prime p ∧ 0 < n ∧ q = p ^ n := by
  exact ⟨q, 1, hqPrime, by decide, by simp⟩



/-- Build parameters when `q` itself is prime. -/
def ofPrime (m q d : ℕ) (hm : 0 < m) (hqPrime : Nat.Prime q) : Parameters :=
  { m := m
    q := q
    d := d
    hm := hm
    hq := hqPrime.pos
    hqPrimePower := prime_primePower hqPrime }

/-- Convenience constructor for the ubiquitous binary field. -/
def ofTwo (m d : ℕ) (hm : 0 < m) : Parameters :=
  ofPrime m 2 d hm Nat.prime_two





/-- Positivity of the field-size parameter after casting to the repository's
real-valued error scalar type. -/
theorem q_cast_pos (params : Parameters) : 0 < (params.q : Error) :=
  Nat.cast_pos.mpr params.hq

end Parameters

instance : Inhabited Parameters where
  default := Parameters.ofTwo 1 0 (by decide)

/-- The successor test obtained by appending one coordinate. -/
@[reducible] def Parameters.next (params : Parameters) : Parameters :=
  { m := params.m + 1
    q := params.q
    d := params.d
    hm := Nat.succ_pos _
    hq := params.hq
    hqPrimePower := params.hqPrimePower }

namespace Parameters

/-- The predecessor parameters obtained by removing the last coordinate from a
non-base ambient dimension.

This is the inverse construction to `Parameters.next` on the data fields.  The
proof fields are inherited from the original parameter bundle, so the inverse is
propositional rather than definitional. -/
def previous (params : Parameters) (hm : 1 < params.m) : Parameters :=
  { m := params.m - 1
    q := params.q
    d := params.d
    hm := Nat.sub_pos_of_lt hm
    hq := params.hq
    hqPrimePower := params.hqPrimePower }

/-- Removing the last coordinate and then applying `Parameters.next` recovers the
original non-base parameters. -/
theorem previous_next_eq (params : Parameters) (hm : 1 < params.m) :
    (previous params hm).next = params := by
  cases params with
  | mk m q d hm0 hq hqPrimePower =>
      have hsub : m - 1 + 1 = m := Nat.sub_add_cancel (le_of_lt hm)
      simp [previous, Parameters.next, hsub]

/-- A bundled predecessor for a parameter set known to be a successor dimension. -/
structure SuccessorDecomposition (params : Parameters) where
  /-- The predecessor parameter bundle. -/
  pred : Parameters
  /-- The predecessor's successor is the original parameter bundle. -/
  next_eq : pred.next = params

/-- Every parameter bundle of dimension strictly larger than one has a bundled
predecessor whose successor is propositionally equal to the original bundle. -/
def successorDecompositionOfOneLtM (params : Parameters) (hm : 1 < params.m) :
    SuccessorDecomposition params where
  pred := previous params hm
  next_eq := previous_next_eq params hm

/-- A positive dimension that is not the base dimension is strictly larger than
one. -/
theorem one_lt_m_of_ne_one (params : Parameters) (hm_ne_one : params.m ≠ 1) :
    1 < params.m :=
  lt_of_le_of_ne params.hm (Ne.symm hm_ne_one)

/-- Non-base parameters have a bundled predecessor decomposition. -/
def successorDecompositionOfNeOne (params : Parameters) (hm_ne_one : params.m ≠ 1) :
    SuccessorDecomposition params :=
  successorDecompositionOfOneLtM params (one_lt_m_of_ne_one params hm_ne_one)

end Parameters

instance {params : Parameters} : NeZero params.q :=
  ⟨Nat.ne_of_gt params.hq⟩

abbrev Fq (params : Parameters) := Fin params.q
abbrev Point (params : Parameters) := Fin params.m → Fq params
abbrev PointTuple (params : Parameters) (k : ℕ) := Fin k → Fq params

instance {params : Parameters} : Inhabited (Fin params.m) :=
  ⟨⟨0, params.hm⟩⟩

instance {params : Parameters} : Inhabited (Fq params) :=
  ⟨⟨0, params.hq⟩⟩

/-- Prime-power metadata extracted from `params.hqPrimePower`, exposing the
honest finite-field carrier `GaloisField p n` underlying the paper's notation
`F_q`. -/
structure PrimePowerFieldSpec (params : Parameters) where
  p : ℕ
  n : ℕ
  pPrime : Nat.Prime p
  nPos : 0 < n
  cardEq : params.q = p ^ n

/-- Recover the prime-power specification bundled inside `Parameters`. -/
noncomputable def Parameters.primePowerFieldSpec
    (params : Parameters) : PrimePowerFieldSpec params :=
  have : Nonempty (PrimePowerFieldSpec params) := by
    obtain ⟨p, n, hp, hn, hq⟩ := params.hqPrimePower
    exact ⟨{
      p := p
      n := n
      pPrime := hp
      nPos := hn
      cardEq := hq
    }⟩
  this.some

/-- An honest finite field of order `q`, obtained from the prime-power
witness bundled in `Parameters`. -/
noncomputable abbrev HonestFq (params : Parameters) (spec : PrimePowerFieldSpec params) :=
  letI : Fact spec.p.Prime := ⟨spec.pPrime⟩
  GaloisField spec.p spec.n

/-- A bundled field model for the paper's `F_q`, together with a coding equivalence
to the repository's finite carrier `Fin q`. -/
class FieldModel (q : ℕ) where
  K : Type*
  instField : Field K
  instFintype : Fintype K
  instDecidableEq : DecidableEq K
  equiv : K ≃ Fin q

attribute [instance_reducible, instance] FieldModel.instField FieldModel.instFintype
  FieldModel.instDecidableEq

namespace FieldModel

/-- The carrier bundled in a `FieldModel q` has exactly `q` elements, matching the
paper's finite-field convention `|F_q| = q` (`preliminaries.tex`, lines 17--19). -/
@[simp] theorem card (q : ℕ) [FieldModel q] :
    Fintype.card (FieldModel.K q) = q := by
  simpa using Fintype.card_congr (FieldModel.equiv (q := q))





end FieldModel

/-- Build the honest field model from prime-power data. -/
@[reducible] noncomputable def PrimePowerFieldSpec.toFieldModel (params : Parameters)
    (spec : PrimePowerFieldSpec params) : FieldModel params.q := by
  classical
  letI : Fact spec.p.Prime := ⟨spec.pPrime⟩
  let K := HonestFq params spec
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = params.q := by
    rw [← Nat.card_eq_fintype_card, spec.cardEq]
    simpa [K, HonestFq] using (GaloisField.card (p := spec.p) (n := spec.n) spec.nPos.ne')
  exact
    { K := K
      instField := inferInstance
      instFintype := inferInstance
      instDecidableEq := inferInstance
      equiv := Fintype.equivFinOfCardEq hcard }

/-- The canonical field model associated to the paper-faithful prime-power data
stored in `params`. Lean prefers larger numeric priorities, so this fallback
uses `100` while the `params.next` transport below uses `200`; that lets
instance search reuse an already chosen model when one is available. This
instance is noncomputable because the coding equivalence to `Fin q` is obtained
from finite cardinality data, so declarations that discover it through
typeclass search may also need to be marked `noncomputable` when they reduce
the model. -/
noncomputable instance (priority := 100) (params : Parameters) : FieldModel params.q :=
  PrimePowerFieldSpec.toFieldModel params (Parameters.primePowerFieldSpec params)

/-- Reuse an already chosen field model for successor parameters. Since Lean
prefers larger numeric priorities, this transport uses `200` so it is tried
before the canonical fallback above. -/
@[instance_reducible] instance (priority := 200) {params : Parameters}
    [inst : FieldModel params.q] :
    FieldModel params.next.q := inst

abbrev Scalar (params : Parameters) [FieldModel params.q] := FieldModel.K params.q
abbrev PolynomialModel (params : Parameters) [FieldModel params.q] :=
  MvPolynomial (Fin params.m) (Scalar params)
abbrev LinePolynomialModel (params : Parameters) [FieldModel params.q] :=
  _root_.Polynomial (Scalar params)

/-- The chosen scalar model for the paper's `F_q` has exactly `q` elements
(`preliminaries.tex`, lines 17--19 and 89--93). -/
@[simp] theorem scalar_card (params : Parameters) [FieldModel params.q] :
    Fintype.card (Scalar params) = params.q := by
  simp [Scalar]

/-- Interpret a coded coordinate in `Fin q` as a scalar in the chosen field model. -/
def decodeScalar {params : Parameters} [FieldModel params.q] (x : Fq params) : Scalar params :=
  (FieldModel.equiv (q := params.q)).symm x

/-- Re-encode a field-model scalar as its canonical representative in `Fin q`. -/
def encodeScalar {params : Parameters} [FieldModel params.q] (x : Scalar params) : Fq params :=
  FieldModel.equiv (q := params.q) x

@[simp] theorem encode_decodeScalar {params : Parameters} [FieldModel params.q] (x : Fq params) :
    encodeScalar (decodeScalar x) = x := by
  simp [encodeScalar, decodeScalar]

@[simp] theorem decode_encodeScalar {params : Parameters} [FieldModel params.q]
    (x : Scalar params) :
    decodeScalar (encodeScalar x) = x := by
  simp [encodeScalar, decodeScalar]

/-- The zero coordinate. -/
def zeroCoord {params : Parameters} [FieldModel params.q] : Fq params :=
  encodeScalar 0

/-- Coordinate addition transported through the `Fin q` coding. -/
def addCoord {params : Parameters} [FieldModel params.q] (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x + decodeScalar y)

/-- Coordinate subtraction transported through the `Fin q` coding. -/
def subCoord {params : Parameters} [FieldModel params.q] (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x - decodeScalar y)

@[simp] theorem addCoord_subCoord_right {params : Parameters} [FieldModel params.q]
    (x y : Fq params) :
    addCoord y (subCoord x y) = x := by
  unfold addCoord subCoord
  rw [decode_encodeScalar]
  simp [sub_eq_add_neg]

@[simp] theorem addCoord_subCoord_left {params : Parameters} [FieldModel params.q]
    (x y : Fq params) :
    addCoord (subCoord x y) y = x := by
  unfold addCoord subCoord
  rw [decode_encodeScalar]
  simp [sub_eq_add_neg]

@[simp] theorem subCoord_addCoord_right {params : Parameters} [FieldModel params.q]
    (x y : Fq params) :
    subCoord (addCoord x y) y = x := by
  unfold subCoord addCoord
  rw [decode_encodeScalar]
  simp [sub_eq_add_neg]

/-- Coordinate multiplication transported through the `Fin q` coding. -/
def mulCoord {params : Parameters} [FieldModel params.q] (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x * decodeScalar y)

/-- Coordinate inversion transported through the `Fin q` coding. -/
def invCoord {params : Parameters} [FieldModel params.q] (x : Fq params) : Fq params :=
  encodeScalar ((decodeScalar x)⁻¹)

/-- Pointwise addition in the coded ambient space. -/
def addPoint {params : Parameters} [FieldModel params.q] (u v : Point params) : Point params :=
  fun i => addCoord (u i) (v i)

/-- Scalar multiplication in the coded ambient space. -/
def smulPoint {params : Parameters} [FieldModel params.q] (t : Fq params) (u : Point params) :
    Point params :=
  fun i => mulCoord t (u i)

/-- The zero point in `F_q^m`. -/
def zeroPoint {params : Parameters} [FieldModel params.q] : Point params :=
  fun _ => zeroCoord

/-- The inclusion of the first `m` coordinates into `m + 1` coordinates. -/
def embedCoord (params : Parameters) : Fin params.m → Fin params.next.m :=
  fun i => ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self params.m)⟩

/-- The old-coordinate inclusion into the appended coordinate space is injective. -/
theorem embedCoord_injective (params : Parameters) :
    Function.Injective (embedCoord params) := by
  intro i j hij
  apply Fin.ext
  simpa [embedCoord] using congrArg Fin.val hij

/-- The last coordinate of `F_q^(m+1)`. -/
def lastCoord (params : Parameters) : Fin params.next.m :=
  ⟨params.m, Nat.lt_succ_self params.m⟩

/-- No old coordinate is the appended last coordinate. -/
theorem embedCoord_ne_lastCoord (params : Parameters) (i : Fin params.m) :
    embedCoord params i ≠ lastCoord params := by
  intro h
  have hval := congrArg Fin.val h
  simp [embedCoord, lastCoord] at hval
  omega

/-- Append a final coordinate to a point in `F_q^m`. -/
def appendPoint (params : Parameters) (u : Point params) (x : Fq params) : Point params.next :=
  fun i => if h : i.1 < params.m then u ⟨i.1, h⟩ else x

/-- Truncate the last coordinate of a point in `F_q^{m+1}`. -/
def truncatePoint (params : Parameters) (u : Point params.next) : Point params :=
  fun i => u ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self params.m)⟩

/-- Extract the final coordinate of a point in `F_q^{m+1}`. -/
def pointHeight (params : Parameters) (u : Point params.next) : Fq params :=
  u (lastCoord params)

@[simp] theorem truncatePoint_appendPoint (params : Parameters)
    (u : Point params) (x : Fq params) :
    truncatePoint params (appendPoint params u x) = u := by
  funext i
  simp [truncatePoint, appendPoint, i.2]

@[simp] theorem pointHeight_appendPoint (params : Parameters)
    (u : Point params) (x : Fq params) :
    pointHeight params (appendPoint params u x) = x := by
  simp [pointHeight, lastCoord, appendPoint]

/-- Decode a coded point as a tuple of scalars in the chosen field model. -/
def decodePoint {params : Parameters} [FieldModel params.q] (u : Point params) :
    Fin params.m → Scalar params :=
  fun i => decodeScalar (u i)

/-- Evaluate a multivariate polynomial over the chosen field model on a coded point. -/
noncomputable def evalPolynomialModel (params : Parameters) [FieldModel params.q]
    (p : PolynomialModel params) (u : Point params) : Fq params :=
  encodeScalar (MvPolynomial.eval (decodePoint u) p)

/-- Evaluate a univariate polynomial over the chosen field model on a coded point. -/
noncomputable def evalLinePolynomialModel (params : Parameters) [FieldModel params.q]
    (p : LinePolynomialModel params) (t : Fq params) : Fq params :=
  encodeScalar (_root_.Polynomial.eval (decodeScalar t) p)

end MIPStarRE.LDT

end

end LIDT


