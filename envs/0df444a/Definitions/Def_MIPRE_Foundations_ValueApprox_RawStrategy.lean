-- Prove2me | Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
-- name    : MIPRE_Foundations_ValueApprox_RawStrategy
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:13:10.845184+00:00
-- url     : https://prove2.me/theorems/6ec5d372-cc38-4928-a516-7cea0e5a6b3b
-- title:
--   Raw candidate strategies over the Gaussian integers, and the exact certificate check
-- statement:
--   Raw candidates for the enumeration behind `lem:value-lower-approx`: Gaussian-integer numerators (`GInt`) over a common denominator $k$, checked against a game description `g : GameData`.
--
--   **List matrices.** `GMat` is `List (List GInt)`, a matrix as a list of rows; `entry M i j`, `vget v i` read entries, $0$ when missing; `gsum n f`, `psum n f` are $\sum_{l < n} f(l)$ in `GInt` and `PInt`.
--
--   **Raw candidates.** `RawStrategy` has fields `k dA dB : ℕ`, `QA QB : List (List GMat)` (operator numerators, by question then answer) and `v : List GInt` (state numerators, row-major $(i,j) \mapsto i\,d_B + j$); `RawStrategy.equivTuple` is its tuple form, giving `instPrimcodable`; `matA r x a`, `matB r y b` read the numerator matrices; `RawStrategy.interp nX nA r` is the `ExactStrategy` on `Fin (nX + 1)`, `Fin (nA + 1)` (numerators divided by $k$).
--
--   **The check.** `IsHermRaw M d`: $M_{ij} = \overline{M_{ji}}$ for $i, j < d$ (as `GInt.Eq'`); `IsIdemRaw M d k`: $\sum_{l<d} M_{il}M_{lj} = k\,M_{ij}$; `IsSumRaw Ms nA d k`: $\sum_{a \le n_A} M_a = k \cdot 1$; `IsPVMRaw Ms nA d k`: all three for the family. `quadRaw A B dA dB v` $= \langle v, (A \otimes B)v\rangle$ (`GInt`) and `normRaw v dA dB` $= \mathrm{Re}\langle v, v\rangle$ (`PInt`); `wt g x y`, `W g` are the question weight and total weight of the description (a point mass at $(0,0)$ and $1$ when the total vanishes), `Draw g x y a b` its decision predicate, and `numer g r` the `wt`-weighted sum over $x, y$ and accepted $a, b$ of the real parts of `quadRaw`. `ValueTest g p q r` is $p/q < \mathrm{value}$ without denominators,
--   $$\bigl(q = 0 \wedge 0 < \mathrm{numer}\bigr)\ \vee\ \bigl(q \ne 0 \wedge p\,W\,k^{2}\,\langle v,v\rangle < q\cdot \mathrm{numer}\bigr),$$
--   and `Check g p q r` is: $0 < k$, `IsPVMRaw` for every question of each player, a nonzero entry of $v$ below index $d_A d_B$, and `ValueTest`; `Decidable` instances: `instDecidableIsHermRaw`, `instDecidableIsIdemRaw`, `instDecidableIsSumRaw`, `instDecidableIsPVMRaw`, `instDecidableValueTest`, `instDecidableCheck`.
--
--   The embedded lemmas are `toC_gsum`, `toInt_psum` (the list sums denote finite sums) and the `Primrec` proofs of `equivTuple` and of the six projections.
--
--   **Formalization Note**. For $q = 0$ the real $p/q$ is $0$ in Lean, hence the separate clause. Missing list entries read as $0$, so every predicate is total; `interp` is `noncomputable`. Per the module docstring, `RawSemantics` proves `Check` correct and `RawPrimrec` proves it primitive recursive.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ValueApprox/RawStrategy.lean; blueprint lem:value-lower-approx

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ValueApprox/RawStrategy.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription

/-!
# Raw candidates and the certificate check

The enumeration behind `lem:value-lower-approx` ranges over *raw candidates*
(`MIPRE.ValueApprox.RawStrategy`): a common denominator `k`, two dimensions, the Gaussian-integer
numerators of the measurement operators as lists of list matrices, and the numerators of the
state. A raw candidate denotes an exact strategy (`RawStrategy.interp`), with entries in
`(1/k) ℤ[i]`; the predicate `Check g p q r` says, in exact integer arithmetic, that the candidate
is a valid strategy for the game described by `g` and that its value exceeds `p / q`:

* `IsPVMRaw`: each family of operators is Hermitian, idempotent (`M² = k M`) and sums to `k·1`;
* the state is nonzero;
* `ValueTest`: `p · W · k² · ⟨v, v⟩ < q · numer`, where `numer` is `∑ wt(x,y) ∑ D re ⟨v, (A ⊗ B) v⟩`
  and `W` the total weight (the point mass on `(0,0)` when the weights vanish, as in
  `GameData.toGame`); for `q = 0`, where `p / q = 0`, the test is `0 < numer`.

All of it is primitive recursive (`MIPRE.Foundations.ValueApprox.RawPrimrec`), and
`MIPRE.Foundations.ValueApprox.RawSemantics` proves that `Check g p q r` holds iff `interp r` is
valid with value above `p / q`.
-/

namespace MIPRE.ValueApprox

open HaltingGameValue (GameData)

/-! ## Matrices and vectors as lists -/

/-- A matrix as a list of rows; missing entries read as `0`. -/
abbrev GMat := List (List GInt)

/-- The `(i, j)` entry of a list matrix, `0` when missing. -/
def entry (M : GMat) (i j : ℕ) : GInt := (M.getD i []).getD j GInt.zero

/-- The `i`-th entry of a list vector, `0` when missing. -/
def vget (v : List GInt) (i : ℕ) : GInt := v.getD i GInt.zero

/-- `∑_{l < n} f l` in `GInt`. -/
def gsum (n : ℕ) (f : ℕ → GInt) : GInt := GInt.sum ((List.range n).map f)

/-- `∑_{l < n} f l` in `PInt`. -/
def psum (n : ℕ) (f : ℕ → PInt) : PInt := PInt.sum ((List.range n).map f)

theorem toC_gsum (n : ℕ) (f : ℕ → GInt) :
    (gsum n f).toC = ∑ i ∈ Finset.range n, (f i).toC := by
  induction n with
  | zero => simp [gsum]
  | succ n ih =>
    rw [gsum, List.range_succ, List.map_append, GInt.toC_sum, List.map_append, List.sum_append,
      Finset.sum_range_succ, ← ih, gsum, GInt.toC_sum]
    simp

theorem toInt_psum (n : ℕ) (f : ℕ → PInt) :
    (psum n f).toInt = ∑ i ∈ Finset.range n, (f i).toInt := by
  induction n with
  | zero => simp [psum]
  | succ n ih =>
    rw [psum, List.range_succ, List.map_append, PInt.toInt_sum, List.map_append, List.sum_append,
      Finset.sum_range_succ, ← ih, psum, PInt.toInt_sum]
    simp

/-! ## Raw candidates -/

/-- The raw data of a candidate: a common denominator `k`, the two dimensions, the numerators of
the first and second players' operators (indexed by question, then answer), and the numerators of
the state, in row-major order `(i, j) ↦ i * dB + j`. -/
structure RawStrategy where
  k : ℕ
  dA : ℕ
  dB : ℕ
  QA : List (List GMat)
  QB : List (List GMat)
  v : List GInt

namespace RawStrategy

/-- Raw candidates are tuples. -/
def equivTuple : RawStrategy ≃ ℕ × ℕ × ℕ × List (List GMat) × List (List GMat) × List GInt where
  toFun r := (r.k, r.dA, r.dB, r.QA, r.QB, r.v)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable RawStrategy := Primcodable.ofEquiv _ equivTuple

theorem primrec_equivTuple : Primrec equivTuple := Primrec.of_equiv
theorem primrec_k : Primrec k := Primrec.fst.comp primrec_equivTuple
theorem primrec_dA : Primrec dA := (Primrec.fst.comp Primrec.snd).comp primrec_equivTuple
theorem primrec_dB : Primrec dB :=
  (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp primrec_equivTuple
theorem primrec_QA : Primrec QA :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).comp primrec_equivTuple
theorem primrec_QB : Primrec QB :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).comp
    primrec_equivTuple
theorem primrec_v : Primrec v :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).comp
    primrec_equivTuple

/-- The numerator matrix of the first player's operator for question `x` and answer `a`. -/
def matA (r : RawStrategy) (x a : ℕ) : GMat := (r.QA.getD x []).getD a []

/-- The numerator matrix of the second player's operator for question `y` and answer `b`. -/
def matB (r : RawStrategy) (y b : ℕ) : GMat := (r.QB.getD y []).getD b []

/-- The exact strategy denoted by raw data, for question alphabet `Fin (nX + 1)` and answer
alphabet `Fin (nA + 1)`: every numerator divided by `k`. -/
noncomputable def interp (nX nA : ℕ) (r : RawStrategy) :
    ExactStrategy (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) where
  dA := r.dA
  dB := r.dB
  PA x a := Matrix.of fun i j => (entry (r.matA x a) i j).toC / r.k
  PB y b := Matrix.of fun i j => (entry (r.matB y b) i j).toC / r.k
  u p := (vget r.v (p.1 * r.dB + p.2)).toC / r.k

end RawStrategy

/-! ## The certificate check -/

/-- The `d × d` matrix `M` is Hermitian. -/
def IsHermRaw (M : GMat) (d : ℕ) : Prop :=
  ∀ i < d, ∀ j < d, GInt.Eq' (entry M i j) (GInt.conj (entry M j i))

/-- `M² = k M`, i.e. `M / k` is idempotent. -/
def IsIdemRaw (M : GMat) (d k : ℕ) : Prop :=
  ∀ i < d, ∀ j < d, GInt.Eq' (gsum d fun l => GInt.mul (entry M i l) (entry M l j))
    (GInt.mul (GInt.ofNat k) (entry M i j))

/-- `∑_{a ≤ nA} Mₐ = k · 1`. -/
def IsSumRaw (Ms : List GMat) (nA d k : ℕ) : Prop :=
  ∀ i < d, ∀ j < d, GInt.Eq' (gsum (nA + 1) fun a => entry (Ms.getD a []) i j)
    (if i = j then GInt.ofNat k else GInt.zero)

/-- `(Mₐ / k)_{a ≤ nA}` is a projective measurement on `ℂ^d`. -/
def IsPVMRaw (Ms : List GMat) (nA d k : ℕ) : Prop :=
  (∀ a < nA + 1, IsHermRaw (Ms.getD a []) d ∧ IsIdemRaw (Ms.getD a []) d k) ∧ IsSumRaw Ms nA d k

/-- The Born numerator `⟨v, (A ⊗ B) v⟩` for `v` of length `dA * dB` in row-major order. -/
def quadRaw (A B : GMat) (dA dB : ℕ) (v : List GInt) : GInt :=
  gsum dA fun i => gsum dB fun j => gsum dA fun k => gsum dB fun l =>
    GInt.mul (GInt.mul (GInt.conj (vget v (i * dB + j))) (GInt.mul (entry A i k) (entry B j l)))
      (vget v (k * dB + l))

/-- The real part of `⟨v, v⟩` for `v` of length `dA * dB` in row-major order. -/
def normRaw (v : List GInt) (dA dB : ℕ) : PInt :=
  psum dA fun i => psum dB fun j =>
    (GInt.mul (GInt.conj (vget v (i * dB + j))) (vget v (i * dB + j))).1

/-- The unnormalized question weight of the description on `(x, y)`, with the point mass on
`(0, 0)` when the total weight vanishes, as in `GameData.toGame`. -/
def wt (g : GameData) (x y : ℕ) : ℕ :=
  if g.totalWeight = 0 then (if x = 0 ∧ y = 0 then 1 else 0) else g.questionWeight x y

/-- The normalizing weight: `1` when the total weight vanishes. -/
def W (g : GameData) : ℕ := if g.totalWeight = 0 then 1 else g.totalWeight

/-- The decision predicate of the description, on naturals. -/
def Draw (g : GameData) (x y a b : ℕ) : Bool :=
  if x = y ∧ a ≠ b then false else decide ((x, y, a, b) ∈ g.acc)

/-- `∑_{x, y} wt(x, y) ∑_{a, b} D(x, y, a, b) · re ⟨v, (A^x_a ⊗ B^y_b) v⟩`. -/
def numer (g : GameData) (r : RawStrategy) : PInt :=
  psum (g.nX + 1) fun x => psum (g.nX + 1) fun y =>
    PInt.mul (PInt.ofNat (wt g x y)) (psum (g.nA + 1) fun a => psum (g.nA + 1) fun b =>
      if Draw g x y a b then (quadRaw (r.matA x a) (r.matB y b) r.dA r.dB r.v).1 else PInt.zero)

/-- `p / q < value`, cleared of denominators: `p · W · k² · ⟨v, v⟩ < q · numer`; for `q = 0`,
where `p / q = 0`, the test is `0 < numer`. -/
def ValueTest (g : GameData) (p q : ℕ) (r : RawStrategy) : Prop :=
  (q = 0 ∧ PInt.Lt' PInt.zero (numer g r)) ∨
    (q ≠ 0 ∧ PInt.Lt' (PInt.mul (PInt.ofNat (p * W g * (r.k * r.k))) (normRaw r.v r.dA r.dB))
      (PInt.mul (PInt.ofNat q) (numer g r)))

/-- The candidate `r` certifies `p / q < val*(G_g)`: positive denominator, projective
measurements on both sides, a nonzero state, and the value test. -/
def Check (g : GameData) (p q : ℕ) (r : RawStrategy) : Prop :=
  0 < r.k ∧ (∀ x < g.nX + 1, IsPVMRaw (r.QA.getD x []) g.nA r.dA r.k) ∧
    (∀ y < g.nX + 1, IsPVMRaw (r.QB.getD y []) g.nA r.dB r.k) ∧
    (∃ i < r.dA, ∃ j < r.dB, ¬ GInt.Eq' (vget r.v (i * r.dB + j)) GInt.zero) ∧ ValueTest g p q r

instance (M : GMat) (d : ℕ) : Decidable (IsHermRaw M d) := by unfold IsHermRaw; infer_instance
instance (M : GMat) (d k : ℕ) : Decidable (IsIdemRaw M d k) := by unfold IsIdemRaw; infer_instance
instance (Ms : List GMat) (nA d k : ℕ) : Decidable (IsSumRaw Ms nA d k) := by
  unfold IsSumRaw; infer_instance
instance (Ms : List GMat) (nA d k : ℕ) : Decidable (IsPVMRaw Ms nA d k) := by
  unfold IsPVMRaw; infer_instance
instance (g : GameData) (p q : ℕ) (r : RawStrategy) : Decidable (ValueTest g p q r) := by
  unfold ValueTest; infer_instance
instance (g : GameData) (p q : ℕ) (r : RawStrategy) : Decidable (Check g p q r) := by
  unfold Check; infer_instance

end MIPRE.ValueApprox


