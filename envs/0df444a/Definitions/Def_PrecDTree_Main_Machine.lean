-- Prove2me | Definitions.Def_PrecDTree_Main_Machine
-- name    : PrecDTree_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:52:01.743483+00:00
-- url     : https://prove2.me/theorems/94ecdd74-3ba4-4c4f-8f96-69b24bd86b3a
-- title:
--   Binary encodings and polynomial-time approximation algorithms for PCWCDT, f-PCSC and Partial-RBSC
-- statement:
--   The paper's "polynomial-time algorithm" is read as one deterministic Turing machine, fixed before the input, that maps the binary code of an instance to the binary code of an output within a number of steps polynomial in the input length. An **$\rho$-approximation algorithm for PCWCDT** outputs, on every instance $I$ (a nonempty hypothesis set, tests, a partial order, every two hypotheses separated), a precedence-closed decision tree $D$ for $I$ with
--   $$\mathrm{cost}_W(D)\le\rho(I)\cdot\mathrm{OPT}(I).$$
--   A **bicriteria $(\alpha,\beta)$-approximation algorithm for f-PCSC** outputs, on every instance, a precedence-closed family covering at least $f\cdot n/\beta$ elements with at most $\alpha\cdot\mathrm{OPT}$ sets.
--
--   **Formalization Note.** `PolyTimeBin alg` is `Nonempty (Turing.TM2ComputableInPolyTime id id alg)` for `alg : List Bool → List Bool` (Mathlib's FinTM2 over `Bool`). Codes: `encNat` (doubled binary digits and a terminator, logarithmic length), `encRat`, incidence bits `encBits`, tables in index order after the dimensions. `DTInstance` is a PCWCDT instance with hypotheses `Fin n`, `encodeDT` its code, `encodeTree` the prefix code of the part of a decision tree reached by the hypotheses. `PCWCDTApprox ratio alg` asks the output on every well-formed instance to be the code of a precedence-closed tree within `ratio I · OPT(I)`. `PCSCInstance` (fraction `f : ℚ`), `PCSCApprox α β alg` with `α : ℕ → ℝ` evaluated at the instance's number of sets, and `HasPolyPCSCApprox α β`. `encodeRB`, `LPSolQ` (rational LP point) with `encodeLPQ`, and `encodeOutcome` (all coins, table by table) serve Theorem 4.2 and Claim 4.8. Codes of invalid instances may get any output.
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 7 (Theorem 3.8), p. 9 (Theorem 4.2), pp. 16–18 (Claim 4.8, Theorem 4.9, Corollary 4.10); the machine model and the codes are this formalization's choice

import Mathlib
import Definitions.Def_PrecDTree_Main_DecisionTree
import Definitions.Def_PrecDTree_Main_PCSC
import Definitions.Def_PrecDTree_Main_RBSC
import Definitions.Def_PrecDTree_Main_Rounding

set_option autoImplicit false

/-!
# Binary encodings and polynomial-time algorithms (Theorems 3.8, 4.2, 4.9, Claim 4.8, Cor. 4.10)

The paper names no machine model ("polynomial-time"). An algorithm is a function
`alg : List Bool → List Bool` computed by a Mathlib `Turing.TM2ComputableInPolyTime` machine on
binary words (`PolyTimeBin`). One machine serves every instance; it is required to behave only on
the codes of valid instances. Natural numbers are written in self-delimiting binary (`encNat`,
length logarithmic in the value), rationals as sign, numerator and denominator, a subset of
`Fin N` as its `N` incidence bits, and every table in index order after its dimensions.
-/

namespace PrecDTree.Main

open Classical

/-! ## Polynomial time -/

/-- `alg` is computed by a deterministic multi-stack Turing machine (Mathlib `FinTM2`) over the
alphabet `Bool`, within a polynomial number of steps in the input length. -/
def PolyTimeBin (alg : List Bool → List Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) alg)

/-! ## Basic codes -/

/-- Self-delimiting binary numeral: the bits of `n` (least significant first), each doubled, then
the terminator `01`. -/
def encNat (n : ℕ) : List Bool := (n.bits.flatMap fun b => [b, b]) ++ [false, true]

/-- An integer as a sign bit and its magnitude. -/
def encInt (z : ℤ) : List Bool := decide (z < 0) :: encNat z.natAbs

/-- A rational as the numerator and the (positive) denominator of its reduced form. -/
def encRat (q : ℚ) : List Bool := encInt q.num ++ encNat q.den

/-- A table `f : Fin n → α`, entries in index order. -/
def encTable {n : ℕ} {α : Type} (e : α → List Bool) (f : Fin n → α) : List Bool :=
  (List.finRange n).flatMap fun i => e (f i)

/-- A subset of `Fin N` as its `N` incidence bits. -/
def encBits {N : ℕ} (S : Finset (Fin N)) : List Bool :=
  encTable (fun i : Fin N => [decide (i ∈ S)]) (fun i : Fin N => i)

/-! ## PCWCDT instances and decision trees -/

/-- A PCWCDT instance: hypotheses `Fin n`, tests `Fin m`, test `t` replies `test t h ∈ ℕ` on
hypothesis `h` (its partition of `H` is the family of fibres), and the precedence relation
`prec a b = true` iff `a ⪯ b`. -/
structure DTInstance where
  n : ℕ
  m : ℕ
  test : Fin m → Fin n → ℕ
  prec : Fin m → Fin m → Bool

/-- The precedence relation `⪯` of a PCWCDT instance. -/
def DTInstance.le (I : DTInstance) : Fin I.m → Fin I.m → Prop := fun a b => I.prec a b = true

/-- A valid PCWCDT instance: `H` nonempty, `⪯` a partial order, and every two distinct hypotheses
separated by some test. -/
def DTInstance.WellFormed (I : DTInstance) : Prop :=
  0 < I.n ∧ IsPartialOrderRel I.le ∧ Identifiable I.test Finset.univ

/-- Binary code of a PCWCDT instance: `n`, `m`, the reply table, the order matrix. -/
def encodeDT (I : DTInstance) : List Bool :=
  encNat I.n ++ encNat I.m ++ encTable (fun row => encTable encNat row) I.test ++
    encTable (fun row => encTable (fun b => [b]) row) I.prec

/-- Binary code of the part of a decision tree reached by the hypotheses of `Hs`: a leaf is `0`
followed by its hypothesis; a node is `1`, its test, the number of nonempty replies, and for each
nonempty reply label `v` in increasing order, `v` followed by the code of the child on `v`. -/
noncomputable def encodeTreeOn {m : ℕ} {H : Type} [DecidableEq H] (T : Fin m → H → ℕ)
    (code : H → List Bool) : Finset H → DTree m H → List Bool
  | _, .leaf h => false :: code h
  | Hs, .node t c =>
      true :: (encNat t.val ++ encNat (Hs.image (T t)).card ++
        ((Hs.image (T t)).sort (· ≤ ·)).flatMap
          (fun v => encNat v ++ encodeTreeOn T code (block T Hs t v) (c v)))

/-- Binary code of a decision tree output for a PCWCDT instance (hypothesis `h` written as
`encNat h`). -/
noncomputable def encodeTree (I : DTInstance) (D : DTree I.m (Fin I.n)) : List Bool :=
  encodeTreeOn I.test (fun h => encNat h.val) Finset.univ D

/-- `alg` is an approximation algorithm for PCWCDT with ratio `ratio I`: on the code of every
valid instance `I` it outputs the code of a precedence-closed decision tree `D` for `I` with
`cost_W(D) ≤ ratio I · OPT(I)`. -/
def PCWCDTApprox (ratio : DTInstance → ℝ) (alg : List Bool → List Bool) : Prop :=
  ∀ I : DTInstance, I.WellFormed →
    ∃ D : DTree I.m (Fin I.n),
      alg (encodeDT I) = encodeTree I D ∧ IsPCTree I.le I.test Finset.univ D ∧
        (costW I.test Finset.univ D : ℝ) ≤ ratio I * (optW I.le I.test Finset.univ : ℝ)

/-! ## f-PCSC instances -/

/-- An f-PCSC instance: sets `sets i ⊆ Fin N` (`i : Fin m`), the order `prec`, and the fraction `f`
(rational). Its universe is `⋃ sets`. -/
structure PCSCInstance where
  N : ℕ
  m : ℕ
  sets : Fin m → Finset (Fin N)
  prec : Fin m → Fin m → Bool
  f : ℚ

/-- The precedence relation of an f-PCSC instance. -/
def PCSCInstance.le (I : PCSCInstance) : Fin I.m → Fin I.m → Prop := fun a b => I.prec a b = true

/-- A valid f-PCSC instance: `⪯` a partial order and `0 < f ≤ 1`. -/
def PCSCInstance.WellFormed (I : PCSCInstance) : Prop :=
  IsPartialOrderRel I.le ∧ 0 < I.f ∧ I.f ≤ 1

/-- Binary code of an f-PCSC instance. -/
def encodePCSC (I : PCSCInstance) : List Bool :=
  encNat I.N ++ encNat I.m ++ encTable encBits I.sets ++
    encTable (fun row => encTable (fun b => [b]) row) I.prec ++ encRat I.f

/-- Binary code of a subfamily `C ⊆ Fin m` (incidence bits). -/
def encodeFamily {m : ℕ} (C : Finset (Fin m)) : List Bool := encBits C

/-- `alg` is a bicriteria `(α, β)`-approximation algorithm for f-PCSC, the ratio `α` evaluated at
the number `m` of sets of the instance: on every valid instance it outputs the code of a
precedence-closed family covering at least `f · n / β` elements, of size at most `α(m) · OPT`. -/
def PCSCApprox (α : ℕ → ℝ) (β : ℝ) (alg : List Bool → List Bool) : Prop :=
  ∀ I : PCSCInstance, I.WellFormed →
    ∃ C : Finset (Fin I.m), alg (encodePCSC I) = encodeFamily C ∧
      IsBicriteria I.le I.sets (I.f : ℝ) (α I.m) β C

/-- There is a polynomial-time bicriteria `(α, β)`-approximation algorithm for f-PCSC. -/
def HasPolyPCSCApprox (α : ℕ → ℝ) (β : ℝ) : Prop :=
  ∃ alg : List Bool → List Bool, PolyTimeBin alg ∧ PCSCApprox α β alg

/-! ## Partial-RBSC instances, LP solutions and coin outcomes -/

/-- Binary code of a Partial-RBSC instance: `k, n, m, t`, then per set its red and blue
incidence bits. -/
def encodeRB (I : RBInstance) : List Bool :=
  encNat I.k ++ encNat I.n ++ encNat I.m ++ encNat I.t ++ encTable encBits I.red ++
    encTable encBits I.blue

/-- A rational LP point. -/
structure LPSolQ (I : RBInstance) where
  y : Fin I.k → ℚ
  x : Fin I.m → ℚ
  z : Fin I.n → ℚ
  a : Fin I.n → Fin I.m → ℚ
  yy : Fin I.k → Fin I.k → ℚ

/-- The real LP point of a rational one. -/
def LPSolQ.toReal {I : RBInstance} (q : LPSolQ I) : LPSol I where
  y r := q.y r
  x S := q.x S
  z u := q.z u
  a u S := q.a u S
  yy r p := q.yy r p

/-- Binary code of a rational LP point. -/
def encodeLPQ {I : RBInstance} (q : LPSolQ I) : List Bool :=
  encTable encRat q.y ++ encTable encRat q.x ++ encTable encRat q.z ++
    encTable (fun row => encTable encRat row) q.a ++ encTable (fun row => encTable encRat row) q.yy

/-- Binary code of a coin outcome: all activation coins, then all trial coins, then all marking
coins, each table in index order. -/
def encodeOutcome (I : RBInstance) (ω : I.Coin → Bool) : List Bool :=
  encTable (fun r => encTable (fun j => [ω (.inl (r, j))]) (fun j : Fin I.k => j))
      (fun r : Fin I.k => r) ++
    encTable (fun r => encTable (fun j => encTable (fun S => [ω (.inr (.inl (r, j, S)))])
      (fun S : Fin I.m => S)) (fun j : Fin I.k => j)) (fun r : Fin I.k => r) ++
    encTable (fun r => encTable (fun j => encTable (fun S => encTable
      (fun u => [ω (.inr (.inr (r, j, S, u)))]) (fun u : Fin I.n => u)) (fun S : Fin I.m => S))
      (fun j : Fin I.k => j)) (fun r : Fin I.k => r)

end PrecDTree.Main


