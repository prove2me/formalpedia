-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_Pcp
-- name    : MIPRE_Foundations_SAT_Pcp
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:10:46.551438+00:00
-- url     : https://prove2.me/theorems/6ef48697-e396-4654-b4d3-2d564e743c7a
-- title:
--   Definitions of Pcp: The bespoke PCP for deciders: the statement `MIPRE.SAT.PcpDecider` is blueprint `thm:pcp-decider` — the paper's theorem…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.Pcp` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The bespoke PCP for deciders: the statement. `MIPRE.SAT.PcpDecider` is blueprint `thm:pcp-decider` — the paper's theorem of the same name in `answer_reduction.tex` — the classical half of answer reduction: a verifier that, given a decider specification and a *PCP view* (a point `z ∈ 𝔽_q^{m'}` and a claimed evaluation of the proof at `z`), accepts an honest low-degree proof with probability `1` and forces any low-degree proof accepted with probability more than `1/2` to encode answers the decider accepts. It consumes `lem:decoupled-5sat` — the decoupled 5SAT description of the decider is what…
--
--   **Definitions** (15): `MIPRE.SAT.BinField` (A field of size `2^k` together with a fixed `k`-bit representation of its elements.); `MIPRE.SAT.BinField.vecBits` (A vector of field elements as a list of `k`-bit blocks.); `MIPRE.SAT.PcpDecider` (**The bespoke PCP for deciders** (blueprint `thm:pcp-decider`).); `MIPRE.SAT.PcpInput` (The verifier's input: a decider specification (`DescInput`) together with a PCP view, the point and the claimed evaluation each a list of…); `MIPRE.SAT.PcpParams` (The PCP parameters `(q, m, d, m', s) = pcpparams(n, T, Q, σ)` of `def:pcpparams`.); `MIPRE.SAT.PcpParams.block` (The `i`-th of the five `m`-coordinate blocks `x₁, …, x₅` of a point of `F^{m'}`.); `MIPRE.SAT.PcpParams.d` (The individual degree bound of the proof polynomials, `d = 7`.); `MIPRE.SAT.PcpParams.m'` (The number of variables of the constraint polynomials, `m' = 5m + 5 + s`.); `MIPRE.SAT.PcpParams.q` (The field size `q = 2^k`.); `MIPRE.SAT.PcpProof` (A **low-degree PCP proof** (`def:pcp-proof`): five `m`-variate polynomials `g₁ … g₅` and `m' + 1` `m'`-variate polynomials `c₀ … c_{m'}`,…); `MIPRE.SAT.PcpProof.ev` (`ev_z(Π)` of `def:pcp-eval`: the five `αᵢ = gᵢ(xᵢ)` and the `m' + 1` `βⱼ = cⱼ(z)`.); `MIPRE.SAT.PcpProof.rawView` (The honest view at `z` in the verifier's input format: the bits of `z`, then the bits of `ev_z(Π)` with the five `αᵢ` before the `m' + 1`…); and -27 more.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `length_vecBits`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.Pcp` (`MIPRE/Foundations/SAT/Pcp.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 20 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Pcp.lean; blueprint lem:pcp-format, thm:pcp-decider

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Pcp.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding

/-!
# The bespoke PCP for deciders: the statement

`MIPRE.SAT.PcpDecider` is blueprint `thm:pcp-decider` — the paper's theorem of the same name
in `answer_reduction.tex` — the classical half of answer reduction: a verifier that, given a
decider specification and a *PCP view* (a point `z ∈ 𝔽_q^{m'}` and a claimed evaluation of the
proof at `z`), accepts an honest low-degree proof with probability `1` and forces any
low-degree proof accepted with probability more than `1/2` to encode answers the decider
accepts. It consumes `lem:decoupled-5sat` — the decoupled 5SAT description of the decider is
what the proof's constraint polynomials arithmetize — and `lem:schwartz-zippel`.

Stated here, before anything is proved, so that the consumers in chapter 6 (`ld_compiler.tex`'s
typed PCP sampler, and `thm:answer-reduction` through it) can be written against it, exactly as
`SuccinctCookLevin` and `DecoupledDescriber` were stated before being inhabited.

## What the statement needs

* `BinField k` — a field of size `2^k` with a fixed `k`-bit representation of its elements.
  The paper's admissible field size is `q = 2^k` with `k` odd and the representation is the one
  the self-dual normal basis of `lem:self-dual-basis` supplies; all the *statement* needs is the
  size and the representation. `SAT.QuotientField.shoupAdmissibleField` supplies this
  interface in the polynomial power basis, with uniform addition and multiplication
  programs. Consumers requiring a self-dual normal basis still need `lem:self-dual-basis`.
* `PcpParams` — `def:pcpparams`. Only `k, m, s` are data: `d = 7` and `m' = 5m + 5 + s` are
  determined, and the paper's `q` is `2^k`.
* `PcpProof` — `def:pcp-proof`: five `m`-variate polynomials and `m' + 1` `m'`-variate ones,
  all of individual degree at most `d`.
* `PcpProof.ev` — `def:pcp-eval`, the evaluation `(α₁ … α₅, β₀ … β_{m'})` at a point, with
  `αᵢ = gᵢ(xᵢ)` reading the `i`-th of the five `m`-coordinate blocks of `z` (`PcpParams.block`).
* `ViewFormat` — the format check item 1 requires the verifier to perform, and
  `PcpProof.rawView` the honest view in the verifier's bit-level input format.

## Two things this statement carries, and one it does not

It carries the blueprint's repair of a confirmed source defect (`rem:pcp-power-of-two`): both
`m` and `m'` are required to be powers of two dividing `q`, where the source's padding
guarantees it only for the outer `m'`. Without the inner one the conditionally linear functions
of the `m`-variate test's lines are ill defined.

It does *not* carry the source's lower bound on `q` (`eq:pcp-q-choice`,
`q ≥ (max\{Q,2\} · a'(d m'(m'+6))^{a'})^{1/b'}`), which is stated in terms of the universal
constants of `thm:lidt-cl-soundness` and is consumed not here but in `ld_compiler.tex`, where
the answer-reduced verifier's soundness error is assembled. The blueprint's statement of
`thm:pcp-decider` does not state it either; when the consumer is written it will need to be
added here or re-derived there, and that is a deliberate gap rather than an oversight.

## One convention fixed here

The paper identifies `{0,1}^m` with `{1, …, M}`, `M = 2^m`, "using, say, the lexicographic
ordering on strings". Any fixed bijection will do, and the one fixed here is the repository's
existing little-endian `bitsVal`/`bitsOfNat` convention (`Cost.bitsVal (List.ofFn w)`), so that
the low-degree encoding of an answer block agrees with the tape indexing `tapeBits` that
`thm:succinct-sat` and `lem:decoupled-5sat` already use. The choice is invisible to the
statement's content, since the same bijection appears in the encoding and in the decoding.
-/

noncomputable section

namespace MIPRE.SAT

open Cost LowDegree MvPolynomial

/-! ## Admissible fields with a bit representation -/

/-- A field of size `2^k` together with a fixed `k`-bit representation of its elements. -/
structure BinField (k : ℕ) where
  /-- The field. -/
  carrier : Type
  /-- Its field structure. -/
  instField : Field carrier
  /-- It is finite. -/
  instFintype : Fintype carrier
  /-- Equality is decidable, so the decoding map `Coded` is defined. -/
  instDecidableEq : DecidableEq carrier
  /-- It has `2^k` elements. -/
  card_carrier : Fintype.card carrier = 2 ^ k
  /-- The representation of an element as `k` bits. -/
  toBits : carrier → Cost.BitStr
  /-- Reading a representation back. -/
  ofBits : Cost.BitStr → carrier
  length_toBits : ∀ a, (toBits a).length = k
  ofBits_toBits : ∀ a, ofBits (toBits a) = a

attribute [instance] MIPRE.SAT.BinField.instField MIPRE.SAT.BinField.instFintype MIPRE.SAT.BinField.instDecidableEq

namespace BinField

variable {k : ℕ} (E : BinField k)

/-- A vector of field elements as a list of `k`-bit blocks. -/
def vecBits {n : ℕ} (v : Fin n → E.carrier) : List Cost.BitStr :=
  (List.ofFn v).map E.toBits

@[simp] theorem length_vecBits {n : ℕ} (v : Fin n → E.carrier) : (E.vecBits v).length = n := by
  simp [vecBits]

end BinField

/-! ## The parameters -/

/-- The PCP parameters `(q, m, d, m', s) = pcpparams(n, T, Q, σ)` of `def:pcpparams`. Only
`k, m, s` are data: `q = 2^k`, `d = 7` and `m' = 5m + 5 + s`. -/
structure PcpParams where
  /-- `q = 2^k`, `k` odd for an admissible field size. -/
  k : ℕ
  /-- The number of variables of the answer polynomials; `M = 2^m ≥ 2T`. -/
  m : ℕ
  /-- The number of auxiliary variables supplied by the padded succinct describer. -/
  s : ℕ

namespace PcpParams

/-- The individual degree bound of the proof polynomials, `d = 7`. -/
def d : ℕ := 7

variable (P : PcpParams)

/-- The field size `q = 2^k`. -/
def q : ℕ := 2 ^ P.k

/-- The number of variables of the constraint polynomials, `m' = 5m + 5 + s`. -/
def m' : ℕ := 5 * P.m + 5 + P.s

/-- The `i`-th of the five `m`-coordinate blocks `x₁, …, x₅` of a point of `F^{m'}`. -/
def block {F : Type*} (i : Fin 5) (z : Fin P.m' → F) : Fin P.m → F := fun j =>
  z ⟨i * P.m + j, by
    have h1 : (i : ℕ) * P.m ≤ 4 * P.m :=
      Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp i.isLt)
    have h2 : (j : ℕ) < P.m := j.isLt
    simp only [m']
    omega⟩

end PcpParams

/-! ## Proofs and views -/

/-- A **low-degree PCP proof** (`def:pcp-proof`): five `m`-variate polynomials `g₁ … g₅` and
`m' + 1` `m'`-variate polynomials `c₀ … c_{m'}`, all of individual degree at most `d`. -/
structure PcpProof (P : PcpParams) (F : Type*) [CommRing F] where
  /-- The answer polynomials `g₁, …, g₅`. -/
  g : Fin 5 → MvPolynomial (Fin P.m) F
  /-- The constraint polynomials `c₀, …, c_{m'}`. -/
  c : Fin (P.m' + 1) → MvPolynomial (Fin P.m') F
  degreeOf_g : ∀ t i, (g t).degreeOf i ≤ PcpParams.d
  degreeOf_c : ∀ t i, (c t).degreeOf i ≤ PcpParams.d

namespace PcpProof

variable {P : PcpParams} {F : Type*} [CommRing F]

/-- `ev_z(Π)` of `def:pcp-eval`: the five `αᵢ = gᵢ(xᵢ)` and the `m' + 1` `βⱼ = cⱼ(z)`. -/
def ev (pf : PcpProof P F) (z : Fin P.m' → F) : (Fin 5 → F) × (Fin (P.m' + 1) → F) :=
  (fun i => eval (P.block i z) (pf.g i), fun j => eval z (pf.c j))

/-- The honest view at `z` in the verifier's input format: the bits of `z`, then the bits of
`ev_z(Π)` with the five `αᵢ` before the `m' + 1` `βⱼ`. -/
def rawView {k : ℕ} (E : BinField k) (pf : PcpProof P E.carrier) (z : Fin P.m' → E.carrier) :
    List Cost.BitStr × List Cost.BitStr :=
  (E.vecBits z, E.vecBits (pf.ev z).1 ++ E.vecBits (pf.ev z).2)

end PcpProof

/-- The verifier's input: a decider specification (`DescInput`) together with a PCP view, the
point and the claimed evaluation each a list of `k`-bit blocks. -/
abbrev PcpInput : Type := DescInput × List Cost.BitStr × List Cost.BitStr

/-- The verifier's input, assembled. -/
def pcpInput (D : Prog) (n T Q σ : ℕ) (x y : Cost.BitStr) (z ev : List Cost.BitStr) : PcpInput :=
  (((D, n, T, Q, σ), x, y), z, ev)

/-- The PCP view is formatted correctly: `m'` blocks for the point, `6 + m'` for the claimed
evaluation, each of `k` bits. Item 1 of the theorem asks the verifier to reject otherwise. -/
structure ViewFormat (P : PcpParams) (z ev : List Cost.BitStr) : Prop where
  length_z : z.length = P.m'
  length_ev : ev.length = 6 + P.m'
  width_z : ∀ b ∈ z, b.length = P.k
  width_ev : ∀ b ∈ ev, b.length = P.k

/-! ## The answer blocks as subcube-indexed vectors -/

/-- The answer block of a string `ap`, as a `{0,1}^m`-indexed vector of field elements: the
tape encoding `tapeBits` read at the little-endian index of the subcube point. This is the
paper's `a = enc_Γ(a_prefix, ⊔^{M/2 - ℓ})`, viewed in `F^M` through `{0,1} ⊆ F`. -/
def answerVec (F : Type*) [CommRing F] (m : ℕ) (ap : Cost.BitStr) : (Fin m → Bool) → F :=
  fun w => ofBool (tapeBits ap (bitsVal (List.ofFn w)))

/-! ## The theorem -/

/-- **The bespoke PCP for deciders** (blueprint `thm:pcp-decider`). An instance of this
structure is the theorem. -/
structure PcpDecider where
  /-- `pcpparams(n, T, Q, σ)`. -/
  params : ℕ → ℕ → ℕ → ℕ → PcpParams
  /-- The field of size `q = 2^k` with its `k`-bit representation, for each admissible
  (odd) extension degree. In particular this excludes `k = 0`, for which `BinField k`
  would require a one-element field. -/
  fld : (k : ℕ) → Odd k → BinField k
  /-- The verifier. -/
  verify : PolyTimeFun PcpInput Bool
  /-- The parameters, in polynomial time from `(n, T, Q, σ)`. -/
  paramsProg : PolyTimeFun (ℕ × ℕ × ℕ × ℕ) (ℕ × ℕ × ℕ)
  paramsProg_eq : ∀ n T Q σ,
    paramsProg (n, T, Q, σ) = ((params n T Q σ).k, (params n T Q σ).m, (params n T Q σ).s)
  /-- The field size is admissible: `k` is odd. -/
  odd_k : ∀ n T Q σ, Odd (params n T Q σ).k
  /-- `m` is chosen so that `M = 2^m ≥ 2T`, as the padded succinct describer chooses it. -/
  two_mul_le : ∀ n T Q σ, 2 * T ≤ 2 ^ (params n T Q σ).m
  /-- `m'` is a power of two: the padding step of the PCP, `def:pcpparams`. -/
  m'_isPow : ∀ n T Q σ, ∃ j, (params n T Q σ).m' = 2 ^ j
  /-- `m' ∣ q`, which the `m'`-variate low-degree test's diagonal lines need. -/
  m'_dvd_q : ∀ n T Q σ, (params n T Q σ).m' ∣ (params n T Q σ).q
  /-- `m` is a power of two as well. This is the blueprint's repair of a confirmed defect in
  the source (`rem:pcp-power-of-two`): the source's padding guarantees a power of two only for
  the outer count `m'`, while the `m`-variate low-degree test applied to the answer
  polynomials needs `m ∣ q` for the inner `m` too. -/
  m_isPow : ∀ n T Q σ, ∃ j, (params n T Q σ).m = 2 ^ j
  /-- `m ∣ q`, the hypothesis `rem:pcp-power-of-two` says a formalization must state. -/
  m_dvd_q : ∀ n T Q σ, (params n T Q σ).m ∣ (params n T Q σ).q
  /-- Item 1: the verifier rejects an invalid specification or a misformatted view. -/
  reject_invalid : ∀ D n T Q σ x y z ev,
    (¬ Valid D n T Q σ x y ∨ ¬ ViewFormat (params n T Q σ) z ev) →
      verify (pcpInput D n T Q σ x y z ev) = false
  /-- Item 2: the verifier runs in time `poly(log T, log n, Q, σ)` on formatted inputs. -/
  time_le : ∃ R : Polynomial ℕ, ∀ D n T Q σ x y z ev, Valid D n T Q σ x y →
    ViewFormat (params n T Q σ) z ev →
      ∃ t ≤ R.eval (Nat.size n + Nat.size T + Q + σ),
        verify.code.Runs (encode (pcpInput D n T Q σ x y z ev))
          (encode (verify (pcpInput D n T Q σ x y z ev))) t
  /-- Item 3 (**completeness**): if the decider accepts `(n, x, y, ap, bp)` within `T`, the
  low-degree proof whose first two answer polynomials are the low-degree encodings of the
  padded answers is accepted at every point. -/
  completeness : ∀ (D : Decider) n T Q σ x y, Valid D.prog n T Q σ x y →
    ∀ ap bp : Cost.BitStr, ap.length ≤ T → bp.length ≤ T → D.AcceptsWithin n x y ap bp T →
      ∃ pf : PcpProof (params n T Q σ) (fld (params n T Q σ).k (odd_k n T Q σ)).carrier,
        pf.g 0 = ldEnc (answerVec _ (params n T Q σ).m ap) ∧
        pf.g 1 = ldEnc (answerVec _ (params n T Q σ).m bp) ∧
        ∀ z, verify (pcpInput D.prog n T Q σ x y
          (pf.rawView (fld (params n T Q σ).k (odd_k n T Q σ)) z).1
          (pf.rawView (fld (params n T Q σ).k (odd_k n T Q σ)) z).2) = true
  /-- Item 4 (**soundness**): a low-degree proof accepted at more than half the points decodes
  to answers the decider accepts within `T`. -/
  soundness : ∀ (D : Decider) n T Q σ x y, Valid D.prog n T Q σ x y →
    ∀ pf : PcpProof (params n T Q σ) (fld (params n T Q σ).k (odd_k n T Q σ)).carrier,
      (params n T Q σ).q ^ (params n T Q σ).m' <
          2 * (Finset.univ.filter
            fun z : Fin (params n T Q σ).m' →
                (fld (params n T Q σ).k (odd_k n T Q σ)).carrier =>
              verify (pcpInput D.prog n T Q σ x y
                (pf.rawView (fld (params n T Q σ).k (odd_k n T Q σ)) z).1
                (pf.rawView (fld (params n T Q σ).k (odd_k n T Q σ)) z).2) = true).card →
        ∃ ap bp : Cost.BitStr, ap.length ≤ T ∧ bp.length ≤ T ∧
          D.AcceptsWithin n x y ap bp T ∧
          coded (pf.g 0) = answerVec _ (params n T Q σ).m ap ∧
          coded (pf.g 1) = answerVec _ (params n T Q σ).m bp

end MIPRE.SAT

end


