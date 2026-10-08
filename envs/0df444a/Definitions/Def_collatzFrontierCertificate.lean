-- Prove2me | Definitions.Def_collatzFrontierCertificate
-- name    : collatzFrontierCertificate
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-04T17:35:52.689973+00:00
-- url     : https://prove2.me/theorems/32ce78a2-88bc-451d-bc8d-dd6ca0963e5c
-- title:
--   Descent-certificate data model: affine states, exact/terminal rows, the checker, and the generator
-- statement:
--   This module fixes the finite, machine-checkable data model behind the Syracuse descent-certificate checker used throughout this contribution. The accelerated map is $\mathrm{syracuseStep}(n) = \mathrm{ordCompl}_2(3n+1)$, the odd part of $3n+1$. An `AffineState` is a pair `(constant, coefficient)` representing the residue family $\mathrm{constant} + \mathrm{coefficient} \cdot q$ ranging over $q \in \mathbb{N}$, so one certificate verifies a whole arithmetic progression at once, not a single integer. A `CertificateRow` records one claimed division step: an exponent $e$ and the resulting `AffineState`. `ExactRowValid s row` holds when `row` is a genuine exact dyadic division of $3 \cdot s.\mathrm{constant} + 1$ (and the parallel coefficient identity $3 \cdot s.\mathrm{coefficient} = 2^{e} \cdot \mathrm{row.next.coefficient}$), with the surviving quotient left odd and the drifting coefficient left even, so the chain can continue. `runExactPrefix` replays a list of such rows from a start state, returning `none` as soon as one row fails validation. A `DescentCertificate` bundles a start state, a finite list of exact rows, and one `terminal` row that only needs the weaker `TerminalRowValid` condition (the same divisibility identities, without the parity side conditions). `StartValid s` is the canonical-input condition: a positive odd representative strictly below an even positive modulus. `checkDescent` is the actual decidable Boolean predicate the checker evaluates: replay the exact rows, then check the start condition, the terminal row, and that both the representative and the modulus did not increase, with the representative strictly decreasing:
--   $$\mathrm{checkDescent}(\mathrm{cert}) = \mathrm{true} \iff \text{the exact rows replay and the start/terminal/decrease conditions all hold.}$$
--   `checkDescentSimple` is an equivalent simplified checker that drops the (provably redundant) final coefficient comparison; agrees with `checkDescent` (repo lemma `CollatzFrontier.checkDescentSimple_eq_checkDescent`, AffineDrift.lean). `candidateExponent`, `candidateRow`, `candidatePrefix`, and `candidateCertificate` together form the executable generator: a bounded trial-division search (capped by an explicit `fuel` parameter) that guesses each row's exponent and quotient; the checker always independently re-validates whatever the generator produces, so a bad guess is simply rejected, never trusted. `chainCertificate` packages an abstract representative sequence $b : \mathbb{N} \to \mathbb{N}$ and exponent sequence $a : \mathbb{N} \to \mathbb{N}$ together with a dyadic modulus budget $K$ into the certificate format, by tracking the exact remaining budget $K - \sum_{j<i} a_j$ as the coefficient at each step; this is the bridge used to turn an actual finite Syracuse descent into an accepted certificate.
--
--   **Role.** These definitions are shared by every theorem in this contribution: the checker-completeness lemma, the linear-budget completeness theorem, the executable failure-rate bounds, and the unconditional (adaptive-budget) completeness equivalence all state their conclusions directly in terms of `checkDescent`, `candidateCertificate`, and `chainCertificate`.
--
--   **Formalization Note.** This is a verbatim defs-only transcription (no proofs) of the structures and functions declared in `lean/CollatzFrontier/FiniteCertificate.lean`, `AffineDrift.lean`, `GeneratedCertificate.lean`, and `CertificateCompleteness.lean` on the cited branch.
-- source:
--   collatz-frontier (private repo), branch research/executable-coverage-20261002 @ 3835de1c8e7bf56d5632af07979d0fd2d580095c (stacks on research/certificate-density-20261002 @ 61e6b54c74e600c8c72fc2d271f5b4d11e9e8869 and main @ 4d656b9c9c5815305bd391f206c9d3e9587dd395); lean/CollatzFrontier/{FiniteCertificate,AffineDrift,GeneratedCertificate,CertificateCompleteness}.lean (definitions only)

import Definitions.Def_syracuseStep

/-
Core data model for the explicit descent-certificate checker, taken verbatim
(defs/structures/instances only, no proofs) from the collatz-frontier repo
(`lean/CollatzFrontier/FiniteCertificate.lean`, `AffineDrift.lean`,
`GeneratedCertificate.lean`, `CertificateCompleteness.lean`), commit 3835de1
(branch research/executable-coverage-20261002, stacking on
research/certificate-density-20261002 @ 61e6b54 and main @ 4d656b9).

A `DescentCertificate` is a finite, machine-checkable witness that a residue
class `n + 2^K * q` (for all `q`) Syracuse-descends in a fixed number of
steps: an exact prefix of division rows (each one dividing `3x+1` by an
exact power of two) followed by one terminal row that only needs a
divisibility bound. `checkDescent` is the actual decidable predicate the
checker evaluates; `candidateCertificate` is the executable generator that
guesses the division exponents by trial division up to a fuel bound; and
`chainCertificate` packages a representative-and-exponent sequence into the
certificate format used by the completeness proofs.
-/

namespace CollatzFrontier

/-- The affine family `constant + coefficient * q`, ranging over `q : ℕ`. -/
structure AffineState where
  constant : ℕ
  coefficient : ℕ
  deriving DecidableEq, Repr

/-- Evaluate the affine family at a given multiplier `q`. -/
def AffineState.eval (s : AffineState) (q : ℕ) : ℕ :=
  s.constant + s.coefficient * q

/-- One exact division row: a claimed valuation exponent and the resulting state. -/
structure CertificateRow where
  exponent : ℕ
  next : AffineState
  deriving DecidableEq, Repr

/-- An exact row is valid when it is a genuine positive-exponent dyadic division of `3x+1`,
with the surviving quotient odd and the drifting coefficient left even. -/
def ExactRowValid (s : AffineState) (row : CertificateRow) : Prop :=
  0 < row.exponent ∧
  3 * s.constant + 1 = 2 ^ row.exponent * row.next.constant ∧
  3 * s.coefficient = 2 ^ row.exponent * row.next.coefficient ∧
  row.next.constant % 2 = 1 ∧ row.next.coefficient % 2 = 0

instance (s : AffineState) (row : CertificateRow) :
    Decidable (ExactRowValid s row) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Replay the list of exact rows from a starting state; a single invalid row rejects
the whole prefix (returns `none`). -/
def runExactPrefix (s : AffineState) : List CertificateRow → Option AffineState
  | [] => some s
  | row :: rest =>
      if ExactRowValid s row then runExactPrefix row.next rest else none

/-- The terminal row only needs the exact dyadic division identities (no parity side
conditions on the quotient). -/
def TerminalRowValid (s : AffineState) (row : CertificateRow) : Prop :=
  0 < row.exponent ∧
  3 * s.constant + 1 = 2 ^ row.exponent * row.next.constant ∧
  3 * s.coefficient = 2 ^ row.exponent * row.next.coefficient

instance (s : AffineState) (row : CertificateRow) :
    Decidable (TerminalRowValid s row) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A descent certificate: a canonical starting state, a finite list of exact rows,
and one terminal row. -/
structure DescentCertificate where
  start : AffineState
  exactRows : List CertificateRow
  terminal : CertificateRow
  deriving Repr

/-- The canonical start condition: a positive odd representative strictly below an
even positive modulus. -/
def StartValid (s : AffineState) : Prop :=
  0 < s.constant ∧ s.constant < s.coefficient ∧
  s.constant % 2 = 1 ∧ s.coefficient % 2 = 0

instance (s : AffineState) : Decidable (StartValid s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The actual finite, executable descent checker: replay the exact rows, then check the
start condition, the terminal row, and that both the representative and the modulus
strictly (resp. weakly) decreased. -/
def checkDescent (cert : DescentCertificate) : Bool :=
  match runExactPrefix cert.start cert.exactRows with
  | none => false
  | some last => decide (StartValid cert.start ∧ TerminalRowValid last cert.terminal ∧
      cert.terminal.next.constant < cert.start.constant ∧
      cert.terminal.next.coefficient ≤ cert.start.coefficient)

/-- An algebraically-equivalent simplified checker that drops the (redundant) coefficient
comparison; agrees with `checkDescent` (repo lemma
`CollatzFrontier.checkDescentSimple_eq_checkDescent`, AffineDrift.lean). -/
def checkDescentSimple (cert : DescentCertificate) : Bool :=
  match runExactPrefix cert.start cert.exactRows with
  | none => false
  | some last => decide (StartValid cert.start ∧ TerminalRowValid last cert.terminal ∧
      cert.terminal.next.constant < cert.start.constant)

/-- Bounded trial-division search for the 2-adic valuation of `n`, capped by `fuel`. -/
def candidateExponent : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n % 2 = 0 then candidateExponent fuel (n / 2) + 1 else 0

/-- The executable row generator: guess the exponent by bounded search, then read off the
resulting quotients. The checker independently re-validates every field. -/
def candidateRow (fuel : ℕ) (s : AffineState) : CertificateRow :=
  let e := candidateExponent fuel (3 * s.constant + 1)
  ⟨e, ⟨(3 * s.constant + 1) / 2 ^ e, (3 * s.coefficient) / 2 ^ e⟩⟩

/-- Iterate the row generator `k` times from a starting state, returning the generated
exact-row list together with the resulting state. -/
def candidatePrefix (fuel : ℕ) : ℕ → AffineState → List CertificateRow × AffineState
  | 0, s => ([], s)
  | k + 1, s =>
      let row := candidateRow fuel s
      let tail := candidatePrefix fuel k row.next
      (row :: tail.1, tail.2)

/-- The fully executable candidate certificate generator: generate `k` exact rows by
bounded search from representative `r` and modulus `M`, then one more generated row as
the terminal row. This is the actual generator the executable checker is run against. -/
def candidateCertificate (fuel k r M : ℕ) : DescentCertificate :=
  let result := candidatePrefix fuel k ⟨r, M⟩
  ⟨⟨r, M⟩, result.1, candidateRow fuel result.2⟩

/-- Compile a representative/exponent pair of sequences `(a, b)` and a dyadic modulus budget
`K` into the certificate format: row `i`'s coefficient is the exact dyadic remainder
`3^i * 2^(K - (a 0 + ... + a (i-1)))` of the budget, so the final representative state is
canonical whenever the full budget `K` is not exceeded. -/
def chainCertificate (a b : ℕ → ℕ) (K k : ℕ) : DescentCertificate :=
  let s := fun i : ℕ => AffineState.mk (b i) (3 ^ i * 2 ^ (K - ∑ j ∈ Finset.range i, a j))
  let row := fun i : ℕ => CertificateRow.mk (a i) (s (i + 1))
  ⟨s 0, (List.range k).map row, row k⟩

end CollatzFrontier


