-- Prove2me | Definitions.Def_DetDLP_Machine
-- name    : DetDLP_Machine
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T09:03:32.640828+00:00
-- url     : https://prove2.me/theorems/a93506d1-4116-4535-b388-496d543c59f7
-- title:
--   Multitape Turing Machine Bounds and Binary Encodings for Deterministic DLP
-- statement:
--   This definition module establishes the uniform deterministic multitape Turing machine execution predicate, clamped logarithmic complexity bounds, and canonical binary input/output encodings used throughout the deterministic discrete logarithm development.
--
--   Building on the published multitape machine model `PrimitiveMachine` (`Def_SubexponentialSAT`), the predicate $\mathrm{RunsWithin}(A, \mathrm{out}, x, y, \tau, \sigma)$ asserts that machine $A$ started on binary input $x$ halts within at most $\tau$ steps with exact output $y$ on tape $\mathrm{out}$ while visiting at most $\sigma$ tape cells in total across all tapes at every intermediate step. For $b = \lceil \log_2 p \rceil$, the safe logarithms
--
--   $$\log_{\mathrm{safe}}(x) = \max\{1, \log_2(\max\{2, x\})\}, \qquad \log\log_{\mathrm{safe}}(x) = \max\{1, \log_2(\max\{2, \log_2(\max\{2, x\})\})\}$$
--
--   define the main time bound $2^{Cb/\sqrt{\log\log_{\mathrm{safe}} b}}$, the main space and Stage I bound $2^{Cb/(\log_{\mathrm{safe}} b)^{1/4}}$, and the Boolean tensor contraction bound $\mathrm{poly}(u) \cdot 2^{Ks/\sqrt{\log_{\mathrm{safe}} s}}$. All integers, field residues, Weierstrass curve coefficients, and affine/infinity point triples $(\iota, x, y)$ are encoded in canonical binary (`countWord` framed by `Encoding.encodeList`) so input sizes remain $O(b)$.
--
--   **Formalization Note** Using binary `countWord` rather than unary encodings prevents exponentially padded inputs; `RunsWithin` counts the input tape in `visitedSpace`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 1.2 (p. 4), Section 2.1 (p. 7), and Lemma 2.5 (p. 10)

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- A deterministic multitape Turing machine run within time `τ` and space `σ`:
started on `input`, the machine `A` halts in `time ≤ τ` steps with `output` on tape `out`,
and every intermediate configuration visits at most `σ` tape cells across all tapes. -/
def RunsWithin (A : PrimitiveMachine) (out : Fin A.tapeCount) (input output : List Bool)
    (τ σ : ℝ) : Prop :=
  ∃ (time : ℕ) (final : LocatedCfg A),
    Trace (locatedStep A) time (locatedInit A input) final ∧
    (∃ b : Bool, final.config.state = Sum.inl b) ∧
    final.config.tapes out = Turing.Tape.mk₁ (output.map some) ∧
    (time : ℝ) ≤ τ ∧
    ∀ (k : ℕ) (c : LocatedCfg A), k ≤ time →
      Trace (locatedStep A) k (locatedInit A input) c → (visitedSpace c : ℝ) ≤ σ

/-- Binary length `b = ⌈log₂ n⌉` (equals `Nat.clog 2 n`; for `p ≥ 2`, `bitLen p ≥ 1`). -/
def bitLen (n : ℕ) : ℕ := Nat.clog 2 n

/-- Well-defined base-2 logarithm `max(1, log₂(max(2, x)))`, matching Section 1.2 so all
complexity expressions remain well-defined for every `p ≥ 2`. -/
noncomputable def logSafe (x : ℝ) : ℝ :=
  max 1 (Real.logb 2 (max 2 x))

/-- Well-defined iterated base-2 logarithm `max(1, log₂(max(2, log₂(max(2, x)))))`,
matching Section 1.2 of the paper. -/
noncomputable def logLogSafe (x : ℝ) : ℝ :=
  max 1 (Real.logb 2 (max 2 (Real.logb 2 (max 2 x))))

/-- Polynomial bound `K (u + 1)^K` with a single constant `K`. -/
noncomputable def polyBound (K u : ℕ) : ℝ :=
  (K : ℝ) * ((u : ℝ) + 1) ^ K

/-- Main Theorem 1.1 time bound `2^{C b / √(log log b)}`. -/
noncomputable def mainTimeBound (C b : ℕ) : ℝ :=
  (2 : ℝ) ^ ((C : ℝ) * (b : ℝ) / Real.sqrt (logLogSafe (b : ℝ)))

/-- Main Theorem 1.1 space bound (and Stage I time bound) `2^{C b / (log b)^{1/4}}`. -/
noncomputable def mainSpaceBound (C b : ℕ) : ℝ :=
  (2 : ℝ) ^ ((C : ℝ) * (b : ℝ) / (logSafe (b : ℝ)) ^ ((1 : ℝ) / 4))

/-- Theorem 2.2 contraction time bound `poly(u) · 2^{K s / √(log s)}`. -/
noncomputable def btnTimeBound (K u s : ℕ) : ℝ :=
  polyBound K u * (2 : ℝ) ^ ((K : ℝ) * (s : ℝ) / Real.sqrt (logSafe (s : ℝ)))

/-- Binary encoding of an optional natural number: `[false]` for `none`,
`true :: countWord x` for `some x`. -/
def encodeOptionNatBin : Option ℕ → List Bool
  | none => [false]
  | some x => true :: countWord x

/-- Binary encoding of an integer: sign bit (`true` iff negative) followed by binary `|z|`. -/
def encodeIntBin (z : ℤ) : List Bool :=
  decide (z < 0) :: countWord z.natAbs

/-- Binary encoding of a list of natural numbers using `countWord` framed by `Encoding.encodeList`. -/
def encodeNatListBin (xs : List ℕ) : List Bool :=
  Encoding.encodeList countWord xs

/-- Canonical binary input encoding for prime-field multiplicative DLP `(p, g, t)`. -/
def encodeFpDLPInput (p g t : ℕ) : List Bool :=
  encodeNatListBin [p, g, t]

/-- Canonical triple `(ι, x, y)` of a Weierstrass curve point over `ZMod p`:
`(1, 0, 0)` for the point at infinity `zero`, and `(0, x.val, y.val)` for affine `(x, y)`. -/
def pointCoords {p : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)} :
    E.toAffine.Point → List ℕ
  | .zero => [1, 0, 0]
  | .some x y _ => [0, x.val, y.val]

/-- Canonical binary input encoding of a Weierstrass curve `(p, a₁, a₂, a₃, a₄, a₆)`. -/
def encodeCurveInput (p : ℕ) [NeZero p] (E : WeierstrassCurve (ZMod p)) : List Bool :=
  encodeNatListBin [p, E.a₁.val, E.a₂.val, E.a₃.val, E.a₄.val, E.a₆.val]

/-- Canonical binary input encoding for elliptic-curve DLP `(p, E, P, Q)`. -/
def encodeECDLPInput (p : ℕ) [NeZero p] (E : WeierstrassCurve (ZMod p))
    (P Q : E.toAffine.Point) : List Bool :=
  encodeNatListBin
    ([p, E.a₁.val, E.a₂.val, E.a₃.val, E.a₄.val, E.a₆.val] ++ pointCoords P ++ pointCoords Q)

end DetDLP


