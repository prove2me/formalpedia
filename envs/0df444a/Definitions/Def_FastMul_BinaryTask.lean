-- Prove2me | Definitions.Def_FastMul_BinaryTask
-- name    : FastMul_BinaryTask
-- status  : Definition
-- author  : @arpcs
-- created : 2026-10-31T03:59:14.621578+00:00
-- url     : https://prove2.me/theorems/efabf833-d5c8-42f4-8afe-6ecfb8b063e8
-- title:
--   Ordinary polynomial products and charged finite-tape time bounds
-- statement:
--   For each positive coefficient length $n$, binary inputs represent ordinary polynomials over $\mathbb F_2$. The output word lists every coefficient of their ordinary product in ascending degree order, including zero coefficients, and has exactly $2n-1$ bits.
--
--   For a rational $0\le\kappa\le1$, the time predicate requires one fixed deterministic finite-tape machine, a constant $C>0$ and a threshold $n_0$, chosen before every input. Every positive input must halt with the complete literal output; for $n\ge n_0$ its transition count is at most $Cn\max(1,\lceil\log_2n\rceil)^{1-\kappa}$.
--
--   The extension predicate fixes each finite field of characteristic two before choosing a positive bit width, an injective coefficient encoding, a machine and its constants. It counts coefficient length $n$ and encodes every output coefficient in the same fixed width.
--
--   The generic machine and its actual transitions are reused from the published IntMul_MultitapeModel definition. Its integer-value and integer-product predicates are not used. These definitions state tasks and do not prove existence of a fast algorithm.
-- source:
--   Árpád Csizmadia, Ordinary Binary Polynomial Multiplication below n log n: Controlled tensor routing on fixed tapes, version 0.1.0-preprint (2026), Theorem 9 and Corollary 10; https://github.com/arpcs/finite-field-polynomial-multiplication/blob/fb94421e3e6d9f8348a6e5b963b5a62d9c525e95/papers/03-best-binary/main.tex#L1013 . Generic machine: avi, IntMul_MultitapeModel, https://prove2.me/theorems/47ff1689-4e87-4af2-9406-674787e32429 . Mathlib supplies ordinary Polynomial and ZMod semantics.

import Definitions.Def_IntMul_MultitapeModel

set_option autoImplicit false

universe u

namespace FastMulPlatform

noncomputable def polynomialOf {F : Type u} [Semiring F] {n : ℕ}
    (f : Fin n → F) : Polynomial F :=
  ∑ i : Fin n, Polynomial.C (f i) * Polynomial.X ^ i.val

def bitCoefficient (b : Bool) : ZMod 2 := if b then 1 else 0

noncomputable def binaryProductWord {n : ℕ} (f g : Fin n → Bool) : List Bool :=
  List.ofFn fun j : Fin (2 * n - 1) =>
    decide (((polynomialOf (fun i => bitCoefficient (f i))) *
      (polynomialOf (fun i => bitCoefficient (g i)))).coeff j.val = 1)

def logScale (n : ℕ) : ℕ := max (Nat.clog 2 n) 1

noncomputable def timeEnvelope (κ : ℚ) (n : ℕ) : ℝ :=
  (n : ℝ) * (logScale n : ℝ) ^ (1 - (κ : ℝ))

def BinaryTimeBound (κ : ℚ) : Prop :=
  0 ≤ κ ∧ κ ≤ 1 ∧
    ∃ (M : IntMul.MultitapeTM) (C : ℝ) (n₀ : ℕ),
      0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ f g : Fin n → Bool,
        ∃ t : ℕ,
          M.HaltsWithOutput (List.ofFn f) (List.ofFn g) t (binaryProductWord f g) ∧
          (n₀ ≤ n → (t : ℝ) ≤ C * timeEnvelope κ n)

def encodeCoefficients {F : Type u} {n w : ℕ}
    (encode : F → Fin w → Bool) (f : Fin n → F) : List Bool :=
  (List.ofFn f).flatMap fun a => List.ofFn (encode a)

noncomputable def fieldProductWord {F : Type u} [Semiring F] {n w : ℕ}
    (encode : F → Fin w → Bool) (f g : Fin n → F) : List Bool :=
  encodeCoefficients encode
    (fun j : Fin (2 * n - 1) => ((polynomialOf f) * (polynomialOf g)).coeff j.val)

def FixedCharTwoTimeBound (κ : ℚ) : Prop :=
  0 ≤ κ ∧ κ ≤ 1 ∧
    ∀ (F : Type u) [Field F] [Fintype F] [CharP F 2],
      ∃ (w : ℕ) (encode : F → Fin w → Bool),
        0 < w ∧ Function.Injective encode ∧
        ∃ (M : IntMul.MultitapeTM) (C : ℝ) (n₀ : ℕ),
          0 < C ∧
          ∀ n : ℕ, 1 ≤ n → ∀ f g : Fin n → F,
            ∃ t : ℕ,
              M.HaltsWithOutput (encodeCoefficients encode f)
                (encodeCoefficients encode g) t (fieldProductWord encode f g) ∧
              (n₀ ≤ n → (t : ℝ) ≤ C * timeEnvelope κ n)

end FastMulPlatform


