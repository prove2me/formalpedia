-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
-- name    : ArdaRH65K_Turing121_Arb4_Q
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:04:14.13564+00:00
-- url     : https://prove2.me/theorems/6291c18d-dd71-4567-b49a-5cfa1ddaa5e7
-- title:
--   Arb4 Q certificate definitions
-- statement:
--   This bundle represents exact signed rational numbers and defines their arithmetic and comparisons. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{Arb4.Q.dm},\;\mathtt{Arb4.Q.mk},\;\mathtt{Arb4.Q.n},\;\mathtt{Arb4.Q}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Q.lean

import Mathlib
/-  Arb4_Q.lean -- lane Arb4 (h1000 compaction): exact rational arithmetic for Boolean kernel
    checkers.

    A certificate side condition such as the error budget of an octant piece is a polynomial
    inequality between explicit rationals.  Closing it by `norm_num` stores the whole normalisation
    trace in the olean (about 300 KB per budget at height 1000).  Here the same inequality is
    computed by `decide +kernel` over plain `Int`/`Nat` arithmetic (GMP-accelerated literals) and
    transported to `ℝ` by ONE soundness theorem per operation, proved once:

      * `Q`             -- an UNNORMALISED rational `n / (dm + 1)` (`n : ℤ`, `dm : ℕ`): the
                           denominator is positive by construction, so no positivity bookkeeping;
                           `val` is its real value, `frac n d` the rational `n / d` (`d ≥ 1`);
      * `add sub mul neg qabs npow div sumQ` -- the operations, `val_*` their homomorphism laws;
      * `le lt`         -- the Boolean comparisons, `le_sound`, `lt_sound`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/


namespace Arb4

/-- A rational `n / (dm + 1)`, NOT normalised (numerator in `ℤ`, denominator minus one in `ℕ`). -/
structure Q where
  n : ℤ
  dm : ℕ

namespace Q

/-- The real value `n / (dm + 1)`. -/
noncomputable def val (a : Q) : ℝ := (a.n : ℝ) / ((a.dm : ℝ) + 1)

/-- The rational `n / d` (for `d ≥ 1`). -/
def frac (n : ℤ) (d : ℕ) : Q := ⟨n, d - 1⟩

/-- `m / 1`. -/
def ofNat (m : ℕ) : Q := ⟨(m : ℤ), 0⟩

/-- `m / 1`. -/
def ofInt (m : ℤ) : Q := ⟨m, 0⟩

def add (a b : Q) : Q := ⟨a.n * ((b.dm : ℤ) + 1) + b.n * ((a.dm : ℤ) + 1), a.dm * b.dm + a.dm + b.dm⟩

def sub (a b : Q) : Q := ⟨a.n * ((b.dm : ℤ) + 1) - b.n * ((a.dm : ℤ) + 1), a.dm * b.dm + a.dm + b.dm⟩

def mul (a b : Q) : Q := ⟨a.n * b.n, a.dm * b.dm + a.dm + b.dm⟩

def neg (a : Q) : Q := ⟨-a.n, a.dm⟩

/-- `|a|`. -/
def qabs (a : Q) : Q := ⟨(a.n.natAbs : ℤ), a.dm⟩

/-- `a ^ k`. -/
def npow (a : Q) : ℕ → Q
  | 0 => ⟨1, 0⟩
  | k + 1 => mul (npow a k) a

/-- `a / b` for a POSITIVE numerator of `b` (read through `Int.toNat`). -/
def div (a b : Q) : Q := ⟨a.n * ((b.dm : ℤ) + 1), (a.dm + 1) * b.n.toNat - 1⟩

/-- `Σ_{i < k} f i`. -/
def sumQ (f : ℕ → Q) : ℕ → Q
  | 0 => ⟨0, 0⟩
  | k + 1 => add (sumQ f k) (f k)

/-- `a ≤ b`, cross-multiplied. -/
def le (a b : Q) : Bool := decide (a.n * ((b.dm : ℤ) + 1) ≤ b.n * ((a.dm : ℤ) + 1))

/-- `a < b`, cross-multiplied. -/
def lt (a b : Q) : Bool := decide (a.n * ((b.dm : ℤ) + 1) < b.n * ((a.dm : ℤ) + 1))

/-! ## The value homomorphism -/





























/-! ## The comparisons -/











/-! ## Literal conversions (small proof terms for the generated certificates) -/











end Q

end Arb4


def ArdaRH65K_Turing121_Arb4_Q : Nat := 0


