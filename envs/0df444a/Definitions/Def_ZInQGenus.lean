-- Prove2me | Definitions.Def_ZInQGenus
-- name    : ZInQGenus
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T20:11:05.164929+00:00
-- url     : https://prove2.me/theorems/c5ee3dc8-7cd0-40be-b4e9-1c7db8493a4f
-- title:
--   Genus class numbers and the genus sum $T_{5b}(d)$
-- statement:
--   This bundle defines TYZ's genus class number and the genus sum of row 5b. For $n\ne 0$, $\mathbb{Q}(\sqrt{-n})$ is represented as Mathlib's quadratic algebra, and $g(n)=\#\bigl(2\,\mathrm{Cl}(\mathbb{Q}(\sqrt{-n}))\bigr)$ is the order of the subgroup of squares of the class group of its ring of integers. For a set $B$ of prime factors of $d$, $d_B=\prod_{p\in B}p$. A set partition of the primes of $d$ is admissible for row 5b when exactly one block has $d_B\equiv 7\pmod 8$, exactly one has $d_B\equiv 3\pmod 8$, and every block is $\equiv 7,3,$ or $1\pmod 8$. The genus sum $T_{5b}(d)\in\mathbb{Z}/2\mathbb{Z}$ sums $\prod_{B} g(d_B)$ over the admissible partitions.
-- source:
--   https://github.com/elliotglazer/diophantine-z-q/blob/964d7dd71f253091dbc5eac793b78cc56d1fcc73/ZInQKernel/RouteK/Rank5b/Sec3/RedeiStatement.lean#L24-L62

import Mathlib
import Mathlib.Algebra.QuadraticAlgebra.Basic

noncomputable section

open NumberField

namespace ZInQ.RouteK.Rank5b

/-- The field Q(sqrt(-n)), as Mathlib's quadratic algebra. -/
abbrev QNeg (n : ℕ) : Type := QuadraticAlgebra ℚ (-(n : ℚ)) 0

/-- No rational r satisfies r^2 = -n (for n != 0); this is the Fact the
QuadraticAlgebra field instance requires at this Mathlib pin. -/
instance QNeg.factNoRoot (n : ℕ) [NeZero n] : Fact (∀ r : ℚ, r ^ 2 ≠ -(n : ℚ) + 0 * r) := by
  refine ⟨fun r hr => ?_⟩
  have h0 : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [zero_mul, add_zero] at hr
  nlinarith [sq_nonneg r]

instance QNeg.numberField (n : ℕ) [NeZero n] : NumberField (QNeg n) where

/-- d_B = product of the primes in B. -/
def dProd {d : ℕ} (B : Finset d.primeFactors) : ℕ := ∏ p ∈ B, (p : ℕ)

instance neZero_dProd {d : ℕ} (B : Finset d.primeFactors) : NeZero (dProd B) :=
  ⟨Finset.prod_ne_zero_iff.mpr fun p _ => (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩

/-- TYZ's genus class number g(n) = #(2 Cl(Q(sqrt(-n)))). -/
def gCl (n : ℕ) [NeZero n] : ℕ :=
  Nat.card (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* ClassGroup (𝓞 (QNeg n))).range

/-- Admissibility for row 5b: one block = 7, one block = 3, all blocks 7, 3 or 1 mod 8. -/
def Admissible5bNat (d : ℕ) (P : Finpartition (Finset.univ : Finset d.primeFactors)) : Prop :=
  (P.parts.filter fun B => dProd B % 8 = 7).card = 1 ∧
  (P.parts.filter fun B => dProd B % 8 = 3).card = 1 ∧
  ∀ B ∈ P.parts, dProd B % 8 = 7 ∨ dProd B % 8 = 3 ∨ dProd B % 8 = 1

instance (d : ℕ) (P : Finpartition (Finset.univ : Finset d.primeFactors)) :
    Decidable (Admissible5bNat d P) := by
  unfold Admissible5bNat; infer_instance

/-- The genus sum of row 5b with TYZ's class-number g. -/
def T5bCl (d : ℕ) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset d.primeFactors),
    if Admissible5bNat d P then ∏ B ∈ P.parts, ((gCl (dProd B) : ℕ) : ZMod 2) else 0

end ZInQ.RouteK.Rank5b


