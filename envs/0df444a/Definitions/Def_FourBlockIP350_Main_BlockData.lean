-- Prove2me | Definitions.Def_FourBlockIP350_Main_BlockData
-- name    : FourBlockIP350_Main_BlockData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:45.410312+00:00
-- url     : https://prove2.me/theorems/8ddc1593-b8e7-4b1c-88f0-d3b3733129ce
-- title:
--   Nonuniform 4-block and generalized n-fold input data
-- statement:
--   Let $k$ be the common block dimension and $n$ the number of local bricks. Each generalized n-fold matrix $E$ consists of its linking blocks $B^{(i)}$ and diagonal blocks $D^{(i)}$. A 4-block instance additionally has the stacked global-column matrix $Z$, right-hand side, costs and bounds, with equations
--   $$Zx+Ey=b.$$
--   The entry bound $\bar\Delta$ constrains only $B^{(i)}$ and $D^{(i)}$, independently across bricks. $Z$ is unrestricted. FiniteBounds allows inconsistent intervals for the finite solver; GoodBox additionally means every interval is nonempty for defining the finite penalized value function. The n-fold optimization input has finite integral endpoints, which may be inconsistent.
--
--   **Formalization Note** A row is indexed by a global/local tag and a coordinate. The global tag is `none`; local tags are `some i`. This is a reindexing of the stacked matrices and imposes no identical-block condition.
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 2–3, (4-Block ILP), matrix display on p. 3; §3 finite-box convention

import Mathlib
import Definitions.Def_FourBlockIP350_Main_IntegerPrograms

namespace FourBlockIP350.Main

open scoped BigOperators

abbrev BlockRow (k n : ℕ) := Option (Fin n) × Fin k
abbrev LocalCol (k n : ℕ) := Fin n × Fin k
abbrev BlockCol (k n : ℕ) := Option (Fin n) × Fin k

/-- No family of blocks is required to be identical. Zero padding permits rectangular blocks. -/
structure NFold (k n : ℕ) where
  B : Fin n → Matrix (Fin k) (Fin k) ℤ
  D : Fin n → Matrix (Fin k) (Fin k) ℤ

def NFold.matrix {k n : ℕ} (Q : NFold k n) : Matrix (BlockRow k n) (LocalCol k n) ℤ :=
  fun r j => match r.1 with
  | none => Q.B j.1 r.2 j.2
  | some i => if i = j.1 then Q.D i r.2 j.2 else 0

def NFold.Bounded {k n : ℕ} (Q : NFold k n) (Δ : ℕ) : Prop :=
  ∀ i a b, |Q.B i a b| ≤ (Δ : ℤ) ∧ |Q.D i a b| ≤ (Δ : ℤ)

structure FourBlock (k n : ℕ) where
  localPart : NFold k n
  Z : Matrix (BlockRow k n) (Fin k) ℤ
  b : BlockRow k n → ℤ
  c : BlockCol k n → ℤ
  lower : BlockCol k n → Option ℤ
  upper : BlockCol k n → Option ℤ

def FourBlock.program {k n : ℕ} (I : FourBlock k n) : IntegerProgram (BlockRow k n) (BlockCol k n) where
  matrix := fun r j => match j.1 with
    | none => I.Z r j.2
    | some i => I.localPart.matrix r (i, j.2)
  rhs := I.b
  cost := I.c
  lower := I.lower
  upper := I.upper

def joinPoint {k n : ℕ} (x : Fin k → ℤ) (y : LocalCol k n → ℤ) : BlockCol k n → ℤ :=
  fun j => match j.1 with | none => x j.2 | some i => y (i, j.2)

/-- Finite endpoints only, allowing empty intervals; used for the finite solver. -/
def FiniteBounds {k n : ℕ} (I : FourBlock k n) : Prop :=
  (∀ j, (I.lower j).isSome = true) ∧ (∀ j, (I.upper j).isSome = true)

def lo {k n : ℕ} (I : FourBlock k n) (j : BlockCol k n) : ℤ := (I.lower j).getD 0

def hi {k n : ℕ} (I : FourBlock k n) (j : BlockCol k n) : ℤ := (I.upper j).getD 0

/-- Standing assumption for the value function, after rejecting empty intervals. -/
def GoodBox {k n : ℕ} (I : FourBlock k n) : Prop :=
  FiniteBounds I ∧ ∀ j, lo I j ≤ hi I j

def LocalBox {k n : ℕ} (I : FourBlock k n) (y : LocalCol k n → ℤ) : Prop :=
  ∀ j, lo I (some j.1, j.2) ≤ y j ∧ y j ≤ hi I (some j.1, j.2)

def GlobalBox {k n : ℕ} (I : FourBlock k n) (x : Fin k → ℤ) : Prop :=
  ∀ j, lo I (none,j) ≤ x j ∧ x j ≤ hi I (none,j)

structure BoundedNFold (k n : ℕ) where
  blocks : NFold k n
  b : BlockRow k n → ℤ
  c : LocalCol k n → ℤ
  lower : LocalCol k n → ℤ
  upper : LocalCol k n → ℤ

def BoundedNFold.program {k n : ℕ} (I : BoundedNFold k n) : IntegerProgram (BlockRow k n) (LocalCol k n) :=
  ⟨I.blocks.matrix, I.b, I.c, fun j => some (I.lower j), fun j => some (I.upper j)⟩

end FourBlockIP350.Main


