-- Prove2me | Definitions.Def_BarelyTestable_LowerBound_Construction
-- name    : BarelyTestable_LowerBound_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:23.738266+00:00
-- url     : https://prove2.me/theorems/84f71d4a-4573-4436-a87c-9cf7f06aa2b5
-- title:
--   The exact four-slice hard function and independent sampling space
-- statement:
--   Fix a positive integer $m$ and let $d=2m^2+2$. Each control half has coordinates $(i,j)\in[m]^2$. Write $\pi(X)$ for its vector of block parities. Labels $\phi_A(X),\phi_B(Y)\in\{0,1\}^m$ are independent uniform values for every subset. Ordered addresses are $\alpha(X)=(\pi(X),\phi_A(X))$ and $\beta(Y)=(\phi_B(Y),\pi(Y))$; a center satisfies equality of these addresses.
--
--   A single independent table has entries $\theta(z)=k/2^d$, with $0\le k<2^d$. It is shared by both addresses. Define $F_A=-4\sum_i(|X\cap A_i|+|Y|)^2$ and $F_B=-4\sum_i(|Y\cap B_i|+|X|)^2$, with $H_A=|\pi(X)\mathbin\triangle\phi_B(Y)|$ and $H_B=|\phi_A(X)\mathbin\triangle\pi(Y)|$. For $s=|X|+|Y|$ and $\sigma=\pm1$,
--
--   $$\begin{aligned}F^{(\sigma)}_{00}&=F_A,\\F^{(\sigma)}_{01}&=F_A-m^4s+\theta(\beta(Y))+\sigma/2^d+H_A,\\F^{(\sigma)}_{10}&=F_B-m^4s,\\F^{(\sigma)}_{11}&=F_B-2m^4s+\theta(\alpha(X))-H_B.\end{aligned}$$
--
--   The full finite sampling type consists of both entire label maps and the entire table. Uniform sampling of this type is exactly the independent product law. Its image under the displayed function is the YES or NO distribution. A coordinate equivalence gives the same function on $\operatorname{Fin}(d)$. The finite grid concerns these hard instances only; all testers and all repairs still range over arbitrary real functions.
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), §3.1 construction, p. 12–13 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Cube

set_option autoImplicit false

namespace BarelyTestable.LowerBound

abbrev Half (m : ℕ) := Fin m × Fin m
abbrev HalfSet (m : ℕ) := Cube (Half m)
abbrev Bits (m : ℕ) := Fin m → Bool
abbrev Address (m : ℕ) := Bits m × Bits m
abbrev LabelMap (m : ℕ) := HalfSet m → Bits m
abbrev Coord (m : ℕ) := Bool ⊕ (Half m ⊕ Half m)
def dimension (m : ℕ) : ℕ := 2 * m ^ 2 + 2
abbrev Table (m : ℕ) := Address m → Fin (2 ^ (dimension m))
abbrev Sample (m : ℕ) := LabelMap m × LabelMap m × Table m

def actionA {m : ℕ} : Coord m := Sum.inl false
def actionB {m : ℕ} : Coord m := Sum.inl true

def block {m : ℕ} (X : HalfSet m) (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun j => (i,j) ∈ X)

def parity {m : ℕ} (X : HalfSet m) : Bits m :=
  fun i => decide ((block X i).card % 2 = 1)

def alpha {m : ℕ} (φA : LabelMap m) (X : HalfSet m) : Address m := (parity X, φA X)
def beta {m : ℕ} (φB : LabelMap m) (Y : HalfSet m) : Address m := (φB Y, parity Y)
def Center {m : ℕ} (φA φB : LabelMap m) (X Y : HalfSet m) : Prop := alpha φA X = beta φB Y

noncomputable def theta {m : ℕ} (t : Table m) (z : Address m) : ℝ :=
  ((t z).val : ℝ) / 2 ^ dimension m

noncomputable def baseA {m : ℕ} (X Y : HalfSet m) : ℝ :=
  -4 * ∑ i : Fin m, (((block X i).card : ℝ) + Y.card) ^ 2
noncomputable def baseB {m : ℕ} (X Y : HalfSet m) : ℝ := baseA Y X

def bitDistance {m : ℕ} (v w : Bits m) : ℕ := (Finset.univ.filter (fun i => v i ≠ w i)).card

def xPart {m : ℕ} (S : Cube (Coord m)) : HalfSet m :=
  Finset.univ.filter (fun x => Sum.inr (Sum.inl x) ∈ S)
def yPart {m : ℕ} (S : Cube (Coord m)) : HalfSet m :=
  Finset.univ.filter (fun y => Sum.inr (Sum.inr y) ∈ S)

/-- Four exact slices; true sign is YES, false sign is NO. -/
noncomputable def slice {m : ℕ} (r : Sample m) (sign : Bool) (X Y : HalfSet m) (a b : Bool) : ℝ :=
  let s : ℝ := X.card + Y.card
  let σ : ℝ := if sign then 1 else -1
  match a, b with
  | false, false => baseA X Y
  | false, true => baseA X Y - (m : ℝ)^4 * s + theta r.2.2 (beta r.2.1 Y) +
      σ / 2 ^ dimension m + bitDistance (parity X) (r.2.1 Y)
  | true, false => baseB X Y - (m : ℝ)^4 * s
  | true, true => baseB X Y - 2 * (m : ℝ)^4 * s + theta r.2.2 (alpha r.1 X) -
      bitDistance (r.1 X) (parity Y)

noncomputable def hard {m : ℕ} (r : Sample m) (sign : Bool) : Oracle (Coord m) :=
  fun S => slice r sign (xPart S) (yPart S) (decide (actionA ∈ S)) (decide (actionB ∈ S))

/-- Coordinate renaming only: cardinality is 2m²+2. -/
noncomputable def coordEquiv (m : ℕ) : Coord m ≃ Fin (dimension m) :=
  Fintype.equivFinOfCardEq (by simp [Coord, Half, dimension]; ring)

noncomputable def hardOnFin {m : ℕ} (r : Sample m) (sign : Bool) : Oracle (Fin (dimension m)) :=
  fun S => hard r sign (S.image (coordEquiv m).symm)

end BarelyTestable.LowerBound


