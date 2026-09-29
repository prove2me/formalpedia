-- Prove2me | Definitions.Def_NetPairing_Basic
-- name    : NetPairing_Basic
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/f822e04e-7cda-5668-8d0d-61b29053b107
-- title:
--   Elliptic-net Weil pairing on p-torsion: definitions
-- statement:
--   Throughout, $W$ is an affine Weierstrass curve over a field $F$ and points are elements of `W.Point`, the type with a point at infinity `0` and affine points `some x y h`. The helper `xOrZero` returns the $x$-coordinate of an affine point and $0$ at infinity, and `netW20` returns $y - \mathrm{negY}(x,y)$ at an affine point and $0$ at infinity, where $\mathrm{negY}$ is the $y$-coordinate of the negative; these are the rank-one and rank-two seed values $W(1,0)$-type data. Four further seeds are defined for a pair $P,Q$: `netW21` $= x(P) - x(P+Q)$, `netW12` $= x(Q) - x(P+Q)$, `netW1m1` $= x(Q) - x(P)$ and `netW2m1` $= (x(Q)-x(P))^2\,(x(P-Q)-x(P))$, all read through `xOrZero`. The column `netCol A B : \mathbb{N} \to F` is defined by $W(0)=W(1)=1$ and the recursion $W(m+2) = W(m+1)^2\,(x(A) - x((m+1)A + B))/W(m)$, field division making the definition total. The rank-one values are `netPsi P n` $= (\mathrm{pre}\Psi_n)(x(P))$ times `netW20` of $P$ when $n$ is even and times $1$ otherwise, with $\mathrm{pre}\Psi$ Mathlib's division polynomial. Then `netTau p P Q` $=$ `netCol P Q (p+1)` $/$ `netPsi P (p+1)`, and `netPairing p P Q` is the ratio `netTau p P Q / netTau p Q P` when $P \neq 0$ and $Q$ is not an integer multiple of $P$, and $1$ otherwise; in particular it is $1$ whenever either argument vanishes.
--
--   Three predicates on $W$ and a natural number $p$ are defined, not proved: `NetShearLaw`, asserting $e_p(P,Q+P) = e_p(P,Q)$; `NetScaleLaw`, asserting $e_p(P,a\cdot Q) = e_p(P,Q)^a$ for all $a \in \mathbb{N}$ — both for all $P,Q$ killed by $p$ with $P \neq 0$ and $Q$ outside the integer multiples of $P$ — and `NetPairingNondegenerate`, asserting the existence of $P,Q$ killed by $p$ with $e_p(P,Q) \neq 1$.
--
--   **Relation to Mathlib.** Built on Mathlib's `WeierstrassCurve.Affine.Point`, `negY` and the division polynomials `preΨ`; the elliptic-net seed values, the column recursion, the $\tau$-ratio and the resulting pairing, together with the shear, scale and nondegeneracy predicates, are the project's own notions.
--
--   **Where it is used.** The pairing defined here is the elliptic-net form of the Weil pairing on $p$-torsion, the input used to show that the determinant of the mod-$p$ Galois representation attached to an elliptic curve is the cyclotomic character, so that $\det\bar\rho_p(\mathrm{Frob}_\ell) \equiv \ell \pmod p$; this feeds the level-lowering side of the argument for the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NetPairing_Basic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve.Affine.Point

universe u

section XCoord

variable {R : Type u} [CommRing R] {W : WeierstrassCurve.Affine R}

def xOrZero : W.Point → R
  | .zero => 0
  | .some x _ _ => x

@[simp] lemma xOrZero_zero : (0 : W.Point).xOrZero = 0 := rfl

@[simp] lemma xOrZero_some {x y : R} (h : W.Nonsingular x y) :
    (Point.some x y h).xOrZero = x := rfl

end XCoord

variable {F : Type u} [Field F] {W : WeierstrassCurve.Affine F}

def netW20 : W.Point → F
  | .zero => 0
  | .some x y _ => y - W.negY x y

@[simp] lemma netW20_zero : (0 : W.Point).netW20 = 0 := rfl

@[simp] lemma netW20_some {x y : F} (h : W.Nonsingular x y) :
    (Point.some x y h).netW20 = y - W.negY x y := rfl

variable [DecidableEq F]

variable (P Q : W.Point)

noncomputable def netW21 : F := P.xOrZero - (P + Q).xOrZero

noncomputable def netW12 : F := Q.xOrZero - (P + Q).xOrZero

noncomputable def netW1m1 : F := Q.xOrZero - P.xOrZero

noncomputable def netW2m1 : F := (Q.xOrZero - P.xOrZero) ^ 2 * ((P - Q).xOrZero - P.xOrZero)

variable {P Q}

noncomputable def netCol (A B : W.Point) : ℕ → F
  | 0 => 1
  | 1 => 1
  | m + 2 =>
      netCol A B (m + 1) ^ 2 * (A.xOrZero - ((m + 1) • A + B).xOrZero) / netCol A B m

@[simp] lemma netCol_zero : netCol P Q 0 = 1 := rfl
@[simp] lemma netCol_one : netCol P Q 1 = 1 := rfl

noncomputable def netPsi (P : W.Point) (n : ℕ) : F :=
  (W.preΨ (n : ℤ)).eval P.xOrZero * (if Even n then P.netW20 else 1)

noncomputable def netTau (p : ℕ) (P Q : W.Point) : F :=
  netCol P Q (p + 1) / P.netPsi (p + 1)

open scoped Classical in

noncomputable def netPairing (p : ℕ) (P Q : W.Point) : F :=
  if P ≠ 0 ∧ ∀ k : ℤ, Q ≠ k • P then netTau p P Q / netTau p Q P else 1

@[simp] lemma netPairing_zero_left (p : ℕ) (Q : W.Point) :
    netPairing p (0 : W.Point) Q = 1 := by
  unfold netPairing; rw [if_neg]; simp

@[simp] lemma netPairing_zero_right (p : ℕ) (P : W.Point) :
    netPairing p P (0 : W.Point) = 1 := by
  unfold netPairing
  by_cases hP : P = 0
  · rw [if_neg]; simp [hP]
  · rw [if_neg]; rintro ⟨_, h⟩; exact h 0 (by rw [zero_zsmul])

variable (W) in

def NetShearLaw (p : ℕ) : Prop :=
  ∀ ⦃P Q : W.Point⦄, p • P = 0 → p • Q = 0 → P ≠ 0 → (∀ k : ℤ, Q ≠ k • P) →
    netPairing p P (Q + P) = netPairing p P Q

variable (W) in

def NetScaleLaw (p : ℕ) : Prop :=
  ∀ ⦃P Q : W.Point⦄, p • P = 0 → p • Q = 0 → P ≠ 0 → (∀ k : ℤ, Q ≠ k • P) →
    ∀ a : ℕ, netPairing p P (a • Q) = netPairing p P Q ^ a

variable (W) in

def NetPairingNondegenerate (p : ℕ) : Prop :=
  ∃ P Q : W.Point, p • P = 0 ∧ p • Q = 0 ∧ netPairing p P Q ≠ 1

end WeierstrassCurve.Affine.Point


