-- Prove2me | Definitions.Def_ECDLPChallengeData
-- name    : ECDLPChallengeData
-- status  : Definition
-- author  : @Lucas
-- created : 2026-11-16T23:42:12.110568+00:00
-- url     : https://prove2.me/theorems/67bf77a2-964b-46df-87ab-c5b256c9b5ea
-- title:
--   The FrontierMath ECDLP challenge instance
-- statement:
--   This definition fixes the public data of Epoch AI's FrontierMath open problem *The Elliptic-Curve Discrete Logarithm Problem*. It records the 256-bit prime modulus $p$, the curve coefficients $a, b$, the curve $E/\mathbb{F}_p : y^2 = x^3 + ax + b$ in short Weierstrass form, the base point $P = (x_P, y_P)$ and target point $Q = (x_Q, y_Q)$ in $E(\mathbb{F}_p)$, the 254-bit prime subgroup order $n$, and the cofactor $h = 5$ with $\#E(\mathbb{F}_p) = hn$. The benchmark's secret is the integer $x$ with $1 \le x < n$ such that $Q = xP$; only the public data are defined here.
--
--   **Formalization Note.** Points are Mathlib's `WeierstrassCurve.Affine.Point`, whose `some` constructor bundles a proof that the coordinates satisfy the Weierstrass equation and are nonsingular; these proofs are discharged by kernel evaluation (`decide`) of the concrete modular arithmetic. The primality of $p$ and $n$, the order of $P$, and the point count are not assumed here; they are stated as separate theorems.
-- source:
--   Epoch AI, FrontierMath: Open Problems — The Elliptic-Curve Discrete Logarithm Problem (ECDLP), https://epoch.ai/frontiermath/open-problems/elliptic-curve-discrete-logarithm — public challenge data (p, a, b, P, Q, n, h) and Task section.

import Mathlib

set_option autoImplicit false

namespace ECDLP

/-- The 256-bit prime modulus of the FrontierMath ECDLP challenge. -/
def p : ℕ := 92031864238688105485400538143121826382268912998421731683072033206257804487869

/-- The coefficient `a` of the challenge curve `y² = x³ + ax + b`, as a natural number. -/
def a : ℕ := 66780434313013275323552928748270304481793221171615836760742707201070562072251

/-- The coefficient `b` of the challenge curve, as a natural number. -/
def b : ℕ := 49926646401131159709065076432340744650532242327390476058390067276099410301761

/-- The prime order of the challenge base point `P`. -/
def n : ℕ := 18406372847737621097080107628624365276513063062857122317960690589425712086189

/-- The cofactor: `#E(F_p) = h * n`. -/
def h : ℕ := 5

/-- The challenge curve `E/F_p : y² = x³ + ax + b` in short Weierstrass form. -/
def E : WeierstrassCurve (ZMod p) :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := (a : ZMod p), a₆ := (b : ZMod p) }

/-- The x-coordinate of the challenge base point `P`. -/
def xP : ZMod p := 38644201185363417798191368696978811687737990190927559170532558153854800741642

/-- The y-coordinate of the challenge base point `P`. -/
def yP : ZMod p := 44805905068903897561820523795034068749084951450263356538447620424400005028012

/-- The x-coordinate of the challenge target point `Q`. -/
def xQ : ZMod p := 54096648540016620506320945354369315155659910460053503439381018376158456438152

/-- The y-coordinate of the challenge target point `Q`. -/
def yQ : ZMod p := 23176800742290374932252879903926227937053123957837615098744936554616726258932

/-- The base point coordinates satisfy the curve equation and are nonsingular. -/
theorem nonsingular_P : E.toAffine.Nonsingular xP yP := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
  exact ⟨by decide, Or.inr (by decide)⟩

/-- The target point coordinates satisfy the curve equation and are nonsingular. -/
theorem nonsingular_Q : E.toAffine.Nonsingular xQ yQ := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
  exact ⟨by decide, Or.inr (by decide)⟩

/-- The challenge base point, asserted by the benchmark to have prime order `n`. -/
def P : E.toAffine.Point := .some _ _ nonsingular_P

/-- The challenge target point `Q = xP` for the secret scalar `x`. -/
def Q : E.toAffine.Point := .some _ _ nonsingular_Q

end ECDLP


