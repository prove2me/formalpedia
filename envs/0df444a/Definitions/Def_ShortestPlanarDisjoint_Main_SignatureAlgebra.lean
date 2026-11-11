-- Prove2me | Definitions.Def_ShortestPlanarDisjoint_Main_SignatureAlgebra
-- name    : ShortestPlanarDisjoint_Main_SignatureAlgebra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:44.680357+00:00
-- url     : https://prove2.me/theorems/d5f05971-198d-45a6-8493-e223631d3e12
-- title:
--   Characteristic-two Laurent matrices and component signatures
-- statement:
--   Work over $\mathbb F_2$. Independent commuting formal variables label every
--   terminal, every seam side and every seam. Finite integer exponent vectors give a
--   Laurent polynomial ring; this ambient ring also permits negative terminal and
--   side exponents, though the expressions defined here only use nonnegative powers
--   of those variables. Negative powers occur only for the invertible seam variables.
--
--   For seam sides $a,b$, put $v_a=(u_a,1)^T$, $v_b=(u_b,1)^T$, $e_1=(1,0)^T$ and
--
--   $$T_{ab}=\lambda v_av_b^TJ+\lambda^{-1}e_1e_1^TJ.$$
--
--   Reversing a crossing interchanges $a,b$. A component's transport is the ordered
--   product of its actual crossing matrices, with empty product $I_2$. A path has
--   signature $[v(t_i),T(P)v(t_j)]$ and a closed component has signature
--   $\operatorname{tr}T(C)$. Their product is the curve signature; doubled edges have
--   factor one. No orientation-invariance, return-removal or leading-term theorem is
--   assumed. Component words are algebraic inputs only; extracting them from graph
--   configurations and glued states is not supplied by this definition.
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Sections 2 and 5.2, equations (4)–(5), p. 18 (PDF p. 20)

import Definitions.Def_ShortestPlanarDisjoint_Main_PortContributions

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main

noncomputable section

/-- Seam variables first; terminal and side-variable order is supplied by the cut.
All variables commute. Integer exponent vectors provide genuine Laurent monomials. -/
abbrev SignatureVariable (k r : ℕ) := Fin r ⊕ (Fin (2 * k) ⊕ (Fin r × Bool))

abbrev SignatureRing (k r : ℕ) :=
  AddMonoidAlgebra (ZMod 2) (SignatureVariable k r → ℤ)

/-- A formal Laurent monomial with coefficient one. -/
def signatureMonomial {k r : ℕ} (e : SignatureVariable k r → ℤ) : SignatureRing k r :=
  AddMonoidAlgebra.single e 1

def signatureVariable {k r : ℕ} (x : SignatureVariable k r) (exponent : ℤ := 1) :
    SignatureRing k r :=
  signatureMonomial (Function.update (fun _ => 0) x exponent)

def seamVariable {k r : ℕ} (s : Fin r) (exponent : ℤ := 1) : SignatureRing k r :=
  signatureVariable (.inl s) exponent

def terminalVariable {k r : ℕ} (i : Fin (2 * k)) : SignatureRing k r :=
  signatureVariable (.inr (.inl i))

def sideVariable {k r : ℕ} (s : Fin r) (side : Bool) : SignatureRing k r :=
  signatureVariable (.inr (.inr (s, side)))

def outerProduct {R : Type*} [CommRing R] (v w : Vec2 R) : Mat2 R := fun i j => v i * w j

/-- Exactly equation (4). false means a_s→b_s; true means b_s→a_s.
The negative seam power is a formal monomial, not division in a finite field. -/
def crossingMatrix {k r : ℕ} (s : Fin r) (reverse : Bool) : Mat2 (SignatureRing k r) :=
  let a : Vec2 (SignatureRing k r) := terminalVector (sideVariable s reverse)
  let b : Vec2 (SignatureRing k r) := terminalVector (sideVariable s (!reverse))
  let e₁ : Vec2 (SignatureRing k r) := ![1, 0]
  fun i j => seamVariable s * (outerProduct a b * switchMatrix (SignatureRing k r)) i j +
    seamVariable s (-1) * (outerProduct e₁ e₁ * switchMatrix (SignatureRing k r)) i j

/-- Actual ordered multiplication along a component; the matrices need not commute. -/
def crossingTransport {k r : ℕ} (crossings : List (Fin r × Bool)) : Mat2 (SignatureRing k r) :=
  transport (crossings.map fun c => crossingMatrix c.1 c.2)

/-- The terminal bracket for a component with the given ordered crossing list. -/
def pathSignature {k r : ℕ} (i j : Fin (2 * k)) (crossings : List (Fin r × Bool)) :
    SignatureRing k r :=
  bracket (terminalVector (terminalVariable i))
    ((crossingTransport crossings).mulVec (terminalVector (terminalVariable j)))

/-- In particular, an empty crossing list contributes tr I₂ in characteristic two. -/
def cycleSignature {k r : ℕ} (crossings : List (Fin r × Bool)) : SignatureRing k r :=
  Matrix.trace (crossingTransport crossings)

/-- Algebraic input to equation (5): ordered seam words of all components.
This is not a graph configuration or a disk state. Extraction of these words
from those objects remains separate mathematical work. -/
structure CurveWords (k r : ℕ) where
  paths : List (Fin (2 * k) × Fin (2 * k) × List (Fin r × Bool))
  cycles : List (List (Fin r × Bool))

/-- Equation (5); omitted doubled edges have factor one. -/
def curveSignature {k r : ℕ} (C : CurveWords k r) : SignatureRing k r :=
  (C.paths.map fun p => pathSignature p.1 p.2.1 p.2.2).prod *
    (C.cycles.map cycleSignature).prod

end
end ShortestPlanarDisjoint.Main


