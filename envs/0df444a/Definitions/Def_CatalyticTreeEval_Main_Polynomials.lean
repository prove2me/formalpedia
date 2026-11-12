-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_Polynomials
-- name    : CatalyticTreeEval_Main_Polynomials
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:04.606203+00:00
-- url     : https://prove2.me/theorems/26ab8c84-d5d6-4dc1-8c42-c49942815f8c
-- title:
--   Finite polynomial matching systems and sparse printing interfaces
-- statement:
--   Polynomials in $H$ variables over $\mathbb Z/m\mathbb Z$ are actual finite multivariate polynomials. A sparse presentation lists distinct exponent vectors with coefficients, whose monomial sum equals the polynomial; zero coefficients may be printed. Multilinearity bounds every variable exponent by one, and symmetry is invariance under every permutation of the variables.
--
--   A polynomial matching family has points $x_i$ and polynomials $f_i$ with
--
--   $$f_i(x_i)=0,\qquad i\ne j\Longrightarrow f_j(x_i)\in S_0,\qquad 0\notin S_0.$$
--
--   The charged family printer outputs both the polynomial and its point. A separate charged printer enumerates a finite list of distinct monomials containing all supports. Exponent vectors are serialized in variable order. For Boolean inputs the Hamming weight is the sum of Boolean digits as natural numbers. The prime-power parameter is $\delta=\max_i p_i^{e_i}$; the dimension count is $\sum_{j<\delta}\binom Hj$.
--
--   A parameter-indexed polynomial system packages these algebraic data and a positive workspace scale, without assuming any construction theorem. The support and enumeration interfaces make the conversion theorem meaningful for subsequent uniform computations.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Definition B.3; Lemmas B.4–B.5, printed p. 37 (PDF p. 39); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Matching

set_option autoImplicit false

namespace CatalyticTreeEval.Main

abbrev Poly (m H : ℕ) := MvPolynomial (Fin H) (ZMod m)
abbrev Monomial (H : ℕ) := Fin H →₀ ℕ

def monomialCode {H : ℕ} (v : Monomial H) : List Bool :=
  natsCode ((List.finRange H).map v)

/-- A finite, nonduplicating, sparse polynomial presentation; zero coefficients may be printed.
The sum, rather than an assigned name, specifies its mathematical meaning. -/
def Represents {m H : ℕ} (code : List (Monomial H × ZMod m)) (f : Poly m H) : Prop :=
  (code.map Prod.fst).Nodup ∧ f = (code.map fun z => MvPolynomial.monomial z.1 z.2).sum

def polynomialCode {m H : ℕ} (code : List (Monomial H × ZMod m)) : List Bool :=
  natCode code.length ++ code.flatMap fun z =>
    monomialCode z.1 ++ bits (Nat.log 2 (m - 1) + 1) z.2.val

def PolyPrint {m H : ℕ} (M : Machine) (input : List Bool) (f : Poly m H) (s : ℝ) : Prop :=
  ∃ code, Represents code f ∧ Prints M input (polynomialCode code) s

def Multilinear {m H : ℕ} (f : Poly m H) : Prop :=
  ∀ v ∈ f.support, ∀ i, v i ≤ 1

def Symmetric {m H : ℕ} (f : Poly m H) : Prop :=
  ∀ σ : Equiv.Perm (Fin H), MvPolynomial.rename σ f = f

def weight {H : ℕ} (x : Fin H → Bool) : ℕ := ∑ i, (x i).toNat

def boolPoint {m H : ℕ} (x : Fin H → Bool) : Vec m H := fun i => ((x i).toNat : ZMod m)

def PolyMatching {m H N : ℕ} (S₀ : Set (ZMod m))
    (f : Fin N → Poly m H) (x : Fin N → Vec m H) : Prop :=
  0 ∉ S₀ ∧ (∀ i, MvPolynomial.eval (x i) (f i) = 0) ∧
    ∀ i j, i ≠ j → MvPolynomial.eval (x i) (f j) ∈ S₀

def PolyFamilyAccess {m H N : ℕ} (M : Machine) (params : List Bool)
    (f : Fin N → Poly m H) (x : Fin N → Vec m H) (s : ℝ) : Prop :=
  ∀ i, ∃ code, Represents code (f i) ∧
    Prints M (listCode params ++ natCode i.val) (polynomialCode code ++ vecCode (x i)) s

/-- Enumeration with no duplicates, so its length is exactly the dimension in B.4. -/
def MonomialAccess {H : ℕ} (M : Machine) (params : List Bool)
    (ms : List (Monomial H)) (s : ℝ) : Prop :=
  ms.Nodup ∧ Prints M (listCode params) (natCode ms.length ++ ms.flatMap monomialCode) s

def delta {t : ℕ} (p e : Fin t → ℕ) : ℕ :=
  (Finset.univ.image fun i => p i ^ e i).sup id

def binomialDimension (H δ : ℕ) : ℕ := ∑ j ∈ Finset.range δ, H.choose j

end CatalyticTreeEval.Main

namespace CatalyticTreeEval.Main

/-- A parameter-indexed polynomial system, with actual finite polynomials and monomials. -/
structure PolySystem where
  m : ℕ
  H : ℕ
  N : ℕ
  s : ℝ
  S₀ : Set (ZMod m)
  f : Fin N → Poly m H
  x : Fin N → Vec m H
  monomials : List (Monomial H)

def PolySystem.params (a : List Bool) (P : PolySystem) : List Bool :=
  listCode a ++ natsCode [P.m,P.H,P.N]

def PolySystem.valid (P : PolySystem) : Prop :=
  1 < P.m ∧ 0 < P.s ∧ PolyMatching P.S₀ P.f P.x ∧
    (∀ i, ∀ v ∈ (P.f i).support, v ∈ P.monomials)

end CatalyticTreeEval.Main


