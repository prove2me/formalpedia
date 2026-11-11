-- Prove2me | Definitions.Def_PolynomialPackingMM_IntegerRecursion_SelectedProduct
-- name    : PolynomialPackingMM_IntegerRecursion_SelectedProduct
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:28.175403+00:00
-- url     : https://prove2.me/theorems/3e3f14e5-d8fa-4294-9948-08ff25602f81
-- title:
--   Selected matrix-polynomial products, role exchanges, tensoring and effort
-- statement:
--   Let $I,J,K$ be arbitrary finite sets of exponent vectors of commuting monomials; matrix coefficients need not commute. For positive dimensions $p,q,r$, the selected product takes independent coefficient matrices $A_u\in F^{p\times q}$ and $B_v\in F^{q\times r}$ over any characteristic-zero field $F$, and returns, at every $w\in K$,
--
--   $$C_w=\sum_{u\in I,\ v\in J,\ u+v=w} A_uB_v.$$
--
--   The module defines Full with supports $[0,a),[0,b),[0,a+b-1)$ and its dual Mid with supports $[0,a),[1-(a+b-1),0],[1-b,0]$. Role permutations act on $(I,J,-K)$ and on matrix indices. Tensoring concatenates disjoint variable lists and multiplies matrix dimensions. Isomorphism means one simultaneous variable-coordinate permutation. The effort is $pqr\prod_k\min(a_k+b_k-1,a_k+h_k-1,b_k+h_k-1)$, with effort zero if any support is empty; compression is used only for positive source effort. The balanced shapes $T^d_{a,b}$ and $Q^d_{a,b}$ are constructed from these actual supports.
--
--   These shared objects provide the model used by all packing statements. **Formalization Note** Scalar entries use finite monomial/row/column keys, and exponent vectors are integer-valued. The empty variable list is additionally available as the internal tensor unit. Range extrema are evaluated only for nonempty supports; no optimum is substituted for effort.
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 8 (PDF 9), Definition 2.1; §2.1 equation (2), pp. 8–9; equation (4), p. 10; Definition 2.6, p. 11; isomorphism, p. 12; equation (7), p. 13; Lemma 4.1 definition, p. 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Mathlib

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

/-- Exponent vectors of commuting monomial variables. Matrix entries remain ordered. -/
abbrev Exponent (m : ℕ) := Fin m → ℤ

/-- Definition 2.1. Zero variables are allowed internally as the tensor unit. -/
structure Shape where
  numVars : ℕ
  left : Finset (Exponent numVars)
  right : Finset (Exponent numVars)
  output : Finset (Exponent numVars)

/-- Positive matrix dimensions; edge i is the matrix index absent from role i. -/
structure SelectedProduct where
  shape : Shape
  edge : Fin 3 → ℕ+

def SelectedProduct.p (P : SelectedProduct) : ℕ := P.edge 1

def SelectedProduct.q (P : SelectedProduct) : ℕ := P.edge 2

def SelectedProduct.r (P : SelectedProduct) : ℕ := P.edge 0

def product (S : Shape) (p q r : ℕ+) : SelectedProduct := ⟨S, ![r, p, q]⟩

noncomputable def negativeSupport {m : ℕ} (S : Finset (Exponent m)) : Finset (Exponent m) :=
  S.image (fun e => -e)

noncomputable def Shape.roles (P : Shape) (i : Fin 3) : Finset (Exponent P.numVars) :=
  ![P.left, P.right, negativeSupport P.output] i

/-- Role permutations act on (I,J,-K), with the resulting third support inverted. -/
noncomputable def Shape.exchange (P : Shape) (σ : Equiv.Perm (Fin 3)) : Shape :=
  ⟨P.numVars, P.roles (σ.symm 0), P.roles (σ.symm 1),
    negativeSupport (P.roles (σ.symm 2))⟩

noncomputable def SelectedProduct.exchange (P : SelectedProduct) (σ : Equiv.Perm (Fin 3)) :
    SelectedProduct := ⟨P.shape.exchange σ, fun i => P.edge (σ.symm i)⟩

def swap12 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

def swap23 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

def swap13 : Equiv.Perm (Fin 3) := Equiv.swap 0 2

noncomputable def full (a b : ℕ) : Shape :=
  ⟨1, (Finset.range a).image (fun (i : ℕ) (_ : Fin 1) => (i : ℤ)),
    (Finset.range b).image (fun (i : ℕ) (_ : Fin 1) => (i : ℤ)),
    (Finset.range (a + b - 1)).image (fun (i : ℕ) (_ : Fin 1) => (i : ℤ))⟩

/-- Equation (2): right exponents 1-s,...,0; output exponents 1-b,...,0. -/
noncomputable def mid (a b : ℕ) : Shape := (full a b).exchange swap23

/-- Disjoint variable lists are concatenated in this fixed order. -/
def appendExponent {m n : ℕ} (u : Exponent m) (v : Exponent n) : Exponent (m + n) :=
  Fin.addCases u v

noncomputable def tensorSupport {m n : ℕ} (I : Finset (Exponent m))
    (J : Finset (Exponent n)) : Finset (Exponent (m + n)) :=
  (I ×ˢ J).image (fun e => appendExponent e.1 e.2)

noncomputable def Shape.tensor (P Q : Shape) : Shape :=
  ⟨P.numVars + Q.numVars, tensorSupport P.left Q.left,
    tensorSupport P.right Q.right, tensorSupport P.output Q.output⟩

noncomputable def SelectedProduct.tensor (P Q : SelectedProduct) : SelectedProduct :=
  ⟨P.shape.tensor Q.shape, fun i => P.edge i * Q.edge i⟩

noncomputable def unitShape : Shape := ⟨0, {0}, {0}, {0}⟩

noncomputable def Shape.power (P : Shape) : ℕ → Shape
  | 0 => unitShape
  | d + 1 => (P.power d).tensor P

/-- Equation (7); the parameter d is never suppressed in Lean. -/
noncomputable def balanced (d a b : ℕ) : Shape := ((full a b).tensor (mid a b)).power d

noncomputable def roundShape (d a b : ℕ) : Shape :=
  ((balanced d a b).tensor ((balanced d a b).exchange swap12)).tensor
    ((balanced d a b).exchange swap13)

noncomputable def renameSupport {m n : ℕ} (π : Fin m ≃ Fin n)
    (I : Finset (Exponent m)) : Finset (Exponent n) := I.image (fun u j => u (π.symm j))

/-- Only one simultaneous coordinate permutation, not a general bilinear equivalence. -/
def Shape.Isomorphic (P Q : Shape) : Prop :=
  ∃ π : Fin P.numVars ≃ Fin Q.numVars,
    Q.left = renameSupport π P.left ∧ Q.right = renameSupport π P.right ∧
      Q.output = renameSupport π P.output

def SelectedProduct.Isomorphic (P Q : SelectedProduct) : Prop :=
  P.edge = Q.edge ∧ P.shape.Isomorphic Q.shape

noncomputable def rangeLength {m : ℕ} (I : Finset (Exponent m)) (k : Fin m) : ℕ :=
  if h : I.Nonempty then
    ((I.image (fun e => e k)).max' (h.image _) -
      (I.image (fun e => e k)).min' (h.image _) + 1).toNat else 0

/-- Equation (4), with the empty-support convention made explicit. -/
noncomputable def Shape.effort (P : Shape) : ℕ :=
  if P.left.Nonempty ∧ P.right.Nonempty ∧ P.output.Nonempty then
    ∏ k : Fin P.numVars,
      min (rangeLength P.left k + rangeLength P.right k - 1)
        (min (rangeLength P.left k + rangeLength P.output k - 1)
          (rangeLength P.right k + rangeLength P.output k - 1))
  else 0

noncomputable def SelectedProduct.effort (P : SelectedProduct) : ℕ :=
  P.p * P.q * P.r * P.shape.effort

/-- Keys give monomials and scalar row/column entries a common literal coordinate system. -/
abbrev Key := List ℤ × ℕ × ℕ

noncomputable def coefficientKeys {m : ℕ} (I : Finset (Exponent m)) (p q : ℕ) : Finset Key :=
  ((I ×ˢ Finset.range p) ×ˢ Finset.range q).image
    (fun x => (List.ofFn x.1.1, x.1.2, x.2))

noncomputable def SelectedProduct.leftKeys (P : SelectedProduct) : Finset Key :=
  coefficientKeys P.shape.left P.p P.q

noncomputable def SelectedProduct.rightKeys (P : SelectedProduct) : Finset Key :=
  coefficientKeys P.shape.right P.q P.r

noncomputable def SelectedProduct.outputKeys (P : SelectedProduct) : Finset Key :=
  coefficientKeys P.shape.output P.p P.r

abbrev Tasks := List SelectedProduct

abbrev LeftIndex (T : Tasks) := Σ i : Fin T.length, {k // k ∈ (T.get i).leftKeys}
abbrev RightIndex (T : Tasks) := Σ i : Fin T.length, {k // k ∈ (T.get i).rightKeys}
abbrev OutputIndex (T : Tasks) := Σ i : Fin T.length, {k // k ∈ (T.get i).outputKeys}

/-- Coefficient of the ordered monomial A_a B_b in selected output o. -/
def localCoefficient (o a b : Key) : ℚ :=
  if o.1 = List.zipWith (· + ·) a.1 b.1 ∧
    o.2.1 = a.2.1 ∧ a.2.2 = b.2.1 ∧ o.2.2 = b.2.2 then 1 else 0

/-- The block diagonal family of selected products; keys from different tasks never interact. -/
noncomputable def targetCoefficient (T : Tasks) (o : OutputIndex T) (a : LeftIndex T)
    (b : RightIndex T) : ℚ :=
  if o.1 = a.1 ∧ o.1 = b.1 then localCoefficient o.2.val a.2.val b.2.val else 0

/-- Evaluation over any characteristic-zero field, keeping A before B in every term. -/
noncomputable def selectedEvaluation {F : Type} [Field F] [CharZero F] (T : Tasks)
    (A : LeftIndex T → F) (B : RightIndex T → F) : OutputIndex T → F :=
  fun o => ∑ a, ∑ b, (targetCoefficient T o a b : F) * A a * B b

noncomputable def totalEffort (T : Tasks) : ℕ := (T.map SelectedProduct.effort).sum

/-- A rate is used only with the separately stated positive-source-effort condition. -/
noncomputable def compression (T S : Tasks) : ℚ := (totalEffort T : ℚ) / totalEffort S

noncomputable def exchangeTasks (T : Tasks) (σ : Equiv.Perm (Fin 3)) : Tasks :=
  T.map (fun P => P.exchange σ)

noncomputable def tensorTasks (T S : Tasks) : Tasks :=
  T.flatMap (fun P => S.map (fun Q => P.tensor Q))

noncomputable def copies (k : ℕ) (P : SelectedProduct) : Tasks := List.replicate k P

end PolynomialPackingMM.IntegerRecursion


