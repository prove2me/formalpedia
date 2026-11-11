-- Prove2me | Definitions.Def_PolynomialPackingMM_IntegerRecursion_Packing
-- name    : PolynomialPackingMM_IntegerRecursion_Packing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:10.066208+00:00
-- url     : https://prove2.me/theorems/bf928df0-db40-48a0-b34c-42bfda420910
-- title:
--   Polynomial packings, copying same-left packings and bilinear data
-- statement:
--   For finite target and source lists $T,S$, a polynomial packing consists of separate left and right linear encoders $E^L,E^R$ and a linear decoder $D$. Its decoded coefficient tensor represents
--
--   $$D\bigl(S(E^L A,E^R B)\bigr)=T(A,B)+\varepsilon R_\varepsilon(A,B).$$
--
--   Exact mode requires rational coefficients and zero error. Approximate mode permits finite Laurent coefficients but requires every error coefficient at exponent $k\le0$ to vanish. Since the construction is bilinear in the scalar input entries, this is precisely a polynomial error divisible by $\varepsilon$, universally in the inputs. Output-degree bounds refer to the fully decoded coefficient tensor. Same-left data check literal equality of all left coefficient spaces and copy the arbitrary common $A$ unchanged to every source. Bilinear data consist of $r$ pairs of linear forms and $r$ rational output vectors; correctness is a separate predicate, and $r$ counts only their scalar products.
--
--   This interface separates finite data from the existence and correctness theorems. **Formalization Note** Coefficients lie in the additive group algebra of $\mathbb Z$ over $\mathbb Q$. No Laurent expression is evaluated at zero. The output/error functions and separate linearity predicate are also defined; the common-left sum uses distinct keys to avoid multiplying the answer by the number of targets.
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 9 (PDF 10), Definition 2.2, equation (3); §2.2 rational bilinear algorithms, p. 10; Lemma A.1, p. 22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_SelectedProduct

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

/-- Finite Laurent polynomials in the formal parameter. No evaluation at zero is used. -/
abbrev Laurent := AddMonoidAlgebra ℚ ℤ

noncomputable def rationalLaurent (q : ℚ) : Laurent := AddMonoidAlgebra.single 0 q

def IsRationalLaurent (x : Laurent) : Prop := ∀ k : ℤ, k ≠ 0 → x.coeff k = 0

/-- A polynomial divisible by ε: every coefficient at degree ≤0 vanishes. -/
def PositiveError (x : Laurent) : Prop := ∀ k : ℤ, k ≤ 0 → x.coeff k = 0

inductive Mode where
  | exact
  | approximate
  deriving DecidableEq

/-- Finite encoder/decoder data, with correctness kept outside the data. -/
structure PackingData (T S : Tasks) where
  left : LeftIndex S → LeftIndex T → Laurent
  right : RightIndex S → RightIndex T → Laurent
  decode : OutputIndex T → OutputIndex S → Laurent

noncomputable def PackingData.coefficient {T S : Tasks} (D : PackingData T S)
    (o : OutputIndex T) (a : LeftIndex T) (b : RightIndex T) : Laurent :=
  ∑ c, ∑ x, ∑ y,
    D.decode o c * rationalLaurent (targetCoefficient S c x y) * D.left x a * D.right y b

/-- Definition 2.2, checked coefficientwise as a universal bilinear identity. -/
def PackingData.Valid {T S : Tasks} (D : PackingData T S) (mode : Mode) : Prop :=
  match mode with
  | .exact =>
      (∀ x a, IsRationalLaurent (D.left x a)) ∧
      (∀ y b, IsRationalLaurent (D.right y b)) ∧
      (∀ o c, IsRationalLaurent (D.decode o c)) ∧
      ∀ o a b, D.coefficient o a b = rationalLaurent (targetCoefficient T o a b)
  | .approximate => ∀ o a b,
      PositiveError (D.coefficient o a b - rationalLaurent (targetCoefficient T o a b))

def HasPacking (mode : Mode) (T S : Tasks) : Prop := ∃ D : PackingData T S, D.Valid mode

def PackingData.DegreeAtMost {T S : Tasks} (D : PackingData T S) (d : ℕ) : Prop :=
  ∀ o a b (k : ℤ), (d : ℤ) < k → (D.coefficient o a b).coeff k = 0

/-- Equality of literal left coefficient spaces, including monomial and matrix indices. -/
def SameLeftSpaces (T S : Tasks) : Prop :=
  ∀ P ∈ T ++ S, ∀ Q ∈ T ++ S, P.leftKeys = Q.leftKeys

/-- The left encoder is copying, by construction, rather than an arbitrary linear map. -/
structure SLPackingData (T S : Tasks) where
  right : RightIndex S → RightIndex T → Laurent
  decode : OutputIndex T → OutputIndex S → Laurent

noncomputable def sameLeftTarget (T : Tasks) (o : OutputIndex T) (a : Key)
    (b : RightIndex T) : ℚ :=
  ∑ x : LeftIndex T, if x.2.val = a then targetCoefficient T o x b else 0

noncomputable def SLPackingData.coefficient {T S : Tasks} (D : SLPackingData T S)
    (o : OutputIndex T) (a : Key) (b : RightIndex T) : Laurent :=
  ∑ c, ∑ y, D.decode o c * rationalLaurent (sameLeftTarget S c a y) * D.right y b

def SLPackingData.Valid {T S : Tasks} (D : SLPackingData T S) (mode : Mode) : Prop :=
  SameLeftSpaces T S ∧ match mode with
  | .exact => (∀ y b, IsRationalLaurent (D.right y b)) ∧
      (∀ o c, IsRationalLaurent (D.decode o c)) ∧
      ∀ o a b, D.coefficient o a b = rationalLaurent (sameLeftTarget T o a b)
  | .approximate => ∀ o a b,
      PositiveError (D.coefficient o a b - rationalLaurent (sameLeftTarget T o a b))

def HasSLPacking (mode : Mode) (T S : Tasks) : Prop :=
  ∃ D : SLPackingData T S, D.Valid mode

def SLPackingData.DegreeAtMost {T S : Tasks} (D : SLPackingData T S) (d : ℕ) : Prop :=
  ∀ o a b (k : ℤ), (d : ℤ) < k → (D.coefficient o a b).coeff k = 0

/-- Rational bilinear data; r counts only the ordered scalar products. -/
structure BilinearData (T : Tasks) (r : ℕ) where
  left : Fin r → LeftIndex T → Laurent
  right : Fin r → RightIndex T → Laurent
  weight : OutputIndex T → Fin r → Laurent

noncomputable def BilinearData.coefficient {T : Tasks} {r : ℕ} (D : BilinearData T r)
    (o : OutputIndex T) (a : LeftIndex T) (b : RightIndex T) : Laurent :=
  ∑ ν, D.left ν a * D.right ν b * D.weight o ν

def BilinearData.Valid {T : Tasks} {r : ℕ} (D : BilinearData T r) (mode : Mode) : Prop :=
  match mode with
  | .exact => (∀ ν a, IsRationalLaurent (D.left ν a)) ∧
      (∀ ν b, IsRationalLaurent (D.right ν b)) ∧
      (∀ o ν, IsRationalLaurent (D.weight o ν)) ∧
      ∀ o a b, D.coefficient o a b = rationalLaurent (targetCoefficient T o a b)
  | .approximate => ∀ o a b,
      PositiveError (D.coefficient o a b - rationalLaurent (targetCoefficient T o a b))

def HasBilinearAlgorithm (mode : Mode) (T : Tasks) (r : ℕ) : Prop :=
  ∃ D : BilinearData T r, D.Valid mode

noncomputable def matrixProduct (v : ℕ+) : SelectedProduct := product (full 1 1) v v v

/-- Output and error as actual bilinear functions over Laurent coefficients. -/
noncomputable def PackingData.evaluate {T S : Tasks} (D : PackingData T S)
    (A : LeftIndex T → Laurent) (B : RightIndex T → Laurent) : OutputIndex T → Laurent :=
  fun o => ∑ a, ∑ b, D.coefficient o a b * A a * B b

noncomputable def targetEvaluate (T : Tasks) (A : LeftIndex T → Laurent)
    (B : RightIndex T → Laurent) : OutputIndex T → Laurent :=
  fun o => ∑ a, ∑ b, rationalLaurent (targetCoefficient T o a b) * A a * B b

noncomputable def PackingData.error {T S : Tasks} (D : PackingData T S)
    (A : LeftIndex T → Laurent) (B : RightIndex T → Laurent) : OutputIndex T → Laurent :=
  D.evaluate A B - targetEvaluate T A B

/-- Restrict the common left sum to distinct keys, avoiding multiplicity from repeated tasks. -/
noncomputable def commonLeftKeys (T : Tasks) : Finset Key :=
  T.foldl (fun I P => I ∪ P.leftKeys) ∅

noncomputable def SLPackingData.output {T S : Tasks} (D : SLPackingData T S)
    (A : Key → Laurent) (B : RightIndex T → Laurent) : OutputIndex T → Laurent :=
  fun o => ∑ a ∈ commonLeftKeys T, ∑ b, D.coefficient o a b * A a * B b

noncomputable def SLPackingData.error {T S : Tasks} (D : SLPackingData T S)
    (A : Key → Laurent) (B : RightIndex T → Laurent) : OutputIndex T → Laurent :=
  D.output A B - fun o => ∑ a ∈ commonLeftKeys T, ∑ b,
    rationalLaurent (sameLeftTarget T o a b) * A a * B b

/-- Bilinearity, including additivity and scalar homogeneity in both arguments. -/
def SeparatelyLinear {U V W : Type} [AddCommGroup U] [Module Laurent U]
    [AddCommGroup V] [Module Laurent V] [AddCommGroup W] [Module Laurent W]
    (f : U → V → W) : Prop :=
  (∀ x y z, f (x + y) z = f x z + f y z) ∧
  (∀ (c : Laurent) x y, f (c • x) y = c • f x y) ∧
  (∀ x y z, f x (y + z) = f x y + f x z) ∧
  (∀ (c : Laurent) x y, f x (c • y) = c • f x y)

end PolynomialPackingMM.IntegerRecursion


