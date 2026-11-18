-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_LinearCertificate
-- name    : RealPinwheel_FiveSixths_LinearCertificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:19:11.511257+00:00
-- url     : https://prove2.me/theorems/a7718f69-cd36-4797-94ad-ee8e2aa08713
-- title:
--   Integer linear certificates for real-domain coverage
-- statement:
--   The data describes finite proofs of coverage by rational coordinate boxes. An atom is an integer linear inequality, with a flag for strictness. A sparse nonnegative integer combination certifies a target inequality by matching its coefficients and bounding its constant term. Strictness must follow from a positive strict summand or a strict constant gap.
--
--   $$s\,a_{\mathrm{target}}=\sum_j\lambda_j a_j,\qquad s>0,\quad\lambda_j\ge0.$$
--
--   Cover trees branch on coordinate inequalities. Their leaves either certify a contradiction or certify membership in an annotated word box. This is an exact arithmetic proof format for the real linear coverage queries in the source; soundness is a separate theorem. The initial context expresses positive ordered densities and the density or potential bound.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (3), Section 4 queries (4)–(5), printed pp. 9–10 (PDF pp. 10–11), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf; explicit linear-combination proof format for the same exact real-arithmetic coverage assertions.

import Definitions.Def_RealPinwheel_FiveSixths_CycleCode

namespace RealPinwheel.FiveSixths

/-- An integer linear inequality, strict exactly when its flag is true. -/
structure LinearAtom (n : ℕ) where
  coeff : Fin n → ℤ
  constant : ℤ
  strict : Bool

def LinearAtom.eval {n : ℕ} (a : LinearAtom n) (d : Fin n → ℝ) : ℝ :=
  (a.constant : ℝ) + ∑ i, (a.coeff i : ℝ) * d i

def LinearAtom.Holds {n : ℕ} (a : LinearAtom n) (d : Fin n → ℝ) : Prop :=
  if a.strict then a.eval d < 0 else a.eval d ≤ 0

def zeroAtom (n : ℕ) : LinearAtom n := ⟨fun _ => 0, 0, false⟩

def contextAtom {n : ℕ} (Γ : List (LinearAtom n)) (i : ℕ) : LinearAtom n :=
  Γ[i]?.getD (zeroAtom n)

/-- A sparse nonnegative integer combination with a positive scale. -/
structure LinearCombination where
  denominator : ℕ
  terms : List (ℕ × ℕ)
  deriving Repr

def combinationCoeff {n : ℕ} (Γ : List (LinearAtom n)) (c : LinearCombination)
    (i : Fin n) : ℤ :=
  (c.terms.map fun x => (x.2 : ℤ) * (contextAtom Γ x.1).coeff i).sum

def combinationConstant {n : ℕ} (Γ : List (LinearAtom n)) (c : LinearCombination) : ℤ :=
  (c.terms.map fun x => (x.2 : ℤ) * (contextAtom Γ x.1).constant).sum

def combinationStrict {n : ℕ} (Γ : List (LinearAtom n)) (c : LinearCombination) : Bool :=
  c.terms.any fun x => decide (0 < x.2) && (contextAtom Γ x.1).strict

def combinationCheck {n : ℕ} (Γ : List (LinearAtom n)) (c : LinearCombination)
    (target : LinearAtom n) : Bool :=
  decide (0 < c.denominator) &&
  (List.finRange n).all (fun i =>
    decide ((c.denominator : ℤ) * target.coeff i = combinationCoeff Γ c i)) &&
  decide ((c.denominator : ℤ) * target.constant ≤ combinationConstant Γ c) &&
  if target.strict then
    decide ((c.denominator : ℤ) * target.constant < combinationConstant Γ c) ||
      combinationStrict Γ c
  else true

def upperAtom {n : ℕ} (i : Fin n) (p q : ℕ) (strict : Bool) : LinearAtom n :=
  ⟨fun j => if j = i then (q : ℤ) else 0, -(p : ℤ), strict⟩

def complementAtom {n : ℕ} (a : LinearAtom n) : LinearAtom n :=
  ⟨fun i => -a.coeff i, -a.constant, !a.strict⟩

def falseAtom (n : ℕ) : LinearAtom n := ⟨fun _ => 0, 0, true⟩

/-- A finite covering proof using coordinate cuts and linear combinations. -/
inductive LinearCoverTree (n : ℕ) where
  | empty : LinearCombination → LinearCoverTree n
  | word : ℕ → (Fin n → LinearCombination) → LinearCoverTree n
  | split : Fin n → ℕ → ℕ → Bool → LinearCoverTree n → LinearCoverTree n → LinearCoverTree n

def emptyCode : CycleCode := ⟨"", #[], #[], #[]⟩

def linearCoverCheck {n : ℕ} (N : ℕ) (codes : ℕ → CycleCode) (Γ : List (LinearAtom n)) :
    LinearCoverTree n → Bool
  | .empty c => combinationCheck Γ c (falseAtom n)
  | .word j cs =>
      let code := codes j
      decide (j < N) &&
      (List.finRange n).all fun i =>
        decide (0 < codeDen code i) &&
        combinationCheck Γ (cs i)
          (upperAtom i (codeNum code i) (codeDen code i) (codeStrict code i))
  | .split i p q strict l r =>
      let a := upperAtom i p q strict
      decide (0 < q) && linearCoverCheck N codes (a :: Γ) l &&
        linearCoverCheck N codes (complementAtom a :: Γ) r

def positiveAtom {n : ℕ} (i : Fin n) : LinearAtom n :=
  ⟨fun j => if j = i then -1 else 0, 0, true⟩

def orderAtom {n : ℕ} (i j : Fin n) : LinearAtom n :=
  ⟨fun z => (if z = j then 1 else 0) - (if z = i then 1 else 0), 0, false⟩

def densityAtom (n k : ℕ) : LinearAtom n :=
  ⟨fun i => if i.val < k then 6 else 0, -5, false⟩

def initialAtoms (n k : ℕ) : List (LinearAtom n) :=
  (List.finRange n).map positiveAtom ++
    (List.finRange (n - 1)).map (fun i =>
      orderAtom (⟨i.val, by omega⟩ : Fin n) ⟨i.val + 1, by omega⟩) ++
    [densityAtom n k]

end RealPinwheel.FiveSixths


