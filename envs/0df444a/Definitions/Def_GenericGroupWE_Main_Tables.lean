-- Prove2me | Definitions.Def_GenericGroupWE_Main_Tables
-- name    : GenericGroupWE_Main_Tables
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:03.578285+00:00
-- url     : https://prove2.me/theorems/88085ab5-3dec-4f76-bd19-baf70a6d6b91
-- title:
--   Boolean moment tables and the weighted assignment stack
-- statement:
--   Let $b\in\{0,1\}^N$, $d\ge1$, and $b_S=\prod_{i\in S}b_i$. Set $r=\max(1,\lfloor\sqrt{\log_2(N+2)}\rfloor)$ and $R=\binom{r+2d}{d}$. The quadratic polynomials $q_s$ are a finite family in $N$ variables, and the exponents $\alpha_j$ are nonnegative integers. For every sample $0\le t\le N(R^2+r)$, include the separately labeled weights $h_{\alpha,t}=\prod_{j=1}^{R^2}\ell_{j,t}^{\alpha_j}$ for $\sum\alpha_j\le r$, where $\ell_{j,t}=1+\sum_{i=1}^N(2^{j-1}t)^i b_i$.
--
--   $$A(b)_{(h,S),T}=h(b)b_Sb_T,\qquad |S|,|T|\le d.$$
--
--   The assignment span is the span of these explicit matrices. The tested space consists of matrices admitting a representation $\sum_b\lambda_bA(b)$ satisfying every test $\sum_b\lambda_bh(b)q_s(b)b_U=0$ for $|U|+2\le2d$. This uses some representation, never a chosen representation. Quadratic tests are entry-level linear tests and are independent of the representation. The module also defines the surviving columns, geometric combinations, replacement coordinates and their actual evaluation functional.
--
--   For nonnegative degree cutoffs $a,b$ and a linear polynomial functional $L$, the rectangular table $H_{a,b}(L)$ uses all ordinary monomials of the indicated degree, including powers and $1$. Finite dimensions and ranks are ordinary algebraic dimensions, without positivity assumptions on $L$.
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, §5.1, eq. (5), PDF p. 15 (printed p. 14); §6.1–6.4, eqs. (25)–(32), PDF pp. 24–29 (printed pp. 23–28); §6.5, eq. (33), PDF p. 30 (printed p. 29).

import Mathlib

namespace GenericGroupWE.Main

open scoped BigOperators

abbrev BooleanAssignment (N : ℕ) := Fin N → Bool

def booleanPoint {K : Type*} [Zero K] [One K] {N : ℕ}
    (b : BooleanAssignment N) (i : Fin N) : K := if b i then 1 else 0

abbrev OrdinaryMonomial (N e : ℕ) :=
  {u : Fin N → Fin (e + 1) // ∑ i, (u i).val ≤ e}

noncomputable instance ordinaryMonomialFintype (N e : ℕ) : Fintype (OrdinaryMonomial N e) :=
  Fintype.ofFinite _

noncomputable def monomialPolynomial {K : Type*} [CommSemiring K] {N e : ℕ}
    (u : OrdinaryMonomial N e) : MvPolynomial (Fin N) K :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (u.val i).val) 1

/-- PDF 25: ordinary monomials, including powers and the constant monomial. -/
noncomputable def rectangularTable {K : Type*} [Field K] {N : ℕ}
    (a b : ℕ) (L : MvPolynomial (Fin N) K →ₗ[K] K) :
    Matrix (OrdinaryMonomial N a) (OrdinaryMonomial N b) K :=
  fun u v => L (monomialPolynomial u * monomialPolynomial v)

def NoBooleanZero {K : Type*} [Field K] {N k : ℕ}
    (q : Fin k → MvPolynomial (Fin N) K) : Prop :=
  ∀ b : BooleanAssignment N, ∃ s, MvPolynomial.eval (booleanPoint b) (q s) ≠ 0

/-- The degree condition avoids truncated subtraction in small degrees. -/
def AnnihilatesEquations {K : Type*} [Field K] {N k : ℕ}
    (q : Fin k → MvPolynomial (Fin N) K)
    (L : MvPolynomial (Fin N) K →ₗ[K] K) (e : ℕ) : Prop :=
  ∀ f : MvPolynomial (Fin N) K, f.totalDegree + 2 ≤ e →
    (∀ i, L (((MvPolynomial.X i)^2 - MvPolynomial.X i) * f) = 0) ∧
    (∀ s, L (q s * f) = 0)

abbrev BitMonomial (N d : ℕ) := {S : Finset (Fin N) // S.card ≤ d}

noncomputable instance bitMonomialFintype (N d : ℕ) : Fintype (BitMonomial N d) :=
  Fintype.ofFinite _

def bitProduct {K : Type*} [CommMonoidWithZero K] {N : ℕ}
    (b : BooleanAssignment N) (S : Finset (Fin N)) : K :=
  ∏ i ∈ S, booleanPoint b i

/-- Eq. (26), using floor(sqrt(log₂(N+2))) = sqrt(floor(log₂(N+2))). -/
def weightDegree (N : ℕ) : ℕ := max 1 (Nat.sqrt (Nat.log 2 (N + 2)))

def rankTarget (N d : ℕ) : ℕ := Nat.choose (weightDegree N + 2 * d) d

abbrev WeightLabel (N d : ℕ) :=
  Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1) ×
    OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N)

abbrev StackRow (N d : ℕ) := WeightLabel N d × BitMonomial N d

/-- Eq. (33), before the prime is supplied. -/
def matrixOrder (N d : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (min d N + 1), Nat.choose N j) *
    (N * ((rankTarget N d)^2 + weightDegree N) + 1) *
    Nat.choose ((rankTarget N d)^2 + weightDegree N) (weightDegree N)

/-- The zeroth coordinate is the literal constant 1. Forms are numbered from 1 in the paper. -/
def geometricForm {K : Type*} [Field K] {N : ℕ}
    (j t : ℕ) (b : BooleanAssignment N) : K :=
  1 + ∑ i : Fin N, (((2 : K)^j * (t : K))^(i.val + 1)) * booleanPoint b i

def stackWeight {K : Type*} [Field K] {N d : ℕ}
    (h : WeightLabel N d) (b : BooleanAssignment N) : K :=
  ∏ j : Fin ((rankTarget N d)^2),
    (geometricForm j.val h.1.val b) ^ (h.2.val j).val

/-- Eqs. (5), (27): labels stay separate when the functions happen to coincide. -/
def assignmentStack {K : Type*} [Field K] {N d : ℕ}
    (b : BooleanAssignment N) : Matrix (StackRow N d) (BitMonomial N d) K :=
  fun row col => stackWeight row.1 b * bitProduct b row.2.val * bitProduct b col.val

noncomputable def representedStack {K : Type*} [Field K] {N d : ℕ}
    (coefficients : BooleanAssignment N → K) : Matrix (StackRow N d) (BitMonomial N d) K :=
  ∑ b, coefficients b • assignmentStack b

noncomputable def assignmentSpan (K : Type*) [Field K] (N d : ℕ) :
    Submodule K (Matrix (StackRow N d) (BitMonomial N d) K) :=
  Submodule.span K (Set.range (assignmentStack (K := K) (N := N) (d := d)))

/-- Eqs. (25): existential representation; no arbitrary choice of assignment coefficients.
For quadratic equations these are the representation-independent entry tests of §6.1. -/
noncomputable def testedSpace {K : Type*} [Field K] {N k d : ℕ}
    (q : Fin k → MvPolynomial (Fin N) K) :
    Set (Matrix (StackRow N d) (BitMonomial N d) K) :=
  {A | ∃ coefficients : BooleanAssignment N → K,
    A = representedStack coefficients ∧
      ∀ (h : WeightLabel N d) (s : Fin k) (U : Finset (Fin N)), U.card + 2 ≤ 2 * d →
        ∑ b, coefficients b * stackWeight h b *
          MvPolynomial.eval (booleanPoint b) (q s) * bitProduct b U = 0}

/-- The surviving column c_i has the extra monomial coordinate U. -/
noncomputable def survivingColumn {K : Type*} [Field K] {N d : ℕ}
    (hd : 1 ≤ d) (A : Matrix (StackRow N d) (BitMonomial N d) K)
    (i : Option (Fin N)) : BitMonomial N (d - 1) → StackRow N d → K :=
  fun U row =>
    match i with
    | none => A row ⟨U.val, U.property.trans (Nat.sub_le d 1)⟩
    | some i => A row ⟨insert i U.val, by
        have h := Finset.card_insert_le i U.val
        have hu := U.property
        omega⟩

noncomputable def survivingDimension {K : Type*} [Field K] {N d : ℕ}
    (hd : 1 ≤ d) (A : Matrix (StackRow N d) (BitMonomial N d) K) : ℕ :=
  Module.finrank K (Submodule.span K (Set.range (survivingColumn hd A)))

noncomputable def geometricColumn {K : Type*} [Field K] {N d : ℕ}
    (hd : 1 ≤ d) (A : Matrix (StackRow N d) (BitMonomial N d) K) (j t : ℕ) :=
  survivingColumn hd A none + ∑ i : Fin N,
    ((((2 : K)^j) * (t : K))^(i.val+1)) • survivingColumn hd A (some i)

noncomputable def IsReplacementBasis {K : Type*} [Field K] {N d δ : ℕ}
    (hd : 1 ≤ d) (A : Matrix (StackRow N d) (BitMonomial N d) K)
    (t : ℕ) (μ : Fin N → Fin δ → K) : Prop :=
  LinearIndependent K (fun j : Fin δ => geometricColumn hd A j.val t) ∧
    Submodule.span K (Set.range (fun j : Fin δ => geometricColumn hd A j.val t)) =
      Submodule.span K (Set.range (survivingColumn hd A)) ∧
    ∀ i, survivingColumn hd A (some i) =
      ∑ j : Fin δ, μ i j • geometricColumn hd A j.val t

def affineBit {K : Type*} [Field K] {N : ℕ}
    (κ : Option (Fin N) → K) (b : BooleanAssignment N) : K :=
  κ none + ∑ i, κ (some i) * booleanPoint b i

noncomputable def sampleStack {K : Type*} [Field K] {N d : ℕ}
    (A : Matrix (StackRow N d) (BitMonomial N d) K)
    (t : Fin (N * ((rankTarget N d)^2 + weightDegree N) + 1)) :
    Matrix (OrdinaryMonomial ((rankTarget N d)^2) (weightDegree N) × BitMonomial N d)
      (BitMonomial N d) K :=
  fun row col => A ((t, row.1), row.2) col

/-- §6.4: replacement coordinates for any coefficients expressing c_i in the selected basis. -/
def replacement {K : Type*} [Field K] {N δ : ℕ}
    (t : ℕ) (μ : Fin N → Fin δ → K) (b : BooleanAssignment N) : Fin N → K :=
  fun i => ∑ j, μ i j * geometricForm j.val t b

noncomputable def replacementFunctional {K : Type*} [Field K] {N δ : ℕ}
    (coefficients : BooleanAssignment N → K) (t : ℕ) (μ : Fin N → Fin δ → K) :
    MvPolynomial (Fin N) K →ₗ[K] K where
  toFun f := ∑ b, coefficients b * MvPolynomial.eval (replacement t μ b) f
  map_add' f g := by simp [MvPolynomial.eval_add, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    simp [MvPolynomial.smul_eq_C_mul, Finset.mul_sum, mul_left_comm]

end GenericGroupWE.Main


