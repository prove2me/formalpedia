-- Prove2me | Definitions.Def_ParityDegreeDepth_Main_Context
-- name    : ParityDegreeDepth_Main_Context
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:46.242934+00:00
-- url     : https://prove2.me/theorems/930bc6bd-1246-491c-8afa-2d6d629614d5
-- title:
--   Operational definitions for parity depth, degree, Fourier size and contraction rank
-- statement:
--   The shared operational interface uses $\mathbb F_2^n$, the published normalized Walsh transform, and the published ANF coefficients through the Boolean/F₂ correspondence. Its spectral norm is the sum of absolute coefficients and sparsity is their nonzero support cardinality. Degree is the maximum cardinality of a nonzero ANF coefficient, with degree $-\infty$ for zero.
--
--   A parity tree queries a nonzero binary linear form and has sign leaves. Evaluation follows its parity bit; depth counts the maximum queries on a path. The minimum computing depth is taken over all exact trees. The exhaustive coordinate tree computes every phase. The explicit protocol simulation sends Alice's local parity bit followed by Bob's local parity bit; its child labels combine the two bits to select the parity branch. It uses the published public-output protocol model, and communication depth minimizes actual exact protocol costs for $f(x+y)$.
--
--   Finite differences define the top form. Vanishing codimension minimizes actual subspace codimension. Binary rank maximizes the ranks of all binary contractions. Formal anchor coordinates lie in a multivariate polynomial ring, and generic ranks are computed over its fraction field. Scalar extension uses the tensor's original standard-basis coefficients. Strong vanishing leaves one argument unrestricted. Block multilinearity is total degree one per block, and multiplicity is the least total order of a nonzero translated monomial, with value $+\infty$ for zero.
--
--   These definitions contain no desired complexity or rank bounds. They provide the common mathematical interface; theorem items duplicate only needed declarations privately to remain independent of unpublished drafts.
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, §§2–3, Appendix A.1–A.4, Definition A.3, Definition B.1 (PDF 5–12,16–22; printed 4–11,15–21).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main

abbrev Vec (n : ℕ) (F : Type) := Fin n → F

def phase {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (x : Vec n (ZMod 2)) : ℝ :=
  (-1 : ℝ) ^ (p x).val

def character {n : ℕ} (a x : Vec n (ZMod 2)) : ℝ :=
  (-1 : ℝ) ^ (∑ i, a i * x i).val

def spectralNorm {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℝ :=
  ∑ a, |QAlgorithms.boolFourier f a|

def sparsity {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℕ :=
  (Finset.univ.filter fun a => QAlgorithms.boolFourier f a ≠ 0).card

def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- The published Boolean ANF coefficient, transported by false ↔ 0, true ↔ 1. -/
def coefficient {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
  then 1 else 0

/-- Degree of the unique multilinear normal form; zero has degree bottom. -/
def anfDegree {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) : WithBot ℕ :=
  Finset.univ.sup fun S : Finset (Fin n) =>
    if coefficient p S = 0 then ⊥ else (S.card : WithBot ℕ)

/-- All affine coordinate injections, including dimension zero. -/
def affineMap {m n : ℕ} (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2))
    (a : Vec n (ZMod 2)) (y : Vec m (ZMod 2)) : Vec n (ZMod 2) := a + B y

inductive ParityTree (n : ℕ) where
  | leaf (b : Bool)
  | query (a : Vec n (ZMod 2)) (ha : a ≠ 0) (zero one : ParityTree n)

def treeDepth {n : ℕ} : ParityTree n → ℕ
  | .leaf _ => 0
  | .query _ _ l r => 1 + max (treeDepth l) (treeDepth r)

def treeEval {n : ℕ} : ParityTree n → Vec n (ZMod 2) → ℝ
  | .leaf b, _ => if b then -1 else 1
  | .query a _ l r, x => if ∑ i, a i * x i = 0 then treeEval l x else treeEval r x

/-- Intrinsic minimum over actual exact computing trees. Feasible for every phase. -/
def parityDepth {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℕ :=
  sInf {k | ∃ t : ParityTree n, treeDepth t = k ∧ ∀ x, treeEval t x = f x}

/-- Exhaustive coordinate tree; the state records previously queried coordinates. -/
def coordinateTree {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (indices : List (Fin n)) (a : Vec n (ZMod 2)) : ParityTree n :=
  match indices with
  | [] => .leaf (decide (p a ≠ 0))
  | i :: rest => .query (Pi.single i 1) (by
      intro h
      have he := congrFun h i
      simpa using he)
      (coordinateTree p rest (Function.update a i 0))
      (coordinateTree p rest (Function.update a i 1))

/-- Each query sends both local parity bits; the child labels combine them into the branch. -/
def simulateTree {n : ℕ} : ParityTree n →
    DetCCHard.Protocol (Vec n (ZMod 2)) (Vec n (ZMod 2))
  | .leaf b => .leaf b
  | .query a _ l r =>
      .alice (fun x => decide (∑ i, a i * x i ≠ 0))
        (.bob (fun y => decide (∑ i, a i * y i ≠ 0)) (simulateTree l) (simulateTree r))
        (.bob (fun y => decide (∑ i, a i * y i ≠ 0)) (simulateTree r) (simulateTree l))

/-- Public sign output is the published protocol's output bit, true ↔ -1. -/
def protocolSign {n : ℕ} (t : DetCCHard.Protocol (Vec n (ZMod 2)) (Vec n (ZMod 2)))
    (x y : Vec n (ZMod 2)) : ℝ := if t.eval x y then -1 else 1

def communicationDepth {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℕ :=
  sInf {k | ∃ t : DetCCHard.Protocol (Vec n (ZMod 2)) (Vec n (ZMod 2)),
    t.depth = k ∧ ∀ x y, protocolSign t x y = f (x + y)}

def delta {n : ℕ} (h : Vec n (ZMod 2)) (p : Vec n (ZMod 2) → ZMod 2)
    (x : Vec n (ZMod 2)) : ZMod 2 := p (x + h) + p x

def differences {n k : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (h : Fin k → Vec n (ZMod 2)) : Vec n (ZMod 2) → ZMod 2 :=
  (List.ofFn h).foldl (fun q v => delta v q) p

def signDerivatives {n k : ℕ} (f : Vec n (ZMod 2) → ℝ)
    (h : Fin k → Vec n (ZMod 2)) : Vec n (ZMod 2) → ℝ :=
  (List.ofFn h).foldl (fun g v x => g x * g (x + v)) f

abbrev Form (F : Type) (n d : ℕ) := (Fin d → Vec n F) → F

def topForm {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (d : ℕ) : Form (ZMod 2) n d :=
  fun h => differences p h 0

def IsMultilinear {F : Type} [Field F] {n d : ℕ} (T : Form F n d) : Prop :=
  (∀ x i u v, T (Function.update x i (u + v)) =
    T (Function.update x i u) + T (Function.update x i v)) ∧
  (∀ x i (c : F) u, T (Function.update x i (c • u)) = c * T (Function.update x i u))

def IsSymmetric {F : Type} {n d : ℕ} (T : Form F n d) : Prop :=
  ∀ (σ : Equiv.Perm (Fin d)) x, T (x ∘ σ) = T x

def IsAlternating {F : Type} [Zero F] {n d : ℕ} (T : Form F n d) : Prop :=
  ∀ x i j, i ≠ j → x i = x j → T x = 0

def Vanishes {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (U : Submodule F (Vec n F)) : Prop := ∀ x, (∀ i, x i ∈ U) → T x = 0

def StrongVanishes {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (U : Submodule F (Vec n F)) : Prop :=
  ∀ (v : Vec n F) (u : Fin (d - 1) → U),
    T (fun i => if hi : i.val = 0 then v else (u ⟨i.val - 1, by omega⟩ : Vec n F)) = 0

def vanishingCodim {n d : ℕ} (T : Form (ZMod 2) n d) : ℕ :=
  sInf {r | ∃ U : Submodule (ZMod 2) (Vec n (ZMod 2)),
    n - Module.finrank (ZMod 2) U = r ∧ Vanishes T U}

def contraction {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (h : Fin (d - 2) → Vec n F) : Matrix (Fin n) (Fin n) F :=
  fun i j => T (fun s => if hs : s.val < d - 2 then h ⟨s.val, hs⟩
    else if s.val = d - 2 then Pi.single i 1 else Pi.single j 1)

def binaryRank {n d : ℕ} (T : Form (ZMod 2) n d) : ℕ :=
  Finset.univ.sup fun h : Fin (d - 2) → Vec n (ZMod 2) => (contraction T h).rank

/-- Scalar extension by the original tensor coefficients on standard basis tuples. -/
def extendForm {F E : Type} [Field F] [Field E] [Algebra F E] {n d : ℕ}
    (T : Form F n d) : Form E n d :=
  fun x => ∑ a : Fin d → Fin n,
    algebraMap F E (T (fun i => Pi.single (a i) 1)) * ∏ i, x i (a i)

abbrev AnchorRing (F : Type) [CommRing F] (n k : ℕ) := MvPolynomial (Fin k × Fin n) F
abbrev AnchorField (F : Type) [Field F] (n k : ℕ) := FractionRing (AnchorRing F n k)

/-- A formal contraction polynomial, before adjoining fractions. -/
def genericMatrix {F : Type} [Field F] {n d : ℕ} (T : Form F n d) :
    Matrix (Fin n) (Fin n) (AnchorRing F n (d - 2)) :=
  fun i j => ∑ a : Fin (d - 2) → Fin n,
    MvPolynomial.C (T (fun s => if hs : s.val < d - 2 then Pi.single (a ⟨s.val, hs⟩) 1
      else if s.val = d - 2 then Pi.single i 1 else Pi.single j 1)) *
    ∏ t, MvPolynomial.X (t, a t)

def genericContraction {F : Type} [Field F] {n d : ℕ} (T : Form F n d) :
    Matrix (Fin n) (Fin n) (AnchorField F n (d - 2)) :=
  (genericMatrix T).map (algebraMap (AnchorRing F n (d - 2)) (AnchorField F n (d - 2)))

def genericRank {F : Type} [Field F] {n d : ℕ} (T : Form F n d) : ℕ :=
  (genericContraction T).rank

def genericRadical {F : Type} [Field F] {n d : ℕ} (T : Form F n d) :
    Submodule (AnchorField F n (d - 2)) (Vec n (AnchorField F n (d - 2))) :=
  LinearMap.ker (Matrix.mulVecLin (genericContraction T))

/-- Block total degree exactly one, not a separate degree bound on each coordinate. -/
def BlockMultilinear {F : Type} [Field F] {n k m r : ℕ}
    (N : Matrix (Fin m) (Fin r) (AnchorRing F n k)) : Prop :=
  ∀ i j e, e ∈ (N i j).support → ∀ b : Fin k, ∑ v : Fin n, e (b, v) = 1

def matrixGenericRank {F : Type} [Field F] {n k m r : ℕ}
    (N : Matrix (Fin m) (Fin r) (AnchorRing F n k)) : ℕ :=
  (N.map (algebraMap (AnchorRing F n k) (AnchorField F n k))).rank

def matrixBinaryRank {n k m r : ℕ}
    (N : Matrix (Fin m) (Fin r) (AnchorRing (ZMod 2) n k)) : ℕ :=
  Finset.univ.sup fun a : (Fin k × Fin n) → ZMod 2 =>
    (N.map (MvPolynomial.eval a)).rank

/-- Formal multiplicity: infinity exactly for the zero polynomial, over any field. -/
def multiplicity {F : Type} [Field F] {n : ℕ} (P : MvPolynomial (Fin n) F)
    (a : Vec n F) : ℕ∞ :=
  ⨅ e ∈ (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) P).support,
    (KakeyaHasse.order e : ℕ∞)

end ParityDegreeDepth.Main


