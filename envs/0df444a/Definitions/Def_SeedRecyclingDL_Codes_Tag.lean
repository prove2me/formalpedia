-- Prove2me | Definitions.Def_SeedRecyclingDL_Codes_Tag
-- name    : SeedRecyclingDL_Codes_Tag
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:47.978025+00:00
-- url     : https://prove2.me/theorems/858bb093-cd33-4de6-90ba-3ce34c6bccb4
-- title:
--   Polynomial tags, recycled ranks, and Appendix C procedures
-- statement:
--   The field is supplied by the published polynomial-basis presentation, specialized to characteristic two. Payload blocks are padded with trailing zeros and become the coefficients of $P_x$. Good evaluation seeds separate every competitor; good multipliers separate their projected products. The tag is
--   $$\phi^{-1}(a)\Vert\phi^{-1}(\lambda)\Vert\pi(\lambda P_x(a)).$$
--
--   Both seeds are selected by message ranks. The layer defines Procedure C.1 using modular squaring, gcds, and trace splitting; Procedure C.3 by a bad-list scan and binary search; and the C.5 bad lists using roots and Gray-code scaled kernels. Rank recovery calls each bad-list computation at most once and rejects invalid or excessive ranks. It returns both additional message blocks.
--
--   **Formalization Note** The first representation bit is the constant coefficient and is the most significant integer-value bit. The mathematical good sets are not efficient machine instructions.
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), §2, PDF pp. 7–9 (printed pp. 5–7); Appendix C.2–C.3, PDF pp. 20–21 (printed pp. 18–19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Channel
import Definitions.Def_FuzzyExtractors_ImprovedJSFull_Presentation

set_option autoImplicit false

noncomputable section

namespace SeedRecyclingDL.Codes

abbrev FieldPresentation (F : Type) [Field F] [Fintype F] :=
  FuzzyExtractors.ImprovedJSFull.Presentation F

def value (u : Word) : ℕ := u.foldl (fun z a => 2 * z + a.val) 0

def binary (width z : ℕ) : Word := EditMulticoloring.Code.repr 2 width z

def allWords (n : ℕ) : List Word := EditMulticoloring.Code.words 2 n

def fromBits {F : Type} [Field F] [Fintype F] (P : FieldPresentation F) (u : Word) : F :=
  P.coordinates.symm (fun i =>
    ⟨((u[i.val]?).getD 0).val % P.p, Nat.mod_lt _ P.prime.pos⟩)

def fieldBits {F : Type} [Field F] [Fintype F] (P : FieldPresentation F) (a : F) : Word :=
  List.ofFn fun i : Fin P.k => ⟨(P.coordinates a i).val % 2, Nat.mod_lt _ (by decide)⟩

def fieldIndex {F : Type} [Field F] [Fintype F] (P : FieldPresentation F) (a : F) : ℕ :=
  value (fieldBits P a)

def orderedField {F : Type} [Field F] [Fintype F] (P : FieldPresentation F) : List F :=
  (allWords P.k).map (fromBits P)

def blockCount (m b : ℕ) : ℕ := (m + b - 1) / b

def payloadPolynomial {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (m : ℕ) (x : Word) : Polynomial F :=
  ∑ i ∈ Finset.range (blockCount m P.k),
    Polynomial.C (fromBits P ((x.drop (i * P.k)).take P.k)) * Polynomial.X ^ i

def project {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (r : ℕ) (a : F) : Word := (fieldBits P a).take r

abbrev Competitors := Word → Finset Word

def ValidCompetitors (m L : ℕ) (Γ : Competitors) : Prop :=
  1 ≤ m ∧ 1 ≤ L ∧ ∀ x : Word, x.length = m →
    (Γ x).card ≤ L ∧ ∀ x' ∈ Γ x, x'.length = m ∧ x' ≠ x

def ValidParameters (m L b r : ℕ) : Prop :=
  1 ≤ r ∧ r ≤ b ∧ 2 * L * blockCount m b ≤ 2 ^ b ∧ 2 * L ≤ 2 ^ r

def goodFirst {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (m : ℕ) (Γ : Competitors) (x : Word) : List F := by
  classical
  exact (orderedField P).filter fun a =>
    ∀ x' ∈ Γ x, (payloadPolynomial P m x).eval a ≠ (payloadPolynomial P m x').eval a

def goodSecond {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (m r : ℕ) (Γ : Competitors) (x : Word) (a : F) : List F := by
  classical
  exact (orderedField P).filter fun lam =>
    ∀ x' ∈ Γ x, project P r (lam * (payloadPolynomial P m x).eval a) ≠
      project P r (lam * (payloadPolynomial P m x').eval a)

/-- Equation (4). The theorem establishes that the default branches are never
used for source parameters and source messages. -/
def tag {F : Type} [Field F] [Fintype F] (P : FieldPresentation F)
    (m r : ℕ) (Γ : Competitors) (x sigma tau : Word) : Word :=
  let a := ((goodFirst P m Γ x)[value sigma]?).getD 0
  let lam := ((goodSecond P m r Γ x a)[value tau]?).getD 0
  fieldBits P a ++ fieldBits P lam ++ project P r (lam * (payloadPolynomial P m x).eval a)

def selectIndex (bad : List ℕ) (v : ℕ) : ℕ × ℕ :=
  let state := bad.foldl (fun st a => if st.2.2 then st else
    if a ≤ st.1 then (st.1 + 1, st.2.1 + 1, false)
    else (st.1, st.2.1 + 1, true)) (v - 1, 0, false)
  (state.1, state.2.1)

def lowerBoundSearch (bad : Array ℕ) (target : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, lo, _ => (lo, 0)
  | fuel + 1, lo, hi =>
    if lo ≥ hi then (lo, 0) else
    let mid := (lo + hi) / 2
    let next := if bad[mid]?.getD 0 < target then
      lowerBoundSearch bad target fuel (mid + 1) hi
      else lowerBoundSearch bad target fuel lo mid
    (next.1, next.2 + 1)

def rankIndex (bad : List ℕ) (a : ℕ) : Option ℕ × ℕ :=
  let found := lowerBoundSearch bad.toArray a (bad.length.log2 + 2) 0 bad.length
  (if bad[found.1]? = some a then none else some (a + 1 - found.1), found.2 + 1)


def TagCode (h N : ℕ) (R : Word → Word → Prop) (A : Word → Word) : Prop :=
  (∀ T : Word, T.length = h → (A T).length = N) ∧
  (∀ T T' : Word, T.length = h → T'.length = h → A T = A T' → T = T') ∧
  ∀ T T' : Word, T.length = h → T'.length = h → T ≠ T' → ¬ R (A T) (A T')

def encode {F : Type} [Field F] [Fintype F] (P : FieldPresentation F)
    (m r : ℕ) (Γ : Competitors) (A : Word → Word) (x sigma tau : Word) : Word :=
  x ++ A (tag P m r Γ x sigma tau)

def codeImage {F : Type} [Field F] [Fintype F] (P : FieldPresentation F)
    (m r : ℕ) (Γ : Competitors) (A : Word → Word) : Set Word :=
  {c | ∃ x sigma tau : Word, x.length = m ∧ sigma.length = P.k - 1 ∧
    tau.length = P.k - 1 ∧ c = encode P m r Γ A x sigma tau}

def log₂ (x : ℝ) : ℝ := Real.log x / Real.log 2

def redundancy (n : ℕ) (C : Set Word) : ℝ := (n : ℝ) - log₂ (C.ncard : ℝ)

/-- Appendix C.1, using modular squaring rather than enumerating the field. -/
def successiveSquares {F : Type} [Field F] (R : Polynomial F) : ℕ → Polynomial F → Polynomial F
  | 0, S => S % R
  | b + 1, S => successiveSquares R b ((S * S) % R)

def tracePolynomial {F : Type} [Field F] (b : ℕ) (G : Polynomial F) (beta : F) : Polynomial F :=
  ((List.range b).foldl (fun acc _ =>
    (acc.1 + acc.2, (acc.2 * acc.2) % G))
    ((0 : Polynomial F), (Polynomial.C beta * Polynomial.X) % G)).1

def splitFactors {F : Type} [Field F] (H : Polynomial F) (fs : List (Polynomial F)) :
    List (Polynomial F) := by
  classical
  exact fs.flatMap fun f => if f.natDegree ≤ 1 then [f] else
    [normalize (EuclideanDomain.gcd f H),
     normalize (EuclideanDomain.gcd f (H + 1))].filter (fun g => 0 < g.natDegree)

def procedureC1 {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (R : Polynomial F) : List F := by
  classical
  exact if R.natDegree = 0 then [] else
  let S := successiveSquares R P.k Polynomial.X
  let G := normalize (EuclideanDomain.gcd R (S - Polynomial.X))
  if G.natDegree = 0 then [] else
  let fs := (List.range P.k).foldl (fun fs i =>
    splitFactors (tracePolynomial P.k G (P.generator ^ i)) fs) [G]
  fs.filterMap fun f => if f.natDegree = 1 then some (-f.coeff 0 / f.coeff 1) else none

/-- C.5 raw roots, retaining repetitions until the sorting pass. -/
def rawBadFirst {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (m : ℕ) (x : Word) (competitors : List Word) : List F :=
  competitors.flatMap fun x' => procedureC1 P
    (payloadPolynomial P m x - payloadPolynomial P m x')

def sortFields {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (xs : List F) : List F := by
  classical
  exact (xs.mergeSort (fun a b => fieldIndex P a ≤ fieldIndex P b)).eraseDups

def badFirst {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (m : ℕ) (x : Word) (competitors : List Word) : List F :=
  sortFields P (rawBadFirst P m x competitors)

def grayKernel {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (r : ℕ) : List F :=
  (List.range (2 ^ (P.k - r))).map fun i =>
    fromBits P (List.replicate r 0 ++ binary (P.k - r) (Nat.xor i (i / 2)))

def rawBadSecond {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (m r : ℕ) (x : Word) (a : F) (competitors : List Word) : List F :=
  competitors.flatMap fun x' =>
    let delta := (payloadPolynomial P m x).eval a - (payloadPolynomial P m x').eval a
    (grayKernel P r).map fun z => delta⁻¹ * z

def badSecond {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (m r : ℕ) (x : Word) (a : F) (competitors : List Word) : List F :=
  sortFields P (rawBadSecond P m r x a competitors)


structure RecoveryReport where
  result : Option (Word × Word)
  firstCalls : ℕ
  secondCalls : ℕ

/-- B.2 rank recovery, instrumented at the actual C.5 bad-list calls. -/
def rankRecovery {F : Type} [Field F] [Fintype F] (P : FieldPresentation F)
    (m r : ℕ) (Γ : Competitors) (x T : Word) : RecoveryReport := by
  classical
  exact if T.length ≠ 2 * P.k + r then ⟨none, 0, 0⟩ else
    let a := fromBits P (T.take P.k)
    let lam := fromBits P ((T.drop P.k).take P.k)
    let B₁ := (badFirst P m x (Γ x).toList).map (fieldIndex P)
    match (rankIndex B₁ (fieldIndex P a)).1 with
    | none => ⟨none, 1, 0⟩
    | some v => if v = 0 ∨ 2 ^ (P.k - 1) < v then ⟨none, 1, 0⟩ else
      let B₂ := (badSecond P m r x a (Γ x).toList).map (fieldIndex P)
      match (rankIndex B₂ (fieldIndex P lam)).1 with
      | none => ⟨none, 1, 1⟩
      | some w => if w = 0 ∨ 2 ^ (P.k - 1) < w then ⟨none, 1, 1⟩ else
        ⟨some (binary (P.k - 1) (v - 1), binary (P.k - 1) (w - 1)), 1, 1⟩

def recoverRanks {F : Type} [Field F] [Fintype F] (P : FieldPresentation F)
    (m r : ℕ) (Γ : Competitors) (x T : Word) : Option (Word × Word) :=
  (rankRecovery P m r Γ x T).result

end SeedRecyclingDL.Codes


