-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P97
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P97
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T09:36:38.677418+00:00
-- url     : https://prove2.me/theorems/8c9549cd-0fb1-4956-b771-52adc7a4909d
-- title:
--   Definitions for A new inequality for the von Neumann entropy
-- statement:
--   The objects the formalized statements of *A new inequality for the von Neumann entropy* (arXiv:quant-ph/0406162) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FullRegister`: PDF pp.2–3: the complete tensor basis, with A,B,C,D numbered 0,1,2,3.
--   - `FourPartyState`: PDF pp.1–3: a normalized finite-dimensional four-party complex density operator. Dimension one is allowed, dimension zero is excluded, and no purity is assumed.
--   - `fourPartyReduction`: PDF p.2: the actual subsystem partial trace of the same joint matrix. This is a coordinate adapter to the frozen traceRight, allowing unequal local finite dimensions. Its empty subsystem has a singleton basis.
--   - `fourPartyEntropyBits`: PDF pp.1–2: base-two von Neumann entropy of the actual marginal, with 0 log 0 = 0.
--   - `entropyDifference`: PDF p.2: conditional entropy S(X|Y) = S(XY)-S(Y). Applications use disjoint groups of factors.
--   - `mutualValue`: PDF p.2: mutual information of disjoint groups of factors.
--   - `conditionalMutualValue`: PDF p.2: I(X;Z|Y), with the conditioning group as the last argument. All applications to states use three pairwise disjoint groups.
--   - `Constraints`: PDF p.3, Theorem 1: the three SSA saturation constraints; no block or recovery structure obtained in the proof is included as an assumption.
--   - `constraintValue`: PDF p.5, Remark 3: individual constraints in the order ABC, CAB, ADB.
--   - `subsetMask`: PDF p.6, table: the mask uses A as bit 0, B as bit 1, C as bit 2, D as bit 3. For every subset of these four labels the mask is between 0 and 15.
--   - `rayOne`: PDF p.6: ray I, in binary-mask order, with empty entry zero. The fallback cannot occur for a subset of Fin 4. This is a formal entropy vector, not a state.
--   - `rayTwo`: PDF p.6: ray II, in binary-mask order, with empty entry zero.
--   - `BasicInequalities`: PDF p.2, all five basic quantum inequalities, for every disjoint subsystem grouping (including empty groups). This is a linear constraint predicate on formal entropy vectors, not a claim that such a vector is entropic.
--   - `marginalAB3`: PDF p.5, Remark 4: actual AB marginal of a tripartite state, tensor-ordered A,(B,C).
--   - `marginalAC3`: PDF p.5, Remark 4: actual AC marginal of the same tripartite state.
-- source:
--   A new inequality for the von Neumann entropy, arXiv:quant-ph/0406162v1, https://arxiv.org/abs/quant-ph/0406162v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability

/-!
arXiv:quant-ph/0406162v1, Linden and Winter, PDF pp.1–7.
All entropies are in bits. Local dimensions are arbitrary positive integers.
Proposition 2 is recorded as reuse in items.json; Remark 3's unspecified generic
family and Conjecture 6 are deferred. No imported paper module is required.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P97

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2–3: the complete tensor basis, with A,B,C,D numbered 0,1,2,3. -/
abbrev FullRegister (dims : Fin 4 → ℕ) := (i : Fin 4) → Fin (dims i)

/-- PDF pp.1–3: a normalized finite-dimensional four-party complex density operator.
Dimension one is allowed, dimension zero is excluded, and no purity is assumed. -/
structure FourPartyState where
  dims : Fin 4 → ℕ
  dims_pos : ∀ i, 0 < dims i
  rho : Matrix (FullRegister dims) (FullRegister dims) ℂ
  density : IsDensityMatrix rho

/-- PDF p.2: the actual subsystem partial trace of the same joint matrix.
This is a coordinate adapter to the frozen traceRight, allowing unequal local
finite dimensions. Its empty subsystem has a singleton basis. -/
def fourPartyReduction {dims : Fin 4 → ℕ}
    (rho : Matrix (FullRegister dims) (FullRegister dims) ℂ) (s : Finset (Fin 4)) :
    Matrix ((i : {i : Fin 4 // i ∈ s}) → Fin (dims i.1))
      ((i : {i : Fin 4 // i ∈ s}) → Fin (dims i.1)) ℂ :=
  let join : (((i : {i : Fin 4 // i ∈ s}) → Fin (dims i.1)) ×
      ((i : {i : Fin 4 // i ∉ s}) → Fin (dims i.1))) → FullRegister dims :=
    fun x i => if h : i ∈ s then x.1 ⟨i, h⟩ else x.2 ⟨i, h⟩
  traceRight (fun x y => rho (join x) (join y))

/-- PDF pp.1–2: base-two von Neumann entropy of the actual marginal, with 0 log 0 = 0. -/
def fourPartyEntropyBits (q : FourPartyState) (s : Finset (Fin 4)) : ℝ :=
  vnEntropy (fourPartyReduction q.rho s)

/-- PDF p.2: conditional entropy S(X|Y) = S(XY)-S(Y).
Applications use disjoint groups of factors. -/
def entropyDifference (h : Finset (Fin 4) → ℝ) (x y : Finset (Fin 4)) : ℝ :=
  h (x ∪ y) - h y

/-- PDF p.2: mutual information of disjoint groups of factors. -/
def mutualValue (h : Finset (Fin 4) → ℝ) (x y : Finset (Fin 4)) : ℝ :=
  h x + h y - h (x ∪ y)

/-- PDF p.2: I(X;Z|Y), with the conditioning group as the last argument.
All applications to states use three pairwise disjoint groups. -/
def conditionalMutualValue (h : Finset (Fin 4) → ℝ) (x z y : Finset (Fin 4)) : ℝ :=
  h (x ∪ y) + h (y ∪ z) - h (x ∪ y ∪ z) - h y

local notation "A" => ({0} : Finset (Fin 4))
local notation "B" => ({1} : Finset (Fin 4))
local notation "C" => ({2} : Finset (Fin 4))
local notation "D" => ({3} : Finset (Fin 4))

/-- PDF p.3, Theorem 1: the three SSA saturation constraints; no block or recovery
structure obtained in the proof is included as an assumption. -/
def Constraints (h : Finset (Fin 4) → ℝ) : Prop :=
  conditionalMutualValue h A C B = 0 ∧ conditionalMutualValue h B C A = 0 ∧ conditionalMutualValue h A B D = 0

/-- PDF p.5, Remark 3: individual constraints in the order ABC, CAB, ADB. -/
def constraintValue (h : Finset (Fin 4) → ℝ) (i : Fin 3) : ℝ :=
  if i = 0 then conditionalMutualValue h A C B else if i = 1 then conditionalMutualValue h B C A else conditionalMutualValue h A B D

/-- PDF p.6, table: the mask uses A as bit 0, B as bit 1, C as bit 2, D as bit 3.
For every subset of these four labels the mask is between 0 and 15. -/
def subsetMask (s : Finset (Fin 4)) : ℕ := ∑ i ∈ s, 2 ^ i.val

/-- PDF p.6: ray I, in binary-mask order, with empty entry zero. The fallback
cannot occur for a subset of Fin 4. This is a formal entropy vector, not a state. -/
def rayOne (s : Finset (Fin 4)) : ℝ :=
  ([0, 3, 3, 4, 2, 3, 3, 4, 2, 3, 3, 4, 4, 3, 3, 2] : List ℝ).getD (subsetMask s) 0

/-- PDF p.6: ray II, in binary-mask order, with empty entry zero. -/
def rayTwo (s : Finset (Fin 4)) : ℝ :=
  ([0, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 6, 5, 5, 2] : List ℝ).getD (subsetMask s) 0

/-- PDF p.2, all five basic quantum inequalities, for every disjoint subsystem
grouping (including empty groups). This is a linear constraint predicate on formal
entropy vectors, not a claim that such a vector is entropic. -/
def BasicInequalities (h : Finset (Fin 4) → ℝ) : Prop :=
  h ∅ = 0 ∧
  (∀ x, 0 ≤ h x) ∧
  (∀ x y, Disjoint x y → 0 ≤ entropyDifference h x y + h x) ∧
  (∀ x y z, Disjoint x y → Disjoint x z → Disjoint y z →
    0 ≤ entropyDifference h z x + entropyDifference h z y) ∧
  (∀ x y, Disjoint x y → 0 ≤ mutualValue h x y) ∧
  (∀ x z y, Disjoint x z → Disjoint x y → Disjoint z y → 0 ≤ conditionalMutualValue h x z y)

/-- PDF p.5, Remark 4: actual AB marginal of a tripartite state, tensor-ordered A,(B,C). -/
def marginalAB3 {X Y Z : Type*} [Fintype Z]
    (rho : Matrix (X × (Y × Z)) (X × (Y × Z)) ℂ) : Matrix (X × Y) (X × Y) ℂ :=
  fun x y => ∑ z, rho (x.1, (x.2, z)) (y.1, (y.2, z))

/-- PDF p.5, Remark 4: actual AC marginal of the same tripartite state. -/
def marginalAC3 {X Y Z : Type*} [Fintype Y]
    (rho : Matrix (X × (Y × Z)) (X × (Y × Z)) ℂ) : Matrix (X × Z) (X × Z) ℂ :=
  fun x y => ∑ z, rho (x.1, (z, x.2)) (y.1, (z, y.2))

/-- Sanity: tracing a zero matrix yields a zero matrix, not a normalized state. -/
example {dims : Fin 4 → ℕ} (s : Finset (Fin 4)) :
    fourPartyReduction (0 : Matrix (FullRegister dims) (FullRegister dims) ℂ) s = 0 := by
  funext x y
  simp [fourPartyReduction, traceRight]

/-- Sanity: the conditional-entropy expression is the source's entropy difference. -/
example (h : Finset (Fin 4) → ℝ) : entropyDifference h A C = h (A ∪ C) - h C := rfl

/-- Sanity: ray I's C and CD entries reproduce the printed table. -/
example : rayOne C = 2 ∧ rayOne (C ∪ D) = 4 := by
  simp [rayOne, subsetMask, Finset.sum_insert, Finset.sum_singleton]
  <;> norm_num

/-- Sanity: ray II's ABC and total entries reproduce the printed table. -/
example : rayTwo (A ∪ B ∪ C) = 5 ∧ rayTwo (A ∪ B ∪ C ∪ D) = 2 := by
  simp [rayTwo, subsetMask, Finset.sum_insert, Finset.sum_singleton]
  <;> norm_num

end QAlgorithms.Papers.Independent.Intakethird100.P97


