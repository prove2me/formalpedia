-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_UpperTester
-- name    : FiniteGroupTesting_LinearQuery_Supplement_UpperTester
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:18:22.017729+00:00
-- url     : https://prove2.me/theorems/ab06214e-d232-4469-9524-8e6ba1853bd8
-- title:
--   The complete adaptive two-sided Section 5 tester
-- statement:
--   For $n\ge2$ and $0<\epsilon<1/2$, put $\bar\epsilon=\max(\epsilon,n^{-2})$, $k=\lceil c_{\rm AR}\log(2n)\rceil$ and $\Lambda=\log(3g(n)n^{k+1})$. Fix $c_D=1/500$, $n_0=1500$, $\gamma=1/10000$, $C_L=100$, $C_A=2000000$, $C_P=1000$ before every input. Set
--   $$m=\left\lceil\sqrt{n\Lambda\log(1/\bar\epsilon)/\bar\epsilon}\right\rceil,\quad L=\left\lceil C_L(n/m)\log(1/\bar\epsilon)\right\rceil,$$
--   $$R_{\rm act}=\lceil C_A\Lambda/\bar\epsilon\rceil,\qquad R_{\rm prod}=\lceil C_P\Lambda/\bar\epsilon\rceil.$$
--   The expansion constant is one fixed classical choice from the numerical specification of published Theorem 2.3. The two fallback integers are one fixed choice from the numerical specification of published Theorem 3.1. The definitions assert no existence or correctness of these choices; those are obligations discharged by the published results in subsequent proofs. No Open theorem is imported into this definition file.
--
--   If $n<n_0$ or $m>c_Dn$, use the unchanged linear tester at $\bar\epsilon$, with its exact-small branch for $n=2,3$. Otherwise construct the dictionary, reject when it has fewer than $m/2$ distinct labels, and sample one common locator word. All candidates see the same fresh action sample list, and the same fresh product sample list, independent of setup and each other. Accept exactly when some candidate passes the equality and conductance filters, has at most $4\gamma\bar\epsilon R_{\rm act}$ action failures, and has at most $\bar\epsilon R_{\rm prod}/4$ product failures. Candidate filtering is evaluated offline at the final decision, so some runs perform samples after an early offline rejection would already be possible; their acceptance distribution is identical. Visible paths are interpreted for all candidates without new queries.
--
--   The two-sided predicate requires acceptance and far-input rejection at least $2/3$. The query predicate bounds every transcript on every table and every random execution. The nonfallback budget is
--   $$2k\lceil\log_2 n\rceil+m+R_{\rm act}(2+2L)+R_{\rm prod}(1+3L).$$
--   The detailed bound uses the exact printed logarithms, and the soft bound fixes a uniform exponent $3$. Between-query computation is unrestricted.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), pp. 13–14, 25–34, Sections 4–5, especially (5.1.3), (5.4.1), (8.23)

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_Candidates
import Definitions.Def_FiniteGroupTesting_LinearQuery_Tester

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

noncomputable section
attribute [local instance] Classical.propDecidable
open OracleRun

/-- The numerical choice predicate is the published expansion guarantee. No guarantee is
assumed: Theorem 2.3 supplies its inhabitation in proofs. This definition imports no Open theorem. -/
def ExpansionConstant (c : ℝ) : Prop :=
  0 < c ∧ ∀ (H : Type) [Group H] [Fintype H],
    (99/100 : ℝ) ≤ uniformProbability
      (fun a : Fin ⌈c * Real.log (Fintype.card H)⌉₊ → H => CayleyExpansion a spectralAccuracy)

def expansionConstant : ℝ := Classical.epsilon ExpansionConstant

/-- Fix two integers for the already defined linear program, using exactly the published
Theorem 3.1 specification. Choice is total; its validity is a proof obligation, not a field. -/
def LinearConstants (ab : ℕ × ℕ) : Prop :=
  ∃ C : ℝ, 0 < ab.1 ∧ 0 < ab.2 ∧ 0 < C ∧
    ∀ n : ℕ, 4 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1/2 →
      TestsGroups ε (sectionTester ab.1 ab.2 n ε) ∧
        ResourceBound (sectionTester ab.1 ab.2 n ε) (10 * n + (accuracyBudget n ε : ℝ))
          (C * ((n : ℝ) * Real.log n * Real.log (Real.log n) + Real.log n / ε))

def fallbackConstants : ℕ × ℕ := Classical.epsilon LinearConstants

def fallbackA : ℕ := fallbackConstants.1

def fallbackB : ℕ := fallbackConstants.2

def epsilonBar (n : ℕ) (ε : ℝ) : ℝ := max ε ((n : ℝ)⁻¹ ^ 2)

def generatorCount (n : ℕ) : ℕ := ⌈expansionConstant * Real.log (2 * n)⌉₊

def candidateLog (n : ℕ) : ℝ :=
  Real.log (3 * ((groupCount n : ℝ) * (n : ℝ) ^ (generatorCount n + 1)))

def dictionarySize (n : ℕ) (ε : ℝ) : ℕ :=
  ⌈Real.sqrt ((n : ℝ) * candidateLog n * Real.log (1 / epsilonBar n ε) / epsilonBar n ε)⌉₊

def locatorLength (n m : ℕ) (ε : ℝ) : ℕ :=
  ⌈100 * ((n : ℝ) / m) * Real.log (1 / epsilonBar n ε)⌉₊

def actionTrials (n : ℕ) (ε : ℝ) : ℕ := ⌈2000000 * candidateLog n / epsilonBar n ε⌉₊

def productTrials (n : ℕ) (ε : ℝ) : ℕ := ⌈1000 * candidateLog n / epsilonBar n ε⌉₊

def gamma : ℝ := 1 / 10000

def sampleFrom {n : ℕ} {α : Type} (xs : List α) (fallback : α) : OracleRun n α := do
  let i ← draw (xs.length - 1)
  pure (xs.getD i.val fallback)

def repeatRun {n : ℕ} {α : Type} (p : OracleRun n α) : ℕ → OracleRun n (List α)
  | 0 => pure []
  | q + 1 => do
      let x ← p
      let xs ← repeatRun p q
      pure (x :: xs)

def inverseList {n : ℕ} : List (Fin n) → OracleRun n (List (Fin n))
  | [] => pure []
  | s :: rest => do
      let t ← binaryPower s (n - 1)
      let ts ← inverseList rest
      pure (t :: ts)

structure ActionRecord (n k : ℕ) where
  x : Fin n
  j : Signed k
  y : Fin n
  z : Fin n
  hx : Option (Fin n × List (Signed k))
  hy : Option (Fin n × List (Signed k))

structure ProductRecord (n k : ℕ) where
  x : Fin n
  y : Fin n
  z : Fin n
  hx : Option (Fin n × List (Signed k))
  hy : Option (Fin n × List (Signed k))
  hz : Option (Fin n × List (Signed k))

def actionTrial {n k : ℕ} (first : Fin n) (sign : Signed k) (u : Signed k → Fin n)
    (D : List (Fin n)) (σ : List (Signed k)) : OracleRun n (ActionRecord n k) := do
  let x ← sampleFrom (List.ofFn fun i : Fin n => i) first
  let j ← sampleFrom ((Finset.univ : Finset (Signed k)).toList) sign
  let y ← ask x (u j)
  let z ← ask y (u (reverseSign j))
  let hx ← queryHit u D x σ
  let hy ← queryHit u D y σ
  pure ⟨x, j, y, z, hx, hy⟩

def productTrial {n k : ℕ} (first : Fin n) (u : Signed k → Fin n)
    (D : List (Fin n)) (σ : List (Signed k)) : OracleRun n (ProductRecord n k) := do
  let x ← sampleFrom (List.ofFn fun i : Fin n => i) first
  let y ← sampleFrom (List.ofFn fun i : Fin n => i) first
  let z ← ask x y
  let hx ← queryHit u D x σ
  let hy ← queryHit u D y σ
  let hz ← queryHit u D z σ
  pure ⟨x, y, z, hx, hy, hz⟩

def actionRecordGood {n k : ℕ} (c : MarkedCandidate n k) (ds : List (Fin n))
    (ξ : List (Signed k)) (r : ActionRecord n k) : Prop :=
  letI := candidateGroup c.1
  ∃ h, candidateLocator c ds ξ r.hx = some h ∧
    candidateLocator c ds ξ r.hy = some (h * signedMark c.2.2 r.j) ∧ r.z = r.x

def productRecordGood {n k : ℕ} (c : MarkedCandidate n k) (ds : List (Fin n))
    (ξ : List (Signed k)) (r : ProductRecord n k) : Prop :=
  letI := candidateGroup c.1
  ∃ h g, candidateLocator c ds ξ r.hx = some h ∧ candidateLocator c ds ξ r.hy = some g ∧
    candidateLocator c ds ξ r.hz = some (h * g)

/-- Every candidate sees exactly the same records; candidate enumeration has no oracle argument. -/
def candidateSurvives {n k : ℕ} (ε : ℝ) (ds : List (Fin n)) (ξ : List (Signed k))
    (actions : List (ActionRecord n k)) (products : List (ProductRecord n k))
    (c : MarkedCandidate n k) : Prop :=
  candidateConductance c ∧ equalityPattern ds (candidateWalk c ξ) ∧
  ((actions.filter fun r => decide (¬actionRecordGood c ds ξ r)).length : ℝ) ≤
    4 * gamma * ε * actions.length ∧
  ((products.filter fun r => decide (¬productRecordGood c ds ξ r)).length : ℝ) ≤
    ε * products.length / 4

/-- The complete Section 5 program. Offline processing is finite but its time is unrestricted. -/
def sublinearTester (n : ℕ) (ε : ℝ) : OracleRun n Bool :=
  if hn : 0 < n then
    let first : Fin n := ⟨0, hn⟩
    let m := dictionarySize n ε
    if n < 1500 ∨ (n : ℝ) / 500 < m then
      if n < 4 then exactSmallTester first else sectionTester fallbackA fallbackB n (epsilonBar n ε)
    else
      let k := generatorCount n
      if hk : 0 < k then do
        let sign : Signed k := (⟨0, hk⟩, false)
        let signs := (Finset.univ : Finset (Signed k)).toList
        let ss ← repeatRun (sampleFrom (List.ofFn fun i : Fin n => i) first) k
        let ts ← inverseList ss
        let u := fun j : Signed k => if j.2 then ts.getD j.1.val first else ss.getD j.1.val first
        let d₀ ← sampleFrom (List.ofFn fun i : Fin n => i) first
        let ξ ← repeatRun (sampleFrom signs sign) m
        let ds ← queryWalk u d₀ ξ
        if (ds.toFinset.card : ℝ) < (m : ℝ) / 2 then return false
        let σ ← repeatRun (sampleFrom signs sign) (locatorLength n m ε)
        let acts ← repeatRun (actionTrial first sign u ds σ) (actionTrials n ε)
        let prods ← repeatRun (productTrial first u ds σ) (productTrials n ε)
        return decide (∃ c ∈ markedCandidates n k,
          candidateSurvives (epsilonBar n ε) ds ξ acts prods c)
      else pure false
  else pure true

/-- Two-sided, in contrast to the base predicate's perfect completeness. -/
def TwoSided {n : ℕ} (ε : ℝ) (p : OracleRun n Bool) : Prop :=
  (∀ op : Table n, IsGroupLaw op → (2/3 : ℝ) ≤ probability op (· = true) p) ∧
  (∀ op : Table n, Far ε op → (2/3 : ℝ) ≤ probability op (· = false) p)

def QueryBound {n : ℕ} (p : OracleRun n Bool) (q : ℝ) : Prop :=
  ∀ (op : Table n) (r : Outcome n Bool), Executes op p r → (r.transcript.length : ℝ) ≤ q

def nonfallbackBudget (n : ℕ) (ε : ℝ) : ℝ :=
  let k := generatorCount n
  let m := dictionarySize n ε
  let L := locatorLength n m ε
  2 * k * ⌈Real.log n / Real.log 2⌉₊ + m +
    (actionTrials n ε : ℝ) * (2 + 2 * L) + (productTrials n ε : ℝ) * (1 + 3 * L)

/-- The detailed printed bound uses log n, not a padded arbitrary polylogarithm. -/
def detailedBound (n : ℕ) (ε : ℝ) : ℝ :=
  Real.sqrt ((n : ℝ) / epsilonBar n ε) * (Real.log n) ^ (3/2 : ℝ) *
    Real.sqrt (Real.log (1 / epsilonBar n ε)) + (Real.log n) ^ 3 / epsilonBar n ε

def softBound (d n : ℕ) (ε : ℝ) : ℝ :=
  (Real.sqrt ((n : ℝ) / ε) + 1 / ε) * (Real.log n + Real.log (1 / ε)) ^ d

end
end FiniteGroupTesting.LinearQuery.Supplement


