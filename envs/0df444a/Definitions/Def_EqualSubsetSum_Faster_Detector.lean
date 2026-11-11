-- Prove2me | Definitions.Def_EqualSubsetSum_Faster_Detector
-- name    : EqualSubsetSum_Faster_Detector
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:23:59.966881+00:00
-- url     : https://prove2.me/theorems/a60d8694-4c6e-48ea-908e-add64f956c41
-- title:
--   The sampled-correction detector of §4.1: position types, conflict sets, truncated counts U, labels, sampling, correction pool, N̂ and N
-- statement:
--   Positions have one of three **types**: at a *normal* position the first list uses the digits $\{0,1\}$ and the second $\{0,1,2\}$; at a *transposed* position the first uses $\{0,1,2\}$ and the second $\{0,1\}$; at an *auxiliary* position the first is fixed to $1$ and the second uses $\{0,1,2\}$. The lists $A',B'$ consist of distinct vectors; $y\in\mathbb Z^n$ are the weights and $a\cdot y$ is the key.
--
--   - **Conflict sets:** $X(a)=\{i \text{ normal}: a_i=0\}\cup\{i\text{ transposed}: a_i=2\}$, $Y(b)=\{i\text{ normal}: b_i=2\}\cup\{i\text{ transposed}: b_i=0\}$, and $c(a,b)=|X(a)\cap Y(b)|$.
--   - $(a,b)$ is **valid** if $a\ne b$, $a\cdot y=b\cdot y$ and $a-b\in\{-1,0,1\}^n$.
--   - $f_d(c)=\sum_{q=0}^{d}(-1)^q\binom cq$, and
--   $$U(a)=\sum_{b\in B',\ b\cdot y=a\cdot y} f_d(c(a,b))\;-\;[a\in B'] .$$
--   - **Labels:** $a\in A'$ outputs $(a\cdot y,J)$ for every $j$-subset $J\subseteq X(a)$; $b\in B'$ outputs $(b\cdot y,J)$ for every $j$-subset $J\subseteq Y(b)$. The **shared labels** are those output by some record of each list.
--   - $u$ is the least nonnegative integer with $\binom{d+1}{j}<32n\,2^u$ (taken as $0$ if none exists, which happens only for $n=0$), and $\omega=2^{-u}$.
--   - A **sampling outcome** keeps or drops each shared label; its law is the product of independent Bernoulli($\omega$) choices (keep with probability $\omega$).
--   - A pair $(a,b)\in A'\times B'$ is **reported** if some kept label is output by both; the **correction pool** $E$ is the set of reported pairs with $c(a,b)>d$.
--   - $\hat N(a)=U(a)-\sum_{b\in B',(a,b)\in E}\binom{c(a,b)-1}{d}$ (eq. (4)), and $N(a)$ is the number of $b\in B'$ such that $(a,b)$ is valid.
--
--   **Formalization Note.** Lists of distinct vectors are `Finset (Fin n → ℤ)`, so a record is its vector. $U(a)$ is defined as the value the graded counting circuit of §4.1 computes (the circuit identity guarantees they agree); the circuit itself is not modelled.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), pp. 14-15, §2.4; pp. 21-23, §4.1

import Mathlib
import Definitions.Def_EqualSubsetSum_Faster_Problem

namespace EqualSubsetSum.Faster

open Classical

/-! The objects of the sampled-correction detector (§2.4, pp. 14–15, and §4.1, pp. 21–23).
Lists of distinct vectors are `Finset (Fin n → ℤ)`, so a record is identified with its vector. -/

/-- The three position types of §2.4. -/
inductive PosType where
  /-- first list digits `{0,1}`, second list digits `{0,1,2}` -/
  | normal
  /-- first list digits `{0,1,2}`, second list digits `{0,1}` -/
  | transposed
  /-- first list fixed to `1`, second list digits `{0,1,2}` -/
  | auxiliary
  deriving DecidableEq

/-- The digits the first list may use at a position of the given type. -/
def FirstDigitOK : PosType → ℤ → Prop
  | .normal, v => v = 0 ∨ v = 1
  | .transposed, v => v = 0 ∨ v = 1 ∨ v = 2
  | .auxiliary, v => v = 1

/-- The digits the second list may use at a position of the given type. -/
def SecondDigitOK : PosType → ℤ → Prop
  | .normal, v => v = 0 ∨ v = 1 ∨ v = 2
  | .transposed, v => v = 0 ∨ v = 1
  | .auxiliary, v => v = 0 ∨ v = 1 ∨ v = 2

/-- The conflict set `X(a) = {i normal : aᵢ = 0} ∪ {i transposed : aᵢ = 2}` of a first-list vector. -/
def confX {n : ℕ} (τ : Fin n → PosType) (a : Fin n → ℤ) : Finset (Fin n) :=
  Finset.univ.filter fun i => (τ i = .normal ∧ a i = 0) ∨ (τ i = .transposed ∧ a i = 2)

/-- The conflict set `Y(b) = {i normal : bᵢ = 2} ∪ {i transposed : bᵢ = 0}` of a second-list vector. -/
def confY {n : ℕ} (τ : Fin n → PosType) (b : Fin n → ℤ) : Finset (Fin n) :=
  Finset.univ.filter fun i => (τ i = .normal ∧ b i = 2) ∨ (τ i = .transposed ∧ b i = 0)

/-- `c(a, b) = |X(a) ∩ Y(b)|`, the number of conflicts of the pair. -/
def conflicts {n : ℕ} (τ : Fin n → PosType) (a b : Fin n → ℤ) : ℕ :=
  (confX τ a ∩ confY τ b).card

/-- `(a, b)` is a *valid pair* for `y`: `a ≠ b`, `a · y = b · y`, `a - b ∈ {-1, 0, 1}ⁿ`. -/
def IsValidPair {n : ℕ} (y a b : Fin n → ℤ) : Prop :=
  a ≠ b ∧ weightedSum a y = weightedSum b y ∧
    ∀ i, a i - b i = -1 ∨ a i - b i = 0 ∨ a i - b i = 1

/-- The truncated alternating sum `f_d(c) = ∑_{q=0}^{d} (-1)^q (c choose q)` of eq. (3). -/
def truncAlt (d c : ℕ) : ℤ := ∑ q ∈ Finset.range (d + 1), (-1) ^ q * (c.choose q : ℤ)

/-- `U(a)`: the sum of `f_d(c(a, b))` over the records `b ∈ B'` with the same key as `a`, minus
one if the vector `a` itself occurs in `B'` (§4.1, p. 22). This is the value the graded counting
circuit computes. -/
noncomputable def upperCount {n : ℕ} (τ : Fin n → PosType) (y : Fin n → ℤ) (d : ℕ)
    (B' : Finset (Fin n → ℤ)) (a : Fin n → ℤ) : ℤ :=
  (∑ b ∈ B'.filter (fun b => weightedSum b y = weightedSum a y), truncAlt d (conflicts τ a b)) -
    (if a ∈ B' then 1 else 0)

/-- The labels `(a · y, J)`, `J ⊆ X(a)`, `|J| = j`, output by a first-list record. -/
noncomputable def labelsA {n : ℕ} (τ : Fin n → PosType) (y : Fin n → ℤ) (j : ℕ)
    (a : Fin n → ℤ) : Finset (ℤ × Finset (Fin n)) :=
  ((confX τ a).powersetCard j).image fun J => (weightedSum a y, J)

/-- The labels `(b · y, J)`, `J ⊆ Y(b)`, `|J| = j`, output by a second-list record. -/
noncomputable def labelsB {n : ℕ} (τ : Fin n → PosType) (y : Fin n → ℤ) (j : ℕ)
    (b : Fin n → ℤ) : Finset (ℤ × Finset (Fin n)) :=
  ((confY τ b).powersetCard j).image fun J => (weightedSum b y, J)

/-- The labels that occur in both lists; each of them is kept or dropped by the sampling. -/
noncomputable def sharedLabels {n : ℕ} (τ : Fin n → PosType) (y : Fin n → ℤ) (j : ℕ)
    (A' B' : Finset (Fin n → ℤ)) : Finset (ℤ × Finset (Fin n)) :=
  A'.biUnion (labelsA τ y j) ∩ B'.biUnion (labelsB τ y j)

/-- `u`: the least nonnegative integer with `(d+1 choose j) < 32 n 2^u` (`0` if there is none,
which happens only for `n = 0`). -/
noncomputable def samplingExponent (n d j : ℕ) : ℕ :=
  sInf {u : ℕ | (d + 1).choose j < 32 * n * 2 ^ u}

/-- The sampling probability `ω = 2^{-u}`, an element of `[0, 1]`. -/
noncomputable def samplingProb (n d j : ℕ) : unitInterval :=
  ⟨(1 / 2 : ℝ) ^ samplingExponent n d j,
    ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩⟩

/-- The law of the sampling outcome: each label of `S` is kept (`true`) independently with
probability `p` (a product of Bernoulli laws giving mass `p` to `true`, `1 - p` to `false`). -/
noncomputable def keepMeasure {n : ℕ} (S : Finset (ℤ × Finset (Fin n))) (p : unitInterval) :
    MeasureTheory.Measure (S → Bool) :=
  MeasureTheory.Measure.pi fun _ => ProbabilityTheory.bernoulliMeasure true false p

/-- Under the sampling outcome `keep`, the pair `(a, b)` is *reported*: some kept label is shared
by `a` (from the first list) and `b` (from the second list). -/
def Reported {n : ℕ} (τ : Fin n → PosType) (y : Fin n → ℤ) (j : ℕ) {S : Finset (ℤ × Finset (Fin n))}
    (keep : S → Bool) (a b : Fin n → ℤ) : Prop :=
  ∃ ℓ : S, keep ℓ = true ∧ (ℓ : ℤ × Finset (Fin n)) ∈ labelsA τ y j a ∧
    (ℓ : ℤ × Finset (Fin n)) ∈ labelsB τ y j b

/-- The correction pool `E`: the reported pairs of `A' × B'` with more than `d` conflicts, each once. -/
noncomputable def correctionPool {n : ℕ} (τ : Fin n → PosType) (y : Fin n → ℤ) (d j : ℕ)
    (A' B' : Finset (Fin n → ℤ)) (keep : sharedLabels τ y j A' B' → Bool) :
    Finset ((Fin n → ℤ) × (Fin n → ℤ)) :=
  (A' ×ˢ B').filter fun ab => Reported τ y j keep ab.1 ab.2 ∧ d < conflicts τ ab.1 ab.2

/-- The corrected count `N̂(a) = U(a) - ∑_{b ∈ B', (a,b) ∈ E} (c(a,b) - 1 choose d)` of eq. (4). -/
noncomputable def correctedCount {n : ℕ} (τ : Fin n → PosType) (y : Fin n → ℤ) (d j : ℕ)
    (A' B' : Finset (Fin n → ℤ)) (keep : sharedLabels τ y j A' B' → Bool) (a : Fin n → ℤ) : ℤ :=
  upperCount τ y d B' a -
    ∑ b ∈ B', if (a, b) ∈ correctionPool τ y d j A' B' keep then
      ((conflicts τ a b - 1).choose d : ℤ) else 0

/-- `N(a)`: the number of valid partners of `a` in `B'`. -/
noncomputable def partnerCount {n : ℕ} (y : Fin n → ℤ) (B' : Finset (Fin n → ℤ))
    (a : Fin n → ℤ) : ℕ :=
  (B'.filter fun b => IsValidPair y a b).card

end EqualSubsetSum.Faster


