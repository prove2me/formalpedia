-- Prove2me | Definitions.Def_QAlgorithms_Defs_WeightedDQI
-- name    : QAlgorithms_Defs_WeightedDQI
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:28.313076+00:00
-- url     : https://prove2.me/theorems/13eeaeb0-5d7f-43e9-aa1a-97383ec870a4
-- title:
--   WeightedDQI
-- statement:
--   WeightedDQI
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\WeightedDQI.lean

import Definitions.Def_QAlgorithms_Defs_FieldCodeGeometry
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.WeightedDQI

/-- Signed clause, +1 on L and -1 outside; 2605.10666 p.5 (2), p.30. -/
def clause {p : ℕ} (L : Finset (ZMod p)) (y : ZMod p) : ℝ :=
  if y ∈ L then 1 else -1

/-- Exhaustive disjoint nonempty weighted blocks; 2605.10666 pp.5–6. -/
structure BlockPartition (m N : ℕ) where
  blocks : Fin N → Finset (Fin m)
  nonempty : ∀ t, (blocks t).Nonempty
  disjoint : Pairwise fun t u => Disjoint (blocks t) (blocks u)
  exhaustive : ∀ i, ∃ t, i ∈ blocks t
  weights : Fin N → ℝ
  positive : ∀ t, 0 < weights t

/-- Block signed objective; 2605.10666 p.5 (5). -/
def blockObjective {p m n N : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod p))
    (L : Fin m → Finset (ZMod p)) (S : BlockPartition m N) (t : Fin N)
    (x : Fin n → ZMod p) : ℝ :=
  ∑ i ∈ S.blocks t, clause (L i) (B.mulVec x i)

/-- Weighted signed objective, not the satisfied-count; 2605.10666 pp.4–5 (1),(5). -/
def objective {p m n N : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod p))
    (L : Fin m → Finset (ZMod p)) (S : BlockPartition m N)
    (x : Fin n → ZMod p) : ℝ :=
  ∑ t, S.weights t * blockObjective B L S t x

/-- Polynomial-image vector; admissible states require IsState and totalDegree ≤ l;
2605.10666 p.5 (8), p.6. No implicit renormalization is performed. -/
def state {p m n N : ℕ} [NeZero p] (B : Matrix (Fin m) (Fin n) (ZMod p))
    (L : Fin m → Finset (ZMod p)) (S : BlockPartition m N)
    (P : MvPolynomial (Fin N) ℂ) : EuclideanSpace ℂ (Fin n → ZMod p) :=
  WithLp.toLp 2 fun x => MvPolynomial.eval (fun t => (blockObjective B L S t x : ℂ)) P

/-- Optimization over the full normalized total-degree state class;
2605.10666 pp.6,34,38. Constant polynomials witness nonemptiness; signed scores
are bounded by the total weighted block size. Attainment remains a theorem. -/
def optimalExpectation {p m n N : ℕ} [NeZero p]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (L : Fin m → Finset (ZMod p))
    (S : BlockPartition m N) (l : ℕ) : ℝ :=
  sSup {v | ∃ P : MvPolynomial (Fin N) ℂ, P.totalDegree ≤ l ∧
    IsState (state B L S P) ∧ v = ∑ x, prob (state B L S P) x * objective B L S x}

/-- Real density allocations in [0,1] with an inequality budget;
2605.10666 p.6 (10). The total length is positive. -/
def allocationSet {m N : ℕ} (S : BlockPartition m N) (_hm : 0 < m) (mu : ℝ) :
    Set (Fin N → ℝ) :=
  {a | (∀ t, 0 ≤ a t ∧ a t ≤ 1) ∧ ∑ t, ((S.blocks t).card : ℝ)/m*a t ≤ mu}

/-- Compact allocation variational value on nonnegative budgets;
2605.10666 p.6 (10), p.36. Zero allocation witnesses nonemptiness. -/
def variationalValue {m N : ℕ} (S : BlockPartition m N) (hm : 0 < m)
    (kappa mu : ℝ) (_hmu : 0 ≤ mu) : ℝ :=
  sSup ((fun a => ∑ t, ((S.blocks t).card : ℝ)/m*S.weights t*
    (kappa*a t+2*Real.sqrt (a t*(1-a t)))) '' allocationSet S hm mu)

/-- Nontrivial prime-field clause domain; 2605.10666 pp.6,30. -/
structure ClauseDomain where
  p : ℕ
  prime : p.Prime
  r : ℕ
  lower : 1 ≤ r
  upper : r < p

/-- Computed (mean, standard deviation, kappa); 2605.10666 pp.6,30 (59)–(60).
Subtraction is performed after conversion to real numbers. -/
def clauseParameters (D : ClauseDomain) : Fin 3 → ℝ :=
  ![2*(D.r : ℝ)/D.p-1, 2*Real.sqrt ((D.r : ℝ)*((D.p : ℝ)-D.r))/D.p,
    ((D.p : ℝ)-2*D.r)/Real.sqrt ((D.r : ℝ)*((D.p : ℝ)-D.r))]

/-- Rescaled centered clause; 2605.10666 pp.6,30 (59)–(60).
The cardinality condition is the normalization's source domain. -/
def centeredClause (D : ClauseDomain) (L : Finset (ZMod D.p))
    (_hL : L.card = D.r) (y : ZMod D.p) : ℝ :=
  (clause L y-clauseParameters D 0)/clauseParameters D 1

example {p : ℕ} (y : ZMod p) : clause ∅ y = -1 := by simp [clause]

example {p m n N : ℕ} [NeZero p] (B : Matrix (Fin m) (Fin n) (ZMod p))
    (L : Fin m → Finset (ZMod p)) (S : BlockPartition m N) : state B L S 0 = 0 := by
  ext x; simp [state]

example : clauseParameters ⟨2,by decide,1,by decide,by decide⟩ = ![0,1,0] := by
  ext i
  fin_cases i <;> norm_num [clauseParameters]


end QAlgorithms.WeightedDQI


