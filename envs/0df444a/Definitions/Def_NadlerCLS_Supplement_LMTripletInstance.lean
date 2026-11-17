-- Prove2me | Definitions.Def_NadlerCLS_Supplement_LMTripletInstance
-- name    : NadlerCLS_Supplement_LMTripletInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:54:24.125184+00:00
-- url     : https://prove2.me/theorems/1d1883eb-e963-4e55-895c-f6c406025856
-- title:
--   LARGE-MARGIN-TRIPLET-FOSP instances and answers
-- statement:
--   A **LARGE-MARGIN-TRIPLET-FOSP instance** has a positive embedding dimension $d_{\mathrm{emb}}$, a finite set $V$ of movable labels, two fixed rational pivots $A,B\in[0,1]^{d_{\mathrm{emb}}}$, and a finite list of weighted ordered triplets over $V\cup\{A,B\}$. Every weight is a positive rational. The common rational margin satisfies $\alpha\ge d_{\mathrm{emb}}$, and the requested rational accuracy satisfies $\varepsilon>0$.
--
--   With $q=d_{\mathrm{emb}}|V|$, a candidate answer is a rational point $z^*\in[0,1]^q$. On the box, the weighted hinge loss agrees with the quadratic polynomial
--
--   $$
--   \widetilde L(z)=\sum_t w_t\left(\|z_{i_t}-z_{j_t}\|_2^2-\|z_{i_t}-z_{k_t}\|_2^2+\alpha\right).
--   $$
--
--   The answer is valid exactly when
--
--   $$
--   \langle u-z^*,\nabla\widetilde L(z^*)\rangle\ge-\varepsilon
--   \qquad\text{for every }u\in[0,1]^q.
--   $$
--
--   This is Definition 3's $\varepsilon$-first-order stationarity condition. If $V=\varnothing$, then $q=0$ and the unique empty tuple is an exact FOSP.
--
--   **Formalization Note** The finite set $V$ is represented by `Fin v`, coordinates are 0-based, and ordered triplets are a list. The gradient coordinates are the derivatives of the canonical quadratic extension in the standard coordinate directions. Inputs and rational answers have explicit binary encodings.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Section 5, equation (5.1), Definition 3 and equation (5.2), pp.13–14

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics
import Definitions.Def_NadlerCLS_l1

set_option autoImplicit false

namespace NadlerCLS

namespace Supplement

open NetworkEquilibriumCLS.LinearNash

/-- A label in a large-margin triplet: a movable point, or one of the two fixed pivots `A`, `B`.
(Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256
1fcc5a02…6dc485, Section 5 and Definition 3, pp.13–14.) -/
inductive TripletPoint (v : ℕ) where
  | movable : Fin v → TripletPoint v
  | pivotA : TripletPoint v
  | pivotB : TripletPoint v
  deriving DecidableEq

/-- One ordered weighted triplet `(i_t,j_t,k_t)` from Definition 3. -/
structure WeightedTriplet (v : ℕ) where
  anchor : TripletPoint v
  near : TripletPoint v
  far : TripletPoint v
  weight : ℚ

/-- The finite rational data of a LARGE-MARGIN-TRIPLET-FOSP instance (Definition 3, pp.13–14).
There are `v` movable points in dimension `d`, two fixed rational pivots, a list of ordered
weighted triplets, a common margin `alpha`, and requested accuracy `epsilon`.

**Formalization Note** The finite set `V` is represented by `Fin v`, and coordinates are 0-based.
The optimization dimension is exactly `d * v`; hence `v = 0` gives `Fin 0`, the empty tuple. -/
structure LMTripletInstance where
  d : ℕ
  v : ℕ
  pivotA : Fin d → ℚ
  pivotB : Fin d → ℚ
  triplets : List (WeightedTriplet v)
  alpha : ℚ
  epsilon : ℚ

/-- The input conditions in Definition 3: positive embedding dimension, pivots in the box,
positive rational weights, `alpha ≥ d`, and positive requested accuracy. -/
def LMTripletInstance.Valid (I : LMTripletInstance) : Prop :=
  0 < I.d ∧
  (∀ j, 0 ≤ I.pivotA j ∧ I.pivotA j ≤ 1) ∧
  (∀ j, 0 ≤ I.pivotB j ∧ I.pivotB j ≤ 1) ∧
  (∀ t ∈ I.triplets, 0 < t.weight) ∧
  (I.d : ℚ) ≤ I.alpha ∧ 0 < I.epsilon

/-- The embedding assigned to a triplet label.  Movable embeddings are read from the flattened
vector in `[0,1]^(d*v)`; the two pivots are fixed instance data. -/
noncomputable def LMTripletInstance.embedding (I : LMTripletInstance)
    (z : Fin (I.d * I.v) → ℝ) (p : TripletPoint I.v) : Fin I.d → ℝ :=
  match p with
  | .movable i => fun j => z (finProdFinEquiv (j, i))
  | .pivotA => fun j => I.pivotA j
  | .pivotB => fun j => I.pivotB j

/-- Squared Euclidean distance between two embeddings. -/
def sqEmbeddingDist {d : ℕ} (a b : Fin d → ℝ) : ℝ :=
  ∑ j, (a j - b j) ^ 2

/-- The smooth quadratic expression `Δ_t(z)` from (5.1), before applying the hinge. -/
noncomputable def LMTripletInstance.delta (I : LMTripletInstance)
    (t : WeightedTriplet I.v) (z : Fin (I.d * I.v) → ℝ) : ℝ :=
  sqEmbeddingDist (I.embedding z t.anchor) (I.embedding z t.near) -
    sqEmbeddingDist (I.embedding z t.anchor) (I.embedding z t.far) + I.alpha

/-- The quadratic polynomial `L̃(z) = ∑_t w_t Δ_t(z)` agreeing with the weighted hinge loss
on the feasible box when `alpha ≥ d` (5.1 and the discussion before Definition 3, pp.13–14). -/
noncomputable def LMTripletInstance.smoothLoss (I : LMTripletInstance)
    (z : Fin (I.d * I.v) → ℝ) : ℝ :=
  (I.triplets.map fun t => (t.weight : ℝ) * I.delta t z).sum

/-- The coordinate gradient of a real function on a finite product, i.e. its derivative in the
standard coordinate direction.  This gives the Euclidean gradient coordinates while retaining
Mathlib's ordinary function-space norm. -/
noncomputable def coordinateGradient {q : ℕ} (f : (Fin q → ℝ) → ℝ)
    (z : Fin q → ℝ) (j : Fin q) : ℝ :=
  fderiv ℝ f z (fun k => if k = j then 1 else 0)

/-- The `epsilon`-FOSP condition (5.2), using the Euclidean gradient of the canonical quadratic
extension `smoothLoss`.  The universal comparison point ranges over the entire feasible box. -/
noncomputable def LMTripletInstance.IsFOSP (I : LMTripletInstance)
    (z : Fin (I.d * I.v) → ℚ) : Prop :=
  InCube (rpt z) ∧
  ∀ u : Fin (I.d * I.v) → ℝ, InCube u →
    -(I.epsilon : ℝ) ≤
      ∑ j, (u j - (z j : ℝ)) * coordinateGradient I.smoothLoss (rpt z) j

/-- Binary encoding of a triplet label. -/
def encTripletPoint {v : ℕ} : TripletPoint v → List Bool
  | .movable i => encNat i
  | .pivotA => encNat v
  | .pivotB => encNat (v + 1)

/-- Binary encoding of one weighted ordered triplet. -/
def encWeightedTriplet {v : ℕ} (t : WeightedTriplet v) : List Bool :=
  encTripletPoint t.anchor ++ encTripletPoint t.near ++ encTripletPoint t.far ++ encRat t.weight

/-- Binary encoding of Definition 3, including the two dimensions and the triplet count. -/
def encLMTriplet (I : LMTripletInstance) : List Bool :=
  encNat I.d ++ encNat I.v ++ encVector I.pivotA ++ encVector I.pivotB ++
    encNat I.triplets.length ++ I.triplets.flatMap encWeightedTriplet ++
    encRat I.alpha ++ encRat I.epsilon

/-- LARGE-MARGIN-TRIPLET-FOSP as a finite-string search problem.  Valid answers are rational
points of the exact box `[0,1]^(d*|V|)` satisfying the variational inequality (5.2). -/
noncomputable def largeMarginTripletFOSPSearch : SearchProblem where
  valid s := ∃ I : LMTripletInstance, I.Valid ∧ encLMTriplet I = s
  answer s t := ∃ I : LMTripletInstance, I.Valid ∧ encLMTriplet I = s ∧
    ∃ z : Fin (I.d * I.v) → ℚ, t = encVector z ∧ I.IsFOSP z

end Supplement

end NadlerCLS


