-- Prove2me | Definitions.Def_VehicleRoutingSurvey_Routing_Approximation
-- name    : VehicleRoutingSurvey_Routing_Approximation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:11:40.258316+00:00
-- url     : https://prove2.me/theorems/087ae0fa-467e-40c7-aad8-26b927b582d3
-- title:
--   Encoded minimization, approximation schemes and effective local search
-- statement:
--   A minimization problem specifies valid finite numeric input codes, feasible output codes and real objective values. Multiplicative guarantees compare an output with every feasible competitor. An approximation algorithm is a uniform Cook-model transducer. A fully polynomial scheme uses reciprocal tolerance 1/(k+1), written in unary so that polynomial input length is polynomial in inverse tolerance. Threshold languages include a rational threshold. Effective local search returns a strict improvement or correctly declares that no improving neighbor exists. Effective neighborhood generation lists all neighbors with lengths delimiting them. Equality of P and NP uses the same published Cook classes over every finite nonempty alphabet.
-- source:
--   Lenstra and Rinnooy Kan, Complexity of vehicle routing and scheduling problems, Econometric Institute Report 7919/O (1979), §4, pp. 6–7; Table 4

import Definitions.Def_VehicleRoutingSurvey_Routing_Encodings

namespace VehicleRoutingSurvey.Routing

/-- A general real-valued encoded minimization problem, independent of routing. -/
structure MinimizationProblem where
  valid : List ℕ → Prop
  feasible : List ℕ → List ℕ → Prop
  cost : List ℕ → List ℕ → ℝ

def HasSolution (P : MinimizationProblem) (x : List ℕ) : Prop :=
  P.valid x ∧ ∃ y, P.feasible x y

def NonnegativeProblem (P : MinimizationProblem) : Prop :=
  ∀ x y, P.valid x → P.feasible x y → 0 ≤ P.cost x y

def Approximation (P : MinimizationProblem) (ρ : ℝ)
    (f : List BinarySymbol → List BinarySymbol) : Prop :=
  CookPvsNP.PolyTimeComputable f ∧ ∀ x, HasSolution P x →
    ∃ y, f (binaryCode x) = binaryCode y ∧ P.feasible x y ∧
      ∀ z, P.feasible x z → (P.cost x y : ℝ) ≤ ρ * (P.cost x z : ℝ)

def precisionInput (x : List ℕ) (k : ℕ) : List BinarySymbol :=
  binaryCode (x.length :: x) ++ none :: List.replicate (k + 1) (some true)

/-- A single uniform machine, polynomial in instance bits and unary accuracy 1/ε.
The reciprocal tolerances 1/(k+1) recover every positive real tolerance by rounding up. -/
def HasFPTAS (P : MinimizationProblem) : Prop :=
  ∃ f : List BinarySymbol → List BinarySymbol,
    CookPvsNP.PolyTimeComputable f ∧ ∀ x, HasSolution P x → ∀ k : ℕ,
      ∃ y, f (precisionInput x k) = binaryCode y ∧ P.feasible x y ∧
        ∀ z, P.feasible x z →
          (P.cost x y : ℝ) ≤ (1 + 1 / ((k : ℝ) + 1)) * (P.cost x z : ℝ)

def thresholdCode (x : List ℕ × ℚ) : List ℕ :=
  x.1.length :: x.1 ++ rationalCode x.2

def ThresholdYes (P : MinimizationProblem) (x : List ℕ × ℚ) : Prop :=
  P.valid x.1 ∧ ∃ y, P.feasible x.1 y ∧ P.cost x.1 y ≤ (x.2 : ℝ)

def ClassesEqual : Prop :=
  ∀ (Alphabet : Type) [Fintype Alphabet] [Nonempty Alphabet],
    CookPvsNP.P Alphabet = CookPvsNP.NP Alphabet

/-- Effective local search returns either a strictly better neighbor or a correct
certificate that none exists. Only each invocation is polynomial-time. -/
def EffectiveLocalSearch (P : MinimizationProblem)
    (neighbor : List ℕ → List ℕ → List ℕ → Prop)
    (step : List BinarySymbol → List BinarySymbol) : Prop :=
  CookPvsNP.PolyTimeComputable step ∧
  ∀ x y, P.valid x → P.feasible x y →
    (step (binaryCode (x.length :: x ++ y)) = binaryCode [0] ∧
      ∀ z, P.feasible x z → neighbor x y z → P.cost x y ≤ P.cost x z) ∨
    ∃ z, step (binaryCode (x.length :: x ++ y)) = binaryCode (1 :: z) ∧
      P.feasible x z ∧ neighbor x y z ∧ P.cost x z < P.cost x y

def LocalOptimum (P : MinimizationProblem)
    (neighbor : List ℕ → List ℕ → List ℕ → Prop) (x y : List ℕ) : Prop :=
  P.feasible x y ∧ ∀ z, P.feasible x z → neighbor x y z → P.cost x y ≤ P.cost x z

/-- A uniform polynomial-time listing, with unambiguous lengths for each neighbor. -/
def EffectiveNeighborhood (P : MinimizationProblem)
    (neighbor : List ℕ → List ℕ → List ℕ → Prop) : Prop :=
  ∃ f : List BinarySymbol → List BinarySymbol, CookPvsNP.PolyTimeComputable f ∧
    ∀ x y, P.valid x → P.feasible x y → ∃ zs : List (List ℕ),
      f (binaryCode (x.length :: x ++ y)) = binaryCode (zs.flatMap (fun z => z.length :: z)) ∧
      ∀ z, z ∈ zs ↔ P.feasible x z ∧ neighbor x y z

end VehicleRoutingSurvey.Routing


