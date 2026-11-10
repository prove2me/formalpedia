-- Prove2me | Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces
-- name    : IntegerMatrixMortality_FixedImage_ScanInterfaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:32:51.385805+00:00
-- url     : https://prove2.me/theorems/fb9e95c4-eb4a-4678-9352-3b85c5fabdf2
-- title:
--   Marker scans, length guesses and recovery candidates
-- statement:
--   A marker-e scan deletes zero or more zeros followed by e, remaining in V throughout. Repeated scans are finite relational composition. In a comparison graph, a guessed prefix of length b ends at its first arrival at the first marker-one phase. Its length counts every zero deletion, including the exit deletion. A leading nonzero residue is specified after dividing by precisely a power of p.
--
--   For m∈{2,3} and strictly decreasing positive guesses r₁,…,rₘ₋₁<mQ, define
--
--   $$H=\sum_{j=1}^m p^{jQ}-\sum_{i=1}^{m-1}p^{r_i},\quad\tau=\frac H{1-H},\quad z=\frac\tau p.$$
--
--   Subtraction here is rational subtraction. Phase arrival for unrestricted words uses the six residue blocks, and first arrival excludes every positive proper prefix. Integer outer products, columns and row kernels provide the rank-one conversion interface. None of these definitions assumes successful recovery.
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Lemma C.3, PDF pp. 22–23 / printed pp. 20–21; (D.5)–(D.8), PDF pp. 27–29 / printed pp. 25–27; §3 and Appendix A, PDF pp. 5–6 and 15 / printed pp. 3–4 and 13

import Mathlib
import Definitions.Def_IntegerMatrixMortality_FixedImage_ConcreteModules

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage


/-- The first b generator actions choose the positive zero prefix; their first arrival at u1=3 ends the guess. -/
def ChosenPrefix (w : List GeneratorEdge) (b : ℕ) : Prop :=
  1 ≤ b ∧ b ≤ w.length ∧ FirstArrival (w.take b) 3 ∧
    (w[b-1]?).map GeneratorEdge.target = some 3

def CompletesWithGuess (p : ℕ) (M : InstructionModule) (b : ℕ)
    (x y : ProjectivePoint) : Prop :=
  ∃ w : List GeneratorEdge, w ≠ [] ∧ FirstArrival w M.exit ∧ ChosenPrefix w b ∧
    ValidWalk p M.edges M.entry x w M.exit y

/-- A marker scan deletes any number of zeros, then the prescribed marker. -/
def MarkerScan (p : ℕ) (e : ℤ) (x y : ProjectivePoint) : Prop :=
  ∃ a : ℕ, Valid p x ∧
    (∀ i ≤ a, Valid p ((deleteDigit p 0)^[i] x)) ∧
    y = deleteDigit p e ((deleteDigit p 0)^[a] x) ∧ Valid p y

def MarkerScans (p : ℕ) (e : ℤ) : ℕ → ProjectivePoint → ProjectivePoint → Prop
  | 0, x, y => x = y
  | k+1, x, y => ∃ z, MarkerScan p e x z ∧ MarkerScans p e k z y

/-- Exact valuation through a nonzero leading residue, avoiding a default valuation at zero. -/
def LeadingResidue (p : ℕ) (x : ℚ) (e : ℤ) : Prop :=
  ¬ (p : ℤ) ∣ e ∧ ∃ a : ℕ, HasResidue p (some (x / (p : ℚ)^a)) e

def recoveryH (p m Q : ℕ) (rs : List ℕ) : ℚ :=
  ((List.range m).map (fun j => (p : ℚ)^((j+1)*Q))).sum -
    (rs.map (fun r => (p : ℚ)^r)).sum

def recoveryCandidate (p m Q : ℕ) (rs : List ℕ) : ProjectivePoint :=
  let H := recoveryH p m Q rs
  some ((H / (1-H)) / (p : ℚ))

/-- Actual nonempty mixed words and projective prefix values, for unrestricted first arrivals. -/
def wordValues (w : List ZMat) (x : ProjectivePoint) : List ProjectivePoint :=
  w.scanl (fun z A => projectiveAction (rationalMatrix A) z) x

def InPhase (p q : ℕ) (x : ProjectivePoint) : Prop :=
  InResidues p (translate (-(6*(q : ℤ)+1)) x) delta

def FirstPhaseArrival (p q : ℕ) (w : List ZMat) (x : ProjectivePoint) : Prop :=
  w ≠ [] ∧ ∀ i : ℕ, 0 < i → i < w.length →
    ¬ InPhase p q (projectiveAction (rationalMatrix (wordMatrix (w.take i))) x)

def OuterProduct (u v : Fin 2 → ℤ) : ZMat := fun i j => u i * v j

def integerColumn (u : Fin 2 → ℤ) : QVec := fun i => (u i : ℚ)

def rowKernel (v : Fin 2 → ℤ) : Submodule ℚ QVec :=
  LinearMap.ker (Matrix.toLin' (fun (_ : Fin 1) (j : Fin 2) => (v j : ℚ)))


end IntegerMatrixMortality.FixedImage


