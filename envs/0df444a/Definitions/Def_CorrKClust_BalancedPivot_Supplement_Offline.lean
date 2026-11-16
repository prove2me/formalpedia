-- Prove2me | Definitions.Def_CorrKClust_BalancedPivot_Supplement_Offline
-- name    : CorrKClust_BalancedPivot_Supplement_Offline
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:25:27.624756+00:00
-- url     : https://prove2.me/theorems/08d241eb-fad3-40fb-bc52-490214c73446
-- title:
--   Encoded offline algorithms and the strong-hardness language
-- statement:
--   A graph on $n$ vertices is written as its complete binary adjacency matrix, preceded by a self-delimiting binary size. Natural numbers use length-prefixed little-endian binary; cluster outputs list the encoded labels. An offline algorithm is a total binary-string transducer, with polynomial running time interpreted by the published Cook Turing-machine semantics. An approximation factor has the usual convention $\alpha\ge1$. Correctness requires an actual legal output, with disagreement cost bounded by the stated factor, for every graph (and every $1\le k\le n$ for the constrained algorithm).
--
--   The decision language contains exactly the codes of disjoint-clique graphs, positive $k$, and thresholds $T$ admitting a clustering $f$ with
--   $$\operatorname{Cost}_G(f)\le T.$$
--   The binary and unary versions encode $k,T$ in binary and unary respectively, while both write the graph explicitly. Unary hardness expresses strong hardness. The module decodes the published indexed 3-PARTITION language and expands each entry $a_i$ into an actual clique of $a_i$ consecutive vertices, using explicit cumulative block indices. Its threshold is $(mB^2-\sum_i a_i^2)/2$; the theorem separately requires the exact doubled-threshold identity, so truncated natural arithmetic cannot change a valid instance. Empty valid source instances map to a fixed YES-instance and invalid strings to a fixed NO-instance. These interfaces specify computation and the source reduction without an optimum oracle.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), §4 and Appendix A, p. 15

import Definitions.Def_CorrKClust_BalancedPivot_Instance
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KingTerrain_NPHard_Complexity
import Definitions.Def_TetrisHard_Rows_ThreePartition

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot.Supplement

/-- Length-prefixed binary natural numbers; little-endian bits, including a self-delimiting length. -/
def binaryNat (a : ℕ) : List Bool :=
  let bits := (Nat.digits 2 a).map (fun x => x == 1)
  List.replicate bits.length true ++ [false] ++ bits

def unaryNat (a : ℕ) : List Bool := List.replicate a true ++ [false]

/-- Explicit n by n adjacency matrix, including zero diagonal and symmetric entries. -/
def graphCode {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool :=
  binaryNat n ++ (List.ofFn fun u : Fin n =>
    List.ofFn fun v : Fin n => decide (G.Adj u v)).flatten

def offlineCode {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : List Bool :=
  binaryNat k ++ graphCode G

def labelsCode {n k : ℕ} (f : Fin n → Fin k) : List Bool :=
  (List.ofFn fun v => binaryNat (f v).val).flatten

/-- An actual polynomial-time string transducer giving an α-approximation on every graph. -/
def CCApprox (α : ℝ) (A : List Bool → List Bool) : Prop :=
  1 ≤ α ∧ CookPvsNP.PolyTimeComputable A ∧
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ f : Fin n → Fin n,
    A (graphCode G) = labelsCode f ∧ (cost G f : ℝ) ≤ α * optCC G

/-- Polynomial time on all strings, with one uniform program for all n and k. -/
def KApprox (α : ℝ) (A : List Bool → List Bool) : Prop :=
  CookPvsNP.PolyTimeComputable A ∧
  ∀ (n k : ℕ) (G : SimpleGraph (Fin n)), 0 < k → k ≤ n →
    ∃ f : Fin n → Fin k, A (offlineCode G k) = labelsCode f ∧
      (cost G f : ℝ) ≤ α * optK G k

/-- Threshold is binary in the ordinary language and unary in the strong-hardness language.
The graph is always explicit; unary k,T has size polynomial when k≤n and T≤n². -/
def decisionCode {n : ℕ} (unary : Bool) (G : SimpleGraph (Fin n)) (k T : ℕ) : List Bool :=
  (if unary then unaryNat k ++ unaryNat T else binaryNat k ++ binaryNat T) ++ graphCode G

def decisionLanguage (unary : Bool) : CookPvsNP.Lang Bool :=
  {w | ∃ (n k T : ℕ) (G : SimpleGraph (Fin n)), 0 < k ∧
    (∃ Q : Fin n → Fin n, IsCliquePartition G Q) ∧
    (∃ f : Fin n → Fin k, cost G f ≤ T) ∧ w = decisionCode unary G k T}

/-- Unary decoding used for the existing 3-PARTITION language; malformed words are rejected below. -/
def readUnary : List Bool → ℕ → List ℕ
  | [], _ => []
  | true :: xs, a => readUnary xs (a + 1)
  | false :: xs, a => a :: readUnary xs 0

def sourceInstance (w : List Bool) : TetrisHard.Rows.ThreePartition :=
  let a := readUnary w 0
  ⟨a.getD 0 0, a.getD 1 0, fun i => a.getD (i.val + 2) 0⟩

/-- Explicit expansion into individual vertices: no weighted or succinct graph encoding. -/
abbrev ReductionVertex (P : TetrisHard.Rows.ThreePartition) :=
  (i : Fin (3 * P.s)) × Fin (P.entry i)

/-- Consecutive blocks of sizes a₀,a₁,…; the first block containing v determines
its clique. This is explicit recursion, not a classically chosen enumeration. -/
def consecutiveGroup : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: as, v => if v < a then 0 else 1 + consecutiveGroup as (v - a)

def reductionGraph (P : TetrisHard.Rows.ThreePartition) :
    SimpleGraph (Fin (Fintype.card (ReductionVertex P))) :=
  cliqueGraph (fun v => consecutiveGroup (List.ofFn P.entry) v.val)

/-- The division is used only on valid positive instances. Theorem 6 also asserts the
exact equation 2T+Σa_i²=mB², excluding truncated subtraction or division artefacts. -/
def reductionThreshold (P : TetrisHard.Rows.ThreePartition) : ℕ :=
  (P.s * P.target ^ 2 - ∑ i, (P.entry i) ^ 2) / 2

/-- Empty valid source instances are YES; invalid words map to a fixed NO-instance. -/
def sourceReduction (w : List Bool) : List Bool :=
  let P := sourceInstance w
  if w = P.code ∧ P.Valid then
    if P.s = 0 then decisionCode true (⊥ : SimpleGraph (Fin 1)) 1 0
    else decisionCode true (reductionGraph P) P.s (reductionThreshold P)
  else decisionCode true (⊥ : SimpleGraph (Fin 2)) 1 0

end CorrKClust.BalancedPivot.Supplement


