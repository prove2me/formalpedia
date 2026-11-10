-- Prove2me | Definitions.Def_QuantumBipartiteTesting_Bipartiteness_FormalMoments
-- name    : QuantumBipartiteTesting_Bipartiteness_FormalMoments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:09:46.594748+00:00
-- url     : https://prove2.me/theorems/85fadeff-7d2d-4b21-a289-423be6b383b4
-- title:
--   Algebraic topology moments and formal acceptance functionals
-- statement:
--   For every connected component of a pattern, count the edges of each color. For a partition $L$ of the components, multiply the matching moments for all classes and colors, where
--   $$R_r(M,\ell)=\prod_{a=1}^{r}\frac{\ell}{M-(2a-1)\ell}.$$
--   Apply the partition-lattice Möbius coefficients, computed as signed refinement chains, and sum $\ell^{-v+|L|}f'_L$ over partitions to obtain $W_F$. The empty pattern has moment one.
--
--   Consistent response monomials receive their topology moment times the actual YES or NO signing probability. Inconsistent tables receive zero. Extend this functional linearly using the circuit's constructed canonical coefficients. Feasible acceptance is instead an average over the actual conditional sampling law.
--
--   **Declared reading.** The appendix's algebraic functional is used instead of identifying it with arbitrary graph output on overflow. At $N=M=4,\ell=2$, empty output on overflow gives a one-edge unconditional moment $1/8$, whereas the algebraic moment is $1/2$. No estimate comparing formal and feasible acceptance is built into this definition. Consistency uses the structural clause of Definition 3.6; it does not assert positive sampling probability at every parameter. A three-vertex two-color path cannot fit blocks of size two, although it is structurally consistent.
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Definition 3.7; (A.2)–(A.4), (A.10)–(A.14), PDF = printed page 15,30–33. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Sampling

namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Partition (k : ℕ) := {p : Fin k → Fin k → Bool // Equivalence (fun i j => p i j = true)}

instance (k : ℕ) : Fintype (Partition k) := inferInstance

def Refines {k : ℕ} (p r : Partition k) : Prop := ∀ i j, p.val i j = true → r.val i j = true

def Blocks {k : ℕ} (p : Partition k) : Finset (Finset (Fin k)) :=
  univ.image fun i => univ.filter fun j => p.val i j = true

/-- Signed refinement chains, including the direct chain for each strict comparable pair. -/
def Mobius {k : ℕ} (p r : Partition k) : ℤ :=
  if p = r then 1 else if Refines p r then
    ∑ S ∈ (univ.filter fun t : Partition k =>
      Refines p t ∧ Refines t r ∧ p ≠ t ∧ t ≠ r).powerset,
      if (∀ x ∈ S, ∀ y ∈ S, Refines x y ∨ Refines y x) then (-1 : ℤ) ^ (S.card + 1) else 0
  else 0

def MatchingMoment (r : ℕ) (M l : ℝ) : ℝ :=
  ∏ a ∈ range r, l / (M - (2*(a+1)-1 : ℕ)*l)

def ComponentAt {N colors : ℕ} (F : Finset (ColoredEdge N colors)) (i : Fin (Components F).card) :
    Finset (Fin N) := (Components F).toList[i.val]?.getD ∅

def ComponentColorCount {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (i : Fin (Components F).card) (j : Fin colors) : ℕ :=
  (F.filter fun e => e.1 ∈ ComponentAt F i ∧ e.2.2 = j).card

def PartitionMoment {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (p : Partition (Components F).card) (M l : ℝ) : ℝ :=
  ∏ S ∈ Blocks p, ∏ j : Fin colors, MatchingMoment (∑ i ∈ S, ComponentColorCount F i j) M l

def PartitionCorrection {N colors : ℕ} (F : Finset (ColoredEdge N colors))
    (p : Partition (Components F).card) (M l : ℝ) : ℝ :=
  ∑ r : Partition (Components F).card,
    if Refines r p then (Mobius r p : ℝ) * PartitionMoment F r M l else 0

/-- Equations (A.2)--(A.4); an algebraic functional, not an overflow-completed law. -/
def TopologyMoment {N colors : ℕ} (F : Finset (ColoredEdge N colors)) (M l : ℝ) : ℝ :=
  ∑ p : Partition (Components F).card,
    l ^ (-(Vertices F).card + (Blocks p).card : ℤ) * PartitionCorrection F p M l

abbrev GraphTable (N : ℕ) (colors : ℕ := 3) := ResponseTable (Address N colors) (Fin N × Bool)

def PatternOf {N colors : ℕ} (T : GraphTable N colors) : Finset (ColoredEdge N colors) :=
  T.val.biUnion fun az => match az.1.1 with
    | none => ∅
    | some u => {(min u az.2.1, max u az.2.1, az.1.2)}

def PatternSign {N colors : ℕ} (T : GraphTable N colors) (e : ColoredEdge N colors) : Bool :=
  decide (∃ az ∈ T.val, az.2.2 = true ∧ az.1.2 = e.2.2 ∧
    ((az.1.1 = some e.1 ∧ az.2.1 = e.2.1) ∨
     (az.1.1 = some e.2.1 ∧ az.2.1 = e.1)))

def ConsistentTable {N colors : ℕ} (T : GraphTable N colors) : Prop :=
  Consistent (PatternOf T) ∧ ∀ az ∈ T.val,
    LiftOracle (SignedResponse (PatternOf T) (PatternSign T)) az.1 = some az.2

def FormalMonomial {N colors : ℕ} (s : Signing) (T : GraphTable N colors) (M l : ℝ) : ℝ :=
  if ConsistentTable T then TopologyMoment (PatternOf T) M l *
    (match s with
     | .yes => SignProbYes (PatternOf T) (PatternSign T)
     | .no => SignProbNo (PatternOf T) (PatternSign T))
  else 0

def FormalAcceptance {N colors k w q : ℕ} (E : Encoding (Fin N × Bool) k)
    (A : Algorithm (Address N colors) k w q)
    (out : (Address N colors × Bits k) × Fin w → Bool) (s : Signing) (M l : ℝ) : ℝ :=
  ∑ T : GraphTable N colors, CanonicalCoeff E A out T * FormalMonomial s T M l

def FormalGap {N colors k w q : ℕ} (E : Encoding (Fin N × Bool) k)
    (A : Algorithm (Address N colors) k w q)
    (out : (Address N colors × Bits k) × Fin w → Bool) (M l : ℝ) : ℝ :=
  FormalAcceptance E A out .yes M l - FormalAcceptance E A out .no M l

def FeasibleGap {N colors k w q : ℕ} (E : Encoding (Fin N × Bool) k)
    (A : Algorithm (Address N colors) k w q)
    (out : (Address N colors × Bits k) × Fin w → Bool) (M l : ℕ) : ℝ :=
  FeasibleAcceptance E A out .yes M l - FeasibleAcceptance E A out .no M l

/-- A circuit, output event, and signing choice; all data are fixed before M and l. -/
structure FormalCircuit (N colors q : ℕ) where
  k : ℕ
  w : ℕ
  encoding : Encoding (Fin N × Bool) k
  algorithm : Algorithm (Address N colors) k w q
  output : (Address N colors × Bits k) × Fin w → Bool
  signing : Signing

def FormalCircuit.value {N colors q : ℕ} (A : FormalCircuit N colors q) (M l : ℝ) : ℝ :=
  FormalAcceptance A.encoding A.algorithm A.output A.signing M l

end
end QuantumBipartiteTesting.Bipartiteness


