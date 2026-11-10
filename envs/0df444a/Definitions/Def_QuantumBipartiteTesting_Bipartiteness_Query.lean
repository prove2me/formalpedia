-- Prove2me | Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Query
-- name    : QuantumBipartiteTesting_Bipartiteness_Query
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:07:13.991625+00:00
-- url     : https://prove2.me/theorems/f4de6ecb-e9f0-4303-9081-09902e930c0a
-- title:
--   Graph testers, general signed multigraphs, and canonical circuit polynomials
-- statement:
--   The published finite query-algorithm model supplies a unit start vector and input-independent complex unitaries. Answers occupy arbitrary full bit-string registers, with an injective binary encoding sending null to zero. The oracle applies XOR, including on unused answer-register strings. Acceptance is the actual squared-amplitude probability of a fixed output event.
--
--   A bipartiteness tester accepts each bipartite graph with probability at least $2/3$ and rejects each graph at edit distance at least $\varepsilon Nd$ with probability at least $2/3$, for every valid neighbor ordering. General loopless signed multigraphs have distinct edge identifiers and packed port representations. Their balance testers quantify over every such graph and representation, rather than just the hard distribution.
--
--   A canonical monomial is a compatible partial response table without null responses. Its coefficient is the finite inclusion–exclusion sum of circuit acceptance on its subwords, with all unspecified responses set to null. This constructs the polynomial from the circuit without assuming its degree or correctness.
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), §2.1.2, Definitions 2.2–2.3 and §2.4, PDF = printed page 8–11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_SignedGraphs

namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Bits (k : ℕ) := Fin k → ZMod 2

structure Encoding (S : Type*) (k : ℕ) where
  code : Option S → Bits k
  injective : Function.Injective code
  null : code none = 0

abbrev Algorithm (I : Type*) [Fintype I] [DecidableEq I] (k w q : ℕ) :=
  QAlgorithms.QueryAlg I (Bits k) (Fin w) q

def Accept {I S : Type*} [Fintype I] [DecidableEq I] {k w q : ℕ}
    (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (O : I → Option S) : ℝ :=
  A.outputProb (QAlgorithms.xorOracle (E.code ∘ O)) out true

abbrev Address (N d : ℕ) := Option (Fin N) × Fin d

def LiftOracle {N d : ℕ} {S : Type*} (O : Fin N × Fin d → Option S) :
    Address N d → Option S :=
  fun a => match a.1 with | none => none | some u => O (u,a.2)

def BipartiteTester {N d k w q : ℕ} (ε : ℝ) (E : Encoding (Fin N) k)
    (A : Algorithm (Address N d) k w q)
    (out : (Address N d × Bits k) × Fin w → Bool) : Prop :=
  ∀ G : Finset (Edge N), IsGraph G → DegreeBound d G →
    ∀ O : Fin N × Fin d → Option (Fin N), Represents G O →
      (Bipartite G → 2/3 ≤ Accept E A out (LiftOracle O)) ∧
      (Far d ε G → Accept E A out (LiftOracle O) ≤ 1/3)

/-- An arbitrary finite loopless signed multigraph, with edge identifiers retaining multiplicity. -/
structure SignedGraph (N m : ℕ) where
  u : Fin m → Fin N
  v : Fin m → Fin N
  loopless : ∀ e, u e ≠ v e
  sign : Fin m → Bool

def SignedGraph.Balanced {N m : ℕ} (G : SignedGraph N m) : Prop :=
  ∃ x : Fin N → Bool, ∀ e, xor (x (G.u e)) (x (G.v e)) = G.sign e

def SignedGraph.Frustration {N m : ℕ} (G : SignedGraph N m) : ℕ :=
  sInf {j | ∃ x : Fin N → Bool, j = (univ.filter
    fun e => xor (x (G.u e)) (x (G.v e)) ≠ G.sign e).card}

/-- Port assignment is representation data and must enumerate each incident edge exactly once. -/
def SignedGraph.Ports {N m d : ℕ} (G : SignedGraph N m)
    (P : Fin N × Fin d → Option (Fin m)) : Prop :=
  (∀ u i e, P (u,i) = some e → G.u e = u ∨ G.v e = u) ∧
  (∀ u e, (G.u e = u ∨ G.v e = u) ↔ ∃! i, P (u,i) = some e) ∧
  (∀ u i, P (u,i) = none ↔
    (univ.filter fun e => G.u e = u ∨ G.v e = u).card ≤ i.val)

def SignedGraph.Oracle {N m d : ℕ} (G : SignedGraph N m)
    (P : Fin N × Fin d → Option (Fin m)) (a : Fin N × Fin d) :
    Option (Fin N × Bool) :=
  (P a).map fun e => (if G.u e = a.1 then G.v e else G.u e, G.sign e)

def BalanceTester {N d k w q : ℕ} (ε : ℝ) (E : Encoding (Fin N × Bool) k)
    (A : Algorithm (Address N d) k w q)
    (out : (Address N d × Bits k) × Fin w → Bool) : Prop :=
  ∀ m (G : SignedGraph N m) (P : Fin N × Fin d → Option (Fin m)), G.Ports P →
    (G.Balanced → 2/3 ≤ Accept E A out (LiftOracle (G.Oracle P))) ∧
    (ε * N * d ≤ (G.Frustration : ℝ) →
      Accept E A out (LiftOracle (G.Oracle P)) ≤ 1/3)

/-- Canonical monomial: a partial response table, with nulls eliminated. -/
def ResponseTable (I S : Type*) [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S] :=
  {T : Finset (I × S) // ∀ a z z', (a,z) ∈ T → (a,z') ∈ T → z = z'}

instance {I S : Type*} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S] :
    Fintype (ResponseTable I S) := by
  unfold ResponseTable
  infer_instance

/-- A total response word with the prescribed entries and null elsewhere. -/
def TableWord {I S : Type*} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (T : Finset (I × S)) (a : I) : Option S :=
  if h : ∃ z, (a,z) ∈ T then some h.choose else none

/-- Unique response-table interpolation coefficients, computed from the actual circuit. -/
def CanonicalCoeff {I S : Type*} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (T : ResponseTable I S) : ℝ :=
  ∑ U ∈ T.val.powerset, (-1 : ℝ) ^ (T.val.card - U.card) * Accept E A out (TableWord U)

def TableMonomial {I S : Type*} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (T : ResponseTable I S) : MvPolynomial (I × S) ℝ :=
  ∏ az ∈ T.val, MvPolynomial.X az

def CanonicalPolynomial {I S : Type*} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    {k w q : ℕ} (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) : MvPolynomial (I × S) ℝ :=
  ∑ T : ResponseTable I S, MvPolynomial.C (CanonicalCoeff E A out T) * TableMonomial T

def Indicators {I S : Type*} [DecidableEq S] (O : I → Option S) (az : I × S) : ℝ :=
  if O az.1 = some az.2 then 1 else 0

end
end QuantumBipartiteTesting.Bipartiteness


