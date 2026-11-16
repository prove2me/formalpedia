-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_TranscriptModel
-- name    : FiniteGroupTesting_LinearQuery_Supplement_TranscriptModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:18:49.904914+00:00
-- url     : https://prove2.me/theorems/5bc7472b-2bd1-412c-acf0-883c829961b1
-- title:
--   Adaptive query trees, arbitrary randomization and hidden-copy transcripts
-- statement:
--   A deterministic depth-$t$ query tree either stops with a Boolean decision or chooses an ordered pair and branches on the oracle answer. It may repeat queries and stop at any node. A randomized tester is an arbitrary probability distribution on this finite tree space; no uniform-tape restriction or computation bound is imposed. Its completeness and soundness are at least $2/3$ for the existing same-carrier group property and distance.
--
--   A hidden operation on $V$ is encoded through a uniform injection into $[n]$, with a specified deterministic outside completion. When $|V|=n$ this is a uniform bijection; otherwise it is exactly a uniform subset followed by a uniform bijection. Full transcripts retain ordered queries, answers and the final decision. Total variation is
--   $$d_{\rm TV}(U,V)=\frac12\sum_{\tau}|\Pr[U=\tau]-\Pr[V=\tau]|,$$
--   summed over the finite set of attainable transcripts; every other transcript has probability zero.
--
--   The common-exponent families are $\prod_i(\mathbb F_{p_i})^{a_i}$ and $\prod_i(\mathbb F_{p_i})^{b_i}$ with distinct primes and positive ranks. Each additive field coordinate is represented by addition modulo $p_i$ on labels $0,\ldots,p_i-1$. The minimum primary-component size is the literal finite minimum of all $p_i^{a_i}$ and $p_i^{b_i}$. Its empty-list default is zero, but no theorem uses an empty family. The rank-$(3,2)$ and rank-$(2,3)$ groups are also named. The paper's outside label $1$ is label zero in the chosen indexing.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), pp. 12–13, Definition 2.1; pp. 35–40, Sections 6.1–6.2

import Definitions.Def_FiniteGroupTesting_LinearQuery_TableModel

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

noncomputable section
attribute [local instance] Classical.propDecidable

/-- All deterministic adaptive ordered-pair testers of depth at most t.
Stopping is allowed at every node; repeated queries are allowed. -/
def QueryTree (n : ℕ) : ℕ → Type
  | 0 => Bool
  | t + 1 => Bool ⊕ ((Fin n × Fin n) × (Fin n → QueryTree n t))

instance queryTreeFintype (n t : ℕ) : Fintype (QueryTree n t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype Bool)
  | succ t ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Bool ⊕ ((Fin n × Fin n) × (Fin n → QueryTree n t))))

abbrev Transcript (n : ℕ) := List ((Fin n × Fin n) × Fin n) × Bool

def runTree {n : ℕ} (op : Table n) : {t : ℕ} → QueryTree n t → Transcript n
  | 0, b => ([], b)
  | _ + 1, .inl b => ([], b)
  | _ + 1, .inr (xy, next) =>
      let z := op xy.1 xy.2
      let r := runTree op (next z)
      (((xy, z) :: r.1), r.2)

/-- Arbitrary probability masses on the finite tree space, not only uniform finite tapes.
Any randomized t-query implementation pushes its internal randomness to such a law. -/
def randomizedAcceptance {n t : ℕ} (μ : PMF (QueryTree n t)) (op : Table n) : ℝ :=
  ∑ T : QueryTree n t, (μ T).toReal * if (runTree op T).2 then 1 else 0

def RandomizedTester {n t : ℕ} (ε : ℝ) (μ : PMF (QueryTree n t)) : Prop :=
  (∀ op : Table n, IsGroupLaw op → (2/3 : ℝ) ≤ randomizedAcceptance μ op) ∧
  (∀ op : Table n, Far ε op → randomizedAcceptance μ op ≤ (1/3 : ℝ))

/-- Transport a hidden operation through an injection; outside its image squared use the
specified deterministic completion. This never assumes a group on all n labels. -/
def encodedTable {V : Type*} (op : V → V → V) {n : ℕ} (f : V ↪ Fin n)
    (outside : Table n) (x y : Fin n) : Fin n :=
  if hx : ∃ v, f v = x then
    if hy : ∃ v, f v = y then f (op (Classical.choose hx) (Classical.choose hy))
    else outside x y
  else outside x y

def zeroCompletion (n : ℕ) : Table n := fun x _ => if hn : 0 < n then ⟨0, hn⟩ else x

/-- Uniform injections are exactly a uniform subset followed by a uniform bijection.
When |V|=n they are the uniform bijections. -/
def encodingWeights {V : Type*} [Fintype V] (op : V → V → V) (n : ℕ)
    (outside : Table n) (table : Table n) : ℝ :=
  uniformProbability fun f : V ↪ Fin n => encodedTable op f outside = table

def transcriptMass {n t : ℕ} (T : QueryTree n t) (w : Table n → ℝ) (tr : Transcript n) : ℝ :=
  ∑ op : Table n, if runTree op T = tr then w op else 0

/-- Half the l1 distance on the entire (finite) attainable transcript space, including queries,
answers and the final stopping decision; all transcripts outside this image have mass zero. -/
def transcriptTV {n t : ℕ} (T : QueryTree n t) (u v : Table n → ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ tr ∈ (Finset.univ.image fun op : Table n => runTree op T),
    |transcriptMass T u tr - transcriptMass T v tr|

/-- Fin p is the additive coordinate labelling 0,...,p-1 of F_p, for prime p. -/
abbrev Primary {r : ℕ} (p d : Fin r → ℕ) := (i : Fin r) → Fin (d i) → Fin (p i)

def primaryAdd {r : ℕ} {p d : Fin r → ℕ} (x y : Primary p d) : Primary p d :=
  fun i j => x i j + y i j

def primaryMinimum {r : ℕ} (p a b : Fin r → ℕ) : ℕ :=
  ((List.ofFn fun i => p i ^ a i) ++ (List.ofFn fun i => p i ^ b i)).min?.getD 0

abbrev PairH (p q : ℕ) := (Fin 3 → Fin p) × (Fin 2 → Fin q)
abbrev PairK (p q : ℕ) := (Fin 2 → Fin p) × (Fin 3 → Fin q)

def pairAddH {p q : ℕ} (x y : PairH p q) : PairH p q := (x.1 + y.1, x.2 + y.2)
def pairAddK {p q : ℕ} (x y : PairK p q) : PairK p q := (x.1 + y.1, x.2 + y.2)

def ConsecutivePrimes (p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ ∀ l, p < l → l < q → ¬Nat.Prime l

end
end FiniteGroupTesting.LinearQuery.Supplement


