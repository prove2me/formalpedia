-- Prove2me | Definitions.Def_RevRedSAT_Placeable
-- name    : RevRedSAT_Placeable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:39.074603+00:00
-- url     : https://prove2.me/theorems/1cbb46cb-c595-415b-b2e8-d7a539b216fe
-- title:
--   Bucket maps: loads, distinct-bucket placements, forests, map codes and decoders
-- statement:
--   A **bucket map** gives every element $u\in[n]$ a set $g(u)\subseteq[q]$ of allowed buckets. This module defines:
--
--   1. the **load** of bucket $b$: the number of elements $u$ with $b\in g(u)$ (its candidates, §6.2, p.42);
--   2. **placeable**: the elements of $S$ can be placed in distinct allowed buckets, i.e. there is $\phi$ injective on $S$ with $\phi(u)\in g(u)$ for $u\in S$ (Lemma 6.8, p.42; Lemma 6.15, p.46);
--   3. **forest**: for maps into pairs of distinct buckets, the multigraph with buckets as vertices and one edge $g(u)$ per $u\in S$ is a forest; parallel pairs count as cycles (Lemma 6.11, p.44; p.46). It is stated as: every nonempty set $E$ of these edges touches more than $|E|$ buckets;
--   4. the code of a map (for each element, its buckets in increasing order) and of a list of maps;
--   5. a **decoder**, a list of pairs of an element and a conjunction of literals; under an assignment it reads the elements for which some conjunction is true ("Recovery reads the active buckets and their addresses", p.42);
--   6. the parameters of Lemma 6.16: $L_0=\lceil\log_2(k+2)\rceil$, $r=\min\{k,L_0^2\}$, $b=\lceil k/r\rceil$, $Q=8rb$.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §6.2, p.42; Lemma 6.11, p.44; Lemma 6.15, p.46; Lemma 6.16, p.47

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_MainResults
import Definitions.Def_RevRedSAT_SearchWithin
import Definitions.Def_RevRedSAT_encCNF

set_option autoImplicit false

namespace RevRedSAT

open RSListDecodingCapacity.AllRates

/-- The number of candidates of bucket `b` under the bucket map `g`: the elements `u` with
`b ∈ g(u)` (§6.2, p.42: "Suppose every bucket has at most B ≥ 1 candidates"). -/
def bucketLoad {n q : ℕ} (g : Fin n → Finset (Fin q)) (b : Fin q) : ℕ :=
  (Finset.univ.filter fun u => b ∈ g u).card

/-- **The elements of `S` can be placed in distinct allowed buckets.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 6.8, p.42: "if some
hitting set of size at most k can be assigned to distinct allowed buckets"; Lemma 6.15, p.46: "an
injective assignment ϕ : S → [8r] with ϕ(u) ∈ h(u) for every u ∈ S". -/
def Placeable {n q : ℕ} (g : Fin n → Finset (Fin q)) (S : Finset (Fin n)) : Prop :=
  ∃ ψ : Fin n → Fin q, Set.InjOn ψ (S : Set (Fin n)) ∧ ∀ u ∈ S, ψ u ∈ g u

/-- **The bucket multigraph of `S` is a forest.** Lemma 6.11, p.44: "the multigraph with buckets as
vertices and the pairs g(u), u ∈ S, as labeled edges is a forest"; p.46: "The graph in the second
item is a multigraph: different elements may be assigned the same pair of buckets, giving parallel
edges. The forest guarantee excludes such parallel pairs among the elements of S."

**Formalization Note** For maps whose values are pairs of distinct buckets (no loops), the
multigraph with one edge `g(u)` per `u ∈ S` is a forest exactly when every nonempty set `E` of its
edges touches more buckets than it has edges (a cycle with `ℓ` edges touches `ℓ` buckets, two
parallel edges touch two). -/
def IsForestOn {n q : ℕ} (g : Fin n → Finset (Fin q)) (S : Finset (Fin n)) : Prop :=
  ∀ E ⊆ S, E.Nonempty → E.card < (E.biUnion g).card

/-- The code of a bucket map `g : [n] → 2^{[q]}`: for each element in order, the list of its buckets
in increasing order. -/
def encMap {n q : ℕ} (g : Fin n → Finset (Fin q)) : List Bool :=
  encList (fun u => encSet ((g u).sort (· ≤ ·))) (List.finRange n)

/-- The code of a list of bucket maps. -/
def encMaps {n q : ℕ} (hs : List (Fin n → Finset (Fin q))) : List Bool := encList encMap hs

/-- **Reading a set of elements from an assignment.** A decoder is a list of pairs `(u, D)`, `u` an
element and `D` a conjunction of literals over the formula's variables; under the assignment `a`,
`u` is read when some pair `(u, D)` has every literal of `D` true. This covers selection bits
(`D = [(x_u, true)]`, Lemma 6.4, p.40: "Reading these bits from any satisfying assignment recovers a
set Y") and activation/address conjunctions (`P_{u,j}`, Lemma 6.8, p.42: "Recovery reads the active
buckets and their addresses"). -/
def readout {n N : ℕ} (dec : List (Fin n × List (Fin N × Bool))) (a : Fin N → Bool) :
    Finset (Fin n) := by
  classical
  exact (dec.filter fun e => decide (∀ l ∈ e.2, a l.1 = l.2)).map Prod.fst |>.toFinset

/-- The code of a decoder: its pairs, each as the element followed by the list of literal codes. -/
def encDecoder {n N : ℕ} (dec : List (Fin n × List (Fin N × Bool))) : List Bool :=
  encList (fun e => encFin e.1 ++ encList encLit e.2) dec

/-- `L₀ = ⌈log₂(k + 2)⌉` (Lemma 6.16, p.47). -/
def cutL0 (k : ℕ) : ℕ := Nat.clog 2 (k + 2)

/-- `r = min{k, L₀²}` (Lemma 6.16, p.47). -/
def cutR (k : ℕ) : ℕ := min k (cutL0 k ^ 2)

/-- `b = ⌈k/r⌉` (Lemma 6.16, p.47), written `(k + r − 1)/r`. -/
def cutB (k : ℕ) : ℕ := (k + cutR k - 1) / cutR k

/-- `Q = 8rb`, the number of buckets of the combined maps (Lemma 6.16, p.47). -/
def cutQ (k : ℕ) : ℕ := 8 * cutR k * cutB k

end RevRedSAT


