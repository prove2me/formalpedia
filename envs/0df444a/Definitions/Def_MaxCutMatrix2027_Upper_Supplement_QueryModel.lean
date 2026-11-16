-- Prove2me | Definitions.Def_MaxCutMatrix2027_Upper_Supplement_QueryModel
-- name    : MaxCutMatrix2027_Upper_Supplement_QueryModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:07:37.21004+00:00
-- url     : https://prove2.me/theorems/7eb5fa8d-4b4f-4c62-9b1a-cc0efe88e124
-- title:
--   Pair-query estimators, hard laws and information quantities
-- statement:
--   This definition file fixes the objects of the lower bounds of §§5–7 for graphs on the vertex set $[n]$ (in Lean $\{0,\dots,n-1\}$).
--
--   1. **Deterministic algorithms.** An adaptive algorithm is a finite decision tree: at an internal node it queries an unordered pair $\{u,v\}$ with $u\neq v$ and continues according to the answer ($1$ if $\{u,v\}$ is an edge), at a leaf it outputs a real number. Its *transcript* on $G$ is the ordered list of queried pairs with their answers; the number of queries counted is the number of *distinct* pairs in it. A tree *always makes exactly $q$ distinct queries* when every transcript has length $q$ and no repeated pair. A non-adaptive algorithm is a fixed set of unordered pairs together with an arbitrary real function of their answers.
--   2. **MAX-CUT accuracy.** An estimate $z$ is accurate with error parameter $\varepsilon$ when $|z-\mathrm{MAXCUT}(G)|\le\varepsilon n^2$, with the published cut objective.
--   3. **Hard laws (Definition 5.1).** Under $D_0$ every pair is an edge independently with probability $1/2$. Under $D_1^{\mathrm{joint}}$ the hidden signs $\Sigma\in\{-1,1\}^n$ are uniform and, given $\Sigma$, each pair is independently an edge with probability $(1-\rho\Sigma_u\Sigma_v)/2$; $D_1$ is the graph marginal. For a fixed query graph $H$, $D_{i,H}$ is the law of the answers on $E(H)$; for a tree $T$, $D_{i,T}$ is the law of its transcript; $\mu_h$ is the posterior of $\Sigma$ given transcript $h$ under $D_1^{\mathrm{joint}}$.
--   4. **Information quantities (§3, p.14).** With base-2 logarithms, $D_{\mathrm{KL}}(P\|Q)=\sum_x P(x)\log_2\frac{P(x)}{Q(x)}$ (zero-mass terms vanish) and $\chi^2(P\|Q)=\sum_x P(x)^2/Q(x)-1$; $U_n$ is the uniform law on $\{-1,1\}^n$.
--
--   These objects carry no separation, divergence or accuracy assumption; they are shared by Lemmas 5.2, 6.3, 7.2, 7.4, 7.5 and Theorems 6.1, 7.1.
--
--   **Formalization Note** Signs are Booleans ($\mathtt{true}\mapsto 1$); laws are explicit finite mass functions on the finite type of simple graphs. The KL and $\chi^2$ formulas are used only where the second law is positive wherever the first is.
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), §3 pp.13–15, Definition 5.1 p.28, §6 p.29, §7 pp.32–34, p.28 (PDF p.28); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Mathlib
import Definitions.Def_IIDMatchHard_Cut

set_option autoImplicit false
open scoped BigOperators

namespace MaxCutMatrix2027.Upper.Supplement

/-! §3, pp.13–14 (adjacency-matrix model), §5 Definition 5.1 p.28, §6 p.29 and §7 p.32.
Pair-query estimators for MAX-CUT on graphs with vertex set `Fin n`, the two hard laws,
and the finite information quantities of §3 p.14 (all logarithms base 2). -/

/-- A deterministic adaptive pair-query algorithm (§3, p.13; §7, p.32): a finite decision tree.
At a `node` it queries the unordered pair `{u, v}` (`u ≠ v`) and continues with the subtree
selected by the answer (`true` = the pair is an edge). At a `leaf` it outputs a real estimate.
Intermediate computation is unrestricted: the tree may be any function of the transcript.
Every path is finite, so every run terminates. Repeated queries are allowed (and not
counted twice, see `distinctQueries`). -/
inductive QueryTree (n : ℕ) where
  | leaf (z : ℝ) : QueryTree n
  | node (u v : Fin n) (h : u ≠ v) (next : Bool → QueryTree n) : QueryTree n

namespace QueryTree

variable {n : ℕ}

open Classical in
/-- The query transcript on input `G`: the ordered list of queried unordered pairs with their
answers (`true` = edge, i.e. the paper's `Y = -1`). -/
noncomputable def transcript : QueryTree n → SimpleGraph (Fin n) → List (Sym2 (Fin n) × Bool)
  | leaf _, _ => []
  | node u v _ next, G => (s(u, v), decide (G.Adj u v)) :: transcript (next (decide (G.Adj u v))) G

open Classical in
/-- The real number output by the tree on input `G`. -/
noncomputable def output : QueryTree n → SimpleGraph (Fin n) → ℝ
  | leaf z, _ => z
  | node u v _ next, G => output (next (decide (G.Adj u v))) G

/-- The number of distinct pairs queried on input `G` (§3, p.13: worst-case query complexity
counts distinct pairs). -/
noncomputable def distinctQueries (T : QueryTree n) (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((T.transcript G).map Prod.fst).toFinset.card

/-- `T` always makes exactly `q` distinct queries (§7, p.32): on every input its transcript has
length `q` and no pair is queried twice. -/
def ExactlyDistinct (T : QueryTree n) (q : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), (T.transcript G).length = q ∧ ((T.transcript G).map Prod.fst).Nodup

end QueryTree

/-- A deterministic non-adaptive pair-query algorithm (§3, p.13): the set of queried unordered
pairs is fixed before any answer is seen, and the output is an arbitrary real function of the
answers to these queries. -/
structure NonAdaptiveQuery (n : ℕ) where
  pairs : Finset (Sym2 (Fin n))
  valid : ∀ e ∈ pairs, ¬ e.IsDiag
  estimate : (↥pairs → Bool) → ℝ

namespace NonAdaptiveQuery

variable {n : ℕ}

open Classical in
/-- The answers of `G` to the queried pairs (`true` = edge). -/
noncomputable def answers (A : NonAdaptiveQuery n) (G : SimpleGraph (Fin n)) : ↥A.pairs → Bool :=
  fun e => decide (e.1 ∈ G.edgeSet)

/-- The output of the non-adaptive algorithm on input `G`. -/
noncomputable def output (A : NonAdaptiveQuery n) (G : SimpleGraph (Fin n)) : ℝ :=
  A.estimate (A.answers G)

end NonAdaptiveQuery

/-- The MAX-CUT value `MAXCUT(G)` (§3, pp.13–14), as a real number (published `maxCut`). -/
noncomputable def maxCutR {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ := (IIDMatchHard.maxCut G : ℝ)

/-- The event that an estimate `z` is correct within error parameter `ε` (§3, p.14):
`|z − MAXCUT(G)| ≤ ε n²`. -/
def Accurate {n : ℕ} (ε : ℝ) (G : SimpleGraph (Fin n)) (z : ℝ) : Prop :=
  |z - maxCutR G| ≤ ε * (n : ℝ) ^ 2

/-- A sign `{−1, 1}` encoded by a Boolean (`true ↦ 1`, `false ↦ −1`). -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The product `x_u x_v` of two signs on an unordered pair (well defined by symmetry). -/
def signProd {n : ℕ} (x : Fin n → Bool) (e : Sym2 (Fin n)) : ℝ :=
  Sym2.lift ⟨fun u v => sgn (x u) * sgn (x v), fun _ _ => mul_comm _ _⟩ e

/-- The unordered pairs `{u, v}`, `u < v`, of `[n]`, listed as ordered pairs with `u < v`. -/
def vertexPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

open Classical in
/-- Conditional probability of the answer of the pair `(u, v)` under the yes law given hidden
signs `σ` (Eq. (35), p.28): an edge (`Y = −1`) has probability `(1 − ρ σ_u σ_v)/2`. -/
noncomputable def pairLikelihood {n : ℕ} (ρ : ℝ) (σ : Fin n → Bool) (G : SimpleGraph (Fin n))
    (p : Fin n × Fin n) : ℝ :=
  if G.Adj p.1 p.2 then (1 - ρ * sgn (σ p.1) * sgn (σ p.2)) / 2
  else (1 + ρ * sgn (σ p.1) * sgn (σ p.2)) / 2

/-- `D₁^joint(σ, G)` (Definition 5.1, p.28): uniform hidden signs, then independent pairs. -/
noncomputable def yesJoint {n : ℕ} (ρ : ℝ) (σ : Fin n → Bool) (G : SimpleGraph (Fin n)) : ℝ :=
  (1 / 2 : ℝ) ^ n * ∏ p ∈ vertexPairs n, pairLikelihood ρ σ G p

/-- The yes law `D₁(G)`: the graph marginal of `D₁^joint`. -/
noncomputable def yesLaw {n : ℕ} (ρ : ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ σ : Fin n → Bool, yesJoint ρ σ G

/-- The no law `D₀(G)` (Definition 5.1): every pair is an edge independently with probability
`1/2`, so each simple graph on `[n]` has mass `2^{-binom(n,2)}`. -/
noncomputable def noLaw {n : ℕ} (_G : SimpleGraph (Fin n)) : ℝ :=
  (1 / 2 : ℝ) ^ (vertexPairs n).card

/-- The probability of an event under a law on graphs. -/
noncomputable def lawProb {n : ℕ} (D : SimpleGraph (Fin n) → ℝ) (P : SimpleGraph (Fin n) → Prop) :
    ℝ := by
  classical
  exact ∑ G : SimpleGraph (Fin n), if P G then D G else 0

/-- `D_{i,H}` (§6, p.29): the law of the answer vector `(Y_e)_{e ∈ E(H)}` for a fixed query
graph `H`, as a push-forward of a graph law `D` (`true` = edge). -/
noncomputable def answerLaw {n : ℕ} (D : SimpleGraph (Fin n) → ℝ) (H : SimpleGraph (Fin n))
    (y : ↥H.edgeSet → Bool) : ℝ := by
  classical
  exact ∑ G : SimpleGraph (Fin n), if (∀ e : ↥H.edgeSet, decide (e.1 ∈ G.edgeSet) = y e) then D G else 0

/-- `D_{i,T}` (§7, p.32): the law of the complete transcript of a deterministic tree `T`. -/
noncomputable def transcriptLaw {n : ℕ} (D : SimpleGraph (Fin n) → ℝ) (T : QueryTree n)
    (h : List (Sym2 (Fin n) × Bool)) : ℝ := by
  classical
  exact ∑ G : SimpleGraph (Fin n), if T.transcript G = h then D G else 0

/-- The finite set of transcripts that `T` can produce; both transcript laws vanish outside it. -/
noncomputable def transcripts {n : ℕ} (T : QueryTree n) : Finset (List (Sym2 (Fin n) × Bool)) := by
  classical
  exact Finset.univ.image T.transcript

/-- `Pr_{D₁^joint}(Σ = σ, T = h)`. -/
noncomputable def jointTranscript {n : ℕ} (ρ : ℝ) (T : QueryTree n) (σ : Fin n → Bool)
    (h : List (Sym2 (Fin n) × Bool)) : ℝ := by
  classical
  exact ∑ G : SimpleGraph (Fin n), if T.transcript G = h then yesJoint ρ σ G else 0

/-- The posterior `μ_h(σ) = Pr_{D₁^joint}(Σ = σ | T = h)` (Lemma 7.4, p.34). At a history of
probability zero the value is `0`; such histories carry zero weight in every expectation. -/
noncomputable def posterior {n : ℕ} (ρ : ℝ) (T : QueryTree n) (h : List (Sym2 (Fin n) × Bool))
    (σ : Fin n → Bool) : ℝ :=
  jointTranscript ρ T σ h / transcriptLaw (yesLaw ρ) T h

/-- The uniform law `U_n` on `{−1, 1}^n`. -/
noncomputable def uniformSigns (n : ℕ) (_x : Fin n → Bool) : ℝ := (1 / 2 : ℝ) ^ n

/-- KL divergence in bits over a finite set `S` (§3, p.14):
`D_KL(P‖Q) = ∑_{x ∈ S} P(x) log₂(P(x)/Q(x))`, terms with `P(x) = 0` contributing zero.
The applications have `Q(x) > 0` wherever `P(x) > 0`. -/
noncomputable def klOn {α : Type*} (S : Finset α) (P Q : α → ℝ) : ℝ :=
  ∑ x ∈ S, if P x = 0 then 0 else P x * Real.logb 2 (P x / Q x)

/-- KL divergence in bits on a finite type. -/
noncomputable def kl {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ := klOn Finset.univ P Q

/-- χ²-divergence (§3, p.14): `χ²(P‖Q) = E_Q[(P/Q)²] − 1 = ∑_x P(x)²/Q(x) − 1`, for `Q`
positive everywhere (as in the applications). -/
noncomputable def chiSq {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ :=
  (∑ x, P x ^ 2 / Q x) - 1

/-- `log₂ e`. -/
noncomputable def log2e : ℝ := Real.logb 2 (Real.exp 1)

end MaxCutMatrix2027.Upper.Supplement


