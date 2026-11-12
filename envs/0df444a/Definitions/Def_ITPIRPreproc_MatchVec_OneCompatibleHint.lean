-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_OneCompatibleHint
-- name    : ITPIRPreproc_MatchVec_OneCompatibleHint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:02.185241+00:00
-- url     : https://prove2.me/theorems/3710a843-6633-4a23-895a-4cf83ccaa04f
-- title:
--   Definition 4.1 — One Compatible Hint PIR
-- statement:
--   A **One Compatible Hint PIR** for databases $D\in\{0,1\}^n$ consists of a finite key space $\mathcal R$, a set $S(R)\subseteq[n]$ for each key $R$, and algorithms
--   $$\mathit{hint}=\mathsf{Hint}(D,R),\qquad (Q,u)\leftarrow\mathsf{Query}(i,R),\qquad \mathit{ans}=\mathsf{Answer}(D,Q),\qquad y=\mathsf{Decode}(i,R,\mathit{hint},Q,u,\mathit{ans}),$$
--   where $\mathsf{Query}$ is randomized, the others deterministic, queries $Q$ are elements of $\mathcal R$, and $y\in\{0,1\}\cup\{\bot\}$. For an index $i$, $\mathcal R_i=\{R\in\mathcal R: i\in S(R)\}$ is the set of keys compatible with $i$; $R\leftarrow\mathcal R$ and $R\leftarrow\mathcal R_i$ denote uniform sampling.
--
--   For $n=m^2$, the primitive satisfies **Definition 4.1** if:
--
--   1. *Compatibility and overlap.* For every $i$ and $j\ne i$,
--   $$\Pr_{R\leftarrow\mathcal R}[i\in S(R)]\ge\frac1{2m},\qquad \Pr_{R\leftarrow\mathcal R_i}[j\in S(R)]\le\frac2m.$$
--   2. *Uniform query.* For every $i$, if $R\leftarrow\mathcal R_i$ and $(Q,u)\leftarrow\mathsf{Query}(i,R)$, then $Q$ is uniform on $\mathcal R$.
--   3. *Soundness and availability.* For every $D$ and $i$, with $R\leftarrow\mathcal R_i$ and $(Q,u)\leftarrow\mathsf{Query}(i,R)$, the output $\mathsf{Decode}(i,R,\mathsf{Hint}(D,R),Q,u,\mathsf{Answer}(D,Q))$ lies in $\{D[i],\bot\}$ with probability $1$ and equals $D[i]$ with probability at least $1/2$.
--
--   This is the interface between the compiler of §4.2 (Lemma 4.2) and the concrete matching-vector primitive of §6.2 (Lemma 6.2).
--
--   **Formalization Note** Probabilities over $R\leftarrow\mathcal R_i$ are averages $|\mathcal R_i|^{-1}\sum_{R\in\mathcal R_i}$, which are $0$ when $\mathcal R_i$ is empty, so no clause holds vacuously.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), §4.1, Syntax and Definition 4.1, printed p.11 (PDF p.13), Eq. (3) and (4)

import Mathlib

open scoped ENNReal

namespace ITPIRPreproc.MatchVec

/-!
# One Compatible Hint PIR (§4.1, Definition 4.1, printed p.11)

"Fix a key space R. Each key R ∈ R specifies a set S(R) ⊆ [n] of indices. For each i, let
R_i = {R ∈ R : i ∈ S(R)} be the set of keys that are compatible with index i. The deterministic
algorithm hint = Hint(D, R) computes a hint value. […]
(Q, u) ← Query(i, R), ans = Answer(D, Q), y = Decode(i, R, hint, Q, u, ans).
The Query algorithm is randomized, while Answer, Decode are deterministic." Queries are elements
of the key space (property (ii) compares their law with `Unif(R)`).

Definition 4.1 (One Compatible Hint PIR properties). "(i) Compatibility and overlap. For every i
and j ≠ i, Pr_{R←R}[i ∈ S(R)] ≥ 1/(2m), Pr_{R←R_i}[j ∈ S(R)] ≤ 2/m. (3)
(ii) Uniform query. For every i, R ← R_i, (Q, u) ← Query(i, R) ⟹ Q ≡ Unif(R). This equality
concerns the full query distribution, including private failure branches.
(iii) Soundness and availability. For every D, i:
Pr_{R←R_i,(Q,u)←Query(i,R)}[Decode(i, R, Hint(D, R), Q, u, Answer(D, Q)) ∈ {D[i], ⊥}] = 1 and
Pr_{R←R_i,(Q,u)←Query(i,R)}[Decode(i, R, Hint(D, R), Q, u, Answer(D, Q)) = D[i]] ≥ 1/2. (4)"

`R ← R` is the uniform law on the finite key space and `R ← R_i` the uniform law on the finite
set `R_i`; `Pr_{R←R_i}[·]` is written `avgOver (compat i) (·)`, the average over `R_i`
(`(#R_i)⁻¹ · Σ`; on an empty `R_i` it is `0`, so no property below holds vacuously).
-/

/-- The data of a One Compatible Hint PIR primitive for databases `D ∈ {0,1}^n`. -/
structure OCHP (n : ℕ) where
  /-- The key space `R`. -/
  Key : Type
  [instFintype : Fintype Key]
  [instDecEq : DecidableEq Key]
  /-- The selected set `S(R) ⊆ [n]`. -/
  sel : Key → Finset (Fin n)
  /-- Hint values. -/
  HintVal : Type
  /-- Private decoder states `u`. -/
  Secret : Type
  /-- Answers. -/
  AnsVal : Type
  /-- `Hint(D, R)` (deterministic). -/
  hint : (Fin n → Bool) → Key → HintVal
  /-- `Query(i, R)`: a law on (query, private state); queries are keys. -/
  query : Fin n → Key → PMF (Key × Secret)
  /-- `Answer(D, Q)` (deterministic). -/
  answer : (Fin n → Bool) → Key → AnsVal
  /-- `Decode(i, R, hint, Q, u, ans) ∈ {0,1} ∪ {⊥}` (`none` is `⊥`; deterministic). -/
  decode : Fin n → Key → HintVal → Key → Secret → AnsVal → Option Bool

attribute [instance] OCHP.instFintype OCHP.instDecEq

variable {n : ℕ}

/-- The set `R_i` of keys compatible with index `i`. -/
def OCHP.compat (P : OCHP n) (i : Fin n) : Finset P.Key :=
  Finset.univ.filter fun R => i ∈ P.sel R

/-- Average of `f` over the finite set `s` (the expectation under the uniform law on `s`). -/
noncomputable def avgOver {α : Type*} (s : Finset α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  (s.card : ℝ≥0∞)⁻¹ * ∑ x ∈ s, f x

/-- `Pr_{R←R}[i ∈ S(R)]`. -/
noncomputable def OCHP.probSel (P : OCHP n) (i : Fin n) : ℝ≥0∞ :=
  (Fintype.card P.Key : ℝ≥0∞)⁻¹ * (P.compat i).card

/-- `Pr_{R←R_i}[j ∈ S(R)]`. -/
noncomputable def OCHP.probOverlap (P : OCHP n) (i j : Fin n) : ℝ≥0∞ :=
  avgOver (P.compat i) fun R => if j ∈ P.sel R then 1 else 0

/-- `Pr[Q = Q₀]` when `R ← R_i` and `(Q, u) ← Query(i, R)`. -/
noncomputable def OCHP.queryLaw (P : OCHP n) (i : Fin n) (Q₀ : P.Key) : ℝ≥0∞ :=
  avgOver (P.compat i) fun R => (P.query i R).toOuterMeasure {p | p.1 = Q₀}

/-- The client's output `Decode(i, R, Hint(D, R), Q, u, Answer(D, Q))` for query outcome
`p = (Q, u)`. -/
def OCHP.outcome (P : OCHP n) (D : Fin n → Bool) (i : Fin n) (R : P.Key)
    (p : P.Key × P.Secret) : Option Bool :=
  P.decode i R (P.hint D R) p.1 p.2 (P.answer D p.1)

/-- `Pr_{R←R_i,(Q,u)←Query(i,R)}[outcome ∈ {D[i], ⊥}]`. -/
noncomputable def OCHP.probSound (P : OCHP n) (D : Fin n → Bool) (i : Fin n) : ℝ≥0∞ :=
  avgOver (P.compat i) fun R =>
    (P.query i R).toOuterMeasure {p | P.outcome D i R p = some (D i) ∨ P.outcome D i R p = none}

/-- `Pr_{R←R_i,(Q,u)←Query(i,R)}[outcome = D[i]]`, the recovery probability. -/
noncomputable def OCHP.probRecover (P : OCHP n) (D : Fin n → Bool) (i : Fin n) : ℝ≥0∞ :=
  avgOver (P.compat i) fun R =>
    (P.query i R).toOuterMeasure {p | P.outcome D i R p = some (D i)}

/-- **Definition 4.1** for databases of length `n = m²` (`m = √n`). -/
structure OCHP.IsOneCompatibleHint (P : OCHP n) (m : ℕ) : Prop where
  /-- (3), first inequality. -/
  sel_prob : ∀ i, (2 * (m : ℝ≥0∞))⁻¹ ≤ P.probSel i
  /-- (3), second inequality. -/
  overlap : ∀ i j, j ≠ i → P.probOverlap i j ≤ 2 / (m : ℝ≥0∞)
  /-- (ii) Uniform query: the query law is `Unif(R)`. -/
  uniform_query : ∀ i (Q₀ : P.Key), P.queryLaw i Q₀ = (Fintype.card P.Key : ℝ≥0∞)⁻¹
  /-- (iii) Soundness. -/
  sound : ∀ (D : Fin n → Bool) i, P.probSound D i = 1
  /-- (iii) Availability (4). -/
  available : ∀ (D : Fin n → Bool) i, 2⁻¹ ≤ P.probRecover D i

end ITPIRPreproc.MatchVec


