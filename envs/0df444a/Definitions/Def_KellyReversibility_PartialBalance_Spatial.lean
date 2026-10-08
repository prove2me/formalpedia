-- Prove2me | Definitions.Def_KellyReversibility_PartialBalance_Spatial
-- name    : KellyReversibility_PartialBalance_Spatial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:43:18.129041+00:00
-- url     : https://prove2.me/theorems/7757200b-c030-4da7-9733-3046782033e7
-- title:
--   Spatial processes, frozen sites, the partial balance equations (9.26)–(9.27), and Markov fields
-- statement:
--   The spatial setting of Kelly's Chapter 9. There are finitely many sites $j\in G$, the vertices of a graph $G$; site $j$ carries an attribute $n_j$ from a finite set $\mathcal N_j$, and the state space is $\mathcal S=\mathcal N_1\times\cdots\times\mathcal N_J$. The operator $T_j^m$ changes the attribute of site $j$ to $m$: $T_j^m\mathbf n=(n_1,\dots,n_{j-1},m,n_{j+1},\dots,n_J)$. Write $\partial j$ for the neighbours of $j$ and $\mathbf n_{G-j}$ for the attributes of the sites other than $j$.
--
--   1. **Spatial process** (§9.2, p. 189): a Markov process on $\mathcal S$ with rates $q$ ($q\ge0$ off the diagonal, $q(\mathbf n,\mathbf n)=0$) such that (i) only one component of $\mathbf n$ can change at a time; (ii) $q(\mathbf n,T_j^m\mathbf n)$ does not depend on $\mathbf n_{G-j-\partial j}$; (iii) for any states $\mathbf n$, $T_j^m\mathbf n$ it is possible to reach $T_j^m\mathbf n$ from $\mathbf n$ by a sequence of transitions which do not alter $\mathbf n_{G-j}$.
--   2. **Freezing all sites but $j$** at $\mathbf n_{G-j}$: the process on $\mathcal N_j$ with rates $a\mapsto b$ equal to $q(T_j^a\mathbf n,T_j^b\mathbf n)$.
--   3. **Conditional probability (9.1)**: $P(n_j\mid\mathbf n_{G-j})=\pi(\mathbf n)/\sum_{m\in\mathcal N_j}\pi(T_j^m\mathbf n)$.
--   4. **Partial balance equations (9.26)** at site $j$:
--   $$\pi(\mathbf n)\sum_m q(\mathbf n,T_j^m\mathbf n)=\sum_m\pi(T_j^m\mathbf n)q(T_j^m\mathbf n,\mathbf n),\qquad \mathbf n\in\mathcal S.$$
--   The equations **(9.27)** are the same equations for the states with a particular attribute $n_j=a$ only.
--   5. **Altered rates**: every $q(\mathbf n,T_j^m\mathbf n)$ multiplied by $c$ (Corollary 9.6 (iii)); or only those with $n_j=a$ (Corollary 9.8 (iii)).
--   6. **Attribute class** $\{\mathbf n:n_j=a\}$, the set to which the process is truncated when site $j$ is frozen at $a$.
--   7. **Markov field** (§9.1, pp. 184–185): a positive $\pi$ on $\mathcal S$ with $\sum_{\mathbf n}\pi(\mathbf n)=1$ such that $P(n_j\mid\mathbf n_{G-j})=P(n_j\mid\mathbf n_{\partial j})$, i.e. the conditional probability (9.1) depends on $\mathbf n_{G-j}$ only through $\mathbf n_{\partial j}$.
--
--   **Formalization Note** Sites form a finite type with decidable equality and $T_j^m$ is `Function.update`. Condition (ii) is stated as: two states that agree at $j$ and at every neighbour of $j$ have the same rate of changing site $j$ to $m$. The book's random field takes values in $(0,1)$; here it is positive and sums to one, which differs only when $\mathcal S$ is a single state. The Markov-field definition is restated here because chunk VIII's definition is an unpublished draft.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 184–185 (§9.1, random field, (9.1), (9.2)), p. 189 (§9.2, spatial process), pp. 201–202 ((9.26), (9.27), Corollaries 9.6, 9.8)

import Mathlib
import Definitions.Def_KellyReversibility_PartialBalance_Core

namespace KellyReversibility.PartialBalance

open Function

variable {ι : Type*} [DecidableEq ι] {N : ι → Type*}

/-- A **spatial process** (Kelly 1979, §9.2, p. 189) on the sites `ι` (the vertices of the graph
`G`), site `j` carrying an attribute in the finite set `N j`, with state space
`𝒮 = ∏_j N j` and transition rates `q`, `q(n,n) = 0`. The three conditions of p. 189 are:
(i) only one component of `n` can change at a time;
(ii) the rate `q(n, T_j^m n)` does not depend on `n_{G−j−∂j}`, i.e. only on `n_j`, `m` and the
attributes of the neighbours of `j`;
(iii) for any states `n`, `T_j^m n` it is possible to reach `T_j^m n` from `n` by a sequence of
transitions which do not alter `n_{G−j}`.
Here `T_j^m n = Function.update n j m` changes the attribute of site `j` to `m`. -/
def IsSpatialProcess (G : SimpleGraph ι) (q : (∀ i, N i) → (∀ i, N i) → ℝ) : Prop :=
  IsRateMatrix q ∧
  (∀ n n' : (∀ i, N i), q n n' ≠ 0 → ∃ (j : ι) (m : N j), n' = update n j m) ∧
  (∀ (j : ι) (m : N j) (n n' : ∀ i, N i), n j = n' j → (∀ i, G.Adj j i → n i = n' i) →
      q n (update n j m) = q n' (update n' j m)) ∧
  (∀ (j : ι) (m : N j) (n : ∀ i, N i),
      Relation.ReflTransGen
        (fun a b : (∀ i, N i) => (∃ m' : N j, b = update a j m') ∧ 0 < q a b) n (update n j m))

/-- The **truncated process at site `j`** obtained when the sites other than `j` are frozen at
`n_{G−j}` (§9.4, p. 201): a process on `N j` whose rate from `a` to `b` is
`q(T_j^a n, T_j^b n)`. -/
def frozenRates (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι) (n : ∀ i, N i) : N j → N j → ℝ :=
  fun a b => q (update n j a) (update n j b)

/-- The **conditional probability** (9.1), p. 185:
`P(n_j | n_{G−j}) = π(n) / ∑_{m∈N_j} π(T_j^m n)`. -/
noncomputable def condProb [∀ i, Fintype (N i)] (π : (∀ i, N i) → ℝ) (j : ι)
    (n : ∀ i, N i) : ℝ :=
  π n / ∑ m : N j, π (update n j m)

/-- The **partial balance equations (9.26)** at site `j` (p. 201):
`π(n) ∑_m q(n, T_j^m n) = ∑_m π(T_j^m n) q(T_j^m n, n)` for every `n ∈ 𝒮`. -/
def SitePartialBalance [∀ i, Fintype (N i)] (π : (∀ i, N i) → ℝ)
    (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι) : Prop :=
  ∀ n : (∀ i, N i), π n * (∑ m : N j, q n (update n j m)) =
    ∑ m : N j, π (update n j m) * q (update n j m) n

open Classical in
/-- The process **altered at site `j`** (Corollary 9.6 (iii)): every rate `q(n, T_j^m n)` of a
transition changing only the attribute of site `j` is changed to `c q(n, T_j^m n)`. -/
noncomputable def siteScaled (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι) (c : ℝ) :
    (∀ i, N i) → (∀ i, N i) → ℝ :=
  fun n n' => if ∀ i, i ≠ j → n i = n' i then c * q n n' else q n n'

/-- The set of states in which site `j` has the particular attribute `a`. -/
def attrClass (j : ι) (a : N j) : Set (∀ i, N i) := {n | n j = a}

/-- The **partial balance equations (9.27)** (p. 202) for the particular attribute `a` of site
`j`: `π(n) ∑_m q(n, T_j^m n) = ∑_m π(T_j^m n) q(T_j^m n, n)` for every `n` with `n_j = a`. -/
def AttrPartialBalance [∀ i, Fintype (N i)] (π : (∀ i, N i) → ℝ)
    (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι) (a : N j) : Prop :=
  ∀ n : (∀ i, N i), n j = a → π n * (∑ m : N j, q n (update n j m)) =
    ∑ m : N j, π (update n j m) * q (update n j m) n

open Classical in
/-- The process **altered at attribute `a` of site `j`** (Corollary 9.8 (iii)): the rate
`q(n, T_j^m n)` is changed to `c q(n, T_j^m n)` for every `n` with `n_j = a` and every `m`;
all other rates are unchanged. -/
noncomputable def attrScaled (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι) (a : N j) (c : ℝ) :
    (∀ i, N i) → (∀ i, N i) → ℝ :=
  fun n n' => if n j = a ∧ (∀ i, i ≠ j → n i = n' i) then c * q n n' else q n n'

/-- A **Markov field** over the graph `G` (§9.1, pp. 184–185): a random field — a function
`π : 𝒮 → (0,1)` on `𝒮 = ∏_j N j` with `∑_n π(n) = 1` — whose conditional probabilities (9.1)
satisfy (9.2), `P(n_j | n_{G−j}) = P(n_j | n_{∂j})`: the conditional probability of `n_j` given
the other sites depends on them only through the attributes of the neighbours of `j`. -/
def IsMarkovField [Fintype ι] [∀ i, Fintype (N i)] (G : SimpleGraph ι)
    (π : (∀ i, N i) → ℝ) : Prop :=
  (∀ n, 0 < π n ∧ π n < 1) ∧ (∑ n, π n) = 1 ∧
  ∀ (j : ι) (n n' : ∀ i, N i), n j = n' j → (∀ i, G.Adj j i → n i = n' i) →
    condProb π j n = condProb π j n'

end KellyReversibility.PartialBalance


