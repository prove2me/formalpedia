-- Prove2me | Definitions.Def_AutomaticSelfReduction_Lifting_Discrepancy
-- name    : AutomaticSelfReduction_Lifting_Discrepancy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:38.932385+00:00
-- url     : https://prove2.me/theorems/263aa2b0-beaa-4298-96d7-a8e8019ceac5
-- title:
--   Independent port laws, discrepancy and conditional node error
-- statement:
--   Fix a black node $v$ of degree $\delta$. Its incident edges are ports $1,\dots,\delta$, and configurations are now read as ordered tuples $C=(\ell_1,\dots,\ell_\delta)$: a tuple is valid when its multiset of labels lies in $C_B$. Let $p_1,\dots,p_\delta$ be probability vectors on $\Sigma$, and let $X=(X_1,\dots,X_\delta)$ have independent coordinates with $X_i\sim p_i$, so that
--   $$
--   \Pr[Z]=\prod_{i=1}^{\delta}p_{i,Z_i}\qquad\text{for every tuple }Z.
--   $$
--   (In the paper, $p_{i,\ell}$ is the probability that the given algorithm outputs $\ell$ on port $i$ of $v$, conditioned on the $(T-1)$-neighbourhood of $v$.) Define:
--
--   1. the **discrepancy** $D(i,\ell)=1-p_{i,\ell}$ and $D(C)=\sum_{i}(1-p_{i,\ell_i})$, the expected number of ports on which $X$ differs from $C$;
--   2. the **conditional node error** $\varepsilon_v=\mathbb E[d(X,C_B)]$, where $d$ is the configuration distance to $C_B$;
--   3. $d_v=\min\{D(C):C\text{ a valid tuple}\}$, the discrepancy of the configuration output by the faster algorithm, which outputs a valid tuple of minimum discrepancy;
--   4. $D_\ell=D((\ell,\dots,\ell))$, the discrepancy of the constant tuple (valid or not);
--   5. for a label $\ell$ and $b\ge0$: $C_\ell=\{C\in C_B: m_C(\ell)\ge\delta-b\}$ (as tuples), $q_\ell=\Pr[X\notin C_\ell]$ and $d_\ell=\min_{C\in C_\ell}D(C)$.
--
--   These quantities carry the local analysis of the one-round speedup: Lemmas 5.3–5.6 bound $d_v$ and $d_\ell$ in terms of $\varepsilon_v$.
--
--   **Formalization Note** Tuples are functions `Fin δ → L`; `tupleMs` gives their multiset. The minima are infima over finite subtypes, which are attained when the subtype is nonempty: the set of valid tuples is nonempty whenever $C_B$ is (every configuration of size $\delta$ can be listed as a tuple), and $C_\ell$ is nonempty whenever $q_\ell<1$. All sums are finite.
-- source:
--   Alkida Balliu, Francesco d’Amore, Dennis Olivetti, Distributed Lower Bounds via Automatic Self-Reduction, STOC 2027 submission #338 (October 2026), §5.1–§5.3, printed pp. 13–17 (PDF pp. 14–18): p_{i,ℓ}, D(i,ℓ), D(C), ε_v, d_v (pp. 13–14), D_ℓ (p. 16), C_ℓ*, q_ℓ*, d_ℓ* (p. 17)

import Definitions.Def_AutomaticSelfReduction_Lifting_Problem

/-!
# Port marginals, discrepancy and conditional error at one node

Balliu, d'Amore, Olivetti, STOC 2027 submission #338 (October 2026), §5.1–§5.3
(PDF pp. 14–18, printed pp. 13–17).

At a passive node of degree `δ`, with its `(T−1)`-view fixed, the outputs `X₁, …, X_δ` of the
given algorithm on its `δ` ports are independent, `Xᵢ` having law `pᵢ` on the labels. This file
works with an arbitrary family `p : Fin δ → L → ℝ` of probability vectors and the product law
`Pr[Z] = ∏ᵢ p_{i, Zᵢ}` on ordered tuples `Z : Fin δ → L`:

* `tupleMs Z`: the multiset of labels of the tuple `Z` (constraints seen as sets of tuples:
  `Z` is valid iff `tupleMs Z ∈ C_B`);
* `disc p C = ∑ᵢ (1 − p_{i, Cᵢ})`: the discrepancy `D(C)` of a tuple;
* `nodeError p 𝒞 = ∑_Z Pr[Z] · d(Z, 𝒞)`: the conditional expected error `ε_v`;
* `minDisc p 𝒞 = min_{C valid} D(C)`: the discrepancy `d_v = D(C_v)` of the output `C_v` of the
  faster algorithm `A'` (which outputs a valid tuple of minimum discrepancy);
* `constDisc p ℓ = D((ℓ, …, ℓ))`: `D_ℓ`;
* `dominatedTuples 𝒞 b ℓ`, `restrictedFailure`, `restrictedMinDisc`: `C_ℓ`, `q_ℓ`, `d_ℓ`.
-/

namespace AutomaticSelfReduction.Lifting

open scoped BigOperators

variable {L : Type*} [Fintype L] [DecidableEq L] {δ : ℕ}

/-- The multiset `{Z₁, …, Z_δ}` of labels of an ordered tuple. -/
def tupleMs (Z : Fin δ → L) : Multiset L :=
  Finset.univ.val.map Z

/-- `p` is a family of probability vectors: each `pᵢ` is a probability distribution on `L`. -/
def IsProbVectors (p : Fin δ → L → ℝ) : Prop :=
  (∀ i ℓ, 0 ≤ p i ℓ) ∧ ∀ i, ∑ ℓ, p i ℓ = 1

/-- `Pr[Z] = ∏ᵢ p_{i, Zᵢ}`: the product (independent-ports) law of the tuple `Z`. -/
def tupleProb (p : Fin δ → L → ℝ) (Z : Fin δ → L) : ℝ :=
  ∏ i, p i (Z i)

/-- Discrepancy `D(C) = ∑_{1 ≤ i ≤ δ} (1 − p_{i, Cᵢ})` of an ordered tuple `C` (PDF p. 14). -/
def disc (p : Fin δ → L → ℝ) (C : Fin δ → L) : ℝ :=
  ∑ i, (1 - p i (C i))

/-- `ε_v = E[d(X, C_B)]`, with `X` distributed as `tupleProb p` and `d` the distance of
Definition 2.6 from the configuration of `X` to the constraint `𝒞` (PDF p. 15). -/
noncomputable def nodeError (p : Fin δ → L → ℝ) (𝒞 : Set (Multiset L)) : ℝ :=
  ∑ Z, tupleProb p Z * (distToSet (tupleMs Z) 𝒞 : ℝ)

/-- `d_v = min_{C} D(C)`, the minimum over all ordered tuples `C` whose configuration lies in
`𝒞`: the discrepancy of the output `C_v` of `A'` (PDF pp. 14–15). It is a minimum over a
finite set, nonempty whenever `𝒞` contains a configuration of size `δ`. -/
noncomputable def minDisc (p : Fin δ → L → ℝ) (𝒞 : Set (Multiset L)) : ℝ :=
  ⨅ C : {Z : Fin δ → L // tupleMs Z ∈ 𝒞}, disc p C.1

/-- `D_ℓ = D((ℓ, …, ℓ))`, the discrepancy of the constant tuple (possibly invalid), PDF p. 16. -/
def constDisc (p : Fin δ → L → ℝ) (ℓ : L) : ℝ :=
  disc p (fun _ => ℓ)

/-- `C_ℓ = {C ∈ C_B : m_C(ℓ) ≥ δ − b}`, as ordered tuples (PDF p. 17). -/
def dominatedTuples (𝒞 : Set (Multiset L)) (b : ℕ) (ℓ : L) : Set (Fin δ → L) :=
  {C | tupleMs C ∈ 𝒞 ∧ δ ≤ (tupleMs C).count ℓ + b}

open Classical in
/-- `q_ℓ = Pr[X ∉ C_ℓ]` (PDF p. 17). -/
noncomputable def restrictedFailure (p : Fin δ → L → ℝ) (𝒞 : Set (Multiset L)) (b : ℕ)
    (ℓ : L) : ℝ :=
  ∑ Z ∈ Finset.univ.filter (fun Z => Z ∉ dominatedTuples 𝒞 b ℓ), tupleProb p Z

/-- `d_ℓ = min_{C ∈ C_ℓ} D(C)` (PDF p. 17). -/
noncomputable def restrictedMinDisc (p : Fin δ → L → ℝ) (𝒞 : Set (Multiset L)) (b : ℕ)
    (ℓ : L) : ℝ :=
  ⨅ C : dominatedTuples 𝒞 b ℓ, disc p C.1

end AutomaticSelfReduction.Lifting


