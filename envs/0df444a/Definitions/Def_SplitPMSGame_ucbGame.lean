-- Prove2me | Definitions.Def_SplitPMSGame_ucbGame
-- name    : SplitPMSGame_ucbGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:28.156416+00:00
-- url     : https://prove2.me/theorems/cb5506a7-093c-422f-a716-3209b98e806f
-- title:
--   The unit-speed constrained basic (UCB) PMS games
-- statement:
--   Assume (Assumption 1) that the job players of each player $i$ have the natural speed $m(i)=v(\{i\})/\psi(\{i\})$. Each job player $\ell$ is split into $m(f(\ell))$ **unit-speed job players**; in the $j$-th **UCB PMS game** $F^{(j)}_U$ one of them carries the requirement of $\ell$ in the $j$-th CB game ($1$ if $\ell\ge j$, else $0$) and the others carry requirement $0$. A coalition $A$ of unit-speed job players costs, by (1),
--   $$
--   F^{(j)}_U(A)=\frac1{|A|}\sum_{k=1}^{|A|}(|A|-k+1)\,q^A_k,
--   $$
--   with $q^A$ its requirements in nondecreasing order. The feasible coalitions are the sets $J^U(S)$ of unit-speed descendants of the coalitions $S\subseteq N$.
--
--   The UCB games are constrained unit-speed $\{0,1\}$ PMS games; Theorem 3 reduces the total balancedness of the PMS game to theirs.
--
--   **Formalization Note** A unit-speed job player is a pair $(\ell,r)$ with $r<m(f(\ell))$; the distinguished descendant is $(\ell,0)$. Its father in $N$ is $f(\ell)$. Lean index $j$ is the paper's $j+1$.
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, §5.1.2, p.2242 (PDF p.11); Assumption 1, p.2240 (PDF p.9)

import Mathlib
import Definitions.Def_SplitPMSGame_sptCost

namespace SplitPMSGame

/-- **Unit-speed job players** `J^U(N)` (Alon, Anily, *The Basic Core of a Parallel Machines
Scheduling Game*, MSOM 25(6) (2023), §5.1.2, p.2242). Under Assumption 1 each job player
`ℓ ∈ J(N)` owns a machine of natural speed `v′({ℓ}) = v({f(ℓ)})/ψ({f(ℓ)}) = m(f(ℓ))`; it is split
into `v′({ℓ})` unit-speed job players. A unit-speed job player is a pair `(ℓ, r)` with
`r < m(f(ℓ))`.

**Formalization Note** `m : N → ℕ` is the common natural speed of the job players of each
player (Assumption 1, p.2240). -/
abbrev UnitPlayer {N : Type*} {ψ : ℕ} (f : Fin ψ → N) (m : N → ℕ) : Type _ :=
  Σ ℓ : Fin ψ, Fin (m (f ℓ))

/-- The father in `N` of a unit-speed job player (MSOM 2023, §5.1.2, p.2242): the father
`f(ℓ)` of the job player `ℓ` it was split from. The feasible coalitions `𝒞^U` of the UCB games
are the sets `J^U(S)` of unit-speed descendants of the coalitions `S ⊆ N`. -/
def ucbFather {N : Type*} {ψ : ℕ} (f : Fin ψ → N) (m : N → ℕ) : UnitPlayer f m → N :=
  fun a => f a.1

/-- **Processing requirement in the `j`-th UCB PMS game** (MSOM 2023, §5.1.2, p.2242): of the
`v′({ℓ})` unit-speed descendants of job player `ℓ`, "one of them is associated with the same
processing requirement (zero or one) as its father" in the `j`-th CB game — `1` iff `ℓ ≥ j` —
"and the others are associated with a zero processing requirement". The distinguished
descendant is `(ℓ, 0)`.

**Formalization Note** Lean index `j` is the paper's `j + 1` (as in `basicReq`). -/
def ucbReq {N : Type*} {ψ : ℕ} (f : Fin ψ → N) (m : N → ℕ) (j : Fin ψ) : UnitPlayer f m → ℝ :=
  fun a => if (a.2 : ℕ) = 0 ∧ j ≤ a.1 then 1 else 0

/-- **The `j`-th UCB PMS game** `(J^U(N), 𝒞^U, F^(j)_U)` (MSOM 2023, §5.1.2, p.2242): every
unit-speed job player owns a unit-speed machine and one job of requirement `ucbReq j`, and a
coalition `A` of unit-speed job players costs, by equation (1),
`(1/|A|) ∑_{k=1}^{|A|} (|A| − k + 1) q^A_k` with `q^A` its requirements in nondecreasing order.

**Formalization Note** The cost is defined on every coalition of unit-speed job players; the
constrained game uses it only on the feasible coalitions `J^U(S)` (see
`ConstrainedTotallyBalanced`). -/
noncomputable def ucbCost {N : Type*} {ψ : ℕ} (f : Fin ψ → N) (m : N → ℕ) (j : Fin ψ)
    (A : Finset (UnitPlayer f m)) : ℝ :=
  sptCost (A.val.map (ucbReq f m j)) (A.card : ℝ)

end SplitPMSGame


