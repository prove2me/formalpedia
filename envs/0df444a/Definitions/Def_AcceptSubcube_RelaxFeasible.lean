-- Prove2me | Definitions.Def_AcceptSubcube_RelaxFeasible
-- name    : AcceptSubcube_RelaxFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:43.044266+00:00
-- url     : https://prove2.me/theorems/8e83ba97-a176-484d-92b0-922ee8c366cc
-- title:
--   The Hamming-ball relaxation (10) and its semidefinite strengthening (14)
-- statement:
--   After XOR-ing every coordinate with the center $\tau$ (so the center is $0^n$), a point of the relaxation of §4.3 is a family of locally consistent distributions $\mu_T$ on $\{0,1\}^T$, $|T|\le k$, written through its multilinear moments $u_T=\tilde{\mathbb E}\prod_{i\in T}x_i$ ($u_\emptyset=1$). Each local probability is the inclusion–exclusion form
--   $$\mathbb P[x_T=1_A]=\sum_{B\subseteq T\setminus A}(-1)^{|B|}u_{A\cup B}.$$
--   The point is **feasible for (10)** when every local probability on at most $k$ variables is nonnegative and, for every $|S|\le2$ and $a\in\{0,1\}^S$,
--   $$\sum_{j=1}^n\mathbb P[x_S=a,x_j=1]\le r\,\mathbb P[x_S=a],$$
--   the summand for $j\in S$ being $\mathbb P[x_S=a]$ or $0$ according to $a_j$. The **objective** is $L=\sum_E\mathbb P[P_E(x_E)=0]$. The strengthening (14) adds $Z\succeq0$ for the moment matrix with $Z_{00}=Z_{ii}=1$, $Z_{0i}=2u_i-1$, $Z_{ij}=4u_{ij}-2u_i-2u_j+1$. The file also defines the shifted instance and the active set $U=\{i:p_i>1/(8k)\}$ of (8).
--
--   **Formalization Note** The moment parametrization makes normalization and consistency hold identically (proof of Lemma 4.7, p.20), so it is the paper's family of local laws, not a restriction. $Z\succeq0$ is Mathlib's `Matrix.PosSemidef` of the real matrix.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), §4.3, p.17 (relaxation, (10)); §4.6, pp.19–20 ((14), Z); (8), p.15; Proof of Lemma 4.7, p.20 (moments)

import Mathlib
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost

namespace AcceptSubcube

/-- The moment `u_T` stored in a moment list (first entry whose variable set is `T`; `0` if none). -/
def momOf (L : List (List ℕ × ℚ)) (T : Finset ℕ) : ℚ :=
  ((L.find? (fun e => decide (e.1.toFinset = T))).map Prod.snd).getD 0

/-- The multilinear moment `u_T = Ẽ[∏_{i∈T} x_i]`, with `u_∅ = 1` (normalization). -/
def mom (L : List (List ℕ × ℚ)) (T : Finset ℕ) : ℚ :=
  if T = ∅ then 1 else momOf L T

/-- **Local probability** `P[x_T = 1_A]` (`A ⊆ T`) of the point with moments `u`, by
inclusion–exclusion: `Σ_{B ⊆ T∖A} (−1)^{|B|} u_{A∪B}`.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Proof of Lemma 4.7, p.20: "Parametrize the
relaxation by the multilinear moments u_T = Ẽ ∏_{i∈T} x_i for 1 ≤ |T| ≤ k … Each local probability
P[x_T = a] is an inclusion–exclusion form in at most 2^{|T|} moments with coefficients ±1, so
normalization and consistency hold identically."

**Formalization Note.** A point of the relaxation of §4.3 ("locally consistent distributions µ_T on
{0,1}^T for all |T| ≤ k, normalized and agreeing on intersections", p.17) is given by its moment
vector, as in the paper's proof of Lemma 4.7; the local laws determined by moments are exactly the
normalized consistent families, so this is a parametrization, not a restriction. A pattern on `T` is
the set `A ⊆ T` of its ones. -/
def atom (L : List (List ℕ × ℚ)) (T A : Finset ℕ) : ℚ :=
  ∑ B ∈ (T \ A).powerset, (-1 : ℚ) ^ B.card * mom L (A ∪ B)

/-- `P[x_i = b]`. -/
def lit1 (L : List (List ℕ × ℚ)) (i : ℕ) (b : Bool) : ℚ :=
  atom L {i} (if b then {i} else ∅)

/-- Nonnegativity of every local probability on at most `k` of the variables `0, …, n−1`. -/
def LocalNonneg (k n : ℕ) (L : List (List ℕ × ℚ)) : Prop :=
  ∀ T ⊆ Finset.range n, T.card ≤ k → ∀ A ⊆ T, 0 ≤ atom L T A

/-- Left side of the conditional budget (10): `Σ_{j=1}^n P[x_S = a, x_j = 1]`, the summand for
`j ∈ S` being `P[x_S = a]` or `0` according to `a_j`. -/
def condLHS (n : ℕ) (L : List (List ℕ × ℚ)) (S A : Finset ℕ) : ℚ :=
  ∑ j ∈ Finset.range n,
    if j ∈ S then (if j ∈ A then atom L S A else 0) else atom L (insert j S) (insert j A)

/-- **The relaxation of §4.3** (center `0^n`, radius `r`).

Cai, Jiang, Liu, STOC 2027 submission (manuscript sha256 66626baf…), §4.3, p.17: "The variables
are locally consistent distributions µ_T on {0,1}^T for all |T| ≤ k … For every S with |S| ≤ 2 and
every a ∈ {0,1}^S we impose the conditional budget Σ_{j=1}^n P[x_S = a, x_j = 1] ≤ r P[x_S = a]
(10), where for j ∈ S the summand is read as P[x_S = a] or 0 according to a_j. The case S = ∅ is
the total budget."

**Formalization Note.** Center `0^n`: §4 XORs every coordinate with `τ` first (p.15; `shift`).
Feasible = nonnegative local laws on every `T` with `|T| ≤ k` (the moment parametrization makes
them normalized and consistent) and every budget (10). -/
def RelaxFeasible (k n r : ℕ) (L : List (List ℕ × ℚ)) : Prop :=
  LocalNonneg k n L ∧
    ∀ S ⊆ Finset.range n, S.card ≤ 2 → ∀ A ⊆ S, condLHS n L S A ≤ (r : ℚ) * atom L S A

/-- **The objective** `L = Σ_E P[P_E(x_E) = 0]` (p.17), summed over the constraints of `I`. -/
def relaxObj (I : GInst) (L : List (List ℕ × ℚ)) : ℚ :=
  (I.cons.map (fun c => ∑ A ∈ c.1.toFinset.powerset,
    if evalTab c (fun v => decide (v ∈ A)) then 0 else atom L c.1.toFinset A)).sum

/-- **The moment matrix `Z` of (14)** (p.19): with `ξ_i = 2x_i − 1`, `Z_00 = Z_ii = 1`,
`Z_0i = Ẽ[ξ_i] = 2u_i − 1`, `Z_ij = Ẽ[ξ_iξ_j] = 4u_ij − 2u_i − 2u_j + 1` (p.20). Index `none` is
`0`, `some i` is variable `i`. -/
def momentMatrix (n : ℕ) (L : List (List ℕ × ℚ)) : Matrix (Option (Fin n)) (Option (Fin n)) ℝ :=
  fun a b =>
    match a, b with
    | none, none => 1
    | none, some i => ((2 * mom L {(i : ℕ)} - 1 : ℚ) : ℝ)
    | some i, none => ((2 * mom L {(i : ℕ)} - 1 : ℚ) : ℝ)
    | some i, some j =>
      if i = j then 1 else
        ((4 * mom L {(i : ℕ), (j : ℕ)} - 2 * mom L {(i : ℕ)} - 2 * mom L {(j : ℕ)} + 1 : ℚ) : ℝ)

/-- **The strengthened relaxation (10)–(14)** (pp.17, 19): the relaxation of §4.3 plus `Z ⪰ 0`. -/
def SDPFeasible (k n r : ℕ) (L : List (List ℕ × ℚ)) : Prop :=
  RelaxFeasible k n r L ∧ (momentMatrix n L).PosSemidef

/-- The constraint with every coordinate XORed with `τ`: its table at `y` is the old table at
`y ⊕ τ_E`. -/
def shiftCons {n : ℕ} (τ : Fin n → Bool) (c : List ℕ × List Bool) : List ℕ × List Bool :=
  (c.1, (List.range (2 ^ c.1.length)).map (fun j =>
    evalTab c (fun v => xor (Nat.testBit j (c.1.idxOf v)) (extA τ v))))

/-- **The shifted instance** (§4, p.15): "We XOR every coordinate with τ, so that the center
becomes 0^n, x_i = 1 means that variable i is flipped, and each predicate is replaced by the
correspondingly shifted predicate". -/
def shift (I : GInst) (τ : Fin I.n → Bool) : GInst :=
  ⟨I.n, I.cons.map (shiftCons τ)⟩

/-- **Active coordinates** (8), p.15: `η = 1/(8k)`, `U = {i : p_i > η}`, `p_i = P[x_i = 1]`. -/
def activeSet (k n : ℕ) (L : List (List ℕ × ℚ)) : Finset ℕ :=
  (Finset.range n).filter (fun i => (1 : ℚ) / (8 * k) < lit1 L i true)

end AcceptSubcube


