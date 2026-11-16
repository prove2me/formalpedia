-- Prove2me | Definitions.Def_CorrKClust_BalancedPivot_Supplement_Online
-- name    : CorrKClust_BalancedPivot_Supplement_Online
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:25:55.983205+00:00
-- url     : https://prove2.me/theorems/79ea4f23-9ae6-454d-af0e-de78b9bf877b
-- title:
--   Causal randomized online policies and integer hard instances
-- statement:
--   For given vertex count $n$ and cluster limit $k$, a deterministic policy table takes the arrival position, the adjacency matrix on positions revealed so far, and the previous assigned labels, and returns one of $k$ labels. Its output is computed recursively, updating exactly the current vertex. Future entries of the matrix are false and future labels are absent. Neither vertex identities nor hidden clique membership are observations.
--
--   A randomized policy is any family of nonnegative real weights on these finitely many tables summing to one. The table is sampled independently of the uniform arrival permutation. Thus
--   $$\mathbb E[\operatorname{Cost}]=\frac1{n!}\sum_\sigma\sum_A p(A)\operatorname{Cost}_G(A(\sigma)).$$
--   Every distribution on arbitrary private random tapes induces such weights; they need not be rational or uniform. Clique preservation means that the original clique blocks are unsplit with joint probability one. The explicit hard graph has $k-1$ cliques of size $m(k)=\lceil2\ln k\rceil$ and two singleton vertices, hence $n(k)=(k-1)m(k)+2$. Its hidden component labels are used only in analysis. These objects support both lower bounds.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), §2 and §5, p. 18

import Definitions.Def_CorrKClust_BalancedPivot_Instance
import Definitions.Def_CorrKClust_BalancedPivot_Orders

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot.Supplement

/-- A finite causal policy table. The padded matrix contains only arrived edges and
previous actions are present only at indices strictly before the current arrival. Hidden
vertex identifiers and component labels never occur in this interface. -/
abbrev Policy (n k : ℕ) := Fin n → (Fin n → Fin n → Bool) →
  (Fin n → Option (Fin k)) → Fin k

/-- Sequential irrevocable decisions, indexed by arrival positions. -/
def policyRun {n k : ℕ} (hk : 0 < k) (G : SimpleGraph (Fin n))
    (σ : ArrivalOrder (Fin n)) (A : Policy n k) : ℕ → (Fin n → Fin k)
  | 0 => fun _ => ⟨0, hk⟩
  | t + 1 =>
    let f := policyRun hk G σ A t
    if h : t < n then
      let v : Fin n := ⟨t, h⟩
      let edges := fun i j : Fin n => decide
        (i.val ≤ t ∧ j.val ≤ t ∧ G.Adj (σ (Fin.cast (by simp) i)) (σ (Fin.cast (by simp) j)))
      let actions := fun i : Fin n => if i.val < t then some (f i) else none
      Function.update f v (A v edges actions)
    else f

def policyOutput {n k : ℕ} (hk : 0 < k) (G : SimpleGraph (Fin n))
    (σ : ArrivalOrder (Fin n)) (A : Policy n k) : Fin n → Fin k :=
  fun v => policyRun hk G σ A n (Fin.cast (by simp) (σ.symm v))

/-- Arbitrary real probability weights on all deterministic tables represent arbitrary
private random tapes. The table is drawn independently of the uniform arrival order. -/
def onlineCost {n k : ℕ} (hk : 0 < k) (G : SimpleGraph (Fin n))
    (p : Policy n k → ℝ) : ℝ :=
  average (fun σ : ArrivalOrder (Fin n) =>
    wExp p (fun A => (cost G (policyOutput hk G σ A) : ℝ)))

/-- No original clique is split, almost surely jointly over the policy and arrival order. -/
def PreservesCliques {n k : ℕ} (hk : 0 < k) (G : SimpleGraph (Fin n))
    (Q : Fin n → Fin n) (p : Policy n k → ℝ) : Prop :=
  average (fun σ : ArrivalOrder (Fin n) => wProb p (fun A =>
    ∀ u v, Q u = Q v → policyOutput hk G σ A u = policyOutput hk G σ A v)) = 1

def hardM (k : ℕ) : ℕ := ⌈2 * Real.log k⌉₊
def hardN (k : ℕ) : ℕ := (k - 1) * hardM k + 2

def hardGroup (k : ℕ) (v : Fin (hardN k)) : ℕ :=
  if v.val < (k - 1) * hardM k then v.val / hardM k
  else k - 1 + (v.val - (k - 1) * hardM k)

def hardGraph (k : ℕ) : SimpleGraph (Fin (hardN k)) := cliqueGraph (hardGroup k)

/-- The clique-preservation predicate for the explicit hard family, without auxiliary
vertex labels in the policy observations. -/
def HardPreserving (k : ℕ) (hk : 0 < k) (p : Policy (hardN k) k → ℝ) : Prop :=
  average (fun σ : ArrivalOrder (Fin (hardN k)) => wProb p (fun A =>
    ∀ u v, hardGroup k u = hardGroup k v →
      policyOutput hk (hardGraph k) σ A u = policyOutput hk (hardGraph k) σ A v)) = 1

end CorrKClust.BalancedPivot.Supplement


