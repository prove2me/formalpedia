-- Prove2me | Definitions.Def_SparsestCutOracle_Main_Geometry
-- name    : SparsestCutOracle_Main_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:09.714129+00:00
-- url     : https://prove2.me/theorems/45280d0b-b295-4fe2-9842-96765880fb5b
-- title:
--   Gram distances, dense balls, and balanced-separator outputs
-- statement:
--   A Gram matrix $X$ determines squared distances $d_X(i,j)=X_{ii}+X_{jj}-2X_{ij}$. Let $B(i,r)=\{j:d_X(i,j)\le r^2\}$ and $r_0=1/(2\sqrt{10})$. The weighted spread of $A$ is
--
--   $$\sum_{i,j\in A}\pi(i)\pi(j)d_X(i,j).$$
--
--   The center procedure searches the finite vertex set for the first radius-four ball of weight at least $\Pi/2$, reporting failure explicitly if none exists. Dense, weighted-spread, and unweighted outcomes encode every cut and response clause separately. Width is the pair of Loewner inequalities $-\rho D_\pi\preceq Z\preceq\rho D_\pi$.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 21–27, Cases B and C and Lemma 11

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Procedures

namespace SparsestCutOracle.Main

def sqdist {n : ℕ} (X : Mat n) (i j : Fin n) : ℝ := X i i + X j j - 2 * X i j

noncomputable def ball {n : ℕ} (X : Mat n) (i : Fin n) (r : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun j => sqdist X i j ≤ r ^ 2

noncomputable def r₀ : ℝ := 1 / (2 * Real.sqrt 10)

def spread {n : ℕ} (π : Fin n → ℝ) (X : Mat n) (A : Finset (Fin n)) : ℝ :=
  ∑ i ∈ A, ∑ j ∈ A, π i * π j * sqdist X i j

/-- A deterministic finite search, with an explicit failure value rather than an assumed center. -/
noncomputable def spreadCenter {n : ℕ} (π : Fin n → ℝ) (X : Mat n) : Option (Fin n) := by
  classical
  let candidates := Finset.univ.filter fun i => totalWeight π / 2 ≤ mass π (ball X i 4)
  exact if h : candidates.Nonempty then some (candidates.min' h) else none

def BalancedSparse {n : ℕ} (G : Graph n) (π : Fin n → ℝ) (α κ β Cq : ℝ)
    (S : Finset (Fin n)) : Prop :=
  S ≠ Finset.univ ∧ β * totalWeight π ≤ mass π S ∧ mass π S ≤ mass π Sᶜ ∧
  cut G.toWGraph S Sᶜ ≤ Cq * (α / totalWeight π) * Real.sqrt (Real.log n / κ) * mass π S

def Width {n : ℕ} (π : Fin n → ℝ) (ρ : ℝ) (Z : Mat n) : Prop :=
  LePSD ((-ρ) • D π) Z ∧ LePSD Z (ρ • D π)

noncomputable def DenseOutcome {n cP : ℕ} (G : Graph n) (π : Fin n → ℝ)
    (X : Mat n) (α β κ Cq Cadd Cwidth : ℝ) (out : State) : Prop :=
  (outInt out 0 = 0 ∧ BalancedSparse G π α κ β Cq (procCut n out)) ∨
  ∃ r : Response n cP, EncodedResponse out r ∧ ValidResponse G.toWGraph π X α β Cadd r ∧
    Width π (Cwidth * α / totalWeight π) (feedback π α r)

noncomputable def SpreadOutcome {n cP : ℕ} (G : Graph n) (π : Fin n → ℝ)
    (X : Mat n) (α κ b Cq Cwidth : ℝ) (out : State) : Prop :=
  (outInt out 0 = 0 ∧ BalancedSparse G π α κ b Cq (procCut n out)) ∨
  ∃ r : Response n cP, EncodedResponse out r ∧
    LePSD r.F (laplacian G.toWGraph) ∧
    dot (pathSum r.paths - r.F) X ≤ -α ∧
    Width π (Cwidth * (α / totalWeight π) * Real.log n ^ 2) (pathSum r.paths - r.F)

noncomputable def UnweightedOutcome {n cP : ℕ} (G : Graph n) (X : Mat n)
    (A : Finset (Fin n)) (α κ b Cq Cwidth : ℝ) (out : State) : Prop :=
  (outInt out 0 = 0 ∧
    let S := procCut n out
    S ≠ Finset.univ ∧ b * n ≤ min ((S ∩ A).card : ℝ) ((A \ S).card : ℝ) ∧
    cut G.toWGraph S Sᶜ ≤ Cq * (α / n) * Real.sqrt (Real.log n / κ) * (S ∩ A).card) ∨
  ∃ r : Response n cP, EncodedResponse out r ∧
    LePSD r.F (laplacian G.toWGraph) ∧
    (∀ p, r.paths.coeff p ≠ 0 → p.Nodup) ∧
    let Q := pathSum r.paths - r.F
    (∀ i j, i ∉ A ∨ j ∉ A → Q i j = 0) ∧
    dot Q X ≤ -α ∧ Width (fun _ => 1) (Cwidth * (α / n) * Real.log n ^ 2) Q

/-- Lemma 11 makes all calls in the original G, not merely in a graph of the same size. -/
def QueriesInGraph {n : ℕ} (G : Graph n) (P : Procedure) (O : FairService) (s : State) : Prop :=
  ∀ (ω : Tape) (t a b : ℕ),
    let st := procRun P O noMatvec s ω t
    st.machine.base.halted = false →
    P[st.machine.base.core.pc]? = some (.fair a b) →
    let q := readFair st.machine (st.machine.base.core.ptrs a)
    FairEncodingValid st.machine (st.machine.base.core.ptrs a) ∧
    q.n = n ∧ HEq q.graph G ∧ q.fairness = 2 ∧
    (∀ v, 0 ≤ q.sources v) ∧ (∀ v, 0 ≤ q.targets v)

end SparsestCutOracle.Main


