-- Prove2me | Definitions.Def_FasterSFM_Supplement_Run
-- name    : FasterSFM_Supplement_Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:52:35.543191+00:00
-- url     : https://prove2.me/theorems/4f6b923e-ad1f-4856-8726-83d28d38df05
-- title:
--   The run of the exact cutting plane method of §8: states, transitions (steps 1–5) and reachable states
-- statement:
--   This definition makes precise the exact cutting plane method of §8 as a transition system, so that statements about *every run* of the algorithm (such as Theorem 14) can be formalized.
--
--   A **state** consists of
--   1. the current quotient DAG $D$ of the implication graph on $U=\{0,\dots,n-1\}$, with $N$ blocks;
--   2. the witness value $m$ (the sliding parameter is $t=h(\emptyset)+1-m$);
--   3. the cutting plane body $P$: the $2n$ cube rows $(\pm e_j,1)$ and the inserted rows $(v_i,\rho_i)$, kept forever;
--   4. for each inserted row, the separation-oracle vector stored with it: its compressed vector, the DAG and partition at the time of the call, its label (greedy or graph), its historical ordering and its timestamp $t_i$;
--   5. the coordinates $y\in\mathbb R^N$ of the center $z=Jy$ in the block basis $J=(\xi_C)_C$, $\xi_C=\mathbf 1_C/\sqrt{|C|}$;
--   6. the control point: step 2, step 5 with a fixed certificate $\alpha$, or halted;
--   7. the number of separation-oracle calls made so far.
--
--   The **initial state** has the empty implication graph ($n$ singleton blocks), $m=\min\{h(\emptyset),h(U)\}$ lowered by calibration (3), $P=[-1,1]^n$, center $0$, and no calls.
--
--   A **transition** is one of the following.
--   1. *Step 2.* If $N=1$, halt. Otherwise call the oracle at the compressed weights $w_C=y_C/\sqrt{|C|}$: if some arc $u\to v$ has $w_u>w_v$ it returns $e_u-e_v$; otherwise it orders the blocks by decreasing $w$ (descendants first on ties), evaluates $h$ on the lifted proper prefixes (lowering $m$), and returns the greedy vector $a_{\pi(j)}=H_t(P_j)-H_t(P_{j-1})$. A zero vector halts. Every call counts.
--   2. *Step 3 (wide step).* With $b=J\tilde a/\|\tilde a\|_2$ and $\upsilon=\sqrt{b^\top H_{\mathrm{fl}}(z)^{-1}b/\gamma}\ge\delta$, insert the row $(b,\upsilon+b^\top z)$, store the vector, and move to an iterate of exact full Newton steps of the new restricted barrier that is a certified center (12).
--   3. *Step 4 (thin event).* If $\upsilon<\delta$, take simplex coefficients $p$ as in Lemma 15 (positive exactly on the inserted rows with $J^\top v_i\neq0$, $\|\sum_ip_iJ^\top v_i/\|J^\top v_i\|_2\|_2\le\chi_n/1024$) and convert them as in Lemma 16, $\alpha_i=(p_i/\sigma_i)/\sum_jp_j/\sigma_j$; go to step 5.
--   4. *Step 5.* If $\Delta\ge\beta$, halt. Otherwise take a block $z$ with $\theta c_z>G$ (Lemma 6), lower $m$ by the queries of the arc search, and either halt because $\Delta\ge\beta$ now holds, or add an arc $u\to z$ with $u\in A_z$ such that every closed set containing $u$ but not $z$ has $H_t>0$ (Lemma 7). If no cycle arises, recalibrate and repeat step 5 with the same certificate. If a cycle arises, contract to the condensation and go to step 1.
--   5. *Step 1.* If a stored greedy vector becomes zero, halt. Otherwise run Recenter (Algorithm 1) from the old center with a contraction matrix $\Gamma$ ($\Gamma\Gamma^\top=I$, $\Gamma^\top\Gamma=I-J'J'^\top$, $J'=J^\top J_{\mathrm{new}}$), take the returned point in the new basis, recalibrate, and go to step 2.
--
--   A state is **reachable** if it arises from an initial state by finitely many transitions.
--
--   **Formalization Note** Where the paper leaves a choice (which violated arc, the tie order, the number of Newton steps, the coefficients of Lemma 15, the target and the head of the arc, the query sets of the binary search of Lemma 7, the matrix $\Gamma$, the numbering of new blocks), every choice with the property the paper's construction guarantees is allowed. The witness set $X_{\mathrm{out}}$ and the caches of evaluated values are not stored: no step branches on them. The zero test after a contraction is applied to the stored greedy vectors of the inserted rows.
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, §4.2, p.11; §5.1, pp.16–17; §5.4, pp.21–22; Lemma 15, p.27; Lemma 16, p.28; Lemmas 6–7, pp.13–15; §7, Algorithm 1, p.30; Lemma 24, p.41; §8, steps 1–5, pp.41–42

import Mathlib
import Definitions.Def_FasterSFM_Params
import Definitions.Def_FasterSFM_BlockDAG
import Definitions.Def_FasterSFM_Barrier
import Definitions.Def_FasterSFM_Recenter
import Definitions.Def_SchrijverSFM_Alg_Setting

namespace FasterSFM.Supplement

open Classical Matrix FasterSFM

/-!
# The run of the exact cutting plane method of §8

Ene & Nguyen, *A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization*,
arXiv:2610.25403v1: the separation oracle (§4.2, p.11), the block basis `J` and isometric vectors
(§5.1, pp.16–17), wide steps and thin events (§5.4, pp.21–22), the certificate of Lemma 15 converted
by Lemma 16 (§6, pp.26–28), target and arc extraction (Lemmas 6–7, pp.13–15), recentering after a
contraction (§7, Algorithm 1, p.30; Lemma 24, p.41) and the complete algorithm (§8, steps 1–5,
pp.41–42).

A state of the algorithm records the current quotient DAG, the witness value `m` (the sliding
parameter is `t = h(∅) + 1 − m`), the cutting plane body, the oracle vector stored with each inserted
row, the center `z = J y`, the control point (step 2, step 5 with its fixed certificate, or halted),
and the number of separation-oracle calls made so far. `Step h` is one transition of §8;
`Reachable h s` says that `s` arises from the initial state by finitely many transitions.

**Formalization Note.**
* The ground set is `U = Fin n`; `h : Finset (Fin n) → ℝ`. The quotient DAG is the published
  `FasterSFM.BlockDAG` (blocks `Fin N`).
* The witness set `X_out` is not stored: no step of the algorithm branches on it (only on `m`).
  The caches of evaluated values are not stored either; they affect only the number of value-oracle
  calls, which `Step` does not count.
* Every value query lowers `m` to the minimum of `m` and the queried values (`MinUpdate`).
* Where the paper leaves a choice, `Step` allows every choice with the property the paper's
  construction guarantees: which violated arc yields the graph vector; the tie-breaking order among
  descendant-first orders; how many exact Newton steps restore (12) after a wide step (any number
  whose iterate is certified); the simplex coefficients of Lemma 15 (any coefficients with the
  properties Lemma 15 states); the target `z` of Lemma 6 (any block with `θ c_z > G`); the head `u`
  of the new arc in Lemma 7 (any `u ∈ A_z` such that every closed set containing `u` but not `z` has
  positive `H_t`), with the value queries of Lemma 7's binary search taken as an arbitrary finite
  family of sets (they can only lower `m`); the matrix `Γ` of §7 (any matrix with orthonormal rows
  and `ΓᵀΓ = I − J'J'ᵀ`; Recenter depends on `Γ` only through `ΓᵀΓ`); and the numbering of the new
  blocks after a contraction.
* After a contraction, the zero test of step 1 is applied to the stored greedy vectors of the
  inserted rows.
* Recenter is the published `Body.recenterRun`; the new center is `J'ᵀ x̄` with
  `J' = Jᵀ J_new` (Lemma 24, p.41), its coordinates in the new basis.
-/

variable {n : ℕ}

/-- The block basis `J = (ξ_C)_C ∈ ℝ^{n×N}`, `ξ_C = 1_C/√|C|` (§5.1, p.16). -/
noncomputable def blockBasis {N : ℕ} (D : BlockDAG n N) : Matrix (Fin n) (Fin N) ℝ :=
  fun u C => if D.blk u = C then 1 / Real.sqrt (D.blockSize C) else 0

/-- The isometric vector `ã_C = a_C/√|C|` of a compressed vector `a` (§5.1, p.16). -/
noncomputable def isoVec {N : ℕ} (D : BlockDAG n N) (a : Fin N → ℝ) : Fin N → ℝ :=
  fun C => a C / Real.sqrt (D.blockSize C)

/-- The compressed weights `w_C = y_C/√|C|` of the center `z = J y` (§5.1, p.17). -/
noncomputable def compWeights {N : ℕ} (D : BlockDAG n N) (y : Fin N → ℝ) : Fin N → ℝ :=
  fun C => y C / Real.sqrt (D.blockSize C)

/-- The Euclidean norm `‖x‖₂`. -/
noncomputable def l2norm {m : ℕ} (x : Fin m → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- The lifted unit normal `b = J(ã/‖ã‖₂) ∈ S` of a nonzero compressed vector `a` on the current DAG
(§5.4, p.21). -/
noncomputable def cutDir {N : ℕ} (D : BlockDAG n N) (a : Fin N → ℝ) : Fin n → ℝ :=
  blockBasis D *ᵥ ((l2norm (isoVec D a))⁻¹ • isoVec D a)

/-- A vector returned by the separation oracle and stored with an inserted row (§4.2, p.11): the DAG
`D_i` (with its partition into blocks) at the time of the call, the compressed vector `a` on its
blocks, its label (greedy or graph), its historical ordering (meaningful for a greedy vector) and its
timestamp `t_i`. -/
structure StoredVec (n : ℕ) where
  /-- number of blocks at the time of the call -/
  N₀ : ℕ
  /-- the DAG and partition at the time of the call -/
  D₀ : BlockDAG n N₀
  /-- the compressed vector -/
  a : Fin N₀ → ℝ
  /-- `true` for a greedy vector, `false` for a graph vector -/
  greedy : Bool
  /-- the historical ordering (position map) of a greedy vector -/
  order : Equiv.Perm (Fin N₀)
  /-- the timestamp `t_i` -/
  stamp : ℝ

/-- A stored vector mapped to the current DAG `D` "by summing the values on the vertices that were
merged during contractions" (Lemma 4, p.12): an old block `C` goes to the current block containing
its elements. -/
noncomputable def StoredVec.current {N : ℕ} (s : StoredVec n) (D : BlockDAG n N) : Fin N → ℝ :=
  pushVec (fun C => D.blk (Function.surjInv s.D₀.blk_surj C)) s.a

/-- `m'` is the witness value after querying the sets of `E` starting from `m`:
`m' = min(m, min_{X ∈ E} h(X))` (§4.1, p.9). -/
def MinUpdate (h : Finset (Fin n) → ℝ) (m : ℝ) (E : Finset (Finset (Fin n))) (m' : ℝ) : Prop :=
  m' ≤ m ∧ (∀ X ∈ E, m' ≤ h X) ∧ (m' = m ∨ ∃ X ∈ E, h X = m')

/-- The sliding parameter `t = h(∅) + 1 − m` (§4.1, p.9). -/
def slide (h : Finset (Fin n) → ℝ) (m : ℝ) : ℝ := h ∅ + 1 - m

/-- The calibration sets `lift(A_z)`, `lift(B_z)` of every block `z` (§4.1, p.10). -/
noncomputable def calibSets {N : ℕ} (D : BlockDAG n N) : Finset (Finset (Fin n)) :=
  Finset.univ.image (fun z => D.lift (D.A z)) ∪ Finset.univ.image (fun z => D.lift (D.B z))

/-- The proper prefixes `lift(P_j)`, `1 ≤ j ≤ N − 1`, of the ordering with position map `σ`
(§4.2, p.11). -/
noncomputable def prefixSets {N : ℕ} (D : BlockDAG n N) (σ : Equiv.Perm (Fin N)) :
    Finset (Finset (Fin n)) :=
  (Finset.Ioo 0 N).image (fun j => D.lift (prefixSet σ j))

/-- `σ` orders the blocks by decreasing weight `w`, placing a descendant before its ancestor on ties
(§4.2, p.11). -/
def OracleOrder {N : ℕ} (D : BlockDAG n N) (w : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) : Prop :=
  (∀ u v, σ u < σ v → w v ≤ w u) ∧
  (∀ u v, w u = w v → Relation.TransGen D.arc u v → σ v < σ u)

/-- The separation oracle of §4.2 (p.11) queried at the compressed weights `w` of the center `y` on
the current DAG `D` with witness value `m`: it returns the vector `a`, its label `g` (greedy or
graph), its ordering `σ` and the new witness value `m'`.
* If some arc `u → v` has `w_u > w_v`, it returns the graph vector `e_u − e_v` (no evaluation).
* Otherwise it orders the blocks by decreasing weight (descendant first on ties), evaluates the
  proper prefixes, updates `m`, and returns the greedy vector `a_{π(j)} = H_t(P_j) − H_t(P_{j−1})`
  at the updated `t`. -/
def OracleAnswer (h : Finset (Fin n) → ℝ) {N : ℕ} (D : BlockDAG n N) (m : ℝ) (y : Fin N → ℝ)
    (m' : ℝ) (a : Fin N → ℝ) (g : Bool) (σ : Equiv.Perm (Fin N)) : Prop :=
  let w := compWeights D y
  ((∃ u v, D.arc u v ∧ w v < w u ∧ a = unitVec u - unitVec v) ∧ m' = m ∧ g = false) ∨
  ((∀ u v, D.arc u v → w u ≤ w v) ∧ OracleOrder D w σ ∧ MinUpdate h m (prefixSets D σ) m' ∧
    a = SchrijverSFM.Alg.greedy (D.Hs h (slide h m')) σ ∧ g = true)

/-- The coefficients of Lemma 15 (p.27): positive simplex coefficients `p_i` on the inserted rows
whose projection `Jᵀv_i` is nonzero (zero on the others), with
`‖Σ_i p_i Jᵀv_i/‖Jᵀv_i‖₂‖₂ ≤ χ_n/1024`. -/
def Lemma15Coeffs {N : ℕ} (P : Body n) (J : Matrix (Fin n) (Fin N) ℝ) (p : Fin P.k → ℝ) : Prop :=
  (∀ i, Jᵀ *ᵥ P.v i ≠ 0 → 0 < p i) ∧ (∀ i, Jᵀ *ᵥ P.v i = 0 → p i = 0) ∧ (∑ i, p i = 1) ∧
  l2norm (∑ i, (p i / l2norm (Jᵀ *ᵥ P.v i)) • (Jᵀ *ᵥ P.v i)) ≤ chi n / 1024

/-- The conversion of Lemma 16 (p.28): with `σ_i = ‖ã_i‖₂` the current isometric norm of the
`i`-th stored vector, `Z = Σ_i p_i/σ_i` and `α_i = (p_i/σ_i)/Z`. -/
noncomputable def convertCoeffs {k : ℕ} (σ : Fin k → ℝ) (p : Fin k → ℝ) : Fin k → ℝ :=
  fun i => (p i / σ i) / ∑ j, p j / σ j

/-- Every closed set containing `u` but not `z` has `H_t(X) > 0`, so the arc `u → z` may be added
(Lemma 7, p.14). -/
def ArcValid (h : Finset (Fin n) → ℝ) {N : ℕ} (D : BlockDAG n N) (t : ℝ) (u z : Fin N) : Prop :=
  ∀ X, D.Closed X → u ∈ X → z ∉ X → 0 < D.Hs h t X

/-- `D'` (with block map `μ`) is the quotient DAG obtained from `D` by adding the arc `u → z` and
contracting the strongly connected components (§4, p.8). -/
def IsCondensation {N N' : ℕ} (D : BlockDAG n N) (u z : Fin N) (μ : Fin N → Fin N')
    (D' : BlockDAG n N') : Prop :=
  let R : Fin N → Fin N → Prop := fun a b => D.arc a b ∨ (a = u ∧ b = z)
  (∀ x, D'.blk x = μ (D.blk x)) ∧
  (∀ a b, μ a = μ b ↔ (Relation.ReflTransGen R a b ∧ Relation.ReflTransGen R b a)) ∧
  (∀ c d, D'.arc c d ↔ ∃ a b, μ a = c ∧ μ b = d ∧ c ≠ d ∧ R a b)

/-- The control point of the algorithm: step 2 (call the oracle), step 5 with the fixed certificate
coefficients `α` on the inserted rows, or halted. -/
inductive Phase (k : ℕ) where
  /-- about to execute step 2 -/
  | oracle : Phase k
  /-- executing step 5 with the certificate coefficients `α` -/
  | cert : (Fin k → ℝ) → Phase k
  /-- terminated -/
  | halted : Phase k

/-- A state of the algorithm of §8. -/
structure State (n : ℕ) where
  /-- number of blocks of the current quotient DAG -/
  N : ℕ
  /-- the current quotient DAG -/
  D : BlockDAG n N
  /-- the witness value `m` -/
  m : ℝ
  /-- the cutting plane body (cube rows and inserted rows) -/
  P : Body n
  /-- the oracle vector stored with each inserted row -/
  stored : Fin P.k → StoredVec n
  /-- the coordinates of the center `z = J y` in the block basis -/
  y : Fin N → ℝ
  /-- the control point -/
  phase : Phase P.k
  /-- number of separation-oracle calls so far -/
  calls : ℕ

namespace State

variable (s : State n)

/-- The current compressed stored vectors `a_i` on the current DAG. -/
noncomputable def curVecs : Fin s.P.k → Fin s.N → ℝ := fun i => (s.stored i).current s.D

/-- The labels of the stored vectors. -/
def grds : Fin s.P.k → Bool := fun i => (s.stored i).greedy

/-- The timestamps of the stored vectors. -/
def stamps : Fin s.P.k → ℝ := fun i => (s.stored i).stamp

/-- The center `z = J y ∈ ℝⁿ`. -/
noncomputable def center : Fin n → ℝ := blockBasis s.D *ᵥ s.y

end State

/-- The initial empty quotient DAG: `n` singleton blocks and no arcs. -/
def initDAG (n : ℕ) : BlockDAG n n where
  blk := id
  blk_surj := Function.surjective_id
  arc := fun _ _ => False
  acyclic := fun _ hz => by cases hz <;> assumption

/-- The cube `[−1, 1]ⁿ`: no inserted rows. -/
def cubeBody (n : ℕ) : Body n := ⟨0, Fin.elim0, Fin.elim0⟩

/-- The initial state with witness value `m` (§8, p.41): empty implication graph, `P = [−1,1]ⁿ`,
center `0`, no stored vectors, no oracle calls. -/
noncomputable def initState (n : ℕ) (m : ℝ) : State n :=
  ⟨n, initDAG n, m, cubeBody n, Fin.elim0, 0, .oracle, 0⟩

/-- Initialization (§4.1, p.9; §8, p.41): query `h(∅)` and `h(U)`, set `m = min{h(∅), h(U)}`, then
calibrate the empty DAG. -/
def IsInit (h : Finset (Fin n) → ℝ) (s : State n) : Prop :=
  ∃ m₁, MinUpdate h (min (h ∅) (h Finset.univ)) (calibSets (initDAG n)) m₁ ∧ s = initState n m₁

/-- One transition of the algorithm of §8 (pp.41–42). -/
inductive Step (h : Finset (Fin n) → ℝ) : State n → State n → Prop
  /-- Step 2: the current DAG has one block; terminate. -/
  | oneBlock (s : State n) (hph : s.phase = .oracle) (hN : s.N = 1) :
      Step h s { s with phase := .halted }
  /-- Step 2: the oracle returns the zero vector; terminate (one oracle call). -/
  | zeroVec (s : State n) (hph : s.phase = .oracle) (hN : s.N ≠ 1) (m' : ℝ) (a : Fin s.N → ℝ)
      (g : Bool) (σ : Equiv.Perm (Fin s.N)) (ho : OracleAnswer h s.D s.m s.y m' a g σ)
      (ha : a = 0) :
      Step h s { s with m := m', phase := .halted, calls := s.calls + 1 }
  /-- Steps 2–3: a wide step. The oracle returns `a ≠ 0`; with `b` its lifted unit normal and
  `υ = (bᵀH_fl(z)⁻¹b/γ)^{1/2} ≥ δ`, the row `(b, υ + bᵀz)` is inserted with `a` stored, and exact
  full Newton steps of the new restricted barrier from `y` reach a certified center `y'`. -/
  | wide (s : State n) (hph : s.phase = .oracle) (hN : s.N ≠ 1) (m' : ℝ) (a : Fin s.N → ℝ)
      (g : Bool) (σ : Equiv.Perm (Fin s.N)) (ho : OracleAnswer h s.D s.m s.y m' a g σ)
      (ha : a ≠ 0)
      (hυ : delta n ≤ s.P.upsilon s.center (cutDir s.D a))
      (k : ℕ) (y' : Fin s.N → ℝ)
      (hy' : y' = (newtonStep ((s.P.insertRow (cutDir s.D a)
          (s.P.upsilon s.center (cutDir s.D a) + cutDir s.D a ⬝ᵥ s.center)).PsiS
            (blockBasis s.D)))^[k] s.y)
      (hcert : (s.P.insertRow (cutDir s.D a)
          (s.P.upsilon s.center (cutDir s.D a) + cutDir s.D a ⬝ᵥ s.center)).Certified
            (blockBasis s.D) y') :
      Step h s
        ⟨s.N, s.D, m',
          s.P.insertRow (cutDir s.D a)
            (s.P.upsilon s.center (cutDir s.D a) + cutDir s.D a ⬝ᵥ s.center),
          (Fin.snoc (α := fun _ => StoredVec n) s.stored ⟨s.N, s.D, a, g, σ, slide h m'⟩ :
            Fin (s.P.k + 1) → StoredVec n),
          y', .oracle, s.calls + 1⟩
  /-- Steps 2 and 4: a thin event. The oracle returns `a ≠ 0` with `υ < δ`; nothing is inserted;
  the coefficients of Lemma 15 are converted by Lemma 16 into the certificate `α`, and the
  algorithm goes to step 5. -/
  | thin (s : State n) (hph : s.phase = .oracle) (hN : s.N ≠ 1) (m' : ℝ) (a : Fin s.N → ℝ)
      (g : Bool) (σ : Equiv.Perm (Fin s.N)) (ho : OracleAnswer h s.D s.m s.y m' a g σ)
      (ha : a ≠ 0)
      (hυ : s.P.upsilon s.center (cutDir s.D a) < delta n)
      (p : Fin s.P.k → ℝ) (hp : Lemma15Coeffs s.P (blockBasis s.D) p) :
      Step h s
        { s with m := m',
                 phase := .cert (convertCoeffs (fun i => l2norm (isoVec s.D (s.curVecs i))) p),
                 calls := s.calls + 1 }
  /-- Step 5: the certificate has `∆ ≥ β`; terminate. -/
  | certStop (s : State n) (α : Fin s.P.k → ℝ) (hph : s.phase = .cert α)
      (hΔ : certBeta s.curVecs α ≤ certDelta α s.grds s.stamps (slide h s.m)) :
      Step h s { s with phase := .halted }
  /-- Step 5: `∆ < β`, a target `z` with `θ c_z > G` (Lemma 6); the value queries of the arc search
  (Lemma 7) raise `t` until `∆ ≥ β`; terminate. -/
  | searchStop (s : State n) (α : Fin s.P.k → ℝ) (hph : s.phase = .cert α)
      (hΔ : certDelta α s.grds s.stamps (slide h s.m) < certBeta s.curVecs α)
      (z : Fin s.N)
      (hz : guardG n (certSupp α) (certBeta s.curVecs α)
          (certDelta α s.grds s.stamps (slide h s.m)) <
        certTheta α s.grds * s.D.cz h (slide h s.m) z)
      (E : Finset (Finset (Fin n))) (m' : ℝ) (hm' : MinUpdate h s.m E m')
      (hΔ' : certBeta s.curVecs α ≤ certDelta α s.grds s.stamps (slide h m')) :
      Step h s { s with m := m', phase := .halted }
  /-- Step 5: `∆ < β`, a target `z` with `θ c_z > G` (Lemma 6), one new arc `u → z` (Lemma 7) that
  creates no strongly connected component; recalibrate and stay in step 5 with the same
  certificate. -/
  | arcAcyclic (s : State n) (α : Fin s.P.k → ℝ) (hph : s.phase = .cert α)
      (hΔ : certDelta α s.grds s.stamps (slide h s.m) < certBeta s.curVecs α)
      (z : Fin s.N)
      (hz : guardG n (certSupp α) (certBeta s.curVecs α)
          (certDelta α s.grds s.stamps (slide h s.m)) <
        certTheta α s.grds * s.D.cz h (slide h s.m) z)
      (E : Finset (Finset (Fin n))) (m' : ℝ) (hm' : MinUpdate h s.m E m')
      (u : Fin s.N) (hu : u ∈ s.D.A z) (hval : ArcValid h s.D (slide h m') u z)
      (hnc : ¬ Relation.ReflTransGen s.D.arc z u)
      (D' : BlockDAG n s.N) (hblk : D'.blk = s.D.blk)
      (harc : ∀ a b, D'.arc a b ↔ (s.D.arc a b ∨ (a = u ∧ b = z)))
      (m'' : ℝ) (hcal : MinUpdate h m' (calibSets D') m'') :
      Step h s { s with D := D', m := m'' }
  /-- Step 5 then step 1: the new arc `u → z` closes a cycle; contract to the condensation `D'`;
  a stored greedy vector that becomes zero terminates the algorithm. -/
  | contractZero (s : State n) (α : Fin s.P.k → ℝ) (hph : s.phase = .cert α)
      (hΔ : certDelta α s.grds s.stamps (slide h s.m) < certBeta s.curVecs α)
      (z : Fin s.N)
      (hz : guardG n (certSupp α) (certBeta s.curVecs α)
          (certDelta α s.grds s.stamps (slide h s.m)) <
        certTheta α s.grds * s.D.cz h (slide h s.m) z)
      (E : Finset (Finset (Fin n))) (m' : ℝ) (hm' : MinUpdate h s.m E m')
      (u : Fin s.N) (hu : u ∈ s.D.A z) (hval : ArcValid h s.D (slide h m') u z)
      (hc : Relation.ReflTransGen s.D.arc z u)
      (N' : ℕ) (D' : BlockDAG n N') (μ : Fin s.N → Fin N') (hcond : IsCondensation s.D u z μ D')
      (i : Fin s.P.k) (hi : (s.stored i).greedy = true ∧ (s.stored i).current D' = 0) :
      Step h s ⟨N', D', m', s.P, s.stored, 0, .halted, s.calls⟩
  /-- Step 5 then step 1: the new arc `u → z` closes a cycle; contract to the condensation `D'`,
  run Recenter (Algorithm 1) from the old center in the old basis with a contraction matrix `Γ`,
  express the returned center in the new basis (`J' = Jᵀ J_new`), recalibrate, and go to step 2. -/
  | contract (s : State n) (α : Fin s.P.k → ℝ) (hph : s.phase = .cert α)
      (hΔ : certDelta α s.grds s.stamps (slide h s.m) < certBeta s.curVecs α)
      (z : Fin s.N)
      (hz : guardG n (certSupp α) (certBeta s.curVecs α)
          (certDelta α s.grds s.stamps (slide h s.m)) <
        certTheta α s.grds * s.D.cz h (slide h s.m) z)
      (E : Finset (Finset (Fin n))) (m' : ℝ) (hm' : MinUpdate h s.m E m')
      (u : Fin s.N) (hu : u ∈ s.D.A z) (hval : ArcValid h s.D (slide h m') u z)
      (hc : Relation.ReflTransGen s.D.arc z u)
      (N' : ℕ) (D' : BlockDAG n N') (μ : Fin s.N → Fin N') (hcond : IsCondensation s.D u z μ D')
      (hnz : ∀ i, (s.stored i).greedy = true → (s.stored i).current D' ≠ 0)
      (Γ : Matrix (Fin (s.N - N')) (Fin s.N) ℝ) (hΓ₁ : Γ * Γᵀ = 1)
      (hΓ₂ : Γᵀ * Γ = 1 - ((blockBasis s.D)ᵀ * blockBasis D') * ((blockBasis s.D)ᵀ * blockBasis D')ᵀ)
      (j : ℕ) (κ : ℝ) (xbar : Fin s.N → ℝ) (ph nw : ℕ)
      (hrec : s.P.recenterRun (blockBasis s.D) Γ s.y j = (κ, xbar, true, ph, nw))
      (m'' : ℝ) (hcal : MinUpdate h m' (calibSets D') m'') :
      Step h s ⟨N', D', m'', s.P, s.stored, ((blockBasis s.D)ᵀ * blockBasis D')ᵀ *ᵥ xbar,
        .oracle, s.calls⟩

/-- `s` is reached from an initial state by finitely many transitions (every finite execution
prefix of the algorithm). -/
def Reachable (h : Finset (Fin n) → ℝ) (s : State n) : Prop :=
  ∃ s₀, IsInit h s₀ ∧ Relation.ReflTransGen (Step h) s₀ s

end FasterSFM.Supplement


