-- Prove2me | Definitions.Def_PolyEulerFlow_eulerOrbit
-- name    : PolyEulerFlow_eulerOrbit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:13.833553+00:00
-- url     : https://prove2.me/theorems/13363217-7909-4dd4-b8cb-d83ca5f0d3e2
-- title:
--   Euler executions, admissible meshes, physical time, active length and phase entries
-- statement:
--   The discrete semantics of a field $f$ on a normed space (Theorem 1, p.2, and the scheme (21), p.27).
--
--   Given a start $z_0$, step sizes $(\eta_k)_{k\ge0}$ and disturbances $(\xi_k)_{k\ge0}$, the **execution** is
--   $$z_{k+1}=z_k+\eta_k f(z_k)+\eta_k\xi_k .$$
--   The **physical time** of index $k$ is $t_k=\sum_{i<k}\eta_i$. A mesh is **admissible** when $0<\eta_k\le1$ for every $k$ and $\sum_k\eta_k=\infty$; a disturbance sequence is **permitted at level** $\nu$ when $\|\xi_k\|\le\nu$ for every $k$ (the update noise is $\eta_k\xi_k$). The logical scale is $h=2^{-s}$.
--
--   The **active length** between indices $a$ and $b$ is $\sum_{a\le k<b}\|z_{k+1}-z_k\|$ (Definition 7, p.6). The **first grid index** at or beyond a physical time $\tau$ is the least $k$ with $t_k\ge\tau$. The **grid sum** $\int_a^b g\,d\eta t$ is $\sum_{a\le k<b}\eta_k g(k)$ (p.27).
--
--   Given four **clock bits** $p_0,\dots,p_3$ (real functions of the state, indices modulo four), the **phase entries** after an index $k_0$ are $k_0<k_1<k_2<\cdots$, where $k_{j+1}$ is the first index strictly after $k_j$ at which $p_{(j+1)\bmod 4}\ge 9/10$ (§6.5, p.29). The internal cycle sections are the indices $k_{4j}$. The phase entries can also be computed from the orbit as successive infima; on a constant mesh $\eta$ the Euler phase-entry time is $\eta k_j$.
--
--   **Formalization Note** The execution is a function of its start, mesh and disturbances. A cycle or phase starting at a later index is the execution of the shifted mesh and disturbance, which is why the milestones start their phases at index $0$. The norm on $\mathbb R^N$ is the sup norm.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Theorem 1, p.2 (PDF 4); Definition 7, p.6 (PDF 8); (21) and grid sums, p.27 (PDF 29); §6.5, p.29 (PDF 31)

import Mathlib

namespace PolyEulerFlow

/-- The logical scale `h = 2^{-s}` (2), p.2. -/
noncomputable def scale (s : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(s : ℤ))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The execution `z₀ = z0`, `z_{k+1} = z_k + η_k f(z_k) + η_k ξ_k` of Theorem 1 (p.2) and of (21) (p.27).
Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), p.2.
**Formalization Note.** An execution is determined by its start, mesh and disturbance, so it is a function.
A cycle or a phase starting at a later index is an orbit of the shifted mesh and disturbance. -/
noncomputable def eulerOrbit (f : E → E) (z0 : E) (η : ℕ → ℝ) (ξ : ℕ → E) : ℕ → E
  | 0 => z0
  | k + 1 => eulerOrbit f z0 η ξ k + η k • f (eulerOrbit f z0 η ξ k) + η k • ξ k

/-- Physical time `t_k = Σ_{i<k} η_i` (p.2). -/
noncomputable def physTime (η : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, η i

/-- An admissible mesh: `0 < η_k ≤ 1` and `Σ_k η_k = ∞` (p.2). -/
def IsAdmissibleMesh (η : ℕ → ℝ) : Prop :=
  (∀ k, 0 < η k ∧ η k ≤ 1) ∧ Filter.Tendsto (physTime η) Filter.atTop Filter.atTop

/-- A permitted disturbance: `‖ξ_k‖ ≤ ν`. The update noise is `η_k ξ_k`. -/
def IsPermittedDisturbance (ν : ℝ) (ξ : ℕ → E) : Prop :=
  ∀ k, ‖ξ k‖ ≤ ν

/-- The active length between indices `a` and `b`: the sum of increments in sup norm (Definition 7, p.6). -/
noncomputable def activeLengthOn (z : ℕ → E) (a b : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico a b, ‖z (k + 1) - z k‖

/-- The first grid index with physical time at least `τ`.
**Formalization Note.** `sInf` of a set of naturals; the set is nonempty for an admissible mesh. -/
noncomputable def firstGrid (η : ℕ → ℝ) (τ : ℝ) : ℕ :=
  sInf {k | τ ≤ physTime η k}

/-- The grid sum `∫_a^b f dηt = Σ_{a ≤ t_k < b} η_k f(t_k)` (p.27), indexed by the grid indices. -/
noncomputable def gridSum (η f : ℕ → ℝ) (a b : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico a b, η k * f k

/-- `k'` is the first index strictly after `k` at which the orbit satisfies `P` ("first subsequent grid time",
p.29). -/
def IsFirstAfter (P : E → Prop) (z : ℕ → E) (k k' : ℕ) : Prop :=
  k < k' ∧ P (z k') ∧ ∀ i, k < i → i < k' → ¬ P (z i)

/-- The clock threshold condition of phase `j`. -/
def AboveThreshold (pv : Fin 4 → E → ℝ) (j : Fin 4) (w : E) : Prop :=
  9 / 10 ≤ pv j w

/-- `kk` lists the first `n` successive phase entries after index `k0`, with phase indices modulo four and
phase `0` active at `k0` (§6.5, p.29; Lemma 16, p.19). `pv i w` is the value of the clock bit `p_i` at `w`. -/
def IsPhaseEntriesUpTo (pv : Fin 4 → E → ℝ) (z : ℕ → E) (k0 n : ℕ) (kk : ℕ → ℕ) : Prop :=
  kk 0 = k0 ∧ ∀ j < n, IsFirstAfter (AboveThreshold pv (Fin.ofNat 4 (j + 1))) z (kk j) (kk (j + 1))

/-- `kk` lists all the successive phase entries after index `k0`. Cycle sections are `kk (4 * j)` (Theorem 1, p.2). -/
def IsPhaseEntries (pv : Fin 4 → E → ℝ) (z : ℕ → E) (k0 : ℕ) (kk : ℕ → ℕ) : Prop :=
  kk 0 = k0 ∧ ∀ j, IsFirstAfter (AboveThreshold pv (Fin.ofNat 4 (j + 1))) z (kk j) (kk (j + 1))

/-- The phase-entry indices computed from an orbit (`t^{(η)}_j` of Lemma 16 is `η * phaseEntry … j` on a constant mesh).
**Formalization Note.** `sInf` of naturals; the `0` of an empty set does not arise along the orbits of the mission,
whose phase entries exist. -/
noncomputable def phaseEntry (pv : Fin 4 → E → ℝ) (z : ℕ → E) : ℕ → ℕ
  | 0 => 0
  | j + 1 => sInf {k | phaseEntry pv z j < k ∧ AboveThreshold pv (Fin.ofNat 4 (j + 1)) (z k)}

end PolyEulerFlow


