-- Prove2me | Definitions.Def_ProjRescale_MaxSupport_Setting
-- name    : ProjRescale_MaxSupport_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:48.89002+00:00
-- url     : https://prove2.me/theorems/3896db3e-bb85-4f7f-8629-d81a11c4caf6
-- title:
--   §2, pp. 4–8 — J(L), σ_i(L), σ(L), ℝ^J, Δ(J), P_{DL|J}, the basic procedure, Algorithm 1 (partial support) and Algorithm 2 (maximum support)
-- statement:
--   The objects of §2 of Peña and Soheili, *Projection and rescaling algorithm for finding maximum support solutions to polyhedral conic systems* (pp. 4–8).
--
--   **Space and orthant.** Work in $\mathbb R^n$ with the standard inner product, coordinates $x_1,\dots,x_n$, and the nonnegative orthant $\mathbb R^n_+ = \{x : x_j \ge 0 \text{ for all } j\}$. For a linear subspace $L \subseteq \mathbb R^n$, $L^\perp = \{s : \langle s, x\rangle = 0 \text{ for all } x \in L\}$. Write $\|x\|_\infty = \max_j |x_j|$, $\|x\|_1 = \sum_j |x_j|$ and $v^+ = (\max(v_j,0))_j$.
--
--   **Maximum support and condition measures.** The *maximum support index set* of $L$ is
--
--   $$J(L) = \{ j \in \{1,\dots,n\} : x_j > 0 \text{ for some } x \in L \cap \mathbb R^n_+ \}.$$
--
--   For $i \in \{1,\dots,n\}$,
--
--   $$\sigma_i(L) = \max\{ x_i : x \in L \cap \mathbb R^n_+,\ \|x\|_\infty \le 1 \},$$
--
--   and the condition measure is $\sigma(L) = \min_{j \in J(L)} \max\{x_j : x \in L\cap\mathbb R^n_+,\ \|x\|_\infty \le 1\}$, with the convention $\sigma(L) = 1$ when $J(L) = \emptyset$. A point $x \in L \cap \mathbb R^n_+$ is a *maximum support point* if its support $\{j : x_j > 0\}$ equals $J(L)$.
--
--   **Coordinate subspaces and projections.** For $J \subseteq \{1,\dots,n\}$, $\mathbb R^J = \{x : x_i = 0 \text{ for } i \notin J\}$ and $\Delta(J) = \{x \in \mathbb R^J : x \ge 0,\ \|x\|_1 = 1\}$. For a positive diagonal matrix $D$, $DL = \{Dx : x \in L\}$, and $P_{DL|J}$ is the orthogonal projection onto $DL \cap \mathbb R^J$.
--
--   **Algorithm 1 (Partial support), input $(L, \sigma)$.** Start with $D = I$ and $J = \{1,\dots,n\}$. Let $P = P_{DL|J}$. The *basic procedure* returns either some $u \in \Delta(J)$ with $(Pu)_j > 0$ for all $j \in J$, in which case the algorithm halts with output $x = D^{-1}Pu$ and $J$; or some $z \in \Delta(J)$ with
--
--   $$\|(Pz)^+\|_1 \le \tfrac12 \|z\|_\infty,$$
--
--   in which case, with $i$ a maximizer of $z_j$, the algorithm doubles $D_{ii}$ (that is, $D := (I + e_ie_i^{\mathsf T})D$), removes $i$ from $J$ if the new $D_{ii}$ exceeds $1/\sigma$, halts with output $x = 0$, $J = \emptyset$ if $J$ has become empty, and otherwise repeats. Each pass through this second branch is one *rescaling step*. The notation $(x, J) = \mathcal J(L, \sigma)$ means that Algorithm 1 on input $(L,\sigma)$ outputs $(x,J)$.
--
--   **Algorithm 2 (Maximum support), input $L$.** Start with $\sigma = 1/2$. In each *main iteration*, compute $(x, J) = \mathcal J(L,\sigma)$ and then $(\hat x, \hat J) = \mathcal J(L^\perp, \sigma)$; if $J \cup \hat J = \{1,\dots,n\}$ halt, otherwise replace $\sigma$ by $\sigma^2$ and start the next main iteration.
--
--   **Corrected iteration count.** For $m \in (0,1]$, $k(m) = \max\{1,\ \lceil \log_2 \log_2 (1/m)\rceil + 1\}$; Theorem 1 uses it with $m = \min\{\sigma(L), \sigma(L^\perp)\}$.
--
--   These objects carry every statement of the mission: the partition of $\{1,\dots,n\}$ by $J(L)$ and $J(L^\perp)$, the effect of one rescaling on $\sigma_i$ (Lemma 1), the analysis of Algorithm 1 (Proposition 1, Corollary 1) and of Algorithm 2 (Theorem 1).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, whose norm is the Euclidean one, so $\|x\|_\infty$ (`supNorm`) and $\|(v)^+\|_1$ (`posL1`) are written out coordinatewise, and on $\mathbb R^n_+$ the constraint $\|x\|_\infty \le 1$ is $x_j \le 1$ for all $j$. $\sigma_i(L)$ is a real `sSup` of a set that contains $0$ and is bounded above by $1$, so it is the paper's maximum. $D$ is stored as its diagonal $d$, and $DL$ is the image of $L$ under $\mathrm{diag}(d)$. `projDLJ L d J` is the orthogonal projection of $\mathbb R^n$ onto $DL \cap \mathbb R^J$; restricted to $\mathbb R^J$ it is the paper's $P_{DL|J}$, and the algorithm applies it only to points of $\Delta(J) \subseteq \mathbb R^J$. The algorithms are *transition relations*: `A1Step L σ` and `A2Step L` allow every admissible answer of the basic procedure and every maximizer $i$, and the states carry counters of rescaling steps and of main iterations. `A1Halts L σ x J r` says that some execution of Algorithm 1 on $(L,\sigma)$ halts with output $(x,J)$ after $r$ rescaling steps. $\lceil\cdot\rceil$ in $k(m)$ is `Int.ceil` followed by `Int.toNat`, and $\log_2$ is `Real.logb 2`.
-- source:
--   Peña & Soheili, Projection and rescaling algorithm for finding maximum support solutions to polyhedral conic systems, arXiv:2003.08911v3, pp. 4–8, §2 (J(L), σ(L) p. 4; ℝ^J, Δ(J), P_{L|J}, σ_i(L) p. 5; Algorithm 1 p. 6; 𝒥(L, σ) p. 7; Algorithm 2 and Equation (6) p. 8)

import Mathlib

namespace ProjRescale.MaxSupport

open scoped InnerProductSpace

/-- The Euclidean space `ℝⁿ`, with coordinates indexed by `Fin n` (the paper's `{1, …, n}`). -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The nonnegative orthant `ℝⁿ₊ = {x : x_j ≥ 0 for all j}` (p. 2). -/
def nonneg (n : ℕ) : Set (E n) := {x | ∀ j, 0 ≤ x j}

/-- The `ℓ∞` norm `‖x‖∞ = max_j |x_j|`, written coordinatewise (the norm of `E n` is `ℓ²`). -/
noncomputable def supNorm {n : ℕ} (x : E n) : ℝ := ⨆ j, |x j|

/-- `‖(v)⁺‖₁ = ∑_j max(v_j, 0)`, the `ℓ₁` norm of the positive part of `v`. -/
noncomputable def posL1 {n : ℕ} (v : E n) : ℝ := ∑ j, max (v j) 0

open Classical in
/-- The maximum support index set (§2, p. 4):
`J(L) = {j ∈ {1, …, n} : x_j > 0 for some x ∈ L ∩ ℝⁿ₊}`. -/
noncomputable def maxSupp {n : ℕ} (L : Submodule ℝ (E n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ∃ x ∈ L, x ∈ nonneg n ∧ 0 < x j)

/-- `σ_i(L) = max{x_i : x ∈ L ∩ ℝⁿ₊, ‖x‖∞ ≤ 1}` (§2, p. 5). On `ℝⁿ₊` the constraint `‖x‖∞ ≤ 1`
is `x_j ≤ 1` for all `j`. The set is nonempty (it contains `0`) and bounded above by `1`, so the
real `sSup` is the paper's maximum. -/
noncomputable def sigmaI {n : ℕ} (L : Submodule ℝ (E n)) (i : Fin n) : ℝ :=
  sSup ((fun x : E n => x i) '' {x | x ∈ L ∧ x ∈ nonneg n ∧ ∀ j, x j ≤ 1})

/-- The condition measure (§2, p. 4):
`σ(L) = min_{j ∈ J(L)} max{x_j : x ∈ L ∩ ℝⁿ₊, ‖x‖∞ ≤ 1}`, and `σ(L) = 1` when `J(L) = ∅`. -/
noncomputable def condMeasure {n : ℕ} (L : Submodule ℝ (E n)) : ℝ :=
  if h : (maxSupp L).Nonempty then (maxSupp L).inf' h (sigmaI L) else 1

/-- `ℝ^J = {x ∈ ℝⁿ : x_i = 0 for i ∉ J}` (§2, p. 5). -/
def coordSub {n : ℕ} (J : Finset (Fin n)) : Submodule ℝ (E n) where
  carrier := {x | ∀ i, i ∉ J → x i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by
    intro i _
    simp
  smul_mem' := by
    intro c x hx i hi
    simp [hx i hi]

/-- `Δ(J) = {x ∈ ℝ^J : x ≥ 0, ‖x‖₁ = 1}` (§2, p. 5). It is empty when `J = ∅`. -/
def simplexJ {n : ℕ} (J : Finset (Fin n)) : Set (E n) :=
  {u | (∀ i, 0 ≤ u i) ∧ (∀ i, i ∉ J → u i = 0) ∧ ∑ i, u i = 1}

/-- The rescaled subspace `DL = {Dx : x ∈ L}` for the diagonal matrix `D = diag(d)`. -/
noncomputable def diagScale {n : ℕ} (d : Fin n → ℝ) (L : Submodule ℝ (E n)) :
    Submodule ℝ (E n) :=
  L.map (Matrix.toEuclideanLin (Matrix.diagonal d))

/-- The orthogonal projection onto `DL ∩ ℝ^J`, as a map `ℝⁿ → ℝⁿ`. Restricted to `ℝ^J` it is the
paper's `P_{DL|J} : ℝ^J → DL ∩ ℝ^J` (§2, p. 5), because `DL ∩ ℝ^J ⊆ ℝ^J`; Algorithm 1 only
applies it to points of `Δ(J) ⊆ ℝ^J`. -/
noncomputable def projDLJ {n : ℕ} (L : Submodule ℝ (E n)) (d : Fin n → ℝ)
    (J : Finset (Fin n)) : E n →L[ℝ] E n :=
  (diagScale d L ⊓ coordSub J).starProjection

/-- `x` is a maximum support point of `L ∩ ℝⁿ₊`: `x ∈ L ∩ ℝⁿ₊` and its support
`{j : x_j > 0}` is `J(L)` (§2, p. 4). -/
def IsMaxSupportPoint {n : ℕ} (L : Submodule ℝ (E n)) (x : E n) : Prop :=
  x ∈ L ∧ x ∈ nonneg n ∧ ∀ j, (0 < x j ↔ j ∈ maxSupp L)

/-! ### Algorithm 1 (Partial support, p. 6) -/

/-- States of Algorithm 1. `run D J r`: current diagonal scaling `D = diag(d)`, current index set
`J`, and `r` rescaling steps performed so far. `halt x J r`: Algorithm 1 has halted with output
`(x, J)` after `r` rescaling steps. -/
inductive A1State (n : ℕ) where
  | run (d : Fin n → ℝ) (J : Finset (Fin n)) (r : ℕ)
  | halt (x : E n) (J : Finset (Fin n)) (r : ℕ)

/-- Step 1 (Initialization): `D := I`, `J := {1, …, n}`, no rescaling step yet. -/
def A1Init (n : ℕ) : A1State n := .run (fun _ => 1) Finset.univ 0

/-- The number of rescaling steps performed so far. -/
def A1State.rescalings {n : ℕ} : A1State n → ℕ
  | .run _ _ r => r
  | .halt _ _ r => r

/-- `s` is a running (not halted) state of Algorithm 1. -/
def A1State.IsRun {n : ℕ} : A1State n → Prop
  | .run _ _ _ => True
  | .halt _ _ _ => False

open Classical in
/-- Step 5 (Rescale `L` & Trim `J`) with `i = argmax_j z_j`: `D := (I + e_i e_iᵀ) D` doubles `D_ii`;
if the new `D_ii > 1/σ` then `J := J \ {i}`; if `J = ∅` then HALT with output `x = 0` and `J = ∅`;
otherwise go back to step 2. The rescaling-step counter increases by one. -/
noncomputable def rescaleNext {n : ℕ} (σ : ℝ) (d : Fin n → ℝ) (J : Finset (Fin n)) (r : ℕ)
    (i : Fin n) : A1State n :=
  let d' := Function.update d i (2 * d i)
  let J' := if 1 / σ < d' i then J.erase i else J
  if J' = ∅ then .halt 0 ∅ (r + 1) else .run d' J' (r + 1)

/-- One step of Algorithm 1 on input `(L, σ)`, with `P := P_{DL|J}` (step 2). The basic procedure
(step 3) may return **any** admissible answer:
* `found`: some `u ∈ Δ(J)` with `(Pu)_J > 0`; then HALT with output `x = D⁻¹Pu` and `J` (step 4);
* `rescale`: some `z ∈ Δ(J)` with `‖(Pz)⁺‖₁ ≤ ½‖z‖∞`, and `i` any maximizer of `z_j`; then
  step 5 (`rescaleNext`). -/
inductive A1Step {n : ℕ} (L : Submodule ℝ (E n)) (σ : ℝ) : A1State n → A1State n → Prop
  | found (d : Fin n → ℝ) (J : Finset (Fin n)) (r : ℕ) (u : E n) (hu : u ∈ simplexJ J)
      (hpos : ∀ j ∈ J, 0 < projDLJ L d J u j) :
      A1Step L σ (.run d J r) (.halt (WithLp.toLp 2 (fun j => (d j)⁻¹ * projDLJ L d J u j)) J r)
  | rescale (d : Fin n → ℝ) (J : Finset (Fin n)) (r : ℕ) (z : E n) (i : Fin n)
      (hz : z ∈ simplexJ J) (hi : ∀ j, z j ≤ z i)
      (hcert : posL1 (projDLJ L d J z) ≤ supNorm z / 2) :
      A1Step L σ (.run d J r) (rescaleNext σ d J r i)

/-- `𝒥(L, σ) = (x, J)` (p. 7): some execution of Algorithm 1 on input `(L, σ)` halts with output
`(x, J)` after `r` rescaling steps. -/
def A1Halts {n : ℕ} (L : Submodule ℝ (E n)) (σ : ℝ) (x : E n) (J : Finset (Fin n)) (r : ℕ) :
    Prop :=
  Relation.ReflTransGen (A1Step L σ) (A1Init n) (.halt x J r)

/-! ### Algorithm 2 (Maximum support, p. 8) -/

/-- States of Algorithm 2. `R` counts the rescaling steps of the completed calls of Algorithm 1.
* `callL i σ R s`: main iteration `i` with guess `σ`, running `𝒥(L, σ)` (inner state `s`);
* `callLperp i σ R x J s`: `𝒥(L, σ)` returned `(x, J)`; running `𝒥(L⊥, σ)` (inner state `s`);
* `done i R x J xh Jh`: Algorithm 2 halted in main iteration `i` with outputs `(x, J)`, `(x̂, Ĵ)`. -/
inductive A2State (n : ℕ) where
  | callL (i : ℕ) (σ : ℝ) (R : ℕ) (s : A1State n)
  | callLperp (i : ℕ) (σ : ℝ) (R : ℕ) (x : E n) (J : Finset (Fin n)) (s : A1State n)
  | done (i : ℕ) (R : ℕ) (x : E n) (J : Finset (Fin n)) (xh : E n) (Jh : Finset (Fin n))

/-- Step 1: `σ := 1/2`, main iteration `1`, start `𝒥(L, σ)`. -/
noncomputable def A2Init (n : ℕ) : A2State n := .callL 1 (1 / 2) 0 (A1Init n)

/-- The index of the current main iteration. -/
def A2State.iter {n : ℕ} : A2State n → ℕ
  | .callL i _ _ _ => i
  | .callLperp i _ _ _ _ _ => i
  | .done i _ _ _ _ _ => i

/-- The total number of rescaling steps performed so far, including those of a running call. -/
def A2State.rescalings {n : ℕ} : A2State n → ℕ
  | .callL _ _ R s => R + s.rescalings
  | .callLperp _ _ R _ _ s => R + s.rescalings
  | .done _ R _ _ _ _ => R

/-- `s` is a halted state of Algorithm 2. -/
def A2State.IsDone {n : ℕ} : A2State n → Prop
  | .done _ _ _ _ _ _ => True
  | _ => False

/-- One step of Algorithm 2 on input `L` (p. 8): run `𝒥(L, σ)`, then `𝒥(L⊥, σ)` (step 2); if
`J ∪ Ĵ = {1, …, n}` then HALT (step 3), else `σ := σ²` and go back to step 2 (step 4). -/
inductive A2Step {n : ℕ} (L : Submodule ℝ (E n)) : A2State n → A2State n → Prop
  | stepL (i : ℕ) (σ : ℝ) (R : ℕ) (s s' : A1State n) (h : A1Step L σ s s') :
      A2Step L (.callL i σ R s) (.callL i σ R s')
  | retL (i : ℕ) (σ : ℝ) (R : ℕ) (x : E n) (J : Finset (Fin n)) (r : ℕ) :
      A2Step L (.callL i σ R (.halt x J r)) (.callLperp i σ (R + r) x J (A1Init n))
  | stepLperp (i : ℕ) (σ : ℝ) (R : ℕ) (x : E n) (J : Finset (Fin n)) (s s' : A1State n)
      (h : A1Step Lᗮ σ s s') :
      A2Step L (.callLperp i σ R x J s) (.callLperp i σ R x J s')
  | halt (i : ℕ) (σ : ℝ) (R : ℕ) (x : E n) (J : Finset (Fin n)) (xh : E n) (Jh : Finset (Fin n))
      (r : ℕ) (hcov : J ∪ Jh = Finset.univ) :
      A2Step L (.callLperp i σ R x J (.halt xh Jh r)) (.done i (R + r) x J xh Jh)
  | next (i : ℕ) (σ : ℝ) (R : ℕ) (x : E n) (J : Finset (Fin n)) (xh : E n) (Jh : Finset (Fin n))
      (r : ℕ) (hcov : J ∪ Jh ≠ Finset.univ) :
      A2Step L (.callLperp i σ R x J (.halt xh Jh r)) (.callL (i + 1) (σ ^ 2) (R + r) (A1Init n))

/-- The corrected iteration bound (6): `k = max{1, ⌈log₂ log₂(1/m)⌉ + 1}` for
`m = min{σ(L), σ(L⊥)}`. -/
noncomputable def kIter (m : ℝ) : ℕ :=
  max 1 (⌈Real.logb 2 (Real.logb 2 (1 / m))⌉ + 1).toNat

end ProjRescale.MaxSupport


