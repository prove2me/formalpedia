-- Prove2me | Definitions.Def_PairwiseRealize_PartialColoring
-- name    : PairwiseRealize_PartialColoring
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:55.061595+00:00
-- url     : https://prove2.me/theorems/4ebb5ee9-a9ab-4147-8a6a-72255c46e096
-- title:
--   §C.1, pp.15–16 — one step and the runs of the partial coloring
-- statement:
--   Fix $16\le s\le m$ and $A\in\{0,1\}^{m\times s}$. The $M=2m$ normals are $v_{(r,\pm)}=\pm A_r/\lceil\sqrt s\rceil$, and $P_0=\lceil\log_2(256M/s)\rceil$, $\lambda=\lceil\sqrt{P_0}\rceil$, $\Delta=1/\lambda$, $\rho=1-8/s$, $\eta=1/(64s)$, $\varepsilon_{\mathrm{mesh}}=2^{-\lceil\log_2(64s^2\lambda^2)\rceil}$. A state is a point $x\in[-1,1]^s$ with weights $w$; a coordinate is **frozen** when $|x_j|=1$, and $\Phi=\sum_iw_i$.
--
--   A **step** from $(x,w)$ to $(x',w')$ requires:
--
--   1. more than $s/2$ coordinates of $x$ are unfrozen;
--   2. there is a direction $z$ vanishing on the frozen coordinates, orthogonal to $x$, to $\sum_iw_iv_i$ and to the $\lfloor s/16\rfloor$ normals of largest weight (ties by a fixed index order), with $1/2\le\|z\|_2\le1$ and $z^{\mathsf T}M_wz\le4\Phi/s$, where $M_w=\sum_iw_iv_iv_i^{\mathsf T}$; with $\alpha$ the largest element of $(0,1]$ such that $\tilde x=x+\Delta\alpha z$ lies in the box, each coordinate with $|\tilde x_j|=1$ is kept and every other coordinate is rounded to a nearest mesh point;
--   3. each new weight satisfies $(1-\eta)\,w_i\rho\,e^{\lambda\langle v_i,x'-x\rangle}\le w_i'\le w_i\rho\,e^{\lambda\langle v_i,x'-x\rangle}$.
--
--   A **run** starts from any $x^{(0)}\in[-1,1]^s$ with all weights $2^{-P_0}$, and consecutive states are related by a step.
--
--   **Formalization Note** The procedure is stated as a relation, so Lemmas C.2 and C.3 cover every implementation that meets the §C.1 specification, including the rational one of §C.2.
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §C.1, pp.15–16 (PDF pp.16–17), (C.1)–(C.3)

import Mathlib

namespace PairwiseRealize

namespace PartialColoring

/-!
# The partial coloring procedure of Appendix C.1

K. Shi, H. Sun, *Robust Exact Realization of Pairwise Boolean Statistics*, STOC 2027 submission
(manuscript sha256 62090516…), §C.1 "Partial coloring", printed pp.15–16 (PDF pp.16–17).

"Consider m binary rows restricted to s active variables, where 16 ≤ s ≤ m, and rational start
x(0) ∈ [−1, 1]^s. Use both signs of each row, so there are M = 2m normals vᵢ = ±Aᵢ/⌈√s⌉ […]
P0 = ⌈log₂(256M/s)⌉, λ = ⌈√P0⌉, Δ = 1/λ, ρ = 1 − 8/s, η = 1/(64s). […] ε_mesh = 2^{−⌈log₂(64s²λ²)⌉}.
[…] Begin with rational weights wᵢ = 2^{−P0}". Each step: "Keep coordinates at ±1 frozen. While
more than s/2 coordinates are unfrozen, let U be the active-coordinate subspace orthogonal to the
current x, the gradient Σᵢ wᵢvᵢ, and the ⌊s/16⌋ normals of largest weight. Ties follow a fixed index
order. […] For M_w = Σᵢ wᵢvᵢvᵢᵀ, choose a rational direction z ∈ U, 1/2 ≤ ‖z‖₂ ≤ 1, such that
zᵀM_w z ≤ 4Φ/s. (C.1) […] Take the largest α ∈ (0, 1] such that x̃ = x + Δαz lies in the box. Round
unfrozen coordinates to the nearest mesh point, keeping every boundary coordinate exactly at ±1, to
obtain x′. […] Update wᵢ by a rational downward approximation to wᵢρ exp(λ⟨vᵢ, x′ − x⟩), (C.3)
with relative loss at most η. […] Repeat until at least half the coordinates are frozen."

**Formalization Note** The procedure is stated as a relation `ValidStep` between consecutive states
`(x, w)`, and a run is any sequence of states starting from `x(0) ∈ [−1,1]^s` and the weights
`2^{−P0}` whose consecutive pairs satisfy it. Lemmas C.2 and C.3 are then statements about every run.
This includes the paper's rational implementation (§C.2), which is one way to meet the specification;
rationality of `x(0)`, `z` and the weights is not required. Normals are indexed by `Fin m × Bool`,
`(r, true) ↦ +A_r/⌈√s⌉` and `(r, false) ↦ −A_r/⌈√s⌉`. The fixed tie-breaking order is
`(r, true), (r, false)` by increasing `r`. Vectors are plain functions `Fin s → ℝ`;
`⟨u, v⟩ = u ⬝ᵥ v` and `‖z‖₂ = √(z ⬝ᵥ z)`. A coordinate `j` is frozen when `|x_j| = 1`.
`⌈log₂ ·⌉` is `Int.ceil (Real.logb 2 ·)`.
-/

variable {m s : ℕ}

/-- The `0/1` entry of a Boolean matrix as a real number. -/
def entry (A : Fin m → Fin s → Bool) (r : Fin m) (j : Fin s) : ℝ := if A r j then 1 else 0

/-- The unsigned normal `A_r/⌈√s⌉`. -/
noncomputable def rowNormal (A : Fin m → Fin s → Bool) (r : Fin m) : Fin s → ℝ :=
  fun j => entry A r j / (⌈Real.sqrt s⌉₊ : ℝ)

/-- The signed normals `v_{(r,+)} = A_r/⌈√s⌉`, `v_{(r,−)} = −A_r/⌈√s⌉`. -/
noncomputable def normal (A : Fin m → Fin s → Bool) (i : Fin m × Bool) : Fin s → ℝ :=
  fun j => (if i.2 then 1 else -1) * rowNormal A i.1 j

/-- `P0 = ⌈log₂(256M/s)⌉` with `M = 2m`. -/
noncomputable def P0 (m s : ℕ) : ℤ := ⌈Real.logb 2 (256 * (2 * m) / s)⌉

/-- `λ = ⌈√P0⌉`. -/
noncomputable def lam (m s : ℕ) : ℝ := (⌈Real.sqrt (P0 m s)⌉ : ℤ)

/-- `Δ = 1/λ`. -/
noncomputable def Delta (m s : ℕ) : ℝ := 1 / lam m s

/-- `ρ = 1 − 8/s`. -/
noncomputable def rho (s : ℕ) : ℝ := 1 - 8 / (s : ℝ)

/-- `η = 1/(64s)`. -/
noncomputable def eta (s : ℕ) : ℝ := 1 / (64 * (s : ℝ))

/-- The dyadic mesh `ε_mesh = 2^{−⌈log₂(64s²λ²)⌉}`. -/
noncomputable def epsMesh (m s : ℕ) : ℝ :=
  (2 : ℝ) ^ (-⌈Real.logb 2 (64 * (s : ℝ) ^ 2 * lam m s ^ 2)⌉)

/-- The initial weight `2^{−P0}`. -/
noncomputable def w0 (m s : ℕ) : ℝ := (2 : ℝ) ^ (-P0 m s)

/-- The unfrozen coordinates of `x`: those with `|x_j| ≠ 1`. -/
noncomputable def unfrozen (x : Fin s → ℝ) : Finset (Fin s) :=
  Finset.univ.filter fun j => |x j| ≠ 1

/-- The potential `Φ(w) = Σᵢ wᵢ`. -/
def Phi (w : Fin m × Bool → ℝ) : ℝ := ∑ i, w i

/-- The weighted gradient `Σᵢ wᵢvᵢ`. -/
noncomputable def grad (A : Fin m → Fin s → Bool) (w : Fin m × Bool → ℝ) : Fin s → ℝ :=
  ∑ i, w i • normal A i

/-- The quadratic form `zᵀM_w z = Σᵢ wᵢ⟨vᵢ, z⟩²` of `M_w = Σᵢ wᵢvᵢvᵢᵀ`. -/
noncomputable def quad (A : Fin m → Fin s → Bool) (w : Fin m × Bool → ℝ) (z : Fin s → ℝ) : ℝ :=
  ∑ i, w i * (normal A i ⬝ᵥ z) ^ 2

/-- The fixed index order used to break ties: `(r, +)` has index `2r`, `(r, −)` has `2r + 1`. -/
def idx (i : Fin m × Bool) : ℕ := 2 * i.1.val + if i.2 then 0 else 1

/-- The `⌊s/16⌋` normals of largest weight, ties broken by `idx`: `i` belongs to it when fewer than
`⌊s/16⌋` normals come before it in the order (weight descending, index ascending). -/
noncomputable def topSet (s : ℕ) (w : Fin m × Bool → ℝ) : Finset (Fin m × Bool) :=
  Finset.univ.filter fun i =>
    (Finset.univ.filter fun j => w i < w j ∨ (w j = w i ∧ idx j < idx i)).card < s / 16

/-- One step of the partial coloring, from the state `(x, w)` to `(x', w')`:
1. more than `s/2` coordinates of `x` are unfrozen;
2. there is a direction `z` vanishing on the frozen coordinates, orthogonal to `x`, to the gradient
   and to the top normals, with `1/2 ≤ ‖z‖₂ ≤ 1` and `zᵀM_w z ≤ 4Φ/s` (C.1); with `α` the largest
   `α ∈ (0, 1]` such that `x̃ = x + Δαz ∈ [−1, 1]^s`, every coordinate with `|x̃_j| = 1` is kept
   (`x'_j = x̃_j`) and every other coordinate is rounded to a nearest point of the mesh `ε_mesh ℤ`;
3. every new weight is a downward approximation of `wᵢρ exp(λ⟨vᵢ, x′ − x⟩)` (C.3) with relative
   loss at most `η`. -/
def ValidStep (A : Fin m → Fin s → Bool) (x : Fin s → ℝ) (w : Fin m × Bool → ℝ)
    (x' : Fin s → ℝ) (w' : Fin m × Bool → ℝ) : Prop :=
  s < 2 * (unfrozen x).card ∧
  (∃ z : Fin s → ℝ, ∃ α : ℝ,
    (∀ j, |x j| = 1 → z j = 0) ∧ z ⬝ᵥ x = 0 ∧ z ⬝ᵥ grad A w = 0 ∧
    (∀ i ∈ topSet s w, normal A i ⬝ᵥ z = 0) ∧
    1 / 2 ≤ Real.sqrt (z ⬝ᵥ z) ∧ Real.sqrt (z ⬝ᵥ z) ≤ 1 ∧
    quad A w z ≤ 4 * Phi w / s ∧
    IsGreatest {a : ℝ | a ∈ Set.Ioc 0 1 ∧ ∀ j, |x j + Delta m s * a * z j| ≤ 1} α ∧
    ∀ j, (|x j + Delta m s * α * z j| = 1 → x' j = x j + Delta m s * α * z j) ∧
      (|x j + Delta m s * α * z j| ≠ 1 →
        (∃ k : ℤ, x' j = k * epsMesh m s) ∧
        ∀ k : ℤ, |x' j - (x j + Delta m s * α * z j)| ≤
          |k * epsMesh m s - (x j + Delta m s * α * z j)|)) ∧
  ∀ i, (1 - eta s) * (w i * rho s * Real.exp (lam m s * (normal A i ⬝ᵥ (x' - x)))) ≤ w' i ∧
    w' i ≤ w i * rho s * Real.exp (lam m s * (normal A i ⬝ᵥ (x' - x)))

/-- A run of `T` steps: states `(x(t), w(t))`, `t = 0, …, T`, with `x(0) ∈ [−1, 1]^s`, all initial
weights `2^{−P0}`, and every consecutive pair a `ValidStep`. -/
def IsRun (A : Fin m → Fin s → Bool) (T : ℕ) (x : Fin (T + 1) → Fin s → ℝ)
    (w : Fin (T + 1) → Fin m × Bool → ℝ) : Prop :=
  (∀ j, |x 0 j| ≤ 1) ∧ (∀ i, w 0 i = w0 m s) ∧
    ∀ t : Fin T, ValidStep A (x t.castSucc) (w t.castSucc) (x t.succ) (w t.succ)

end PartialColoring

end PairwiseRealize


