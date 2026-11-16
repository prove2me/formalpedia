-- Prove2me | Definitions.Def_GaussMixHH_Supplement_RecoveryLayout
-- name    : GaussMixHH_Supplement_RecoveryLayout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:35:58.804091+00:00
-- url     : https://prove2.me/theorems/5d7b5b0b-9879-44e0-91c4-092b2ce04e02
-- title:
--   Input and output layout of the recovery algorithm, and the recovery guarantee (RP)
-- statement:
--   This definition fixes how an algorithm for the **recovery problem** (RP) receives its parameters and returns its list, on the real RAM of the mission, and states the guarantee (RP) itself.
--
--   1. **Input.** Pointer register $0$ holds the dimension $n$; memory cells $0,1,2$ hold $\varepsilon_{wt},\varepsilon_{dist},\Delta_{\min}$.
--   2. **Output**, read when the machine halts: the list length $L$ is pointer register $1$ (truncated at $0$; any natural number). For $j<L$, the point $z_j\in\mathbb R^n$ occupies memory cells $j(n+1),\dots,j(n+1)+n-1$ and its weight $\widehat w_j$ occupies cell $j(n+1)+n$.
--   3. **(RP).** Let $\mathcal D$ be a center distribution with positive-weight atoms $\mathrm{Supp}$ and weights $\mathcal D(\mu)$. The list $(z_j,\widehat w_j)_{j<L}$ solves (RP) if there is an injective map $\rho$ from the list positions $\{0,\dots,L-1\}$ into $\mathrm{Supp}$ such that
--      - (Soundness) for every $j$, $\|z_j-\rho(j)\|\le\varepsilon_{dist}$ and $|\widehat w_j-\mathcal D(\rho(j))|\le\varepsilon_{wt}$;
--      - (Completeness) every $\mu\in\mathrm{Supp}$ with $\mathcal D(\mu)\ge 2\varepsilon_{wt}$ equals $\rho(j)$ for some $j$.
--
--   (RP) is the paper's recovery problem (p.3): find approximately every heavy center of the mixture together with its weight, and report nothing spurious. Theorem 4 is stated with this layout.
--
--   **Formalization Note** The paper names no layout for $\mathrm{Recover}(\varepsilon_{wt},\varepsilon_{dist},\Delta_{\min})$; this one is a reading. Indices run over $0,\dots,L-1$ (the paper's $1,\dots,L$). The paper writes $\rho$ on the points $z_1,\dots,z_L$; here it is indexed by list positions, which forbids two positions being sent to the same center. When $\varepsilon_{dist}<\Delta_{\min}/2$, equal points at two positions would have to be sent to the same center, so the position form is the paper's map on a list without repetitions.
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), (RP), p.3 (PDF p.5); Theorem 4, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussMixHH_CenterModel

open MeasureTheory

namespace GaussMixHH.Supplement

open GaussMixHH

/-!
# Inputs and outputs of the recovery algorithm, and the recovery guarantee (RP)

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), (RP), p.3 (PDF p.5), and
Theorem 4, p.5 (PDF p.7).

**Formalization Note.**
* The paper names no input or output layout for `Recover(εwt, εdist, ∆min)`; this one is a reading.
  Input: pointer `0` holds `n` and memory cells `0, 1, 2` hold `εwt, εdist, ∆min`
  (`recoverInput`, built with the published `GaussMixHH.initState`).
* Output, read at `halt`: the list length is `L = (p[1]).toNat` (pointer register `1`, any natural
  number); for `j < L` the point `z_j ∈ ℝⁿ` occupies memory cells `j(n+1), …, j(n+1)+n−1` and its
  weight `ŵ_j` occupies cell `j(n+1)+n`. Indices run over `0, …, L−1` (the paper's `1, …, L`).
* `IsRecoveryOutput D εwt εdist L z w` is (RP) for the list `(z_j, ŵ_j)_{j<L}`: there is an
  injective map `ρ` from the list indices to `Supp D` (the positive-weight atoms of `D`) with
  (Soundness) `∥z_j − ρ(j)∥ ≤ εdist` and `|ŵ_j − D(ρ(j))| ≤ εwt` for every `j`, and
  (Completeness) every `μ ∈ Supp D` with `D(μ) ≥ 2εwt` is `ρ(j)` for some `j`. `D(μ)` is
  `(D {μ}).toReal`. The paper writes `ρ` on the points `z_1, …, z_L`; indexing it by positions is
  the same map when the points are distinct and never weaker (injective on positions forbids two
  copies of one point being sent to one center).
-/

/-- The input of Theorem 4: `n` in pointer `0`; `εwt, εdist, ∆min` in memory cells `0, 1, 2`. -/
noncomputable def recoverInput (n : ℕ) (εwt εdist Δmin : ℝ) : State :=
  initState n [εwt, εdist, Δmin]

/-- The length `L` of the output list: pointer register `1` at halt, truncated at `0`. -/
def outLength (s : State) : ℕ := (s.core.ptrs 1).toNat

/-- The `j`-th output point `z_j ∈ ℝⁿ`: memory cells `j(n+1), …, j(n+1)+n−1`. -/
noncomputable def outPoint (n : ℕ) (s : State) (j : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i : Fin n => s.core.mem ((j * (n + 1) + i.1 : ℕ) : ℤ))

/-- The `j`-th output weight `ŵ_j`: memory cell `j(n+1)+n`. -/
def outWeight (n : ℕ) (s : State) (j : ℕ) : ℝ :=
  s.core.mem ((j * (n + 1) + n : ℕ) : ℤ)

/-- (RP), p.3: the list `(z_j, ŵ_j)_{j<L}` solves the recovery problem for the center
distribution `D`. -/
def IsRecoveryOutput {n : ℕ} (D : Measure (EuclideanSpace ℝ (Fin n))) (εwt εdist : ℝ) (L : ℕ)
    (z : ℕ → EuclideanSpace ℝ (Fin n)) (w : ℕ → ℝ) : Prop :=
  ∃ ρ : Fin L → EuclideanSpace ℝ (Fin n), Function.Injective ρ ∧
    (∀ j : Fin L, ρ j ∈ Supp D ∧ dist (z j) (ρ j) ≤ εdist ∧ |w j - (D {ρ j}).toReal| ≤ εwt) ∧
    (∀ μ ∈ Supp D, 2 * εwt ≤ (D {μ}).toReal → ∃ j : Fin L, ρ j = μ)

end GaussMixHH.Supplement


