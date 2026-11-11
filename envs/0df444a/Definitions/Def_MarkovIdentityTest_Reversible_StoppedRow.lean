-- Prove2me | Definitions.Def_MarkovIdentityTest_Reversible_StoppedRow
-- name    : MarkovIdentityTest_Reversible_StoppedRow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:38:21.798182+00:00
-- url     : https://prove2.me/theorems/60e444a2-8c87-41ad-bd5b-af4db8384f40
-- title:
--   The stopped-row law (5.1) — abstract and for a chain — the retained-row score $W$, $\mathrm{Lin}$, the scores $Z_t$ and $\mathrm{Fluc}_t$ and the enlarged alphabet
-- statement:
--   **Abstract stopped row.** A reached row has a return probability $s\in[0,1)$, a returning law $r$, a final law $e$ and row law $q=sr+(1-s)e$. Its outcome is the retained length $L=l\ge0$ and $l+1$ destinations $y_0,\dots,y_{l-1}$ (retained) and $y_l$ (the deleted final one), with probability $(1-s)s^l\prod_{a<l}r_{y_a}\,e_{y_l}$ — the law (5.1). The conditional expectation of $g$ given that the row is reached is the series of $g$ against these weights; integrability is absolute convergence.
--
--   - **Feature covariance** $\Sigma_q=\sum_yq_y\phi(y)\phi(y)^\top$ for a centred feature $\phi$ with values in $\mathbb R^D$.
--   - **Retained-row score** $W=\frac1L\sum_{a\ne b\le L}\langle\phi(Y_a),\phi(Y_b)\rangle$ on the retained destinations, $W=0$ when $L=0$ (§5.2.1).
--   - $\mathrm{Lin}_l=\sum_{b\le l}\bar\kappa_{Y_b}$ with $\bar\kappa=\kappa-\mathbb E_q\kappa$ (§5.3).
--
--   **Stopped rows of a chain** $Q$ at the geometric time of mean $M$ (§5.1):
--   - $h_y$: after a transition $i\to y$, the probability of returning to $i$ and departing from $i$ again before the deadline. By memorylessness the number of transitions still observed is $T'-1$ with $T'$ a fresh positive geometric time, so $h_y$ is the probability that the chain started at $y$ is at $i$ at some time $u<T'-1$.
--   - $s=\sum_yQ_{iy}h_y$, $r_y=Q_{iy}h_y/s$, $e_y=Q_{iy}(1-h_y)/(1-s)$.
--   - $W_i$: the retained-row score of row $i$ on a path, for a feature of the destination.
--   - The retained quadratic score $\sum_{i:L_i\ge1}U_{b_i}(Q_i;D_i)/L_i$ of (5.2).
--   - A prefix is **supported** when every observed transition has $P_{ij}>0$. The **observable score** is
--   $$Z_t=\sum_{i:L_i\ge1}\Big[\frac1{L_i}\sum_{j:P_{ij}>0}\frac{D_{ij}(D_{ij}-1)}{P_{ij}}-(L_i-1)\Big].$$
--   - **Enlarged alphabet** (§5.4): the supported destinations of row $P_i$ plus one extra outcome that aggregates the unsupported ones; its reference probability is $0$, its $Q$-probability is $\sum_{j:P_{ij}=0}Q_{ij}$, its weight is $M$, and its count is the number of retained unsupported transitions. Supported destinations have weight $1/P_{ij}$. The **fluctuation** is
--   $$\mathrm{Fluc}_t=\sum_{i:L_i\ge1}\frac{U_{v_i}(q_i;D_i)}{L_i},$$
--   with $q_i$ the enlarged row of $Q$ and $v_i$ the capped weights.
--
--   **Formalization Note.** The enlarged alphabet is `Option (Fin n)`; an unsupported `some j` carries weight, mass and count $0$ and contributes nothing. Divisions by $s=0$ or $L=0$ return $0$ in Lean; they occur only where the paper's formula is multiplied by $s^l=0$ or excluded by $L_i\ge1$.
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), pp. 24–25 §5.1–5.2.1 (Eq. (5.1), W), p. 27 (features), p. 28 §5.3 (Lin), pp. 29–30 §5.4 (Z_t, enlarged alphabet, Fluc_t)

import Mathlib
import Definitions.Def_MarkovIdentityTest_Reversible_Discrepancy
import Definitions.Def_MarkovIdentityTest_Reversible_Trajectory
import Definitions.Def_MarkovIdentityTest_Reversible_RowStatistics

set_option autoImplicit false

open Finset

namespace MarkovIdentityTest.Reversible

/-! ### The abstract stopped row (§5.1, law (5.1))

A reached row is described by its retained length `L = l ≥ 0` and its `l + 1` destinations
`y 0, …, y (l-1)` (retained) and `y (last l)` (the deleted final one). Under the law (5.1) this
outcome has probability `(1 - s) s^l ∏_{a<l} r(y a) · e(y last)`. -/

/-- The mixture `q = s r + (1 - s) e` (§5.1, p. 24 / PDF 26). -/
def rowMixture {α : Type*} (s : ℝ) (r e : α → ℝ) (y : α) : ℝ :=
  s * r y + (1 - s) * e y

/-- Probability of the reached-row outcome `(l, y)` under the law (5.1). -/
noncomputable def stoppedRowWeight {α : Type*} (s : ℝ) (r e : α → ℝ) (l : ℕ)
    (y : Fin (l + 1) → α) : ℝ :=
  (1 - s) * s ^ l * (∏ a : Fin l, r (y a.castSucc)) * e (y (Fin.last l))

/-- Conditional expectation, given that the row is reached, of `g(L, Y₁, …, Y_N)`. -/
noncomputable def stoppedRowExp {α : Type*} [Fintype α] (s : ℝ) (r e : α → ℝ)
    (g : (l : ℕ) → (Fin (l + 1) → α) → ℝ) : ℝ :=
  ∑' l, ∑ y, stoppedRowWeight s r e l y * g l y

/-- `g` has finite conditional expectation under the law (5.1). -/
def StoppedRowIntegrable {α : Type*} [Fintype α] (s : ℝ) (r e : α → ℝ)
    (g : (l : ℕ) → (Fin (l + 1) → α) → ℝ) : Prop :=
  Summable fun l => ∑ y, stoppedRowWeight s r e l y * |g l y|

/-- The feature second-moment (= covariance, the feature being centred) matrix
`Σ_q = ∑_y q_y ϕ(y) ϕ(y)ᵀ` (§5.2.1, p. 25 / PDF 27). -/
noncomputable def featureCov {α : Type*} [Fintype α] {D : ℕ} (q : α → ℝ)
    (ϕ : α → Fin D → ℝ) : Matrix (Fin D) (Fin D) ℝ :=
  ∑ y, q y • Matrix.vecMulVec (ϕ y) (ϕ y)

/-- The pair score of `l` destinations: `(1/l) ∑_{a ≠ b} ⟨ϕ(y a), ϕ(y b)⟩`, and `0` when `l = 0`. -/
noncomputable def pairScore {α : Type*} {D : ℕ} (ϕ : α → Fin D → ℝ) (l : ℕ) (y : Fin l → α) : ℝ :=
  if l = 0 then 0 else
    (1 / (l : ℝ)) * ∑ a : Fin l, ∑ b : Fin l, if a = b then 0 else ϕ (y a) ⬝ᵥ ϕ (y b)

/-- The retained-row score `W` (§5.2.1, p. 25 / PDF 27) of a reached-row outcome: the pair score
of the `L = l` retained destinations (the final destination is deleted). -/
noncomputable def retainedScore {α : Type*} {D : ℕ} (ϕ : α → Fin D → ℝ) (l : ℕ)
    (y : Fin (l + 1) → α) : ℝ :=
  pairScore ϕ l fun a => y a.castSucc

/-- `Lin_l = ∑_{b ≤ l} κ̄(Y_b)` with `κ̄ = κ - E_q κ` (§5.3, p. 28 / PDF 30), over the retained
destinations of a reached-row outcome. -/
noncomputable def linCorrection {α : Type*} [Fintype α] (q κ : α → ℝ) (l : ℕ)
    (y : Fin (l + 1) → α) : ℝ :=
  ∑ b : Fin l, (κ (y b.castSucc) - ∑ z, q z * κ z)

/-! ### The stopped rows of a chain at a geometric time -/

/-- `h_y` (§5.1): after a transition `i → y`, the probability that the trajectory returns to `i`
and departs from `i` again before the geometric deadline. By memorylessness the number of
transitions still observed after that transition is `T' - 1` with `T'` a fresh positive
geometric time of mean `M`, so `h_y` is the probability that the chain started at `y` visits
`i` at some time `u` with `u < T' - 1`. -/
noncomputable def returnProb {n : ℕ} (M : ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (i y : Fin n) : ℝ :=
  geomProb M Q y fun t ω => ∃ u : Fin (t + 1), (u : ℕ) + 1 < t ∧ ω u = i

/-- `s = ∑_y q_y h_y` with `q = Qᵢ` (§5.1). -/
noncomputable def returnMass {n : ℕ} (M : ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  ∑ y, Q i y * returnProb M Q i y

/-- The returning law `r_y = q_y h_y / s` (§5.1). -/
noncomputable def returnLaw {n : ℕ} (M : ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (i y : Fin n) : ℝ :=
  Q i y * returnProb M Q i y / returnMass M Q i

/-- The final law `e_y = q_y (1 - h_y) / (1 - s)` (§5.1). -/
noncomputable def finalLaw {n : ℕ} (M : ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (i y : Fin n) : ℝ :=
  Q i y * (1 - returnProb M Q i y) / (1 - returnMass M Q i)

/-- The retained-row score `Wᵢ` of row `i` on a path, for a feature `ϕ` of the destination:
`(1/Lᵢ) ∑_{a ≠ b} ⟨ϕ(Y_a), ϕ(Y_b)⟩` over the retained departures from `i` (zero if `Lᵢ = 0`). -/
noncomputable def chainRowScore {n t D : ℕ} (ϕ : Fin n → Fin D → ℝ) (i : Fin n)
    (ω : Fin (t + 1) → Fin n) : ℝ :=
  (1 / (retainedLength ω i : ℝ)) *
    ∑ s ∈ retainedTimes ω i, ∑ s' ∈ retainedTimes ω i,
      if s = s' then 0 else ϕ (ω s.succ) ⬝ᵥ ϕ (ω s'.succ)

/-- The retained quadratic row scores `∑_{i : Lᵢ ≥ 1} U_{bᵢ}(qᵢ; Dᵢ)/Lᵢ` of (5.2), with
`qᵢ = Qᵢ`. -/
noncomputable def retainedQuadScore {n t : ℕ} (b Q : Matrix (Fin n) (Fin n) ℝ)
    (ω : Fin (t + 1) → Fin n) : ℝ :=
  ∑ i ∈ univ.filter (fun i => 1 ≤ retainedLength ω i),
    pairStat (b i) (Q i) (retainedCount ω i) / (retainedLength ω i : ℝ)

/-- Every observed transition lies in the support of `P`. -/
def SupportedPrefix {n t : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (ω : Fin (t + 1) → Fin n) : Prop :=
  ∀ s : Fin t, 0 < P (ω s.castSucc) (ω s.succ)

/-- The observable transition score `Z_t` (§5.4, p. 29 / PDF 31):
`∑_{i : Lᵢ ≥ 1} [ (1/Lᵢ) ∑_{j : Pᵢⱼ > 0} Dᵢⱼ(Dᵢⱼ - 1)/Pᵢⱼ - (Lᵢ - 1) ]`. -/
noncomputable def observableScore {n t : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (ω : Fin (t + 1) → Fin n) : ℝ :=
  ∑ i ∈ univ.filter (fun i => 1 ≤ retainedLength ω i),
    ((1 / (retainedLength ω i : ℝ)) *
        ∑ j ∈ univ.filter (fun j => 0 < P i j),
          (retainedCount ω i j : ℝ) * ((retainedCount ω i j : ℝ) - 1) / P i j
      - ((retainedLength ω i : ℝ) - 1))

/-! ### The enlarged alphabet of §5.4: supported destinations `some j` (with `Pᵢⱼ > 0`) plus one
extra outcome `none` aggregating the unsupported destinations, whose reference probability is
`0`. An unsupported `some j` carries true mass, weight and count `0`, so it contributes nothing. -/

/-- True probabilities on the enlarged alphabet: `Qᵢⱼ` on supported `some j`, the unsupported
mass `∑_{j : Pᵢⱼ = 0} Qᵢⱼ` on the extra outcome. -/
noncomputable def enlargedTrue {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Option (Fin n) → ℝ
  | none => ∑ j ∈ univ.filter (fun j => P i j = 0), Q i j
  | some j => if 0 < P i j then Q i j else 0

/-- Weights on the enlarged alphabet: `1/Pᵢⱼ` on supported destinations, `M` on the extra
outcome. -/
noncomputable def enlargedWeight {n : ℕ} (M : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Option (Fin n) → ℝ
  | none => M
  | some j => if 0 < P i j then 1 / P i j else 0

/-- Retained counts on the enlarged alphabet. -/
noncomputable def enlargedCount {n t : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (ω : Fin (t + 1) → Fin n) (i : Fin n) :
    Option (Fin n) → ℕ
  | none => ∑ j ∈ univ.filter (fun j => P i j = 0), retainedCount ω i j
  | some j => if 0 < P i j then retainedCount ω i j else 0

/-- The signed fluctuation `Fluc_t = ∑_{i : Lᵢ(t) ≥ 1} U_{vᵢ}(qᵢ; Dᵢ(t))/Lᵢ(t)` of Lemma 5.5
(pp. 29–30 / PDF 31–32): the retained quadratic score on the enlarged alphabet, centred at the
true row `qᵢ` of `Q` and using the capped weights `vᵢ = min {wᵢ, 3/qᵢ}`. -/
noncomputable def fluctuation {n t : ℕ} (M : ℝ) (P Q : Matrix (Fin n) (Fin n) ℝ)
    (ω : Fin (t + 1) → Fin n) : ℝ :=
  ∑ i ∈ univ.filter (fun i => 1 ≤ retainedLength ω i),
    pairStat (cappedWeight (enlargedWeight M P i) (enlargedTrue P Q i)) (enlargedTrue P Q i)
      (enlargedCount P ω i) / (retainedLength ω i : ℝ)

end MarkovIdentityTest.Reversible


