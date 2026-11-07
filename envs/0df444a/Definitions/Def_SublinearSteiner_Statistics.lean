-- Prove2me | Definitions.Def_SublinearSteiner_Statistics
-- name    : SublinearSteiner_Statistics
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:44:15.553026+00:00
-- url     : https://prove2.me/theorems/6d82729b-04a1-4590-96a0-4d96d5ef6bea
-- title:
--   The ideal statistics $\Gamma,\Lambda$; covers; the band score $D_i(C)$; the deletion classes $\mathcal C_0$, $U$
-- statement:
--   **Ideal statistics.** For $C\in\mathrm{comp}(G_{a_i}(T))$, where $a_i=a_*\omega^{i+u}$,
--   $$A_i(C)=\max_{Y\subseteq C,\ 2\le|Y|\le4}\bigl(B_T(Y)-c(Y)\bigr)_+,\qquad \Gamma=\sum_ia_iY_i,\qquad \Lambda=\sum_ia_i\bigl|\{C:A_i(C)\ge\sigma_0a_i\}\bigr|.$$
--
--   **Covers and bands.** $N\subseteq T$ is a $\rho$-cover of $T$ if every terminal is within distance $\rho$ of $N$. For a point set $C$ and $Y\subseteq C$, $B_C(Y)$ is the integral over $t\in[\tau a,a-2\rho]$ of the number of components of $G_t(C)$ meeting $Y$, minus one, and the band score is
--   $$D_i(C)=\max\Bigl\{0,\max_{Y\subseteq C,\ 2\le|Y|\le4}\bigl[B_C(Y)-c(Y)-6\rho\bigr]\Bigr\}.$$
--   $T_Q$ is the sum of $D_i(C)$ over all scales and over components with at most $B_Q$ points.
--
--   **Deletion.** Given selected centers $S$, $D$ is the union of the balls $A_v=\{x\in T:w(v,x)\le5a/8\}$, $v\in S$. Among the components of $G_a(N)$, $\mathcal C_0$ are those with at most $B$ points that meet $D$, $U$ the other ones with at most $B$ points, and $b_{\mathrm{large}}$ counts those with more than $B$ points.
--
--   **Formalization Note.** A maximum over no admissible $Y$ (a singleton $C$) is $0$. $\Gamma$ and $\Lambda$ are finite sums over an explicit index set. The integrand of $B_C(Y)$ is a bounded step function with finitely many jumps, so the integral is genuine.
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Section 3, (3.1), p.15; Section 4.1, (4.4), p.20; p.24

import Mathlib
import Definitions.Def_SublinearSteiner_Constants
import Definitions.Def_SublinearSteiner_Saving

open scoped Classical NNReal

namespace SublinearSteiner

/-!
# The ideal statistics `Γ, Λ` and the cover statistics

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), Section 3, (3.1), p.15; Section 4.1, (4.4), p.20; Section 4.3, p.24;
Section 4.4, p.24.

**Formalization Note.**
* `Ai(C) = max_{Y ⊆ C, 2 ≤ |Y| ≤ 4} (B_T(Y) − c(Y))₊` and `Di(C) = max{0, max_Y [B_C(Y) − c(Y) − 6ρ]}` are written as a
  supremum in `ℝ≥0`, which is `0` when no admissible `Y` exists (a singleton `C`).
* `Γ` and `Λ` are finite sums over an explicit index set `J` with an arbitrary scale function.
* `B_C(Y)` is an integral over `t ∈ [τa, a − 2ρ]` of a step function with finitely many jumps (`G_t(C)` changes only at
  distances of `C`), bounded by `|C|`, so it is integrable. It uses `G_t(C)` of the point set `C` itself, not of `T`.
-/

variable {n : ℕ}

/-- The sets `Y ⊆ C` with `2 ≤ |Y| ≤ 4`. -/
noncomputable def smallSubsets (C : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  C.powerset.filter fun Y => 2 ≤ Y.card ∧ Y.card ≤ 4

/-- `Ai(C) = max_{Y ⊆ C, 2 ≤ |Y| ≤ 4} (B_T(Y) − c(Y))₊` (p.15). -/
noncomputable def idealScore (w : FinMetric n) (T C : Finset (Fin n)) : ℝ :=
  (((smallSubsets C).sup fun Y => Real.toNNReal (benefit w T Y - pointCost w Y) : ℝ≥0) : ℝ)

/-- `a_i = a∗ ω^{i+u}`, `i ∈ ℤ` (p.15). -/
noncomputable def idealScale (aStar u : ℝ) (i : ℤ) : ℝ := aStar * omega ^ ((i : ℝ) + u)

/-- `Γ = Σ_{i ∈ J} a_i Y_i` (3.1). -/
noncomputable def Gamma {ι : Type*} (w : FinMetric n) (T : Finset (Fin n)) (a : ι → ℝ) (J : Finset ι) : ℝ :=
  ∑ i ∈ J, a i * (idealSaving w T (a i) : ℝ)

/-- `Λ = Σ_{i ∈ J} a_i |{C ∈ Q_i : Ai(C) ≥ σ0 a_i}|` (3.1). -/
noncomputable def Lambda {ι : Type*} (w : FinMetric n) (T : Finset (Fin n)) (a : ι → ℝ) (J : Finset ι) : ℝ :=
  ∑ i ∈ J, a i * (((comp w T (a i)).filter fun C => sigma0 * a i ≤ idealScore w T C).card : ℝ)

/-- `N ⊆ T` is a `ρ`-cover of `T`: every terminal is within distance `ρ` of `N` (p.20). -/
def IsCover (w : FinMetric n) (T N : Finset (Fin n)) (ρ : ℝ) : Prop :=
  N ⊆ T ∧ ∀ x ∈ T, ∃ y ∈ N, w.d x y ≤ ρ

/-- `B_C(Y)`: the integral over `t ∈ [τa, a − 2ρ]` of the number of components of `G_t(C)` meeting `Y`, minus one
(p.20). -/
noncomputable def bandBenefit (w : FinMetric n) (C : Finset (Fin n)) (a ρ : ℝ) (Y : Finset (Fin n)) : ℝ :=
  ∫ t in (tau * a)..(a - 2 * ρ), (((comp w C t).filter fun D => (D ∩ Y).Nonempty).card : ℝ) - 1

/-- The band score `Di(C) = max{0, max_{Y ⊆ C, 2 ≤ |Y| ≤ 4} [B_C(Y) − c(Y) − 6ρ]}` (4.4). -/
noncomputable def bandScore (w : FinMetric n) (C : Finset (Fin n)) (a ρ : ℝ) : ℝ :=
  (((smallSubsets C).sup fun Y =>
      Real.toNNReal (bandBenefit w C a ρ Y - pointCost w Y - 6 * ρ) : ℝ≥0) : ℝ)

/-- `T_Q = Σ_i Σ_{C ∈ C_i, |C| ≤ B_Q} Di(C)` over the first `I` scales, with `ρ_i = δ a_i` (p.24). -/
noncomputable def boundedBandSum (w : FinMetric n) (N : ℕ → Finset (Fin n)) (a : ℕ → ℝ) (I BQ : ℕ) : ℝ :=
  ∑ i ∈ Finset.range I, ∑ C ∈ (comp w (N i) (a i)).filter (fun C => C.card ≤ BQ),
    bandScore w C (a i) (delta * a i)

/-- The ball `A_v = {x ∈ T : w(v, x) ≤ 5a/8}` (p.24). -/
noncomputable def ballA (w : FinMetric n) (T : Finset (Fin n)) (a : ℝ) (v : Fin n) : Finset (Fin n) :=
  T.filter fun x => w.d v x ≤ 5 * a / 8

/-- `D`, the union of the balls `A_v` of the selected centers `S` (p.24). -/
noncomputable def deletedSet (w : FinMetric n) (T S : Finset (Fin n)) (a : ℝ) : Finset (Fin n) :=
  S.biUnion (ballA w T a)

/-- `C_0`: the components of `G_a(N)` with at most `B` points that meet `D` (p.24). -/
noncomputable def hitComps (w : FinMetric n) (T N S : Finset (Fin n)) (a : ℝ) (B : ℕ) :
    Finset (Finset (Fin n)) :=
  (comp w N a).filter fun C => C.card ≤ B ∧ (C ∩ deletedSet w T S a).Nonempty

/-- `U`: the other components of `G_a(N)` with at most `B` points (p.24). -/
noncomputable def restComps (w : FinMetric n) (T N S : Finset (Fin n)) (a : ℝ) (B : ℕ) :
    Finset (Finset (Fin n)) :=
  (comp w N a).filter fun C => C.card ≤ B ∧ ¬ (C ∩ deletedSet w T S a).Nonempty

/-- `b_large`: the number of components of `G_a(N)` with more than `B` points (p.24). -/
noncomputable def largeCount (w : FinMetric n) (N : Finset (Fin n)) (a : ℝ) (B : ℕ) : ℕ :=
  ((comp w N a).filter fun C => B < C.card).card

end SublinearSteiner


