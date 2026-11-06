-- Prove2me | Definitions.Def_FeedbackSwitching_centering
-- name    : FeedbackSwitching_centering
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:17.980041+00:00
-- url     : https://prove2.me/theorems/9651a9ac-e6e8-4478-a8e8-1b2e2844296b
-- title:
--   Probability vectors, weighted inner products, the centering matrix $C_v$ and $\mathrm{Var}_v$
-- statement:
--   Notation of §3.1 and §3.4.
--
--   1. A **probability vector** has nonnegative entries summing to one; a **positive** one has positive entries.
--   2. For a vector $v$, $\langle f,g\rangle_v=\sum_i v_if_ig_i$ and $\|f\|_v^2=\langle f,f\rangle_v$.
--   3. The **centering matrix** is $C_v=I-\mathbf 1v^{\mathsf T}$, so $C_vf=f-(v^{\mathsf T}f)\mathbf 1$, and $\mathrm{Var}_v(f)=\|C_vf\|_v^2$.
--   4. A **transition matrix** $P$ has nonnegative entries and unit row sums; $P_{ij}=P(j\mid i)$.
--   5. $P$ is **reversible** with respect to $p$ if $p_iP_{ij}=p_jP_{ji}$ for all $i,j$.
--   6. A loss vector lies in $[0,1]^K$.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), §3.1, p.13; §3.4, pp.16–17 (PDF pp.15, 18–19)

import Mathlib
open Matrix

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

A probability vector on `[K]` (p.13). -/
def IsProbVec {K : ℕ} (v : Fin K → ℝ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1

/-- A positive probability vector. -/
def IsPosProbVec {K : ℕ} (v : Fin K → ℝ) : Prop :=
  (∀ i, 0 < v i) ∧ ∑ i, v i = 1

/-- A loss vector in `[0,1]^K`. -/
def InUnitCube {K : ℕ} (ℓ : Fin K → ℝ) : Prop :=
  ∀ i, 0 ≤ ℓ i ∧ ℓ i ≤ 1

/-- Weighted inner product `⟨f, g⟩_v = ∑_i v_i f_i g_i` (p.13). -/
def wInner {K : ℕ} (v f g : Fin K → ℝ) : ℝ :=
  ∑ i, v i * f i * g i

/-- Weighted squared norm `‖f‖²_v = ⟨f, f⟩_v` (p.13). -/
def wNormSq {K : ℕ} (v f : Fin K → ℝ) : ℝ :=
  wInner v f f

/-- **Centering matrix** `C_v = I − 1 vᵀ`, so `C_v f = f − (vᵀf) 1` (p.13 = PDF p.15). -/
def centering {K : ℕ} (v : Fin K → ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  1 - Matrix.of (fun _ j => v j)

/-- Weighted variance `Var_v(f) = ‖C_v f‖²_v` (p.13). -/
def wVar {K : ℕ} (v f : Fin K → ℝ) : ℝ :=
  wNormSq v (centering v *ᵥ f)

/-- A transition matrix: nonnegative entries, rows summing to one; `P i j = P(j | i)` (p.16). -/
def IsTransitionMatrix {K : ℕ} (P : Matrix (Fin K) (Fin K) ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- `P` is reversible with respect to `p`: detailed balance `p_i P_ij = p_j P_ji` (p.17). -/
def IsReversible {K : ℕ} (P : Matrix (Fin K) (Fin K) ℝ) (p : Fin K → ℝ) : Prop :=
  ∀ i j, p i * P i j = p j * P j i

end FeedbackSwitching


