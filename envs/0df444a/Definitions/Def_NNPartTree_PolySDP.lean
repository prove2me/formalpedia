-- Prove2me | Definitions.Def_NNPartTree_PolySDP
-- name    : NNPartTree_PolySDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:15.314126+00:00
-- url     : https://prove2.me/theorems/a071656a-0c3b-451d-bd3c-6204c89cbad6
-- title:
--   Monomials, the feature map $\phi_k$, and the semidefinite relaxation $\Pi_{\mathrm{sdp}}$
-- statement:
--   For $\alpha\in\mathbb Z_{\ge0}^d$ with $|\alpha|\le k$, $\phi_k(z)_\alpha=z^\alpha$; there are $N=\binom{d+k}{k}$ such exponents. A degree-$k$ polynomial is $x\mapsto w^\top\phi_k(x)$.
--
--   For a sample $S=((x_i,y_i))_{i\le m}$, put $V_i=\phi_k(x_i)-\phi_k(y_i)$, $Y_i=\phi_k(y_i)$ and $\bar Y=\frac1m\sum_iY_i$. A matrix $M\in\mathbb R^{N\times N}$ is **feasible** for $\Pi_{\mathrm{sdp}}(S,C)$ if
--
--   1. $\bar Y^\top M\bar Y=0$,
--   2. $\frac1m\sum_iY_i^\top MY_i=1$,
--   3. $\frac1m\sum_i(Y_i^\top MY_i)^2\le C$,
--   4. $M\succeq0$,
--
--   and its objective value is $\frac1m\sum_iV_i^\top MV_i$. This relaxes the program $\Pi$ over polynomials: a feasible polynomial with coefficient vector $w$ gives the feasible rank-one matrix $ww^\top$ with the same objective.
--
--   **Formalization Note** The page fixes no order on the monomials. Output layouts need one, so `monomials d k` lists exponent vectors lexicographically by first exponent. A program can enumerate this list.
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), p.18, including Definition 5.5

import Mathlib
import Definitions.Def_NNPartTree_Moments

open MeasureTheory
open scoped Matrix

namespace NNPartTree

/-!
# Monomials, the feature map `φ_k` and the semidefinite relaxation

S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*,
arXiv:2607.09909 (STOC 2027 submission), held copy of 2026-11-03, sha256 d32992f2…, p.18,
Definition 5.5.

**Formalization Note.**
* The page fixes no order on the `N = (d + k choose k)` monomials. Output layouts need one, so
  `monomials d k` lists the exponent vectors of degree at most `k` in lexicographic order of the first
  exponent, then the rest. A program can enumerate this list.
* The sample `S` is a function on `Fin m`; averages are `(1/m) Σ_i`. Every statement has `m ≥ 1`.
-/

variable {d : ℕ}

/-- The exponent vectors `α ∈ ℤ^d_{≥0}` with `|α| ≤ k` (p.18), in lexicographic order. -/
def monomials : (d k : ℕ) → List (Fin d → ℕ)
  | 0, _ => [Fin.elim0]
  | d + 1, k => (List.range (k + 1)).flatMap fun e => (monomials d (k - e)).map (Fin.cons e)

/-- `N`, the number of monomials of degree at most `k` in `d` variables. -/
def numMonomials (d k : ℕ) : ℕ := (monomials d k).length

/-- The embedding `φ_k(z)_α = z^α` (p.18). -/
noncomputable def phi (k : ℕ) (z : Pt d) : Fin (numMonomials d k) → ℝ :=
  fun a => ∏ i, z i ^ ((monomials d k).get a i)

/-- The degree-`k` polynomial function `x ↦ w^⊤ φ_k(x)` with coefficient vector `w` (p.18). -/
noncomputable def evalCoef {k : ℕ} (w : Fin (numMonomials d k) → ℝ) (x : Pt d) : ℝ :=
  w ⬝ᵥ phi k x

/-- The vector `V_i = φ_k(x_i) − φ_k(y_i)` (Definition 5.5, p.18). -/
noncomputable def sdpV (k : ℕ) {m : ℕ} (S : Fin m → Pt d × Pt d) (i : Fin m) :
    Fin (numMonomials d k) → ℝ :=
  phi k (S i).1 - phi k (S i).2

/-- The vector `Y_i = φ_k(y_i)` (Definition 5.5, p.18). -/
noncomputable def sdpY (k : ℕ) {m : ℕ} (S : Fin m → Pt d × Pt d) (i : Fin m) :
    Fin (numMonomials d k) → ℝ :=
  phi k (S i).2

/-- The vector `Ȳ = (1/m) Σ_i Y_i` (Definition 5.5, p.18). -/
noncomputable def sdpYbar (k : ℕ) {m : ℕ} (S : Fin m → Pt d × Pt d) :
    Fin (numMonomials d k) → ℝ :=
  (m : ℝ)⁻¹ • ∑ i, sdpY k S i

/-- The objective `(1/m) Σ_i V_i^⊺ M V_i` of `Π_sdp` (Definition 5.5, p.18). -/
noncomputable def sdpObjective {k m : ℕ} (S : Fin m → Pt d × Pt d)
    (M : Matrix (Fin (numMonomials d k)) (Fin (numMonomials d k)) ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i, sdpV k S i ⬝ᵥ M *ᵥ sdpV k S i

/-- `M` is feasible for `Π_sdp(S, C)` (Definition 5.5, p.18): (i) `Ȳ^⊺ M Ȳ = 0`,
(ii) `(1/m) Σ_i Y_i^⊺ M Y_i = 1`, (iii) `(1/m) Σ_i (Y_i^⊺ M Y_i)² ≤ C`, (iv) `M ⪰ 0`. -/
def SdpFeasible {k m : ℕ} (S : Fin m → Pt d × Pt d) (C : ℝ)
    (M : Matrix (Fin (numMonomials d k)) (Fin (numMonomials d k)) ℝ) : Prop :=
  sdpYbar k S ⬝ᵥ M *ᵥ sdpYbar k S = 0 ∧
    (m : ℝ)⁻¹ * ∑ i, sdpY k S i ⬝ᵥ M *ᵥ sdpY k S i = 1 ∧
    (m : ℝ)⁻¹ * ∑ i, (sdpY k S i ⬝ᵥ M *ᵥ sdpY k S i) ^ 2 ≤ C ∧
    M.PosSemidef

end NNPartTree


