-- Prove2me | Definitions.Def_NaculichRegge_ColorAlgebra
-- name    : NaculichRegge_ColorAlgebra
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T23:13:56.433713+00:00
-- url     : https://prove2.me/theorems/3ea75ad3-2304-4291-9589-3ad95d896a81
-- title:
--   Colour algebra of the Regge limit: $\mathbf T_t^2$, $\mathbf T_{s-u}^2$, $C_{00}$ and the Regge colour factors $C_{ik}$
-- statement:
--   Colour factors of the four-gluon amplitude in an $SU(N)$ gauge theory are expanded in the six-dimensional basis of single and double traces $c[1],\dots,c[6]$ (Naculich, eq. (2.1)); the components are polynomials in $N$. This file fixes:
--
--   * the colour operators $\mathbf T_t^2$ and $\mathbf T_{s-u}^2=\tfrac12(\mathbf T_s^2-\mathbf T_u^2)$ as the explicit $6\times6$ matrices of eq. (4.15), acting on column vectors;
--   * the tree-level $t$-channel colour factor $C_{00}=c[1]-c[3]$ (eqs. (3.5)–(3.6));
--   * the crossing operator exchanging external legs 2 and 3, which swaps $c[1]\leftrightarrow c[3]$ and $c[4]\leftrightarrow c[6]$ (eq. (3.7));
--   * the Regge colour factors (eqs. (1.1), (4.23))
--   $$C_{ii}=(\mathbf T_{s-u}^2)^iC_{00},\quad C_{i1}=[\mathbf T_t^2,\dots,[\mathbf T_t^2,[\mathbf T_t^2,\mathbf T_{s-u}^2]]\cdots]C_{00},\quad C_{i,i-1}=[\mathbf T_{s-u}^2,\dots,[\mathbf T_{s-u}^2,[\mathbf T_t^2,\mathbf T_{s-u}^2]]\cdots]C_{00},$$
--   each containing exactly $i$ operators;
--   * the admissible index pairs of eq. (4.25): $k=0$ for $i=0$, $k=1$ for $i=1$, $k\in\{1,2\}$ for $i=2$, $k\in\{1,i-1,i\}$ for $i\ge3$.
--
--   The number of colours $N$ is the polynomial variable, and coefficients are complex numbers.
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, pp. 3, 5, 8, 11–13, 16; eqs. (1.1), (2.1), (3.5)–(3.7), (4.15), (4.23), (4.25)

import Mathlib

/-!
# Colour algebra of the four-gluon amplitude in the Regge limit

Source: S. G. Naculich, *All-loop-orders relation between Regge limits of N = 4 SYM and
N = 8 supergravity four-point amplitudes*, arXiv:2012.00030v2, Sections 2–4.

We work in the six-dimensional trace basis `c[1], …, c[6]` of eq. (2.1); index `j : Fin 6`
stands for `c[j+1]`. A colour factor is a vector of six polynomials in the number of colours
`N`, which is the polynomial variable `X`. The colour operators `𝐓_t²` and `𝐓_{s-u}²` are the
matrices of eq. (4.15), acting on column vectors (to the right).
-/

namespace NaculichRegge

open Polynomial

/-- A colour factor: its six components in the trace basis `c[1], …, c[6]` of eq. (2.1),
each a polynomial in `N` (the variable `X`). -/
abbrev ColorVec := Fin 6 → ℂ[X]

/-- A linear colour operator on the trace basis, as a `6 × 6` matrix with entries
polynomial in `N`. -/
abbrev ColorOp := Matrix (Fin 6) (Fin 6) ℂ[X]

/-- The operator `𝐓_t²`, eq. (4.15). -/
noncomputable def Tt2 : ColorOp :=
  !![X, 0, 0, 0, 0, -1;
     0, 2 * X, 0, 1, 0, 1;
     0, 0, X, -1, 0, 0;
     0, 2, 0, 2 * X, 0, 0;
     -2, 0, -2, 0, 0, 0;
     0, 2, 0, 0, 0, 2 * X]

/-- The operator `𝐓_{s-u}² = ½(𝐓_s² − 𝐓_u²)`, eq. (4.15). -/
noncomputable def Tsu2 : ColorOp :=
  !![-(C (1 / 2) * X), 0, 0, 0, -1, -C (1 / 2);
     0, 0, 0, -C (1 / 2), 0, C (1 / 2);
     0, 0, C (1 / 2) * X, C (1 / 2), 1, 0;
     0, 1, 2, X, 0, 0;
     -1, 0, 1, 0, 0, 0;
     -2, -1, 0, 0, 0, -X]

/-- The tree-level `t`-channel colour factor `C₀₀ = t₁ − t₃ = c[1] − c[3]`, eqs. (3.5)–(3.6). -/
noncomputable def C00 : ColorVec := ![1, 0, -1, 0, 0, 0]

/-- Crossing symmetry: exchanging external legs 2 and 3 (`a₂ ↔ a₃`) permutes the trace
basis as `c[1] ↔ c[3]`, `c[4] ↔ c[6]`, fixing `c[2]` and `c[5]`, eq. (3.7). -/
noncomputable def crossing : ColorOp :=
  !![0, 0, 1, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 1, 0, 0]

/-- The commutator `[A, B] = A B − B A` of two colour operators. -/
noncomputable def comm (A B : ColorOp) : ColorOp := A * B - B * A

/-- The operator producing the Regge colour factor `C_{ik}` from `C₀₀`, eqs. (1.1), (4.23):
* `i = 0`: the identity (so `C₀₀ = C₀₀`);
* `k = i ≥ 1`: `(𝐓_{s-u}²)^i`;
* `k = 1`, `i ≥ 2`: `[𝐓_t², ⋯, [𝐓_t², [𝐓_t², 𝐓_{s-u}²]] ⋯]` with `i − 1` copies of `𝐓_t²`;
* `k = i − 1`, `i ≥ 3`: `[𝐓_{s-u}², ⋯, [𝐓_{s-u}², [𝐓_t², 𝐓_{s-u}²]] ⋯]` with `i − 2` outer
  copies of `𝐓_{s-u}²`.
All other index pairs (which do not occur in the Regge basis) are assigned `0`. -/
noncomputable def reggeOp (i k : ℕ) : ColorOp :=
  if i = 0 then 1
  else if k = i then Tsu2 ^ i
  else if k = 1 then (comm Tt2)^[i - 1] Tsu2
  else if k = i - 1 then (comm Tsu2)^[i - 2] (comm Tt2 Tsu2)
  else 0

/-- The Regge colour factor `C_{ik} = (operator) C₀₀`, eqs. (1.1), (4.8), (4.14), (4.19), (4.23). -/
noncomputable def reggeColor (i k : ℕ) : ColorVec := (reggeOp i k).mulVec C00

/-- The admissible index pairs `(i, k)` of the Regge basis, eq. (1.3)/(4.25):
`k = 0` if `i = 0`; `k = 1` if `i = 1`; `k ∈ {1, 2}` if `i = 2`; `k ∈ {1, i−1, i}` if `i ≥ 3`. -/
def IsReggeIndex (i k : ℕ) : Prop :=
  (i = 0 ∧ k = 0) ∨ (i = 1 ∧ k = 1) ∨ (i = 2 ∧ (k = 1 ∨ k = 2)) ∨
    (3 ≤ i ∧ (k = 1 ∨ k = i - 1 ∨ k = i))

instance (i k : ℕ) : Decidable (IsReggeIndex i k) := by
  unfold IsReggeIndex; infer_instance

/-- The index pairs `(i, k)` with `0 ≤ i ≤ ℓ` appearing in the `ℓ`-loop Regge basis, eq. (4.24). -/
def reggeIndex (ℓ : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (ℓ + 1) ×ˢ Finset.range (ℓ + 1)).filter (fun p => IsReggeIndex p.1 p.2)

end NaculichRegge


