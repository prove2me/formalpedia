-- Prove2me | Definitions.Def_FermiGaussMix_IsLocalModel
-- name    : FermiGaussMix_IsLocalModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:29.101518+00:00
-- url     : https://prove2.me/theorems/13245682-3b41-4715-a83b-2732c1796a36
-- title:
--   The local model (A.5)–(A.6), the constants $C_H$, $C_V$, $I_\beta$ and the threshold $g\le g_{\mathrm{mix}}$
-- statement:
--   A local model consists of supports $B_1,\dots,B_m\subseteq[2n]$, quadratic operators $H_{0,j}$ and even operators $V_j$ such that
--
--   1. each $B_j$ has at most $d$ labels, and each label lies in at most $q_B$ of the $B_j$;
--   2. $H_{0,j}$ is quadratic and supported in $B_j$, with operator norm $\|H_{0,j}\|\le 1$;
--   3. $V_j$ is even and supported in $B_j$, with operator norm $\|V_j\|\le g$, where $g\ge 0$.
--
--   The constants are
--   $$
--   C_H=2q_B(d-1),\qquad C_V=q_B2^d,\qquad I_\beta=\int_0^{\beta/2}e^{dC_Hu}\,du,
--   $$
--   $$
--   \eta_{\mathrm{mix}}=\min\Bigl\{\frac1d,\frac12\log\frac{13}{12}\Bigr\},\qquad g_{\mathrm{mix}}=\frac{\eta_{\mathrm{mix}}}{2^dC_VI_\beta}.
--   $$
--   None of these depends on the number of modes $n$.
--
--   **Formalization Note** The lattice $\Lambda\subset\mathbb Z^D$ of the paper enters only through $d$ and $q_B$, so the family of supports is abstract. The condition $g\le g_{\mathrm{mix}}$ is written in product form, $d\eta\le 1$ and $\eta\le\frac12\log\frac{13}{12}$ with $\eta=2^dC_VI_\beta g$, which agrees with the quotient for $d,q_B\ge 1$ and avoids the Lean convention $1/0=0$ otherwise. In $C_H$ the expression $d-1$ is truncated at $0$; the printed formula is negative at $d=0$, where every support is empty.
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, eqs. (A.5)–(A.6), (A.9)–(A.12), pp. 9–10

import Mathlib
import Definitions.Def_FermiGaussMix_P

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- The constant `C_H = 2 q_B (d - 1)` of eq. (A.9), p.9 (Han, Zhao, Liu, arXiv:2609.35159v1).

**Formalization Note** `d - 1` is natural-number subtraction, so `C_H = 0` at `d = 0`. The printed formula is
negative there, and (A.9) would fail for a model with empty supports. For `d ≥ 1` the two agree, and `d * C_H`,
the only form in which `C_H` enters the threshold, is `0` at `d = 0` either way. -/
noncomputable def CH (qB d : ℕ) : ℝ := 2 * (qB : ℝ) * ((d - 1 : ℕ) : ℝ)

/-- The constant `C_V = q_B 2^d` of eq. (A.10), p.10 (Han, Zhao, Liu, arXiv:2609.35159v1). -/
noncomputable def CV (qB d : ℕ) : ℝ := (qB : ℝ) * 2 ^ d

/-- `I_β = ∫_0^{β/2} e^{d C_H u} du`, eq. (A.11), p.10 (Han, Zhao, Liu, arXiv:2609.35159v1). -/
noncomputable def Ibeta (qB d : ℕ) (β : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(β / 2), Real.exp ((d : ℝ) * CH qB d * u)

/-- The condition `g ≤ g_mix` of eq. (A.12), p.10, with `η_mix = min{1/d, ½ log(13/12)}` and
`g_mix = η_mix / (2^d C_V I_β)` (Han, Zhao, Liu, arXiv:2609.35159v1).

**Formalization Note** Written in product form with `η := 2^d C_V I_β g`: `d η ≤ 1` and `η ≤ ½ log(13/12)`. For
`d, q_B ≥ 1` and `β > 0` this is exactly `g ≤ g_mix`. For `d = 0` or `q_B = 0` the printed formula divides by
zero; the product form reads `1/0` as `+∞`, while a Lean quotient would read it as `0` and shrink the theorem. -/
def BelowThreshold (d qB : ℕ) (β g : ℝ) : Prop :=
  (d : ℝ) * ((2 : ℝ) ^ d * CV qB d * Ibeta qB d β * g) ≤ 1 ∧
    (2 : ℝ) ^ d * CV qB d * Ibeta qB d β * g ≤ (1 / 2) * Real.log (13 / 12)

/-- The local decompositions (A.5)–(A.6), p.9 (Han, Zhao, Liu, arXiv:2609.35159v1), of `H₀ = Σ_j H_{0,j}` and
`V = Σ_j V_j` over a finite family of supports `B_j ⊆ [2n]`: each `B_j` has at most `d` Majorana labels, each
label lies in at most `q_B` supports, `H_{0,j}` is quadratic and supported in `B_j` with `‖H_{0,j}‖ ≤ 1`, `V_j`
is even and supported in `B_j` with `‖V_j‖ ≤ g`, and `g ≥ 0`.

**Formalization Note** Norms are operator norms (`Matrix.Norms.L2Operator`). The lattice `Λ ⊂ ℤ^D`, the radius
`r₀` and the mode bound `ν` enter Theorem A.1 only through `d` and `q_B`, so the family is abstract. A lattice
family is one such family, since a label sits at one site and a site lies in at most `q_B` sets. -/
def IsLocalModel {n m : ℕ} (d qB : ℕ) (g : ℝ) (B : Fin m → Finset (Fin (2 * n)))
    (H0 V : Fin m → Op n) : Prop :=
  (∀ j, (B j).card ≤ d) ∧
  (∀ a : Fin (2 * n), (Finset.univ.filter (fun j => a ∈ B j)).card ≤ qB) ∧
  (∀ j, H0 j ∈ quadraticSpan (B j) ∧ ‖H0 j‖ ≤ 1) ∧
  (∀ j, V j ∈ evenSpan (B j) ∧ ‖V j‖ ≤ g) ∧
  0 ≤ g

end FermiGaussMix


