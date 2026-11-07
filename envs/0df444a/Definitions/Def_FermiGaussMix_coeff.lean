-- Prove2me | Definitions.Def_FermiGaussMix_coeff
-- name    : FermiGaussMix_coeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:32.913273+00:00
-- url     : https://prove2.me/theorems/0aec1260-36c8-466f-ac60-c9fbdef241d4
-- title:
--   Majorana coefficients and the weighted sums $L_q$, $J_q$; the matrix $K_0$
-- statement:
--   For an operator $O$ on $n$ modes and an even set $R$, the coefficient of $P_R$ in $O$ is
--   $$
--   o_R=2^{-n}\operatorname{Tr}(P_RO).
--   $$
--   For $q\ge 1$ the weighted sums of an operator $Y=\sum_Ry_RP_R$ are
--   $$
--   L_q(Y)=\sum_R|y_R|\,q^{|R|},\qquad J_q(Y)=\max_a\sum_{R\ni a}|y_R|\,q^{|R|}.
--   $$
--   An operator has degree at most $k$ when $y_R=0$ for every even $R$ with $|R|>k$. The antisymmetric matrix $K_0$ of a quadratic operator $H_0=\frac14\gamma^{T}K_0\gamma$ is read off from the coefficients: the coefficient of $P_{\{a,b\}}=i\gamma_a\gamma_b$, $a<b$, is $-i(K_0)_{ab}/2$.
--
--   The sums $L_q$ and $J_q$ measure how large and how nonlocal an operator is, independently of the system size.
--
--   **Formalization Note** The sums run over even $R$, so $L_q$ does not see an odd part of an operator; statements about an operator not visibly even also state its evenness. $J_q$ is a real supremum over the labels, equal to the printed maximum for $n\ge 1$ and to $0$ for $n=0$.
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, eqs. (A.7)–(A.8), p. 9, and (B.70), p. 18

import Mathlib
import Definitions.Def_FermiGaussMix_P

open scoped BigOperators
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- The Majorana coefficient `o_R = 2^{-n} Tr(P_R O)` of eqs. (A.7)–(A.8), p.9 (Han, Zhao, Liu,
arXiv:2609.35159v1).

**Formalization Note** It is defined for every operator. If `O` has an odd part, that part has no effect on
`coeff O R` for even `R`, so bounds on the coefficients of an operator do not control an odd part. -/
noncomputable def coeff {n : ℕ} (O : Op n) (R : Finset (Fin (2 * n))) : ℂ :=
  (2 : ℂ)⁻¹ ^ n * (P n R * O).trace

/-- "Every Majorana monomial in `Y` has degree at most `k`" (Lemma B.6, p.20, Han, Zhao, Liu,
arXiv:2609.35159v1). -/
def HasDegreeLE {n : ℕ} (k : ℕ) (Y : Op n) : Prop :=
  ∀ R : Finset (Fin (2 * n)), Even R.card → k < R.card → coeff Y R = 0

/-- `L_q(Y) = Σ_R |y_R| q^{|R|}`, eq. (B.70), p.18 (Han, Zhao, Liu, arXiv:2609.35159v1).

**Formalization Note** The sum runs over even `R`, including `R = ∅`. It is blind to an odd part of `Y`, so
every statement that bounds `Lq q Y` for a `Y` not visibly even also states evenness. -/
noncomputable def Lq {n : ℕ} (q : ℝ) (Y : Op n) : ℝ :=
  ∑ R ∈ evenSets n, ‖coeff Y R‖ * q ^ R.card

/-- `J_q(Y) = max_a Σ_{R∋a} |y_R| q^{|R|}`, eq. (B.70), p.18 (Han, Zhao, Liu, arXiv:2609.35159v1).

**Formalization Note** This is a real supremum over the finite type of labels, hence the printed maximum when
`n ≥ 1`. At `n = 0` there is no label and the value is `0`, the empty sum. -/
noncomputable def Jq {n : ℕ} (q : ℝ) (Y : Op n) : ℝ :=
  ⨆ a : Fin (2 * n), ∑ R ∈ (evenSets n).filter (fun R => a ∈ R), ‖coeff Y R‖ * q ^ R.card

/-- The matrix `K₀` of eq. (A.4), p.9, read off from `H₀` by the sentence "The coefficient of
`P_{a,b} = iγ_aγ_b` in `H₀` is `-i(K₀)_{ab}/2`" (Han, Zhao, Liu, arXiv:2609.35159v1).

**Formalization Note** The printed identity holds for `a < b`, where `P_{a,b} = iγ_aγ_b` by (A.2). The matrix
is extended antisymmetrically, with `0` on the diagonal. -/
noncomputable def K0 {n : ℕ} (H : Op n) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  fun a b =>
    if a < b then 2 * Complex.I * coeff H {a, b}
    else if b < a then -(2 * Complex.I * coeff H {a, b})
    else 0

end FermiGaussMix


