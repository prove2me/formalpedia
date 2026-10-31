-- Prove2me | Definitions.Def_MaxEntSampling_zLD
-- name    : MaxEntSampling_zLD
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:32.761397+00:00
-- url     : https://prove2.me/theorems/438922aa-f048-4347-bef7-06b0b2518e2e
-- title:
--   The value $z^{LD}$ of the Lagrangian dual LD (5)
-- statement:
--   Let $v_i$ be the $i$-th column of $V\in\mathbb R^{d\times n}$. The **Lagrangian dual** of MESP is
--
--   $$
--   z^{LD} := \min_{\Lambda\succ0,\ \nu\ge0,\ \mu\in\mathbb R^n_+}\Bigl\{-\log{\det}_s(\Lambda)+s\nu+\sum_{i\in[n]}\mu_i-s : \nu+\mu_i\ge v_i^\top\Lambda v_i\ \ \forall i\in[n]\Bigr\}.
--   $$
--
--   Theorem 1 shows $z^{LD}\ge z^*$, and Theorem 2 identifies $z^{LD}$ with the value of PC (9).
--
--   **Formalization Note** (1) $\Lambda$ ranges over positive definite matrices; the display (5) writes $\Lambda\succeq0$, but the derivation (6) and Lemmas 1 and 3 use $\Lambda\succ0$, and a singular $\Lambda$ has objective $+\infty$. (2) "$\nu,\mu\in\mathbb R^n_+$" is read as a scalar $\nu\ge0$ and $\mu\in\mathbb R^n_+$. (3) The minimum is the infimum in the extended reals.
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, eq. (5), p.7 (PDF p.7)

import Mathlib
import Definitions.Def_MaxEntSampling_detBot

open Matrix

namespace MaxEntSampling

/-- **The optimal value `z^LD` of the Lagrangian dual LD (5).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, eq. (5), p.7 (PDF p.7):
"(LD) z^LD := min_{Λ⪰0, ν, µ∈R^n_+} { − log det_s(Λ) + sν + Σ_{i∈[n]} µi − s :
ν + µi ≥ vi^⊤Λvi, ∀i ∈ [n] }".

`zLD V s` is the infimum of `−log det_s(Λ) + sν + Σ_i µ_i − s` over symmetric positive definite
`Λ ∈ ℝ^{d×d}`, scalars `ν ≥ 0` and `µ ∈ ℝⁿ₊` with `ν + µ_i ≥ v_iᵀ Λ v_i` for every `i`, where
`v_i` is the `i`-th column of `V`.

**Formalization Note.** (1) `Λ` ranges over positive definite matrices: the display of (5) writes
`Λ ⪰ 0`, while the derivation (6), Lemma 1 and Lemma 3 use `Λ ≻ 0`; a singular `Λ ⪰ 0` has
`det_s(Λ) = 0`, i.e. objective `+∞`, so it never lowers the infimum. (2) "ν, µ ∈ R^n_+" is read as
a scalar `ν ≥ 0` and a vector `µ ∈ ℝⁿ₊`. (3) "min" is the optimal value, an infimum in `EReal`
(`sInf`). For `Λ ≻ 0`, `det_s(Λ) > 0`, so every objective value is a real number. -/
noncomputable def zLD {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (s : ℕ) : EReal :=
  sInf {z : EReal | ∃ (Λ : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (μ : Fin n → ℝ),
    Λ.PosDef ∧ 0 ≤ ν ∧ (∀ i, 0 ≤ μ i) ∧
    (∀ i, (fun a => V a i) ⬝ᵥ (Λ *ᵥ fun a => V a i) ≤ ν + μ i) ∧
    z = ((-Real.log (detBot s Λ) + s * ν + ∑ i, μ i - s : ℝ) : EReal)}

end MaxEntSampling


