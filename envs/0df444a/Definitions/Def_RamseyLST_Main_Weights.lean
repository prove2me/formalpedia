-- Prove2me | Definitions.Def_RamseyLST_Main_Weights
-- name    : RamseyLST_Main_Weights
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:07:24.303209+00:00
-- url     : https://prove2.me/theorems/ffbf999a-b131-4541-a35c-e846a8cba4ab
-- title:
--   Set weights, $q$-decomposable weights (Definition 11) and the core exponents $\psi_1,\psi_2,\psi_3,\hat\psi$
-- statement:
--   For a weight function $w$ on a candidate core $Z^{in}$ and any set $Q$, the **weight** of $Q$ is $w(Q)=\sum_{z\in Q\cap Z^{in}}w(z)$ (p. 9).
--
--   A weight function $w:S\to\mathbb R_{>0}$ on a finite set $S$, with $W=w(S)$, is **$q$-decomposable** (Definition 11) if there are $\omega>0$ and a partition $S=A\uplus B$ with $w(z)\ge W/q$ for every $z\in A$ (heavy points) and $w(z)=\omega$ for every $z\in B$ (light points).
--
--   For parameters $\sigma$, $t$, $q$ and an aspect ratio bound $\Phi$, the core exponents of Table 3 are
--
--   $$\psi_1(\Phi)=(t\log_\sigma\Phi)^{-2/t},\qquad \psi_2=(\log q)^{-1/t},\qquad \psi_3=1-\frac1t,\qquad \hat\psi(\Phi)=\psi_1(\Phi)+\psi_2+\psi_3-2,$$
--
--   with $\log$ in base 2. In the paper $\sigma=800$ (Remark 1) and $q=2^t$ (Lemma 46).
--
--   These objects enter Lemmas 32, 34, 35 and 46.
--
--   **Formalization Note** Positivity of $w$ on $S$ is part of `IsQDecomposable`. The exponents are functions of explicit real parameters $\sigma,t,q,\Phi$, with `Real.logb` and `Real.rpow`.
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), pp. 9, 38–39, 48, 51, 56 (PDF 13, 42–43, 52, 55, 60), Definition 11, Table 3

import Mathlib

namespace RamseyLST.Main

/-- The weight of a set (§2, p. 9): for a weight function `w` on the candidate core `Zin`,
`w(Q) = ∑_{z ∈ Q ∩ Zin} w(z)`. -/
def setWeight {ι : Type} [DecidableEq ι] (Zin : Finset ι) (w : ι → ℝ) (Q : Finset ι) : ℝ :=
  ∑ z ∈ Q ∩ Zin, w z

/-- Definition 11 (p. 38, [BLMN05, Def. 3.18]): a weight function `w : S → ℝ_{>0}` on a finite
set `S`, with total weight `W = w(S)`, is `q`-decomposable if there are a value `ω > 0` and a
partition `S = A ⊎ B` with `w(z) ≥ W/q` for every `z ∈ A` (heavy points) and `w(z) = ω` for every
`z ∈ B` (light points). Positivity of `w` on `S` is part of the notion. -/
def IsQDecomposable {ι : Type} [DecidableEq ι] (q : ℝ) (S : Finset ι) (w : ι → ℝ) : Prop :=
  (∀ z ∈ S, 0 < w z) ∧
    ∃ ω : ℝ, 0 < ω ∧ ∃ A B : Finset ι, Disjoint A B ∧ A ∪ B = S ∧
      (∀ z ∈ A, (∑ s ∈ S, w s) / q ≤ w z) ∧ ∀ z ∈ B, w z = ω

/-- `ψ₁(Φ) = (t · log_σ Φ)^{-2/t}` (Table 3, p. 39; Lemma 34, p. 48). -/
noncomputable def psi1 (σ t Φ : ℝ) : ℝ := (t * Real.logb σ Φ) ^ (-2 / t)

/-- `ψ₂ = (log q)^{-1/t}`, with `log` in base 2 (Table 3, p. 39; Lemma 35, p. 48). -/
noncomputable def psi2 (q t : ℝ) : ℝ := (Real.logb 2 q) ^ (-1 / t)

/-- `ψ₃ = 1 − 1/t` (Table 3, p. 39). -/
noncomputable def psi3 (t : ℝ) : ℝ := 1 - 1 / t

/-- The overall core exponent `ψ̂(Φ⋆) = ψ₁(Φ⋆) + ψ₂ + ψ₃ − 2` (p. 39 and p. 51). -/
noncomputable def psiHat (σ q t Φ : ℝ) : ℝ := psi1 σ t Φ + psi2 q t + psi3 t - 2

end RamseyLST.Main


