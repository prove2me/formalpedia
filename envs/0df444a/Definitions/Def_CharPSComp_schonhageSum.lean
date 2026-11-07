-- Prove2me | Definitions.Def_CharPSComp_schonhageSum
-- name    : CharPSComp_schonhageSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:16.586194+00:00
-- url     : https://prove2.me/theorems/c24b9497-6912-44a1-9e90-47a859e3914f
-- title:
--   The linear forms $\phi_\lambda,\psi_\lambda,\chi_\lambda$ of Schönhage's identity and the polynomials $G$, $G_{\mathrm{err}}$
-- statement:
--   The integer form of Schönhage's identity (Appendix A.1) lives in the polynomial ring over $\mathbb Z$ in the variables
--   $$I_X=\{x_i:i\in[q_0]\}\cup\{u_{ij}:i,j\in[q_0-1]\},\quad I_Y=\{y_j\}\cup\{v_{ij}\},\quad I_Z=\{z_0\}\cup\{z_{ij}:i,j\in[q_0]\}.$$
--   $\widehat U$ is $U=(u_{ij})$ extended by a row of negative column sums and a zero column; $\widehat V$ is $V=(v_{ij})$ extended by a column of negative row sums and a zero row. Over $\Lambda\triangleq\{0\}\cup[q_0]^2$,
--   $$\phi_{ij}=x_i+\widehat U_{ij},\ \psi_{ij}=y_j+\widehat V_{ij},\ \chi_{ij}=z_{ij}+z_0,\qquad \phi_0=-\sum_ix_i,\ \psi_0=\sum_jy_j,\ \chi_0=z_0 .$$
--   `schonhageSum q` is $\sum_{\lambda\in\Lambda}\phi_\lambda\psi_\lambda\chi_\lambda$, and
--   $$G\triangleq\sum_{i,j=1}^{q_0}x_iy_jz_{ij}+z_0\sum_{i,j=1}^{q_0-1}u_{ij}v_{ij},\qquad G_{\mathrm{err}}\triangleq\sum_{i,j=1}^{q_0}\big(x_i\widehat V_{ij}+\widehat U_{ij}y_j+\widehat U_{ij}\widehat V_{ij}\big)z_{ij}.$$
--
--   **Formalization Note** Indices are $0$-based: $[q_0]$ is `Fin q₀`, $[q_0-1]$ is `Fin (q₀-1)`, and the appended row and column sit at index $q_0-1$.
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Appendix A.1, pp.18–19 (PDF pp.19–20)

import Mathlib

namespace CharPSComp

open MvPolynomial

/-- The indeterminates of Schönhage's identity (Zhu, *Faster Power Series Composition in Fixed
Positive Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), Appendix A.1, p.18,
PDF p.19): `I_X = {x_i : i ∈ [q₀]} ∪ {u_ij : i, j ∈ [q₀−1]}`, `I_Y = {y_j} ∪ {v_ij}`,
`I_Z = {z₀} ∪ {z_ij : i, j ∈ [q₀]}`.

**Formalization Note** Indices are `0`-based: the paper's `[q₀] = {1, …, q₀}` is `Fin q₀` and
`[q₀ − 1]` is `Fin (q₀ − 1)`; the row and column the paper appends at index `q₀` are index
`q₀ − 1` here. -/
inductive SVar (q : ℕ) : Type
  | x (i : Fin q)
  | u (i j : Fin (q - 1))
  | y (j : Fin q)
  | v (i j : Fin (q - 1))
  | z0
  | z (i j : Fin q)

/-- `Û`: `U = (u_ij)` extended by a row of negative column sums (at index `q₀ − 1`) and a zero
column (at index `q₀ − 1`) (ibid., p.18–19). -/
noncomputable def Uhat (q : ℕ) (i j : Fin q) : MvPolynomial (SVar q) ℤ :=
  if hij : i.val < q - 1 ∧ j.val < q - 1 then X (SVar.u ⟨i.val, hij.1⟩ ⟨j.val, hij.2⟩)
  else if hj : j.val < q - 1 then -∑ i' : Fin (q - 1), X (SVar.u i' ⟨j.val, hj⟩)
  else 0

/-- `V̂`: `V = (v_ij)` extended by a column of negative row sums (at index `q₀ − 1`) and a zero row
(at index `q₀ − 1`) (ibid., p.19). -/
noncomputable def Vhat (q : ℕ) (i j : Fin q) : MvPolynomial (SVar q) ℤ :=
  if hij : i.val < q - 1 ∧ j.val < q - 1 then X (SVar.v ⟨i.val, hij.1⟩ ⟨j.val, hij.2⟩)
  else if hi : i.val < q - 1 then -∑ j' : Fin (q - 1), X (SVar.v ⟨i.val, hi⟩ j')
  else 0

/-- The left side of (10) (ibid., Appendix A.1, p.19, PDF p.20): `Σ_{λ∈Λ} ϕ_λ ψ_λ χ_λ` over
`Λ ≜ {0} ∪ [q₀]²`, with `ϕ_ij ≜ x_i + Û_ij`, `ψ_ij ≜ y_j + V̂_ij`, `χ_ij ≜ z_ij + z₀`,
`ϕ₀ ≜ −Σ_i x_i`, `ψ₀ ≜ Σ_j y_j`, `χ₀ ≜ z₀`. -/
noncomputable def schonhageSum (q : ℕ) : MvPolynomial (SVar q) ℤ :=
  (-∑ i : Fin q, X (SVar.x i)) * (∑ j : Fin q, X (SVar.y j)) * X SVar.z0
    + ∑ i : Fin q, ∑ j : Fin q,
        (X (SVar.x i) + Uhat q i j) * (X (SVar.y j) + Vhat q i j) * (X (SVar.z i j) + X SVar.z0)

/-- `G ≜ Σ_{i,j=1}^{q₀} x_i y_j z_ij + z₀ Σ_{i,j=1}^{q₀−1} u_ij v_ij` (ibid., p.19). -/
noncomputable def schonhageG (q : ℕ) : MvPolynomial (SVar q) ℤ :=
  ∑ i : Fin q, ∑ j : Fin q, X (SVar.x i) * X (SVar.y j) * X (SVar.z i j)
    + X SVar.z0 * ∑ i : Fin (q - 1), ∑ j : Fin (q - 1), X (SVar.u i j) * X (SVar.v i j)

/-- `G_err ≜ Σ_{i,j=1}^{q₀} (x_i V̂_ij + Û_ij y_j + Û_ij V̂_ij) z_ij` (ibid., p.19). -/
noncomputable def schonhageGerr (q : ℕ) : MvPolynomial (SVar q) ℤ :=
  ∑ i : Fin q, ∑ j : Fin q,
    (X (SVar.x i) * Vhat q i j + Uhat q i j * X (SVar.y j) + Uhat q i j * Vhat q i j)
      * X (SVar.z i j)

end CharPSComp


