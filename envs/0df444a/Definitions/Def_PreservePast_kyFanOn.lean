-- Prove2me | Definitions.Def_PreservePast_kyFanOn
-- name    : PreservePast_kyFanOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:39:32.339687+00:00
-- url     : https://prove2.me/theorems/cb4b17f1-b079-484c-8b4f-af96e3dec282
-- title:
--   Ky Fan sums $\mathcal K_L(A)$, $\mathcal K_L(A|_U)$ and $\Gamma_r(M;p,Q)$
-- statement:
--   For a symmetric $m\times m$ matrix $A$, $\mathcal K_L(A)$ is the sum of its $L$ largest eigenvalues, and $\mathcal K_L(A|_U)$ is the same sum after compression of $A$ to a subspace $U\subseteq\mathbb R^m$. By Ky Fan's maximum principle, for $L\le\dim U$,
--   $$
--   \mathcal K_L(A|_U)=\max\Big\{\sum_{j=1}^{L}y_j^\top Ay_j\ :\ y_1,\dots,y_L\in U\ \text{orthonormal}\Big\},\qquad \mathcal K_L(A)=\mathcal K_L(A|_{\mathbb R^m}).
--   $$
--   For $M\succeq0$, a unit vector $p$ and a subspace $Q\ni p$ with $\dim Q\ge r$, the paper writes
--   $$
--   \Gamma_r(M;p,Q)=p^\top Mp+\mathcal K_{r-1}(M|_{Q\cap p^\perp}),
--   $$
--   the largest trace of $M$ captured by an $r$-dimensional subspace of $Q$ that contains the prescribed direction $p$.
--
--   **Formalization Note** $\mathcal K_L(A|_U)$ is defined by the maximum principle (a supremum over orthonormal $L$-families in $U$); it is used only for symmetric $A$ and $L\le\dim U$, where the supremum is attained (for $L>\dim U$ Lean's `sSup ∅ = 0`). $p^\perp=\{v:p^\top v=0\}$; $r-1$ is natural subtraction, used for $r\ge1$.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §C.4, p.20 (PDF p.22); p.22 (PDF p.24)

import Mathlib

open Matrix

namespace PreservePast

/-- `Y` is an orthonormal `L`-frame (a family of `L` orthonormal vectors of `ℝᵐ`) lying in the
subspace `U`. -/
def IsOrthoFrameIn {m L : ℕ} (U : Submodule ℝ (Fin m → ℝ)) (Y : Fin L → Fin m → ℝ) : Prop :=
  (∀ j, Y j ∈ U) ∧ ∀ j k, Y j ⬝ᵥ Y k = if j = k then 1 else 0

/-- **Ky Fan sum after compression** `𝒦_L(A|_U)`, and `𝒦_L(A) = 𝒦_L(A|_{ℝᵐ})`.
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.4, p.20 (PDF p.22): "For a symmetric matrix let 𝒦_L(A) be the sum of its largest L
eigenvalues; 𝒦_L(A|_U) denotes the sum after compression to U."

`kyFanOn L A U` is the largest value of `Σ_{j<L} y_jᵀ A y_j` over orthonormal families
`y_0, …, y_{L−1}` in `U`; `kyFanOn L A ⊤` is `𝒦_L(A)`.

**Formalization Note.** Defined by Ky Fan's maximum principle: for a symmetric `A` and
`L ≤ dim U`, the sum of the `L` largest eigenvalues of the compression `P_U A P_U|_U` equals this
maximum. It is used only for symmetric `A` and `L ≤ dim U`, where the set is nonempty and
bounded; for `L > dim U` the set is empty and Lean's `sSup ∅ = 0`. -/
noncomputable def kyFanOn {m : ℕ} (L : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (U : Submodule ℝ (Fin m → ℝ)) : ℝ :=
  sSup {s : ℝ | ∃ Y : Fin L → Fin m → ℝ, IsOrthoFrameIn U Y ∧ s = ∑ j, Y j ⬝ᵥ (A *ᵥ Y j)}

/-- The orthogonal complement `p^⊥ = {v : pᵀv = 0}` of a vector `p` in `ℝᵐ`. -/
def perp {m : ℕ} (p : Fin m → ℝ) : Submodule ℝ (Fin m → ℝ) :=
  LinearMap.ker (Matrix.toLin' (Matrix.replicateRow (Fin 1) p))

/-- **The trace captured with a prescribed direction** `Γ_r(M; p, Q) = pᵀMp + 𝒦_{r−1}(M|_{Q∩p^⊥})`.
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.4, p.22 (PDF p.24): "For M ⪰ 0 and a space Q ∋ p, with ‖p‖ = 1 and dim Q ≥ r, write
Γ_r(M; p, Q) = p^⊤Mp + 𝒦_{r−1}(M|_{Q∩p^⊥})."

**Formalization Note.** `r − 1` is natural subtraction; used for `r ≥ 1`. -/
noncomputable def gammaR {m : ℕ} (r : ℕ) (M : Matrix (Fin m) (Fin m) ℝ) (p : Fin m → ℝ)
    (Q : Submodule ℝ (Fin m → ℝ)) : ℝ :=
  p ⬝ᵥ (M *ᵥ p) + kyFanOn (r - 1) M (Q ⊓ perp p)

end PreservePast


