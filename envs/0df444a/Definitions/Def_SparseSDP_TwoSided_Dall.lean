-- Prove2me | Definitions.Def_SparseSDP_TwoSided_Dall
-- name    : SparseSDP_TwoSided_Dall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:04.83241+00:00
-- url     : https://prove2.me/theorems/a6ad0659-95bd-4f6e-8a73-bfc0266cf7a8
-- title:
--   The target-value game: payoff matrices $D_j(g)$, value $s_g$, certificates $\ell_g,u_g$
-- statement:
--   For a candidate value $g$, on the lifted index (one extra coordinate records unused trace),
--   $$
--   D_0(g)=\begin{pmatrix}C&0\\0&0\end{pmatrix}-\frac gRI_{n+1},\qquad D_j(g)=\frac{b_j}{R}I_{n+1}-\begin{pmatrix}A_j&0\\0&0\end{pmatrix},
--   $$
--   Eq. (44). With simplex radius one, $s_g=\max_{Y\in R\mathcal S_{n+1}}\min_{0\le j\le m}\langle D_j(g),Y\rangle$ (Eq. (47)), and the lower and upper certificates of a returned pair are
--   $$
--   \ell_g=\min_{0\le j\le m}\langle D_j(g),Y^{\mathrm{out}}\rangle,\qquad u_g=R\lambda_{\max}\Big(\sum_{j=0}^mp^{\mathrm{out}}_jD_j(g)\Big),
--   $$
--   Eqs. (52), (53). The value $g$ is **attainable** if some $X\succeq0$ with $\operatorname{Tr}X\le R$ has $\langle C,X\rangle\ge g$ and $\langle A_j,X\rangle\le b_j$ for all $j$ (Eq. (43)).
--
--   This game turns optimization into a sequence of feasibility tests.
--
--   **Formalization Note** Index $0$ of `Fin (m+1)` is the objective and $j+1$ is constraint $j$.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, §2.6.2, Eqs. (43)–(47), pp. 18–19; Eqs. (52), (53), p. 19

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Instance

open Matrix
open scoped ComplexOrder

namespace SparseSDP.TwoSided

variable {𝕜 : Type*} [RCLike 𝕜] {κ : Type*} [Fintype κ] [DecidableEq κ] {n m : ℕ}

/-- `D₀(g) = (C 0; 0 0) − (g/R) I`, Eq. (44), p. 18. -/
noncomputable def D0 (C : Matrix κ κ 𝕜) (R g : ℝ) : Matrix (κ ⊕ Unit) (κ ⊕ Unit) 𝕜 :=
  fromBlocks C 0 0 0 - (g / R) • (1 : Matrix (κ ⊕ Unit) (κ ⊕ Unit) 𝕜)

/-- `Dⱼ(g) = (bⱼ/R) I − (Aⱼ 0; 0 0)`, Eq. (44), p. 18. -/
noncomputable def Dj (A : Matrix κ κ 𝕜) (b R : ℝ) : Matrix (κ ⊕ Unit) (κ ⊕ Unit) 𝕜 :=
  (b / R) • (1 : Matrix (κ ⊕ Unit) (κ ⊕ Unit) 𝕜) - fromBlocks A 0 0 0

/-- The payoff matrices `D₀(g), D₁(g), …, D_m(g)` of the target-value game; index `0` is the
objective and index `j + 1` is constraint `j`. -/
noncomputable def Dall (I : Instance 𝕜 n m) (R g : ℝ) :
    Fin (m + 1) → Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) 𝕜 :=
  Fin.cases (D0 I.C R g) fun j => Dj (I.A j) (I.b j) R

/-- `s_g = max_{Y ∈ RS_{n+1}} min_{0 ≤ j ≤ m} ⟨Dⱼ(g), Y⟩`, Eq. (47), p. 19 (simplex radius one). -/
noncomputable def gameValue (I : Instance 𝕜 n m) (R g : ℝ) : ℝ :=
  saddleValue (Dall I R g) R 1

/-- `ℓ_g = min_{0 ≤ j ≤ m} ⟨Dⱼ(g), Y^out⟩`, Eq. (52), p. 19. -/
noncomputable def lowCert (I : Instance 𝕜 n m) (R g : ℝ)
    (Y : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) 𝕜) : ℝ :=
  minOver fun j => hs (Dall I R g j) Y

/-- `u_g = R λmax(∑ⱼ p_j^out Dⱼ(g))`, Eq. (53), p. 19. -/
noncomputable def upCert (I : Instance 𝕜 n m) (R g : ℝ) (p : Fin (m + 1) → ℝ) : ℝ :=
  R * lamMax (adj (Dall I R g) p)

/-- `g` is attainable: there is `X ⪰ 0` with `Tr X ≤ R`, `⟨C, X⟩ ≥ g` and `⟨Aⱼ, X⟩ ≤ bⱼ` for all
`j`, Eq. (43), p. 18. -/
def Attainable (I : Instance 𝕜 n m) (R g : ℝ) : Prop :=
  ∃ X : Matrix (Fin n) (Fin n) 𝕜, X.PosSemidef ∧ RCLike.re (Matrix.trace X) ≤ R ∧
    g ≤ hs I.C X ∧ ∀ j, hs (I.A j) X ≤ I.b j

end SparseSDP.TwoSided


