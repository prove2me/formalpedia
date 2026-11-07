-- Prove2me | Definitions.Def_StrongConvFull
-- name    : StrongConvFull
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T08:50:02.004124+00:00
-- url     : https://prove2.me/theorems/50b9f8d3-c7eb-49e3-a93c-9cea8e33774f
-- title:
--   P(u, u*) as an element of M_D(ℂ) ⊗ C*(F_d), with u the canonical unitaries of the full group C*-algebra (Chen–Garza-Vargas–Tropp–van Handel 2026, p. 12)
-- statement:
--   A noncommutative polynomial with matrix coefficients, evaluated at the canonical unitaries $u_1, \dots, u_d$ of the full group $C^*$-algebra of the free group (`FullGroupCStar (FreeGroup (Fin d))`). In the paper the letters $s_i$ also denote the left-regular unitaries, for which $\|P(\boldsymbol s, \boldsymbol s^*)\|$ is the *reduced* norm; the unitaries here are different, so they are written $u_i$.
--
--   Chen–Garza-Vargas–Tropp–van Handel, p. 12: “We will formulate our strong convergence results for general noncommutative polynomials $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ with matrix coefficients, that is, $$P(\boldsymbol s, \boldsymbol s^*) = \sum_w A_w \otimes w(\boldsymbol s, \boldsymbol s^*),$$ where the sum is over a finite set of words $w$ in the symbols $s_1, \dots, s_d, s_1^*, \dots, s_d^*$ and $A_w \in \mathrm M_D(\mathbb C)$ are matrix coefficients.” The same page continues: “The notation used here agrees with the standard definition in terms of the norm in the full $C^*$-algebra of the free group, see, e.g., [17, Theorem 7].” That norm is the norm of $P(\boldsymbol u, \boldsymbol u^*)$, defined here.
--
--   - `StrongConv.NCPoly.letterElt` sends the formal letter $s_i$ (`Sum.inl i`) to the canonical unitary $u_i$ = `FullGroupCStar.of (FreeGroup.of i)` of the free generator $g_i$, and $s_i^*$ (`Sum.inr i`) to $u_i^*$.
--   - `StrongConv.NCPoly.wordElt w` is $w(\boldsymbol u, \boldsymbol u^*)$, the product of the images of the letters of the word $w$, in the order they appear.
--   - `StrongConv.NCPoly.toFull P` is $P(\boldsymbol u, \boldsymbol u^*) = \sum_w A_w \otimes w(\boldsymbol u, \boldsymbol u^*)$: the $D \times D$ matrix over $C^*(\mathbf F_d)$ whose $(a, b)$ entry is $\sum_w (A_w)_{ab}\, w(\boldsymbol u, \boldsymbol u^*)$, in `CStarMatrix (Fin D) (Fin D) (FullGroupCStar (FreeGroup (Fin d)))`, Mathlib's $C^*$-algebra of matrices over a $C^*$-algebra, which is $\mathrm M_D(\mathbb C) \otimes C^*(\mathbf F_d)$. Its norm is the paper's $\|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$ in the standard sense; `StrongConv.norm_toFull_eq_fullNorm` states that it equals the paper's supremum over unitary matrices.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 12, P(s, s*) in M_D(ℂ) ⊗ C*(F_d)

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_FullGroupCStar

/-!
# `P(u, u*)` in `M_D(ℂ) ⊗ C*(F_d)` (CGTvH p. 12)

A noncommutative polynomial `P = ∑_w A_w ⊗ w` with `D × D` matrix coefficients, evaluated at the
canonical unitaries `u₁, …, u_d` of the full group C*-algebra `C*(F_d)` of the free group (not the
left-regular unitaries `s₁, …, s_d` of the paper), as an element of the C*-algebra `CStarMatrix (Fin D) (Fin D) (C*(F_d))` of `D × D` matrices over `C*(F_d)`.
-/

noncomputable section

namespace StrongConv

namespace NCPoly

variable {D d : ℕ}

/-- The formal letter `sᵢ` (`Sum.inl i`) or `sᵢ*` (`Sum.inr i`) sent into `C*(F_d)`: the canonical
unitary `uᵢ` of the free generator `gᵢ`, or its adjoint. -/
def letterElt : Fin d ⊕ Fin d → FullGroupCStar (FreeGroup (Fin d))
  | Sum.inl i => (FullGroupCStar.of (FreeGroup.of i) : FullGroupCStar (FreeGroup (Fin d)))
  | Sum.inr i => star (FullGroupCStar.of (FreeGroup.of i) : FullGroupCStar (FreeGroup (Fin d)))

/-- A word in `s₁, …, s_d, s₁*, …, s_d*` evaluated at `u₁, …, u_d` in `C*(F_d)`: the product of its
letters in the order they appear. -/
def wordElt (w : FreeMonoid (Fin d ⊕ Fin d)) : FullGroupCStar (FreeGroup (Fin d)) :=
  (w.toList.map letterElt).prod

/-- `P(u, u*) = ∑_w A_w ⊗ w(u, u*)`, as an element of `M_D(C*(F_d))`. -/
def toFull (P : NCPoly D d) : CStarMatrix (Fin D) (Fin D) (FullGroupCStar (FreeGroup (Fin d))) :=
  CStarMatrix.ofMatrix fun a b => ∑ w ∈ P.support, (P w a b) • wordElt w

end NCPoly

end StrongConv


