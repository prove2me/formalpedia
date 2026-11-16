-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_Supplement_Portfolio
-- name    : FasterExactColoring_ThreeColor_Supplement_Portfolio
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:49:21.605673+00:00
-- url     : https://prove2.me/theorems/c74270a2-ee47-4e30-bb89-bdf49ef76e09
-- title:
--   General finite terminal portfolios and their dual comparison
-- statement:
--   Fix arbitrary finite parameter and algorithm counts $p,a$, matrices $M\in\mathbb R^{3\times p}$ and $R\in\mathbb R^{a\times p}$, and a nonnegative parameter function $x(P)\in\mathbb R^p$ on valid terminal instances. Polynomial computability is witnessed by one deterministic finite program producing dyadic approximations to absolute error $2^{-q}$ in time polynomial in $n+q+1$. Signed integer numerators and the requested precision give an explicit encoding.
--
--   The parameter identity and the dual conditions are
--   $$Mx(P)=(|S|,n_{K_3},n_{K_4})^\top,\qquad
--    \eta\ge0,\quad\mathbf1^\top\eta=1,\quad
--    \eta^\top R\le(\ln r)(\omega_{c3},\omega_{k3},\omega_{k4})M.$$
--
--   Each row of the portfolio has its own actual finite program, uniform positive polynomial coefficient and natural exponent, deciding terminal instances within $O^*(\exp(R_i x(P)+\gamma n))$. The fixed finite portfolio is defined in either algorithm mode. This supplies the general interfaces needed for Lemma 5.8 without restricting that lemma to Appendix E's eleven parameters. The source's $n$ is the original graph order, retained throughout branching.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 5.8, Eqs. (8)–(9), p. 15 (PDF p. 17)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_TerminalBounds
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_Measure

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

def signedCode (a : ℤ) : ℕ := if 0 ≤ a then 2*a.natAbs else 2*a.natAbs+1

/-- Fixed-precision dyadic output: denominator 2^q is implicit in the request. -/
def parameterCode {p : ℕ} (a : Fin p → ℤ) : List ℕ :=
  (List.finRange p).map (fun j => signedCode (a j))

/-- Polynomial computability of a real parameter vector, to requested absolute
precision 2^(-q). The finite program, constants and exponent precede all inputs. -/
def parametersComputable {p : ℕ} (x : {n : ℕ} → Restricted n → Fin p → ℝ) : Prop :=
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧ deterministic A ∧
    ∀ (n : ℕ) (P : Restricted n) (q : ℕ), P.valid → P.terminal →
      runWithin A (P.code ++ [q]) (C*(n+q+1 : ℕ)^d) (fun y =>
        ∃ a : Fin p → ℤ, y = parameterCode a ∧
          ∀ j, |(a j : ℝ)/(2 : ℝ)^q - x P j| ≤ (2 : ℝ)^(-(q : ℤ)))

noncomputable def parameterIdentity {p : ℕ}
    (x : {n : ℕ} → Restricted n → Fin p → ℝ) (M : Matrix (Fin 3) (Fin p) ℝ) : Prop :=
  ∀ (n : ℕ) (P : Restricted n), P.valid → P.terminal →
    (∀ j, 0 ≤ x P j) ∧
    ∀ i, (∑ j, M i j*x P j) = ![(P.S.card : ℝ),P.nClique 3,P.nClique 4] i

noncomputable def terminalPortfolio {p a : ℕ} (mode : Mode) (γ : ℝ)
    (x : {n : ℕ} → Restricted n → Fin p → ℝ) (R : Matrix (Fin a) (Fin p) ℝ) : Prop :=
  ∀ i : Fin a, ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧
    ∀ (n : ℕ) (P : Restricted n), P.valid → P.terminal →
      decides mode A P.code
        (polynomial C d P.code * Real.exp ((∑ j, R i j*x P j)+γ*n)) P.colorable

noncomputable def dualComparison {p a : ℕ} (r : ℝ) (w : Weights)
    (M : Matrix (Fin 3) (Fin p) ℝ) (R : Matrix (Fin a) (Fin p) ℝ)
    (η : Fin a → ℝ) : Prop :=
  (∀ i, 0 ≤ η i) ∧ (∑ i, η i) = 1 ∧
  ∀ j, (∑ i, η i*R i j) ≤
    Real.log r * (w.c3*M 0 j+w.k3*M 1 j+w.k4*M 2 j)

end FasterExactColoring.ThreeColor.Supplement


