-- Prove2me | Definitions.Def_eulerMascheroni_padeTransform
-- name    : eulerMascheroni_padeTransform
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-11T14:04:56.728342+00:00
-- url     : https://prove2.me/theorems/0e5a00df-86f3-45f7-b67c-6e117886e528
-- title:
--   Euler Padé recurrence and the factorial quotient binomial transform
-- statement:
--   Define integer sequences $P_n,Q_n$ by $P_0=0,P_1=1,Q_0=1,Q_1=2$ and
--
--   $$U_{n+2}=(2n+4)U_{n+1}-(n+1)^2U_n.$$
--
--   For a real sequence $f$, define
--
--   $$T_n(f)=\sum_{j=0}^n\binom nj\binom{n+j}n f_{n+j}.$$
--
--   The integer weights transfer common-denominator information to normalized Padé linear forms.
-- source:
--   Matala-aho–Zudilin, Euler’s factorial series and global relations, https://arxiv.org/html/1703.02633, Eqs. (10)–(11) and the preceding explicit Padé polynomials. The finite transform realizes (Q_n a−P_n)/(n!)² for the factorial quotient coefficients; this realization is a theorem, not built into the definition.

import Definitions.Def_eulerMascheroni_factorialQuotient

namespace EulerMascheroni.Arithmetic

def padeSeq (u₀ u₁ : ℤ) : ℕ → ℤ
  | 0 => u₀
  | 1 => u₁
  | n+2 => (2*(n:ℤ)+4)*padeSeq u₀ u₁ (n+1) - ((n:ℤ)+1)^2*padeSeq u₀ u₁ n

def padeP : ℕ → ℤ := padeSeq 0 1

def padeQ : ℕ → ℤ := padeSeq 1 2

noncomputable def binomialTransform (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), ((n.choose j * (n+j).choose n : ℕ) : ℝ) * f (n+j)

end EulerMascheroni.Arithmetic


