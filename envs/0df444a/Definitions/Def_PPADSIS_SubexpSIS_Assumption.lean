-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_Assumption
-- name    : PPADSIS_SubexpSIS_Assumption
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:48:46.343567+00:00
-- url     : https://prove2.me/theorems/58707767-9d31-408e-8fbb-f4808b833f6a
-- title:
--   Assumption 3.5 (SIS_e) parameter regime, Assumption 3.5 and Assumption 7.7 (subexponentially hard SIS_e)
-- statement:
--   Fix a real constant $e$ and put $\beta(\lambda):=2^{n(\lambda)^e}$. Parameter functions $n,m,q:\mathbb N\to\mathbb N$ are **in the regime of Assumption 3.5** if
--
--   - $n$ is polynomially bounded and $n\ge\lambda^{\Omega(1)}$: for some real $c>0$, $n(\lambda)\ge\lambda^c$ for all sufficiently large $\lambda$;
--   - $m$ is polynomially bounded;
--   - at every $\lambda$, $q(\lambda)$ is a power of two with
--   $$n\sqrt m\cdot\beta\le q\le 2^{\mathrm{poly}(n)},$$
--   the upper bound being $q(\lambda)\le2^{(n(\lambda)+2)^k}$ for one exponent $k$.
--
--   **Assumption 3.5** ($\mathrm{SIS}_e$): for all parameters in this regime, $\mathrm{SIS}_{n,m,q,\beta}$ is polynomially hard.
--
--   **Assumption 7.7** (subexponentially hard $\mathrm{SIS}_e$) for constants $e,\nu$: for all parameters $n,m,q,\beta$ as in Assumption 3.5 that additionally satisfy $q(\lambda)\le2^{2\lceil n(\lambda)^e\rceil}$ at every $\lambda$, $\mathrm{SIS}_{n,m,q,\beta}$ is $2^{n^\nu}$-hard. The paper states it for $0<e<5/9$ and $4e/5<\nu<1-e$ (for instance $e=\nu=1/3$); these ranges are hypotheses of the theorems that use it.
--
--   It is the only hypothesis of the mission's goal: SIS at norm bound $2^{n^e}$, modulus between $n\sqrt m\,2^{n^e}$ and about $2^{2n^e}$, is hard for adversaries of size $2^{n^\nu}$.
--
--   **Formalization Note** The conditions on $q$ are required at every $\lambda$; requiring them only eventually would quantify over more parameter functions and make the assumption stronger. No computability of $n,m,q$ is required, as in the paper. The bound $q\le2^{\mathrm{poly}(n)}$ is kept although $q\le2^{2\lceil n^e\rceil}$ implies it.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 21, Assumption 3.5; p. 57, Assumption 7.7

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_SIS

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

/-- The norm bound `β(λ) := 2^{n(λ)^e}` of Assumption 3.5 (a real number). -/
noncomputable def betaE (e : ℝ) (n : ℕ → ℕ) (lam : ℕ) : ℝ := (2 : ℝ) ^ ((n lam : ℝ) ^ e)

/-- The **parameter regime of Assumption 3.5** (`SIS_e`; Choudhuri, *PPAD Hardness from SIS*, STOC
2027 submission (manuscript sha256 17abad73…), p. 21): with `β := 2^{n^e}`,
- `n` is polynomially bounded and `n ≥ λ^{Ω(1)}`: for some real `c > 0`, `n(λ) ≥ λ^c` for all
  sufficiently large `λ`;
- `m` is polynomially bounded;
- every `q(λ)` is a power of two with `n√m · β ≤ q ≤ 2^{poly(n)}`, i.e. `q(λ) ≤ 2^{(n(λ)+2)^k}` for
  one exponent `k`.
The conditions on `q` hold at every `λ`. -/
def SISeParams (e : ℝ) (n m q : ℕ → ℕ) : Prop :=
  PolyBounded n ∧
  (∃ c : ℝ, 0 < c ∧ ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, (lam : ℝ) ^ c ≤ n lam) ∧
  PolyBounded m ∧
  (∀ lam, ∃ k : ℕ, q lam = 2 ^ k) ∧
  (∀ lam, (n lam : ℝ) * Real.sqrt (m lam) * betaE e n lam ≤ q lam) ∧
  (∃ k : ℕ, ∀ lam, q lam ≤ 2 ^ ((n lam + 2) ^ k))

/-- **Assumption 3.5** (`SIS_e`, p. 21): for all parameters in the regime `SISeParams e`,
`SIS_{n,m,q,β}` with `β = 2^{n^e}` is polynomially hard. (Only its parameter set is used by this
mission's goal, through Assumption 7.7.) -/
def Assumption35 (e : ℝ) : Prop :=
  ∀ n m q : ℕ → ℕ, SISeParams e n m q → SISPolyHard n m q (betaE e n)

/-- **Assumption 7.7** (subexponentially hard `SIS_e`, p. 57) for the constants `e, ν`: for all
parameters `n, m, q, β` as in Assumption 3.5 that additionally satisfy `q ≤ 2^{2⌈n^e⌉}` (at every
`λ`), `SIS_{n,m,q,β}` is `2^{n^ν}`-hard. The paper states it for `0 < e < 5/9` and
`4e/5 < ν < 1 − e`; those ranges are hypotheses of the theorems that use it. -/
def Assumption77 (e ν : ℝ) : Prop :=
  ∀ n m q : ℕ → ℕ, SISeParams e n m q →
    (∀ lam, q lam ≤ 2 ^ (2 * ⌈(n lam : ℝ) ^ e⌉₊)) →
    SISSubexpHard n m q (betaE e n) ν

end PPADSIS.SubexpSIS


