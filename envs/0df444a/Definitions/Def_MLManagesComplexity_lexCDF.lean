-- Prove2me | Definitions.Def_MLManagesComplexity_lexCDF
-- name    : MLManagesComplexity_lexCDF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:39:10.577549+00:00
-- url     : https://prove2.me/theorems/be190568-91aa-4111-b35d-fc2260e8cfd1
-- title:
--   Distribution families on $\{0,1\}^n$, the uniform family, and the lexicographic CDF
-- statement:
--   All distributions in the paper live on $\{0,1\}^n$. A **distribution family** $\mu=(\mu_n)_{n\in\mathbb N}$ gives a probability distribution $\mu_n$ on $\{0,1\}^n$ for every length $n$; $U=(U_n)$ is the **uniform family**, $U_n(x)=2^{-n}$.
--
--   For $x=x_1\dots x_n\in\{0,1\}^n$ let $\mathrm{rank}(x)=\sum_{i=1}^n x_i\,2^{n-i}$, the number with binary digits $x_1x_2\dots x_n$ ($x_1$ most significant); for strings of one length, $\mathrm{rank}(y)\le\mathrm{rank}(x)$ exactly when $y\le x$ in the lexicographic order. The **cumulative distribution function** of a distribution $\mu$ on $\{0,1\}^n$ is
--
--   $$
--   F_\mu(x)=\sum_{y\le x}\mu(y),
--   $$
--
--   the sum over all $y$ lexicographically at most $x$.
--
--   The CDF is the object through which the paper defines computable distributions (P/poly-computability).
--
--   **Formalization Note** Strings are functions $\mathrm{Fin}\,n\to\mathrm{Bool}$ and the paper's $x_i$ is the coordinate $i-1$. Masses are real numbers (the published `AutoregressiveCompression.Main.mass`, the real value of a Mathlib `PMF`).
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), §3.2, p.4 (PDF p.5): CDF; Theorem A.1(1), p.15 (PDF p.16): lexicographic order

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Information

set_option autoImplicit false

open AutoregressiveCompression.Main

namespace MLManagesComplexity

/-- A **family of distributions on `{0,1}^n`**, one for each length `n` (Fortnow,
arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), §3.2, printed p.4, PDF p.5:
"In this paper all distributions will be over {0, 1}^n").

**Formalization Note** A string `x = x₁ … xₙ` is a function `Fin n → Bool`; the paper's bit `xᵢ`
is `x ⟨i - 1, _⟩`. Asymptotic notions (negligible, polynomial size) are about such families. -/
abbrev DistFamily : Type := (n : ℕ) → PMF (Fin n → Bool)

/-- The **uniform distribution** `U` on `{0,1}^n`, as a family in `n`. -/
noncomputable def uniformFamily : DistFamily := fun n => PMF.uniformOfFintype (Fin n → Bool)

/-- The **lexicographic rank** of `x ∈ {0,1}^n`: the number with binary digits `x₁ x₂ … xₙ`,
`x₁` most significant. For strings of one length, `lexRank x ≤ lexRank y` iff `x ≤ y` in the
lexicographic order (with `0 < 1`). -/
def lexRank {n : ℕ} (x : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if x i then 2 ^ (n - 1 - i.val) else 0

/-- The **cumulative distribution function** of a distribution `μ` on `{0,1}^n` in the
lexicographic order (Fortnow, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), §3.2,
printed p.4, PDF p.5: "the CDF function f(x) = ∑_{y≤x} μ(y)"; Theorem A.1(1), printed p.15,
PDF p.16: "F_μ(x) = ∑_{z≤x} μ(z) … where ≤ is the lexicographic order on {0, 1}^n"):
`F_μ(x) = ∑_{y ≤_lex x} μ(y)`.

**Formalization Note** `≤_lex` is compared through `lexRank` (`x₁` most significant). Masses
are the real numbers `mass μ y = (μ y).toReal` of the published
`AutoregressiveCompression.Main.mass`. -/
noncomputable def lexCDF {n : ℕ} (μ : PMF (Fin n → Bool)) (x : Fin n → Bool) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : Fin n → Bool => lexRank y ≤ lexRank x), mass μ y

end MLManagesComplexity


