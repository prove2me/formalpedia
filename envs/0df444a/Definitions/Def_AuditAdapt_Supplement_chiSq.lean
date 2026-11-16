-- Prove2me | Definitions.Def_AuditAdapt_Supplement_chiSq
-- name    : AuditAdapt_Supplement_chiSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:33:29.854201+00:00
-- url     : https://prove2.me/theorems/07530500-2ab9-4e55-82c2-51daa59c5501
-- title:
--   $\chi^2$-divergence $\chi^2(p\|q)$ of distributions on a finite set, with $\chi^2=\infty$ if $p\not\ll q$
-- statement:
--   For probability distributions $p,q$ on a finite set $\mathcal A$, the **$\chi^2$-divergence** is
--
--   $$
--   \chi^2(p\|q)=\begin{cases}\displaystyle\sum_{a\in\mathcal A}\frac{p(a)^2}{q(a)}-1, & p\ll q\ \ (q(a)=0\Rightarrow p(a)=0),\\[1ex] +\infty, & p\not\ll q,\end{cases}
--   $$
--
--   with values in $[0,\infty]$; a term with $q(a)=p(a)=0$ contributes $0$.
--
--   It is the complexity parameter of auditing from logs: the second moment of the importance weight $p/q$ is $1+\chi^2(p\|q)$. It is used for action distributions, $\chi^2(\bar p\|\pi(\cdot\mid x))$, and on the finite trajectory space, $\chi^2(P^\nu\|P^\pi)$.
--
--   **Formalization Note** The value is in `ℝ≥0∞`, so $\chi^2=\infty$ is represented. For distributions with $p\ll q$, Cauchy–Schwarz gives $\sum_a p(a)^2/q(a)\ge 1$, so `ENNReal.ofReal` does not truncate.
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), §2 "Information quantities", p.3 (PDF p.3; the PDF prints no page numbers)

import Mathlib

namespace AuditAdapt.Supplement

open scoped ENNReal

/-- The χ²-divergence of two distributions `p, q` on a finite set
(Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…), §2 "Information quantities", p.3: "For distributions p, q on A, χ²(p∥q) = Σ_a p(a)²/q(a) − 1,
with the convention χ² = ∞ if p ̸≪ q").

`chiSq p q = Σ_a p(a)²/q(a) − 1` when `p ≪ q` (every `a` with `q a = 0` has `p a = 0`), and `∞`
otherwise. The value lies in `[0, ∞]`.

**Formalization Note** The value is in `ℝ≥0∞`, so the paper's `χ² = ∞` is represented, not replaced
by a junk value. A term with `q a = 0` (hence `p a = 0`) is `0 / 0 = 0` in Lean, as it should be.
For distributions with `p ≪ q`, Cauchy–Schwarz gives `Σ_a p(a)²/q(a) ≥ 1`, so the `ENNReal.ofReal`
never truncates; it is only applied to distributions in this mission. The same definition on the
finite trajectory space gives `χ²(P^ν∥P^π)` of Theorem 5.5. -/
noncomputable def chiSq {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ≥0∞ :=
  if ∀ a, q a = 0 → p a = 0 then ENNReal.ofReal ((∑ a, p a ^ 2 / q a) - 1) else ⊤

end AuditAdapt.Supplement


