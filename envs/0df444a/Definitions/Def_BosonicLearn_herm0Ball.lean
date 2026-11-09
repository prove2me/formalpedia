-- Prove2me | Definitions.Def_BosonicLearn_herm0Ball
-- name    : BosonicLearn_herm0Ball
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:22:42.453193+00:00
-- url     : https://prove2.me/theorems/08f631ce-65ab-4c52-83e8-09e517707215
-- title:
--   Schatten-norm balls $B_{p,a}(X_0)$ in $\mathrm{Herm}_0(n)$
-- statement:
--   For $X_0\in\mathrm{Herm}_0(n)$, $a\in\mathbb R$ and $p\in[1,\infty]$,
--
--   $$B_{p,a}(X_0)=\{X\in\mathrm{Herm}_0(n):\ \|X-X_0\|_p\le a\}.$$
--
--   The trace-norm ball $B_{\mathrm{tr},a}$ is $p=1$ and the operator-norm ball $B_{\mathrm{op},a}$ is $p=\infty$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.1, p. 30

import Mathlib
import Definitions.Def_BosonicLearn_Herm0
import Definitions.Def_WHMultiplicativity_schattenNorm

open scoped ENNReal

namespace BosonicLearn

/-- **Schatten-norm balls in `Herm₀(n)`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.1, p. 30: "for X_0 ∈ Herm_0(n), define the trace-norm ball B_{tr,a}(X_0) := {X ∈ Herm_0(n) :
‖X − X_0‖_tr ≤ a} and the operator-norm ball B_{op,a}(X_0) := {X ∈ Herm_0(n) : ‖X − X_0‖_op ≤ a}".

`herm0Ball p X₀ a = {X ∈ Herm₀(n) : ‖X − X₀‖_p ≤ a}`; `B_tr` is `p = 1`, `B_op` is `p = ∞`.

**Formalization Note.** `‖·‖_p` is the published Schatten norm `WHMultiplicativity.schattenNorm`
(`(tr |X|^p)^{1/p}` for `p < ∞`, the operator norm on `ℂⁿ` for `p = ∞`). -/
def herm0Ball {n : ℕ} (p : ℝ≥0∞) (X₀ : Herm0 n) (a : ℝ) : Set (Herm0 n) :=
  {X | WHMultiplicativity.schattenNorm p (((X - X₀ : Herm0 n)) : Matrix (Fin n) (Fin n) ℂ) ≤ a}

end BosonicLearn


