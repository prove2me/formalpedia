-- Prove2me | Definitions.Def_AbelianCayleyHDX_Delta
-- name    : AbelianCayleyHDX_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:34:29.114205+00:00
-- url     : https://prove2.me/theorems/a4b557a5-4f0d-43fc-863e-09c26f6206a7
-- title:
--   The hyperplane parameter $\Delta(D)$
-- statement:
--   For $D \subseteq \mathrm{PG}(t-1, F)$,
--   $$\Delta(D) = \min_{0 \ne c \in V_0^\vee} \big|\{[a] \in D : c(a) \neq 0\}\big|,$$
--   the least number of directions of $D$ outside a hyperplane. When $D$ spans, it is the minimum distance of the evaluation code $\{(c(a))_{[a] \in D} : c \in V_0^\vee\}$.
--
--   **Formalization Note** Whether $c(a) \ne 0$ does not depend on the representative. For $t = 0$ there is no nonzero functional and the value is a junk $0$; every statement using $\Delta$ assumes $t \ge 1$, as Section 3.1 does.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.1, p.11

import Mathlib
import Definitions.Def_AbelianCayleyHDX_PG

namespace AbelianCayleyHDX

/-- **`Δ(D)`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.1, p.11): `Δ(D) = min_{0 ≠ c ∈ V₀^∨} |{[a] ∈ D : c(a) ≠ 0}|`.

**Formalization Note** The minimum is `sInf` over the attained values; whether `c(a) ≠ 0` does
not depend on the representative `a` of `[a]`. For `t = 0` there is no nonzero functional and the
value is the junk `0`; every statement using `Δ` assumes `t ≥ 1`, as Section 3.1 does. -/
noncomputable def Delta {t : ℕ} {F : Type*} [Field F] [DecidableEq F] (D : Finset (PG t F)) : ℕ :=
  sInf {k : ℕ | ∃ c : Module.Dual F (Fin t → F), c ≠ 0 ∧ (D.filter fun d => c d.rep ≠ 0).card = k}

end AbelianCayleyHDX


