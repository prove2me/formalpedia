-- Prove2me | Definitions.Def_DynHaussler_ldim
-- name    : DynHaussler_ldim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:46.365742+00:00
-- url     : https://prove2.me/theorems/5acac25f-2d0c-4cfb-8e62-01daf7f61878
-- title:
--   Littlestone dimension $\mathrm{Ldim}(H)$ of a binary class
-- statement:
--   Let $H\subseteq\{0,1\}^X$ be a binary class. An **instance tree** of depth $n$ is a family $x=(x_t)_{t=1}^n$ of maps $x_t:\{-1,+1\}^{t-1}\to X$. The tree is **Littlestone-shattered** by $H$ if every sign path $\sigma\in\{-1,+1\}^n$ has a witness $h\in H$ with
--   $$
--   h\bigl(x_t(\sigma_{<t})\bigr)=\frac{1+\sigma_t}{2}\qquad(t=1,\dots,n).
--   $$
--   The **Littlestone dimension** $\mathrm{Ldim}(H)$ is the largest depth of a shattered tree, and $\infty$ if these depths are unbounded.
--
--   The Littlestone dimension is the controlling parameter of online learnability of binary classes; for binary classes it coincides with the sequential fat-shattering dimension at every scale $0<\eta\le1$, and the lower-bound class $H_d$ of the mission has $\mathrm{Ldim}(H_d)=d$.
--
--   **Formalization Note** A binary class is a set of real functions $X\to\mathbb R$ with values in $\{0,1\}$, so it is literally a subclass of $[0,1]^X$. Signs are `Bool` with `true` $\mapsto+1$, so the required label is $1$ on `true` and $0$ on `false`; rounds are 0-based. The value lies in `ℕ∞`; the empty class gets $0$ rather than $-1$, which never matters since the definition is only applied to nonempty classes.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Section 3.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_histPrefix

set_option autoImplicit false

namespace DynHaussler

/-- The **Littlestone dimension** `Ldim(H)` of a binary class `H ⊆ {0,1}^X`: the largest depth `n`
of an instance tree `x = (x_t)_{t=1}^n`, `x_t : {−1,+1}^{t−1} → X`, on which every sign path `σ`
has a witness `h ∈ H` with `h(x_t(σ_{<t})) = (1 + σ_t)/2` at every level; `∞` if these depths are
unbounded.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Section 3.1, p.13 (PDF p.15).

**Formalization Note** A binary class is a class of real functions `X → ℝ` with values in
`{0, 1}`, so that it is literally a subclass of `[0,1]^X`. Signs are `Bool` with `true ↦ +1`, so
the required label `(1 + σ_t)/2` is `1` on `true` and `0` on `false`. Rounds are 0-based
(`Fin n`). The value lies in `ℕ∞` (`⊤` for unbounded depths); the empty class gets `0` rather
than the paper's `−1`, which never matters because this definition is only applied to nonempty
classes. -/
noncomputable def ldim {X : Type*} (H : Set (X → ℝ)) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ z : NondualOpt.Tree X n, ∀ b : Fin n → Bool, ∃ h ∈ H, ∀ t : Fin n,
      h (z t (NondualOpt.histPrefix b t)) = if b t then 1 else 0), (n : ℕ∞)

end DynHaussler


