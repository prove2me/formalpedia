-- Prove2me | Definitions.Def_WildeQIT_ErasureClassical_errorProb
-- name    : WildeQIT_ErasureClassical_errorProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:35.183555+00:00
-- url     : https://prove2.me/theorems/8ec0c6fc-a847-48f0-a27b-8f316b702d1d
-- title:
--   Probability of error $p_e(m)$ of a classical code
-- statement:
--   Let $\mathcal N$ be a quantum channel and let a code consist of encoding states $\rho^m_{A'^n}$ and a decoding POVM $\{\Lambda_m\}$. The **probability of error** for message $m$ is
--
--   $$
--   p_e(m)\equiv 1-\Pr\{M'=m\mid M=m\}=\mathrm{Tr}\big\{(I-\Lambda_m)\,\mathcal N^{\otimes n}(\rho^m_{A'^n})\big\}.
--   $$
--
--   The maximal probability of error is $p_e^*=\max_m p_e(m)$, and the code has error at most $\varepsilon$ when $p_e^*\le\varepsilon$, i.e. when $p_e(m)\le\varepsilon$ for every message.
--
--   **Formalization Note** The trace is a complex number whose imaginary part vanishes for Hermitian arguments; its real part is taken.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §20.2.1, (20.12)–(20.14), p. 562

import Definitions.Def_WildeQIT_ErasureClassical_ClassicalCode
import Definitions.Def_WildeQIT_Degradable_tensorPower

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §20.2.1, p. 562,
eqs. (20.12)–(20.13) (probability of error for a message).
-/

namespace WildeQIT.ErasureClassical

/-- **Probability of error for message `m`** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 562, (20.12)–(20.13)): `p_e(m) ≡ 1 − Pr{M′ = m | M = m}
= Tr{(I − Λ_m) N^{⊗n}(ρᵐ_{A′ⁿ})}`.

**Formalization Note.** The trace is a complex number; its real part is taken (the trace is
real because `I − Λ_m` and `N^{⊗n}(ρᵐ)` are Hermitian). The maximal probability of error (20.14)
is bounded by `ε` exactly when `p_e(m) ≤ ε` for every `m`, which is how it is used. -/
noncomputable def errorProb {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {n M : ℕ} (N : QChannel a b) (c : ClassicalCode a b n M) (m : Fin M) : ℝ :=
  (((1 : Matrix (Fin n → b) (Fin n → b) ℂ) - c.dec m) * (WildeQIT.Degradable.tensorPower N n).apply (c.enc m)).trace.re

end WildeQIT.ErasureClassical


