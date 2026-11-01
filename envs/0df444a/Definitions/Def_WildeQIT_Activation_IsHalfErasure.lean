-- Prove2me | Definitions.Def_WildeQIT_Activation_IsHalfErasure
-- name    : WildeQIT_Activation_IsHalfErasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T19:11:47.059417+00:00
-- url     : https://prove2.me/theorems/6ce6d05a-119e-421c-94d4-c8c80222d6b9
-- title:
--   The 50% quantum erasure channel $\rho\mapsto\frac12\rho+\frac12|e\rangle\langle e|$
-- statement:
--   A channel $\mathcal N$ is a **50% quantum erasure channel** when it transmits its input state with probability $1/2$ and replaces it with an orthogonal erasure state with probability $1/2$:
--
--   $$
--   \rho\mapsto\tfrac12\,\rho+\tfrac12\,|e\rangle\langle e| ,\qquad \langle e|\rho|e\rangle=0 \text{ for all inputs } \rho ,
--   $$
--
--   the erasure channel (24.5) with $\varepsilon=1/2$. Its output space contains a copy of the input space and a unit vector $|e\rangle$ orthogonal to that copy.
--
--   **Formalization Note** The copy of the input space is the range of an isometry $V$ ($V^\dagger V=I$), and $|e\rangle$ is a unit vector with $V^\dagger|e\rangle=0$. The identity $\mathcal N(\rho)=\tfrac12V\rho V^\dagger+\tfrac12\operatorname{Tr}(\rho)\,|e\rangle\langle e|$ is required for every operator $\rho$, the linear extension of the book's map on density operators (where $\operatorname{Tr}\rho=1$). The output may be larger than the input plus the erasure flag, as (24.5) allows.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §24.2, eq. (24.5), p. 660, with ε = 1/2, and §24.8.2, p. 684

import Definitions.Def_WildeQIT_QChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §24.2, p. 660, eq. (24.5) with `ε = 1/2`, and §24.8.2, p. 684 ("a 50% quantum erasure
channel N1 that transmits its input state with probability 1/2 and replaces it with an orthogonal
erasure state with probability 1/2").
-/

open Matrix

namespace WildeQIT.Activation

/-- **The 50% quantum erasure channel** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, (24.5), p. 660, and p. 684): `N` is a 50% erasure
channel when its output space contains a copy of its input space and an erasure state `|e⟩`
orthogonal to that copy, and `N(ρ) = ½ ρ + ½ |e⟩⟨e|` (with `⟨e|ρ|e⟩ = 0` for all inputs).

**Formalization Note.** The copy of the input space is the range of an isometry
`V : A → B` (`V†V = I`), and `|e⟩` is a unit vector with `V†|e⟩ = 0`. The identity is required
for every operator `ρ` (linearity), with the erasure term weighted by `Tr ρ`, which is `1` on
density operators. The output may be larger than `A ⊕ span{|e⟩}`: such a channel is the book's
channel followed by an isometric embedding. -/
def IsHalfErasure {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b) : Prop :=
  ∃ (V : Matrix b a ℂ) (e : b → ℂ), Vᴴ * V = 1 ∧ star e ⬝ᵥ e = 1 ∧ Vᴴ *ᵥ e = 0 ∧
    ∀ ρ : Matrix a a ℂ,
      N.apply ρ = (1 / 2 : ℂ) • (V * ρ * Vᴴ) + ((1 / 2 : ℂ) * ρ.trace) • vecMulVec e (star e)

end WildeQIT.Activation


