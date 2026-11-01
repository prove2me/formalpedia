-- Prove2me | Definitions.Def_WildeQIT_QErasure_QCode_IsGood
-- name    : WildeQIT_QErasure_QCode_IsGood
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:59.740358+00:00
-- url     : https://prove2.me/theorems/78c77e8d-f2fe-4171-bd1d-86b333a670af
-- title:
--   Error criterion $\tfrac12\|\varphi_{RA_1}-\omega_{RB_1}\|_1\le\varepsilon$ of an $(n,Q,\varepsilon)$ code
-- statement:
--   A quantum communication code $(\mathcal E,\mathcal D)$ of block length $n$ for $\mathcal N$ meets the **error criterion** $\varepsilon$ if, for **every** pure state $|\phi\rangle_{RA_1}$, the final state
--
--   $$
--   \omega_{RB_1}\equiv\mathcal D_{B^n\to B_1}\big(\mathcal N^{\otimes n}_{A'\to B}(\mathcal E_{A_1\to A'^n}(\phi_{RA_1}))\big)
--   $$
--
--   satisfies
--
--   $$
--   \tfrac12\,\big\|\phi_{RA_1}-\omega_{RB_1}\big\|_1\le\varepsilon .
--   $$
--
--   This is the entanglement-transmission criterion of an $(n,Q,\varepsilon)$ code.
--
--   **Formalization Note** The maps act on the $A_1$ share via the published `QAlgorithms.idTensorSuperop`, with the reference as left factor; $\phi_{RA_1}=|\phi\rangle\langle\phi|$ for a unit vector; $\|\cdot\|_1$ is the published `WildeQIT.traceNorm`. The criterion is required for every unit vector, not only for the maximally entangled one.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §24.1, (24.1)–(24.2), p. 659

import Definitions.Def_WildeQIT_QErasure_QCode
import Definitions.Def_WildeQIT_Degradable_tensorPower
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Information

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §24.1, p. 659, (24.1)–(24.2)
(the error criterion of an `(n, Q, ε)` quantum communication code).
-/

namespace WildeQIT.QErasure

/-- **Error criterion of an `(n, Q, ε)` quantum communication code** (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, §24.1, p. 659): with the final state
`ω_{RB₁} ≡ D_{Bⁿ→B₁}(N_{A′ⁿ→Bⁿ}(E_{A₁→A′ⁿ}(ϕ_{RA₁})))` (24.1), where `N_{A′ⁿ→Bⁿ} ≡ (N_{A′→B})^{⊗n}`,
"the following condition should hold for all states `|ϕ⟩_{RA₁}`: `½ ‖ϕ_{RA₁} − ω_{RB₁}‖₁ ≤ ε`" (24.2).

**Formalization Note.** The reference `R` is the left factor `Fin m` of `Fin m × Fin m`; the maps act
on the right factor through the published `QAlgorithms.idTensorSuperop` (`id_R ⊗ Φ`). `ϕ_{RA₁}` is
`|ϕ⟩⟨ϕ|` (published `QAlgorithms.pureDensity`) for a unit vector `|ϕ⟩`, and the criterion is
required for **every** unit vector, as the book states (not only the maximally entangled one).
`‖·‖₁` is the published `WildeQIT.traceNorm`. -/
def QCode.IsGood {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] {n m : ℕ}
    (c : QCode a b n m) (N : QChannel a b) (ε : ℝ) : Prop :=
  ∀ ϕ : EuclideanSpace ℂ (Fin m × Fin m), ‖ϕ‖ = 1 →
    (1 / 2 : ℝ) * traceNorm (QAlgorithms.pureDensity ϕ -
      QAlgorithms.idTensorSuperop (R := Fin m)
        (fun X => c.dec.apply ((WildeQIT.Degradable.tensorPower N n).apply (c.enc.apply X)))
        (QAlgorithms.pureDensity ϕ)) ≤ ε

end WildeQIT.QErasure


