-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Supplement_toomRule
-- name    : AutoQMem_Lindblad_Supplement_toomRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:42:51.421004+00:00
-- url     : https://prove2.me/theorems/57e0df39-c5a1-4c39-9c0c-0b880329440b
-- title:
--   The 4D Toom update rules $a^{(X)}$, $a^{(Z)}$
-- statement:
--   For the plaquette $i=(x,\{\mu,\nu\})$ of the 4D toric code, its two **positively oriented boundary edges** are $e^+_{i,\mu}=(x+u_\mu,\{\nu\})$ and $e^+_{i,\nu}=(x+u_\nu,\{\mu\})$. The **X-sector Toom predicate** is
--   $$a^{(X)}_i(s)=s_{e^+_{i,\mu}}\,s_{e^+_{i,\nu}},$$
--   so $a^{(X)}_i(s)=1$ iff both positively oriented boundary edges carry syndrome. The **Z-sector predicate** is the same construction on the dual lattice: with $\{\kappa,\lambda\}$ the two directions not in $\{\mu,\nu\}$, the 3-cubes on the positive side of $i$ are $c^+_{i,\kappa}=(x,\{\mu,\nu,\kappa\})$ and $c^+_{i,\lambda}=(x,\{\mu,\nu,\lambda\})$, and $a^{(Z)}_i(s)=s_{c^+_{i,\kappa}}s_{c^+_{i,\lambda}}$.
--
--   These are the update rules lifted to the quantum channel of Theorem 3.
--
--   **Formalization Note** "Positively oriented" is read as displaced in the positive coordinate directions (Toom's north-east neighbours). The other consistent reading, the near-side edges $(x,\{\nu\}),(x,\{\mu\})$, is its image under the lattice reflection $x\mapsto-x$, which is a symmetry of the code.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 6.2, eq. (169), p. 48 (PDF p. 50); p. 47 (PDF p. 49)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Supplement_toricCode
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

variable (L : ℕ) [NeZero L]

/-- **X-sector 4D Toom predicate.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from
Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03), Definition 6.2, eq. (169),
p. 48 (PDF 50): "If a plaquette i lies in the coordinate plane spanned by (û_μ, û_ν), let e⁺_{i,μ}
and e⁺_{i,ν} be its two positively oriented boundary edges. For s ∈ Σ_X, define the X-sector Toom
predicate by a^{(X)}_i(s) = s_{e⁺_{i,μ}} s_{e⁺_{i,ν}}."

**Formalization Note (Reading T1).** For the plaquette `i = (x, {μ, ν})` the positively oriented
boundary edges are the two boundary edges displaced in the positive coordinate directions (Toom's
"positively-oriented neighbors", p. 47): `e⁺_{i,μ} = (x + u_μ, {ν})` and `e⁺_{i,ν} = (x + u_ν, {μ})`.
The formula is `a^{(X)}_i(s) = ∏_{μ ∈ S} s_{(x + u_μ, S ∖ {μ})}` for `i = (x, S)`, `|S| = 2`. The
reading `(x, {ν}), (x, {μ})` is the image of this one under the reflection `x ↦ −x`, a symmetry
of the code. The rule is total on `𝔽₂^{m_X}`; only valid syndromes enter the lift. -/
noncomputable def toomX (s : Fin (Fintype.card (Cell L 1)) → ZMod 2) :
    Fin (toricN' L + 1) → ZMod 2 := fun i =>
  ∏ μ ∈ (encP L i).2.1.attach,
    s ((encE L).symm ((encP L i).1 + unitVec L μ,
      ⟨(encP L i).2.1.erase μ, by rw [Finset.card_erase_of_mem μ.2, (encP L i).2.2]⟩))

/-- **Z-sector 4D Toom predicate** (Definition 6.2: "The Z-sector predicate a^{(Z)}_i is defined by
the same construction on the dual lattice").

**Formalization Note (Reading T1).** The dual of the plaquette `i = (x, S)` spans the complementary
directions `{κ, λ} = {0,1,2,3} ∖ S`; its dual edges are the 3-cubes containing `i`, and the two
displaced in the positive dual directions are `c⁺_{i,κ} = (x, S ∪ {κ})` and `c⁺_{i,λ} = (x, S ∪ {λ})`.
The formula is `a^{(Z)}_i(s) = ∏_{κ ∉ S} s_{(x, S ∪ {κ})}`. -/
noncomputable def toomZ (s : Fin (Fintype.card (Cell L 3)) → ZMod 2) :
    Fin (toricN' L + 1) → ZMod 2 := fun i =>
  ∏ κ ∈ ((encP L i).2.1)ᶜ.attach,
    s ((encC L).symm ((encP L i).1,
      ⟨insert κ.1 (encP L i).2.1, by
        rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp κ.2), (encP L i).2.2]⟩))

end AutoQMem.Lindblad.Supplement


