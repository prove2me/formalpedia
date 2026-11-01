-- Prove2me | Definitions.Def_AccessibleMaps_Composite
-- name    : AccessibleMaps_Composite
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:21.818009+00:00
-- url     : https://prove2.me/theorems/87130df0-4cb1-4028-8183-06284ae68bb1
-- title:
--   The composite Hilbert space $\mathbb C^{a}\otimes\mathcal H$ as $a$ blocks in $\mathcal H$
-- statement:
--   Let $a$ be a finite index set, the labels of an orthonormal basis $\{|i\rangle\}$ of the system space $\mathcal H_A=\mathbb C^{a}$, and let $\mathcal H$ be a complex Hilbert space (the environment, or ancilla, $B$). The **composite space** of system and environment is
--   $$
--   \mathcal H_A\otimes\mathcal H \;\cong\; \bigoplus_{i\in a}\mathcal H ,
--   $$
--   the space of tuples $(x_i)_{i\in a}$ of vectors of $\mathcal H$ with the inner product $\sum_i\langle x_i,y_i\rangle$. The vector $|i\rangle\otimes\psi$ is the tuple with $\psi$ in slot $i$ and $0$ elsewhere.
--
--   All states and operators of the bipartite system $AB$ in this mission live on this space.
--
--   **Formalization Note** The space is `PiLp 2 (fun _ : a => H)`, the $\ell^2$ direct sum of $|a|$ copies of $\mathcal H$. It is isometric to $\mathbb C^{a}\otimes\mathcal H$ for every Hilbert space $\mathcal H$, including infinite-dimensional ones, so no completed tensor product is needed.
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, §I, p.1 (combined state τ_AB of system A and environment B)

import Mathlib

namespace AccessibleMaps

/-- The composite Hilbert space `ℂ^a ⊗ H` of the system `A` (a finite-dimensional space with
orthonormal basis indexed by `a`) and the ancilla `H`, as vectors of `a` blocks in `H`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, §I, p.1 (PDF p.1), "the combined state of
a system (A) and its environment (B)".

**Formalization Note.** `PiLp 2 (fun _ : a => H)` is the `ℓ²` direct sum of `card a` copies of `H`,
which is isometric to `ℂ^a ⊗ H` for every Hilbert space `H`, including infinite-dimensional ones,
with no completed tensor product needed. -/
abbrev Composite (a H : Type*) : Type _ := PiLp 2 (fun _ : a => H)

end AccessibleMaps


