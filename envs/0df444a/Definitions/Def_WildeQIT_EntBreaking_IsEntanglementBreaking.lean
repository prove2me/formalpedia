-- Prove2me | Definitions.Def_WildeQIT_EntBreaking_IsEntanglementBreaking
-- name    : WildeQIT_EntBreaking_IsEntanglementBreaking
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:28.242211+00:00
-- url     : https://prove2.me/theorems/bb67ba16-1212-4fdf-9c62-92fcaf156252
-- title:
--   Entanglement-breaking map — $\mathrm{id}_R\otimes\mathcal N$ makes every state separable (Definition 4.6.8)
-- statement:
--   Let $\mathcal N:\mathcal L(\mathcal H_A)\to\mathcal L(\mathcal H_B)$ be a linear map. It is **entanglement breaking** when, for a reference system $R$ of every finite size and every density operator $\rho_{RA}$ on $\mathcal H_R\otimes\mathcal H_A$, the output
--
--   $$
--   (\mathrm{id}_R\otimes\mathcal N)(\rho_{RA})
--   $$
--
--   is a separable state of $RB$ in the sense of Definition 4.3.2: a convex combination $\sum_x p_X(x)\,|\psi_x\rangle\langle\psi_x|_R\otimes|\phi_x\rangle\langle\phi_x|_B$ of tensor products of pure states. An **entanglement-breaking channel** (Definition 4.6.8) is a quantum channel with this property.
--
--   Theorem 4.6.1 characterizes these channels as the ones with unit-rank Kraus operators.
--
--   **Formalization Note** The reference is $\mathbb C^r$ for every $r$, as the first tensor factor; $\mathrm{id}_R\otimes\mathcal N$ is the published `QAlgorithms.idTensorSuperop`, which applies $\mathcal N$ blockwise as in (4.180)–(4.184). Separability is the published `WildeQIT.IsSeparable` and density operators are `WildeQIT.IsDensityOperator`. Being a channel is not part of the predicate; the theorems assume it separately.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 4.6.8, p. 166; Definition 4.3.2 (separable state)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_IsSeparable

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §4.6.7,
Definition 4.6.8 (Entanglement-Breaking Channel), p. 166.
-/

namespace WildeQIT.EntBreaking

/-- **Definition 4.6.8 (Entanglement-Breaking Channel)**, Wilde, *From Classical to Quantum
Shannon Theory*, arXiv:1106.1445v8, p. 166: "An entanglement-breaking channel
`N^EB : L(ℋ_A) → L(ℋ_B)` is defined by the property that the channel `id_R ⊗ N^EB_{A→B}` takes any
state `ρ_RA` to a separable state, where `R` is a reference system of arbitrary size."

`IsEntanglementBreaking N` is that property: for every finite reference size `r` and every density
operator `ρ` on `ℋ_R ⊗ ℋ_A` (`R = ℂ^r`, the first factor), the output `(id_R ⊗ N)(ρ)` is separable
in the sense of Definition 4.3.2 (`WildeQIT.IsSeparable`: a convex combination of tensor products
of pure states). An entanglement-breaking channel is a quantum channel with this property.

**Formalization Note.** `id_R ⊗ N` is `QAlgorithms.idTensorSuperop`, which applies `N` to every
block `X^{i,j}_A` of `X_RA = ∑_{i,j} |i⟩⟨j|_R ⊗ X^{i,j}_A`, the book's (4.180)–(4.184). Every
finite-dimensional reference is isomorphic to `ℂ^r`, so `Fin r` covers a reference of arbitrary
size. Being a channel is not part of this predicate; the theorems that use it assume it. -/
def IsEntanglementBreaking {a b : Type} [Fintype a] [Fintype b]
    (N : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ) : Prop :=
  ∀ (r : ℕ) (ρ : Matrix (Fin r × a) (Fin r × a) ℂ), WildeQIT.IsDensityOperator ρ →
    WildeQIT.IsSeparable (QAlgorithms.idTensorSuperop N ρ)

end WildeQIT.EntBreaking


