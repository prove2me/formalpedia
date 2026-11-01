-- Prove2me | Definitions.Def_WildeQIT_EntManip_IsOneWayLOCCAB
-- name    : WildeQIT_EntManip_IsOneWayLOCCAB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:15.239983+00:00
-- url     : https://prove2.me/theorems/df064056-16f2-4d71-a192-21f97a40ffef
-- title:
--   One-way LOCC round from Alice to Bob, $\sum_x \mathcal F^x_A\otimes\mathcal G^x_B$
-- statement:
--   Let $\mathcal H_A,\mathcal H_B,\mathcal H_{A'},\mathcal H_{B'}$ be finite-dimensional Hilbert spaces. A map $\Lambda:\mathcal L(\mathcal H_A\otimes\mathcal H_B)\to\mathcal L(\mathcal H_{A'}\otimes\mathcal H_{B'})$ is a **one-way LOCC round from Alice to Bob** when Alice performs a quantum instrument, forwards its classical outcome $x$ to Bob, and Bob performs a quantum channel conditioned on $x$; that is,
--
--   $$
--   \Lambda = \sum_x \mathcal F^x_{A\to A'}\otimes\mathcal G^x_{B\to B'},
--   $$
--
--   where $x$ ranges over a finite set, $\{\mathcal F^x_A\}$ is a collection of completely positive maps such that $\sum_x\mathcal F^x_A$ is a quantum channel, and $\{\mathcal G^x_B\}$ is a collection of quantum channels.
--
--   This is the first of the two building blocks of LOCC channels in §19.2.
--
--   **Formalization Note** Each $\mathcal F^x_A$ is given by Kraus operators $F_{x,k}:\mathcal H_A\to\mathcal H_{A'}$, $\mathcal F^x_A(Y)=\sum_kF_{x,k}YF_{x,k}^\dagger$, and trace preservation of $\sum_x\mathcal F^x_A$ is $\sum_{x,k}F_{x,k}^\dagger F_{x,k}=I_A$; every completely positive map in finite dimensions has a finite Kraus decomposition (Theorem 4.4.1), and a common Kraus index set can be used by padding with zero operators. Each $\mathcal G^x_B$ is a published `WildeQIT.QChannel` (Kraus form). The tensor product of operators is the Kronecker product on `a' × b'`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §19.2, item 1, (19.21), p. 538

import Mathlib
import Definitions.Def_WildeQIT_QChannel

open scoped Kronecker Matrix

namespace WildeQIT.EntManip

/-- **One-way LOCC round from Alice to Bob** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, §19.2, item 1, p. 538): Alice performs a quantum instrument, forwards the
classical outcome `x` to Bob, who performs a quantum channel conditioned on `x`; the overall
channel is `∑_x F^x_A ⊗ G^x_B` (19.21), where `{F^x_A}` is a collection of completely positive
maps such that `∑_x F^x_A` is a quantum channel and `{G^x_B}` is a collection of quantum channels.

The map `Λ : L(H_A ⊗ H_B) → L(H_{A'} ⊗ H_{B'})` is such a round when there are a finite outcome
set `X`, Kraus operators `F x k : H_A → H_{A'}` of the completely positive maps `F^x_A`
(`F^x_A(Y) = ∑_k F_{x,k} Y F_{x,k}†`) with `∑_{x,k} F_{x,k}† F_{x,k} = I_A` (so `∑_x F^x_A` is
trace preserving), and channels `G x : H_B → H_{B'}` (published `WildeQIT.QChannel`, Kraus form),
with `Λ(ρ) = ∑_x (F^x_A ⊗ G^x_B)(ρ)` for every operator `ρ`.

**Formalization Note** Finite dimensions: operators are complex matrices over finite index types;
`⊗` of operators is the Kronecker product on `a' × b'`. A completely positive map between
finite-dimensional spaces has a finite Kraus decomposition (Theorem 4.4.1, p. 151), so writing
`F^x_A` by Kraus operators is no restriction; one Kraus index type `κ` serves every `x` (pad with
zero operators). -/
def IsOneWayLOCCAB {a b a' b' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype a'] [Fintype b']
    (Λ : Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (κ : Type) (_ : Fintype κ)
    (F : X → κ → Matrix a' a ℂ) (G : X → WildeQIT.QChannel b b'),
    (∑ x, ∑ k, (F x k)ᴴ * F x k = 1) ∧
    ∀ ρ : Matrix (a × b) (a × b) ℂ,
      Λ ρ = ∑ x, ∑ k, ∑ l, (F x k ⊗ₖ (G x).K l) * ρ * (F x k ⊗ₖ (G x).K l)ᴴ

end WildeQIT.EntManip


