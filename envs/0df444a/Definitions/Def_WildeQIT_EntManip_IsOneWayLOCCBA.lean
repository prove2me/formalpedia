-- Prove2me | Definitions.Def_WildeQIT_EntManip_IsOneWayLOCCBA
-- name    : WildeQIT_EntManip_IsOneWayLOCCBA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:19.786442+00:00
-- url     : https://prove2.me/theorems/3a9b8f09-ffd4-4127-a7d4-d156662cfd73
-- title:
--   One-way LOCC round from Bob to Alice, $\sum_x \mathcal G^x_A\otimes\mathcal F^x_B$
-- statement:
--   Let $\mathcal H_A,\mathcal H_B,\mathcal H_{A'},\mathcal H_{B'}$ be finite-dimensional Hilbert spaces. A map $\Lambda:\mathcal L(\mathcal H_A\otimes\mathcal H_B)\to\mathcal L(\mathcal H_{A'}\otimes\mathcal H_{B'})$ is a **one-way LOCC round from Bob to Alice** when Bob performs a quantum instrument, forwards the classical outcome $x$ to Alice, and Alice performs a quantum channel conditioned on $x$:
--
--   $$
--   \Lambda = \sum_x \mathcal G^x_{A\to A'}\otimes\mathcal F^x_{B\to B'},
--   $$
--
--   with $\{\mathcal F^x_B\}$ completely positive maps such that $\sum_x\mathcal F^x_B$ is a quantum channel and $\{\mathcal G^x_A\}$ quantum channels; this is (19.21) with the labels $A$ and $B$ switched.
--
--   **Formalization Note** As for the Alice-to-Bob round: Bob's instrument by Kraus operators $F_{x,k}:\mathcal H_B\to\mathcal H_{B'}$ with $\sum_{x,k}F_{x,k}^\dagger F_{x,k}=I_B$, Alice's channels as published `WildeQIT.QChannel`s, Kronecker product with Alice's factor first.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §19.2, item 2, p. 538

import Mathlib
import Definitions.Def_WildeQIT_QChannel

open scoped Kronecker Matrix

namespace WildeQIT.EntManip

/-- **One-way LOCC round from Bob to Alice** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, §19.2, item 2, p. 538): "The situation is reversed, with Bob performing the
initial instrument, who forwards the classical data to Alice, who then performs a quantum channel
conditioned on the classical data", i.e. a channel `∑_x G^x_A ⊗ F^x_B` of the form (19.21) with
the `A` and `B` labels switched: `{F^x_B}` completely positive with `∑_x F^x_B` a channel, and
`{G^x_A}` quantum channels.

`Λ : L(H_A ⊗ H_B) → L(H_{A'} ⊗ H_{B'})` is such a round when there are a finite outcome set `X`,
Kraus operators `F x k : H_B → H_{B'}` with `∑_{x,k} F_{x,k}† F_{x,k} = I_B`, and channels
`G x : H_A → H_{A'}` (published `WildeQIT.QChannel`), with
`Λ(ρ) = ∑_x (G^x_A ⊗ F^x_B)(ρ)` for every operator `ρ`.

**Formalization Note** As for `IsOneWayLOCCAB`: finite dimensions, Kronecker product on
`a' × b'` (Alice's factor first), Kraus form of the completely positive maps (Theorem 4.4.1). -/
def IsOneWayLOCCBA {a b a' b' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype a'] [Fintype b']
    (Λ : Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (κ : Type) (_ : Fintype κ)
    (F : X → κ → Matrix b' b ℂ) (G : X → WildeQIT.QChannel a a'),
    (∑ x, ∑ k, (F x k)ᴴ * F x k = 1) ∧
    ∀ ρ : Matrix (a × b) (a × b) ℂ,
      Λ ρ = ∑ x, ∑ k, ∑ l, ((G x).K l ⊗ₖ F x k) * ρ * ((G x).K l ⊗ₖ F x k)ᴴ

end WildeQIT.EntManip


