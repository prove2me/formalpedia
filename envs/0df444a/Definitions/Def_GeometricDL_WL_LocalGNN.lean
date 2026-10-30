-- Prove2me | Definitions.Def_GeometricDL_WL_LocalGNN
-- name    : GeometricDL_WL_LocalGNN
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:21:09.720681+00:00
-- url     : https://prove2.me/theorems/a8a995f5-c3d4-48a8-ac77-3a3f2aaba64f
-- title:
--   A stack of local GNN layers
-- statement:
--   A **local GNN** on node features of type $F$ consists of
--
--   1. a hidden type $H_\ell$ for every layer index $\ell\ge 0$;
--   2. an encoder $\mathrm{enc}:F\to H_0$;
--   3. for every $\ell$, a layer map $\Phi_\ell:H_\ell\times\mathrm{Multiset}(H_\ell\times\mathbb N)\to H_{\ell+1}$, which takes a node's current state and the multiset of pairs (neighbour state, neighbour degree).
--
--   Each layer is the shared local function $\varphi(x_u,X_{N_u})$ of eq. (13), with the degree of every neighbour attached to its state. Every layer of the three flavours (33)–(35) is of this form, so every stack of such layers (possibly mixing flavours and changing from layer to layer) is a local GNN.
--
--   **Formalization Note** Layers are 0-based. Neighbour degrees are part of the input because the convolutional coefficients the paper cites (e.g. $1/\sqrt{d_ud_v}$) depend on them.
-- source:
--   Bronstein, Bruna, Cohen & Veličković, Geometric Deep Learning, arXiv:2104.13478v2, §5.3, printed p. 78 (PDF p. 82) ("shared permutation invariant functions φ(x_u, X_{N_u}) over local neighbourhoods", "GNN layer"); eq. (13), printed p. 34 (PDF p. 38)

import Mathlib

universe u v

namespace GeometricDL.WL

/-- **A stack of local GNN layers.**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning*, arXiv:2104.13478v2, §5.3,
printed p. 78 (PDF p. 82): "We will study GNN architectures that are permutation equivariant
functions F(X, A) constructed by applying shared permutation invariant functions φ(x_u, X_{N_u})
over local neighbourhoods. … the overall computation of such F as a “GNN layer”."; eq. (13),
printed p. 34 (PDF p. 38).

A `LocalGNN F` on node features of type `F` consists of
1. a hidden type `H ℓ` for every layer index `ℓ`,
2. an encoder `enc : F → H 0` of the input features,
3. for every `ℓ`, a layer map `layer ℓ : H ℓ → Multiset (H ℓ × ℕ) → H (ℓ + 1)`, which takes a
   node's current state and the multiset of (neighbour state, neighbour degree) pairs.

**Formalization Note.** A layer is the shared local function `φ(x_u, X_{N_u})` of (13), with each
neighbour's degree `|N_v|` attached to its state; every layer of the three flavours (33)–(35) is
of this form (milestone `flavours_are_local`). Layers may differ from layer to layer and the
stack may mix flavours. Layers are 0-based. -/
structure LocalGNN (F : Type u) : Type (max u (v + 1)) where
  /-- hidden type after `ℓ` layers -/
  H : ℕ → Type v
  /-- encoder of the input features -/
  enc : F → H 0
  /-- layer `ℓ`: own state, multiset of (neighbour state, neighbour degree) ↦ new state -/
  layer : (ℓ : ℕ) → H ℓ → Multiset (H ℓ × ℕ) → H (ℓ + 1)

end GeometricDL.WL


