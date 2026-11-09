-- Prove2me | Definitions.Def_GroupIsoPoly_TensorIso
-- name    : GroupIsoPoly_TensorIso
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:22.631765+00:00
-- url     : https://prove2.me/theorems/bb6f7fdd-6845-4439-8191-5fa1d0bf489a
-- title:
--   3-way arrays and isomorphism of 3-tensors
-- statement:
--   An **$\ell\times m\times n$ 3-way array** over a field $\mathbb F$ is $A=(a_{i,j,k})$ with $i\in[\ell]$, $j\in[m]$, $k\in[n]$. Two arrays $A,B$ are **isomorphic as 3-tensors** if there are $R=(r_{i,i'})\in\mathrm{GL}(\ell,\mathbb F)$, $S=(s_{j,j'})\in\mathrm{GL}(m,\mathbb F)$ and $T=(t_{k,k'})\in\mathrm{GL}(n,\mathbb F)$ with
--   $$
--   a_{i,j,k}=\sum_{i',j',k'}r_{i,i'}\,s_{j,j'}\,t_{k,k'}\,b_{i',j',k'}\qquad\text{for all }i,j,k,
--   $$
--   that is, $A=(R\otimes S\otimes T)B$. This is Definition 1 of the paper (restated on p.71 as $(g_1\otimes g_2\otimes g_3)T=T'$).
--
--   **Formalization Note** Indices run over `Fin ℓ`, `Fin m`, `Fin n`; `tensorAct R S T B` is $(R\otimes S\otimes T)B$.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 1, p.1 (PDF p.5); Definition 1 (restated), p.71 (PDF p.75)

import Mathlib

set_option autoImplicit false

namespace GroupIsoPoly

/-- `ℓ × m × n` 3-way arrays over `K`: `A i j k = a_{i,j,k}`. -/
abbrev Array3 (K : Type*) (l m n : ℕ) : Type _ := Fin l → Fin m → Fin n → K

/-- The action `(R, S, T) · B` of three matrices on a 3-way array:
`((R, S, T) · B)_{i,j,k} = Σ_{i',j',k'} r_{i,i'} s_{j,j'} t_{k,k'} b_{i',j',k'}`, i.e. the coordinates of
`(R ⊗ S ⊗ T) B`. -/
def tensorAct {K : Type*} [CommRing K] {l m n : ℕ} (R : Matrix (Fin l) (Fin l) K)
    (S : Matrix (Fin m) (Fin m) K) (T : Matrix (Fin n) (Fin n) K) (B : Array3 K l m n) :
    Array3 K l m n :=
  fun i j k => ∑ i', ∑ j', ∑ k', R i i' * S j j' * T k k' * B i' j' k'

/-- **Isomorphism of 3-tensors.**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 1, p.1 (PDF p.5): "Let A = (a_{i,j,k}),
B = (b_{i,j,k}), where i ∈ [ℓ], j ∈ [m], k ∈ [n], a_{i,j,k}, b_{i,j,k} ∈ F, be 3-way arrays over F. We
say that A and B are isomorphic as 3-tensors, if there exist R = (r_{i,i′}) ∈ GL(ℓ, F),
S = (s_{j,j′}) ∈ GL(m, F), and T = (t_{k,k′}) ∈ GL(n, F) such that for any i, j, k,
a_{i,j,k} = Σ_{i′,j′,k′} r_{i,i′} s_{j,j′} t_{k,k′} b_{i′,j′,k′}." Restated as Definition 1, p.71 (PDF p.75):
"(g1 ⊗ g2 ⊗ g3)T = T′".

**Formalization Note.** Indices run over `Fin ℓ`, `Fin m`, `Fin n`; `GL (Fin ℓ) K` is Mathlib's group
of invertible matrices. -/
def TensorIso {K : Type*} [CommRing K] {l m n : ℕ} (A B : Array3 K l m n) : Prop :=
  ∃ (R : GL (Fin l) K) (S : GL (Fin m) K) (T : GL (Fin n) K),
    A = tensorAct (R : Matrix (Fin l) (Fin l) K) (S : Matrix (Fin m) (Fin m) K)
      (T : Matrix (Fin n) (Fin n) K) B

end GroupIsoPoly


