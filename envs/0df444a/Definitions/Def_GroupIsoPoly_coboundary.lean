-- Prove2me | Definitions.Def_GroupIsoPoly_coboundary
-- name    : GroupIsoPoly_coboundary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:20.335515+00:00
-- url     : https://prove2.me/theorems/63ae5886-292c-4dac-996a-9dcbd89ef2e7
-- title:
--   Cochain differentials and the induced map $T_{\alpha,\beta}$ on cochains
-- statement:
--   For an action $\theta$ of $Q$ on $V$, a $j$-cochain is a map $f:Q^j\to V$ and its **differential** is the $(j+1)$-cochain
--   $$
--   (df)(g_0,\dots,g_j)=\theta(g_0)f(g_1,\dots,g_j)+\sum_{i=0}^{j-1}(-1)^{i+1}f(g_0,\dots,g_ig_{i+1},\dots,g_j)+(-1)^{j+1}f(g_0,\dots,g_{j-1}).
--   $$
--   In degree 1, $(db)(q,r)=\theta(q)b(r)-b(qr)+b(q)$. For a linear automorphism $\alpha$ of $V$ and an automorphism $\beta$ of $Q$, the **induced map on cochains** is
--   $$
--   (T_{\alpha,\beta}f)(q_1,\dots,q_j)=\alpha\, f(\beta^{-1}q_1,\dots,\beta^{-1}q_j).
--   $$
--   These are the objects of the extension-isomorphism criterion (§9.2.2).
--
--   **Formalization Note** `coboundary θ j f` is Mathlib's inhomogeneous formula (`Fin.contractNth` for the faces); all cochains are allowed, which computes the same cohomology as the paper's normalised subcomplex.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), §9.2.2, p.95 (PDF p.99)

import Mathlib

set_option autoImplicit false

namespace GroupIsoPoly

/-- **The inhomogeneous cochain differential** `d : C^j(Q, V) → C^{j+1}(Q, V)` for an action `θ`:
`(df)(g₀, …, g_j) = θ(g₀) f(g₁, …, g_j) + Σ_{i=0}^{j} (−1)^{i+1} f(…)` where the `i`-th term
multiplies `g_i g_{i+1}` for `i < j` and drops `g_j` for `i = j`.

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), §9.2.2, p.95 (PDF p.99): "Its induced map on cochains
… commutes with the differentials", with the cochain conventions of Subsection 3.6.

In degree 1 this is `(db)(q, r) = θ(q) b(r) − b(qr) + b(q)`.

**Formalization Note.** A `j`-cochain is a function `(Fin j → Q) → V`; the `i`-th face uses Mathlib's
`Fin.contractNth`, which is the formula of Mathlib's `groupCohomology.inhomogeneousCochains.d`. -/
def coboundary {k V Q : Type*} [CommRing k] [AddCommGroup V] [Module k V] [Group Q]
    (θ : Representation k Q V) (j : ℕ) (f : (Fin j → Q) → V) : (Fin (j + 1) → Q) → V :=
  fun g => θ (g 0) (f fun i => g i.succ) +
    ∑ i : Fin (j + 1), ((-1 : k) ^ ((i : ℕ) + 1)) • f (Fin.contractNth i (· * ·) g)

/-- **The induced map on cochains** `T_{α,β}`.

Qiao, Zhang, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), §9.2.2, p.95 (PDF p.99): "Its
induced map on cochains is (T_{α,β}f)(q1, . . . , qj) = αf(β^{−1}q1, . . . , β^{−1}qj)."

For a linear automorphism `α` of `V` and an automorphism `β` of `Q`,
`(T_{α,β} f)(q₁, …, q_j) = α (f (β⁻¹ q₁, …, β⁻¹ q_j))`. -/
def Tmap {k V Q : Type*} [CommRing k] [AddCommGroup V] [Module k V] [Group Q]
    (α : V ≃ₗ[k] V) (β : MulAut Q) (j : ℕ) (f : (Fin j → Q) → V) : (Fin j → Q) → V :=
  fun g => α (f fun i => β.symm (g i))

end GroupIsoPoly


