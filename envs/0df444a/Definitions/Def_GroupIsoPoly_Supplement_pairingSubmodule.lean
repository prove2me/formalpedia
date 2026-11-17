-- Prove2me | Definitions.Def_GroupIsoPoly_Supplement_pairingSubmodule
-- name    : GroupIsoPoly_Supplement_pairingSubmodule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:27:30.902269+00:00
-- url     : https://prove2.me/theorems/0dc6a9fc-48d3-476d-8dc7-a7a0438b44a1
-- title:
--   The pairing submodule $J(T)$ of a triple tensor product (Definition 16)
-- statement:
--   Let a group $D$ act on $F$-vector spaces $T_1,T_2,T_3$ by matrices $\rho_1,\rho_2,\rho_3$, and let $T=T_1\otimes_F T_2\otimes_F T_3$ with the diagonal action. For $i\in\{1,2,3\}$ with other indices $j<\ell$, put $B_i=(T_j\otimes_F T_\ell)^D$, the $D$-fixed vectors. For $\eta\in B_i$, $\kappa_{i,\eta}:T_i\to T$ inserts its argument in position $i$ and $\eta$ in the other two positions, in their original order. The **pairing submodule** is
--
--   $$J(T)=\operatorname{im}\Big(J_T:\ \bigoplus_{i=1}^3 T_i\otimes_F B_i\to T,\quad v\otimes\eta\mapsto\kappa_{i,\eta}(v)\Big)=\operatorname{span}_F\{\kappa_{i,\eta}(v): i,\ \eta\in B_i,\ v\in T_i\}.$$
--
--   Theorem 6.3 asserts that the quotient $T/J(T)$ has no fixed vectors and no first cohomology.
--
--   **Formalization Note** Tensors are coordinate arrays $t(a,b,c)$ and $D$ acts by $(g\cdot t)(a,b,c)=\sum\rho_1(g)_{aa'}\rho_2(g)_{bb'}\rho_3(g)_{cc'}t(a',b',c')$; $\kappa_{1,\eta}(v)(a,b,c)=v_a\eta_{bc}$, $\kappa_{2,\eta}(v)(a,b,c)=\eta_{ac}v_b$, $\kappa_{3,\eta}(v)(a,b,c)=\eta_{ab}v_c$. The image of $J_T$ is written as the span of the insertions. The definition is for any field, so it serves over the defining field and over $\mathbb F_p$.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 16, p.48 (PDF p.52)

import Mathlib

set_option autoImplicit false

namespace GroupIsoPoly

namespace Supplement

variable {F : Type*} [Field F] {D : Type*}
variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]

/-- The action `g ↦ ρ₁(g) ⊗ ρ₂(g) ⊗ ρ₃(g)` on `T = F^{ι₁} ⊗ F^{ι₂} ⊗ F^{ι₃}`, written on coordinate
arrays: `(g·t)(a, b, c) = Σ ρ₁(g)_{a a'} ρ₂(g)_{b b'} ρ₃(g)_{c c'} t(a', b', c')`. -/
def tensorAct (ρ₁ : D → Matrix ι₁ ι₁ F) (ρ₂ : D → Matrix ι₂ ι₂ F) (ρ₃ : D → Matrix ι₃ ι₃ F)
    (g : D) (t : ι₁ × ι₂ × ι₃ → F) : ι₁ × ι₂ × ι₃ → F :=
  fun x => ∑ a, ∑ b, ∑ c, ρ₁ g x.1 a * ρ₂ g x.2.1 b * ρ₃ g x.2.2 c * t (a, b, c)

/-- The `D`-fixed vectors `(T_j ⊗ T_ℓ)^D` of a two-fold tensor product, on coordinate arrays. -/
def invPairs {α β : Type*} [Fintype α] [Fintype β] (σ : D → Matrix α α F) (τ : D → Matrix β β F) :
    Set (α × β → F) :=
  {η | ∀ g x, ∑ a, ∑ b, σ g x.1 a * τ g x.2 b * η (a, b) = η x}

/-- **The pairing submodule `J(T)` (Definition 16).**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 16, p.48 (PDF p.52): "For i ∈ {1, 2, 3}, let
j < ℓ be the other two indices and put Bi = (Tj ⊗K Tℓ)^D. For η ∈ Bi, let κi,η : Ti → T be the linear
map that inserts its argument in position i and η in the other two positions. Define the pairing
parameter space and its insertion map by P(T) = ⊕_{i=1}^3 Ti ⊗K Bi, JT : P(T) → T,
JT|Ti⊗KBi (v ⊗ η) = κi,η(v). The pairing submodule is J(T) = im JT."

On coordinate arrays, `κ_{1,η}(v)(a, b, c) = v_a η_{bc}`, `κ_{2,η}(v)(a, b, c) = η_{ac} v_b` and
`κ_{3,η}(v)(a, b, c) = η_{ab} v_c` (the other two positions in their original order), and `J(T)` is
the span of all `κ_{i,η}(v)` with `η ∈ B_i`.

**Formalization Note.** `P(T)` is spanned by the pure tensors `v ⊗ η` with `η ∈ B_i`, and `J_T` is
linear, so `im J_T` is the span of the vectors `κ_{i,η}(v)`; the definition uses this span. It is
stated for any field `F` and any three matrix representations, so that it applies both over the
defining field `K` and over `F_p`. -/
def pairingSubmodule (ρ₁ : D → Matrix ι₁ ι₁ F) (ρ₂ : D → Matrix ι₂ ι₂ F)
    (ρ₃ : D → Matrix ι₃ ι₃ F) : Submodule F (ι₁ × ι₂ × ι₃ → F) :=
  Submodule.span F
    ({t | ∃ (v : ι₁ → F) (η : ι₂ × ι₃ → F), η ∈ invPairs ρ₂ ρ₃ ∧
        t = fun x => v x.1 * η (x.2.1, x.2.2)} ∪
     {t | ∃ (v : ι₂ → F) (η : ι₁ × ι₃ → F), η ∈ invPairs ρ₁ ρ₃ ∧
        t = fun x => η (x.1, x.2.2) * v x.2.1} ∪
     {t | ∃ (v : ι₃ → F) (η : ι₁ × ι₂ → F), η ∈ invPairs ρ₁ ρ₂ ∧
        t = fun x => η (x.1, x.2.1) * v x.2.2})

end Supplement

end GroupIsoPoly


