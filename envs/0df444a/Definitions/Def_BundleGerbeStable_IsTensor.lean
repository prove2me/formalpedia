-- Prove2me | Definitions.Def_BundleGerbeStable_IsTensor
-- name    : BundleGerbeStable_IsTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:43.750913+00:00
-- url     : https://prove2.me/theorems/07698508-c489-4f38-a118-9a2945fcce6c
-- title:
--   The product $(P\otimes Q, Y\times_\pi Z)$ of bundle gerbes
-- statement:
--   The relation **`IsTensor G P Q`** says that $G$, a bundle gerbe over $Y\times_\pi Z$, is the product $P\otimes Q$ of $(P,Y)$ and $(Q,Z)$. It asks for a smooth map $t$, defined on pairs with $p$ over $(y_1,y_2)$ and $q$ over $(z_1,z_2)$ where $(y_i,z_i)\in Y\times_\pi Z$, with values in the fibre of $G$ over $((y_1,z_1),(y_2,z_2))$, such that
--   $$t(zp,q)=z\,t(p,q)=t(p,zq),\qquad t(pp',qq')=t(p,q)\,t(p',q').$$
--
--   This is the product used in Theorem 2.2, Definition 3.1 and Proposition 3.2.
--
--   **Formalization Note.** By the universal property of the contracted product $t$ is a map of principal $\mathbb C^\times$ spaces out of $P_{(y_1,y_2)}\otimes Q_{(z_1,z_2)}$, automatically bijective, and a smooth equivariant map of locally trivial bundles over one base is a diffeomorphism. So $G$ is determined up to isomorphism; the milestone `product_exists` states that $G$ exists.
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.3 (product of bundle gerbes)

import Mathlib
import Definitions.Def_BundleGerbeStable_BundleGerbe

open Diffeology

namespace BundleGerbeStable

universe u

variable {M : Type u} [TopologicalSpace M] [DiffeologicalSpace M] {S T : LocallySplit M}

/-- `G` is the **product** `(P ⊗ Q, Y ×_π Z)` of the bundle gerbes `(P, Y)` and `(Q, Z)` (Murray,
Stevenson, *Bundle gerbes: stable isomorphism and local theory*, arXiv:math/9908135v1, §2, p.3): there is
a smooth map `t`, defined on pairs `(p, q)` with `p` over `(y₁, y₂)`, `q` over `(z₁, z₂)` and
`(yᵢ, zᵢ) ∈ Y ×_π Z`, into the fibre of `G` over `((y₁, z₁), (y₂, z₂))`, which is balanced and
equivariant in each argument and sends the products of `P` and `Q` to the product of `G`.

**Formalization Note.** By the universal property of the contracted product, such a `t` is a map of
ℂ× spaces `P_(y₁,y₂) ⊗ Q_(z₁,z₂) → G_((y₁,z₁),(y₂,z₂))`, which is automatically bijective, and a
smooth equivariant map between locally trivial bundles over the same base is a diffeomorphism. So `G`
is determined up to isomorphism. `π y₁ = π y₂` and `π z₁ = π z₂` hold on `Y^[2]`, `Z^[2]`, so the single
condition `π y₁ = π z₁` is the condition on both pairs. `product_exists` (§2, p.3) is the existence
of such a `G`, and it is what rules out a vacuous definition. -/
def IsTensor (G : BundleGerbe (fibreProd S T)) (P : BundleGerbe S) (Q : BundleGerbe T) : Prop :=
  ∃ t : (p : P.bdl.P) → (q : Q.bdl.P) → S.π (P.bdl.src p) = T.π (Q.bdl.src q) → G.bdl.P,
    DSmooth (fun r : {r : P.bdl.P × Q.bdl.P // S.π (P.bdl.src r.1) = T.π (Q.bdl.src r.2)} ↦
      t r.1.1 r.1.2 r.2) ∧
    (∀ p q h, ((G.bdl.src (t p q h) : FibreProd S T)).1 = (P.bdl.src p, Q.bdl.src q)) ∧
    (∀ p q h, ((G.bdl.tgt (t p q h) : FibreProd S T)).1 = (P.bdl.tgt p, Q.bdl.tgt q)) ∧
    (∀ (z : ℂˣ) p q h h', t (z • p) q h' = z • t p q h) ∧
    (∀ (z : ℂˣ) p q h h', t p (z • q) h' = z • t p q h) ∧
    ∀ p p' q q' hp hq h h₁ h₂ hm,
      t (P.mul p p' hp) (Q.mul q q' hq) h = G.mul (t p q h₁) (t p' q' h₂) hm

end BundleGerbeStable


