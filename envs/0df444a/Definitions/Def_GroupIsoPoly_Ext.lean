-- Prove2me | Definitions.Def_GroupIsoPoly_Ext
-- name    : GroupIsoPoly_Ext
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:06.677211+00:00
-- url     : https://prove2.me/theorems/612e7a87-2295-4236-ae0f-2e5011ad3ac8
-- title:
--   Extension coordinates: the group $A\times Q$ with $(u,q)(v,r)=(u+\theta(q)v+f(q,r),qr)$
-- statement:
--   Let $Q$ be a group acting linearly on a module $A$ by $\theta$. A **normalised 2-cocycle** is a map $f:Q\times Q\to A$ with
--   $$
--   \theta(q)f(r,s)-f(qr,s)+f(q,rs)-f(q,r)=0,\qquad f(1,q)=f(q,1)=0 .
--   $$
--   The **extension group** $E(\theta,f)$ is the set $A\times Q$ with multiplication
--   $$
--   (u,q)(v,r)=\big(u+\theta(q)v+f(q,r),\;qr\big),
--   $$
--   identity $(0,1)$ and inverse $(u,q)^{-1}=\big(-\theta(q^{-1})u-f(q^{-1},q),\,q^{-1}\big)$. Every extension of $A$ by $Q$ with action $\theta$ is of this form after choosing a section $s$ with $s(1)=1$ and writing $(u,q)$ for $u\,s(q)$ — the paper's coordinates (9.4).
--
--   **Formalization Note** The group axioms are exactly the cocycle identity and the normalisation; they are proved in the definition module. The mission uses $A=\mathbb F_p^a$.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), §9.2.2, (9.4), p.95 (PDF p.99)

import Mathlib

set_option autoImplicit false

namespace GroupIsoPoly

/-- **A normalised 2-cocycle** `f : Q × Q → A` for an action `θ` of `Q` on `A`: the cocycle identity
`θ(q) f(r, s) − f(qr, s) + f(q, rs) − f(q, r) = 0`, and `f(1, q) = f(q, 1) = 0`. -/
structure NormCocycle {k V Q : Type*} [CommRing k] [AddCommGroup V] [Module k V] [Group Q]
    (θ : Representation k Q V) where
  /-- the cocycle -/
  f : Q → Q → V
  cocycle : ∀ q r s : Q, θ q (f r s) - f (q * r) s + f q (r * s) - f q r = 0
  one_left : ∀ q : Q, f 1 q = 0
  one_right : ∀ q : Q, f q 1 = 0

/-- **The extension group in coordinates** (9.4): the set `A × Q` with
`(u, q)(v, r) = (u + θ(q)v + f(q, r), qr)`.

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), §9.2.2, p.95 (PDF p.99): "For an extension of
A ≅ F_p^a by Q, use a section s : Q → G with s(1) = 1, as in Subsection 3.6. Writing (u, q) for us(q)
gives (u, q)(v, r) = (u + θ(q)v + f(q, r), qr), (9.4) where θ and f are its action and normalised
2-cocycle."

`Ext θ f` is the group on `V × Q` with this multiplication, identity `(0, 1)` and inverse
`(u, q)⁻¹ = (−θ(q⁻¹)u − f(q⁻¹, q), q⁻¹)`.

**Formalization Note.** The module `V`, the ring `k` and the group `Q` are arbitrary here; the
mission uses `V = F_p^a` (`Fin a → ZMod p`). The group axioms are exactly the cocycle identity and the
normalisation. -/
def Ext {k V Q : Type*} [CommRing k] [AddCommGroup V] [Module k V] [Group Q]
    (θ : Representation k Q V) (_f : NormCocycle θ) : Type _ :=
  V × Q

namespace Ext

variable {k V Q : Type*} [CommRing k] [AddCommGroup V] [Module k V] [Group Q]
  {θ : Representation k Q V} {f : NormCocycle θ}

/-- The element `(u, q) = u·s(q)` of the extension. -/
def mk (u : V) (q : Q) : Ext θ f := (u, q)

/-- The kernel coordinate `u` of `(u, q)`. -/
def fst (x : Ext θ f) : V := Prod.fst (α := V) (β := Q) x

/-- The quotient coordinate `q` of `(u, q)`. -/
def snd (x : Ext θ f) : Q := Prod.snd (α := V) (β := Q) x

instance : Mul (Ext θ f) where
  mul x y := mk (fst x + θ (snd x) (fst y) + f.f (snd x) (snd y)) (snd x * snd y)

instance : One (Ext θ f) where
  one := mk 0 1

instance : Inv (Ext θ f) where
  inv x := mk (-(θ (snd x)⁻¹ (fst x)) - f.f (snd x)⁻¹ (snd x)) (snd x)⁻¹

theorem ext_iff' {x y : Ext θ f} : x = y ↔ fst x = fst y ∧ snd x = snd y :=
  Prod.ext_iff

@[simp] theorem fst_mk (u : V) (q : Q) : fst (mk u q : Ext θ f) = u := rfl
@[simp] theorem snd_mk (u : V) (q : Q) : snd (mk u q : Ext θ f) = q := rfl
@[simp] theorem fst_mul (x y : Ext θ f) :
    fst (x * y) = fst x + θ (snd x) (fst y) + f.f (snd x) (snd y) := rfl
@[simp] theorem snd_mul (x y : Ext θ f) : snd (x * y) = snd x * snd y := rfl
@[simp] theorem fst_one : fst (1 : Ext θ f) = 0 := rfl
@[simp] theorem snd_one : snd (1 : Ext θ f) = 1 := rfl
@[simp] theorem fst_inv (x : Ext θ f) :
    fst x⁻¹ = -(θ (snd x)⁻¹ (fst x)) - f.f (snd x)⁻¹ (snd x) := rfl
@[simp] theorem snd_inv (x : Ext θ f) : snd x⁻¹ = (snd x)⁻¹ := rfl

instance instGroup : Group (Ext θ f) :=
  Group.ofLeftAxioms
    (fun x y z => by
      rw [ext_iff']
      refine ⟨?_, by simp [mul_assoc]⟩
      have h := f.cocycle (snd x) (snd y) (snd z)
      simp only [fst_mul, snd_mul, map_mul, Module.End.mul_apply, map_add]
      have e : fst x + θ (snd x) (fst y) + f.f (snd x) (snd y) + θ (snd x) (θ (snd y) (fst z)) +
          f.f (snd x * snd y) (snd z) -
          (fst x + (θ (snd x) (fst y) + θ (snd x) (θ (snd y) (fst z)) +
            θ (snd x) (f.f (snd y) (snd z))) + f.f (snd x) (snd y * snd z)) =
          -(θ (snd x) (f.f (snd y) (snd z)) - f.f (snd x * snd y) (snd z) +
            f.f (snd x) (snd y * snd z) - f.f (snd x) (snd y)) := by abel
      rw [h, neg_zero] at e
      exact sub_eq_zero.mp e)
    (fun x => by
      rw [ext_iff']
      simp [f.one_left])
    (fun x => by
      rw [ext_iff']
      refine ⟨?_, by simp⟩
      simp only [fst_mul, fst_inv, snd_inv, fst_one]
      abel)

end Ext

end GroupIsoPoly


