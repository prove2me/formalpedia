-- Prove2me | Definitions.Def_SymCircMM_indRep
-- name    : SymCircMM_indRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:29:41.418103+00:00
-- url     : https://prove2.me/theorems/afd8d08f-90d1-4b75-8aaf-6261afbc26e9
-- title:
--   Left transversals and the induced representation $\mathrm{Ind}_H^G W$
-- statement:
--   Let $H\le G$ be groups and $(W,\phi)$ a representation of $H$ over $F$. A **left transversal** is a choice $T=\{t_1,\dots,t_m\}$ of one representative of every left coset of $H$, $G=\bigsqcup_r t_rH$, with $t_1=1_G$. The **induced representation** is
--
--   $$\mathrm{Ind}_H^G W=\bigoplus_{r=1}^m t_r\otimes W,$$
--
--   a direct sum of $m=[G:H]$ copies of $W$, where for $g\in G$ and $r\le m$, with the unique $s\le m$ and $h\in H$ such that $gt_r=t_sh$,
--
--   $$g\cdot(t_r\otimes w)=t_s\otimes(h\cdot w).\tag{3}$$
--
--   The map $\iota:W\to\mathrm{Res}_H\,\mathrm{Ind}_H^GW$, $w\mapsto 1\otimes w$, views $W$ inside the representation it induces.
--
--   This is the explicit construction in which the paper states Frobenius reciprocity (Theorem 3.3) over an arbitrary field.
--
--   **Formalization Note** $\bigoplus_r t_r\otimes W$ is the space of functions $f:G/H\to W$, the value $f(q)$ being the component in $t_q\otimes W$, and $t_r\otimes w$ is the function supported at $r$ with value $w$; for finite index this is the direct sum. The action is $(g\cdot f)(s)=h\cdot f(g^{-1}s)$ with $h=t_s^{-1}g\,t_{g^{-1}s}\in H$, which is (3).
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), §3, "Restrictions and Induced Representations", p.9 (PDF p.10), display (3)

import Mathlib

set_option autoImplicit false

namespace SymCircMM

variable {G : Type} [Group G] (H : Subgroup G)

/-- A **left transversal** `T = {t₁, …, t_m}` of `H` in `G` with `t₁ = 1_G` (Dahan, Dawar, Kush, Pago,
*Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), §3, "Restrictions and
Induced Representations", p.9 (PDF p.10)): one representative `t q ∈ q` of every left coset `q = tH`,
the identity representing `H` itself. -/
structure LeftTransversal where
  /-- the representative of each left coset -/
  t : G ⧸ H → G
  mk_t : ∀ q, (QuotientGroup.mk (t q) : G ⧸ H) = q
  t_one : t (QuotientGroup.mk 1) = 1

namespace LeftTransversal

variable {H}

theorem cocycle_mem (T : LeftTransversal H) (g : G) (s : G ⧸ H) :
    (T.t s)⁻¹ * g * T.t (g⁻¹ • s) ∈ H := by
  have h1 : (QuotientGroup.mk (g⁻¹ * T.t s) : G ⧸ H) = QuotientGroup.mk (T.t (g⁻¹ • s)) := by
    rw [T.mk_t]
    conv_rhs => rw [← T.mk_t s]
    rfl
  have := QuotientGroup.eq.1 h1
  simpa [mul_assoc] using this

/-- For `g ∈ G` and the coset `s`, the unique `h ∈ H` with `g t_r = t_s h`, where `t_r` represents
`g⁻¹ s` (display (3), p.9 (PDF p.10)). -/
def cocycle (T : LeftTransversal H) (g : G) (s : G ⧸ H) : H :=
  ⟨(T.t s)⁻¹ * g * T.t (g⁻¹ • s), T.cocycle_mem g s⟩

theorem cocycle_one (T : LeftTransversal H) (s : G ⧸ H) : T.cocycle 1 s = 1 := by
  apply Subtype.ext
  simp [cocycle]

theorem cocycle_mul (T : LeftTransversal H) (g₁ g₂ : G) (s : G ⧸ H) :
    T.cocycle (g₁ * g₂) s = T.cocycle g₁ s * T.cocycle g₂ (g₁⁻¹ • s) := by
  apply Subtype.ext
  simp only [cocycle, Subgroup.coe_mul, mul_inv_rev, mul_smul]
  group

end LeftTransversal

variable {F W : Type} [Field F] [AddCommGroup W] [Module F W]

/-- The **induced representation** `Ind^G_H W = ⨁_{r ≤ m} t_r ⊗ W` (§3, p.9 (PDF p.10)), with
`g · (t_r ⊗ w) := t_s ⊗ (h · w)` where `g t_r = t_s h`, `h ∈ H` (display (3)).

**Formalization Note.** `⨁_r t_r ⊗ W` is the space of functions `f : G ⧸ H → W`, `f(q)` being the
component in the copy `t_q ⊗ W`; `t_r ⊗ w` is `Pi.single r w`. For finite index this is the direct
sum. Then `(g · f)(s) = h · f(g⁻¹ s)` with `h = t_s⁻¹ g t_{g⁻¹ s} ∈ H`, which is (3). -/
def indRep (T : LeftTransversal H) (ρ : Representation F H W) :
    Representation F G (G ⧸ H → W) where
  toFun g :=
    { toFun := fun f s => ρ (T.cocycle g s) (f (g⁻¹ • s))
      map_add' := fun f₁ f₂ => funext fun s => by simp
      map_smul' := fun c f => funext fun s => by simp }
  map_one' := by
    apply LinearMap.ext
    intro f
    funext s
    simp [LeftTransversal.cocycle_one]
  map_mul' g₁ g₂ := by
    apply LinearMap.ext
    intro f
    funext s
    simp [LeftTransversal.cocycle_mul, mul_smul]

/-- The canonical embedding `ι : W → Res_H Ind^G_H W`, `w ↦ 1 ⊗ w = t₁ ⊗ w` (§3, p.9 (PDF p.10)). -/
noncomputable def indIota : W →ₗ[F] (G ⧸ H → W) := by
  classical
  exact LinearMap.single F (fun _ => W) (QuotientGroup.mk 1 : G ⧸ H)

end SymCircMM


