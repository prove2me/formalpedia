-- Prove2me | Definitions.Def_HoneycombCodes_IsMPSetup
-- name    : HoneycombCodes_IsMPSetup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:39.296256+00:00
-- url     : https://prove2.me/theorems/6e2a6b8e-e3d8-4490-a0fe-28d9831503d9
-- title:
--   Standing data of the finite moving-projection theorem (§3)
-- statement:
--   The setting of Theorem 3.1:
--
--   1. a finite group $G$ acting transitively on a finite set $X$, a base point $o$ and its stabilizer $H$;
--   2. a unitary $G$-representation $W$ and an equivariant map $x\mapsto\ell_x\in W$ with $\|\ell_x\|=1$ and real matrix coefficients $t(x,y)=\langle\ell_x,\ell_y\rangle$;
--   3. an irreducible unitary $H$-representation $E$ of dimension $d_E$;
--   4. a finite family $\Omega$ of pairwise inequivalent irreducible unitary $G$-representations $V_\omega$ with $\dim\mathrm{Hom}_H(E,\mathrm{Res}^G_H V_\omega)=1$, and isometric $H$-equivariant embeddings $\phi_{\omega,o}:E\to V_\omega$;
--   5. on every retained edge $\omega\to\omega'$ an isometric $G$-intertwiner $C_{\omega,\omega'}:V_{\omega'}\to W\otimes V_\omega$ and a scalar $c_{\omega,\omega'}\ge 0$ with
--
--   $$
--   C^*_{\omega,\omega'}(\ell_x\otimes\phi_{\omega,x}u)=c_{\omega,\omega'}\,\phi_{\omega',x}u,\qquad \phi_{\omega,x}[g,u]=g\,\phi_{\omega,o}u ;
--   $$
--
--   6. directed coefficients $p_{\omega,\omega'}=c^2_{\omega,\omega'}$ on retained edges and $0$ otherwise, with the balance identity $D_\omega p_{\omega,\omega'}=D_{\omega'}p_{\omega',\omega}$ on retained edges, $D_\omega=\dim V_\omega$.
--
--   **Formalization Note** Representations are Mathlib `Representation ℂ G V` on finite-dimensional complex inner-product spaces; unitarity is invariance of the inner product; $W\otimes V_\omega$ carries Mathlib's tensor inner product. The contraction identity is stated for every $g\in G$ (with $x=go$) in the adjoint-free form $\langle C v',\ell_{go}\otimes g\phi_{\omega,o}u\rangle=c\,\langle v',g\phi_{\omega',o}u\rangle$. Multiplicity one is: a nonzero $H$-intertwiner $E\to V_\omega$ exists and every $H$-intertwiner is a complex multiple of it. The retained edges are an arbitrary relation on $\Omega$; the paper retains exactly the pairs with $V_{\omega'}\subseteq W\otimes V_\omega$.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §3, pp.13–14 (PDF 15–16), eq. (15)

import Mathlib

set_option autoImplicit false

open scoped InnerProductSpace TensorProduct

namespace HoneycombCodes

open Classical in
/-- The **directed coefficients** `p_{ω,ω′} = c²_{ω,ω′}` on retained edges and `p_{ω,ω′} = 0`
on missing edges, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*,
arXiv:2608.20287v2 (sha256 f4b07e31…cd51), §3, p.14 (PDF 16). -/
noncomputable def pcoef {Ω : Type*} (retained : Ω → Ω → Prop) (c : Ω → Ω → ℝ) (ω ω' : Ω) : ℝ :=
  if retained ω ω' then c ω ω' ^ 2 else 0

/-- The **standing data of §3** (the finite moving-projection setting), arXiv:2608.20287v2,
§3, pp.13–14 (PDF 15–16):

* a finite group `G` acting transitively on a finite set `X`, a base point `o`, `H = Stab_G(o)`;
* a unitary `G`-representation `ρW` on `W` and an equivariant map `x ↦ ℓ_x ∈ W` with `‖ℓ_x‖ = 1`
  whose matrix coefficients `t(x, y) = ⟨ℓ_x, ℓ_y⟩` are real;
* an irreducible unitary `H`-representation `ρE` on `E`;
* a finite family `Ω` of pairwise inequivalent irreducible unitary `G`-representations
  `ρ ω` on `V ω` with `dim Hom_H(E, Res^G_H V_ω) = 1`;
* isometric `H`-equivariant embeddings `ϕ ω = ϕ_{ω,o} : E → V_ω`;
* for every retained edge `ω → ω′`, an isometric `G`-intertwiner `C ω ω′ : V_{ω′} → W ⊗ V_ω` and a
  scalar `c ω ω′ ≥ 0` satisfying (15), `C*_{ω,ω′}(ℓ_x ⊗ ϕ_{ω,x}u) = c_{ω,ω′} ϕ_{ω′,x}u`;
* the balance identity `D_ω p_{ω,ω′} = D_{ω′} p_{ω′,ω}` on every retained edge, `D_ω = dim V_ω`.

**Formalization Note.**
* Representations are Mathlib `Representation ℂ G V` on finite-dimensional complex inner-product
  spaces; unitarity is `⟪ρ g v, ρ g v'⟫ = ⟪v, v'⟫`. `W ⊗ V_ω` carries Mathlib's tensor-product
  inner product and the representation `ρW.tprod (ρ ω)`.
* The bundle maps are `ϕ_{ω,x}[g, u] = g ϕ_{ω,o} u` for `x = g o`; (15) is stated for every
  `g ∈ G` and `u ∈ E` in adjoint-free form: `⟪C v′, ℓ_{g o} ⊗ g ϕ_{ω,o} u⟫ = c ⟪v′, g ϕ_{ω′,o} u⟫`
  for all `v′ ∈ V_{ω′}`, which is equivalent to `C*(ℓ_x ⊗ ϕ_{ω,x}u) = c ϕ_{ω′,x}u`.
* `dim Hom_H(E, Res V_ω) = 1` is: a nonzero `H`-intertwiner `E → V_ω` exists and every
  `H`-intertwiner is a complex multiple of it.
* `retained ω ω′` marks the retained edges; on a non-retained pair no condition is imposed and
  `p_{ω,ω′} = 0` (`pcoef`). The paper retains exactly the edges with `V_{ω′} ⊆ W ⊗ V_ω`; any
  family of retained edges for which the intertwiners exist is admitted. -/
structure IsMPSetup
    {G : Type*} [Group G] [Fintype G] {X : Type*} [Fintype X] [MulAction G X] (o : X)
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ρW : Representation ℂ G W) (ℓ : X → W)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρE : Representation ℂ (MulAction.stabilizer G o) E)
    {Ω : Type*} [Fintype Ω] (V : Ω → Type*) [∀ ω, NormedAddCommGroup (V ω)]
    [∀ ω, InnerProductSpace ℂ (V ω)] [∀ ω, FiniteDimensional ℂ (V ω)]
    (ρ : ∀ ω, Representation ℂ G (V ω)) (ϕ : ∀ ω, E →ₗ[ℂ] V ω)
    (retained : Ω → Ω → Prop) (C : ∀ ω ω', V ω' →ₗ[ℂ] (W ⊗[ℂ] V ω)) (c : Ω → Ω → ℝ) : Prop where
  transitive : MulAction.IsPretransitive G X
  unitaryW : ∀ (g : G) (v v' : W), ⟪ρW g v, ρW g v'⟫_ℂ = ⟪v, v'⟫_ℂ
  equivariant : ∀ (g : G) (x : X), ℓ (g • x) = ρW g (ℓ x)
  norm_one : ∀ x : X, ‖ℓ x‖ = 1
  real_coeff : ∀ x y : X, (⟪ℓ x, ℓ y⟫_ℂ).im = 0
  unitaryE : ∀ (h : MulAction.stabilizer G o) (u u' : E), ⟪ρE h u, ρE h u'⟫_ℂ = ⟪u, u'⟫_ℂ
  irredE : ρE.IsIrreducible
  unitaryV : ∀ (ω : Ω) (g : G) (v v' : V ω), ⟪ρ ω g v, ρ ω g v'⟫_ℂ = ⟪v, v'⟫_ℂ
  irredV : ∀ ω : Ω, (ρ ω).IsIrreducible
  inequiv : ∀ ω ω' : Ω, ω ≠ ω' → IsEmpty ((ρ ω).Equiv (ρ ω'))
  mult_one : ∀ ω : Ω, ∃ f₀ : E →ₗ[ℂ] V ω, f₀ ≠ 0 ∧
    (∀ (h : MulAction.stabilizer G o) (u : E), f₀ (ρE h u) = ρ ω (h : G) (f₀ u)) ∧
    ∀ f : E →ₗ[ℂ] V ω,
      (∀ (h : MulAction.stabilizer G o) (u : E), f (ρE h u) = ρ ω (h : G) (f u)) →
      ∃ a : ℂ, f = a • f₀
  phi_isometry : ∀ (ω : Ω) (u : E), ‖ϕ ω u‖ = ‖u‖
  phi_equivariant : ∀ (ω : Ω) (h : MulAction.stabilizer G o) (u : E),
    ϕ ω (ρE h u) = ρ ω (h : G) (ϕ ω u)
  C_isometry : ∀ ω ω' : Ω, retained ω ω' → ∀ v : V ω', ‖C ω ω' v‖ = ‖v‖
  C_intertwines : ∀ ω ω' : Ω, retained ω ω' → ∀ (g : G) (v : V ω'),
    C ω ω' (ρ ω' g v) = (ρW.tprod (ρ ω)) g (C ω ω' v)
  c_nonneg : ∀ ω ω' : Ω, 0 ≤ c ω ω'
  contraction : ∀ ω ω' : Ω, retained ω ω' → ∀ (g : G) (u : E) (v' : V ω'),
    ⟪C ω ω' v', ℓ (g • o) ⊗ₜ[ℂ] (ρ ω g (ϕ ω u))⟫_ℂ = (c ω ω' : ℂ) * ⟪v', ρ ω' g (ϕ ω' u)⟫_ℂ
  balance : ∀ ω ω' : Ω, retained ω ω' →
    (Module.finrank ℂ (V ω) : ℝ) * pcoef retained c ω ω' =
      (Module.finrank ℂ (V ω') : ℝ) * pcoef retained c ω' ω

end HoneycombCodes


