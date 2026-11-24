-- Prove2me | Definitions.Def_EquivariantHomogeneous_Basic
-- name    : EquivariantHomogeneous_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T05:31:11.279192+00:00
-- url     : https://prove2.me/theorems/a194d6ed-7f0a-4da7-abd2-525c0c565433
-- title:
--   Coset sections, Mackey functions, induced representations and equivariant kernel spaces $\mathcal K_G$, $\mathcal K_C$, $\mathcal K_D$
-- statement:
--   Objects of Sections 2-3 and Appendices A-B of Cohen, Geiger and Weiler (2019).
--
--   1. **Coset sections and the $\mathrm h$-function.** $G$ is a group and $H\le G$ a subgroup; $G/H$ is the space of left cosets $gH$, with the left action $u(gH)=(ug)H$. A section is a map $s:G/H\to G$ with $s(x)\in x$, normalised by $s(H)=e$ (eq. (16)). The $\mathrm h$-function is $\mathrm h(x,g)=s(gx)^{-1}g\,s(x)\in H$ (eq. (19)), and $\mathrm h(g)=\mathrm h(H,g)=s(gH)^{-1}g$ (eq. (25)).
--   2. **Fields.** $V$ is a real vector space carrying a representation $\rho$ of $H$. The Mackey functions are the $f:G\to V$ with $f(gh)=\rho(h^{-1})f(g)$ for all $g\in G$, $h\in H$ (eq. (1)); they form a subspace $\mathcal I_G$. Functions $f:G/H\to V$ form $\mathcal I_C$. The lifting map is $[\Lambda f](g)=\rho(\mathrm h(g)^{-1})f(gH)$, with $[\Lambda^{-1}f'](x)=f'(s(x))$ (eq. (2)).
--   3. **Induced representations.** On $\mathcal I_G$, $[\pi_G(g)f](k)=f(g^{-1}k)$ (eq. (3)). On $\mathcal I_C$, $[\pi_C(g)f](x)=\rho(\mathrm h(x,g^{-1})^{-1})f(g^{-1}x)$ (eq. (4)).
--   4. **Equivariant maps and correlation.** For subgroups $H_1,H_2$ with representations $(\rho_i,V_i)$, $\mathcal H$ is the set of linear maps $\Phi:\mathcal I_G^1\to\mathcal I_G^2$ with $\Phi\,\pi_1(u)=\pi_2(u)\,\Phi$ for all $u\in G$. For a finite group $G$ with counting (Haar) measure, the cross-correlation of $\kappa:G\to\mathrm{Hom}(V_1,V_2)$ with $f:G\to V_1$ is $[\kappa\star f](g)=\sum_{g'\in G}\kappa(g^{-1}g')f(g')$ (eq. (7)). The integral over $G/H$ is $\int_{G/H}F(x)\,dx=\sum_{g\in G}F(gH)$ (eq. (34)).
--   5. **Kernel spaces.** $\mathcal K_G$ is the set of $\kappa:G\to\mathrm{Hom}(V_1,V_2)$ with $\kappa(h_2gh_1)=\rho_2(h_2)\kappa(g)\rho_1(h_1)$ (eq. (8)). $\mathcal K_C$ is the set of $\overleftarrow\kappa:G/H_1\to\mathrm{Hom}(V_1,V_2)$ with $\overleftarrow\kappa(h_2x)=\rho_2(h_2)\overleftarrow\kappa(x)\rho_1(\mathrm h_1(x,h_2)^{-1})$ (eq. (9)). The kernel lifting is $[\Lambda_{\mathcal K}\overleftarrow\kappa](g)=\overleftarrow\kappa(gH_1)\rho_1(\mathrm h_1(g))$ (eq. (10)).
--   6. **Double cosets.** $H_2\backslash G/H_1$ is the set of double cosets $H_2gH_1$, and $\gamma$ picks a representative $\gamma(x)\in x$ of each. The $H_2$-orbit of $y\in G/H_1$ is the double coset $H_2y$. For $h$ in the stabilizer $H_2^{\gamma(x)H_1}=\{h\in H_2\mid h\gamma(x)H_1=\gamma(x)H_1\}$, $\rho_1^x(h)=\rho_1(\mathrm h_1(\gamma(x)H_1,h))$ (eq. (13)). $\mathcal K_D$ is the set of $\bar\kappa:H_2\backslash G/H_1\to\mathrm{Hom}(V_1,V_2)$ with $\bar\kappa(x)=\rho_2(h)\bar\kappa(x)\rho_1^x(h)^{-1}$ for all $x$ and all $h\in H_2^{\gamma(x)H_1}$ (eq. (12)). Then $[\Omega_{\mathcal K}^{-1}\overleftarrow\kappa](x)=\overleftarrow\kappa(\gamma(x)H_1)$ (eq. (41)), and $[\Omega_{\mathcal K}\bar\kappa](y)=\rho_2(h)\bar\kappa(H_2y)\rho_1(\mathrm h_1(\gamma(H_2y)H_1,h))^{-1}$ for some $h\in H_2$ with $y=h\gamma(H_2y)H_1$ (eq. (43)).
--
--   **Formalization Note** Sums over a finite group replace the paper's Haar integrals; the counting measure is the Haar measure of a discrete group (Appendix A.3). The section $s$ is global: $G/H$ is discrete, so the whole of $G/H$ is a trivialising neighbourhood. In eq. (4) the paper prints $\mathrm h(g^{-1},x)$, which in the paper's own argument order $(x,g)$ is $\mathrm h(x,g^{-1})$. In $\Omega_{\mathcal K}$ the element $h$ is chosen by Hilbert's $\varepsilon$; the double coset $H_2y$ is computed from a chosen representative of $y$. $\rho_1^x$ uses the first expression in eq. (13), which is the one the proof uses.
-- source:
--   Cohen, Geiger and Weiler, A General Theory of Equivariant CNNs on Homogeneous Spaces, arXiv:1811.02017v2 (NeurIPS 2019), Sections 2.2-2.4 (Eqs. (1)-(4)), Section 3 (Eqs. (7)-(13)), Appendix A (Eqs. (16), (19), (25), (34)), Appendix A.1, Appendix B.2 (Eqs. (41), (43))

import Mathlib

/-!
Cohen, Geiger and Weiler, *A General Theory of Equivariant CNNs on Homogeneous Spaces*,
arXiv:1811.02017v2 (NeurIPS 2019): coset sections and the `h`-function (Section 2.2 and
Appendix A), Mackey functions, local sections, the lifting isomorphism and the induced
representations (Sections 2.3-2.4), equivariant maps, cross-correlation and the kernel spaces
`K_G`, `K_C`, `K_D` (Section 3, Appendix B), double cosets (Appendix A.1) and the integral over
`G/H` (Appendix A.3, eq. (34)).

Integrals over `G` are taken against the counting measure of a finite group (the Haar measure
of a discrete group, Appendix A.3), so they are finite sums.
-/

noncomputable section

namespace EquivariantHomogeneous

variable {G : Type*} [Group G]

/-- Appendix A, eq. (16) and Section 2.2: a section `s : G/H → G` of the projection
`p : G → G/H`, `p ∘ s = id`, i.e. a choice of coset representatives, normalised by `s(H) = e`
(the paper's standing assumption, eq. (16)). -/
structure CosetSection (H : Subgroup G) where
  /-- The coset representative `s(x)` of `x ∈ G/H`. -/
  toFun : G ⧸ H → G
  /-- `s(x) ∈ x`, i.e. `p(s(x)) = x`. -/
  mk_toFun : ∀ x : G ⧸ H, (QuotientGroup.mk (toFun x) : G ⧸ H) = x
  /-- `s(H) = e` (eq. (16)). -/
  toFun_one : toFun (QuotientGroup.mk (1 : G)) = 1

/-- Section 2.2 and Appendix A, eq. (19): the function `h : G/H × G → H`,
`h(x, g) = s(gx)⁻¹ g s(x)`, defined by `g s(x) = s(gx) h(x, g)` (eq. (18)). -/
def hfun {H : Subgroup G} (s : CosetSection H) (x : G ⧸ H) (g : G) : H :=
  ⟨(s.toFun (g • x))⁻¹ * g * s.toFun x, by
    have hx := s.mk_toFun x
    rw [mul_assoc, ← QuotientGroup.eq, s.mk_toFun]
    show g • x = g • (QuotientGroup.mk (s.toFun x) : G ⧸ H)
    rw [hx]⟩

/-- Section 2.3.2 and Appendix A, eq. (25): `h(g) = h(H, g) = s(gH)⁻¹ g ∈ H`. -/
def hElem {H : Subgroup G} (s : CosetSection H) (g : G) : H :=
  hfun s (QuotientGroup.mk (1 : G)) g

section Fields

variable {H : Subgroup G} {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Section 2.3.1, eq. (1): the space `I_G` of Mackey functions, i.e. functions `f : G → V`
with `f(gh) = ρ(h⁻¹) f(g)` for all `g ∈ G`, `h ∈ H`. -/
def mackey (ρ : Representation ℝ H V) : Submodule ℝ (G → V) where
  carrier := {f | ∀ (g : G) (h : H), f (g * (h : G)) = ρ h⁻¹ (f g)}
  add_mem' := by
    intro a b ha hb g h
    simp [ha g h, hb g h]
  zero_mem' := by
    intro g h
    simp
  smul_mem' := by
    intro c a ha g h
    simp [ha g h]

/-- Section 2.3.2, eq. (2): the lifting map `Λ : I_C → I_G`,
`[Λ f](g) = ρ(h(g)⁻¹) f(gH)`, from functions on `G/H` (sections over the whole of `G/H`, the
trivialising neighbourhood being all of `G/H` here) to functions on `G`. -/
def liftSection (s : CosetSection H) (ρ : Representation ℝ H V) (f : G ⧸ H → V) : G → V :=
  fun g => ρ (hElem s g)⁻¹ (f (QuotientGroup.mk g))

/-- Section 2.3.2, eq. (2): the inverse lifting map `[Λ⁻¹ f'](x) = f'(s(x))`. -/
def unliftSection (s : CosetSection H) (f' : G → V) : G ⧸ H → V :=
  fun x => f' (s.toFun x)

/-- Section 2.4, eq. (3): the induced representation on `I_G`, `[π_G(g) f](k) = f(g⁻¹ k)`. -/
def indG (g : G) (f : G → V) : G → V :=
  fun k => f (g⁻¹ * k)

/-- Section 2.4, eq. (4): the induced representation on `I_C`,
`[π_C(g) f](x) = ρ(h(x, g⁻¹)⁻¹) f(g⁻¹ x)`. The paper prints the first factor as
`h(g⁻¹, x)`; since `h` takes its arguments in the order `(x, g) ∈ G/H × G` (eq. (19)), this is
`h(x, g⁻¹)`. -/
def indC (s : CosetSection H) (ρ : Representation ℝ H V) (g : G) (f : G ⧸ H → V) :
    G ⧸ H → V :=
  fun x => ρ (hfun s x g⁻¹)⁻¹ (f (g⁻¹ • x))

end Fields

section Kernels

variable {H₁ H₂ : Subgroup G} {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂]

/-- Section 3: the space `H = Hom_G(I¹, I²)` of linear maps `Φ : I_G¹ → I_G²` between spaces of
Mackey functions that are equivariant, `Φ π₁(u) = π₂(u) Φ` for all `u ∈ G`. -/
def equivariantMaps (ρ₁ : Representation ℝ H₁ V₁) (ρ₂ : Representation ℝ H₂ V₂) :
    Set (mackey ρ₁ →ₗ[ℝ] mackey ρ₂) :=
  {Φ | ∀ (u : G) (f f' : mackey ρ₁), (f' : G → V₁) = indG u (f : G → V₁) →
      ((Φ f' : mackey ρ₂) : G → V₂) = indG u ((Φ f : mackey ρ₂) : G → V₂)}

/-- Section 3, eq. (7): the cross-correlation `[κ ⋆ f](g) = ∫_G κ(g⁻¹ g') f(g') dg'` with a
one-argument kernel `κ : G → Hom(V₁, V₂)`, for the counting (Haar) measure of a finite group. -/
def corr [Fintype G] (κ : G → V₁ →ₗ[ℝ] V₂) (f : G → V₁) : G → V₂ :=
  fun g => ∑ g' : G, κ (g⁻¹ * g') (f g')

/-- Theorem 3.2, eq. (8): the space `K_G` of bi-equivariant kernels,
`κ(h₂ g h₁) = ρ₂(h₂) κ(g) ρ₁(h₁)` for all `g ∈ G`, `h₁ ∈ H₁`, `h₂ ∈ H₂`. -/
def kernelsG (ρ₁ : Representation ℝ H₁ V₁) (ρ₂ : Representation ℝ H₂ V₂) :
    Set (G → V₁ →ₗ[ℝ] V₂) :=
  {κ | ∀ (g : G) (h₁ : H₁) (h₂ : H₂),
      κ ((h₂ : G) * g * (h₁ : G)) = (ρ₂ h₂).comp ((κ g).comp (ρ₁ h₁))}

/-- Theorem 3.3, eq. (9): the space `K_C` of left-equivariant kernels on `G/H₁`,
`κ⃖(h₂ x) = ρ₂(h₂) κ⃖(x) ρ₁(h₁(x, h₂)⁻¹)` for all `h₂ ∈ H₂`, `x ∈ G/H₁`, where `h₁` is the
`h`-function of the section `s₁` of `G → G/H₁`. -/
def kernelsC (s₁ : CosetSection H₁) (ρ₁ : Representation ℝ H₁ V₁)
    (ρ₂ : Representation ℝ H₂ V₂) : Set (G ⧸ H₁ → V₁ →ₗ[ℝ] V₂) :=
  {κ | ∀ (h₂ : H₂) (x : G ⧸ H₁),
      κ ((h₂ : G) • x) = (ρ₂ h₂).comp ((κ x).comp (ρ₁ (hfun s₁ x h₂)⁻¹))}

/-- Proof of Theorem 3.3, eq. (10): the lifting map for kernels `Λ_K : K_C → K_G`,
`κ(g) = κ⃖(gH₁) ρ₁(h₁(g))`. -/
def liftKernel (s₁ : CosetSection H₁) (ρ₁ : Representation ℝ H₁ V₁)
    (κ : G ⧸ H₁ → V₁ →ₗ[ℝ] V₂) : G → V₁ →ₗ[ℝ] V₂ :=
  fun g => (κ (QuotientGroup.mk g)).comp (ρ₁ (hElem s₁ g))

/-- Appendix A.1: a choice of double coset representatives `γ : H₂\G/H₁ → G`,
`γ(H₂ g H₁) ∈ H₂ g H₁`. -/
structure DoubleCosetSection (H₂ H₁ : Subgroup G) where
  /-- The representative `γ(x)` of the double coset `x`. -/
  toFun : DoubleCoset.Quotient (H₂ : Set G) (H₁ : Set G) → G
  /-- `γ(x) ∈ x`. -/
  mk_toFun : ∀ x, DoubleCoset.mk H₂ H₁ (toFun x) = x

/-- Appendix A.1: the `H₂`-orbit `H₂ y ∈ H₂\G/H₁` of a coset `y ∈ G/H₁`, i.e. the double coset
`H₂ g H₁` of any `g` with `y = gH₁`. -/
def dcOf (H₂ H₁ : Subgroup G) (y : G ⧸ H₁) : DoubleCoset.Quotient (H₂ : Set G) (H₁ : Set G) :=
  DoubleCoset.mk H₂ H₁ (Quotient.out y)

/-- Theorem 3.4, eq. (13): the representation `ρ₁ˣ(h) = ρ₁(h₁(γ(x)H₁, h))` of the stabilizer
`H₂^{γ(x)H₁} = {h ∈ H₂ | h γ(x) H₁ = γ(x) H₁}`; the formula is evaluated at every `h ∈ G`
and is only used for `h` in the stabilizer. -/
def rhoStab (s₁ : CosetSection H₁) (γ : DoubleCosetSection H₂ H₁)
    (ρ₁ : Representation ℝ H₁ V₁) (x : DoubleCoset.Quotient (H₂ : Set G) (H₁ : Set G))
    (h : G) : V₁ →ₗ[ℝ] V₁ :=
  ρ₁ (hfun s₁ (QuotientGroup.mk (γ.toFun x)) h)

/-- Theorem 3.4, eq. (12): the space `K_D` of kernels `κ̄ : H₂\G/H₁ → Hom(V₁, V₂)` with
`κ̄(x) = ρ₂(h) κ̄(x) ρ₁ˣ(h)⁻¹` for all `x ∈ H₂\G/H₁` and `h ∈ H₂^{γ(x)H₁}`. -/
def kernelsD (s₁ : CosetSection H₁) (γ : DoubleCosetSection H₂ H₁)
    (ρ₁ : Representation ℝ H₁ V₁) (ρ₂ : Representation ℝ H₂ V₂) :
    Set (DoubleCoset.Quotient (H₂ : Set G) (H₁ : Set G) → V₁ →ₗ[ℝ] V₂) :=
  {κ | ∀ x (h : H₂), (h : G) • (QuotientGroup.mk (γ.toFun x) : G ⧸ H₁) =
        QuotientGroup.mk (γ.toFun x) →
      κ x = (ρ₂ h).comp ((κ x).comp (ρ₁ (hfun s₁ (QuotientGroup.mk (γ.toFun x)) h)⁻¹))}

/-- Appendix B.2, eq. (41): the map `Ω_K⁻¹ : K_C → K_D`, `κ̄(x) = κ⃖(γ(x)H₁)`. -/
def restrictKernel (γ : DoubleCosetSection H₂ H₁) (κ : G ⧸ H₁ → V₁ →ₗ[ℝ] V₂) :
    DoubleCoset.Quotient (H₂ : Set G) (H₁ : Set G) → V₁ →ₗ[ℝ] V₂ :=
  fun x => κ (QuotientGroup.mk (γ.toFun x))

/-- Appendix B.2, eq. (43): the map `Ω_K : K_D → K_C`,
`κ⃖(y) = ρ₂(h) κ̄(H₂y) ρ₁(h₁(γ(H₂y)H₁, h))⁻¹`, where `h ∈ H₂` is some element (chosen here by
`Classical.epsilon`) with `y = h γ(H₂y) H₁`. -/
def extendKernel (s₁ : CosetSection H₁) (γ : DoubleCosetSection H₂ H₁)
    (ρ₁ : Representation ℝ H₁ V₁) (ρ₂ : Representation ℝ H₂ V₂)
    (κ : DoubleCoset.Quotient (H₂ : Set G) (H₁ : Set G) → V₁ →ₗ[ℝ] V₂) (y : G ⧸ H₁) :
    V₁ →ₗ[ℝ] V₂ :=
  haveI : Nonempty H₂ := ⟨1⟩
  let x := dcOf H₂ H₁ y
  let h : H₂ := Classical.epsilon fun h : H₂ =>
    y = (h : G) • (QuotientGroup.mk (γ.toFun x) : G ⧸ H₁)
  (ρ₂ h).comp ((κ x).comp (ρ₁ (hfun s₁ (QuotientGroup.mk (γ.toFun x)) h)⁻¹))

end Kernels

/-- Appendix A.3, eq. (34): the integral over `G/H` defined through the integral over `G`,
`∫_{G/H} f(x) dx = ∫_G f(gH) dg`, for the counting (Haar) measure of a finite group. -/
def quotientIntegral [Fintype G] {M : Type*} [AddCommMonoid M] (H : Subgroup G)
    (f : G ⧸ H → M) : M :=
  ∑ g : G, f (QuotientGroup.mk g)

end EquivariantHomogeneous


