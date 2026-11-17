-- Prove2me | Definitions.Def_HoneycombCodes_Supplement_FrameCert
-- name    : HoneycombCodes_Supplement_FrameCert
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:34:41.632963+00:00
-- url     : https://prove2.me/theorems/78f1fa1a-9262-4b88-8496-70d693ac9372
-- title:
--   Multiplicity-space transfer operators, frame-profile certificates $h=(F,A,b,\lambda)$ and the bound $B(h;s)$
-- statement:
--   Let $G$ be a group, $H\le G$, $W$ a unitary $G$-representation with an $H$-fixed unit vector $\ell_o$, $E$ an irreducible unitary $H$-representation of dimension $d_E$, and $\Omega$ a finite family of pairwise inequivalent irreducible unitary $G$-representations $V_\omega$, $D_\omega=\dim V_\omega$, with no multiplicity-one assumption. Put
--
--   $$
--   M_\omega=\mathrm{Hom}_H(E,\mathrm{Res}^G_H V_\omega),\qquad \langle a,b\rangle_{M_\omega}=\tfrac1{d_E}\operatorname{tr}(a^*b),
--   $$
--
--   the Hilbert structure for which $M_\omega\otimes E\to V_\omega$, $a\otimes u\mapsto a(u)$, is unitary onto the $E$-isotypic component. A finite directed edge set (parallel edges allowed) carries, for each edge $e$ from $\omega$ to $\nu$, an isometric $G$-intertwiner $C_e:V_\nu\to W\otimes V_\omega$, parallel intertwiners of one pair having orthogonal images. The **transfer operator** $T_e:M_\omega\to M_\nu$ is defined by (81), $C_e^*(\ell_o\otimes a(u))=(T_ea)(u)$.
--
--   A **frame-profile certificate** $h=(F,A,b,\lambda)$ (Definition 7.3) consists of a nonzero finite-dimensional Hilbert space $F$, $m=\dim F$; linear maps $A_\omega:F\to M_\omega$ with $\sum_\omega A_\omega^*A_\omega=I_F$ (82); scalars $b_e\in\mathbb C$ with $\sum_{e:t(e)=\nu}|b_e|^2\le1$ for every $\nu$ (83); and $\lambda>0$ with $\sum_{e:t(e)=\nu}b_eT_eA_{s(e)}=\sqrt\lambda A_\nu$ for every $\nu$ (84). With $q_\omega=\|A_\omega\|_F^2$ and $\Delta(A)=\sum_\omega q_\omega^2/D_\omega$,
--
--   $$
--   B(h;s)=\frac{(1-s)m}{d_E(\lambda-s)\Delta(A)}.
--   $$
--
--   The **certificate kernel** is $K_h(x,y)=\operatorname{tr}(P_xP_y)$ with $P_x=\Psi_x\Psi_x^*$, $\Psi_x(a\otimes u)=\bigoplus_\omega\Phi_{\omega,x}(A_\omega a\otimes u)$.
--
--   These data carry Theorem 7.4 and the certificate libraries and localizers of Sections 8 and 10.
--
--   **Formalization Note** $H$ is given by an embedding $\iota:H\to G$. $T_e=C_e^*\circ(\ell_o\otimes\cdot)\circ a$ uses Mathlib's tensor-product inner product and adjoint; (82) is stated as $\sum_\omega\langle A_\omega f,A_\omega f'\rangle_{M_\omega}=\langle f,f'\rangle$. $q_\omega$ is computed in an orthonormal basis of $F$. The kernel is $\sum_{i,j}|\sum_\omega\langle g_x\psi_{\omega,i},g_y\psi_{\omega,j}\rangle|^2$ for the frame vectors $\psi_{\omega,(a,b)}=(A_\omega f_a)(u_b)$ and any $g_x$ with $g_x o=x$.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §7.1, eq. (81), p.36 (PDF 38); Definition 7.3, eqs. (82)–(84), and (86), p.37 (PDF 39); proof of Theorem 7.4, p.38 (PDF 40)

import Mathlib

set_option autoImplicit false

open scoped InnerProductSpace TensorProduct

namespace HoneycombCodes.Supplement

variable {G : Type*} [Group G] {H : Type*} [Group H]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- `a ∈ M_ω = Hom_H(E, Res^G_H V_ω)`: the linear map `a : E → V_ω` intertwines `ρ_E` with the
restriction of `ρ_V` along `ι : H → G`, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code
Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), §7.1, p.36 (PDF 38). -/
def IsHMap {Vω : Type*} [AddCommGroup Vω] [Module ℂ Vω] (ι : H →* G)
    (ρE : Representation ℂ H E) (ρV : Representation ℂ G Vω) (a : E →ₗ[ℂ] Vω) : Prop :=
  ∀ (h : H) (u : E), a (ρE h u) = ρV (ι h) (a u)

/-- The **multiplicity-space inner product** `⟨a, b⟩_{M_ω} = tr(a* b)/d_E`, arXiv:2608.20287v2,
§7.1, p.36 (PDF 38): the Hilbert structure on `M_ω` for which the evaluation map
`Φ_{ω,o} : M_ω ⊗ E → V_ω`, `a ⊗ u ↦ a(u)`, is unitary onto the `E`-isotypic component.

**Formalization Note.** Conjugate-linear in `a`, linear in `b` (Mathlib's convention);
`d_E = finrank E`. -/
noncomputable def mInner {Vω : Type*} [NormedAddCommGroup Vω] [InnerProductSpace ℂ Vω]
    [FiniteDimensional ℂ Vω] (a b : E →ₗ[ℂ] Vω) : ℂ :=
  LinearMap.trace ℂ E (LinearMap.adjoint a ∘ₗ b) / (Module.finrank ℂ E : ℂ)

/-- The **transfer operator** `T_e : M_ω → M_ν` of an edge with isometric intertwiner
`C_e : V_ν → W ⊗ V_ω`, defined by (81) at the base point,
`C_e*(ℓ_o ⊗ a(u)) = (T_e a)(u)`, arXiv:2608.20287v2, §7.1, eq. (81), p.36 (PDF 38).

**Formalization Note.** `T_e a = C_e* ∘ (ℓ_o ⊗ ·) ∘ a`, with Mathlib's tensor-product inner product
and adjoint. By `G`-equivariance (81) at `x = o` gives (81) at every `x` (p.36). -/
noncomputable def transferT {Vω Vν : Type*} [NormedAddCommGroup Vω] [InnerProductSpace ℂ Vω]
    [FiniteDimensional ℂ Vω] [NormedAddCommGroup Vν] [InnerProductSpace ℂ Vν]
    [FiniteDimensional ℂ Vν] (ℓo : W) (C : Vν →ₗ[ℂ] W ⊗[ℂ] Vω) (a : E →ₗ[ℂ] Vω) :
    E →ₗ[ℂ] Vν :=
  LinearMap.adjoint C ∘ₗ TensorProduct.mk ℂ W Vω ℓo ∘ₗ a

/-- The **standing data of §7.1** (the setup of §3 without multiplicity one),
arXiv:2608.20287v2, §7.1, p.36 (PDF 38), at the base point:

* a group `G` with a subgroup `H` (given by the embedding `ι`), a unitary `G`-representation `ρW`
  and a unit vector `ℓ_o ∈ W` fixed by `H`;
* an irreducible unitary `H`-representation `ρE`;
* a finite family `Ω` of pairwise inequivalent irreducible unitary `G`-representations `ρ ω` on
  `V ω` (no multiplicity condition: `M_ω = Hom_H(E, Res V_ω)` may have any dimension);
* a finite directed edge set, `Edge ω ν` being the (possibly several, parallel) edges from source
  `ω` to target `ν`, each with an isometric `G`-intertwiner `C_e : V_ν → W ⊗ V_ω`; parallel
  intertwiners of one pair `(ω, ν)` have orthogonal images.

**Formalization Note.** Representations are Mathlib `Representation`s on finite-dimensional complex
inner-product spaces, unitarity is `⟪ρ g v, ρ g v'⟫ = ⟪v, v'⟫`, and `W ⊗ V_ω` carries Mathlib's
tensor-product inner product and `ρW.tprod (ρ ω)`. The points `x ∈ X` other than `o` enter only
Theorem 7.4 and the kernel `K_h`. -/
structure IsFrameSetup (ι : H →* G) (ρW : Representation ℂ G W) (ℓo : W)
    (ρE : Representation ℂ H E) {Ω : Type*} [Fintype Ω] (V : Ω → Type*)
    [∀ ω, NormedAddCommGroup (V ω)] [∀ ω, InnerProductSpace ℂ (V ω)]
    [∀ ω, FiniteDimensional ℂ (V ω)] (ρ : ∀ ω, Representation ℂ G (V ω))
    (Edge : Ω → Ω → Type*) [∀ ω ν, Fintype (Edge ω ν)]
    (C : ∀ ω ν, Edge ω ν → (V ν →ₗ[ℂ] W ⊗[ℂ] V ω)) : Prop where
  unitaryW : ∀ (g : G) (v v' : W), ⟪ρW g v, ρW g v'⟫_ℂ = ⟪v, v'⟫_ℂ
  ellO_norm : ‖ℓo‖ = 1
  ellO_fixed : ∀ h : H, ρW (ι h) ℓo = ℓo
  unitaryE : ∀ (h : H) (u u' : E), ⟪ρE h u, ρE h u'⟫_ℂ = ⟪u, u'⟫_ℂ
  irredE : ρE.IsIrreducible
  unitaryV : ∀ (ω : Ω) (g : G) (v v' : V ω), ⟪ρ ω g v, ρ ω g v'⟫_ℂ = ⟪v, v'⟫_ℂ
  irredV : ∀ ω : Ω, (ρ ω).IsIrreducible
  inequiv : ∀ ω ω' : Ω, ω ≠ ω' → IsEmpty ((ρ ω).Equiv (ρ ω'))
  C_isometry : ∀ (ω ν : Ω) (e : Edge ω ν) (v : V ν), ‖C ω ν e v‖ = ‖v‖
  C_intertwines : ∀ (ω ν : Ω) (e : Edge ω ν) (g : G) (v : V ν),
    C ω ν e (ρ ν g v) = (ρW.tprod (ρ ω)) g (C ω ν e v)
  parallel_orth : ∀ (ω ν : Ω) (e e' : Edge ω ν), e ≠ e' → ∀ v v' : V ν,
    ⟪C ω ν e v, C ω ν e' v'⟫_ℂ = 0

/-- A **frame-profile certificate** `h = (F, A, b, λ)` on `(E, Ω, Edge)` (Definition 7.3),
arXiv:2608.20287v2, §7.2, p.37 (PDF 39):

* (a) `F` a nonzero finite-dimensional Hilbert space, `m = dim F`;
* (b) linear maps `A_ω : F → M_ω` with the Parseval condition `Σ_ω A_ω* A_ω = I_F` (82);
* (c) scalars `b_e ∈ ℂ` with `Σ_{e : t(e) = ν} |b_e|² ≤ 1` for every `ν` (83);
* (d) `λ > 0` with the harmonic frame equations `Σ_{e : t(e) = ν} b_e T_e A_{s(e)} = √λ A_ν` (84).

**Formalization Note.** `A ω f : E → V ω` is required to lie in `M_ω` (`IsHMap`); adjoints in (82)
are taken for the `M_ω` inner product `mInner`, so (82) reads
`Σ_ω ⟨A_ω f, A_ω f'⟩_{M_ω} = ⟪f, f'⟫` for all `f, f'`. `T_e` is `transferT ℓ_o (C e)`. -/
structure IsFrameCertificate (ι : H →* G) (ℓo : W) (ρE : Representation ℂ H E)
    {Ω : Type*} [Fintype Ω] (V : Ω → Type*)
    [∀ ω, NormedAddCommGroup (V ω)] [∀ ω, InnerProductSpace ℂ (V ω)]
    [∀ ω, FiniteDimensional ℂ (V ω)] (ρ : ∀ ω, Representation ℂ G (V ω))
    (Edge : Ω → Ω → Type*) [∀ ω ν, Fintype (Edge ω ν)]
    (C : ∀ ω ν, Edge ω ν → (V ν →ₗ[ℂ] W ⊗[ℂ] V ω))
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : ∀ ω, F →ₗ[ℂ] (E →ₗ[ℂ] V ω)) (b : ∀ ω ν, Edge ω ν → ℂ) (lam : ℝ) : Prop where
  nontrivialF : Nontrivial F
  maps_in_M : ∀ (ω : Ω) (f : F), IsHMap ι ρE (ρ ω) (A ω f)
  parseval : ∀ f f' : F, ∑ ω, mInner (A ω f) (A ω f') = ⟪f, f'⟫_ℂ
  column : ∀ ν : Ω, ∑ ω, ∑ e : Edge ω ν, ‖b ω ν e‖ ^ 2 ≤ 1
  lam_pos : 0 < lam
  harmonic : ∀ (ν : Ω) (f : F),
    ∑ ω, ∑ e : Edge ω ν, b ω ν e • transferT ℓo (C ω ν e) (A ω f) =
      ((Real.sqrt lam : ℝ) : ℂ) • A ν f

/-- The **frame weights** `q_ω = ‖A_ω‖²_F` (Frobenius norm for the `M_ω` inner product),
arXiv:2608.20287v2, §7.2, p.37 (PDF 39): `q_ω = Σ_a ⟨A_ω f_a, A_ω f_a⟩_{M_ω}` over an orthonormal
basis `(f_a)` of `F` (basis-independent). -/
noncomputable def qFrob {Vω : Type*} [NormedAddCommGroup Vω] [InnerProductSpace ℂ Vω]
    [FiniteDimensional ℂ Vω] (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (Aω : F →ₗ[ℂ] (E →ₗ[ℂ] Vω)) : ℝ :=
  ∑ a, (mInner (Aω (stdOrthonormalBasis ℂ F a)) (Aω (stdOrthonormalBasis ℂ F a))).re

/-- `Δ(A) = Σ_ω q_ω²/D_ω` with `D_ω = dim V_ω`, arXiv:2608.20287v2, §7.2, p.37 (PDF 39). -/
noncomputable def DeltaA {Ω : Type*} [Fintype Ω] (V : Ω → Type*)
    [∀ ω, NormedAddCommGroup (V ω)] [∀ ω, InnerProductSpace ℂ (V ω)]
    [∀ ω, FiniteDimensional ℂ (V ω)]
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : ∀ ω, F →ₗ[ℂ] (E →ₗ[ℂ] V ω)) : ℝ :=
  ∑ ω, qFrob F (A ω) ^ 2 / (Module.finrank ℂ (V ω) : ℝ)

/-- The **frame-profile bound** (86), `B(h; s) = (1 − s) m / (d_E (λ − s) Δ(A))`,
`m = dim F`, `d_E = dim E`, arXiv:2608.20287v2, Theorem 7.4, p.37 (PDF 39). -/
noncomputable def boundB {Ω : Type*} [Fintype Ω] (V : Ω → Type*)
    [∀ ω, NormedAddCommGroup (V ω)] [∀ ω, InnerProductSpace ℂ (V ω)]
    [∀ ω, FiniteDimensional ℂ (V ω)]
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : ∀ ω, F →ₗ[ℂ] (E →ₗ[ℂ] V ω)) (lam s : ℝ) : ℝ :=
  (1 - s) * (Module.finrank ℂ F : ℝ) /
    ((Module.finrank ℂ E : ℝ) * (lam - s) * DeltaA V F A)

/-- The **certificate kernel** `K_h(x, y) = tr(P_x P_y)`, `P_x = Ψ_x Ψ_x*`, of the moving frame
`Ψ_x(a ⊗ u) = ⊕_ω Φ_{ω,x}(A_ω a ⊗ u)`, arXiv:2608.20287v2, proof of Theorem 7.4, p.38 (PDF 40),
and §7.3, p.39 (PDF 41).

**Formalization Note.** The frame is given by the vectors `ψ_{ω,i} = Ψ_o(e_i)` of an orthonormal
basis `(e_i)_{i ∈ ι}` of `F ⊗ E` (for `e_i = f_a ⊗ u_b`, `ψ_{ω,i} = (A_ω f_a)(u_b)`); `rep x ∈ G` is
any group element with `rep x · o = x`, so `Φ_{ω,x}(a ⊗ [rep x, u]) = rep x · a(u)`. Then
`tr(P_x P_y) = ‖Ψ_x* Ψ_y‖²_HS = Σ_{i,j} |Σ_ω ⟨rep x · ψ_{ω,i}, rep y · ψ_{ω,j}⟩|²`, which does not
depend on the choice of `rep` because the frame is `H`-equivariant. -/
noncomputable def frameKernel {Ω : Type*} [Fintype Ω] (V : Ω → Type*)
    [∀ ω, NormedAddCommGroup (V ω)] [∀ ω, InnerProductSpace ℂ (V ω)]
    (ρ : ∀ ω, Representation ℂ G (V ω)) {ι : Type*} [Fintype ι] (ψ : ∀ ω, ι → V ω)
    {X : Type*} (rep : X → G) (x y : X) : ℝ :=
  ∑ i, ∑ j, ‖∑ ω, ⟪ρ ω (rep x) (ψ ω i), ρ ω (rep y) (ψ ω j)⟫_ℂ‖ ^ 2

/-- The frame vectors `ψ_{ω,(a,b)} = (A_ω f_a)(u_b)` of a frame-profile certificate, for the
standard orthonormal bases `(f_a)` of `F` and `(u_b)` of `E`. -/
noncomputable def frameVectors {Ω : Type*} (V : Ω → Type*)
    [∀ ω, NormedAddCommGroup (V ω)] [∀ ω, InnerProductSpace ℂ (V ω)]
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : ∀ ω, F →ₗ[ℂ] (E →ₗ[ℂ] V ω)) :
    ∀ ω, (Fin (Module.finrank ℂ F) × Fin (Module.finrank ℂ E)) → V ω :=
  fun ω i => A ω (stdOrthonormalBasis ℂ F i.1) (stdOrthonormalBasis ℂ E i.2)

end HoneycombCodes.Supplement


