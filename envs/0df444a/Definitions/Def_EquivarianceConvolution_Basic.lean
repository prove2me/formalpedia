-- Prove2me | Definitions.Def_EquivarianceConvolution_Basic
-- name    : EquivarianceConvolution_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T19:58:14.848949+00:00
-- url     : https://prove2.me/theorems/e78b3c4e-fe8b-4a36-9675-2b907219bb6f
-- title:
--   Equivariant feed-forward networks, generalized convolution on quotient spaces, G-CNNs and Fourier transforms on finite groups
-- statement:
--   Objects of Sections 3–5 and Appendices A, B and E of Kondor and Trivedi (2018). Throughout, $G$ is a finite group.
--
--   1. **Actions on functions (Section 3.1).** If $G$ acts on a set $\mathcal X$, it acts on functions $f:\mathcal X\to V$ by $(\mathbb T_g f)(x)=f(g^{-1}x)$.
--   2. **Equivariance (Definition 2).** A map $\phi:L_{V_1}(\mathcal X_1)\to L_{V_2}(\mathcal X_2)$ is $G$-equivariant if $\phi(\mathbb T_g f)=\mathbb T'_g\,\phi(f)$ for all $f$ and all $g\in G$.
--   3. **Feed-forward networks (Definitions 1 and 3).** A network has index sets $\mathcal X_0,\dots,\mathcal X_L$, activation spaces $V_\ell=\mathbb C^{d_\ell}$, linear maps $\phi_\ell:L_{V_{\ell-1}}(\mathcal X_{\ell-1})\to L_{V_\ell}(\mathcal X_\ell)$ and pointwise nonlinearities $\sigma_\ell:V_\ell\to V_\ell$. Its activations are $f_\ell(x)=\sigma_\ell(\phi_\ell(f_{\ell-1})(x))$, starting from the input $f_0$. The network is $G$-equivariant if replacing $f_0$ by $\mathbb T^0_gf_0$ replaces every $f_\ell$ by $\mathbb T^\ell_gf_\ell$.
--   4. **Quotient spaces and liftings (Section 3 box).** For a subgroup $H$, a function $f$ on $G/H$ lifts to $f\uparrow^G(g)=f(gH)$, and a function on $H\backslash G$ lifts to $f\uparrow^G(g)=f(Hg)$. A function on the double quotient $H\backslash G/K$ is identified with its lift, a function $\chi$ on $G$ with $\chi(hvk)=\chi(v)$ for $h\in H$, $k\in K$.
--   5. **Convolution (eqs. (7)–(8), Definitions 4 and 7).** $(f*g)(u)=\sum_{v\in G}f(uv^{-1})g(v)$. For $f:G\to\mathbb C^m$ and a matrix-valued $\chi:G\to\mathbb C^{n\times m}$, $(f*\chi)(u)=\sum_{v\in G}\chi(v)f(uv^{-1})$.
--   6. **G-CNN (Definition 5).** A linear map $\phi:L_{\mathbb C^m}(G/H)\to L_{\mathbb C^n}(G/K)$ is a generalized convolution if there is a filter $\chi$ on $H\backslash G/K$ with $\phi(f)\uparrow^G=f\uparrow^G*\chi\uparrow^G$. A network with $\mathcal X_\ell=G/H_\ell$ is a $G$-CNN if every $\phi_\ell$ is a generalized convolution with a filter on $H_{\ell-1}\backslash G/H_\ell$.
--   7. **Representations (Appendix A).** A representation is a homomorphism $\rho:G\to\mathbb C^{n\times n}$. It is irreducible if $n\ge1$ and the only subspaces of $\mathbb C^n$ invariant under every $\rho(g)$ are $0$ and $\mathbb C^n$. The trivial representation is $\rho_{\mathrm{tr}}(g)=(1)$. A decomposition $\rho|_H=\mu_1\oplus\cdots\oplus\mu_k$ means that every $\rho(h)$, $h\in H$, is block diagonal with consecutive diagonal blocks $\mu_1(h),\dots,\mu_k(h)$, and each $\mu_t$ is an irreducible representation of $H$. A block is trivial if it is one-dimensional and equals $1$ on $H$.
--   8. **Fourier transform (eq. (13), Section 4.2).** $\hat f(\rho)=\sum_{u\in G}f(u)\rho(u)$. A function on a quotient space is transformed through its lift.
--   9. **Subrepresentations (Appendices A, E).** For linear actions $\{T_g\}$ on a complex vector space $U$: a subspace $W$ is invariant if $T_gW\subseteq W$ for all $g$. It is irreducible if it is nonzero, invariant, and contains no invariant subspaces other than $0$ and $W$. Two such restrictions are equivalent if a linear isomorphism intertwines them. The isotypic component $U_\rho$ of an irrep $\rho$ is the sum of all invariant subspaces on which the action is equivalent to $\rho$.
--
--   **Formalization Note** The layers are indexed from $0$: the Lean map `phi ℓ` is the paper's $\phi_{\ell+1}$, and a network is given for all $\ell\in\mathbb N$, of which an $(L+1)$-layer statement uses $\ell<L$. The origin of $G/H$ is the coset $H$. Functions on $H\backslash G/K$ are represented by their lifts to $G$. The paper's filter type $L_{V_{\ell-1}\times V_\ell}$ is read as matrices acting on $V_{\ell-1}$, using the product of Definition 7 (3). The paper states its results for compact groups but works with finite or countable groups throughout (Section 4.1, Appendix A). A countable compact (Hausdorff) group is finite, so the statements take $G$ finite.
-- source:
--   Kondor and Trivedi, On the Generalization of Equivariance and Convolution in Neural Networks to the Action of Compact Groups, arXiv:1802.03690v3 (ICML 2018), Sections 3-5 (Definitions 1-5, eqs. (7)-(13)), Appendix A, Appendix B (Definition 7), Appendix E

import Mathlib

/-!
Kondor and Trivedi, *On the Generalization of Equivariance and Convolution in Neural Networks to
the Action of Compact Groups*, arXiv:1802.03690v3 (ICML 2018): feed-forward networks and
equivariance (Section 3, Definitions 1–3), convolution on finite groups and quotient spaces
(Section 4, eqs. (7)–(12), Definition 4, Appendix B Definition 7), G-CNNs (Section 5,
Definition 5), representations and Fourier transforms (Section 4.2, eq. (13), Appendix A), and the
subrepresentations and isotypic components used in Appendix E.

The paper assumes throughout that the group is finite or countable (Section 4.1, Appendix A) and
states its results for compact groups; the statements take `G` finite.
-/

noncomputable section

namespace EquivarianceConvolution

open scoped BigOperators

section Basic

variable {G : Type*} [Group G]

/-- Section 3.1, item 3: the action of `g ∈ G` on functions `f : X → V` induced by an action on
`X`, `f' (T_g x) = f x`, i.e. `(T_g f)(x) = f (g⁻¹ x)`. -/
def translateFun {X V : Type*} [MulAction G X] (g : G) (f : X → V) : X → V :=
  fun x => f (g⁻¹ • x)

/-- Definition 2: a (linear or non-linear) map `φ : L_{V₁}(X₁) → L_{V₂}(X₂)` is `G`-equivariant
if `φ (T_g f) = T'_g (φ f)` for every `f` and every `g ∈ G`. -/
def IsEquivariantMap (G : Type*) [Group G] {X₁ X₂ V₁ V₂ : Type*} [MulAction G X₁]
    [MulAction G X₂] (φ : (X₁ → V₁) → (X₂ → V₂)) : Prop :=
  ∀ (g : G) (f : X₁ → V₁), φ (translateFun g f) = translateFun g (φ f)

/-- Definition 1: a multilayer feed-forward network with index sets `X ℓ` and activations in
`V_ℓ = ℂ^{d ℓ}`: linear maps `phi ℓ : L_{V_ℓ}(X_ℓ) → L_{V_{ℓ+1}}(X_{ℓ+1})` (the paper's
`φ_{ℓ+1}`) and pointwise nonlinearities `sigma ℓ : V_{ℓ+1} → V_{ℓ+1}` (the paper's `σ_{ℓ+1}`).
A network with `L + 1` layers uses the entries with `ℓ < L` only. -/
structure FeedForwardNet (X : ℕ → Type*) (d : ℕ → ℕ) where
  /-- The linear map from layer `ℓ` to layer `ℓ + 1`. -/
  phi : ∀ l : ℕ, (X l → Fin (d l) → ℂ) →ₗ[ℂ] (X (l + 1) → Fin (d (l + 1)) → ℂ)
  /-- The pointwise nonlinearity of layer `ℓ + 1`. -/
  sigma : ∀ l : ℕ, (Fin (d (l + 1)) → ℂ) → (Fin (d (l + 1)) → ℂ)

/-- Definition 1: the activations `f_0 ↦ f_1 ↦ … `, `f_{ℓ+1}(x) = σ(φ(f_ℓ)(x))`, as a function of
the input `f_0`. -/
def FeedForwardNet.act {X : ℕ → Type*} {d : ℕ → ℕ} (N : FeedForwardNet X d) :
    (l : ℕ) → (X 0 → Fin (d 0) → ℂ) → (X l → Fin (d l) → ℂ)
  | 0 => fun f => f
  | l + 1 => fun f x => N.sigma l (N.phi l (N.act l f) x)

/-- Definition 3: an `L + 1` layer network is `G`-equivariant if transforming the input
`f_0 ↦ T^0_g f_0` transforms every layer `f_ℓ ↦ T^ℓ_g f_ℓ`, `0 ≤ ℓ ≤ L`, for every `g ∈ G`. -/
def IsEquivariantNet (G : Type*) [Group G] {X : ℕ → Type*} [∀ l, MulAction G (X l)]
    {d : ℕ → ℕ} (L : ℕ) (N : FeedForwardNet X d) : Prop :=
  ∀ (g : G) (f₀ : X 0 → Fin (d 0) → ℂ) (l : ℕ), l ≤ L →
    N.act l (translateFun g f₀) = translateFun g (N.act l f₀)

/-- Box "Essential definitions for quotient spaces" (Section 3): the lifting `f↑^G(g) = f([g]_X)`
of a function on `X = G/H` to `G`, with origin `x₀ = H` so that `[g]_X = gH`. -/
def liftQ {H : Subgroup G} {V : Type*} (f : G ⧸ H → V) : G → V :=
  fun g => f (g : G ⧸ H)

/-- The lifting `f↑^G(g) = f(Hg)` of a function on the right quotient space `H\G` to `G`
(Section 3 box; Section 4.2). -/
def liftR {H : Subgroup G} {V : Type*} (f : Quotient (QuotientGroup.rightRel H) → V) : G → V :=
  fun g => f (Quotient.mk _ g)

/-- Lifts of functions on the double quotient space `H\G/K` (Section 3 box, Case III of
Section 4.1): `χ (h v k) = χ v` for all `h ∈ H`, `k ∈ K`, `v ∈ G`. -/
def IsDoubleCosetFun (H K : Subgroup G) {V : Type*} (χ : G → V) : Prop :=
  ∀ h ∈ H, ∀ k ∈ K, ∀ v : G, χ (h * v * k) = χ v

/-- Eq. (7) and Definition 4 (eq. (8)) on lifted functions: `(f ∗ g)(u) = ∑_{v ∈ G} f(u v⁻¹) g(v)`. -/
def groupConv [Fintype G] (f g : G → ℂ) : G → ℂ :=
  fun u => ∑ v, f (u * v⁻¹) * g v

/-- Appendix B, Definition 7 (3) (eq. (25)): for `f : G → ℂ^m` and `χ : G → ℂ^{n×m}`,
`(f ∗ χ)(u) = ∑_{v ∈ G} χ(v) f(u v⁻¹)`. -/
def vecConv [Fintype G] {m n : ℕ} (f : G → Fin m → ℂ) (χ : G → Matrix (Fin n) (Fin m) ℂ) :
    G → Fin n → ℂ :=
  fun u => ∑ v, Matrix.mulVec (χ v) (f (u * v⁻¹))

/-- Definitions 4, 5 and 7: `φ : L_{ℂ^m}(G/H) → L_{ℂ^n}(G/K)` is a generalized convolution
`φ(f) = f ∗ χ` with a filter `χ` on `H\G/K` (given by its lift to `G`), the result read as a
function on `G/K`. -/
def IsConvLayer [Fintype G] (H K : Subgroup G) {m n : ℕ}
    (φ : (G ⧸ H → Fin m → ℂ) → (G ⧸ K → Fin n → ℂ)) : Prop :=
  ∃ χ : G → Matrix (Fin n) (Fin m) ℂ, IsDoubleCosetFun H K χ ∧
    ∀ (f : G ⧸ H → Fin m → ℂ) (u : G), liftQ (φ f) u = vecConv (liftQ f) χ u

/-- Definition 5: an `L + 1` layer network with index sets `X_ℓ = G/H_ℓ` is a `G`-CNN if every
linear map `φ_ℓ` is a generalized convolution with a filter on `H_{ℓ-1}\G/H_ℓ`. -/
def IsGCNN [Fintype G] (H : ℕ → Subgroup G) {d : ℕ → ℕ} (L : ℕ)
    (N : FeedForwardNet (fun l => G ⧸ H l) d) : Prop :=
  ∀ l < L, IsConvLayer (H l) (H (l + 1)) (N.phi l)

/-- Appendix A ("Equivalence, reducibility and irreps"): the matrices `ρ(g)`, `g ∈ S`, acting on
`ℂ^ι` are irreducible: `ι` is nonempty and the only subspaces invariant under all of them are `0`
and `ℂ^ι`. -/
def IsIrreducibleOn {ι : Type*} [Fintype ι] (S : Set G) (ρ : G → Matrix ι ι ℂ) : Prop :=
  Nonempty ι ∧ ∀ W : Submodule ℂ (ι → ℂ),
    (∀ g ∈ S, ∀ w ∈ W, Matrix.mulVec (ρ g) w ∈ W) → W = ⊥ ∨ W = ⊤

/-- Appendix A: `ρ : G → ℂ^{n×n}` with `ρ(g₁)ρ(g₂) = ρ(g₁g₂)` is an irreducible representation. -/
def IsIrrep {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsIrreducibleOn Set.univ (fun g => ρ g)

/-- Appendix A: `ρ` is the trivial representation `ρ_tr(g) = (1)`. -/
def IsTrivialRep {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) : Prop :=
  n = 1 ∧ ∀ g, ρ g = 1

/-- Proposition 1 (hypothesis): on restriction to `H`, `ρ` is block diagonal,
`ρ|_H = μ_1 ⊕ ⋯ ⊕ μ_k`, with consecutive blocks; `b i` is the block containing index `i`, and each
block `μ_t` is an irreducible representation of `H`. -/
def IsRestrictionDecomp {n k : ℕ} (H : Subgroup G) (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → Fin k) : Prop :=
  Monotone b ∧ (∀ h ∈ H, ∀ i j, b i ≠ b j → ρ h i j = 0) ∧
    ∀ t : Fin k, IsIrreducibleOn (H : Set G)
      (fun h => (ρ h).submatrix (fun i : {i // b i = t} => i.1) (fun i => i.1))

/-- Proposition 1: the block `μ_t` of the decomposition `b` of `ρ|_H` is the trivial
representation of `H` (one-dimensional, equal to `(1)` on `H`). -/
def IsTrivialBlock {n k : ℕ} (H : Subgroup G) (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → Fin k) (t : Fin k) : Prop :=
  Fintype.card {i // b i = t} = 1 ∧ ∀ h ∈ H, ∀ i, b i = t → ρ h i i = 1

/-- Eq. (13): the Fourier transform `f̂(ρ) = ∑_{u ∈ G} f(u) ρ(u)`; for a function on a quotient
space it is applied to the lifting (Section 4.2). -/
def groupFourier [Fintype G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (f : G → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ u, f u • ρ u

section Modules

variable {U V : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]

/-- Appendix E: a subspace `W ⊆ U` fixed by the linear action `{T_g}`. -/
def IsInvariantSubspace (T : Representation ℂ G U) (W : Submodule ℂ U) : Prop :=
  ∀ g : G, ∀ w ∈ W, T g w ∈ W

/-- Appendix E (Lemma 5): an irreducible subspace: nonzero, invariant, and with no invariant
subspaces other than `0` and itself. -/
def IsIrreducibleSubspace (T : Representation ℂ G U) (W : Submodule ℂ U) : Prop :=
  W ≠ ⊥ ∧ IsInvariantSubspace T W ∧
    ∀ W' : Submodule ℂ U, W' ≤ W → IsInvariantSubspace T W' → W' = ⊥ ∨ W' = W

/-- Appendix E (Lemmas 5–6): a linear map `φ : U → V` equivariant with the actions `{T_g}` and
`{T'_g}`: `φ (T_g u) = T'_g (φ u)`. -/
def IsEquivariantLinear (T : Representation ℂ G U) (T' : Representation ℂ G V)
    (φ : U →ₗ[ℂ] V) : Prop :=
  ∀ (g : G) (u : U), φ (T g u) = T' g (φ u)

/-- Appendix A and E (Lemma 5): the restriction of `{T_g}` to `W` and of `{T'_g}` to `Z` are
equivalent representations: a linear isomorphism `W ≅ Z` intertwining them. -/
def AreEquivalentSubreps (T : Representation ℂ G U) (W : Submodule ℂ U)
    (T' : Representation ℂ G V) (Z : Submodule ℂ V) : Prop :=
  ∃ e : W ≃ₗ[ℂ] Z, ∀ (g : G) (w w' : W), (w' : U) = T g w → (e w' : V) = T' g (e w)

/-- Appendix A and E: an invariant subspace `W` on which `{T_g}` is equivalent to the matrix
representation `ρ`. -/
def IsOfType {n : ℕ} (T : Representation ℂ G U) (W : Submodule ℂ U)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsInvariantSubspace T W ∧
    ∃ e : W ≃ₗ[ℂ] (Fin n → ℂ), ∀ (g : G) (w w' : W),
      (w' : U) = T g w → e w' = Matrix.mulVec (ρ g) (e w)

/-- Appendix E (Lemma 6): the isotypic component `U_ρ` of `U` belonging to the irrep `ρ`, the sum
of all invariant subspaces of `U` on which the action is equivalent to `ρ`. -/
def isotypicPart {n : ℕ} (T : Representation ℂ G U) (ρ : G →* Matrix (Fin n) (Fin n) ℂ) :
    Submodule ℂ U :=
  ⨆ (W : Submodule ℂ U) (_ : IsOfType T W ρ), W

end Modules

end Basic

end EquivarianceConvolution


