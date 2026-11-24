-- Prove2me | Definitions.Def_DeepONetError_Basic
-- name    : DeepONetError_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T05:23:01.427603+00:00
-- url     : https://prove2.me/theorems/fb8e1df1-b9eb-4cc4-8859-28ab2922b84a
-- title:
--   DeepONets, their error decomposition and covariance-operator projections
-- statement:
--   Objects of Sections 2 and 3 of Lanthaler, Mishra and Karniadakis (arXiv:2102.09618v3).
--
--   1. **ReLU networks (Section 2.1, eqs. (2.1)-(2.3)).** A ReLU network $\mathbb{R}^{d_{in}}\to\mathbb{R}^{d_{out}}$ is $C_K\circ\sigma\circ C_{K-1}\circ\cdots\circ\sigma\circ C_1$ with $K\ge2$ affine maps $C_kz=W_kz+b_k$, $W_k\in\mathbb{R}^{d_{k+1}\times d_k}$, $d_1=d_{in}$, $d_{K+1}=d_{out}$, and $\sigma(z)=\max(z,0)$ applied componentwise.
--   2. **DeepONets (Section 2.2, eqs. (2.7)-(2.10), Definition 2.4).** For sensors $x_1,\dots,x_m\in D$ the encoder is $\mathcal{E}(u)=(u(x_1),\dots,u(x_m))$. The approximator is a ReLU network $\mathcal{A}:\mathbb{R}^m\to\mathbb{R}^p$. Trunk functions $\tau_0,\dots,\tau_p$ induce the reconstructor $\mathcal{R}(\alpha)=\tau_0+\sum_{k=1}^p\alpha_k\tau_k$. The DeepONet is $\mathcal{N}=\mathcal{R}\circ\mathcal{A}\circ\mathcal{E}$. When the trunk functions come from a ReLU network $\boldsymbol\tau:\mathbb{R}^n\to\mathbb{R}^{p+1}$, they are viewed as elements of $L^2(U)$.
--   3. **Data (Definition 2.1).** $D\subset\mathbb{R}^d$ and $U\subset\mathbb{R}^n$ are bounded measurable sets carrying Lebesgue measure. $X$ is a normed space (the theorems add completeness and separability as separate assumptions) with a continuous linear injection $\iota:X\to L^2(D)$, and $\mu$ is a Borel probability measure on $X$ with $\int\|u\|_X^2\,d\mu<\infty$. A Borel set $A\subset X$ with $\mu(A)=1$ consists of elements whose image in $L^2(D)$ has a representative that is continuous on $D$. Finally $\mathcal{G}:X\to L^2(U)$ is Borel measurable with $\int\|\mathcal{G}(u)\|^2_{L^2(U)}\,d\mu<\infty$.
--   4. **Errors (eqs. (2.11), (3.1)-(3.3)).** The quantities below take values in $[0,\infty]$:
--    - total error: $\widehat{\mathcal{E}}=(\int\|\mathcal{G}(u)-\mathcal{N}(u)\|^2_{L^2(U)}d\mu)^{1/2}$;
--    - encoding error: $\widehat{\mathcal{E}}_{\mathcal{E}}=(\int\|\mathcal{D}\circ\mathcal{E}(u)-u\|_X^2d\mu)^{1/2}$;
--    - approximation error: $\widehat{\mathcal{E}}_{\mathcal{A}}=(\int\|\mathcal{A}(y)-\mathcal{P}\circ\mathcal{G}\circ\mathcal{D}(y)\|^2_{\ell^2}d(\mathcal{E}_\#\mu)(y))^{1/2}$;
--    - reconstruction error: $\widehat{\mathcal{E}}_{\mathcal{R}}=(\int\|\mathcal{R}\circ\mathcal{P}(v)-v\|^2d\nu(v))^{1/2}$, with $\nu=\mathcal{G}_\#\mu$ in the paper.
--   5. **Lipschitz and Hölder constants (Section 3.2.1).** $\mathrm{Lip}(F)=\sup_{u,u'}\|F(u)-F(u')\|/\|u-u'\|$ and $\mathrm{Lip}_\alpha(\mathcal{G})=\sup_{u,u'\in A}\|\mathcal{G}(u)-\mathcal{G}(u')\|/\|u-u'\|^\alpha$, both with values in $[0,\infty]$.
--   6. **Measures on a Hilbert space $H$ (Section 3.3).** $\nu\in\mathcal{P}_2(H)$ means a probability measure with $\int\|v\|^2d\nu<\infty$. Its mean is $\mathbb{E}[v]=\int v\,d\nu$. The uncentered covariance operator is $\overline\Gamma w=\int\langle v,w\rangle v\,d\nu$ and the covariance operator is $\Gamma w=\int\langle v-\mathbb{E}[v],w\rangle(v-\mathbb{E}[v])\,d\nu$. A spectral decomposition $\Gamma=\sum_k\lambda_k\,\phi_k\otimes\phi_k$ consists of an orthonormal sequence $(\phi_k)$ and a non-increasing sequence $(\lambda_k)$ with $\Gamma w=\sum_k\lambda_k\langle\phi_k,w\rangle\phi_k$ for all $w$. The span of the eigenvectors with eigenvalue in a set $S$ is also defined.
--   7. **Projection errors (eqs. (3.13), (3.16)).** $\widehat{\mathcal{E}}_{\mathrm{Proj}}(S)=\int\inf_{w\in S}\|v-w\|^2d\nu(v)\in[0,\infty]$. A linear subspace $V$ with $\dim V=p$ is optimal if it minimizes this error among $p$-dimensional linear subspaces. An affine subspace is optimal if it minimizes the error among affine subspaces whose direction is $p$-dimensional.
--   8. **Optimal projector and reconstruction (eqs. (3.19), (3.21)).** For linearly independent $\tau_1,\dots,\tau_p$, the dual basis is $\tau_k^*=\sum_j(\mathrm{Gram}^{-1})_{kj}\tau_j$, and the projector is $\mathcal{P}(u)=(\langle u-\tau_0,\tau_k^*\rangle)_{k=1}^p$. The optimal trunk functions are $\hat\tau_0=\mathbb{E}_\nu[v]$ and $\hat\tau_k=\phi_k$.
--
--   **Formalization Note** The output space $Y$ is identified with its image in $L^2(U)$, as in Section 2.2 of the paper; every result uses only the $L^2(U)$ norm on the output side. Eigenvalues are indexed from $0$, so the paper's $\lambda_k$ is `lam (k-1)` and the tail $\sum_{k>p}\lambda_k$ is `∑' k, lam (k + p)`. Square roots and integrals of nonnegative quantities are taken in $[0,\infty]$. The function `toL2` returns $0$ for a function that is not square integrable on $U$; it is used only for ReLU networks on a compact $U$, which are always square integrable there.
-- source:
--   Lanthaler, Mishra and Karniadakis, Error estimates for DeepOnets: A deep learning framework in infinite dimensions, arXiv:2102.09618v3 (2022), Section 2.1 eqs. (2.1)-(2.3); Section 2.2, Definitions 2.1 and 2.4, eqs. (2.7)-(2.11); Section 3.2, eqs. (3.1)-(3.3), (3.8); Section 3.3, eqs. (3.13)-(3.18); Section 3.4, eqs. (3.19)-(3.23), Proposition 3.15

import Mathlib

/-!
Lanthaler, Mishra and Karniadakis, *Error estimates for DeepOnets: A deep learning framework in
infinite dimensions*, arXiv:2102.09618v3 (2022): ReLU networks (Section 2.1), DeepONets and the
data of the approximation problem (Section 2.2, Definitions 2.1 and 2.4, eqs. (2.7)-(2.11)), the
encoding, approximation and reconstruction errors (Section 3.2.1, eqs. (3.1)-(3.3)), Lipschitz and
Hoelder constants (Section 3.2.1), covariance operators and projection errors (Sections 3.2.2 and
3.3, eqs. (3.8), (3.13)-(3.18)) and the optimal projector and reconstruction (Section 3.4,
eqs. (3.19)-(3.23)).
-/

open MeasureTheory

noncomputable section

namespace DeepONetError

/-- Eq. (2.2): the ReLU activation `sigma(z) = max(z, 0)`. -/
def relu (z : ℝ) : ℝ := max z 0

/-- Section 2.1, eqs. (2.1)-(2.3): a ReLU network `C_K ∘ sigma ∘ C_{K-1} ∘ ... ∘ sigma ∘ C_1`
from `ℝ^din` to `ℝ^dout` with `K = L + 1` affine maps `C_k z = W_k z + b_k` and `L = K - 1 ≥ 1`
hidden layers. The layer widths are `width 0 = din, width 1, ..., width (L+1) = dout`; the affine
map number `k` (counting from `0`) goes from `ℝ^(width k)` to `ℝ^(width (k+1))`. -/
structure ReLUNet (din dout : ℕ) where
  /-- The number `L = K - 1` of hidden layers. -/
  L : ℕ
  /-- The paper requires `1 < K`. -/
  one_le_L : 1 ≤ L
  /-- The layer widths `d_1, ..., d_{K+1}` (here indexed from `0`). -/
  width : ℕ → ℕ
  width_zero : width 0 = din
  width_last : width (L + 1) = dout
  /-- The weight matrices `W_k`. -/
  W : (k : ℕ) → Matrix (Fin (width (k + 1))) (Fin (width k)) ℝ
  /-- The bias vectors `b_k`. -/
  b : (k : ℕ) → Fin (width (k + 1)) → ℝ

/-- Eq. (2.1): the output `sigma ∘ C_k ∘ ... ∘ sigma ∘ C_1 (x)` of the first `k` layers of a ReLU
network (the input itself for `k = 0`). -/
def ReLUNet.hidden {din dout : ℕ} (N : ReLUNet din dout) (x : Fin din → ℝ) :
    (k : ℕ) → Fin (N.width k) → ℝ
  | 0 => fun i => x (Fin.cast N.width_zero i)
  | k + 1 => fun i => relu ((N.W k).mulVec (N.hidden x k) i + N.b k i)

/-- Eq. (2.1): the function `ℝ^din → ℝ^dout` realized by a ReLU network; the last affine map
`C_K` is not followed by an activation. -/
def ReLUNet.eval {din dout : ℕ} (N : ReLUNet din dout) (x : Fin din → ℝ) : Fin dout → ℝ :=
  fun i => (N.W N.L).mulVec (N.hidden x N.L) (Fin.cast N.width_last.symm i) +
    N.b N.L (Fin.cast N.width_last.symm i)

/-- The Hilbert space `L^2(U)` for a set `U ⊆ ℝ^n` with Lebesgue measure (Section 2.2). -/
abbrev L2 {n : ℕ} (U : Set (Fin n → ℝ)) : Type := Lp ℝ 2 (volume.restrict U)

open Classical in
/-- A function on `ℝ^n` viewed as an element of `L^2(U)` (Section 2.2: a trunk net restricted to
the bounded set `U` is square integrable there; the value `0` is only a default for functions
that are not square integrable on `U`). -/
def toL2 {n : ℕ} (U : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : L2 U :=
  if h : MemLp f 2 (volume.restrict U) then h.toLp f else 0

/-- Eq. (2.9): the reconstructor induced by the functions `tau_0, ..., tau_p`,
`R(alpha) = tau_0 + sum_{k=1}^p alpha_k tau_k`. Here `tau k.succ` is the paper's `tau_{k+1}`. -/
def trunkRec {F : Type*} [AddCommGroup F] [Module ℝ F] {p : ℕ} (tau : Fin (p + 1) → F)
    (a : EuclideanSpace ℝ (Fin p)) : F :=
  tau 0 + ∑ k : Fin p, a k • tau k.succ

/-- Eq. (2.10) and Definition 2.4: the DeepONet `N = R ∘ A ∘ E` on continuous input functions
`u ∈ C(D)`, with sensors `x_1, ..., x_m ∈ D` (encoder (2.7), `E(u) = (u(x_1), ..., u(x_m))`),
an approximator ReLU network `A : ℝ^m → ℝ^p` (eq. (2.8)) and a trunk ReLU network
`tau : ℝ^n → ℝ^(p+1)` (Section 2.2), with values in `L^2(U)`. -/
def deepONet {d n m p : ℕ} {Dset : Set (Fin d → ℝ)} (U : Set (Fin n → ℝ)) (x : Fin m → Dset)
    (Apx : ReLUNet m p) (trunk : ReLUNet n (p + 1)) (u : C(Dset, ℝ)) : L2 U :=
  trunkRec (fun k => toL2 U (fun y => trunk.eval y k))
    (WithLp.toLp 2 (Apx.eval (fun j => u (x j))))

/-- Definition 2.1 (data for the DeepONet approximation problem), with the output space `Y`
identified with its image in `L^2(U)` as in Section 2.2: `D ⊆ ℝ^d` and `U ⊆ ℝ^n` are bounded
(measurable) sets, `iota : X → L^2(D)` is a continuous linear embedding, `mu` is a Borel probability
measure on `X` with finite second moment, there is a Borel set `A` with `mu(A) = 1` consisting of
(elements whose image in `L^2(D)` has a representative that is) continuous functions on `D`, and
`G` is Borel measurable with `∫ ‖G(u)‖²_{L^2(U)} dmu < ∞`. -/
def IsDeepONetData {d n : ℕ} (Dset : Set (Fin d → ℝ)) (U : Set (Fin n → ℝ)) {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [MeasurableSpace (L2 U)]
    (iota : X →L[ℝ] L2 Dset) (mu : Measure X) (A : Set X) (G : X → L2 U) : Prop :=
  Bornology.IsBounded Dset ∧ MeasurableSet Dset ∧ Bornology.IsBounded U ∧ MeasurableSet U ∧
    Function.Injective iota ∧ IsProbabilityMeasure mu ∧ (∫⁻ u, ‖u‖ₑ ^ 2 ∂mu) < ⊤ ∧
    MeasurableSet A ∧ mu A = 1 ∧
    (∀ u ∈ A, ∃ f : (Fin d → ℝ) → ℝ, ContinuousOn f Dset ∧
      ((iota u : L2 Dset) : (Fin d → ℝ) → ℝ) =ᵐ[volume.restrict Dset] f) ∧
    Measurable G ∧ (∫⁻ u, ‖G u‖ₑ ^ 2 ∂mu) < ⊤

/-- Eq. (2.11): the DeepONet error `(∫_X ‖G(u) - N(u)‖²_{L^2(U)} dmu(u))^{1/2}`, valued in
`[0, ∞]`. -/
def totalErr {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] (mu : Measure X)
    (G N : X → F) : ENNReal :=
  (∫⁻ u, ‖G u - N u‖ₑ ^ 2 ∂mu) ^ ((1 : ℝ) / 2)

/-- Eq. (3.1): the encoding error `(∫_X ‖D(E(u)) - u‖²_X dmu(u))^{1/2}` of an encoder `E` and a
decoder `D`. -/
def encErr {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] {m : ℕ} (mu : Measure X)
    (E : X → EuclideanSpace ℝ (Fin m)) (Dec : EuclideanSpace ℝ (Fin m) → X) : ENNReal :=
  (∫⁻ u, ‖Dec (E u) - u‖ₑ ^ 2 ∂mu) ^ ((1 : ℝ) / 2)

/-- Eq. (3.2): the approximation error
`(∫_{ℝ^m} ‖A(y) - P(G(D(y)))‖²_{ℓ^2} d(E_# mu)(y))^{1/2}`. -/
def approxErr {X F : Type*} [MeasurableSpace X] {m p : ℕ} (mu : Measure X) (G : X → F)
    (E : X → EuclideanSpace ℝ (Fin m)) (Apx : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin p))
    (Dec : EuclideanSpace ℝ (Fin m) → X) (Proj : F → EuclideanSpace ℝ (Fin p)) : ENNReal :=
  (∫⁻ y, ‖Apx y - Proj (G (Dec y))‖ₑ ^ 2 ∂(mu.map E)) ^ ((1 : ℝ) / 2)

/-- Eq. (3.3): the reconstruction error `(∫ ‖R(P(v)) - v‖² dnu(v))^{1/2}` of a reconstructor `R`
and a projector `P` with respect to a measure `nu` on the output space (in the paper
`nu = G_# mu`). -/
def recErr {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] {p : ℕ} (nu : Measure F)
    (R : EuclideanSpace ℝ (Fin p) → F) (Proj : F → EuclideanSpace ℝ (Fin p)) : ENNReal :=
  (∫⁻ v, ‖R (Proj v) - v‖ₑ ^ 2 ∂nu) ^ ((1 : ℝ) / 2)

/-- Section 3.2.1: the Lipschitz constant `Lip(F) = sup_{u,u'} ‖F(u) - F(u')‖ / ‖u - u'‖`, valued
in `[0, ∞]` (pairs with `u = u'` contribute `0`). -/
def lipConst {α β : Type*} [EMetricSpace α] [EMetricSpace β] (f : α → β) : ENNReal :=
  ⨆ x, ⨆ y, edist (f x) (f y) / edist x y

/-- Section 3.2.1 and the proof of Theorem 3.3 (Appendix C.2): the Hoelder constant
`Lip_alpha(G : A → L^2(U)) = sup_{u,u' ∈ A} ‖G(u) - G(u')‖ / ‖u - u'‖^alpha` of `G` on `A`,
valued in `[0, ∞]`. -/
def holderConst {α β : Type*} [EMetricSpace α] [EMetricSpace β] (alpha : ℝ) (f : α → β)
    (A : Set α) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, edist (f x) (f y) / edist x y ^ alpha

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]

/-- Definition 2.1 and Section 3.3: `nu ∈ P_2(H)`, a probability measure with finite second
moment `∫ ‖v‖² dnu(v) < ∞`. -/
def IsP2 (nu : Measure H) : Prop :=
  IsProbabilityMeasure nu ∧ (∫⁻ v, ‖v‖ₑ ^ 2 ∂nu) < ⊤

/-- Section 3.2.2: the mean `E[v] = ∫ v dnu(v)`. -/
def mean (nu : Measure H) : H := ∫ v, v ∂nu

/-- Eq. (3.14): the uncentered covariance operator `w ↦ ∫ ⟨v, w⟩ v dnu(v)`, i.e.
`∫ v ⊗ v dnu(v)`. -/
def uncovOp (nu : Measure H) (w : H) : H := ∫ v, inner ℝ v w • v ∂nu

/-- Eqs. (3.8) and (3.18): the covariance operator
`w ↦ ∫ ⟨v - E[v], w⟩ (v - E[v]) dnu(v)`, i.e. `∫ (v - E[v]) ⊗ (v - E[v]) dnu(v)`. -/
def covOp (nu : Measure H) (w : H) : H :=
  ∫ v, inner ℝ (v - mean nu) w • (v - mean nu) ∂nu

/-- Proposition 3.15 (and the eigenvalue convention of Theorems 3.6, 3.8, 3.10, 3.12, 3.14):
`Gamma = sum_k lam_k (phi_k ⊗ phi_k)` with an orthonormal family `phi` and decreasing `lam`, i.e.
`Gamma w = sum_k lam_k ⟨phi_k, w⟩ phi_k` for every `w`. Then `lam_0 ≥ lam_1 ≥ ...` are the
eigenvalues of `Gamma` repeated according to multiplicity (the paper's `lam_1 ≥ lam_2 ≥ ...`,
indexed here from `0`). -/
def IsSpectralDecomp (Gamma : H → H) (lam : ℕ → ℝ) (phi : ℕ → H) : Prop :=
  Orthonormal ℝ phi ∧ Antitone lam ∧
    ∀ w, HasSum (fun k => (lam k * inner ℝ (phi k) w) • phi k) (Gamma w)

/-- Theorems 3.10 and 3.12: the span of the eigenvectors of `Gamma` whose eigenvalue lies in
`S`; for `S = (c, ∞)` or `[c, ∞)` this is the direct sum of the corresponding eigenspaces
`E_j`. -/
def eigSpan (Gamma : H → H) (S : Set ℝ) : Submodule ℝ H :=
  Submodule.span ℝ {v | ∃ c ∈ S, Gamma v = c • v}

/-- Eqs. (3.13) and (3.16): the projection error `∫ inf_{w ∈ S} ‖v - w‖² dnu(v)` of a set `S`
(a linear or affine subspace), valued in `[0, ∞]`. -/
def projErr (nu : Measure H) (S : Set H) : ENNReal :=
  ∫⁻ v, Metric.infEDist v S ^ 2 ∂nu

/-- Theorem 3.10: `V` is an optimal `p`-dimensional subspace, i.e. `dim V = p` and `V` minimizes
the projection error among all `p`-dimensional linear subspaces. -/
def IsOptimalSubspace (nu : Measure H) (p : ℕ) (V : Submodule ℝ H) : Prop :=
  Module.finrank ℝ V = p ∧
    ∀ W : Submodule ℝ H, Module.finrank ℝ W = p → projErr nu (V : Set H) ≤ projErr nu (W : Set H)

/-- Theorem 3.12: `V0` is an optimal `p`-dimensional affine subspace, i.e. its direction has
dimension `p` and `V0` minimizes the projection error among all affine subspaces whose direction
has dimension `p`. -/
def IsOptimalAffine (nu : Measure H) (p : ℕ) (V0 : AffineSubspace ℝ H) : Prop :=
  Module.finrank ℝ V0.direction = p ∧
    ∀ W : AffineSubspace ℝ H, Module.finrank ℝ W.direction = p → projErr nu (V0 : Set H) ≤ projErr nu (W : Set H)

/-- The Gram matrix `(⟨v_i, v_j⟩)_{i,j}` of a finite family. -/
def gram {p : ℕ} (v : Fin p → H) : Matrix (Fin p) (Fin p) ℝ := fun i j => inner ℝ (v i) (v j)

/-- Lemma 3.13: the dual basis `v*_k = sum_j (Gram^{-1})_{kj} v_j` of linearly independent
`v_1, ..., v_p`, the unique elements of their span with `⟨v_l, v*_k⟩ = delta_{lk}`. -/
def dualBasis {p : ℕ} (v : Fin p → H) (k : Fin p) : H :=
  ∑ j, (gram v)⁻¹ k j • v j

/-- Eq. (3.19): the projector associated with the reconstructor of `tau_0, ..., tau_p`,
`P(u) = (⟨u - tau_0, tau*_1⟩, ..., ⟨u - tau_0, tau*_p⟩)`. -/
def optProj {p : ℕ} (tau : Fin (p + 1) → H) (u : H) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (fun k => inner ℝ (u - tau 0) (dualBasis (fun j => tau j.succ) k))

/-- Eq. (3.21) and Proposition 3.15: the functions of the optimal reconstruction,
`hat tau_0 = E[v]` and `hat tau_k = phi_k` (the paper's `phi_k`, `k = 1, ..., p`, is `phi (k-1)`
here). -/
def optTrunk {p : ℕ} (nu : Measure H) (phi : ℕ → H) (k : Fin (p + 1)) : H :=
  Fin.cases (motive := fun _ => H) (mean nu) (fun j : Fin p => phi j) k

end Hilbert

end DeepONetError


