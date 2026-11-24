-- Prove2me | Definitions.Def_SteerableE2CNN_Basic
-- name    : SteerableE2CNN_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T09:37:09.968044+00:00
-- url     : https://prove2.me/theorems/58dc5bdc-34b0-4f1b-b4a4-17632577a4b7
-- title:
--   Feature fields, kernel constraints, nonlinearities and SO(2)/O(2) kernel bases of E(2)-steerable CNNs
-- statement:
--   Objects of Sections 2.1-2.6 and Appendices B, D and F of Weiler and Cesa (2019).
--
--   1. **Plane and symmetry groups.** The plane is $\mathbb{R}^2$ with Lebesgue measure. $\mathrm{O}(2)=\{O\in\mathbb{R}^{2\times2}\mid O^\top O=I\}$, and $G\le\mathrm{O}(2)$ is any subgroup, acting on $\mathbb{R}^2$ by matrix multiplication.
--   2. **Representations.** A representation of a group $G$ on $\mathbb{R}^n$ is a homomorphism $\rho:G\to\mathrm{GL}(\mathbb{R}^n)$. It is irreducible if $\mathbb{R}^n\neq0$ and the only $\rho$-invariant subspaces are $0$ and $\mathbb{R}^n$.
--   3. **Feature fields (eq. 1).** A field $f:\mathbb{R}^2\to\mathbb{R}^n$ of type $\rho$ transforms under $tg\in(\mathbb{R}^2,+)\rtimes G$ by $([\operatorname{Ind}\rho](tg)f)(x)=\rho(g)\,f(g^{-1}(x-t))$.
--   4. **Kernel constraint (eqs. 2, 3).** A kernel $k:\mathbb{R}^2\to\mathbb{R}^{m\times n}$ satisfies the constraint for output and input matrices $\rho_{\mathrm{out}}(g)$, $\rho_{\mathrm{in}}(g)$ if $k(gx)=\rho_{\mathrm{out}}(g)\,k(x)\,\rho_{\mathrm{in}}(g)^{-1}$ for all group elements $g$ and all $x\in\mathbb{R}^2$. It is $G$-steerable when $g$ ranges over $G\le\mathrm{O}(2)$ and $\rho_{\mathrm{in}},\rho_{\mathrm{out}}$ are representations of $G$.
--   5. **Convolution (Appendix D.1).** $(k\star f)(x)=\int_{\mathbb{R}^2}k(y)\,f(x+y)\,dy$.
--   6. **Irrep blocks (Section 2.4).** For irreps $\psi_i$ ($i\in I_{\mathrm{out}}$) of dimensions $d_i$, a matrix indexed by $\bigsqcup_i\{1,\dots,d_i\}$ and $\bigsqcup_j\{1,\dots,d_j\}$ has blocks $\kappa^{ij}\in\mathbb{R}^{d_i\times d_j}$. The direct sum $\bigoplus_i\psi_i(g)$ is the block-diagonal matrix.
--   7. **Nonlinearities (Section 2.6, Appendix D.2).** $|v|=(\sum_iv_i^2)^{1/2}$. The norm nonlinearity is $\sigma_{\mathrm{norm}}(v)=\eta(|v|)\,v/|v|$. The quotient representation of a finite group $G$ with subgroup $H$ acts on $\mathbb{R}^{G/H}$ by $\rho_{\mathrm{quot}}(\tilde g)e_{gH}=e_{\tilde ggH}$. The regular representation of $C_N$ acts on $\mathbb{R}^{\mathbb{Z}/N}$ by $\rho_{\mathrm{reg}}(\tilde p)e_p=e_{\tilde p+p}$. The vector field nonlinearity is $\sigma_{\mathrm{vec}}(f)=\max(f)\,(\cos\theta,\sin\theta)^\top$ with $\theta=2\pi\arg\max(f)/N$.
--   8. **Rotations, reflections, polar coordinates (Appendix F.1).** $\psi(\theta)$ is the rotation matrix by $\theta$ and $\xi(s)=\mathrm{diag}(1,s)$ for $s\in\{\pm1\}$. The element $r_\theta s\in\mathrm{O}(2)$ is the matrix $\psi(\theta)\xi(s)$, and $x(r,\phi)=(r\cos\phi,r\sin\phi)$.
--   9. **Irreps of SO(2) and O(2) (Appendix F.2).** $\psi^{\mathrm{SO}(2)}_0(r_\theta)=1$ and $\psi^{\mathrm{SO}(2)}_k(r_\theta)=\psi(k\theta)$ for $k\ge1$. $\psi^{\mathrm{O}(2)}_{i,0}(r_\theta s)=s^i$ for $i\in\{0,1\}$, and $\psi^{\mathrm{O}(2)}_{1,k}(r_\theta s)=\psi(k\theta)\xi(s)$ for $k\ge1$.
--   10. **Angular kernel bases (Tables 8 and 2, Appendix F.4).** For each pair of irreps there is a finite list of angular functions $b(\phi)$, each of one integer angular frequency $\mu$:
--      - $\mathrm{SO}(2)$, $\psi_m\leftarrow\psi_n$: $[1]$ if $m=n=0$; $[\cos(n\phi+\gamma),\sin(n\phi+\gamma)]$ if $m=0<n$; $[\cos(m\phi+\gamma);\sin(m\phi+\gamma)]$ if $n=0<m$; $\psi((m-sn)\phi+\gamma)\xi(s)$ if $m,n>0$. Here $\gamma\in\{0,\pi/2\}$ and $s\in\{\pm1\}$.
--      - $\mathrm{O}(2)$, $\psi_{j,n}\to\psi_{i,m}$: $[1]$ if $m=n=0$ and $i=j$, and nothing if $m=n=0$ and $i\neq j$; $[\cos(n\phi+i\pi/2),\sin(n\phi+i\pi/2)]$ if $m=0<n$; $[\cos(m\phi+j\pi/2);\sin(m\phi+j\pi/2)]$ if $n=0<m$; $\psi((m-n)\phi)$ and $\psi((m+n)\phi)\xi(-1)$ if $m,n>0$.
--
--   **Formalization Note** Points of the plane are vectors $\mathrm{Fin}\,2\to\mathbb{R}$, and feature vectors are functions on a finite index type. The kernel constraint is one definition, parametrised by an index set of group elements and by the matrices of the action and of the two representations. For $\mathrm{SO}(2)$ the group elements are the angles $\theta$, and for $\mathrm{O}(2)$ they are the pairs $(\theta,s)$. A label $(i,k)$ of an $\mathrm{O}(2)$ irrep carries the condition $k=0$ or $i=1$. The $\mathrm{O}(2)$ basis for one-dimensional/two-dimensional pairs is the one derived in Appendix F.4.3, eqs. (37) and (38). In Tables 2 and 9 the trivial and sign-flip rows and columns of these cells are interchanged. At $v=0$ the norm nonlinearity takes the value $0$, because Lean sets $a/0=0$. `argmax` is a fixed choice among the maximisers.
-- source:
--   Weiler and Cesa, General E(2)-Equivariant Steerable CNNs, arXiv:1911.08251v2 (NeurIPS 2019), Sections 2.1-2.6 (eqs. (1)-(5), Table 2), Appendix B, Appendix D, Appendix F.1-F.4 (Tables 8, 9; eqs. (24)-(38))

import Mathlib

/-!
Weiler and Cesa, *General E(2)-Equivariant Steerable CNNs*, arXiv:1911.08251v2 (NeurIPS 2019):
feature fields and their induced transformation law (Section 2.2, eq. (1)), the kernel constraint
(Section 2.3, eq. (2)) and its irrep blocks (Section 2.4, eq. (3)), steerable convolutions
(Appendix D.1), the nonlinearities of Section 2.6 and Appendix D.2 (norm, pointwise on quotient
representations, vector field), and the real irreducible representations of SO(2) and O(2) with
the angular kernel bases derived in Appendix F (Section 2.5, Tables 2, 8, 9; eqs. (24)-(38)).
-/

open Matrix MeasureTheory

noncomputable section

namespace SteerableE2CNN

/-- Section 2.1: the plane `ℝ²`, written as coordinate vectors `Fin 2 → ℝ`, with Lebesgue
measure. -/
abbrev Plane : Type := Fin 2 → ℝ

/-- Section 2.1: the orthogonal group `O(2) = {O ∈ ℝ^{2×2} | OᵀO = id}`. -/
abbrev O2 : Type := ↥(Matrix.orthogonalGroup (Fin 2) ℝ)

/-- Section 2.1: the `2 × 2` matrix of an element `g` of a subgroup `G ≤ O(2)`, acting on the
plane by `x ↦ g x`. -/
def gMat {G : Subgroup O2} (g : G) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((g : O2) : Matrix (Fin 2) (Fin 2) ℝ)

/-- Section 2.2 and Appendix B: a (real, finite-dimensional) group representation
`ρ : G → GL(ℝⁿ)`, a homomorphism into invertible matrices indexed by `n`. -/
abbrev MatRep (G : Type*) [Group G] (n : Type*) [Fintype n] [DecidableEq n] : Type _ :=
  G →* Matrix.GeneralLinearGroup n ℝ

/-- The matrix `ρ(g)` of a representation. -/
def repMat {G : Type*} [Group G] {n : Type*} [Fintype n] [DecidableEq n] (ρ : MatRep G n)
    (g : G) : Matrix n n ℝ :=
  ((ρ g : Matrix.GeneralLinearGroup n ℝ) : Matrix n n ℝ)

/-- Appendix B ("Irreducible representations"): `ρ` is irreducible if its representation space
is nonzero and has no invariant subspace other than `0` and the whole space. -/
def IsIrrep {G : Type*} [Group G] {n : Type*} [Fintype n] [DecidableEq n] (ρ : MatRep G n) :
    Prop :=
  Nonempty n ∧ ∀ W : Submodule ℝ (n → ℝ), (∀ g : G, ∀ v ∈ W, repMat ρ g *ᵥ v ∈ W) →
    W = ⊥ ∨ W = ⊤

/-- Eqs. (2) and (3): the kernel constraint `κ(g x) = ρ_out(g) κ(x) ρ_in(g)⁻¹` for all group
elements `g` and all `x ∈ ℝ²`. The group elements are indexed by `Idx`, `act g` is the matrix by
which `g` acts on the plane, and `ρout g`, `ρin g` are the matrices of the output and input
representations. -/
def KernelConstraint {Idx : Type*} {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (act : Idx → Matrix (Fin 2) (Fin 2) ℝ) (ρout : Idx → Matrix m m ℝ)
    (ρin : Idx → Matrix n n ℝ) (κ : Plane → Matrix m n ℝ) : Prop :=
  ∀ (g : Idx) (x : Plane), κ (act g *ᵥ x) = ρout g * κ x * (ρin g)⁻¹

/-- Section 2.3, eq. (2): `k : ℝ² → ℝ^{c_out × c_in}` is a `G`-steerable kernel for the input and
output field types `ρin`, `ρout` of a subgroup `G ≤ O(2)`. -/
def IsSteerable (G : Subgroup O2) {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (ρin : MatRep G n) (ρout : MatRep G m) (k : Plane → Matrix m n ℝ) : Prop :=
  KernelConstraint (fun g : G => gMat g) (repMat ρout) (repMat ρin) k

/-- Section 2.2, eq. (1): the induced representation `Ind_G^{(ℝ²,+)⋊G} ρ` acting on a feature field
`f : ℝ² → ℝ^c` of type `ρ`: `([Ind ρ](t g) f)(x) = ρ(g) f(g⁻¹(x - t))`. -/
def indAct (G : Subgroup O2) {n : Type*} [Fintype n] [DecidableEq n] (ρ : MatRep G n)
    (t : Plane) (g : G) (f : Plane → n → ℝ) : Plane → n → ℝ :=
  fun x => repMat ρ g *ᵥ f (gMat g⁻¹ *ᵥ (x - t))

/-- Appendix D.1: the convolution (correlation) of a feature field with a kernel,
`(k ⋆ f)(x) = ∫_{ℝ²} k(y) f(x + y) dy`. -/
def steerConv {m n : Type*} [Fintype m] [Fintype n] (k : Plane → Matrix m n ℝ)
    (f : Plane → n → ℝ) : Plane → m → ℝ :=
  fun x => ∫ y, k y *ᵥ f (x + y)

/-- Section 2.4: the block `κ^{ij}` of a matrix `κ` written in the irrep bases, i.e. indexed by
`Σ i, Fin (dOut i)` (output irreps `i ∈ I_out` of dimensions `dOut i`) and `Σ j, Fin (dIn j)`. -/
def kernelBlock {Iout Iin : Type*} {dOut : Iout → ℕ} {dIn : Iin → ℕ}
    (κ : Matrix (Σ i, Fin (dOut i)) (Σ j, Fin (dIn j)) ℝ) (i : Iout) (j : Iin) :
    Matrix (Fin (dOut i)) (Fin (dIn j)) ℝ :=
  Matrix.of fun a b => κ ⟨i, a⟩ ⟨j, b⟩

/-- Section 2.6 and Appendix D.2.2: the Euclidean norm `|v|` of a feature vector. -/
def eNorm {n : Type*} [Fintype n] (v : n → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- Section 2.6 and Appendix D.2.2: the norm nonlinearity `σ_norm(v) = η(|v|) v / |v|`. (At
`v = 0` Lean's convention `a / 0 = 0` gives `σ_norm(0) = 0`; the paper leaves this value
undefined.) -/
def normNL {n : Type*} [Fintype n] (η : ℝ → ℝ) (v : n → ℝ) : n → ℝ :=
  (η (eNorm v) / eNorm v) • v

open Classical in
/-- Section 2.6 and Appendix B: the quotient representation `ρ_quot^{G/H}` of a finite group `G`,
permuting the axes `e_{gH}` of `ℝ^{|G|/|H|}` by `ρ_quot(g̃) e_{gH} = e_{g̃gH}`. -/
def quotRep {G : Type*} [Group G] (H : Subgroup G) (g : G) : Matrix (G ⧸ H) (G ⧸ H) ℝ :=
  Matrix.of fun a b => if a = g • b then 1 else 0

/-- Appendix D.2.4: the regular representation of the cyclic group `C_N`, whose elements are the
rotations by `2πp/N`, `p ∈ ℤ/N`, acting on `ℝ^N` (axes `e_p`) by `ρ_reg(p̃) e_p = e_{p̃ + p}`. -/
def regRepCN (N : ℕ) (p : ZMod N) : Matrix (ZMod N) (ZMod N) ℝ :=
  Matrix.of fun q q' => if q = p + q' then 1 else 0

/-- Appendix D.2.4: an index `argmax f` of a maximal entry of `f ∈ ℝ^N` (a fixed choice among the
maximisers). -/
def vfArgmax (N : ℕ) [NeZero N] (v : ZMod N → ℝ) : ZMod N :=
  Classical.choose (Finset.exists_max_image Finset.univ v Finset.univ_nonempty)

/-- Appendix D.2.4: the vector field nonlinearity
`σ_vec(f) = max(f) (cos θ, sin θ)ᵀ` with `θ = 2π argmax(f) / N`. -/
def vecFieldNL (N : ℕ) [NeZero N] (v : ZMod N → ℝ) : Plane :=
  (Finset.univ.sup' Finset.univ_nonempty v) •
    ![Real.cos (2 * Real.pi * ((vfArgmax N v).val : ℝ) / N),
      Real.sin (2 * Real.pi * ((vfArgmax N v).val : ℝ) / N)]

/-- Appendix F.1: the rotation matrix `ψ(θ)`. -/
def rotMat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- Appendix F.1: the matrix `ξ(s) = diag(1, s)`, `s ∈ ({±1}, *)`; `ξ(-1)` is the reflection along
the horizontal axis. -/
def flipMat (s : ℤˣ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, ((s : ℤ) : ℝ)]

/-- Appendix F.1: the matrix `ψ(θ) ξ(s)` of the element `g = r_θ s` of `O(2)`; it acts on polar
coordinates by `g.x(r, φ) = x(r, sφ + θ)`. Every element of `O(2)` is of this form. -/
def o2Elem (θ : ℝ) (s : ℤˣ) : Matrix (Fin 2) (Fin 2) ℝ := rotMat θ * flipMat s

/-- Section 2.5 and Appendix F.1: the point `x(r, φ) = (r cos φ, r sin φ)` with polar
coordinates `(r, φ)`. -/
def polar (r φ : ℝ) : Plane := ![r * Real.cos φ, r * Real.sin φ]

/-- Appendix F.2: the dimension of the real irrep `ψ_k` of `SO(2)` of frequency `k ∈ ℕ`
(`1` for `k = 0`, `2` otherwise). -/
def so2Dim : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 2

/-- Appendix F.2: the real irreps of `SO(2)` evaluated at the rotation `r_θ`:
`ψ_0(r_θ) = 1` and `ψ_k(r_θ) = ψ(kθ)` for `k ≥ 1`. -/
def so2Irrep : (k : ℕ) → ℝ → Matrix (Fin (so2Dim k)) (Fin (so2Dim k)) ℝ
  | 0 => fun _ => 1
  | k + 1 => fun θ => rotMat (((k + 1 : ℕ) : ℝ) * θ)

/-- Table 8: the number of angular basis elements of `SO(2)`-steerable kernels from `ψ_n` to
`ψ_m`. -/
def so2BasisCard : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 2
  | _ + 1, 0 => 2
  | _ + 1, _ + 1 => 4

/-- Table 8 and eqs. (24), (26), (28), (29): the angular basis of `SO(2)`-steerable kernels
`κ : ℝ² → ℝ^{dim ψ_m × dim ψ_n}` for input irrep `ψ_n` and output irrep `ψ_m`:
* `m = n = 0`: `[1]` (eq. (26));
* `m = 0 < n`: `[cos(nφ + γ), sin(nφ + γ)]`, `γ ∈ {0, π/2}` (eq. (29));
* `n = 0 < m`: `[cos(mφ + γ); sin(mφ + γ)]`, `γ ∈ {0, π/2}` (eq. (28));
* `m, n > 0`: `ψ(μφ + γ) ξ(s)` with `μ = m - sn`, `γ ∈ {0, π/2}`, `s ∈ {±1}` (eq. (24)); the index
  `b ∈ {0,1,2,3}` encodes `γ = (b mod 2) π/2` and `s = 1` for `b < 2`, `s = -1` otherwise. -/
def so2Basis : (m n : ℕ) → Fin (so2BasisCard m n) → ℝ →
    Matrix (Fin (so2Dim m)) (Fin (so2Dim n)) ℝ
  | 0, 0 => fun _ _ => 1
  | 0, n + 1 => fun b φ =>
      !![Real.cos (((n + 1 : ℕ) : ℝ) * φ + ((b : ℕ) : ℝ) * (Real.pi / 2)),
        Real.sin (((n + 1 : ℕ) : ℝ) * φ + ((b : ℕ) : ℝ) * (Real.pi / 2))]
  | m + 1, 0 => fun b φ =>
      !![Real.cos (((m + 1 : ℕ) : ℝ) * φ + ((b : ℕ) : ℝ) * (Real.pi / 2));
        Real.sin (((m + 1 : ℕ) : ℝ) * φ + ((b : ℕ) : ℝ) * (Real.pi / 2))]
  | m + 1, n + 1 => fun b φ =>
      rotMat ((((m + 1 : ℕ) : ℝ) - (if (b : ℕ) < 2 then 1 else -1) * ((n + 1 : ℕ) : ℝ)) * φ
          + (((b : ℕ) % 2 : ℕ) : ℝ) * (Real.pi / 2)) *
        flipMat (if (b : ℕ) < 2 then 1 else -1)

/-- Table 8: the angular frequency `μ` of each basis element of `so2Basis m n`. -/
def so2BasisFreq : (m n : ℕ) → Fin (so2BasisCard m n) → ℤ
  | 0, 0 => fun _ => 0
  | 0, n + 1 => fun _ => (n + 1 : ℕ)
  | m + 1, 0 => fun _ => (m + 1 : ℕ)
  | m + 1, n + 1 => fun b =>
      ((m + 1 : ℕ) : ℤ) - (if (b : ℕ) < 2 then 1 else -1) * ((n + 1 : ℕ) : ℤ)

/-- Appendix F.2: a label `(i, k)` of a real irrep `ψ_{i,k}` of `O(2)`: `ψ_{0,0}` (trivial),
`ψ_{1,0}` (sign of the reflection) and `ψ_{1,k}`, `k ≥ 1` (frequency `k`). -/
structure O2IrrepLabel where
  /-- the index `i ∈ {0, 1}` -/
  i : Fin 2
  /-- the frequency `k ∈ ℕ` -/
  k : ℕ
  /-- `ψ_{0,k}` is an irrep only for `k = 0` -/
  valid : k = 0 ∨ i = 1

/-- Appendix F.2: the dimension of `ψ_{i,k}` (`1` for `k = 0`, `2` otherwise). -/
def o2Dim (l : O2IrrepLabel) : ℕ :=
  match l.k with
  | 0 => 1
  | _ + 1 => 2

/-- Appendix F.2: the real irreps of `O(2)` evaluated at `g = r_θ s`:
`ψ_{i,0}(r_θ s) = s^i` and `ψ_{1,k}(r_θ s) = ψ(kθ) ξ(s)` for `k ≥ 1`. -/
def o2Irrep : (l : O2IrrepLabel) → ℝ → ℤˣ → Matrix (Fin (o2Dim l)) (Fin (o2Dim l)) ℝ
  | ⟨i, 0, _⟩ => fun _ s => !![((s : ℤ) : ℝ) ^ (i : ℕ)]
  | ⟨_, k + 1, _⟩ => fun θ s => rotMat (((k + 1 : ℕ) : ℝ) * θ) * flipMat s

/-- Table 2 / Table 9 (as derived in eqs. (34), (35), (37), (38)): the number of angular basis
elements of `O(2)`-steerable kernels from `ψ_{j,n}` to `ψ_{i,m}`. -/
def o2BasisCard (l l' : O2IrrepLabel) : ℕ :=
  match l.k, l'.k with
  | 0, 0 => if l.i = l'.i then 1 else 0
  | 0, _ + 1 => 1
  | _ + 1, 0 => 1
  | _ + 1, _ + 1 => 2

/-- Section 2.5, Table 2, and Appendix F.4.3, eqs. (34), (35), (37), (38): the angular basis of
`O(2)`-steerable kernels for input irrep `ψ_{j,n}` and output irrep `ψ_{i,m}`, as derived in
Appendix F.4.3:
* `m = n = 0`: `[1]` if `i = j`, no element otherwise (eq. (35));
* `m = 0 < n`: `[cos(nφ + iπ/2), sin(nφ + iπ/2)]` (eq. (38));
* `n = 0 < m`: `[cos(mφ + jπ/2); sin(mφ + jπ/2)]` (eq. (37));
* `m, n > 0`: `ψ(μφ) ξ(s)` with `μ = m - sn`, `s ∈ {±1}`, i.e. `ψ((m-n)φ)` and `ψ((m+n)φ) ξ(-1)`
  (eq. (34)). -/
def o2Basis : (l l' : O2IrrepLabel) → Fin (o2BasisCard l l') → ℝ →
    Matrix (Fin (o2Dim l)) (Fin (o2Dim l')) ℝ
  | ⟨_, 0, _⟩, ⟨_, 0, _⟩ => fun _ _ => !![(1 : ℝ)]
  | ⟨i, 0, _⟩, ⟨_, n + 1, _⟩ => fun _ φ =>
      !![Real.cos (((n + 1 : ℕ) : ℝ) * φ + ((i : ℕ) : ℝ) * (Real.pi / 2)),
        Real.sin (((n + 1 : ℕ) : ℝ) * φ + ((i : ℕ) : ℝ) * (Real.pi / 2))]
  | ⟨_, m + 1, _⟩, ⟨j, 0, _⟩ => fun _ φ =>
      !![Real.cos (((m + 1 : ℕ) : ℝ) * φ + ((j : ℕ) : ℝ) * (Real.pi / 2));
        Real.sin (((m + 1 : ℕ) : ℝ) * φ + ((j : ℕ) : ℝ) * (Real.pi / 2))]
  | ⟨_, m + 1, _⟩, ⟨_, n + 1, _⟩ => fun b φ =>
      rotMat ((((m + 1 : ℕ) : ℝ) - (if (b : ℕ) = 0 then 1 else -1) * ((n + 1 : ℕ) : ℝ)) * φ) *
        flipMat (if (b : ℕ) = 0 then 1 else -1)

/-- Table 2: the angular frequency `μ` of each basis element of `o2Basis l l'`. -/
def o2BasisFreq : (l l' : O2IrrepLabel) → Fin (o2BasisCard l l') → ℤ
  | ⟨_, 0, _⟩, ⟨_, 0, _⟩ => fun _ => 0
  | ⟨_, 0, _⟩, ⟨_, n + 1, _⟩ => fun _ => (n + 1 : ℕ)
  | ⟨_, m + 1, _⟩, ⟨_, 0, _⟩ => fun _ => (m + 1 : ℕ)
  | ⟨_, m + 1, _⟩, ⟨_, n + 1, _⟩ => fun b =>
      ((m + 1 : ℕ) : ℤ) - (if (b : ℕ) = 0 then 1 else -1) * ((n + 1 : ℕ) : ℤ)

end SteerableE2CNN


