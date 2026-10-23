-- Prove2me | Definitions.Def_OrbNetEqui_Equivariance_Basic
-- name    : OrbNetEqui_Equivariance_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:08.841562+00:00
-- url     : https://prove2.me/theorems/a36838b4-2c84-4fe4-960d-2329d4e06152
-- title:
--   S2.3–S2.5 and Methods 1.1, pp. 7–10, 23–26 — unitary representations, N-body tensors and the local action (S26), the UNiTE building blocks (S31), (S36)–(S45) and the network
-- statement:
--   This module fixes the objects of Appendix S2 and Methods 1.1 of Qiao et al.
--
--   **Representations.** $K$ is a group (standing for $\mathrm U(n)$, or $\mathrm O(3)$ in the experiments). A unitary matrix representation is a homomorphism $\rho : K \to \mathrm U(m)$. It is *irreducible* (`IsIrreducibleUnitary`) when $m > 0$ and the only subspaces of $\mathbb C^m$ invariant under every $\rho(k)$ are $0$ and $\mathbb C^m$. A family $(U^L)_{L\in\Lambda}$ of representations on $\mathbb V^L = \mathbb C^{\dim L}$ is a *complete catalogue* (`CatalogComplete`) when every irreducible unitary representation of $K$ is intertwined, by a linear isomorphism, with some $U^L$.
--
--   **Tensors and actions.** For matrices $A_1,\dots,A_N$, `tensorProdAct` is $(A_1\otimes\cdots\otimes A_N)T$, i.e. $p\mapsto\sum_q \prod_j (A_j)_{p_j q_j} T(q)$, and `diagAct A` is the diagonal case $A\otimes\cdots\otimes A$ (eq. (S27)). `labelRep` is the block-diagonal matrix $\pi^2(k)=\bigoplus_a U^{\mathrm{lab}(a)}_k$ on $V_u\simeq\bigoplus_a\mathbb V^{\mathrm{lab}(a)}$ (Definition S2), and `coeffMap Q` is the linear map (S31) $\psi(T)_{\nu,L,M}=\sum_{\vec v}T(\vec v)\,Q^{\vec v}_{\nu,L,M}$.
--
--   There are $d$ atoms $u$, each with a finite local basis $\{e_{u;v}\}_{v\in\iota_u}$; the concatenated basis is `Orb ι` $=\{(u,v)\}$. An N-body tensor of order $N=n+1$ is a function $T$ of $N$ concatenated indices. Given representations $\pi^1_u : K\to\mathrm U(\iota_u)$ and $g=(g_u)_u$, the local action (S26) `tensorAct` rotates every index in atom $u$'s block by $\pi^1_u(g_u)$; on the sub-tensor $T_{\vec u}$ it is $(\pi^1(g_{u_1})\otimes\cdots\otimes\pi^1(g_{u_N}))T_{\vec u}$.
--
--   **Features.** A feature of one atom assigns to each label $L$ and channel $c<n_{\max}$ a vector in $\mathbb C^{\dim L}$; $k$ acts by $(k\cdot h)_{L,c}=U^L_k h_{L,c}$ (`featAct`).
--
--   **Building blocks.** With matching matrices $(D_u)^{L,k,M}_v=\langle e_{u;v},\pi_{u;L,k,M}\rangle$, where $k$ counts the copies of $\mathbb V^L$ in $V_u$:
--
--   1. matching layer (S44): $\rho_u(h)^i_v=\sum_{L,k,M}(D_u)^{L,k,M}_v\sum_c (W^i_{u,L})_{k,c}h_{L,c,M}$;
--   2. block convolution (S36): $(\mathbf m_{\vec u})^i_{v_1}=\sum_{v_2,\dots,v_N}T_{\vec u}(v_1,\dots,v_N)\prod_{j=2}^N\overline{\rho_{u_j}(h_{u_j})^i_{v_j}}$;
--   3. aggregation (S37): $\tilde{\mathbf m}_{u_1}=\sum_{u_2,\dots,u_N}\bigoplus_{i,j}(\mathbf m_{\vec u})^i\alpha^j_{\vec u}$;
--   4. reverse matching (S45): $\rho^\dagger_u(\tilde{\mathbf m})_{L,c,M}=\sum_{k,i,j}(W^\dagger_{u,L})_{c,(k,i,j)}\sum_v\overline{(D_u)^{L,k,M}_v}\,\tilde{\mathbf m}^{(i,j)}_v$;
--   5. regularized norm (23) $\|x\|=\sqrt{\sum_M|x_M|^2+\epsilon^2}-\epsilon$ and EvNorm (S39): $\bar h_{L,c}=(\|h_{L,c}\|-\mu_{L,c})/\sigma_{L,c}$, $\hat h_{L,c,M}=h_{L,c,M}/(\|h_{L,c}\|+1/\beta_{L,c}+\epsilon)$;
--   6. point-wise interaction (S40)–(S42): $f=\mathrm{MLP}_1(\bar h)\hat h$, $q_{L,c,M}=g_{L,c,M}+\sum_{L_1,L_2}\sum_{M_1,M_2}f_{L_1,c,M_1}g_{L_2,c,M_2}C^{c,L,M}_{L_1M_1;L_2M_2}$, $\phi(h,g)=h+\mathrm{MLP}_2(\bar q)\hat q$.
--
--   **The network.** The diagonal reduction gives $h^0_{u,L,c}=\sum_\nu (W_0)_{u,L,c,\nu}\,\psi_u(T_u)_{L,\nu}$ with $T_u$ the diagonal sub-tensor of atom $u$ (eq. (12)). Then $t_1$ full steps $h^{t+1}_u=\phi_t(h^t_u,\rho^\dagger_u(\tilde{\mathbf m}^t_u))$ ((S38), (27)), with attention weights $\alpha^t$ computed from $(T,h^t)$, and $t_2$ local steps $h^{t+1}_u=\phi_t(h^t_u,h^t_u)$ ((30)). `unite` returns the final features.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note.** Scalars are complex. The paper's multilayer perceptrons are arbitrary functions, and the EvNorm statistics $\mu,\sigma$ are fixed parameters. The matching weights carry the multiplicity index $k$ of the main-text shapes (16) and (28), and are allowed to depend on the atom. Every label uses the same number $n_{\max}$ of channels, as (S41) requires. The coupling coefficients $C^{\nu(n)}$ are indexed by the channel directly. The diagonal reduction $\psi_u$ is any linear map; its equivariance is a hypothesis of the theorems, not part of the definition.
-- source:
--   Qiao et al., Informing Geometric Deep Learning with Electronic Interactions to Accelerate Quantum Chemistry, arXiv:2105.14655v4, pp. 7–10 (eqs. (12), (15)–(30)), pp. 23–26 (Definitions S2–S3, eqs. (S26)–(S27), (S31), (S35)–(S45))

import Mathlib

namespace OrbNetEqui.Equivariance

open Matrix

/-! ## Unitary representations and the catalogue of irreducibles (Definition S2, pp. 23–24) -/

/-- A unitary matrix representation `ρ : K → U(m)` is irreducible: `m > 0` and the only
complex subspaces of `ℂ^m` invariant under every `ρ k` are `0` and `ℂ^m`. -/
def IsIrreducibleUnitary {K : Type*} [Group K] {m : ℕ}
    (ρ : K →* Matrix.unitaryGroup (Fin m) ℂ) : Prop :=
  0 < m ∧ ∀ W : Submodule ℂ (Fin m → ℂ),
    (∀ k, ∀ x ∈ W, (ρ k : Matrix (Fin m) (Fin m) ℂ) *ᵥ x ∈ W) → W = ⊥ ∨ W = ⊤

/-- The catalogue `(U L)_{L : Λ}` is complete: every irreducible unitary matrix
representation of `K` is linearly equivalent (intertwined) to some catalogue member `U L`.
This is the content of "we have abstracted the labelling details for U(n) irreducible
representations into the index L" (p. 24). -/
def CatalogComplete {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ) : Prop :=
  ∀ (m : ℕ) (ρ : K →* Matrix.unitaryGroup (Fin m) ℂ), IsIrreducibleUnitary ρ →
    ∃ L, ∃ e : (Fin m → ℂ) ≃ₗ[ℂ] (Fin (dim L) → ℂ),
      ∀ k x, e ((ρ k : Matrix (Fin m) (Fin m) ℂ) *ᵥ x) = (U L k : Matrix _ _ ℂ) *ᵥ e x

/-! ## Tensor actions (S26)–(S28), pp. 23–24 -/

/-- Action of a family of matrices `A j` on an order-`N` tensor with index types `κ j`:
`(A_1 ⊗ ⋯ ⊗ A_N) T`, i.e. `p ↦ ∑_q (∏_j A_j(p_j, q_j)) T(q)`. -/
def tensorProdAct {N : ℕ} {κ : Fin N → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (A : (j : Fin N) → Matrix (κ j) (κ j) ℂ) (T : ((j : Fin N) → κ j) → ℂ) :
    ((j : Fin N) → κ j) → ℂ :=
  fun p => ∑ q : (j : Fin N) → κ j, (∏ j, A j (p j) (q j)) * T q

/-- The diagonal action `(A ⊗ A ⊗ ⋯ ⊗ A) T` of one matrix on an order-`N` tensor over a single
index type `β` (eq. (S27)). -/
def diagAct {N : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (A : Matrix β β ℂ) (T : (Fin N → β) → ℂ) : (Fin N → β) → ℂ :=
  fun w => ∑ w' : Fin N → β, (∏ j, A (w j) (w' j)) * T w'

/-- The space `V_u ≃ ⊕_a V^{lab a}` of Definition S2, with the irreducible blocks listed with
multiplicity by `lab : Fin r → Λ`; its basis index is `Σ a, Fin (dim (lab a))` and `labelRep`
is the block-diagonal matrix `π²(k) = ⊕_a U^{lab a}_k`. -/
def labelRep {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ) {r : ℕ} (lab : Fin r → Λ) (k : K) :
    Matrix (Σ a : Fin r, Fin (dim (lab a))) (Σ a : Fin r, Fin (dim (lab a))) ℂ :=
  Matrix.blockDiagonal' fun a => (U (lab a) k : Matrix (Fin (dim (lab a))) (Fin (dim (lab a))) ℂ)

/-- The linear map (S31) defined by coefficients `Q`:
`ψ(T)_{ν,L,M} = ∑_v T(v) Q^v_{ν,L,M}`. -/
def coeffMap {Λ : Type*} {dim : Λ → ℕ} {μ : Λ → ℕ} {N : ℕ} {β : Type*} [Fintype β]
    (Q : (L : Λ) → Fin (μ L) → Fin (dim L) → (Fin N → β) → ℂ) (T : (Fin N → β) → ℂ) :
    (L : Λ) → Fin (μ L) → Fin (dim L) → ℂ :=
  fun L ν M => ∑ v : Fin N → β, T v * Q L ν M v

/-! ## N-body tensors over local atomic bases and the local action (S24), (S26) -/

/-- The concatenated basis index `{(u, v)}` of all atoms `u : Fin d`, each with local basis
index `ι u` (Definitions S1, S3). -/
abbrev Orb {d : ℕ} (ι : Fin d → Type*) := Σ u : Fin d, ι u

/-- The block-diagonal unitary `⊕_u π¹_u(g_u)` acting on the concatenated basis: each atom's
block is rotated by the unitary of that atom's own group element. -/
def blockRep {K : Type*} [Group K] {d : ℕ} {ι : Fin d → Type*} [∀ u, Fintype (ι u)]
    [∀ u, DecidableEq (ι u)] (π₁ : (u : Fin d) → K →* Matrix.unitaryGroup (ι u) ℂ)
    (g : Fin d → K) : Matrix (Orb ι) (Orb ι) ℂ :=
  Matrix.blockDiagonal' fun u => (π₁ u (g u) : Matrix (ι u) (ι u) ℂ)

/-- The local action (S26) of `g = (g_u)_u` on an order-`(n+1)` N-body tensor
`T : (Fin (n+1) → Orb ι) → ℂ`: every tensor index lying in atom `u`'s block is rotated by
`π¹_u(g_u)`, so the sub-tensor `T_{u⃗}` becomes `(π¹(g_{u₁}) ⊗ ⋯ ⊗ π¹(g_{u_N})) T_{u⃗}`. -/
def tensorAct {K : Type*} [Group K] {d n : ℕ} {ι : Fin d → Type*} [∀ u, Fintype (ι u)]
    [∀ u, DecidableEq (ι u)] (π₁ : (u : Fin d) → K →* Matrix.unitaryGroup (ι u) ℂ)
    (g : Fin d → K) (T : (Fin (n + 1) → Orb ι) → ℂ) : (Fin (n + 1) → Orb ι) → ℂ :=
  diagAct (blockRep π₁ g) T

/-! ## Order-1 features (S2.5, p. 25) -/

/-- Hidden features of one atom: for each label `L`, each channel `c < nmax`, a vector in
`V^L = ℂ^{dim L}`. -/
abbrev Feature (Λ : Type*) (dim : Λ → ℕ) (nmax : ℕ) := (L : Λ) → Fin nmax → Fin (dim L) → ℂ

/-- The action `π²(k)` on features: `(k · h)_{L,c} = U^L_k h_{L,c}` (Definition S3). -/
def featAct {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ) (k : K)
    (h : Feature Λ dim nmax) : Feature Λ dim nmax :=
  fun L c => (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ h L c

/-! ## Building blocks (S2.5, pp. 25–26; Methods 1.1, pp. 7–10) -/

/-- Index type `(L, k, M)` of atom `u`'s basis `{π_{u;L,M}}` in Definition S2/S3 form: `k`
runs over the `Kmul u L` copies of `V^L` in `V_u`, `M` over a basis of `V^L`. -/
abbrev MIdx {Λ : Type*} (dim : Λ → ℕ) {d : ℕ} (Kmul : Fin d → Λ → ℕ) (u : Fin d) :=
  Σ L : Λ, Fin (Kmul u L) × Fin (dim L)

/-- `π²_u(k)` in the basis `{π_{u;L,k,M}}`: block-diagonal over `L`, acting as `1 ⊗ U^L_k` on
`(k, M)`. -/
def π₂mat {K : Type*} [Group K] {Λ : Type*} [DecidableEq Λ] {dim : Λ → ℕ} {d : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ) (Kmul : Fin d → Λ → ℕ)
    (u : Fin d) (k : K) : Matrix (MIdx dim Kmul u) (MIdx dim Kmul u) ℂ :=
  Matrix.blockDiagonal' fun L =>
    Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin (Kmul u L)) (Fin (Kmul u L)) ℂ)
      (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ)

/-- Matching layer (S44), with the multiplicity index of (16):
`ρ_u(h)^i_v = ∑_{L,k,M} (D_u)_v^{L,k,M} ∑_c (W^i_{u,L})_{k,c} h_{L,c,M}`, where
`(D_u)_v^{L,k,M} = ⟨e_{u;v}, π_{u;L,k,M}⟩`. -/
def matching {Λ : Type*} [Fintype Λ] {dim : Λ → ℕ} {d nmax I : ℕ} {Kmul : Fin d → Λ → ℕ}
    {ι : Fin d → Type*} (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ)
    (W : (u : Fin d) → Fin I → (L : Λ) → Matrix (Fin (Kmul u L)) (Fin nmax) ℂ)
    (u : Fin d) (i : Fin I) (h : Feature Λ dim nmax) : ι u → ℂ :=
  fun v => ∑ x : MIdx dim Kmul u, D u v x * ∑ c : Fin nmax, W u i x.1 x.2.1 c * h x.1 c x.2.2

/-- Block convolution (S36), order `N = n + 1` and complex scalars:
`(m_{u⃗})^i_{v₁} = ∑_{v₂,…,v_N} T_{u⃗}(v₁,…,v_N) ∏_{j=2}^N conj(ρ_{u_j}(h_{u_j})^i_{v_j})`. -/
def blockConv {Λ : Type*} [Fintype Λ] {dim : Λ → ℕ} {d n nmax I : ℕ}
    {Kmul : Fin d → Λ → ℕ} {ι : Fin d → Type*} [∀ u, Fintype (ι u)]
    (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ)
    (W : (u : Fin d) → Fin I → (L : Λ) → Matrix (Fin (Kmul u L)) (Fin nmax) ℂ)
    (T : (Fin (n + 1) → Orb ι) → ℂ) (h : Fin d → Feature Λ dim nmax)
    (uvec : Fin (n + 1) → Fin d) (i : Fin I) (v₁ : ι (uvec 0)) : ℂ :=
  ∑ vr : (j : Fin n) → ι (uvec j.succ),
    T (fun j => ⟨uvec j, (Fin.cons v₁ vr : (j : Fin (n + 1)) → ι (uvec j)) j⟩) *
      ∏ j : Fin n, starRingEnd ℂ (matching D W (uvec j.succ) i (h (uvec j.succ)) (vr j))

/-- Message aggregation (S37): `m̃_{u₁} = ∑_{u₂,…,u_N} ⊕_{i,j} (m_{u⃗})^i α^j_{u⃗}`, as a family
indexed by `(i, j)` of vectors over atom `u₁`'s basis. -/
def aggregate {Λ : Type*} [Fintype Λ] {dim : Λ → ℕ} {d n nmax I J : ℕ}
    {Kmul : Fin d → Λ → ℕ} {ι : Fin d → Type*} [∀ u, Fintype (ι u)]
    (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ)
    (W : (u : Fin d) → Fin I → (L : Λ) → Matrix (Fin (Kmul u L)) (Fin nmax) ℂ)
    (T : (Fin (n + 1) → Orb ι) → ℂ) (h : Fin d → Feature Λ dim nmax)
    (α : (Fin (n + 1) → Fin d) → Fin J → ℂ) (u₁ : Fin d) : Fin I × Fin J → ι u₁ → ℂ :=
  fun ij v => ∑ ur : Fin n → Fin d,
    blockConv D W T h (Fin.cons u₁ ur) ij.1 v * α (Fin.cons u₁ ur) ij.2

/-- Reverse matching layer (S45), with the main-text weight shape of (28):
`ρ†_u(m̃)_{L,c,M} = ∑_{k,i,j} (W†_{u,L})_{c,(k,i,j)} ∑_v conj((D_u)_v^{L,k,M}) m̃^{(i,j)}_v`. -/
def revMatching {Λ : Type*} {dim : Λ → ℕ} {d nmax I J : ℕ}
    {Kmul : Fin d → Λ → ℕ} {ι : Fin d → Type*} [∀ u, Fintype (ι u)]
    (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ)
    (Wd : (u : Fin d) → (L : Λ) → Matrix (Fin nmax) (Fin (Kmul u L) × Fin I × Fin J) ℂ)
    (u : Fin d) (m : Fin I × Fin J → ι u → ℂ) : Feature Λ dim nmax :=
  fun L c M => ∑ x : Fin (Kmul u L) × Fin I × Fin J,
    Wd u L c x * ∑ v : ι u, starRingEnd ℂ (D u v ⟨L, (x.1, M)⟩) * m (x.2.1, x.2.2) v

/-- The regularized norm (23): `‖x‖_ε = sqrt(∑_M |x_M|² + ε²) − ε`. -/
noncomputable def regNorm {m : ℕ} (ε : ℝ) (x : Fin m → ℂ) : ℝ :=
  Real.sqrt (∑ M, Complex.normSq (x M) + ε ^ 2) - ε

/-- Invariant part of EvNorm (S39): `h̄_{L,c} = (‖h_{L,c}‖_ε − μ_{L,c}) / σ_{L,c}`. -/
noncomputable def evNormBar {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (μ σ : Λ → Fin nmax → ℝ) (ε : ℝ) (h : Feature Λ dim nmax) : Λ → Fin nmax → ℝ :=
  fun L c => (regNorm ε (h L c) - μ L c) / σ L c

/-- Direction part of EvNorm (S39): `ĥ_{L,c,M} = h_{L,c,M} / (‖h_{L,c}‖_ε + 1/β_{L,c} + ε)`. -/
noncomputable def evNormHat {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (β : Λ → Fin nmax → ℝ) (ε : ℝ) (h : Feature Λ dim nmax) : Feature Λ dim nmax :=
  fun L c M => h L c M / ((regNorm ε (h L c) + 1 / β L c + ε : ℝ) : ℂ)

/-- Parameters of one point-wise interaction block (S40)–(S42): the two MLPs (any functions of
the invariant features), EvNorm statistics `μ, σ` and scales `β` for its two EvNorms (on `h` and
on `q`), and the coupling coefficients `C^{ν(c)}_{L₁;L₂ → L}` for each channel `c`. -/
structure PointwiseParams (Λ : Type*) (dim : Λ → ℕ) (nmax : ℕ) where
  mlp₁ : (Λ → Fin nmax → ℝ) → (Λ → Fin nmax → ℝ)
  mlp₂ : (Λ → Fin nmax → ℝ) → (Λ → Fin nmax → ℝ)
  μh : Λ → Fin nmax → ℝ
  σh : Λ → Fin nmax → ℝ
  βh : Λ → Fin nmax → ℝ
  μq : Λ → Fin nmax → ℝ
  σq : Λ → Fin nmax → ℝ
  βq : Λ → Fin nmax → ℝ
  C : Fin nmax → (L₁ L₂ L : Λ) → Matrix (Fin (dim L)) (Fin (dim L₁) × Fin (dim L₂)) ℂ

/-- Point-wise interaction `φ(h, g)` (S40)–(S42):
`f_{L,c,M} = MLP₁(h̄)_{L,c} ĥ_{L,c,M}`,
`q_{L,c,M} = g_{L,c,M} + ∑_{L₁,L₂} ∑_{M₁,M₂} f_{L₁,c,M₁} g_{L₂,c,M₂} C^{ν(c),L,M}_{L₁M₁;L₂M₂}`,
`φ(h,g)_{L,c,M} = h_{L,c,M} + MLP₂(q̄)_{L,c} q̂_{L,c,M}`. -/
noncomputable def pointwise {Λ : Type*} [Fintype Λ] {dim : Λ → ℕ} {nmax : ℕ}
    (P : PointwiseParams Λ dim nmax) (ε : ℝ) (h g : Feature Λ dim nmax) :
    Feature Λ dim nmax :=
  let f : Feature Λ dim nmax := fun L c M =>
    ((P.mlp₁ (evNormBar P.μh P.σh ε h) L c : ℝ) : ℂ) * evNormHat P.βh ε h L c M
  let q : Feature Λ dim nmax := fun L c M =>
    g L c M + ∑ L₁ : Λ, ∑ L₂ : Λ, ∑ M₁ : Fin (dim L₁), ∑ M₂ : Fin (dim L₂),
      f L₁ c M₁ * g L₂ c M₂ * P.C c L₁ L₂ L M (M₁, M₂)
  fun L c M => h L c M + ((P.mlp₂ (evNormBar P.μq P.σq ε q) L c : ℝ) : ℂ) * evNormHat P.βq ε q L c M

/-! ## The network (Methods 1.1, pp. 7–10; (27), (30)) -/

/-- The diagonal sub-tensor `T_u` (all indices in atom `u`'s block). -/
def diagBlock {d n : ℕ} {ι : Fin d → Type*} (T : (Fin (n + 1) → Orb ι) → ℂ) (u : Fin d) :
    (Fin (n + 1) → ι u) → ℂ :=
  fun w => T (fun j => ⟨u, w j⟩)

/-- All parameters of a UNiTE network acting on order-`(n+1)` tensors over `d` atoms:
the diagonal reduction `ψ_u` with output multiplicities `μd u L` and the channel projection
`W₀`; per-step matching weights `W t`, reverse-matching weights `Wd t`, attention weights
`α t` (a function of the step's inputs), point-wise parameters `P t`; the stability factor
`ε`; and the stack counts `t₁` (full steps) and `t₂` (local steps). -/
structure UniteParams (d n : ℕ) (ι : Fin d → Type*) (Λ : Type*) (dim : Λ → ℕ) (nmax : ℕ)
    (Kmul : Fin d → Λ → ℕ) (I J : ℕ) where
  μd : Fin d → Λ → ℕ
  ψ : (u : Fin d) → ((Fin (n + 1) → ι u) → ℂ) →ₗ[ℂ] ((L : Λ) → Fin (μd u L) → Fin (dim L) → ℂ)
  W₀ : (u : Fin d) → (L : Λ) → Matrix (Fin nmax) (Fin (μd u L)) ℂ
  W : ℕ → (u : Fin d) → Fin I → (L : Λ) → Matrix (Fin (Kmul u L)) (Fin nmax) ℂ
  Wd : ℕ → (u : Fin d) → (L : Λ) → Matrix (Fin nmax) (Fin (Kmul u L) × Fin I × Fin J) ℂ
  α : ℕ → ((Fin (n + 1) → Orb ι) → ℂ) → (Fin d → Feature Λ dim nmax) →
    (Fin (n + 1) → Fin d) → Fin J → ℂ
  P : ℕ → PointwiseParams Λ dim nmax
  ε : ℝ
  t₁ : ℕ
  t₂ : ℕ

variable {d n : ℕ} {ι : Fin d → Type*} [∀ u, Fintype (ι u)] {Λ : Type*} [Fintype Λ]
  {dim : Λ → ℕ} {nmax : ℕ} {Kmul : Fin d → Λ → ℕ} {I J : ℕ}

/-- Initial features `h⁰` from the diagonal reduction (12):
`h⁰_{u,L,c,M} = ∑_ν (W₀)_{u,L,c,ν} ψ_u(T_u)_{L,ν,M}`. -/
def diagReduce (θ : UniteParams d n ι Λ dim nmax Kmul I J) (T : (Fin (n + 1) → Orb ι) → ℂ) :
    Fin d → Feature Λ dim nmax :=
  fun u L c M => ∑ ν : Fin (θ.μd u L), θ.W₀ u L c ν * θ.ψ u (diagBlock T u) L ν M

/-- Features after `t` full steps (S36)–(S38), (27):
`h^{t+1}_u = φ_t(h^t_u, ρ†_u(m̃^t_u))`. -/
noncomputable def fullSteps (θ : UniteParams d n ι Λ dim nmax Kmul I J)
    (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ) (T : (Fin (n + 1) → Orb ι) → ℂ) :
    ℕ → Fin d → Feature Λ dim nmax
  | 0 => diagReduce θ T
  | t + 1 =>
    fun u => pointwise (θ.P t) θ.ε (fullSteps θ D T t u)
      (revMatching D (θ.Wd t) u
        (aggregate D (θ.W t) T (fullSteps θ D T t) (θ.α t T (fullSteps θ D T t)) u))

/-- Features after `s` further local steps (30), starting from `h` at step `t₁`:
`h^{t+1}_u = φ_t(h^t_u, h^t_u)` for `t = t₁ + s`. -/
noncomputable def localSteps (θ : UniteParams d n ι Λ dim nmax Kmul I J)
    (h : Fin d → Feature Λ dim nmax) : ℕ → Fin d → Feature Λ dim nmax
  | 0 => h
  | s + 1 => fun u =>
    pointwise (θ.P (θ.t₁ + s)) θ.ε (localSteps θ h s u) (localSteps θ h s u)

/-- The UNiTE network: diagonal reduction, then `t₁` full steps, then `t₂` local steps. -/
noncomputable def unite (θ : UniteParams d n ι Λ dim nmax Kmul I J)
    (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ) (T : (Fin (n + 1) → Orb ι) → ℂ) :
    Fin d → Feature Λ dim nmax :=
  localSteps θ (fullSteps θ D T θ.t₁) θ.t₂

end OrbNetEqui.Equivariance


