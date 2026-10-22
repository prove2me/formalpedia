-- Prove2me | Definitions.Def_GeomDL_Sets_Defs
-- name    : GeomDL_Sets_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:35.16507+00:00
-- url     : https://prove2.me/theorems/a39bebb7-b684-4b40-94dc-4eeec960c61d
-- title:
--   §4.1, pp. 32–34; §5.4, p. 81 — permutation actions PX and PAPᵀ, permutation invariance (9) and equivariance (10), the constructions (6), (7), (11)–(13)
-- statement:
--   These definitions set up the objects of Section 4.1 (*Graphs and Sets*) of Bronstein, Bruna, Cohen and Veličković.
--
--   A graph has $n$ nodes $\{1,\dots,n\}$. Node features are stacked as rows of a matrix $\mathbf X\in\mathbb R^{n\times d}$, $\mathbf X=(\mathbf x_1,\dots,\mathbf x_n)^\top$, and connectivity is an adjacency matrix $\mathbf A\in\mathbb R^{n\times n}$.
--
--   1. **Permutation action.** A permutation $\sigma\in\Sigma_n$ acts through its permutation matrix $\mathbf P$ by reordering rows: $(\mathbf P\mathbf X)_u=\mathbf x_{\sigma^{-1}(u)}$, and on adjacency matrices by $(\mathbf P\mathbf A\mathbf P^\top)_{uv}=a_{\sigma^{-1}(u)\,\sigma^{-1}(v)}$. On a single channel $x\in\mathbb R^n$ this is $(\mathbf P x)_u=x_{\sigma^{-1}(u)}$.
--   2. **Averaging.** $\mathbf F_2 x=\tfrac1n\mathbf 1\mathbf 1^\top x$ is the vector all of whose entries equal $\tfrac1n\sum_{u=1}^n x_u$; $\mathbf 1\mathbf 1^\top$ is the all-ones $n\times n$ matrix.
--   3. **Invariance and equivariance on sets.** $f$ is permutation invariant if $f(\mathbf P\mathbf X)=f(\mathbf X)$, and $\mathbf F$ is permutation equivariant if $\mathbf F(\mathbf P\mathbf X)=\mathbf P\mathbf F(\mathbf X)$, for every permutation matrix $\mathbf P$.
--   4. **On graphs**, eqs. (9) and (10): a graph-wise $f$ is permutation invariant if $f(\mathbf P\mathbf X,\mathbf P\mathbf A\mathbf P^\top)=f(\mathbf X,\mathbf A)$, and a node-wise $\mathbf F$ is permutation equivariant if $\mathbf F(\mathbf P\mathbf X,\mathbf P\mathbf A\mathbf P^\top)=\mathbf P\mathbf F(\mathbf X,\mathbf A)$, for every permutation matrix $\mathbf P$.
--   5. **Constructions.** The sum readout (6) $f(\mathbf X)=\phi\big(\sum_{u\in\mathcal V}\psi(\mathbf x_u)\big)$; the node-wise linear map (7) $\mathbf F_{\boldsymbol\Theta}(\mathbf X)=\mathbf X\boldsymbol\Theta$; the neighbourhood (11) $\mathcal N_u=\{v:(u,v)\in\mathcal E\text{ or }(v,u)\in\mathcal E\}$; the neighbourhood features (12), the multiset $\mathbf X_{\mathcal N_u}=\{\!\{\mathbf x_v:v\in\mathcal N_u\}\!\}$; the local layer (13) whose $u$-th row is $\phi(\mathbf x_u,\mathbf X_{\mathcal N_u})$; and the convolutional-type layer of §5.4, $\mathbf h_u=\phi\big(\mathbf x_u,\bigoplus_{v\in\mathcal N_u}\psi(\mathbf x_v)\big)$.
--   6. **Equivariant maps on adjacency matrices.** The real vector space of linear maps $L:\mathbb R^{n\times n}\to\mathbb R^{n\times n}$ with $L(\mathbf P\mathbf A\mathbf P^\top)=\mathbf P\,L(\mathbf A)\,\mathbf P^\top$ for every permutation matrix $\mathbf P$.
--
--   These are the shared vocabulary of every statement in this mission.
--
--   **Formalization Note** The edge set of an adjacency matrix is $\mathcal E=\{(u,v):a_{uv}\neq0\}$; for the 0/1 matrix (8) this is the book's edge set, and real matrices are allowed so that weighted graphs are covered. The function $\phi$ of (13) takes the neighbourhood features as a `Multiset`, and the aggregator $\bigoplus$ of §5.4 is a function of a multiset, so their permutation invariance holds by construction. The permutation convention (rows moved by $\sigma^{-1}$) is used in every statement of the mission.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.1, eqs. (6)–(13), pp. 32–34; §5.4, p. 81

import Mathlib

namespace GeomDL.Sets

open Matrix

noncomputable section

/-- §4.1, p. 32: the action of a permutation `σ ∈ Σₙ` on a node-feature matrix
`X ∈ ℝ^{n×d}` (rows `x_u`) by the permutation matrix `P = ρ(σ)`, i.e. `PX`.
Convention: row `u` of `PX` is row `σ⁻¹(u)` of `X`. -/
def permRows {n d : ℕ} (σ : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin d) ℝ) :
    Matrix (Fin n) (Fin d) ℝ :=
  X.submatrix σ.symm id

/-- §4.1, p. 33: the action `A ↦ PAPᵀ` of `σ ∈ Σₙ` on an `n × n` adjacency matrix,
in the same convention as `permRows`: `(PAPᵀ)_{uv} = A_{σ⁻¹(u) σ⁻¹(v)}`. -/
def permAdj {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  A.submatrix σ.symm σ.symm

/-- The single-channel case of `permRows`: `(Px)_u = x_{σ⁻¹(u)}` for `x ∈ ℝⁿ`. -/
def permVec {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun u => x (σ.symm u)

/-- §4.1, p. 33: the averaging generator `F₂x = (1/n) 𝟙𝟙ᵀ x` on a single channel:
every coordinate equals the mean `(1/n) ∑ᵤ x_u`. -/
def average {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun _ => (n : ℝ)⁻¹ * ∑ u, x u

/-- The all-ones matrix `𝟙𝟙ᵀ ∈ ℝ^{n×n}`. -/
def allOnes (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun _ _ => 1

/-- §4.1, p. 32: `f` is permutation invariant if `f(PX) = f(X)` for every permutation matrix `P`. -/
def IsPermInvariant {n d : ℕ} {Y : Type*} (f : Matrix (Fin n) (Fin d) ℝ → Y) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin d) ℝ), f (permRows σ X) = f X

/-- §4.1, pp. 32–33: `F` is permutation equivariant if `F(PX) = PF(X)` for every permutation
matrix `P`. -/
def IsPermEquivariant {n d d' : ℕ}
    (F : Matrix (Fin n) (Fin d) ℝ → Matrix (Fin n) (Fin d') ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin d) ℝ), F (permRows σ X) = permRows σ (F X)

/-- §4.1, eq. (9), p. 33: a graph-wise function `f(X, A)` is permutation invariant if
`f(PX, PAPᵀ) = f(X, A)` for every permutation matrix `P`. -/
def IsGraphPermInvariant {n d : ℕ} {Y : Type*}
    (f : Matrix (Fin n) (Fin d) ℝ → Matrix (Fin n) (Fin n) ℝ → Y) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin d) ℝ) (A : Matrix (Fin n) (Fin n) ℝ),
    f (permRows σ X) (permAdj σ A) = f X A

/-- §4.1, eq. (10), p. 33: a node-wise function `F(X, A)` is permutation equivariant if
`F(PX, PAPᵀ) = PF(X, A)` for every permutation matrix `P`. -/
def IsGraphPermEquivariant {n d d' : ℕ}
    (F : Matrix (Fin n) (Fin d) ℝ → Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin d') ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin d) ℝ) (A : Matrix (Fin n) (Fin n) ℝ),
    F (permRows σ X) (permAdj σ A) = permRows σ (F X A)

/-- §4.1, eq. (6), p. 32: `f(X) = φ(∑_{u ∈ V} ψ(x_u))`, with `ψ` applied to every node's
features and `φ` applied to the sum. -/
def sumReadout {n d : ℕ} {M Y : Type*} [AddCommMonoid M] (φ : M → Y) (ψ : (Fin d → ℝ) → M)
    (X : Matrix (Fin n) (Fin d) ℝ) : Y :=
  φ (∑ u, ψ (X u))

/-- §4.1, eq. (7), p. 33: the shared node-wise linear transform `F_Θ(X) = XΘ`,
`Θ ∈ ℝ^{d×d'}`. -/
def nodeLinear {n d d' : ℕ} (Θ : Matrix (Fin d) (Fin d') ℝ) (X : Matrix (Fin n) (Fin d) ℝ) :
    Matrix (Fin n) (Fin d') ℝ :=
  X * Θ

/-- §4.1, eq. (11), p. 34: the neighbourhood `N_u = {v : (u,v) ∈ E or (v,u) ∈ E}`, where the
edge set of an adjacency matrix `A` is `E = {(u,v) : a_{uv} ≠ 0}` (for the 0/1 matrix (8) this is
exactly the edge set). -/
def neighbourhood {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => A u v ≠ 0 ∨ A v u ≠ 0)

/-- §4.1, eq. (12), p. 34: the neighbourhood features, the multiset `X_{N_u} = {{x_v : v ∈ N_u}}`. -/
def neighbourhoodFeatures {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n) : Multiset (Fin d → ℝ) :=
  (neighbourhood A u).val.map (fun v => X v)

/-- §4.1, eq. (13), p. 34: the local construction `F(X, A)_u = φ(x_u, X_{N_u})`: a shared
function `φ` of a node's features and the multiset of its neighbours' features, applied at
every node. Since `φ` receives a multiset, it is invariant to the ordering of `N_u` by
construction. -/
def localLayer {n d d' : ℕ} (φ : (Fin d → ℝ) → Multiset (Fin d → ℝ) → (Fin d' → ℝ))
    (X : Matrix (Fin n) (Fin d) ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin d') ℝ :=
  Matrix.of fun u => φ (X u) (neighbourhoodFeatures X A u)

/-- §5.4, p. 81: a convolutional-type GNN layer `h_u = φ(x_u, ⊕_{v ∈ N_u} ψ(x_v))`, where the
permutation-invariant aggregator `⊕` is a function of the multiset `{{ψ(x_v) : v ∈ N_u}}`. -/
def aggLayer {n d d' : ℕ} {M M' : Type*} (φ : (Fin d → ℝ) → M' → (Fin d' → ℝ))
    (ψ : (Fin d → ℝ) → M) (agg : Multiset M → M')
    (X : Matrix (Fin n) (Fin d) ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin d') ℝ :=
  Matrix.of fun u => φ (X u) (agg ((neighbourhood A u).val.map (fun v => ψ (X v))))

/-- §4.1, pp. 33–34: the space of linear maps `L : ℝ^{n×n} → ℝ^{n×n}` that are equivariant
under `A ↦ PAPᵀ`, i.e. `L(PAPᵀ) = P L(A) Pᵀ` for every permutation matrix `P`. -/
def adjEquivariantMaps (n : ℕ) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ) where
  carrier := {L | ∀ (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ),
    L (permAdj σ A) = permAdj σ (L A)}
  add_mem' := by
    intro L₁ L₂ h₁ h₂ σ A
    simp only [LinearMap.add_apply, h₁ σ A, h₂ σ A]
    rfl
  zero_mem' := by
    intro σ A
    simp only [LinearMap.zero_apply]
    rfl
  smul_mem' := by
    intro c L h σ A
    simp only [LinearMap.smul_apply, h σ A]
    rfl

end

end GeomDL.Sets


