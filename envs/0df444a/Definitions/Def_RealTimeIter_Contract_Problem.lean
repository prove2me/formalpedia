-- Prove2me | Definitions.Def_RealTimeIter_Contract_Problem
-- name    : RealTimeIter_Contract_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:43.191252+00:00
-- url     : https://prove2.me/theorems/10a5c304-232e-4768-b7d6-74e80818dcb7
-- title:
--   §1.1, §2, §2.1, §3, pp. 1715–1720 — the problems $P_k(x_k)$, the Lagrangian $\mathcal L^k$, the KKT matrix and its Newton-type approximation $J^k$, the projections $\Pi^{k+1}$
-- statement:
--   **The control system and the problems $P_k(x_k)$.** Fix a horizon $N\in\mathbb N$, state and control dimensions $n_x,n_u$, dynamics $f_i:\mathbb R^{n_x}\times\mathbb R^{n_u}\to\mathbb R^{n_x}$, stage costs $L_i:\mathbb R^{n_x}\times\mathbb R^{n_u}\to\mathbb R$ ($i=0,\dots,N-1$) and a terminal cost $E:\mathbb R^{n_x}\to\mathbb R$. The discrete-time system is $x_{k+1}=f_k(x_k,u_k)$. For $k\le N$ and an initial value $x_k$, problem $P_k(x_k)$ is
--   $$\min_{s_k,\dots,s_N,\;q_k,\dots,q_{N-1}}\ \sum_{i=k}^{N-1}L_i(s_i,q_i)+E(s_N)\quad\text{s.t.}\quad x_k-s_k=0,\quad f_i(s_i,q_i)-s_{i+1}=0\ (i=k,\dots,N-1).$$
--
--   **Primal-dual variables.** The primal-dual vector of $P_k$ is $y=(\lambda_k,s_k,q_k,\lambda_{k+1},s_{k+1},q_{k+1},\dots,\lambda_N,s_N)\in\mathbb R^{n_k}$, $n_k=(2n_x+n_u)(N-k)+2n_x$, with the Euclidean inner product. The projection $\Pi^{k+1}:\mathbb R^{n_k}\to\mathbb R^{n_{k+1}}$ drops the stage-$k$ block: $\Pi^{k+1}(\lambda_k,s_k,q_k,\tilde y)=\tilde y$. Its transpose $(\Pi^{k+1})^T$ extends by zero; $\Pi^k\cdots\Pi^1:\mathbb R^{n_0}\to\mathbb R^{n_k}$ drops all stages below $k$ and $(\Pi^k\cdots\Pi^1)^T$ extends by zero.
--
--   **The Lagrangian.** For $y\in\mathbb R^{n_k}$,
--   $$\mathcal L^k(y)=\sum_{i=k}^{N-1}L_i(s_i,q_i)+E(s_N)+\lambda_k^T(x_k-s_k)+\sum_{i=k}^{N-1}\lambda_{i+1}^T\big(f_i(s_i,q_i)-s_{i+1}\big),$$
--   with gradient $\nabla_y\mathcal L^k(y)$ and Hessian $\nabla^2_y\mathcal L^k(y)$. The Hessian does not depend on $x_k$, which enters linearly.
--
--   **The Newton-type matrix.** The data also include, for each stage $i<N$, an approximation $\begin{pmatrix}Q^H_i&M^H_i\\(M^H_i)^T&R^H_i\end{pmatrix}(s_i,q_i,\lambda_{i+1})$ of the Hessian block $\nabla^2_{(s_i,q_i)}\mathcal L^k$, and an approximation $Q^H_N(s_N)$ of the terminal block $Q_N=\nabla^2_{s_N}\mathcal L^k$. The matrix $J^k(y)$ is $\nabla^2_y\mathcal L^k(y)$ with every diagonal block $(s_i,q_i)$, $k\le i\le N-1$, replaced by its approximation and the block $s_N$ replaced by $Q^H_N(s_N)$; every other entry (the $-\mathbb I$ blocks and the Jacobians $A_i=\partial f_i/\partial s_i$, $B_i=\partial f_i/\partial q_i$) is kept exact.
--
--   These objects are the setting of every statement of the mission.
--
--   **Formalization Note.** Coordinates of $\mathbb R^{n_k}$ are indexed by (block, stage, component) with stage $\ge k$ (`PD P k`), so $\Pi^{k+1}$ is a restriction; the coordinate order is irrelevant to every statement. Accessors `lamL`, `sL`, `qL` read $\lambda_i,s_i,q_i$ (zero outside the stages present); `blockSQ`/`embSQ` are the block read-out $\pi_i$ and its zero extension $\iota_i$, and $J^k(y)=\nabla^2\mathcal L^k(y)+\sum_{i=k}^{N-1}\iota_i\big(H_i-\pi_i\nabla^2\mathcal L^k(y)\iota_i\big)\pi_i+\iota_N\big(Q^H_N-\pi_N\nabla^2\mathcal L^k(y)\iota_N\big)\pi_N$. The paper writes the approximations as functions of $\lambda_{k+1}$; the stage-$i$ block involves $\lambda_{i+1}$ (the multiplier of $f_i$), which is what is encoded. The paper keeps $Q_N$ exact in §2.1 and approximates it in §2.2; the terminal approximation covers both ($Q^H_N=\nabla^2E$ recovers the former). Symmetry of the approximations is not required. `grad` is the gradient for the initial value $x$; `hess` is the Fréchet derivative of the gradient at $x=0$; both are Mathlib's total operators, which return $0$ where $\mathcal L^k$ is not differentiable, so every theorem assumes differentiability where it uses them. `Eterm` is the paper's $E$.
-- source:
--   Diehl, Bock, Schlöder, A real-time iteration scheme for nonlinear optimization in optimal feedback control, SIAM J. Control Optim. 43 (2005), pp. 1715–1720, (1.1), (1.2), §2 (Lagrangian, footnote 1, (2.4)), §2.1 (KKT matrix, Remarks 1–2), §2.2 (Q^H_N), §3 (Π^{k+1})

import Mathlib

noncomputable section

namespace RealTimeIter.Contract

open scoped InnerProductSpace

/-- The Euclidean space `ℝ^n` of states (`n = n_x`) or controls (`n = n_u`). -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The data of the shrinking-horizon optimal control problems `P_k(x_k)` of (1.1)–(1.2) and of the
Newton-type method of §2.1: horizon `N`, state and control dimensions `nx`, `nu`, dynamics `f i`, stage
costs `L i`, terminal cost `Eterm` (the paper's `E`), the approximation `QH i s q λ` of the stage Hessian
block `[[Q_i, M_i], [M_iᵀ, R_i]]` (as a function of `(s_i, q_i, λ_{i+1})`) and the approximation
`QHN s` of the terminal block `Q_N`. Only `f i`, `L i`, `QH i` with `i < N` are ever used. -/
structure OCP where
  N : ℕ
  nx : ℕ
  nu : ℕ
  f : ℕ → Vec nx → Vec nu → Vec nx
  L : ℕ → Vec nx → Vec nu → ℝ
  Eterm : Vec nx → ℝ
  QH : ℕ → Vec nx → Vec nu → Vec nx → (Vec nx × Vec nu →L[ℝ] Vec nx × Vec nu)
  QHN : Vec nx → (Vec nx →L[ℝ] Vec nx)

/-- Coordinates of the primal-dual vector of `P_0`: `λ_i` (`i ≤ N`), `s_i` (`i ≤ N`), `q_i` (`i < N`),
each tagged with its stage and its component. -/
abbrev Coord (P : OCP) :=
  (Fin (P.N + 1) × Fin P.nx) ⊕ (Fin (P.N + 1) × Fin P.nx) ⊕ (Fin P.N × Fin P.nu)

/-- The stage `i` of a coordinate of `λ_i`, `s_i` or `q_i`. -/
def stage {P : OCP} : Coord P → ℕ
  | Sum.inl (i, _) => i.val
  | Sum.inr (Sum.inl (i, _)) => i.val
  | Sum.inr (Sum.inr (i, _)) => i.val

/-- The primal-dual space `ℝ^{n_k}` of problem `P_k`: the coordinates
`y = (λ_k, s_k, q_k, …, λ_N, s_N)` of stages `≥ k`, with the Euclidean structure. -/
abbrev PD (P : OCP) (k : ℕ) := EuclideanSpace ℝ {c : Coord P // k ≤ stage c}

/-- Generic coordinate map between Euclidean spaces: coordinate `j` of the image is coordinate `g j` of
the argument, or `0` if `g j = none`. All restrictions and zero extensions below are of this form. -/
def pull {ι ι' : Type} [Fintype ι] [Fintype ι'] (g : ι' → Option ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι' :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (fun j => match g j with
        | some i => y i
        | none => 0)
      map_add' := by
        intro a b; ext j; simp only [PiLp.add_apply]; split <;> simp
      map_smul' := by
        intro c a; ext j; simp only [PiLp.smul_apply]; split <;> simp }

/-- `Π^{k+1} : ℝ^{n_k} → ℝ^{n_{k+1}}`, `(λ_k, s_k, q_k, ỹ) ↦ ỹ`: drops the stage-`k` coordinates. -/
def proj (P : OCP) (k : ℕ) : PD P k →L[ℝ] PD P (k + 1) :=
  pull (fun c => some ⟨c.1, Nat.le_of_succ_le c.2⟩)

/-- `(Π^{k+1})ᵀ : ℝ^{n_{k+1}} → ℝ^{n_k}`, `ỹ ↦ (0, 0, 0, ỹ)`: extension by zero. -/
def projT (P : OCP) (k : ℕ) : PD P (k + 1) →L[ℝ] PD P k :=
  pull (fun c => if h : k + 1 ≤ stage c.1 then some ⟨c.1, h⟩ else none)

/-- `Π^k ⋯ Π^1 : ℝ^{n_0} → ℝ^{n_k}`: drops the coordinates of stages `< k`. -/
def projTo (P : OCP) (k : ℕ) : PD P 0 →L[ℝ] PD P k :=
  pull (fun c => some ⟨c.1, Nat.zero_le _⟩)

/-- `(Π^k ⋯ Π^1)ᵀ : ℝ^{n_k} → ℝ^{n_0}`: extension by zero. -/
def liftFrom (P : OCP) (k : ℕ) : PD P k →L[ℝ] PD P 0 :=
  pull (fun c => if h : k ≤ stage c.1 then some ⟨c.1, h⟩ else none)

/-- The stage-`i` multiplier `λ_i` of `y ∈ ℝ^{n_k}` (zero unless `k ≤ i ≤ N`). -/
def lamL (P : OCP) (k i : ℕ) : PD P k →L[ℝ] Vec P.nx :=
  pull (fun j => if h : i < P.N + 1 ∧ k ≤ i then
    some ⟨Sum.inl (⟨i, h.1⟩, j), by simpa [stage] using h.2⟩ else none)

/-- The stage-`i` state `s_i` of `y ∈ ℝ^{n_k}` (zero unless `k ≤ i ≤ N`). -/
def sL (P : OCP) (k i : ℕ) : PD P k →L[ℝ] Vec P.nx :=
  pull (fun j => if h : i < P.N + 1 ∧ k ≤ i then
    some ⟨Sum.inr (Sum.inl (⟨i, h.1⟩, j)), by simpa [stage] using h.2⟩ else none)

/-- The stage-`i` control `q_i` of `y ∈ ℝ^{n_k}` (zero unless `k ≤ i < N`). -/
def qL (P : OCP) (k i : ℕ) : PD P k →L[ℝ] Vec P.nu :=
  pull (fun j => if h : i < P.N ∧ k ≤ i then
    some ⟨Sum.inr (Sum.inr (⟨i, h.1⟩, j)), by simpa [stage] using h.2⟩ else none)

/-- Zero extension `ℝ^{n_x} → ℝ^{n_k}` into the `s_i` coordinates (transpose of `sL`). -/
def sT (P : OCP) (k i : ℕ) : Vec P.nx →L[ℝ] PD P k :=
  pull (fun c => match c.1 with
    | Sum.inr (Sum.inl (i', j)) => if i'.val = i then some j else none
    | _ => none)

/-- Zero extension `ℝ^{n_u} → ℝ^{n_k}` into the `q_i` coordinates (transpose of `qL`). -/
def qT (P : OCP) (k i : ℕ) : Vec P.nu →L[ℝ] PD P k :=
  pull (fun c => match c.1 with
    | Sum.inr (Sum.inr (i', j)) => if i'.val = i then some j else none
    | _ => none)

/-- `π_i`: reads the block `(s_i, q_i)` of `y ∈ ℝ^{n_k}`. -/
def blockSQ (P : OCP) (k i : ℕ) : PD P k →L[ℝ] Vec P.nx × Vec P.nu :=
  (sL P k i).prod (qL P k i)

/-- `ι_i`: zero extension of a block `(s_i, q_i)` into `ℝ^{n_k}` (transpose of `π_i`). -/
def embSQ (P : OCP) (k i : ℕ) : Vec P.nx × Vec P.nu →L[ℝ] PD P k :=
  (sT P k i).coprod (qT P k i)

/-- The Lagrangian `ℒ^k(y)` of `P_k(x)` (§2, p. 1717):
`Σ_{i=k}^{N-1} L_i(s_i,q_i) + E(s_N) + λ_kᵀ(x − s_k) + Σ_{i=k}^{N-1} λ_{i+1}ᵀ(f_i(s_i,q_i) − s_{i+1})`. -/
def lagr (P : OCP) (k : ℕ) (x : Vec P.nx) (y : PD P k) : ℝ :=
  (∑ i ∈ Finset.Ico k P.N, P.L i (sL P k i y) (qL P k i y)) + P.Eterm (sL P k P.N y)
    + ⟪lamL P k k y, x - sL P k k y⟫_ℝ
    + ∑ i ∈ Finset.Ico k P.N,
        ⟪lamL P k (i + 1) y, P.f i (sL P k i y) (qL P k i y) - sL P k (i + 1) y⟫_ℝ

/-- `∇_y ℒ^k(y)` for the initial value `x`. -/
def grad (P : OCP) (k : ℕ) (x : Vec P.nx) (y : PD P k) : PD P k :=
  gradient (lagr P k x) y

/-- `∇²_y ℒ^k(y)`. It does not depend on `x`, which enters `ℒ^k` linearly (Remark 1); it is computed
at `x = 0`. -/
def hess (P : OCP) (k : ℕ) (y : PD P k) : PD P k →L[ℝ] PD P k :=
  fderiv ℝ (fun z => gradient (lagr P k 0) z) y

/-- The Newton-type matrix `J^k(y)` (§2.1, p. 1718): `∇²_y ℒ^k(y)` with each diagonal block
`(s_i, q_i)`, `k ≤ i < N`, replaced by `QH i (s_i) (q_i) (λ_{i+1})` and the block `s_N` replaced by
`QHN (s_N)`. -/
def J (P : OCP) (k : ℕ) (y : PD P k) : PD P k →L[ℝ] PD P k :=
  hess P k y
    + (∑ i ∈ Finset.Ico k P.N,
        (embSQ P k i).comp
          ((P.QH i (sL P k i y) (qL P k i y) (lamL P k (i + 1) y)
              - (blockSQ P k i).comp ((hess P k y).comp (embSQ P k i))).comp (blockSQ P k i)))
    + (sT P k P.N).comp
        ((P.QHN (sL P k P.N y)
            - (sL P k P.N).comp ((hess P k y).comp (sT P k P.N))).comp (sL P k P.N))

end RealTimeIter.Contract

end


