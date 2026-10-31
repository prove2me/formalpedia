-- Prove2me | Definitions.Def_ZeroOneSCO_Equations
-- name    : ZeroOneSCO_Equations
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:52:27.850984+00:00
-- url     : https://prove2.me/theorems/1406ade6-30c8-4f8f-a1d7-b44c00d0748b
-- title:
--   The $\tau$-stationarity conditions (58), the system $F(w;\mathcal V)$, the matrix $\nabla F_\mu(w;\mathcal V)$, $\tau<\tau_*$ and Assumption 2
-- statement:
--   This module sets up the equations of the semismooth Newton method.
--
--   **Variables.** A point is $w:=(x;\mathrm{vec}(W))\in\mathbb R^{K+MN}$, with $Z:=G(x)$ and $\Lambda:=Z+\tau W$. For $T\subseteq\mathcal N$, $U_T:=\{(m,n)\in\mathcal M\times T:\Lambda_{mn}\ge0\}$.
--
--   **Stationarity.** A point $x^*$ is $\tau$-stationary, with multiplier $W^*$, if
--   $$
--   x^*=\Pi_\Omega\bigl(x^*-\tau[\nabla f(x^*)+\textstyle\sum W^*_{mn}\nabla G_{mn}(x^*)]\bigr),\qquad Z^*\in\Pi_{\mathcal S}(Z^*+\tau W^*),
--   $$
--   where $Z^*:=G(x^*)$, and one writes $\mathcal V_*:=V_{\Gamma_0^*}$ for the zero entries of $Z^*$ in the columns $\Gamma_0^*$ of zero maximum.
--
--   **The system.** For $\mathcal V\subseteq\mathcal M\times\mathcal N$,
--   $$
--   \varphi(w;\mathcal V):=x-\Pi_\Omega\bigl(x-\tau[\nabla f(x)+\textstyle\sum_{\mathcal V}W_{mn}\nabla G_{mn}(x)]\bigr),\qquad
--   F(w;\mathcal V):=\begin{bmatrix}\varphi(w;\mathcal V)\\ \mathrm{vec}(Z_{\mathcal V})\\ \mathrm{vec}(W_{\overline{\mathcal V}})\end{bmatrix},
--   $$
--   and for $H=[P\ Q\ 0]\in\partial\varphi(w;\mathcal V)$ and $\mu\ge 0$,
--   $$
--   \nabla F_\mu(w;\mathcal V):=\begin{bmatrix}P&Q&0\\ \nabla_{\mathcal V}G(x)^\top&-\mu I_{|\mathcal V|}&0\\ 0&0&I_{|\overline{\mathcal V}|}\end{bmatrix}.
--   $$
--
--   **The threshold.** With $\tau_*:=(Z^*)^{\downarrow}_s/\max_{n\in\Gamma_0^*}\|W^*_{:n}\|$, and $\tau_*=+\infty$ when $\|Z^*\|_0^+<s$ or $W^*_{:\Gamma_0^*}=0$, the hypothesis $\tau<\tau_*$ says that if $\|Z^*\|_0^+=s$ then $\tau\|W^*_{:n}\|<(Z^*)^{\downarrow}_s$ for every $n\in\Gamma_0^*$.
--
--   **Assumption 2.** The map $\varphi(\cdot;\mathcal V_*)$ is semismooth at $w^*$, and for every $\mathcal V\subseteq\mathcal V_*$ and every $H^*=[P^*\ Q^*\ 0]\in\partial\varphi(w^*;\mathcal V)$ the matrix
--   $$
--   \begin{bmatrix}P^*&Q^*\\ \nabla_{\mathcal V}G(x^*)^\top&0\end{bmatrix}
--   $$
--   is nonsingular.
--
--   **Formalization Note** `Wsp K M N` is the Euclidean space on the index type `Fin K ⊕ (Fin M × Fin N)`, so `Fmap` and `newtonMat` carry no block reordering; they are the page's vector and matrix up to one permutation. The block $0$ of $H$ on $W_{\overline{\mathcal V}}$ is automatic, as $\varphi(\cdot;\mathcal V)$ ignores those coordinates. `projOmega` is chosen by `Classical.epsilon` and `projOmega_spec` shows that it is a projection for nonempty closed $\Omega$. `IsTauStationary` takes $W^*$ as an argument. `BelowTauStar` has no division, and does not include $\tau>0$. The Clarke Jacobian is the reused `NonsmoothNewton.Shared.clarkeJac`, taken in the whole variable $w$ with $\mathcal V$ fixed.
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, pp.7, 12, 14, 17, 20, (20), (52), (58), (67)–(70), (83), Assumption 2

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_ZeroOneSCO_Columns
import Definitions.Def_ZeroOneSCO_Semismooth

namespace ZeroOneSCO

/-- The decision space `ℝ^K` of Zhou, Pan, Xiu & Li, arXiv:2210.11889v5, p.3. -/
abbrev Pt (K : ℕ) := EuclideanSpace ℝ (Fin K)

/-- Index set of the variable `w = (x; vec(W))` of arXiv:2210.11889v5, (67), p.17. -/
abbrev Idx (K M N : ℕ) := Fin K ⊕ (Fin M × Fin N)

/-- The space `ℝ^{K+MN}` of `w = (x; vec(W))`, arXiv:2210.11889v5, (67), p.17.

**Formalization Note.** Indexed by `Idx K M N` in place of the stacking order of `vec`. Its Euclidean
norm is the paper's `‖w‖`. -/
abbrev Wsp (K M N : ℕ) := EuclideanSpace ℝ (Idx K M N)

/-- The part `x` of `w = (x; vec(W))`, arXiv:2210.11889v5, (67), p.17. -/
noncomputable def xPart {K M N : ℕ} (w : Wsp K M N) : Pt K :=
  WithLp.toLp 2 fun k => w (Sum.inl k)

/-- The part `W` of `w = (x; vec(W))`, arXiv:2210.11889v5, (67), p.17. -/
noncomputable def wPart {K M N : ℕ} (w : Wsp K M N) : Mat M N :=
  Matrix.of fun m n => w (Sum.inr (m, n))

/-- `w = (x; vec(W))` built from `x` and `W`, arXiv:2210.11889v5, (67), p.17. -/
noncomputable def pack {K M N : ℕ} (x : Pt K) (W : Mat M N) : Wsp K M N :=
  WithLp.toLp 2 (Sum.elim (fun k => x k) (fun p => W p.1 p.2))

/-- The action `v ↦ A v` of a square matrix on the Euclidean space of its index type. -/
noncomputable def applyMat {I : Type*} [Fintype I] (A : Matrix I I ℝ)
    (v : EuclideanSpace ℝ I) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (A.mulVec v.ofLp)

/-- `p` is a Euclidean projection of `z` onto `Ω`, arXiv:2210.11889v5, (20), p.7. -/
def IsProjOnto {K : ℕ} (Ω : Set (Pt K)) (z p : Pt K) : Prop :=
  p ∈ Ω ∧ ∀ y ∈ Ω, ‖z - p‖ ≤ ‖z - y‖

/-- `Π_Ω(z)`, arXiv:2210.11889v5, (20), p.7: the paper writes it as a point because the minimizer is
unique for a nonempty closed convex `Ω` (p.7).

**Formalization Note.** Chosen by `Classical.epsilon`, so it is meaningful when `Ω` is nonempty and
closed; see `projOmega_spec`. -/
noncomputable def projOmega {K : ℕ} (Ω : Set (Pt K)) (z : Pt K) : Pt K :=
  Classical.epsilon (IsProjOnto Ω z)

/-- `projOmega` is a projection whenever `Ω` is nonempty and closed. -/
theorem projOmega_spec {K : ℕ} {Ω : Set (Pt K)} (hne : Ω.Nonempty) (hc : IsClosed Ω) (z : Pt K) :
    IsProjOnto Ω z (projOmega Ω z) := by
  obtain ⟨p, hp, hd⟩ := hc.exists_infDist_eq_dist hne z
  refine Classical.epsilon_spec (p := IsProjOnto Ω z) ⟨p, hp, fun y hy => ?_⟩
  rw [← dist_eq_norm, ← dist_eq_norm, ← hd]
  exact Metric.infDist_le_dist_of_mem hy

/-- `∇G_mn(x)`, the gradient of the entry `x ↦ G_mn(x)`, arXiv:2210.11889v5, p.5. -/
noncomputable def gradG {K M N : ℕ} (G : Pt K → Mat M N) (x : Pt K) (m : Fin M) (n : Fin N) : Pt K :=
  gradient (fun y => G y m n) x

/-- `(x*, W*)` satisfies the `τ`-stationarity conditions (58) of arXiv:2210.11889v5, p.14:
`x* = Π_Ω(x* − τ[∇f(x*) + ∑ W*_mn ∇G_mn(x*)])` and `Z* ∈ Π_S(Z* + τW*)` with `Z* = G(x*)`.

**Formalization Note.** The page's "there is a `W*`" is the explicit argument `Ws`. -/
def IsTauStationary {K M N : ℕ} [NeZero M] (f : Pt K → ℝ) (G : Pt K → Mat M N) (Ω : Set (Pt K))
    (s : ℕ) (τ : ℝ) (xs : Pt K) (Ws : Mat M N) : Prop :=
  xs = projOmega Ω
      (xs - τ • (gradient f xs + ∑ p : Fin M × Fin N, Ws p.1 p.2 • gradG G xs p.1 p.2)) ∧
    G xs ∈ projS s (G xs + τ • Ws)

/-- `Λ := Z + τW` with `Z = G(x)`, arXiv:2210.11889v5, (67), p.17. -/
noncomputable def Lam {K M N : ℕ} (G : Pt K → Mat M N) (τ : ℝ) (w : Wsp K M N) : Mat M N :=
  G (xPart w) + τ • wPart w

/-- `U_T := {(m,n) ∈ M × T : Λ_mn ≥ 0}`, arXiv:2210.11889v5, (67), p.17. -/
noncomputable def U {M N : ℕ} (T : Finset (Fin N)) (Λ : Mat M N) : Finset (Fin M × Fin N) :=
  Finset.univ.filter fun p => p.2 ∈ T ∧ 0 ≤ Λ p.1 p.2

/-- `V* := V_{Γ₀(Z)}(Z)` for `Z = Z*`, arXiv:2210.11889v5, (52), p.12. -/
noncomputable def Vstar {M N : ℕ} [NeZero M] (Z : Mat M N) : Finset (Fin M × Fin N) :=
  VGamma (gammaZero Z) Z

/-- `ϕ(w; V) := x − Π_Ω(x − τ[∇f(x) + ∑_V W_mn ∇G_mn(x)])`, arXiv:2210.11889v5, (67), p.17. -/
noncomputable def phi {K M N : ℕ} (f : Pt K → ℝ) (G : Pt K → Mat M N) (Ω : Set (Pt K)) (τ : ℝ)
    (w : Wsp K M N) (V : Finset (Fin M × Fin N)) : Pt K :=
  xPart w - projOmega Ω (xPart w - τ • (gradient f (xPart w) +
    ∑ p ∈ V, wPart w p.1 p.2 • gradG G (xPart w) p.1 p.2))

/-- `F(w; V)`, arXiv:2210.11889v5, (68), p.17.

**Formalization Note.** The blocks `ϕ(w; V)`, `vec(Z_V)`, `vec(W_V̄)` are written on the index type
`Idx K M N`: the coordinate `inl k` carries `ϕ_k`, and `inr (m,n)` carries `Z_mn` if `(m,n) ∈ V` and
`W_mn` otherwise. This is the page's vector up to one permutation of coordinates, which preserves
the Euclidean norm. -/
noncomputable def Fmap {K M N : ℕ} (f : Pt K → ℝ) (G : Pt K → Mat M N) (Ω : Set (Pt K)) (τ : ℝ)
    (w : Wsp K M N) (V : Finset (Fin M × Fin N)) : Wsp K M N :=
  WithLp.toLp 2 (Sum.elim (fun k => phi f G Ω τ w V k)
    (fun p => if p ∈ V then G (xPart w) p.1 p.2 else wPart w p.1 p.2))

/-- `∇F_µ(w; V)`, arXiv:2210.11889v5, (69), p.17, for `H = [P Q 0] ∈ ∂ϕ(w; V)`.

**Formalization Note.** Written on `Idx K M N` with no block reordering, so it is the page's matrix up
to one simultaneous permutation of rows and columns. Row `inl k` is row `k` of `H`, whose entries on
`W_V̄` vanish for `H ∈ ∂ϕ(·; V)(w)` because `ϕ(·; V)` ignores `W_V̄`: this is the page's `0` block.
Row `inr p` with `p ∈ V` is `∇G_p(x)ᵀ` followed by `−µ` on the diagonal. Row `inr p` with `p ∉ V` is the
unit row. -/
noncomputable def newtonMat {K M N : ℕ} (G : Pt K → Mat M N) (μ : ℝ) (w : Wsp K M N)
    (V : Finset (Fin M × Fin N)) (H : Wsp K M N →L[ℝ] Pt K) :
    Matrix (Idx K M N) (Idx K M N) ℝ :=
  Matrix.of fun i j =>
    match i with
    | Sum.inl k => H (EuclideanSpace.single j 1) k
    | Sum.inr p =>
      if p ∈ V then
        match j with
        | Sum.inl l => gradG G (xPart w) p.1 p.2 l
        | Sum.inr q => if q = p then -μ else 0
      else if j = Sum.inr p then 1 else 0

/-- The hypothesis `0 < τ < τ*` of Lemmas 2 and 3 of arXiv:2210.11889v5, p.20, without the `τ > 0`
part, where `τ* := (Z*)↓_s / max_{n ∈ Γ₀*} ‖W*_{:n}‖` (p.14) and `τ* = +∞` when `‖Z*‖₀⁺ < s` or
`W*_{:Γ₀*} = 0`.

**Formalization Note.** Stated with no division: when `‖Z*‖₀⁺ = s`, every `n ∈ Γ₀*` has
`τ ‖W*_{:n}‖ < (Z*)↓_s`. A literal quotient would be `0` in Lean when the maximum vanishes. -/
def BelowTauStar {K M N : ℕ} [NeZero M] (G : Pt K → Mat M N) (s : ℕ) (τ : ℝ) (xs : Pt K)
    (Ws : Mat M N) : Prop :=
  plusZero (G xs) = s → ∀ n ∈ gammaZero (G xs), τ * colNorm Ws n < rthLargest (G xs) s

/-- The matrix (83) of arXiv:2210.11889v5, p.20, on `ℝ^{K+|V|}`: `[P Q; ∇_V G(x)ᵀ 0]`, where `P`, `Q` are
the blocks of `H` on the `x`-coordinates and on the `W_V`-coordinates. -/
noncomputable def reducedMat {K M N : ℕ} (G : Pt K → Mat M N) (x : Pt K)
    (V : Finset (Fin M × Fin N)) (H : Wsp K M N →L[ℝ] Pt K) :
    Matrix (Fin K ⊕ V) (Fin K ⊕ V) ℝ :=
  Matrix.fromBlocks
    (Matrix.of fun k l => H (EuclideanSpace.single (Sum.inl l) 1) k)
    (Matrix.of fun k (p : V) => H (EuclideanSpace.single (Sum.inr p.1) 1) k)
    (Matrix.of fun (p : V) l => gradG G x p.1.1 p.1.2 l)
    0

/-- Assumption 2 of arXiv:2210.11889v5, p.20: `ϕ(·; V*)` is semismooth at `w*` and the matrix (83) is
nonsingular for every `V ⊆ V*` and every `H* ∈ ∂ϕ(w*; V)`. -/
def Assumption2 {K M N : ℕ} [NeZero M] (f : Pt K → ℝ) (G : Pt K → Mat M N) (Ω : Set (Pt K))
    (τ : ℝ) (xs : Pt K) (Ws : Mat M N) : Prop :=
  SemismoothAt10 (fun w => phi f G Ω τ w (Vstar (G xs))) (pack xs Ws) ∧
  ∀ V ⊆ Vstar (G xs), ∀ H ∈ NonsmoothNewton.Shared.clarkeJac (fun w => phi f G Ω τ w V) (pack xs Ws),
    IsUnit (reducedMat G xs V H).det

end ZeroOneSCO


