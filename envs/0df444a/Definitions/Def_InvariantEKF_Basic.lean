-- Prove2me | Definitions.Def_InvariantEKF_Basic
-- name    : InvariantEKF_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T01:15:42.714189+00:00
-- url     : https://prove2.me/theorems/687ef9c9-2f00-47fe-9961-a03296229460
-- title:
--   Matrix Lie groups, invariant errors, the invariant EKF and the Deyst-Price conditions
-- statement:
--   Objects of Sections 2-3 and Appendices A-C of Barrau and Bonnabel, *The invariant extended Kalman filter as a stable observer* (arXiv:1410.1465v4).
--
--   1. **Matrices.** $\|A\|_F$ is the Frobenius norm. $A\preceq B$ means that $B-A$ is positive semidefinite. Derivatives of matrix-valued functions are taken entry by entry.
--   2. **Matrix Lie groups (Appendix A).** A matrix Lie group is a set $G\subset\mathbb R^{N\times N}$ of invertible matrices that contains $I$, is closed under inverses and products, and is a closed subgroup of $GL_N(\mathbb R)$. A linear map $\mathcal L_{\mathfrak g}:\mathbb R^{\dim\mathfrak g}\to\mathbb R^{N\times N}$ is a coordinate map of the Lie algebra if it is injective with range $\mathfrak g=\{X:\exp_m(sX)\in G\ \forall s\in\mathbb R\}$. The group exponential is $\exp(\xi)=\exp_m(\mathcal L_{\mathfrak g}(\xi))$.
--   3. **Systems and errors (Section 2).** A trajectory of $\frac{d}{dt}\chi_t=f_{u_t}(\chi_t)$ on a time set $S$ takes values in $G$ and has the derivative $f_{u_t}(\chi_t)$ at every $t\in S$ (one-sided at an endpoint). The left- and right-invariant errors are $\eta^L=\chi^{-1}\bar\chi$ and $\eta^R=\bar\chi\chi^{-1}$ (eqs. 5-6). An error is *state-trajectory independent* (Definition 1) if a single function $g$ gives $\frac{d}{dt}\eta_t=g_{u_t}(\eta_t)$ for every pair of trajectories. The system is *group affine* (eq. 12) if $f_u(ab)=f_u(a)b+af_u(b)-af_u(I)b$ for all $u$ and $a,b\in G$. The error fields are $g^L_u(\eta)=f_u(\eta)-f_u(I)\eta$ and $g^R_u(\eta)=f_u(\eta)-\eta f_u(I)$ (eqs. 8-9). A matrix $A$ is the linearization of $g$ if $g(\exp\xi)=\mathcal L_{\mathfrak g}(A\xi)+O(\|\xi\|^2)$ as $\xi\to0$. As a standing regularity condition, the field $(t,X)\mapsto F_t(X)$ is locally Lipschitz in $X$, uniformly for $t$ in each window $[0,T]$.
--   4. **Simplified car (Section 2.1).** For car states $(\theta,x^1,x^2)$ and $(\bar\theta,\bar x^1,\bar x^2)$ with $s=\theta-\bar\theta$, the logarithmic error is $\xi=\big(s,\ \tfrac12 s\,[a(s)I_2-J_2]\,R(-\bar\theta)(X-\bar X)\big)$ with $a(s)=\sin s/(1-\cos s)$. The factor $\tfrac12 s\,a(s)$ takes its limit value $1$ at $s=0$.
--   5. **IEKF (Section 3, eqs. 36-37).** The observations $Y^i=\chi d^i$ (left-invariant) or $Y^i=\chi^{-1}d^i$ (right-invariant), $i=1,\dots,k$, are taken at the times $t_n=n\,\Delta t$. Between observations the estimate follows $\frac{d}{dt}\hat\chi_t=f_{u_t}(\hat\chi_t)$, and $P_t$ follows $\frac{d}{dt}P=A_{u_t}P+PA_{u_t}^T+\hat Q_t(\hat\chi_t)$. At $t_n$ the update is $\hat\chi^+=\hat\chi\exp(L_nz)$ (LIEKF) or $\hat\chi^+=\exp(L_nz)\hat\chi$ (RIEKF), with $P^+=(I-L_nH)P$. Here $z=(\hat\chi^{-1}Y^i-d^i)_i$ or $z=(\hat\chi Y^i-d^i)_i$, the gain is $L_n=PH^TS^{-1}$ with $S=HPH^T+\hat N_n(\hat\chi_{t_n})$, and $H\xi=(\mathcal L_{\mathfrak g}(\xi)d^i)_i$ for the LIEKF and $H\xi=(-\mathcal L_{\mathfrak g}(\xi)d^i)_i$ for the RIEKF. A filter started at $t_0$ is stored as one propagation segment per sampling interval. Its value at an observation time is the updated value.
--   6. **Linear Kalman filter and Deyst-Price conditions (Theorem 3).** $\Phi_s^t$ is the transition matrix of $\dot x=A_tx$. Conditions (i)-(v) are: $(\Phi_{t_n}^{t_{n+1}})^T\Phi_{t_n}^{t_{n+1}}\succeq\delta_1I$; $Q_s=G_sQ'G_s^T$ with $Q'\succeq\delta_2I_q$; $N_n\succeq\delta_3I$; $\alpha_1I\preceq\int_{t_{n-M}}^{t_n}\Phi_s^{t_n}Q_s(\Phi_s^{t_n})^Tds\preceq\alpha_2I$; and $\beta_1I\preceq\sum_{i=n-M}^{n}(\Phi_{t_n}^{t_i})^TH^TN_i^{-1}H\Phi_{t_n}^{t_i}\preceq\beta_2I$. The *bounded transition* condition is $(\Phi_s^t)^T\Phi_s^t\preceq cI$ for $s,t$ in one sampling interval.
--   7. **Stability (Definition 2).** The distance between the true state and the estimate is measured through the invariant error: $\|\chi^{-1}\hat\chi-I\|_F$ for the LIEKF and $\|\hat\chi\chi^{-1}-I\|_F$ for the RIEKF. The design matrices are *comparable along the true trajectory* if for every $\kappa>1$ there is $\varepsilon>0$ such that an error $\exp(\xi)$ with $\|\xi\|<\varepsilon$ gives $\kappa^{-1}\hat Q_t(\chi_t)\preceq\hat Q_t(\hat\chi_t)\preceq\kappa\hat Q_t(\chi_t)$, and the same for $\hat N_n$.
--
--   **Formalization Note** The paper does not fix the distance $d$ of Definition 2. The invariant-error distance is used because it is the quantity the proof controls. Section 3.3 prints $H$ with the opposite sign. With that sign, the linearized update is $\xi^+=(I+L_nH)\xi$ and the filter diverges. The sign used here is the one of the paper's worked examples (Sections 4.2.3, 4.2.4, 5.2.3). Condition (v) is printed with $\Phi_{t_{i+1}}^{t_n}$, $i=n-M,\dots,n-1$, and $N_n$. It is written here in the form of Deyst and Price.
-- source:
--   Barrau and Bonnabel, The invariant extended Kalman filter as a stable observer, arXiv:1410.1465v4 (2015), Sections 2.1-2.3 (eqs. (2)-(13)), Section 3 (eqs. (14)-(37)), Section 3.4 (Definition 2, Theorem 3), Appendices A-C

import Mathlib

/-!
A. Barrau and S. Bonnabel, *The invariant extended Kalman filter as a stable observer*,
arXiv:1410.1465v4 (2015): matrix Lie groups and their exponential coordinates (Appendix A),
systems on matrix Lie groups and their invariant errors (Section 2.2, eqs. (4)-(9) and (12)),
the logarithmic error of the simplified car (Section 2.1, eq. (2)), the invariant extended Kalman
filter with discrete observations and its Riccati equation (Section 3, eqs. (14)-(37)), the
linear Kalman filter and the Deyst-Price conditions of Theorem 3, and the stability notion of
Definition 2 (Section 3.4).
-/

open MeasureTheory Matrix

noncomputable section

namespace InvariantEKF

/-! ### Matrix utilities -/

/-- Frobenius norm of a real matrix, used as the distance on matrices. -/
def frob {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- The Loewner order `A ⪯ B` of Theorem 3 and Appendix C: `B - A` is positive semidefinite. -/
def LoewnerLE {m : Type*} [Fintype m] (A B : Matrix m m ℝ) : Prop :=
  (B - A).PosSemidef

/-- The matrix-valued function `X` has derivative `D` at `t` within `S`, entry by entry. -/
def HasMatDerivWithinAt {m n : Type*} (X : ℝ → Matrix m n ℝ) (D : Matrix m n ℝ) (S : Set ℝ)
    (t : ℝ) : Prop :=
  ∀ i j, HasDerivWithinAt (fun s => X s i j) (D i j) S t

/-- The matrix-valued function `X` has derivative `D` at `t`, entry by entry. -/
def HasMatDerivAt {m n : Type*} (X : ℝ → Matrix m n ℝ) (D : Matrix m n ℝ) (t : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun s => X s i j) (D i j) t

/-! ### Matrix Lie groups (Appendix A) -/

/-- Appendix A: a matrix Lie group `G ⊂ ℝ^{N×N}` is a set of invertible matrices containing `Id`
and closed under inversion and products; as a Lie group it is a closed subgroup of `GL_N(ℝ)`
(every limit of elements of `G` that is invertible lies in `G`). -/
def IsMatrixLieGroup {N : ℕ} (G : Set (Matrix (Fin N) (Fin N) ℝ)) : Prop :=
  (1 : Matrix (Fin N) (Fin N) ℝ) ∈ G ∧ (∀ a ∈ G, IsUnit a.det ∧ a⁻¹ ∈ G) ∧
    (∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) ∧
    ∀ (x : ℕ → Matrix (Fin N) (Fin N) ℝ) (a : Matrix (Fin N) (Fin N) ℝ),
      (∀ n, x n ∈ G) → Filter.Tendsto x Filter.atTop (nhds a) → IsUnit a.det → a ∈ G

/-- Appendix A: `L_𝔤 : ℝ^{dim 𝔤} → 𝔤` is a linear isomorphism onto the Lie algebra `𝔤` of `G`,
the set of matrices `X` with `exp_m(sX) ∈ G` for all real `s`. -/
def IsLieAlgebraCoords {N d : ℕ} (G : Set (Matrix (Fin N) (Fin N) ℝ))
    (L : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ) : Prop :=
  Function.Injective L ∧
    ∀ X : Matrix (Fin N) (Fin N) ℝ, X ∈ LinearMap.range L ↔ ∀ s : ℝ, NormedSpace.exp (s • X) ∈ G

/-- Appendix A: the exponential `exp(ξ) = exp_m(L_𝔤(ξ))` of `ξ ∈ ℝ^{dim 𝔤}`. -/
def expG {N d : ℕ} (L : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ) (ξ : Fin d → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  NormedSpace.exp (L ξ)

/-! ### Systems on matrix Lie groups and invariant errors (Section 2) -/

/-- Eq. (12) (and eq. (14)): the vector fields `f_u` satisfy
`f_u(ab) = f_u(a) b + a f_u(b) - a f_u(Id) b` for every input `u` and all `a, b ∈ G`. -/
def IsGroupAffine {N : ℕ} {U : Type*} (G : Set (Matrix (Fin N) (Fin N) ℝ))
    (f : U → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ v a b, a ∈ G → b ∈ G → f v (a * b) = f v a * b + a * f v b - a * f v 1 * b

/-- `X` solves `dX/dt = F_t(X_t)` at every time of `S` (derivatives within `S`). -/
def IsSolution {N : ℕ} (F : ℝ → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ)
    (S : Set ℝ) (X : ℝ → Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ t ∈ S, HasMatDerivWithinAt X (F t (X t)) S t

/-- Eq. (4): a trajectory `χ_t` of `dχ_t/dt = f_{u_t}(χ_t)` on the time set `S`, with values
in `G`. -/
def IsTrajectory {N : ℕ} {U : Type*} (G : Set (Matrix (Fin N) (Fin N) ℝ))
    (f : U → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ) (u : ℝ → U) (S : Set ℝ)
    (χ : ℝ → Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ t ∈ S, χ t ∈ G) ∧ IsSolution (fun t => f (u t)) S χ

/-- Eqs. (5)-(6): the left-invariant error `η^L = χ⁻¹ χ̄` (`left = true`) or the
right-invariant error `η^R = χ̄ χ⁻¹` (`left = false`) between `χ` and `χ̄`. -/
def invError {N : ℕ} (left : Bool) (χ χbar : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  if left then χ⁻¹ * χbar else χbar * χ⁻¹

/-- Definition 1 (Section 2.2): the left (`left = true`) or right invariant error has a
state-trajectory independent propagation: for one function `g`, the error between any two
trajectories of eq. (4) on `t > 0` satisfies `dη_t/dt = g_{u_t}(η_t)`. -/
def ErrorAutonomous {N : ℕ} {U : Type*} (left : Bool) (G : Set (Matrix (Fin N) (Fin N) ℝ))
    (f : U → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ) (u : ℝ → U) : Prop :=
  ∃ g : U → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ,
    ∀ χ χbar : ℝ → Matrix (Fin N) (Fin N) ℝ,
      IsTrajectory G f u (Set.Ioi 0) χ → IsTrajectory G f u (Set.Ioi 0) χbar →
        ∀ t, 0 < t → HasMatDerivAt (fun s => invError left (χ s) (χbar s))
          (g (u t) (invError left (χ t) (χbar t))) t

/-- Eqs. (8)-(9): `g^L_u(η) = f_u(η) - f_u(Id) η` (`left = true`) and
`g^R_u(η) = f_u(η) - η f_u(Id)` (`left = false`). -/
def errField {N : ℕ} {U : Type*} (left : Bool)
    (f : U → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ) (v : U)
    (η : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  if left then f v η - f v 1 * η else f v η - η * f v 1

/-- Standing regularity of the time-dependent vector field `F_t` (needed for "the flow" of
Appendix B to be well defined): on every time window `[0, T]` it is locally Lipschitz in the
state, uniformly in time, for the Frobenius distance. -/
def IsLocLipschitzField {N : ℕ}
    (F : ℝ → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ (T : ℝ) (X₀ : Matrix (Fin N) (Fin N) ℝ), ∃ r > 0, ∃ K : ℝ,
    ∀ t ∈ Set.Icc 0 T, ∀ X Y : Matrix (Fin N) (Fin N) ℝ, frob (X - X₀) < r → frob (Y - X₀) < r →
      frob (F t X - F t Y) ≤ K * frob (X - Y)

/-- Theorem 2 / eq. (20): `A` is the matrix defined by `g(exp(ξ)) = L_𝔤(A ξ) + O(‖ξ‖²)`. -/
def IsLinearization {N d : ℕ} (L : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ)
    (g : Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ C r : ℝ, 0 < r ∧ ∀ ξ : Fin d → ℝ, ‖ξ‖ < r →
    ∀ i j, |(g (expG L ξ) - L (A *ᵥ ξ)) i j| ≤ C * ‖ξ‖ ^ 2

/-! ### The simplified car of Section 2.1 -/

/-- Eq. (2): the factor `(s/2) a(s) = s sin s / (2(1 - cos s))`, extended by its limit `1`
at `s = 0`. -/
def carCoef (s : ℝ) : ℝ :=
  if s = 0 then 1 else s * Real.sin s / (2 * (1 - Real.cos s))

/-- Eq. (2): the non-linear error `ξ_t = (Δθ, ½ Δθ [a(Δθ) I₂ - J₂] R(-θ̄)(X - X̄))` between the
car states `(θ, x¹, x²)` and `(θ̄, x̄¹, x̄²)`, with `Δθ = θ - θ̄`. -/
def carLogError (θ x1 x2 θbar xbar1 xbar2 : ℝ) : Fin 3 → ℝ :=
  let s := θ - θbar
  let p := Real.cos θbar * (x1 - xbar1) + Real.sin θbar * (x2 - xbar2)
  let q := -Real.sin θbar * (x1 - xbar1) + Real.cos θbar * (x2 - xbar2)
  ![s, carCoef s * p + s / 2 * q, carCoef s * q - s / 2 * p]

/-- Eq. (3): the matrix of the linear error equation of Proposition 1, with the sign of the
`u_t` entry as the proof of Proposition 1 establishes it (see the statement). -/
def carErrorMatrix (uv ω : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 0, 0, ω; uv, -ω, 0]

/-! ### The invariant extended Kalman filter (Section 3) -/

/-- Eqs. (15) and (22): the observation `Y^i = χ d^i` (left-invariant, `left = true`) or
`Y^i = χ⁻¹ d^i` (right-invariant, `left = false`). -/
def obsY {N : ℕ} (left : Bool) (χ : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) : Fin N → ℝ :=
  if left then χ *ᵥ v else χ⁻¹ *ᵥ v

/-- Eq. (36): the stacked innovation `(χ̂⁻¹ Y^i - d^i)_i` (LIEKF) or `(χ̂ Y^i - d^i)_i` (RIEKF)
in `ℝ^{kN}`, indexed by `(i, a) ∈ {1..k} × {1..N}`. -/
def innovation {N K : ℕ} (left : Bool) (dvec : Fin K → Fin N → ℝ)
    (χhat : Matrix (Fin N) (Fin N) ℝ) (Y : Fin K → Fin N → ℝ) : Fin K × Fin N → ℝ :=
  fun p => ((if left then χhat⁻¹ else χhat) *ᵥ Y p.1) p.2 - dvec p.1 p.2

/-- Eq. (36): the update `χ̂⁺ = χ̂ exp(ζ)` (LIEKF) or `χ̂⁺ = exp(ζ) χ̂` (RIEKF), with
`ζ = L_n (innovation)`. -/
def iekfUpdate {N d : ℕ} (left : Bool) (L : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ)
    (χhat : Matrix (Fin N) (Fin N) ℝ) (ζ : Fin d → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  if left then χhat * expG L ζ else expG L ζ * χhat

/-- Section 3.3: the observation matrix `H ∈ ℝ^{kN × dim 𝔤}` of the IEKF, with the sign for which
the linearised innovation is `-Hξ` (the convention of the worked examples of Sections 4.2.3,
4.2.4 and 5.2.3): `Hξ = (L_𝔤(ξ) d^i)_i` for the LIEKF and `Hξ = (-L_𝔤(ξ) d^i)_i` for the RIEKF. -/
def obsH {N d K : ℕ} (left : Bool) (L : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ)
    (dvec : Fin K → Fin N → ℝ) : Matrix (Fin K × Fin N) (Fin d) ℝ :=
  fun p j => (if left then (1 : ℝ) else -1) * (L (Pi.single j 1) *ᵥ dvec p.1) p.2

/-- Eq. (37): the Kalman gain `L_n = P H^T S⁻¹` with `S = H P H^T + N`. -/
def kalmanGain {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix (Fin d) (Fin d) ℝ)
    (H : Matrix ι (Fin d) ℝ) (Nn : Matrix ι ι ℝ) : Matrix (Fin d) ι ℝ :=
  P * Hᵀ * (H * P * Hᵀ + Nn)⁻¹

/-- The propagation interval `[max(t₀, t_n), t_{n+1}]` between the observation times
`t_n = n dt`, for a filter started at time `t₀`. -/
def segIcc (t0 dt : ℝ) (n : ℕ) : Set ℝ :=
  Set.Icc (max t0 ((n : ℝ) * dt)) (((n : ℝ) + 1) * dt)

/-- The value at time `t` of a filter stored as one propagation segment per interval: the
segment `⌊t / dt⌋` (so the value at an observation time is the updated value). -/
def piecewiseRun {α : Type*} (xs : ℕ → ℝ → α) (dt t : ℝ) : α :=
  xs ⌊t / dt⌋₊ t

/-- Eq. (37): `P` solves the Riccati equation `dP/dt = A_t P + P A_tᵀ + Q_t` on each propagation
interval, starts at `P₀` at time `t₀`, and jumps to `P⁺ = (I - L_n H) P` at each observation time
`t_{n+1} = (n+1) dt`, where `L_n` uses the matrix `Nend n` of that observation. -/
def IsRiccatiRun {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → Matrix (Fin d) (Fin d) ℝ) (H : Matrix ι (Fin d) ℝ)
    (Q : ℕ → ℝ → Matrix (Fin d) (Fin d) ℝ) (Nend : ℕ → Matrix ι ι ℝ) (dt t0 : ℝ)
    (P0 : Matrix (Fin d) (Fin d) ℝ) (Ps : ℕ → ℝ → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ n : ℕ, t0 < ((n : ℝ) + 1) * dt →
    ((n : ℝ) * dt ≤ t0 → Ps n t0 = P0) ∧
    (∀ t ∈ segIcc t0 dt n,
      HasMatDerivWithinAt (Ps n) (A t * Ps n t + Ps n t * (A t)ᵀ + Q n t) (segIcc t0 dt n) t) ∧
    Ps (n + 1) (((n : ℝ) + 1) * dt) =
      (1 - kalmanGain (Ps n (((n : ℝ) + 1) * dt)) H (Nend n) * H) * Ps n (((n : ℝ) + 1) * dt)

/-- Eqs. (36)-(37): a run of the Left (`left = true`) or Right (`left = false`) Invariant EKF
started at time `t₀` from `(χ̂₀, P₀)`, observing the true trajectory `χ` at the times
`t_n = n dt` through eq. (15) or (22). Between observations `χ̂` follows eq. (14) and `P` the
Riccati equation with `A_{u_t}`; the design matrix `Q̂_t` is evaluated at the current estimate,
and `N̂_n` at the estimate just before the update. -/
def IsIEKFRun {N d K : ℕ} {U : Type*} (left : Bool)
    (L : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ)
    (f : U → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ) (u : ℝ → U)
    (A : U → Matrix (Fin d) (Fin d) ℝ) (dvec : Fin K → Fin N → ℝ) (dt : ℝ)
    (Qhat : ℝ → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin d) (Fin d) ℝ)
    (Nhat : ℕ → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin K × Fin N) (Fin K × Fin N) ℝ)
    (χ : ℝ → Matrix (Fin N) (Fin N) ℝ) (t0 : ℝ) (χhat0 : Matrix (Fin N) (Fin N) ℝ)
    (P0 : Matrix (Fin d) (Fin d) ℝ) (xs : ℕ → ℝ → Matrix (Fin N) (Fin N) ℝ)
    (Ps : ℕ → ℝ → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  IsRiccatiRun (fun t => A (u t)) (obsH left L dvec) (fun n t => Qhat t (xs n t))
      (fun n => Nhat (n + 1) (xs n (((n : ℝ) + 1) * dt))) dt t0 P0 Ps ∧
  ∀ n : ℕ, t0 < ((n : ℝ) + 1) * dt →
    ((n : ℝ) * dt ≤ t0 → xs n t0 = χhat0) ∧
    (∀ t ∈ segIcc t0 dt n, HasMatDerivWithinAt (xs n) (f (u t) (xs n t)) (segIcc t0 dt n) t) ∧
    xs (n + 1) (((n : ℝ) + 1) * dt) =
      iekfUpdate left L (xs n (((n : ℝ) + 1) * dt))
        (kalmanGain (Ps n (((n : ℝ) + 1) * dt)) (obsH left L dvec)
            (Nhat (n + 1) (xs n (((n : ℝ) + 1) * dt))) *ᵥ
          innovation left dvec (xs n (((n : ℝ) + 1) * dt))
            (fun i => obsY left (χ (((n : ℝ) + 1) * dt)) (dvec i)))

/-- Definition 2 for the IEKF: the distance between the true state `χ` and the estimate `χ̂`,
measured through the invariant error, `‖χ⁻¹χ̂ - Id‖` (LIEKF) or `‖χ̂χ⁻¹ - Id‖` (RIEKF). -/
def invErrDist {N : ℕ} (left : Bool) (χ χhat : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  frob (invError left χ χhat - 1)

/-- The estimate `exp(ξ) χ` or `χ exp(ξ)` whose invariant error with `χ` is `exp(ξ)`. -/
def perturbed {N d : ℕ} (left : Bool) (L : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ)
    (χ : Matrix (Fin N) (Fin N) ℝ) (ξ : Fin d → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  if left then χ * expG L ξ else expG L ξ * χ

/-- Appendix C, proof of Lemma 4: the design matrices evaluated at estimates close to the true
trajectory are comparable with their values on the true trajectory: for every `κ > 1` there is
`ε > 0` such that an invariant error `exp(ξ)` with `‖ξ‖ < ε` gives
`κ⁻¹ Q̂(χ_t) ⪯ Q̂(χ̂_t) ⪯ κ Q̂(χ_t)` and `κ⁻¹ N̂_n(χ_{t_n}) ⪯ N̂_n(χ̂_{t_n}) ⪯ κ N̂_n(χ_{t_n})`. -/
def TuningComparable {N d K : ℕ} (left : Bool) (L : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ)
    (χ : ℝ → Matrix (Fin N) (Fin N) ℝ) (dt : ℝ)
    (Qhat : ℝ → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin d) (Fin d) ℝ)
    (Nhat : ℕ → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin K × Fin N) (Fin K × Fin N) ℝ) : Prop :=
  ∀ κ : ℝ, 1 < κ → ∃ ε > 0, ∀ ξ : Fin d → ℝ, ‖ξ‖ < ε →
    (∀ t : ℝ, 0 ≤ t →
      LoewnerLE (κ⁻¹ • Qhat t (χ t)) (Qhat t (perturbed left L (χ t) ξ)) ∧
      LoewnerLE (Qhat t (perturbed left L (χ t) ξ)) (κ • Qhat t (χ t))) ∧
    (∀ n : ℕ, 1 ≤ n →
      LoewnerLE (κ⁻¹ • Nhat n (χ ((n : ℝ) * dt))) (Nhat n (perturbed left L (χ ((n : ℝ) * dt)) ξ)) ∧
      LoewnerLE (Nhat n (perturbed left L (χ ((n : ℝ) * dt)) ξ)) (κ • Nhat n (χ ((n : ℝ) * dt))))

/-! ### The linear Kalman filter and the Deyst-Price conditions (Theorem 3) -/

/-- Theorem 3: `Phi s t = Phi_s^t` is the transition matrix of `dx/dt = A_t x`:
`Phi_s^s = I` and `d/dt Phi_s^t = A_t Phi_s^t`. -/
def IsTransitionMatrix {d : ℕ} (A : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (Phi : ℝ → ℝ → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ s, Phi s s = 1 ∧ ∀ t, HasMatDerivAt (fun r => Phi s r) (A t * Phi s t) t

/-- Theorem 3 (iv): the controllability Gramian `∫_{t_{n-M}}^{t_n} Phi_s^{t_n} Q_s (Phi_s^{t_n})ᵀ ds`,
entry by entry, with `t_n = n dt`. -/
def ctrlGramian {d : ℕ} (dt : ℝ) (Phi : ℝ → ℝ → Matrix (Fin d) (Fin d) ℝ)
    (Q : ℝ → Matrix (Fin d) (Fin d) ℝ) (M n : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∫ s in (((n - M : ℕ) : ℝ) * dt)..((n : ℝ) * dt),
    (Phi s ((n : ℝ) * dt) * Q s * (Phi s ((n : ℝ) * dt))ᵀ) i j

/-- Theorem 3 (v), in the form of Deyst and Price (1968): the observability Gramian
`∑_{i=n-M}^{n} (Phi_{t_n}^{t_i})ᵀ Hᵀ N_i⁻¹ H Phi_{t_n}^{t_i}`, with `t_i = i dt`. -/
def obsGramian {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (dt : ℝ)
    (Phi : ℝ → ℝ → Matrix (Fin d) (Fin d) ℝ) (H : Matrix ι (Fin d) ℝ) (Nm : ℕ → Matrix ι ι ℝ)
    (M n : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ i ∈ Finset.Icc (n - M) n,
    (Phi ((n : ℝ) * dt) ((i : ℝ) * dt))ᵀ * Hᵀ * (Nm i)⁻¹ * H * Phi ((n : ℝ) * dt) ((i : ℝ) * dt)

/-- Theorem 3 (i)-(v): the Deyst-Price conditions for the linear system with transition matrix
`Phi`, process-noise matrices `Q_s`, observation matrix `H` and measurement-noise matrices `N_n`
at the times `t_n = n dt` (with the observability sum in the form of Deyst and Price). -/
def DeystPriceConditions {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (dt : ℝ)
    (Phi : ℝ → ℝ → Matrix (Fin d) (Fin d) ℝ) (Q : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (H : Matrix ι (Fin d) ℝ) (Nm : ℕ → Matrix ι ι ℝ) (α₁ α₂ β₁ β₂ δ₁ δ₂ δ₃ : ℝ) (M : ℕ) :
    Prop :=
  (∀ n : ℕ, LoewnerLE (δ₁ • (1 : Matrix (Fin d) (Fin d) ℝ))
      ((Phi ((n : ℝ) * dt) (((n : ℝ) + 1) * dt))ᵀ * Phi ((n : ℝ) * dt) (((n : ℝ) + 1) * dt))) ∧
  (∃ q : ℕ, 0 < q ∧ ∃ Q' : Matrix (Fin q) (Fin q) ℝ, LoewnerLE (δ₂ • 1) Q' ∧
      ∀ s : ℝ, 0 < s → ∃ Gs : Matrix (Fin d) (Fin q) ℝ, Q s = Gs * Q' * Gsᵀ) ∧
  (∀ n : ℕ, 1 ≤ n → LoewnerLE (δ₃ • (1 : Matrix ι ι ℝ)) (Nm n)) ∧
  (∀ n : ℕ, M ≤ n →
      (∀ i j, IntervalIntegrable (fun s => (Phi s ((n : ℝ) * dt) * Q s * (Phi s ((n : ℝ) * dt))ᵀ) i j)
        volume (((n - M : ℕ) : ℝ) * dt) ((n : ℝ) * dt)) ∧
      LoewnerLE (α₁ • 1) (ctrlGramian dt Phi Q M n) ∧ LoewnerLE (ctrlGramian dt Phi Q M n) (α₂ • 1)) ∧
  (∀ n : ℕ, M + 1 ≤ n →
      LoewnerLE (β₁ • 1) (obsGramian dt Phi H Nm M n) ∧ LoewnerLE (obsGramian dt Phi H Nm M n) (β₂ • 1))

/-- Theorem 3, conclusion "`γ_min I ⪯ P_t ⪯ γ_max I` for all `t`" (p. 13): the transition matrix
is bounded within each sampling interval, `(Phi_s^t)ᵀ Phi_s^t ⪯ c I` for `s, t ∈ [t_n, t_{n+1}]`.
The paper does not state this condition; the bound on `P_t` between observations needs it. -/
def BoundedTransition {d : ℕ} (dt : ℝ) (Phi : ℝ → ℝ → Matrix (Fin d) (Fin d) ℝ) (c : ℝ) :
    Prop :=
  ∀ n : ℕ, ∀ s ∈ Set.Icc ((n : ℝ) * dt) (((n : ℝ) + 1) * dt),
    ∀ t ∈ Set.Icc ((n : ℝ) * dt) (((n : ℝ) + 1) * dt),
      LoewnerLE ((Phi s t)ᵀ * Phi s t) (c • (1 : Matrix (Fin d) (Fin d) ℝ))

/-- Theorem 3: a run of the linear Kalman filter for `dx/dt = A_t x`, `y_{t_n} = H x_{t_n}`,
tuned with `Q` and `N`, started at time `t₀` from `(x̂₀, P₀)`: `x̂` follows `dx̂/dt = A_t x̂`
between the observation times `t_n = n dt`, where `x̂⁺ = x̂ + L_n (y_{t_n} - H x̂)`, and `P` is
a run of the Riccati equation (37). -/
def IsKalmanRun {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → Matrix (Fin d) (Fin d) ℝ) (H : Matrix ι (Fin d) ℝ)
    (Q : ℝ → Matrix (Fin d) (Fin d) ℝ) (Nm : ℕ → Matrix ι ι ℝ) (dt : ℝ)
    (x : ℝ → Fin d → ℝ) (t0 : ℝ) (xhat0 : Fin d → ℝ) (P0 : Matrix (Fin d) (Fin d) ℝ)
    (xs : ℕ → ℝ → Fin d → ℝ) (Ps : ℕ → ℝ → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  IsRiccatiRun A H (fun _ t => Q t) (fun n => Nm (n + 1)) dt t0 P0 Ps ∧
  ∀ n : ℕ, t0 < ((n : ℝ) + 1) * dt →
    ((n : ℝ) * dt ≤ t0 → xs n t0 = xhat0) ∧
    (∀ t ∈ segIcc t0 dt n, HasDerivWithinAt (xs n) (A t *ᵥ xs n t) (segIcc t0 dt n) t) ∧
    xs (n + 1) (((n : ℝ) + 1) * dt) =
      xs n (((n : ℝ) + 1) * dt) +
        kalmanGain (Ps n (((n : ℝ) + 1) * dt)) H (Nm (n + 1)) *ᵥ
          (H *ᵥ x (((n : ℝ) + 1) * dt) - H *ᵥ xs n (((n : ℝ) + 1) * dt))

end InvariantEKF


