-- Prove2me | Definitions.Def_Arxiv1705_08274_Basic
-- name    : Arxiv1705_08274_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T02:02:23.603733+00:00
-- url     : https://prove2.me/theorems/ad8f3e80-a8d8-4138-abc0-2731cc912148
-- title:
--   Discrete ordinates Jacobian, node response matrices, adding and doubling, and node approximations for polarized 1D radiative transfer
-- statement:
--   Objects of Sections I-II and Appendix B of Ganapol (2017), arXiv:1705.08274.
--
--   1. **Discrete ordinates model (eqs. (1a)-(3g)).** A homogeneous node is described by $N$ quadrature directions $0<\mu_m\le1$, weights $w_m\ge0$, an albedo $0\le\omega\le1$ and a $2\times2$ scattering matrix factor $Q(\mu)$ with $Q(-\mu)=Q(\mu)$. A half-range Stokes vector $I^\pm$ has $2N$ components, indexed by a direction $m$ and a Stokes component ($I$ or $Q$). The $2N\times2N$ matrices are $M=\mathrm{diag}\{\mu_mI_2\}$, $W=\mathrm{diag}\{w_mI_2\}$, and $P$, whose $(m,m')$ block of size $2\times2$ is $\frac{\omega}{2}Q(\mu_m)Q^T(\mu_{m'})$.
--   2. **Jacobian (eq. (5c)).** For $Y=[I^+;I^-]$ the discrete ordinates equations are $\frac{d}{d\tau}Y+AY=0$ with
--   $$A=\begin{bmatrix}\alpha&-\beta\\\beta&-\alpha\end{bmatrix},\qquad \alpha=M^{-1}(I-PW),\quad \beta=M^{-1}PW.$$
--   3. **Node propagator and response (eqs. (6a)-(11b), (43)).** Over a node of width $h$, $Y_{j+1}=e^{-Ah}Y_j$. For a propagator $E=[[E_{11},E_{12}],[E_{21},E_{22}]]$ the response matrix is $R=[[E_{12},-I],[E_{22},0]]^{-1}[[0,-E_{11}],[I,-E_{21}]]$. It maps the incoming intensities $[I^-_{j+1};I^+_j]$ to the outgoing intensities $[I^-_j;I^+_{j+1}]$. For a scheme $Y_{j+1}=P^{*-1}PY_j$ the response matrix is $R=[[-P_{12},P^*_{11}],[-P_{22},P^*_{21}]]^{-1}[[-P^*_{12},P_{11}],[-P^*_{22},P_{21}]]$. A response matrix is *symmetric* if its diagonal blocks are equal ($T_n$) and its off-diagonal blocks are equal ($R_f$).
--   4. **Adding (eqs. (28b)-(28d)).** For a composite with response $[[Q_1,Q_2],[Q_2,Q_1]]$ and an added node with response $[[T_n,R_f],[R_f,T_n]]$, the paper sets $w_m=[[I,-Q_2],[-R_f,I]]$, $w_p=[[0,Q_1],[T_n,0]]$, $U=w_m^{-1}w_p$ and $Q=w_pU+[[0,Q_2],[R_f,0]]$. Applied to two full response matrices, adding uses the $(1,1)$ and $(1,2)$ blocks of each. The adding sequence of $l$ identical nodes starts from the empty slab ($Q_0=I$, so $Q_1=R$). The doubling sequence combines two copies of the previous response: $Q_0=R$, $Q_{k+1}=Q_k\star Q_k$. An adding step is admissible when $w_m$ is invertible.
--   5. **Boundary reflection (eq. (32b)).** $\mathcal D$ is the $N\times N$ array all of whose $2\times2$ blocks equal the reflection matrix $D$.
--   6. **Node approximations (Section II.A).** The $(q,q)$ Padé polynomials are $N_q(h)=I+\sum_{j=1}^q(-1)^jc_{q,j}A^jh^j$ and $D_q(h)=I+\sum_{j=1}^qc_{q,j}A^jh^j$, with $c_{q,j}=\frac{(2q-j)!\,q!}{(2q)!\,j!\,(q-j)!}$. The RK5 matrix $P^*(h)=I+\sum_{i=1}^6b_ig_i(h)$, with $g_i(h)=\frac h2A\big[I+\sum_{n<i}a_{in}g_n(h)\big]$, is one Fehlberg fifth-order step for $\frac{d\xi}{d\tau}=\frac A2\xi$, with the coefficients of Table 1.
--
--   **Formalization Note** Vectors of length $2N$ are indexed by pairs (direction, Stokes component), and block matrices by the disjoint union of two copies of that index set, upper block $I^+$. The matrix exponential is Mathlib's `NormedSpace.exp`. The Padé coefficient uses $(q-j)!$; the paper prints $(q-j)$, which is $0$ for $j=q$. Matrix inverses that the paper takes for granted are written as hypotheses in the statements that use them.
-- source:
--   B. D. Ganapol, A 1D Radiative Transfer Benchmark with Polarization via Doubling and Adding, arXiv:1705.08274v1 (2017), Sections I.A-I.E (eqs. (1a)-(37b)), Section II.A (eqs. (40)-(54), Table 1), Appendix B (eq. (B1))

import Mathlib

/-!
B. D. Ganapol, *A 1D Radiative Transfer Benchmark with Polarization via Doubling and Adding*,
arXiv:1705.08274v1 (2017): the discrete ordinates Jacobian of Sections I.A-I.B (eqs. (1a)-(5c)),
the single node response matrix of Section I.C (eqs. (6a)-(11b)), the adding recurrence and
doubling of Sections I.D-I.E (eqs. (25a)-(37b)), and the node propagators of Section II.A
(diamond difference, Padé, RK5; eqs. (40)-(54), Table 1) and Appendix B (eq. (B1)).

Throughout, a vector of `2N` components (eqs. (3a,b)) is indexed by `Dir N = Fin N × Fin 2`
(direction `m`, Stokes component `I` or `Q`), and a matrix of order `4N` acting on the stacked
vector `Y = [I⁺; I⁻]` (eq. (5a)) is a block matrix indexed by `Dir N ⊕ Dir N`, upper block `I⁺`.
-/

open Matrix

noncomputable section

namespace Arxiv1705_08274

/-- Eqs. (3a,b): index set of an unrolled half-range Stokes vector, direction `m ∈ {1,…,N}` and
Stokes component `i ∈ {I, Q}` (a vector of length `2N`). -/
abbrev Dir (N : ℕ) : Type := Fin N × Fin 2

/-- Sections I.A-I.B, eqs. (1a)-(3g): the data of the discrete ordinates model of a homogeneous
node: positive quadrature directions `μ_m`, quadrature weights `w_m` (written `ω_m` in eq. (3e)),
single scatter albedo `ω`, and the `2 × 2` scattering matrix factor `Q(μ)` of eq. (1a). -/
structure DOModel (N : ℕ) where
  /-- Quadrature directions `μ_m > 0`, eq. (2a). -/
  mu : Fin N → ℝ
  /-- Quadrature weights, eq. (2b). -/
  wt : Fin N → ℝ
  /-- Single scatter albedo `ω`, eq. (1a). -/
  albedo : ℝ
  /-- Scattering matrix factor `Q(μ)`, eq. (1a). -/
  scat : ℝ → Matrix (Fin 2) (Fin 2) ℝ

/-- Sections I.A-I.B and II.B: the standing assumptions on the model: directions
`0 < μ_m ≤ 1`, weights `w_m ≥ 0` (Section II.B adds the beam direction with weight `ε` and
Section II.D adds edit directions with weight `0`), albedo `0 ≤ ω ≤ 1`, and the scattering
symmetry `Q(-μ) = Q(μ)` of eq. (1b). -/
def DOModel.Admissible {N : ℕ} (S : DOModel N) : Prop :=
  (∀ m, 0 < S.mu m ∧ S.mu m ≤ 1) ∧ (∀ m, 0 ≤ S.wt m) ∧ 0 ≤ S.albedo ∧ S.albedo ≤ 1 ∧
    ∀ x, S.scat (-x) = S.scat x

/-- Eq. (3f): `M = diag{μ_m I₂}`. -/
def DOModel.muMat {N : ℕ} (S : DOModel N) : Matrix (Dir N) (Dir N) ℝ :=
  diagonal fun p => S.mu p.1

/-- Eq. (3e): `W = diag{w_m I₂}`. -/
def DOModel.wMat {N : ℕ} (S : DOModel N) : Matrix (Dir N) (Dir N) ℝ :=
  diagonal fun p => S.wt p.1

/-- Eq. (3g): the matrix of `2 × 2` blocks `P = (ω/2) {Q(μ_m) Qᵀ(μ_m')}`. -/
def DOModel.scatMat {N : ℕ} (S : DOModel N) : Matrix (Dir N) (Dir N) ℝ :=
  fun p q => S.albedo / 2 * (S.scat (S.mu p.1) * (S.scat (S.mu q.1))ᵀ) p.2 q.2

/-- Eqs. (5c), (18a), (A1): the block `α = η₁₁⁽¹⁾ = M⁻¹(I - PW)`. -/
def DOModel.alpha {N : ℕ} (S : DOModel N) : Matrix (Dir N) (Dir N) ℝ :=
  S.muMat⁻¹ * (1 - S.scatMat * S.wMat)

/-- Eqs. (5c), (18a), (A1): the block `β = η₁₂⁽¹⁾ = M⁻¹PW`. -/
def DOModel.beta {N : ℕ} (S : DOModel N) : Matrix (Dir N) (Dir N) ℝ :=
  S.muMat⁻¹ * (S.scatMat * S.wMat)

/-- Eq. (5c): the constant Jacobian `A = [[M⁻¹(I - PW), -M⁻¹PW], [M⁻¹PW, -M⁻¹(I - PW)]]` of
`dY/dτ + AY = 0` (eq. (5b)) for the stacked vector `Y = [I⁺; I⁻]`. -/
def DOModel.jacobian {N : ℕ} (S : DOModel N) : Matrix (Dir N ⊕ Dir N) (Dir N ⊕ Dir N) ℝ :=
  fromBlocks S.alpha (-S.beta) S.beta (-S.alpha)

/-- Eq. (32b): the `N × N` array `𝒟` all of whose `2 × 2` blocks equal the reflection matrix
`D` of eq. (1e). -/
def reflArray {N : ℕ} (D : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Dir N) (Dir N) ℝ :=
  fun p q => D p.2 q.2

section Blocks

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Eqs. (6a), (7), (17): the exact node propagator `e^{-Ah}` over a homogeneous node of width
`h` (the matrix exponential). -/
def nodeExp (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (h : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  NormedSpace.exp (-(h • A))

/-- Eq. (11b): the response matrix of a node with propagator `E = [[E₁₁, E₁₂], [E₂₁, E₂₂]]`
(`Y_{j+1} = E Y_j`): `R = [[E₁₂, -I], [E₂₂, 0]]⁻¹ [[0, -E₁₁], [I, -E₂₁]]`, mapping
`[I⁻_{j+1}; I⁺_j]` to `[I⁻_j; I⁺_{j+1}]` (eq. (11a)). -/
def respOfProp (E : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  (fromBlocks E.toBlocks₁₂ (-1) E.toBlocks₂₂ 0)⁻¹ *
    fromBlocks 0 (-E.toBlocks₁₁) 1 (-E.toBlocks₂₁)

/-- Eqs. (43), (B1): the response matrix of a node propagated by `Y_{j+1} = P*⁻¹ P Y_j`:
`R = [[-P₁₂, P*₁₁], [-P₂₂, P*₂₁]]⁻¹ [[-P*₁₂, P₁₁], [-P*₂₂, P₂₁]]`. -/
def respOfPair (Ps P : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  (fromBlocks (-P.toBlocks₁₂) Ps.toBlocks₁₁ (-P.toBlocks₂₂) Ps.toBlocks₂₁)⁻¹ *
    fromBlocks (-Ps.toBlocks₁₂) P.toBlocks₁₁ (-Ps.toBlocks₂₂) P.toBlocks₂₁

/-- Eqs. (13)-(14): a response matrix is symmetric (in the paper's sense) when its diagonal
blocks agree (`T_n`) and its off-diagonal blocks agree (`R_f`). -/
def IsSymmetricResponse (R : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Prop :=
  R.toBlocks₁₁ = R.toBlocks₂₂ ∧ R.toBlocks₁₂ = R.toBlocks₂₁

/-- Eq. (28c): `w_{m,l} = [[I, -Q_{l-1,2}], [-R_f, I]]`. -/
def wMinus (Q2 Rf : Matrix n n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  fromBlocks 1 (-Q2) (-Rf) 1

/-- Eq. (28c): `w_{p,l} = [[0, Q_{l-1,1}], [T_n, 0]]`. -/
def wPlus (Q1 Tn : Matrix n n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  fromBlocks 0 Q1 Tn 0

/-- Eq. (28b): `U_l = w_{m,l}⁻¹ w_{p,l}`, for a composite with symmetric response
`[[Q₁, Q₂], [Q₂, Q₁]]` (eq. (25b)) and an added node with response `[[T_n, R_f], [R_f, T_n]]`. -/
def addU (Q1 Q2 Tn Rf : Matrix n n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  (wMinus Q2 Rf)⁻¹ * wPlus Q1 Tn

/-- Eq. (28d): the combined response `Q_l = [[0, Q_{l-1,1}], [T_n, 0]] U_l + [[0, Q_{l-1,2}],
[R_f, 0]]`. -/
def addQ (Q1 Q2 Tn Rf : Matrix n n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  wPlus Q1 Tn * addU Q1 Q2 Tn Rf + fromBlocks 0 Q2 Rf 0

/-- Section I.D, eqs. (25b), (28b) and the paragraph after (29b): the matrix `U_l` for adding
a composite (or node) with response `R` to a composite with response `Q`, both taken in the
symmetric form, i.e. `Q_{l-1,1} = Q₁₁`, `Q_{l-1,2} = Q₁₂`, `T_n = R₁₁`, `R_f = R₁₂`. -/
def addRespU (Q R : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  addU Q.toBlocks₁₁ Q.toBlocks₁₂ R.toBlocks₁₁ R.toBlocks₁₂

/-- Section I.D, eqs. (25b), (28d) and the paragraph after (29b): the combined response of a
composite with response `Q` followed by a composite (or node) with response `R`, both taken in
the symmetric form. -/
def addResp (Q R : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  addQ Q.toBlocks₁₁ Q.toBlocks₁₂ R.toBlocks₁₁ R.toBlocks₁₂

/-- Eq. (28b) (implicit "suitable invertibility"): the matrix `w_{m,l}` of the adding step of
`R` to `Q` is invertible. -/
def CanAdd (Q R : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Prop :=
  IsUnit (wMinus Q.toBlocks₁₂ R.toBlocks₁₂).det

/-- Section I.E.2, eq. (35): the cumulative response `Q_l` of `l` identical nodes of response
`R`, added one at a time with eqs. (28). `Q_0 = I` is the response of an empty slab, so
`Q_1 = R`. -/
def addSeq (R : Matrix (n ⊕ n) (n ⊕ n) ℝ) : ℕ → Matrix (n ⊕ n) (n ⊕ n) ℝ
  | 0 => 1
  | l + 1 => addResp (addSeq R l) R

/-- Section I.E.1: the response after `k` doublings of a node of response `R`
(`Q_0 = R`, `Q_{k+1}` combines two copies of `Q_k` with eqs. (28)), i.e. of `2^k` nodes. -/
def dblSeq (R : Matrix (n ⊕ n) (n ⊕ n) ℝ) : ℕ → Matrix (n ⊕ n) (n ⊕ n) ℝ
  | 0 => R
  | k + 1 => addResp (dblSeq R k) (dblSeq R k)

/-- Eqs. (46b,c): the coefficient `(2q - j)! q! / ((2q)! j! (q - j)!)` of the `(q,q)` Padé
approximant of the exponential (Moler and Van Loan, Ref. 13; the paper prints `(q - j)` for
`(q - j)!`). -/
def padeCoeff (q j : ℕ) : ℝ :=
  ((2 * q - j).factorial * q.factorial : ℝ) /
    ((2 * q).factorial * j.factorial * (q - j).factorial)

/-- Eq. (46b): `N_q(h) = I + ∑_{j=1}^q (-1)^j c_{q,j} A^j h^j`. -/
def padeNum (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (h : ℝ) (q : ℕ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  1 + ∑ j ∈ Finset.Icc 1 q, ((-1) ^ j * padeCoeff q j * h ^ j) • A ^ j

/-- Eq. (46c): `D_q(h) = I + ∑_{j=1}^q c_{q,j} A^j h^j`. -/
def padeDen (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (h : ℝ) (q : ℕ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  1 + ∑ j ∈ Finset.Icc 1 q, (padeCoeff q j * h ^ j) • A ^ j

/-- Eqs. (51c,d), (52a,b), Table 1: one step of Fehlberg's fifth-order Runge-Kutta method of
size `h` for `dξ/dτ = (A/2) ξ`, written as the matrix `P*(h) = I + ∑ b_i g_i(h)` with
`g_i(h) = (h/2) A [I + ∑_{n<i} a_{in} g_n(h)]`. -/
def rk5Pstar (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (h : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  let K := (h / 2) • A
  let g1 := K
  let g2 := K * (1 + (1 / 4 : ℝ) • g1)
  let g3 := K * (1 + (3 / 32 : ℝ) • g1 + (9 / 32 : ℝ) • g2)
  let g4 := K * (1 + (1932 / 2197 : ℝ) • g1 + (-7200 / 2197 : ℝ) • g2 + (7296 / 2197 : ℝ) • g3)
  let g5 := K * (1 + (439 / 216 : ℝ) • g1 + (-8 : ℝ) • g2 + (3680 / 513 : ℝ) • g3 +
    (-845 / 4104 : ℝ) • g4)
  let g6 := K * (1 + (-8 / 27 : ℝ) • g1 + (2 : ℝ) • g2 + (-3544 / 2565 : ℝ) • g3 +
    (1859 / 4104 : ℝ) • g4 + (-11 / 40 : ℝ) • g5)
  1 + (16 / 135 : ℝ) • g1 + (0 : ℝ) • g2 + (6656 / 12825 : ℝ) • g3 + (28561 / 56430 : ℝ) • g4 +
    (-9 / 50 : ℝ) • g5 + (2 / 55 : ℝ) • g6

end Blocks

end Arxiv1705_08274


