-- Prove2me | Definitions.Def_GrothendieckPD_Digits_OneVariable
-- name    : GrothendieckPD_Digits_OneVariable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:48.791985+00:00
-- url     : https://prove2.me/theorems/25a13469-9f1d-4443-9a6c-c2b9ea8d6783
-- title:
--   §B.1: the one-variable criterion objects $B_N$, $\Gamma_m$, $\alpha$, $\beta$, feasible moments, $F(M)$, $\Phi(x)$
-- statement:
--   The objects of §B.1 (p. 19), for one interval's parameters: rational weights $w^{(N)}\in\mathbb Q^{(N-1)/2}$ ($N=7,9$), symmetric rational $11\times11$ matrices $H_p,K_p$ ($p=0,1$), vectors $\ell_h,\ell_k\in\mathbb Q^{11}$ and rationals $t,c_h,c_k,C$.
--
--   1. $B_N=\max_{\sigma\in\{-1,1\}^N}\frac1N\sum_{r=0}^{N-1}\sum_{j=1}^{(N-1)/2}w^{(N)}_j\sigma_r\sigma_{r+j}$ with $\sigma_{r+N}=-\sigma_r$ (B.3); $\Gamma_m=\sum_{N\in\{7,9\}}\sum_{j=1}^{(N-1)/2}w^{(N)}_j\cos^m(\pi j/N)$ and $B=B_7+B_9$ (B.4).
--   2. $\alpha_m=q_m-\Gamma_m$ ($m=3,5,\dots,21$) and $\beta_m=-q_m-\Gamma_m$ ($m=1,3,\dots,21$), all other entries zero (B.5), with $q$ from Eq. (4.1).
--   3. $M\in\mathbb R^{44}$ is **feasible** when $M=(\mathbb E[\psi u],\mathbb E[\psi v])$ for measurable $u,v:\mathbb R\to[-1,1]$, $\psi=(\psi_0,\dots,\psi_{21})$, the expectation under $\gamma_1$; $(h_p(M))_j=(M_{2j+p}+M_{22+2j+p})/2$ and $(k_p(M))_j=(M_{2j+p}-M_{22+2j+p})/2$ for $0\le j\le10$ (B.6).
--   4. $\varepsilon=10^{-7}$, $D_{p,r}(a)=\mathrm{diag}(a_{2j+p+r})_{j=0}^{10}$, and condition (B.7): $\Gamma_m\ge0$ for odd $m>21$, $1-\Gamma_1>0$; condition (B.8): for $(A,a,\lambda,c)\in\{(H,\alpha,\ell_h,c_h),(K,\beta,\ell_k,c_k)\}$, $p=0,1$, $1\le r\le21$: $A_p\succeq0$, $A_p+\varepsilon I_{11}\succeq D_{p,r}(a)$, and $\begin{pmatrix}A_1+\varepsilon I_{11}-D_{1,0}(a)&\lambda\\ \lambda^T&c+\varepsilon\end{pmatrix}\succeq0$.
--   5. $$F(M)=\sum_{p=0}^1\bigl(h_p^TH_ph_p+k_p^TK_pk_p\bigr)+t\,(h_1(M))_0-2\ell_h^Th_1(M)-2\ell_k^Tk_1(M)\quad(B.9),$$ $$\Phi(x)=B+c_h+c_k+3\varepsilon+(1-\Gamma_1)\tfrac2\pi x^2-t\sqrt{2/\pi}\,x\quad(B.10),$$ and $v_*=1000/1773-10^{-9}$.
--
--   These are the ingredients of Proposition B.2, which reduces the bound on $v_n(q)$ to a 44-dimensional problem.
--
--   **Formalization Note** $w^{(N)}$ is indexed from $0$ in Lean (entry $j$ is $w_{j+1}$); $\sigma$ ranges over Boolean vectors; positive semidefiniteness is Mathlib's `Matrix.PosSemidef` of the real matrices.
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Appendix B.1, p. 19: Eq. (B.3)–(B.10); Eq. (B.12) p. 20 (v_*); Eq. (4.1) p. 11

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames
open MeasureTheory ProbabilityTheory

namespace GrothendieckPD.Digits

/-- The dimension-independent parameters attached to one interval in §B.1 (p. 19): rational weights
`w^{(7)} ∈ ℚ^3`, `w^{(9)} ∈ ℚ^4` (entry `j` is `w_{j+1}`), symmetric rational `11 × 11` matrices
`H_p, K_p` (`p = 0, 1`), vectors `ℓ_h, ℓ_k ∈ ℚ^{11}` and rationals `t, c_h, c_k, C`. -/
structure CertParams where
  w7 : Fin 3 → ℚ
  w9 : Fin 4 → ℚ
  H : Fin 2 → Matrix (Fin 11) (Fin 11) ℚ
  K : Fin 2 → Matrix (Fin 11) (Fin 11) ℚ
  lh : Fin 11 → ℚ
  lk : Fin 11 → ℚ
  t : ℚ
  ch : ℚ
  ck : ℚ
  C : ℚ

/-- `+1` or `-1`. -/
def signVal (b : Bool) : ℝ := if b then 1 else -1

/-- The antiperiodic extension `σ_{r+N} = -σ_r` of `σ ∈ {±1}^N` (Eq. B.3), at an index `i < 2N`. -/
def sigmaExt (N : ℕ) [NeZero N] (σ : Fin N → Bool) (i : ℕ) : ℝ :=
  (if i < N then 1 else -1) * signVal (σ (Fin.ofNat N i))

/-- `B_N = max_{σ ∈ {-1,1}^N} (1/N) ∑_{r=0}^{N-1} ∑_{j=1}^{(N-1)/2} w_j^{(N)} σ_r σ_{r+j}` with
`σ_{r+N} = -σ_r` (Eq. B.3, p. 19); `w j` is `w_{j+1}^{(N)}`. -/
noncomputable def BN (N : ℕ) [NeZero N] (w : Fin ((N - 1) / 2) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun σ : Fin N → Bool =>
    (1 / (N : ℝ)) * ∑ r : Fin N, ∑ j : Fin ((N - 1) / 2),
      w j * signVal (σ r) * sigmaExt N σ (r.val + (j.val + 1))

/-- `B = B_7 + B_9` (Eq. B.4). -/
noncomputable def Bsum (P : CertParams) : ℝ :=
  BN 7 (fun j => (P.w7 j : ℝ)) + BN 9 (fun j => (P.w9 j : ℝ))

/-- `Γ_m = ∑_{N ∈ {7,9}} ∑_{j=1}^{(N-1)/2} w_j^{(N)} cos^m(πj/N)` (Eq. B.4, p. 19). -/
noncomputable def Gamma (P : CertParams) (m : ℕ) : ℝ :=
  (∑ j : Fin 3, (P.w7 j : ℝ) * Real.cos (Real.pi * (j.val + 1 : ℝ) / 7) ^ m) +
    ∑ j : Fin 4, (P.w9 j : ℝ) * Real.cos (Real.pi * (j.val + 1 : ℝ) / 9) ^ m

/-- `α_m = q_m - Γ_m` for `m = 3, 5, …, 21`, all other entries zero (Eq. B.5); `q` is Eq. (4.1). -/
noncomputable def alphaSeq (P : CertParams) (m : ℕ) : ℝ :=
  if Odd m ∧ 3 ≤ m ∧ m ≤ 21 then qCert m - Gamma P m else 0

/-- `β_m = -q_m - Γ_m` for `m = 1, 3, …, 21`, all other entries zero (Eq. B.5). -/
noncomputable def betaSeq (P : CertParams) (m : ℕ) : ℝ :=
  if Odd m ∧ 1 ≤ m ∧ m ≤ 21 then -qCert m - Gamma P m else 0

/-- `M ∈ ℝ^{44}` is feasible when `M = (E[ψ u], E[ψ v])` with `ψ = (ψ_0, …, ψ_21)` and measurable
`u, v : ℝ → [-1, 1]`, the expectation under `γ_1` (p. 19): coordinates `0, …, 21` are `E[ψ_j u]`
and coordinates `22, …, 43` are `E[ψ_j v]`. -/
def Feasible (M : Fin 44 → ℝ) : Prop :=
  ∃ u v : ℝ → ℝ, Measurable u ∧ Measurable v ∧
    (∀ s, u s ∈ Set.Icc (-1 : ℝ) 1) ∧ (∀ s, v s ∈ Set.Icc (-1 : ℝ) 1) ∧
    ∀ j : Fin 22,
      M ⟨j.val, by omega⟩ = ∫ s, psi j.val s * u s ∂gaussianReal 0 1 ∧
      M ⟨22 + j.val, by omega⟩ = ∫ s, psi j.val s * v s ∂gaussianReal 0 1

/-- `(h_p(M))_j = (M_{2j+p} + M_{22+2j+p}) / 2`, `0 ≤ j ≤ 10` (Eq. B.6). -/
noncomputable def hVec (M : Fin 44 → ℝ) (p : Fin 2) : Fin 11 → ℝ :=
  fun j => (M ⟨2 * j.val + p.val, by omega⟩ + M ⟨22 + 2 * j.val + p.val, by omega⟩) / 2

/-- `(k_p(M))_j = (M_{2j+p} - M_{22+2j+p}) / 2`, `0 ≤ j ≤ 10` (Eq. B.6). -/
noncomputable def kVec (M : Fin 44 → ℝ) (p : Fin 2) : Fin 11 → ℝ :=
  fun j => (M ⟨2 * j.val + p.val, by omega⟩ - M ⟨22 + 2 * j.val + p.val, by omega⟩) / 2

/-- `ε = 10^{-7}` (p. 19). -/
noncomputable def epsB : ℝ := 1 / 10 ^ 7

/-- `D_{p,r}(a) = diag(a_{2j+p+r})_{j=0}^{10}` (p. 19). -/
def Dmat (a : ℕ → ℝ) (p r : ℕ) : Matrix (Fin 11) (Fin 11) ℝ :=
  Matrix.diagonal fun j => a (2 * j.val + p + r)

/-- `H_p` as a real matrix. -/
def Hr (P : CertParams) (p : Fin 2) : Matrix (Fin 11) (Fin 11) ℝ := (P.H p).map (↑)

/-- `K_p` as a real matrix. -/
def Kr (P : CertParams) (p : Fin 2) : Matrix (Fin 11) (Fin 11) ℝ := (P.K p).map (↑)

/-- `F(M) = ∑_{p=0}^{1} (h_p^T H_p h_p + k_p^T K_p k_p) + t (h_1(M))_0 - 2 ℓ_h^T h_1(M) - 2 ℓ_k^T k_1(M)`
(Eq. B.9, p. 19); `t` is the scalar parameter. -/
noncomputable def Fval (P : CertParams) (M : Fin 44 → ℝ) : ℝ :=
  (∑ p : Fin 2, (hVec M p ⬝ᵥ (Hr P p).mulVec (hVec M p) +
      kVec M p ⬝ᵥ (Kr P p).mulVec (kVec M p))) +
    (P.t : ℝ) * hVec M 1 0 - 2 * ((fun j => (P.lh j : ℝ)) ⬝ᵥ hVec M 1) -
    2 * ((fun j => (P.lk j : ℝ)) ⬝ᵥ kVec M 1)

/-- `Φ(x) = B + c_h + c_k + 3ε + (1 - Γ_1)(2/π) x² - t √(2/π) x` (Eq. B.10, p. 19). -/
noncomputable def Phi (P : CertParams) (x : ℝ) : ℝ :=
  Bsum P + P.ch + P.ck + 3 * epsB + (1 - Gamma P 1) * (2 / Real.pi) * x ^ 2 -
    P.t * Real.sqrt (2 / Real.pi) * x

/-- Condition (B.7): `Γ_m ≥ 0` for odd `m > 21`, and `1 - Γ_1 > 0`. -/
def CondB7 (P : CertParams) : Prop :=
  (∀ m : ℕ, Odd m → 21 < m → 0 ≤ Gamma P m) ∧ 0 < 1 - Gamma P 1

/-- One half of condition (B.8) for a tuple `(A, a, λ, c)`: for `p = 0, 1` and `1 ≤ r ≤ 21`,
`A_p ⪰ 0`, `A_p + ε I_{11} ⪰ D_{p,r}(a)`, and
`[[A_1 + ε I_{11} - D_{1,0}(a), λ], [λ^T, c + ε]] ⪰ 0`. -/
def CondB8Part (A : Fin 2 → Matrix (Fin 11) (Fin 11) ℝ) (a : ℕ → ℝ) (lam : Fin 11 → ℝ)
    (c : ℝ) : Prop :=
  (∀ p : Fin 2, (A p).PosSemidef) ∧
  (∀ p : Fin 2, ∀ r : ℕ, 1 ≤ r → r ≤ 21 → (A p + epsB • (1 : Matrix (Fin 11) (Fin 11) ℝ) -
      Dmat a p.val r).PosSemidef) ∧
  (Matrix.fromBlocks (A 1 + epsB • (1 : Matrix (Fin 11) (Fin 11) ℝ) - Dmat a 1 0)
      (fun i (_ : Unit) => lam i) (fun (_ : Unit) j => lam j)
      (fun (_ : Unit) (_ : Unit) => c + epsB)).PosSemidef

/-- Condition (B.8) for both tuples `(H, α, ℓ_h, c_h)` and `(K, β, ℓ_k, c_k)` (p. 19). -/
def CondB8 (P : CertParams) : Prop :=
  CondB8Part (Hr P) (alphaSeq P) (fun j => (P.lh j : ℝ)) P.ch ∧
    CondB8Part (Kr P) (betaSeq P) (fun j => (P.lk j : ℝ)) P.ck

/-- The matrices `H_p, K_p` are symmetric (p. 19). -/
def ParamsSymm (P : CertParams) : Prop :=
  ∀ p : Fin 2, (P.H p).IsSymm ∧ (P.K p).IsSymm

/-- `v_* = 1000/1773 - 10^{-9}` (Eq. B.12, p. 20). -/
noncomputable def vStar : ℝ := 1000 / 1773 - 1 / 10 ^ 9

end GrothendieckPD.Digits


