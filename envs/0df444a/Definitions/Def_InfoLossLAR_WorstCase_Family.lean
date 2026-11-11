-- Prove2me | Definitions.Def_InfoLossLAR_WorstCase_Family
-- name    : InfoLossLAR_WorstCase_Family
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:05:46.667497+00:00
-- url     : https://prove2.me/theorems/407578a2-ceee-4488-bb37-37485257b40d
-- title:
--   Public parameter families (§3.1), fixed-order Gaussian T-AFTs (Definition 5.3), and the fixed family of §9.9
-- statement:
--   A **public parameter family** (§3.1, augmented as in Definition 5.3) gives for each $\lambda$ an odd prime $q$, dimensions $N\ge1$ and $d$, a modular rank $r<d$ (so $\ell=d-r\ge1$), a rounding matrix $T$ with chosen Smith matrices $U,V$, and a rational width $\sigma>0$; $\mathrm{pp}(\lambda)$ is the binary code of $(q,N,d,r,T,U,V,\sigma)$. It is **efficiently computable** if one deterministic polynomial-time map computes $\mathrm{pp}(\lambda)$ from $1^\lambda$ and $N,d$ are polynomially bounded. $\mathrm{Adv}^{\mathrm{dLAR}}$, $\mathrm{Adv}^{\mathrm{UZF\text{-}LWE}}$ (error $U(\mathcal F_{T,0})$) and $\mathrm{Adv}^{\mathrm{Gauss\text{-}LWE}}$ (error $\chi_G$) are the experiments of the item `Laws` for this family.
--
--   The family **admits fixed-order Gaussian T-AFTs** (Definition 5.3) if for every integer $c\ge1$ there is a uniform classical PPT sampler $\mathrm{Sample}_c(1^\lambda,\mathrm{pp})\to(Q,\beta)$ with $Q\bmod q\in\mathrm{GL}_d(\mathbb F_q)$ on every output and a threshold $\lambda_0(c)$ with
--   $$\Delta\big(\mathcal L(\mathrm{Eval}(Q,\beta,e)),\,U(\mathcal F_{T,0})\big)\le\lambda^{-c}\qquad(\lambda\ge\lambda_0(c)),\quad e\leftarrow\chi_G .$$
--
--   The **fixed family** of §9.9: $L=\lambda+2$, $N=\lambda$, $\sigma=L$, $q$ the least prime $\ge2^{16}t^8$ with $t=L^8$, $d=n_B+2g$ with $n_B=qt^{12}$, $g=t^{16}$; $T$ and $P=\mathbf 1^\top$ of Definition 6.3 ($r=d-1$, $\ell=1$); $\mathrm{pp}(\lambda)$ is the code of $(q,N,d,\sigma)$; its label is $f_T$ of Definition 6.3 as a vector of $\mathbb F_q^1$.
--
--   **Formalization Note.** For the fixed family $T$ and $P$ are determined by $(q,d)$, so pp lists only $(q,N,d,\sigma)$. The other §9.9 symbols ($K_B,K_L,K_Q,K_{BS},a_{\mathrm{anc}},B_L,h,\rho$) are internal to the sampler and do not enter any statement.
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), pp. 19–20 §3.1, p. 20 Definitions 3.6–3.7, pp. 23–24 Definitions 5.1 and 5.3, p. 27 Definition 6.3, p. 58 §9.9

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
import Definitions.Def_InfoLossLAR_WorstCase_FixedT
import Definitions.Def_InfoLossLAR_WorstCase_Laws

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

/-!
# Public parameter families, fixed-order Gaussian T-AFTs, and the fixed family of §9.9

Chen Qian, *Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices*,
arXiv:2611.05136 (held version, sha256 2ebdfbf3…), §3.1, pp. 19–20 (public parameter family),
Definitions 3.6–3.7, p. 20, p. 21 (`Adv^{LWE}`), Definitions 5.1 and 5.3, pp. 23–24 (T-AFT,
fixed-order Gaussian T-AFTs), §9.9, p. 58 (the fixed family), Definition 6.3, p. 27.
-/

/-- A public parameter family as in §3.1 (pp. 19–20), augmented by a positive Gaussian width as
in Definition 5.3 (p. 24): for each security parameter `λ`, an odd prime `q`, dimensions
`N ≥ 1`, `d`, a modular rank `r < d` (so `ℓ = d − r ≥ 1`), a rounding matrix `T` with its chosen
Smith matrices `U, V` (hence `P`, `J`, `f_T`), and a rational width `σ > 0`. -/
structure RoundingFamily where
  /-- The modulus `q(λ)`. -/
  q : ℕ → ℕ
  /-- The secret dimension `N(λ)`. -/
  N : ℕ → ℕ
  /-- The dimension `d(λ)`. -/
  d : ℕ → ℕ
  /-- The modular rank `r(λ)`; `ℓ(λ) = d(λ) − r(λ)`. -/
  r : ℕ → ℕ
  /-- The rounding matrix `T(λ)`. -/
  T : (lam : ℕ) → Matrix (Fin (d lam)) (Fin (d lam)) ℤ
  /-- The chosen Smith matrices of `T(λ)`. -/
  smith : (lam : ℕ) → SmithData (q lam) (r lam) (d lam) (T lam)
  /-- The Gaussian width `σ(λ)`. -/
  σ : ℕ → ℚ
  q_prime : ∀ lam, (q lam).Prime
  q_odd : ∀ lam, q lam ≠ 2
  N_pos : ∀ lam, 1 ≤ N lam
  ell_pos : ∀ lam, r lam < d lam
  σ_pos : ∀ lam, 0 < σ lam

instance (F : RoundingFamily) (lam : ℕ) : NeZero (F.q lam) := ⟨(F.q_prime lam).ne_zero⟩

/-- The output dimension `ℓ(λ) = d(λ) − r(λ)`. -/
def RoundingFamily.ell (F : RoundingFamily) (lam : ℕ) : ℕ := F.d lam - F.r lam

/-- The binary code of `pp(λ) = (q, N, d, r, T, U, V, σ)`. -/
def RoundingFamily.pp (F : RoundingFamily) (lam : ℕ) : Str :=
  encB (F.q lam) ++ encB (F.N lam) ++ encB (F.d lam) ++ encB (F.r lam) ++
    encMat encI (F.T lam) ++ encMat encI (F.smith lam).U ++ encMat encI (F.smith lam).V ++
    encQ (F.σ lam)

/-- §3.1: the family is efficiently computable: one fixed deterministic polynomial-time map
computes `pp(λ)` from `1^λ`, and the dimensions are polynomially bounded in `λ`. -/
def RoundingFamily.Efficient (F : RoundingFamily) : Prop :=
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam, g (unary lam) = F.pp lam) ∧
  ∃ p : Polynomial ℕ, ∀ lam, F.N lam ≤ p.eval lam ∧ F.d lam ≤ p.eval lam

/-- `Adv^{dLAR}_D(λ, t)` for the family (Definition 3.7), label `f_T`. -/
noncomputable def RoundingFamily.advLAR (F : RoundingFamily) (D : Family) (lam t : ℕ) : ℝ :=
  InfoLossLAR.WorstCase.advLAR D lam (F.pp lam) (F.q lam) (F.N lam) (F.d lam) (F.d lam - F.r lam) t (F.smith lam).fT

/-- `Adv^{UZF-LWE}_B(λ, t)`: the block-LWE advantage with `χ = U(F_{T,0})` (§4, p. 21). -/
noncomputable def RoundingFamily.advUZF (F : RoundingFamily) (B : Family) (lam t : ℕ) : ℝ :=
  advLWE B lam (F.pp lam) (F.q lam) (F.N lam) (F.d lam) t (unifZeroFiber (F.smith lam).fT)

/-- `Adv^{Gauss-LWE}_B(λ, t)`: the block-LWE advantage with `χ = χ_G` of width `σ(λ)`
(Definition 2.11). -/
noncomputable def RoundingFamily.advGauss (F : RoundingFamily) (B : Family) (lam t : ℕ) : ℝ :=
  advLWE B lam (F.pp lam) (F.q lam) (F.N lam) (F.d lam) t (chiG (F.q lam) (F.d lam) (F.σ lam))

/-- Definition 5.3 (p. 24), for a family given by its sampler input `inp λ` (the code of
`(1^λ, pp)`), modulus, dimension, width and label function: the family **admits fixed-order
Gaussian T-AFTs** if for every integer `c ≥ 1` there is a uniform classical PPT sampler
`Sample_c` (file `QPT`, `IsPPTAffineSampler`) whose every output `(Q, β)` has
`Q mod q ∈ GL_d(𝔽_q)`, at every `λ`, and such that `Δ(L(Eval(Q, β, e)), U(F_{T,0})) ≤ λ^{−c}`
for all `λ ≥ λ₀(c)`, with `(Q, β) ← Sample_c(1^λ, pp)` and `e ← χ_G` independent. The sampler's
polynomial and the threshold may depend on `c`. (`Eval` is the affine map `Qx + β mod q`, which
is deterministic polynomial time.) -/
def AdmitsFixedOrderGaussianAFT (inp : ℕ → Str) (q d ℓ : ℕ → ℕ) [∀ lam, NeZero (q lam)]
    (σ : ℕ → ℝ) (f : (lam : ℕ) → (Fin (d lam) → ZMod (q lam)) → Fin (ℓ lam) → ZMod (q lam)) :
    Prop :=
  ∀ c : ℕ, 1 ≤ c →
    ∃ (m : Polynomial ℕ)
      (S : (lam : ℕ) → (Fin (m.eval lam) → Bool) →
        Matrix (Fin (d lam)) (Fin (d lam)) ℤ × (Fin (d lam) → ℤ)),
      IsPPTAffineSampler inp d m S ∧
      (∀ lam ρ, IsUnit (matModq (q lam) (S lam ρ).1).det) ∧
      ∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
        sdist (transportLaw (S lam) (chiG (q lam) (d lam) (σ lam))) (unifZeroFiber (f lam)) ≤
          (lam : ℝ) ^ (-(c : ℝ))

/-- Definition 5.3 for a §3.1 family: the sampler reads `(1^λ, pp)`. -/
def RoundingFamily.AdmitsFixedOrderGaussianAFT (F : RoundingFamily) : Prop :=
  InfoLossLAR.WorstCase.AdmitsFixedOrderGaussianAFT (fun lam => encPair (unary lam) (F.pp lam))
    F.q F.d F.ell (fun lam => (F.σ lam : ℝ)) (fun lam => (F.smith lam).fT)

/-! ### The fixed family of §9.9 (p. 58) -/

/-- `L = λ + 2`. -/
def famL (lam : ℕ) : ℕ := lam + 2

/-- The family's `q`: the least prime `≥ 2^{16} t^8` with `t = L^8`, i.e. `≥ 2^{16} L^{64}`. -/
def famq (lam : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (2 ^ 16 * famL lam ^ 64))

instance (lam : ℕ) : NeZero (famq lam) :=
  ⟨(Nat.find_spec (Nat.exists_infinite_primes (2 ^ 16 * famL lam ^ 64))).2.ne_zero⟩

/-- `N = λ`. -/
def famN (lam : ℕ) : ℕ := lam

/-- `d = n_B + 2g` with `n_B = q t^{12} = q L^{96}` and `g = t^{16} = L^{128}`. -/
def famd (lam : ℕ) : ℕ := famq lam * famL lam ^ 96 + 2 * famL lam ^ 128

/-- `σ = L`. -/
def famσ (lam : ℕ) : ℕ := famL lam

/-- The binary code of the fixed family's `pp(λ) = (q, N, d, σ)`; `T` (Definition 6.3) and the
scalar encoding `P = 1ᵀ` (`ℓ = 1`, `r = d − 1`) are determined by `(q, d)`. -/
def famPP (lam : ℕ) : Str := encB (famq lam) ++ encB (famN lam) ++ encB (famd lam) ++ encB (famσ lam)

/-- The fixed family's label `f_T(x) = ∑_j ⌊(T[x]_q)_j / q⌋ mod q` (Definition 6.3, `P = 1ᵀ`),
as a vector in `𝔽_q^1` (`ℓ = 1`). -/
def famLabel (lam : ℕ) (x : Fin (famd lam) → ZMod (famq lam)) : Fin 1 → ZMod (famq lam) :=
  fun _ => fT63 (famq lam) (famd lam) x

/-- `Adv^{dLAR}_D(λ, t)` for the fixed family of §9.9 (Definition 3.7). -/
noncomputable def famAdvLAR (D : Family) (lam t : ℕ) : ℝ :=
  advLAR D lam (famPP lam) (famq lam) (famN lam) (famd lam) 1 t (famLabel lam)

/-- The sampler input `(1^λ, pp)` of the fixed family. -/
def famInput (lam : ℕ) : Str := encPair (unary lam) (famPP lam)

end InfoLossLAR.WorstCase


