-- Prove2me | Definitions.Def_InfoLossLAR_WorstCase_Laws
-- name    : InfoLossLAR_WorstCase_Laws
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:04:24.592823+00:00
-- url     : https://prove2.me/theorems/c1b9a93c-d0a4-44d5-ae20-5f6fbd227d0d
-- title:
--   Statistical distance, the Gaussian law $\chi_G$, negligibility, and the LAR and block-LWE experiments
-- statement:
--   Laws on finite sets are point-mass functions. The **statistical distance** is $\Delta(P,Q)=\frac12\sum_\omega|P(\omega)-Q(\omega)|$ (§2.3). With $\rho_\sigma(x)=\exp(-\pi\|x\|_2^2/\sigma^2)$ (the published `RegevLWE.GaussConv.rho`), the **Gaussian error law** on $\mathbb F_q^d$ is (Definition 2.11)
--   $$\chi_G(e)=\frac{\rho_\sigma([e]_q+q\mathbb Z^d)}{\rho_\sigma(\mathbb Z^d)} .$$
--   A nonnegative $f$ is **negligible** if for every $c>0$, $f(\lambda)\le\lambda^{-c}$ for all large $\lambda$ (§3.1).
--
--   For a label function $f:\mathbb F_q^d\to\mathbb F_q^\ell$ and $t\ge1$ (Definition 3.6): one secret $s\leftarrow U(\mathbb F_q^N)$ (zero included), independent $M_i\leftarrow U(\mathbb F_q^{d\times N})$ and $u_i\leftarrow U(\mathbb F_q^\ell)$; $\mathrm{Real}^{\mathrm{LAR}}_t$ is the law of $\{(M_i,f(M_is))\}_{i=1}^t$ and $\mathrm{Ideal}^{\mathrm{LAR}}_t$ that of $\{(M_i,u_i)\}$; and (Definition 3.7)
--   $$\mathrm{Adv}^{\mathrm{dLAR}}_D(\lambda,t)=\big|\Pr[D(1^\lambda,\mathrm{pp},\mathrm{Real}^{\mathrm{LAR}}_t)=1]-\Pr[D(1^\lambda,\mathrm{pp},\mathrm{Ideal}^{\mathrm{LAR}}_t)=1]\big| .$$
--   Block LWE (Definition 2.10) with error law $\chi$: $A_i\leftarrow U(\mathbb F_q^{d\times N})$, $e_i\leftarrow\chi$, $u_i\leftarrow U(\mathbb F_q^d)$, real samples $(A_i,A_is+e_i)$, ideal samples $(A_i,u_i)$, and $\mathrm{Adv}^{\mathrm{LWE}}_B$ the analogous gap. The affine evaluation is $\mathrm{Eval}(Q,\beta,x)=Qx+\beta\bmod q$ (Definition 5.1), and the **transport law** is the law of $\mathrm{Eval}(Q,\beta,e)$ for $(Q,\beta)$ from uniform coins and $e\leftarrow\chi$ independent.
--
--   **Formalization Note.** All experiments are exact finite averages; the input of the algorithm is the binary code of $(1^\lambda,\mathrm{pp},\text{table})$. $\Delta$ carries the factor $\frac12$ (the published `RegevLWE` `statDist` does not and is not used).
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 14 §2.3, pp. 16–18 Definitions 2.8, 2.10–2.12, p. 20 §3.1 and Definitions 3.6–3.7, p. 21, p. 23 Definition 5.1

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Rounding

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

/-!
# Laws, statistical distance, the Gaussian error law, and the LAR and LWE experiments

Chen Qian, *Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices*,
arXiv:2611.05136 (held version, sha256 2ebdfbf3…), §2.3, p. 14 (statistical distance with the
factor `1/2`), §2.6, pp. 16–17 (Definitions 2.8, 2.10, 2.11: `ρ_σ`, `D_{ℤ^d,σ}`, shared-secret
block LWE, Gaussian LWE `χ_G = D_{ℤ^d,σ} mod q`), p. 18 (Definition 2.12: uniform-zero-fiber
LWE), p. 20 (§3.1 negligible; Definitions 3.6, 3.7: real/ideal LAR and the decisional
advantage), p. 21 (`Adv^{LWE}_B`), Definition 5.1, p. 23 (`Eval(Q, β, x) = Qx + β mod q`).

Laws on finite sets are real-valued point-mass functions. All experiments are finite, so every
probability is an exact finite average: one secret `s ← U(𝔽_q^N)` (zero included), independent
uniform matrices, labels, responses, and errors weighted by their law. The classical input of the
algorithm is `encInput λ pp table` (file `Encoding`), and its acceptance probability is
`acceptProb` (file `QPT`).

A sample table is an indexed family `Fin t → 𝔽_q^{d×N} × 𝔽_q^k` (`k = ℓ` for LAR, `k = d` for
LWE), encoded entry by entry in index order.
-/

/-- The statistical distance `Δ(P, Q) = (1/2) ∑_ω |P(ω) − Q(ω)|` of two laws on a finite set
(§2.3, p. 14), with the factor `1/2`. -/
noncomputable def sdist {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ :=
  (1 / 2) * ∑ a, |P a - Q a|

/-- The uniform law `U(S)` on a finite set `S` (point mass `1/|S|` on `S`, `0` off it). -/
noncomputable def unifOn {α : Type*} (S : Finset α) [DecidableEq α] (a : α) : ℝ :=
  if a ∈ S then ((S.card : ℝ))⁻¹ else 0

/-- The uniform law on the zero fiber `F_{g,0} = g^{-1}(0)` of a label function `g`
(Definition 2.12, p. 18; with `g = f_T` this is `U(F_{T,0})` of §4). -/
noncomputable def unifZeroFiber {q d ℓ : ℕ} [NeZero q] (g : (Fin d → ZMod q) → Fin ℓ → ZMod q)
    (e : Fin d → ZMod q) : ℝ :=
  unifOn (Finset.univ.filter fun x => g x = 0) e

/-- `ρ_σ(x) = exp(−π‖x‖₂² / σ²)` at an integer point `x ∈ ℤ^d` (§2.6, p. 16), via the published
`RegevLWE.GaussConv.rho` on `ℝ^d` with the Euclidean norm. -/
noncomputable def rhoInt (σ : ℝ) {d : ℕ} (x : Fin d → ℤ) : ℝ :=
  RegevLWE.GaussConv.rho σ (WithLp.toLp 2 (fun i => (x i : ℝ)))

/-- Definition 2.11 (p. 17): the Gaussian error law `χ_G = D_{ℤ^d,σ} mod q` on `𝔽_q^d`,
`χ_G(e) = ρ_σ([e]_q + qℤ^d) / ρ_σ(ℤ^d)`: the mass of the integer points reducing to `e`, divided
by the total mass. (Both sums converge for `σ > 0`.) -/
noncomputable def chiG (q d : ℕ) (σ : ℝ) (e : Fin d → ZMod q) : ℝ :=
  (∑' x : Fin d → ℤ, if modq q x = e then rhoInt σ x else 0) / ∑' x : Fin d → ℤ, rhoInt σ x

/-- §3.1 (p. 20): a nonnegative function of `λ` is negligible if for every constant `c > 0` it is
at most `λ^{−c}` for all sufficiently large `λ`. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ f n) ∧ ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ n ≥ n₀, f n ≤ (n : ℝ) ^ (-c)

/-- A function `ℕ → ℕ` bounded by a polynomial. -/
def PolyBoundedFn (t : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, t n ≤ p.eval n

/-- The binary code of a sample table `{(A_i, b_i)}_{i=1}^t`. -/
def encTable {q d N k t : ℕ} (tbl : Fin t → Matrix (Fin d) (Fin N) (ZMod q) × (Fin k → ZMod q)) :
    Str :=
  encVec (fun p => encPair (encMat encZM p.1) (encVec encZM p.2)) tbl

/-- `Pr[D(1^λ, pp, Real^{LAR}_t) = 1]` (Definition 3.6, p. 20) for the label function `f`: one
uniform secret `s ∈ 𝔽_q^N`, independent uniform `M_i ∈ 𝔽_q^{d×N}`, samples `(M_i, f(M_i s))`. -/
noncomputable def prRealLAR (D : Family) (lam : ℕ) (pp : Str) (q N d ℓ t : ℕ) [NeZero q]
    (f : (Fin d → ZMod q) → Fin ℓ → ZMod q) : ℝ :=
  avg fun s : Fin N → ZMod q => avg fun M : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
    acceptProb D (encInput lam pp (encTable fun i => (M i, f ((M i).mulVec s))))

/-- `Pr[D(1^λ, pp, Ideal^{LAR}_t) = 1]` (Definition 3.6): independent uniform `M_i` and uniform
labels `u_i ∈ 𝔽_q^ℓ`. -/
noncomputable def prIdealLAR (D : Family) (lam : ℕ) (pp : Str) (q N d ℓ t : ℕ) [NeZero q] : ℝ :=
  avg fun M : Fin t → Matrix (Fin d) (Fin N) (ZMod q) => avg fun u : Fin t → Fin ℓ → ZMod q =>
    acceptProb D (encInput lam pp (encTable fun i => (M i, u i)))

/-- Definition 3.7 (p. 20): `Adv^{dLAR}_D(λ, t) = |Pr[D(1^λ, pp, Real) = 1] − Pr[D(1^λ, pp,
Ideal) = 1]|`. -/
noncomputable def advLAR (D : Family) (lam : ℕ) (pp : Str) (q N d ℓ t : ℕ) [NeZero q]
    (f : (Fin d → ZMod q) → Fin ℓ → ZMod q) : ℝ :=
  |prRealLAR D lam pp q N d ℓ t f - prIdealLAR D lam pp q N d ℓ t|

/-- `Pr[B(1^λ, pp, Real^{LWE}_{χ,t}) = 1]` (Definition 2.10, p. 17): one uniform secret
`s ∈ 𝔽_q^N`, independent uniform `A_i ∈ 𝔽_q^{d×N}` and errors `e_i ← χ`; samples
`(A_i, A_i s + e_i)`. -/
noncomputable def prRealLWE (B : Family) (lam : ℕ) (pp : Str) (q N d t : ℕ) [NeZero q]
    (χ : (Fin d → ZMod q) → ℝ) : ℝ :=
  avg fun s : Fin N → ZMod q => avg fun A : Fin t → Matrix (Fin d) (Fin N) (ZMod q) =>
    ∑ e : Fin t → Fin d → ZMod q, (∏ i, χ (e i)) *
      acceptProb B (encInput lam pp (encTable fun i => (A i, (A i).mulVec s + e i)))

/-- `Pr[B(1^λ, pp, Ideal^{LWE}_t) = 1]` (Definition 2.10): independent uniform `A_i` and
`u_i ∈ 𝔽_q^d`. -/
noncomputable def prIdealLWE (B : Family) (lam : ℕ) (pp : Str) (q N d t : ℕ) [NeZero q] : ℝ :=
  avg fun A : Fin t → Matrix (Fin d) (Fin N) (ZMod q) => avg fun u : Fin t → Fin d → ZMod q =>
    acceptProb B (encInput lam pp (encTable fun i => (A i, u i)))

/-- `Adv^{LWE}_B(λ, t)` (p. 21) for the error law `χ`. -/
noncomputable def advLWE (B : Family) (lam : ℕ) (pp : Str) (q N d t : ℕ) [NeZero q]
    (χ : (Fin d → ZMod q) → ℝ) : ℝ :=
  |prRealLWE B lam pp q N d t χ - prIdealLWE B lam pp q N d t|

/-- The affine evaluation of Definition 5.1 (p. 23): `Eval(Q, β, x) = Qx + β mod q ∈ 𝔽_q^d` for
integer `Q, β` and `x ∈ 𝔽_q^d`. -/
def evalAffine {q d : ℕ} (Q : Matrix (Fin d) (Fin d) ℤ) (β : Fin d → ℤ) (x : Fin d → ZMod q) :
    Fin d → ZMod q :=
  (matModq q Q).mulVec x + modq q β

/-- The law of `Eval(Q, β, e)` (Definitions 5.1, 5.3) for a source `e ← χ` independent of the
affine data `(Q, β) = S(ρ)`, with `ρ` uniform on a finite coin space `Ω`. -/
noncomputable def transportLaw {q d : ℕ} [NeZero q] {Ω : Type*} [Fintype Ω]
    (S : Ω → Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ)) (χ : (Fin d → ZMod q) → ℝ)
    (x' : Fin d → ZMod q) : ℝ :=
  avg fun ρ : Ω => ∑ e : Fin d → ZMod q, if evalAffine (S ρ).1 (S ρ).2 e = x' then χ e else 0

end InfoLossLAR.WorstCase


