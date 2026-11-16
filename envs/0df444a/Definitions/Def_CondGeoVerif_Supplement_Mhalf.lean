-- Prove2me | Definitions.Def_CondGeoVerif_Supplement_Mhalf
-- name    : CondGeoVerif_Supplement_Mhalf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:10:20.276594+00:00
-- url     : https://prove2.me/theorems/97315f5c-e844-4382-9c8e-cfc205d74a40
-- title:
--   The signed conditional moment problem $M_\eta(u)$, $J_\eta$, the dual coefficients $\alpha_\eta,\gamma_\eta$, and the revealed-coordinate certificate $H_\lambda$, $A_\lambda$, $V_\lambda$
-- statement:
--   Let $G\sim N(0,1)$ and $0<\eta<1/2$. The **signed conditional moment problem** (D.1) is
--   $$M_\eta(u)=\sup\{\mathbb E[e(G)1\{G<-u\}]:0\le e\le1,\ \mathbb E e(G)=\eta,\ \mathbb E[Ge(G)]=0\},$$
--   and (D.6) sets $F_\eta(u)=2M_\eta(u)-\bar\Phi(u)$, $J_\eta=\int_0^\infty F_\eta(u)\,du$. With $b_\eta=\Phi^{-1}((1+\eta)/2)$ and $k_\eta=\Phi^{-1}(1-\eta/2)$, the roots $\ell,z>|u|$ of
--   $$\phi(\ell)+\phi(z)=\phi(u),\qquad \bar\Phi(u)-\bar\Phi(\ell)+\bar\Phi(z)=\eta\qquad(D.2)$$
--   define the **dual coefficients** $(\alpha_\eta,\gamma_\eta)(u)=(1,0)$ for $u\le-b_\eta$, $(z/(\ell+z),-1/(\ell+z))$ for $-b_\eta<u<k_\eta$, and $(0,0)$ for $u\ge k_\eta$.
--
--   **Revealed coordinates (§D.4).** For $X\sim N(0,I_d)$, a unit candidate normal $v$, a matrix $S$ with orthonormal columns perpendicular to $v$, $T=v\cdot X$, $U=S^\top X$, $Z=(I-vv^\top-SS^\top)X$, a unit coefficient tuple $\lambda=(c,\beta,\sigma)$ with $\sigma\ge0$, and a residual unit $n$: $h_0=\mathrm{sign}(T)$, $h_w=\mathrm{sign}(cT+\beta\cdot U+\sigma n\cdot X)$, $D_\lambda=1\{h_0\ne h_w\}$. For $\sigma>0$, $u_\lambda=\mathrm{sign}(T)(cT+\beta\cdot U)/\sigma$, $\alpha_\lambda=\alpha_\eta(u_\lambda)$, $\gamma_\lambda=\gamma_\eta(u_\lambda)$ and
--   $$H_\lambda=2(D_\lambda-\alpha_\lambda-\gamma_\lambda\,\mathrm{sign}(T)N)_++2\eta\alpha_\lambda-D_\lambda,\qquad N=n\cdot X;$$
--   for $\sigma=0$, $\alpha_\lambda=D_\lambda$, $\gamma_\lambda=0$ and $H_\lambda=-aD_\lambda$ with $a=1-2\eta$. For a labeled law, $E_0=1\{Y\ne h_0(X)\}$, $A_\lambda=\mathbb E[\alpha_\lambda(E_0-\eta)]$ and $V_\lambda=\mathbb E[\gamma_\lambda\,\mathrm{sign}(T)ZE_0]\in\mathbb R^d$.
--
--   These are the objects of Theorems D.2 and D.5.
--
--   **Formalization Note** $M_\eta(u)$ is the published first-moment program `Mprog 1 η` in dimension one with disagreement $1\{z_1<-u\}$. The roots are selected by choice; by Lemma D.1 they exist and are unique where they are used. $J_\eta$ is a Lebesgue integral of a measurable integrand dominated by $\bar\Phi$.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §D.1, p.38 (PDF p.41), (D.1)–(D.2); §D.2, p.39, (D.6); §D.4, p.41 (PDF p.44); Theorem D.5, pp.41–42

import Mathlib
import Definitions.Def_CondGeoVerif_Mprog
import Definitions.Def_CondGeoVerif_Supplement_critA
import Definitions.Def_CondGeoVerif_Supplement_boolComp

set_option autoImplicit false

namespace CondGeoVerif.Supplement

noncomputable section

open MeasureTheory ProbabilityTheory Cohen2019.Robust CondGeoVerif
open scoped Matrix

/-- **The signed conditional moment problem** (D.1) (Chen, *The Conditional Geometry of Statistical
Verification*, manuscript, October 2026, sha256 07a66d18…, §D.1, p.38 = PDF p.41):
`M_η(u) = sup{E[e(G)1{G < −u}] : 0 ≤ e ≤ 1, E e(G) = η, E[G e(G)] = 0}`, `G ∼ N(0, 1)`.

**Formalization Note** This is the published first-moment program `Mprog 1 η` in dimension `r = 1`
with the disagreement indicator `D(z) = 1{z₁ < −u}` (allocations are Borel with values in
`[0, 1]`). -/
noncomputable def Mhalf (η u : ℝ) : ℝ :=
  Mprog 1 η (fun z : Vec 1 => decide (z 0 < -u))

/-- **The conditional moment threshold integral** (D.6) (Chen, Oct. 2026, §D.2, p.39 = PDF p.42):
`F_η(u) = 2M_η(u) − Φ̄(u)` and `J_η = ∫₀^∞ F_η(u) du`.

**Formalization Note** A Lebesgue integral over `(0, ∞)`. The integrand is measurable
(`u ↦ M_η(u)` is nonincreasing, since the indicator shrinks as `u` grows) and bounded in absolute
value by `Φ̄(u)`, which is integrable on `(0, ∞)` (paper, p.39), so the integral is the paper's. -/
noncomputable def Jeta (η : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), (2 * Mhalf η u - Phibar u)

/-- `b_η = Φ⁻¹((1 + η)/2)` (Chen, Oct. 2026, §D.1, p.38). -/
noncomputable def bEta (η : ℝ) : ℝ := PhiInvReal ((1 + η) / 2)

/-- `k_η = Φ⁻¹(1 − η/2)` (Chen, Oct. 2026, §D.1, p.38). -/
noncomputable def kEta (η : ℝ) : ℝ := PhiInvReal (1 - η / 2)

/-- The root conditions (D.2) (Chen, Oct. 2026, Lemma D.1, p.38): `ℓ, z > |u|`,
`ϕ(ℓ) + ϕ(z) = ϕ(u)`, `Φ̄(u) − Φ̄(ℓ) + Φ̄(z) = η`. -/
def IsRootPair (η u : ℝ) (p : ℝ × ℝ) : Prop :=
  |u| < p.1 ∧ |u| < p.2 ∧ phi p.1 + phi p.2 = phi u ∧ Phibar u - Phibar p.1 + Phibar p.2 = η

open Classical in
/-- The roots `(ℓ, z)` of (D.2) (Chen, Oct. 2026, Lemma D.1, p.38), when they exist.

**Formalization Note** Chosen by `Classical.choose`; by Lemma D.1 the roots exist and are unique for
`0 < η < 1/2` and `−b_η < u < k_η`, the only region where they are used, so the choice is the
unique root pair (and continuous in `u` there). Elsewhere the value `(0, 0)` is never used. -/
noncomputable def roots (η u : ℝ) : ℝ × ℝ :=
  if h : ∃ p : ℝ × ℝ, IsRootPair η u p then Classical.choose h else (0, 0)

/-- **The dual coefficient** `α_η(u)` (Chen, Oct. 2026, Lemma D.1, p.38): `1` for `u ≤ −b_η`,
`z/(ℓ + z)` for `−b_η < u < k_η`, and `0` for `u ≥ k_η`, where `(ℓ, z)` solve (D.2). -/
noncomputable def alphaEta (η u : ℝ) : ℝ :=
  if u ≤ -bEta η then 1
  else if u < kEta η then (roots η u).2 / ((roots η u).1 + (roots η u).2) else 0

/-- **The dual coefficient** `γ_η(u)` (Chen, Oct. 2026, Lemma D.1, p.38): `0` for `u ≤ −b_η`,
`−1/(ℓ + z)` for `−b_η < u < k_η`, and `0` for `u ≥ k_η`. -/
noncomputable def gammaEta (η u : ℝ) : ℝ :=
  if u ≤ -bEta η then 0
  else if u < kEta η then -1 / ((roots η u).1 + (roots η u).2) else 0

/-! ### Revealed coordinates (Chen, Oct. 2026, §D.4, p.41 = PDF p.44)

`X ∼ N(0, I_d)`, a unit candidate normal `v`, a matrix `S ∈ ℝ^{d×m}` with orthonormal columns
perpendicular to `v`, `T = v·X`, `U = SᵀX`, `Z = (I − vvᵀ − SSᵀ)X`, a unit coefficient tuple
`λ = (c, β, σ)`, `σ ≥ 0`, and a residual unit `n` when `σ > 0`. -/

/-- The candidate `h₀ = sign(T) = sign(v·x)`. -/
noncomputable def hCand {d : ℕ} (v : Vec d) : Vec d → Bool := fun x => sgn (inner ℝ v x)

/-- The competitor `h_w = sign(cT + β·U + σ n·X)`. -/
noncomputable def hComp {d m : ℕ} (v : Vec d) (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ) (β : Vec m)
    (σ : ℝ) (n : Vec d) : Vec d → Bool :=
  fun x => sgn (c * inner ℝ v x + inner ℝ β (matVec Sᵀ x) + σ * inner ℝ n x)

/-- The disagreement indicator `D_λ = 1{h₀ ≠ h_w}`. -/
noncomputable def Dlam {d m : ℕ} (v : Vec d) (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ) (β : Vec m)
    (σ : ℝ) (n : Vec d) (x : Vec d) : ℝ :=
  ind (decide (hComp v S c β σ n x ≠ hCand v x))

/-- `u_λ = sign(T)(cT + β·U)/σ` (used for `σ > 0`). -/
noncomputable def uLam {d m : ℕ} (v : Vec d) (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ) (β : Vec m)
    (σ : ℝ) (x : Vec d) : ℝ :=
  sgnR (inner ℝ v x) * (c * inner ℝ v x + inner ℝ β (matVec Sᵀ x)) / σ

/-- `α_λ = α_η(u_λ)` for `σ > 0`, and `α_λ = D_λ` for `σ = 0`. -/
noncomputable def alphaLam (η : ℝ) {d m : ℕ} (v : Vec d) (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ)
    (β : Vec m) (σ : ℝ) (n : Vec d) (x : Vec d) : ℝ :=
  if 0 < σ then alphaEta η (uLam v S c β σ x) else Dlam v S c β σ n x

/-- `γ_λ = γ_η(u_λ)` for `σ > 0`, and `γ_λ = 0` for `σ = 0`. -/
noncomputable def gammaLam (η : ℝ) {d m : ℕ} (v : Vec d) (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ)
    (β : Vec m) (σ : ℝ) (x : Vec d) : ℝ :=
  if 0 < σ then gammaEta η (uLam v S c β σ x) else 0

/-- **The Gaussian baseline** of Theorem D.5 (Chen, Oct. 2026, p.41): for `σ > 0`,
`H_λ = 2(D_λ − α_λ − γ_λ sign(T)N)₊ + 2ηα_λ − D_λ` with `N = n·X` and `η = (1 − a)/2`; for `σ = 0`,
`H_λ = −aD_λ`. -/
noncomputable def Hlam (a : ℝ) {d m : ℕ} (v : Vec d) (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ)
    (β : Vec m) (σ : ℝ) (n : Vec d) (x : Vec d) : ℝ :=
  if 0 < σ then
    2 * max (Dlam v S c β σ n x - alphaLam ((1 - a) / 2) v S c β σ n x
        - gammaLam ((1 - a) / 2) v S c β σ x * sgnR (inner ℝ v x) * inner ℝ n x) 0
      + 2 * ((1 - a) / 2) * alphaLam ((1 - a) / 2) v S c β σ n x - Dlam v S c β σ n x
  else -a * Dlam v S c β σ n x

/-- The residual component `Z = (I − vvᵀ − SSᵀ)x`. -/
noncomputable def residual {d m : ℕ} (v : Vec d) (S : Matrix (Fin d) (Fin m) ℝ) (x : Vec d) :
    Vec d :=
  x - inner ℝ v x • v - matVec S (matVec Sᵀ x)

/-- `A_λ = E[α_λ(E₀ − η)]` under a labeled law `P`, with `E₀ = 1{Y ≠ h₀(X)}` (Chen, Oct. 2026,
Theorem D.5, p.42 = PDF p.45). -/
noncomputable def Alam (η : ℝ) {d m : ℕ} (P : Measure (Vec d × Bool)) (v : Vec d)
    (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ) (β : Vec m) (σ : ℝ) (n : Vec d) : ℝ :=
  ∫ p, alphaLam η v S c β σ n p.1 * (ind (decide (p.2 ≠ hCand v p.1)) - η) ∂P

/-- `V_λ = E[γ_λ sign(T) Z E₀] ∈ ℝᵈ` under a labeled law `P` (Chen, Oct. 2026, Theorem D.5,
p.42). -/
noncomputable def Vlam (η : ℝ) {d m : ℕ} (P : Measure (Vec d × Bool)) (v : Vec d)
    (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ) (β : Vec m) (σ : ℝ) : Vec d :=
  ∫ p, (gammaLam η v S c β σ p.1 * sgnR (inner ℝ v p.1) * ind (decide (p.2 ≠ hCand v p.1))) •
    residual v S p.1 ∂P

end

end CondGeoVerif.Supplement


