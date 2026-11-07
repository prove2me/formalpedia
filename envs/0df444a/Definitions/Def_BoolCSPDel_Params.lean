-- Prove2me | Definitions.Def_BoolCSPDel_Params
-- name    : BoolCSPDel_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:46.554813+00:00
-- url     : https://prove2.me/theorems/a939daa4-a4a2-4c7a-9349-f44d0fda3fe7
-- title:
--   The parameters of §A.1.3, $h$-wise masks, (A.2), and the sketch pair interface
-- statement:
--   For $m,D,\mu,b_0$, $\lambda=2^{-L}$, $\varepsilon=2^{-e}$, $\delta=2^{-g}$: $\lambda_0$ is the least power of two at least $\max\{1,b_0m\mu^2\}$, $K=1+\log_2(\lambda_0/\lambda)$, $\lambda_j=2^{-j}\lambda_0$, $T=\lceil\log_4(8Km/\delta)\rceil$, $\beta_c=\delta/(8KT)$, $\beta_s=\delta/(8KT(T+1))$, $h=2\lceil\log_2(4D^2/\beta_c)\rceil$, $\varepsilon_s=\varepsilon/(64T)$, $\varepsilon_a=\varepsilon/(1000(T+1))$, $\varepsilon_v=1/100$, $\eta=\varepsilon_s^2/(2^{14}\cdot1000h)$, $\theta=1024\eta$, $g_a$ the largest power of two at most $\varepsilon_a/100$, $M_{\max}=\lceil12D/\theta\rceil$, $W_{\max}=2^{T+3}\mu$, $C_{\max}=4m(T+2)W_{\max}(b_0+1)$, $U$ the least power of two at least $\lambda_0+b_0M_{\max}W_{\max}^2$, $g_v$ the largest power of two at most $\varepsilon_v\lambda/(8U^2D)$, and $r_{\mathrm{inv}}=(U/\lambda)\lceil\log_2(8U(b_0+1)/(\varepsilon_v\lambda))\rceil$.
--
--   A mask is $h$-wise independent with Bernoulli($1/4$) entries. A **sketch pair** is a random matrix $\Phi$ with entries in $\{-1,0,1\}$ and estimators read from $\Phi y$. Its guarantee is Lemma A.1: for $A$, $v_1,\dots,v_m$ fixed independently of the seed, with probability at least $1-\beta$ the estimates for $y^{(i)}=Av_i$ satisfy, for every $i$,
--
--   $$|\hat y_i-y^{(i)}_i|\le\alpha\|y^{(i)}\|_2,\qquad 0.9\|y^{(i)}\|_2^2\le\hat\nu_i\le1.1\|y^{(i)}\|_2^2.\tag{A.2}$$
--
--   **Formalization Note** The paper specifies the pair only through this guarantee, so Lean keeps exactly that interface. With $\varepsilon,\delta,\lambda$ powers of two, the logarithms have integer arguments and are computed exactly.
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), §A.1.3, pp.53–54; p.48; Lemma A.1, p.54

import Mathlib

open MeasureTheory

namespace BoolCSPDel

/-- **The parameters of §A.1.3.** Bandekar, Sharma, Velusamy, STOC 2027 submission (manuscript sha256
15f83519…), §A.1.3, pp.53–54: "We now fix all quantities used by the algorithms. We may first round
`ε` and `δ` down to powers of two".

The main inputs: `m, D, μ, b₀`, the regularizer `λ = 2^{-L}`, `ε = 2^{-e}` and `δ = 2^{-g}`.

**Formalization Note.** With `ε`, `δ`, `λ` powers of two, every logarithm of §A.1.3 has an integer
argument, so each `⌈log₂ x⌉` is `Nat.clog 2 x` exactly and "least power of two at least `x`" and
"largest power of two at most `x`" are computed. The formula of each quantity is the page's. -/
structure Params where
  /-- Rows. -/
  m : ℕ
  /-- Columns. -/
  D : ℕ
  /-- Multiplicity bound. -/
  μ : ℕ
  /-- Squared row norm bound. -/
  b₀ : ℕ
  /-- `λ = 2^{-L}`. -/
  L : ℕ
  /-- `ε = 2^{-e}`. -/
  e : ℕ
  /-- `δ = 2^{-g}`. -/
  g : ℕ

namespace Params

variable (P : Params)

/-- `ε`. -/
def eps : ℚ := 1 / 2 ^ P.e
/-- `δ`. -/
def delta : ℚ := 1 / 2 ^ P.g
/-- `λ`. -/
def lam : ℚ := 1 / 2 ^ P.L
/-- (i): `λ₀ = 2^{l₀}` is the least power of two at least `max{1, b₀mμ²}`. -/
def lam0Exp : ℕ := Nat.clog 2 (max 1 (P.b₀ * P.m * P.μ ^ 2))
/-- (i): `λ₀`. -/
def lam0 : ℕ := 2 ^ P.lam0Exp
/-- (i): `K = 1 + log₂(λ₀/λ)`. -/
def K : ℕ := 1 + P.lam0Exp + P.L
/-- (i): `λ_j = 2^{-j} λ₀`. -/
def lamJ (j : ℕ) : ℚ := (P.lam0 : ℚ) / 2 ^ j
/-- (ii): `T = ⌈log₄(8Km/δ)⌉`. -/
def T : ℕ := Nat.clog 4 (8 * P.K * P.m * 2 ^ P.g)
/-- (ii): `β_c = δ/(8KT)`. -/
def betaC : ℚ := P.delta / (8 * P.K * P.T)
/-- (ii): `β_s = δ/(8KT(T + 1))`. -/
def betaS : ℚ := P.delta / (8 * P.K * P.T * (P.T + 1))
/-- (iii): `h = 2⌈log₂(4D²/β_c)⌉`. -/
def h : ℕ := 2 * Nat.clog 2 (4 * P.D ^ 2 * (8 * P.K * P.T) * 2 ^ P.g)
/-- (iii): `ε_s = ε/(64T)`. -/
def epsS : ℚ := P.eps / (64 * P.T)
/-- (iii): `ε_a = ε/(1000(T + 1))`. -/
def epsA : ℚ := P.eps / (1000 * (P.T + 1))
/-- (iii): `ε_v = 1/100`. -/
def epsV : ℚ := 1 / 100
/-- (iv): `η = ε_s²/(2¹⁴ · 1000h)`. -/
def eta : ℚ := P.epsS ^ 2 / (2 ^ 14 * 1000 * P.h)
/-- (iv): `θ = 1024η`. -/
def theta : ℚ := 1024 * P.eta
/-- (iv): `g_a` is the largest power of two at most `ε_a/100`; `100/ε_a` is an integer. -/
def ga : ℚ := 1 / 2 ^ Nat.clog 2 (100 * (1000 * (P.T + 1)) * 2 ^ P.e)
/-- (v): `M_max = ⌈12D/θ⌉`. -/
def Mmax : ℕ := ⌈(12 * P.D : ℚ) / P.theta⌉₊
/-- (v): `W_max = 2^{T+3} μ`. -/
def Wmax : ℕ := 2 ^ (P.T + 3) * P.μ
/-- (v): `C_max = 4m(T + 2) W_max (b₀ + 1)`. -/
def Cmax : ℕ := 4 * P.m * (P.T + 2) * P.Wmax * (P.b₀ + 1)
/-- (vi): `U` is the least power of two at least `λ₀ + b₀ M_max W_max²`. -/
def U : ℕ := 2 ^ Nat.clog 2 (P.lam0 + P.b₀ * P.Mmax * P.Wmax ^ 2)
/-- (vi): `g_v` is the largest power of two at most `ε_v λ/(8U²D)`; the reciprocal is an integer. -/
def gv : ℚ := 1 / 2 ^ Nat.clog 2 (8 * P.U ^ 2 * P.D * 100 * 2 ^ P.L)
/-- (vi): `r_inv = (U/λ)⌈log₂(8U(b₀ + 1)/(ε_v λ))⌉`. -/
def rinv : ℕ := (P.U * 2 ^ P.L) * Nat.clog 2 (8 * P.U * (P.b₀ + 1) * 100 * 2 ^ P.L)

end Params

/-- p.48: the mask law. "Each `ξ_{j,t}(i)` is Bernoulli with mean 1/4. Within a mask, these variables
are `h`-wise independent, meaning that every set of at most `h` entries has the joint distribution of
independent variables." -/
def IsHWiseQuarter {ι : Type} [Fintype ι] (ν : PMF (ι → Bool)) (h : ℕ) : Prop :=
  ∀ (I : Finset ι), I.card ≤ h → ∀ a : ι → Bool,
    ν.toMeasure {ξ | ∀ i ∈ I, ξ i = a i} =
      ∏ i ∈ I, (if a i then (1 / 4 : ENNReal) else 3 / 4)

/-- (A.2), p.54: the estimates `ŷ`, `ν̂` for the vector `y`, coordinate `i`, at accuracy `α`:
`|ŷ − y_i| ≤ α ‖y‖₂` and `0.9‖y‖₂² ≤ ν̂ ≤ 1.1‖y‖₂²`. -/
def EstimatesOK {m : ℕ} (α : ℝ) (y : Fin m → ℝ) (i : Fin m) (yh nu : ℝ) : Prop :=
  |yh - y i| ≤ α * Real.sqrt (y ⬝ᵥ y) ∧
    (9 / 10 : ℝ) * (y ⬝ᵥ y) ≤ nu ∧ nu ≤ (11 / 10 : ℝ) * (y ⬝ᵥ y)

/-- **The sketch pair interface.** §A.1.1, p.48, and Lemma A.1, p.54. A random linear map `Φ` with
coordinate and norm estimators read from `Φy`. The entries of `Φ` lie in `{-1, 0, 1}` (p.54, "We
implement the coordinate and norm estimates with coefficients in {−1, 0, 1}"; Claim A.24 relies on
this for the entry limit).

**Formalization Note.** The paper specifies the pair only through Claims A.5, A.6 and (A.2), so Lean
keeps exactly that interface: any finite seed space with the guarantee `SketchPair.Guarantee`. -/
structure SketchPair (m : ℕ) (Ωs : Type) where
  /-- The number of sketch entries per column. -/
  r : ℕ
  /-- The sketching matrix of a seed. -/
  Φ : Ωs → Matrix (Fin r) (Fin m) ℚ
  /-- Its entries are `-1`, `0` or `1`. -/
  Φ_entry : ∀ s a i, Φ s a i = -1 ∨ Φ s a i = 0 ∨ Φ s a i = 1
  /-- The CountSketch estimate of a coordinate. -/
  coord : Ωs → (Fin r → ℚ) → Fin m → ℚ
  /-- The AMS estimate of the squared norm. -/
  norm : Ωs → (Fin r → ℚ) → ℚ

/-- Lemma A.1, p.54: for `A` and `v₁, …, v_m` fixed independently of the seed, given `ΦA` the estimates
for `y⁽ⁱ⁾ = Av_i` satisfy (A.2), simultaneously for every `i`, with probability at least `1 − β`. -/
def SketchPair.Guarantee {m D : ℕ} {Ωs : Type} [MeasurableSpace Ωs] (pair : SketchPair m Ωs)
    (ν : PMF Ωs) (α β : ℝ) : Prop :=
  ∀ (A : Matrix (Fin m) (Fin D) ℚ) (v : Fin m → Fin D → ℚ),
    ν.toMeasure {s | ¬ ∀ i,
      EstimatesOK α (fun a => ((A.mulVec (v i) a : ℚ) : ℝ)) i
        (pair.coord s ((pair.Φ s * A).mulVec (v i)) i : ℚ)
        (pair.norm s ((pair.Φ s * A).mulVec (v i)) : ℚ)} ≤ ENNReal.ofReal β

end BoolCSPDel


