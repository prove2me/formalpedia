-- Prove2me | Definitions.Def_FreeWeaver_Walk_Walk
-- name    : FreeWeaver_Walk_Walk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:36:07.97049+00:00
-- url     : https://prove2.me/theorems/16eb0eee-097d-4502-a906-f48a3649ce0a
-- title:
--   §8–§9 and Appendix E.2–E.3 — parameters (9.1), invariant (9.2), Algorithm 1, the step size t_*, and Algorithm 2 with oracle answers
-- statement:
--   Section 9 takes $\varepsilon=\max_ia_i$ (`epsMax`), $u=128$, $D=2m$ and the parameters (9.1): $\rho=1/(100n^2)$, $t_o=\rho/16$, $\zeta=t_o/1000$, $\eta=t_o\rho/100$, $\kappa=1/(2uDn\cdot128^2)$, with the smooth profile $c_\zeta$ (`walkProfile`). `tStar` is the step size $t_*=\min\{r_0/2,\kappa/(8C_{\mathcal F})\}$ of Lemma E.2 with $c_{\min}=u\rho/2$, $\beta_1,\beta_2,\beta_3$, $M_{\mathcal Y}=8n(1+\beta_1+\beta_2+\beta_3)$, $\delta_0=\sqrt{u\varepsilon}/(4\sqrt D(1+4D)^2)$, $r_0=\min\{\rho/4,\delta_0/(4M_{\mathcal Y})\}$, $C_{\mathcal R}=2/\delta_0$, $C_{\mathcal F}=24C_{\mathcal R}^5M_{\mathcal Y}^3+18C_{\mathcal R}^4M_{\mathcal Y}^2+2C_{\mathcal R}^3M_{\mathcal Y}$ (§E.3). `Inv92 … ε x z C` is (9.2): $z>\lambda_+(\mathcal Y(x))$, $\mathcal F(x,z)\le B$, $z\le z_0+C$ with $C$ the charges paid so far. `roundAlg v x` is Algorithm 1: $E_0\leftarrow0$, $\sigma_i\leftarrow x_i$ off the live set, then for the live $i$ in increasing order $\sigma_i\leftarrow$ the $s\in\{1,-1\}$ minimizing $\|E_0+(s-x_i)A_i\|_{HS}$ ($s=1$ on ties) and $E_0\leftarrow E_0+(\sigma_i-x_i)A_i$; `roundInput` is its machine input (`weaverInput` followed by $x$). `WalkPass v s ω cf out` is one pass of the loop of Algorithm 2 from the configuration $cf=(x,z,\text{charge})$: boundary rounding of the live $i$ with $|x_i|\ge1-\rho$ (charge $\varepsilon(1-|x_i|)$ each); return $x$ if no coordinate is live; otherwise, with oracle values $\hat q$ within the tolerances of Proposition E.4(a), the outward move of the smallest live $i$ with $\ell_i\hat q_i\ge1-\eta/2$ (`secant` is $\ell_i$; charge $t_o\eta\varepsilon$), or Round$(x)$ if $\hat{\mathfrak m}=\sum_{i\text{ live}}c_i\hat q_i^2\le9/128$, or a curvature step to whichever of $x\pm t_*h$ has the smaller approximate potential ($x+t_*h$ on ties), for any unit $h$ on the live set with $x^Th=0$, $\mathcal F''[h,h]<-\kappa/2$ and approximate potentials to error $\kappa t_*^2/96$ (Proposition E.4(b)–(d)). `WalkReach` is the set of configurations reached after $k$ passes from $(0,z_0,0)$.
--
--   **Formalization Note** Quantifying over every oracle answer within the tolerances of Proposition E.4 replaces Algorithm 3 and the procedure of Lemma E.8; the paper says these tolerances are their only properties used (p. 35).
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), pp. 34–37 (Algorithm 1, (9.1), (9.2), Algorithm 2) and pp. 59–60 (Lemma E.2, Proposition E.4, §E.3)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FreeWeaver_Walk_Weaver
import Definitions.Def_FreeWeaver_Walk_FreeModel

namespace FreeWeaver.Walk

noncomputable section

/-!
# The walk: parameters, invariant, final rounding and the resolvent-square walk

Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version dated
November 3, 2026; sha256 c06bf728…), §8–§9, pp. 34–37 (Algorithm 1, the parameters (9.1), the
invariant (9.2), Algorithm 2), Appendix E.2–E.3, pp. 59–60 (the step size `t_*` of Lemma E.2 and the
tolerances of Proposition E.4).

**Formalization Note** Section 9 takes `ε = max_i ‖v_i‖²` (`epsMax`), `u = 128`, `D = 2m`, and the
smooth profile `c = c_ζ` with `ζ = t_o/1000`. The step size `t_* = min{r_0/2, κ/(8C_ℱ)}` is spelled
out from §E.3: `c_min = uρ/2`, `β_1, β_2, β_3`, `M_Y = 8n(1 + β_1 + β_2 + β_3)`,
`δ_0 = √(uε)/(4√D(1 + 4D)²)` (E.1), `r_0 = min{ρ/4, δ_0/(4M_Y)}`, `C_R = 2/δ_0`,
`C_ℱ = 24C_R⁵M_Y³ + 18C_R⁴M_Y² + 2C_R³M_Y` (Lemma E.6).

Algorithm 2 is a relation `WalkPass` between a configuration `(x, z, total charge)` and the outcome of
one pass through its loop: a new configuration or returned signs. The numerical oracle of Appendix
E.2 (Algorithm 3) is replaced by every answer that meets the tolerances of Proposition E.4: values
`q̂_i` with `|q̂_i − q_i| ≤ η/(12u)` and `|𝔪̂ − 𝔪| ≤ 1/128` (E.4(a)); a unit vector `h` supported on
the live coordinates with `xᵀh = 0` and `ℱ''[h, h] < −κ/2` (E.4(b),(c)); values of `ℱ` at `x ± t_* h`
to error `ξ_v = κt_*²/96` (E.4(d)). Every answer of Algorithm 3 is such an answer.
-/

/-- `ε = max_i ‖v_i‖²` (Section 9, p. 35). -/
def epsMax {n m : ℕ} (v : Fin n → Fin m → ℂ) : ℝ := ⨆ i, sqNorm (v i)

/-- `ρ = 1/(100n²)` (9.1). -/
def rho (n : ℕ) : ℝ := 1 / (100 * (n : ℝ) ^ 2)

/-- `t_o = ρ/16` (9.1). -/
def tOut (n : ℕ) : ℝ := rho n / 16

/-- `ζ = t_o/1000` (9.1). -/
def zeta (n : ℕ) : ℝ := tOut n / 1000

/-- `η = t_o ρ/100` (9.1). -/
def eta (n : ℕ) : ℝ := tOut n * rho n / 100

/-- `κ = 1/(2uDn · 128²)` with `u = 128`, `D = 2m` (9.1). -/
def kappa (n m : ℕ) : ℝ := 1 / (2 * 128 * (2 * (m : ℝ)) * n * 128 ^ 2)

/-- The profile of the walk: the smooth profile `c_ζ` with `u = 128`, `ζ = t_o/1000`. -/
def walkProfile (n : ℕ) : ℝ → ℝ := smoothProfile 128 (zeta n)

/-- The step size `t_* = min{r_0/2, κ/(8C_ℱ)}` of Lemma E.2, with `r_0`, `C_ℱ` of §E.3 (p. 60). -/
def tStar (n m : ℕ) (ε : ℝ) : ℝ :=
  let u : ℝ := 128
  let D : ℝ := 2 * (m : ℝ)
  let ζ := zeta n
  let cmin := u * rho n / 2
  let β1 := 3 * u / (2 * Real.sqrt cmin)
  let β2 := 3 * u / (2 * ζ * Real.sqrt cmin) + 9 * u ^ 2 / (4 * cmin ^ ((3 : ℝ) / 2))
  let β3 := 3 * u / (2 * ζ ^ 2 * Real.sqrt cmin) + 27 * u ^ 2 / (4 * ζ * cmin ^ ((3 : ℝ) / 2)) +
    81 * u ^ 3 / (8 * cmin ^ ((5 : ℝ) / 2))
  let MY := 8 * (n : ℝ) * (1 + β1 + β2 + β3)
  let δ0 := Real.sqrt (u * ε) / (4 * Real.sqrt D * (1 + 4 * D) ^ 2)
  let r0 := min (rho n / 4) (δ0 / (4 * MY))
  let CR := 2 / δ0
  let CF := 24 * CR ^ 5 * MY ^ 3 + 18 * CR ^ 4 * MY ^ 2 + 2 * CR ^ 3 * MY
  min (r0 / 2) (kappa n m / (8 * CF))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n m : ℕ}

/-- The invariant (9.2) at `(x, z)` for the total charge `C` paid so far: `z > λ₊(Y(x))`,
`ℱ(x, z) ≤ B` and `z ≤ z_0 + C`. -/
def Inv92 (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (ε : ℝ) (x : Fin n → ℝ) (z C : ℝ) : Prop :=
  edge c v s x < z ∧ potential c v s ω x z ≤ budget 128 ε ∧ z ≤ zStart 128 ε + C

/-- The Hilbert–Schmidt norm `‖M‖_HS = (Σ_{j,k} |M_{jk}|²)^{1/2}`. -/
def hsNorm (M : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  Real.sqrt (∑ j, ∑ k, Complex.normSq (M j k))

/-- One iteration of Algorithm 1 (lines 3–4) at coordinate `i`, on `(E_0, σ)`: a live `i` gets the
sign `s ∈ {1, −1}` minimizing `‖E_0 + (s − x_i) A_i‖_HS`, with `s = 1` on ties. -/
def roundStep (v : Fin n → Fin m → ℂ) (x : Fin n → ℝ)
    (st : Matrix (Fin m) (Fin m) ℂ × (Fin n → ℝ)) (i : Fin n) :
    Matrix (Fin m) (Fin m) ℂ × (Fin n → ℝ) :=
  if |x i| < 1 then
    let sgnI : ℝ :=
      if hsNorm (st.1 + (((1 : ℝ) - x i : ℝ) : ℂ) • rankOne (v i)) ≤
          hsNorm (st.1 + (((-1 : ℝ) - x i : ℝ) : ℂ) • rankOne (v i)) then 1 else -1
    (st.1 + ((sgnI - x i : ℝ) : ℂ) • rankOne (v i), Function.update st.2 i sgnI)
  else st

/-- Algorithm 1, `Round(x)` (p. 35): `E_0 ← 0`, `σ_i ← x_i` for frozen `i`, then the live coordinates
in increasing order. -/
def roundAlg (v : Fin n → Fin m → ℂ) (x : Fin n → ℝ) : Fin n → ℝ :=
  ((List.finRange n).foldl (roundStep v x) (0, x)).2

/-- The machine input of Algorithm 1: the layout of `weaverInput` followed by `x_1, …, x_n`. -/
def roundInput (n m : ℕ) (v : Fin n → Fin m → ℂ) (x : Fin n → ℝ) : List ℝ :=
  weaverInput n m v ++ MatMulTimeLP.vecToList x

/-- A configuration of Algorithm 2 at the head of its loop: the state `x`, the threshold `z`, and the
total charge paid so far. -/
abbrev WalkConf (n : ℕ) := (Fin n → ℝ) × ℝ × ℝ

/-- Lines 3–5 of Algorithm 2: every live `i` with `|x_i| ≥ 1 − ρ` is set to `sgn(x_i)`, and `z` and
the total charge rise by `ε(1 − |x_i|)` for each. -/
def boundaryRound (n : ℕ) (ε : ℝ) (cf : WalkConf n) : WalkConf n :=
  let Δ := ∑ i, if |cf.1 i| < 1 ∧ 1 - rho n ≤ |cf.1 i| then ε * (1 - |cf.1 i|) else 0
  (fun i => if |cf.1 i| < 1 ∧ 1 - rho n ≤ |cf.1 i| then sgn (cf.1 i) else cf.1 i,
    cf.2.1 + Δ, cf.2.2 + Δ)

/-- The outward secant `ℓ_i = (c(x_i) − c(x_i + sgn(x_i) t_o))/t_o` of the walk profile. -/
def secant (n : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (walkProfile n (x i) - walkProfile n (x i + sgn (x i) * tOut n)) / tOut n

/-- One pass through the loop of Algorithm 2 (p. 37), with oracle answers meeting the tolerances of
Proposition E.4: from the configuration `cf`, the pass may end in the configuration or the returned
signs `out`. -/
def WalkPass (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (cf : WalkConf n) (out : WalkConf n ⊕ (Fin n → ℝ)) : Prop :=
  let ε := epsMax v
  let c := walkProfile n
  let b := boundaryRound n ε cf
  let x := b.1
  let z := b.2.1
  let ch := b.2.2
  if ¬ ∃ i, |x i| < 1 then out = Sum.inr x
  else
    ∃ qhat : Fin n → ℝ,
      (∀ i, |x i| < 1 → |qhat i - qCoef c v s ω x z i| ≤ eta n / (12 * 128)) ∧
      |(∑ i, if |x i| < 1 then c (x i) * qhat i ^ 2 else 0) - mass c v s ω x z| ≤ 1 / 128 ∧
      ((∃ i, |x i| < 1 ∧ 1 - eta n / 2 ≤ secant n x i * qhat i) →
        ∃ i, (|x i| < 1 ∧ 1 - eta n / 2 ≤ secant n x i * qhat i) ∧
          (∀ j, j < i → ¬ (|x j| < 1 ∧ 1 - eta n / 2 ≤ secant n x j * qhat j)) ∧
          out = Sum.inl (Function.update x i (x i + sgn (x i) * tOut n),
            z + tOut n * eta n * ε, ch + tOut n * eta n * ε)) ∧
      ((¬ ∃ i, |x i| < 1 ∧ 1 - eta n / 2 ≤ secant n x i * qhat i) →
        (∑ i, if |x i| < 1 then c (x i) * qhat i ^ 2 else 0) ≤ 9 / 128 →
        out = Sum.inr (roundAlg v x)) ∧
      ((¬ ∃ i, |x i| < 1 ∧ 1 - eta n / 2 ≤ secant n x i * qhat i) →
        ¬ (∑ i, if |x i| < 1 then c (x i) * qhat i ^ 2 else 0) ≤ 9 / 128 →
        ∃ (h : Fin n → ℝ) (Fp Fm : ℝ),
          ∑ i, h i ^ 2 = 1 ∧ (∀ i, ¬ |x i| < 1 → h i = 0) ∧ ∑ i, x i * h i = 0 ∧
          secondVar c v s ω x z h < -(kappa n m) / 2 ∧
          |Fp - potential c v s ω (x + tStar n m ε • h) z| ≤ kappa n m * tStar n m ε ^ 2 / 96 ∧
          |Fm - potential c v s ω (x - tStar n m ε • h) z| ≤ kappa n m * tStar n m ε ^ 2 / 96 ∧
          out = Sum.inl (if Fp ≤ Fm then x + tStar n m ε • h else x - tStar n m ε • h, z, ch))

/-- `WalkReach v s ω k cf`: some run of Algorithm 2 (with admissible oracle answers) is at the
configuration `cf` at the head of its loop after `k` passes; the run starts at
`(x, z, charge) = (0, z_0, 0)` (line 1). -/
inductive WalkReach (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H) :
    ℕ → WalkConf n → Prop
  | init : WalkReach v s ω 0 (0, zStart 128 (epsMax v), 0)
  | step {k : ℕ} {cf cf' : WalkConf n} :
      WalkReach v s ω k cf → WalkPass v s ω cf (Sum.inl cf') → WalkReach v s ω (k + 1) cf'

end

end FreeWeaver.Walk


