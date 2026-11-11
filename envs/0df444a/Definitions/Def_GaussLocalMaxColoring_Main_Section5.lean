-- Prove2me | Definitions.Def_GaussLocalMaxColoring_Main_Section5
-- name    : GaussLocalMaxColoring_Main_Section5
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:21:02.537456+00:00
-- url     : https://prove2.me/theorems/e7a3acbb-5cb9-4e89-a1f2-0d79d8dace3e
-- title:
--   Table 3, the capacity $C_D(\rho)$, the thresholds $q_c, f_A, q_A$, $\varepsilon_t$, the events $\mathcal G_i(r),\mathcal L_i(r)$, and the conditions of Lemma 40
-- statement:
--   **Table 3** (all functions of $n$): $\beta=0.692601$, $\eta=10^{-6}$, $\delta=n^{-(1-\beta)/2}$, $T=\lceil n\delta/(100\ell^4)\rceil$, $R=\lceil32\delta^{-2}\log(8n\ell)\rceil$, $t=\sqrt{(1-\beta)\log n}$, $H_0=2/(1-\beta)$, $D=2\beta/(1-\beta)$, $D_a=D+3\eta$, $H=H_0+3\eta$, $w=\log t/t^2$, $A_0=\sqrt{D_a+1/4}$, $A_i=\max\{1.968,A_0-iw\}$, $m_0=\lceil(A_0-1.968)/w\rceil$, $U_0=3/(2\sqrt2)$, $U_i=U_0+i/3000$; $\varepsilon_t=\exp(-(1/4+\eta)t^2/2)$.
--
--   **Definition 36.** $C_D(\rho)=\min\{D+2,\tfrac12(1+\sqrt{1+6D(D+1)\tfrac{1-2\rho}{1-4\rho}})\}$ on $[-\tfrac12,0]$, $\min\{D+2,\tfrac12(1+\sqrt{1+\tfrac{6D(D+1)}{1+2\rho}})\}$ on $[0,\tfrac14]$, $D+1$ on $(\tfrac14,1]$.
--
--   **§5.4.1.** $q_c(\rho)=\sqrt{(1-\rho^2)(C_{D_a}(\rho)+1/4)}$; $f_A(\rho)=\tilde f(A)\sqrt{1-\rho^2}-0.714\zeta_1+0.826\zeta_1^2-0.8\zeta_2+0.45\zeta_2^2+0.39\zeta_3+0.65\zeta_3^2$ with $\tilde f(A)=2.466+0.52(A-2)+2.46(A-2)^2$, $\zeta_1=(-\tfrac1{40}-\rho)_+$, $\zeta_2=(\rho-\tfrac1{50})_+$, $\zeta_3=(\rho-\tfrac14)_+$; $q_A=\min\{q_c,f_A\}$.
--
--   **Events** (p. 40), for a core sequence $(F_i)$ and a root $r$: $\mathcal G_i(r)=\{\exists x\in F_{i+1}:|\langle g,u_x\rangle|>q_{A_i}(\rho_x)t\}$, $\mathcal L_i(r)=\{M_{F_{i+1}}(r)>A_it\}$.
--
--   **Lemma 40's conditions** for $(a,b,\mu,c,\kappa,\theta)$ and entries $(L,J,\Lambda)$: (i) $a,\mu,c,\kappa\ge0$, $0<\theta<14$; (ii) $a^2+b^2+\mu^2\le1-10^{-12}$, $c^2+\kappa^2\le\tfrac14-10^{-20}$; (iii) $L^2+\Lambda(\mu+\theta(\mu+\kappa))^2\ge J+10^{-18}$; (iv) for every $\rho'$ with $-\tfrac12\le\rho'\le\tfrac12-\rho$ and $\tfrac34-\rho^2-\rho'^2-\rho\rho'\ge0$: $\frac{L(1/2+\rho\rho')-(1+\theta)b(\rho'+\rho/2)+\theta c|\rho'+\rho/2|}{\sqrt{1-\rho^2}}+\tfrac32(1+\theta)a-\tfrac{\sqrt3}2\theta A\ge q_A(\rho')+3\cdot10^{-6}$. Case 1: $L=q_A(\rho)/\sqrt{1-\rho^2}$, $J=C_{D_a}(\rho)+\tfrac14$, $\Lambda=1$. Case 2 ($\rho=-\tfrac12$): $L=A$, $J=D_a+\tfrac14$, $\Lambda=3999/1000$.
--
--   The **maximizer of $M_F(x)$** is the $y\in N_F(x)$ maximizing $\langle g,v_{xy}\rangle$, ties broken by the vertex order (least index).
--
--   **Formalization Note.** Constants are exact rationals ($1.968=1968/1000$). $C_D$ is written with the first formula for $\rho\le0$; values outside $[-1/2,1]$ are never used. The maximizer is taken only on $\{M_F(x)>At\}$, where $N_F(x)\neq\emptyset$.
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Table 3 (p. 31, PDF 33), Definition 36 (p. 38, PDF 40), p. 40 (PDF 42), §5.4.1 and Lemma 40 (pp. 41–42, PDF 43–44), Lemma 42 (ii) (p. 43, PDF 45)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Basic

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical
noncomputable section

namespace GaussLocalMaxColoring.Main

/-! # Section 5: Table 3, the capacity `C_D` (Definition 36), the thresholds `q_c, f_A, q_A`
(§5.4.1), `ε_t`, the global and local events `𝒢_i(r), ℒ_i(r)`, and the conditions of Lemma 40

Deguchi–Kawarabayashi–Yoneda–Yoneda, arXiv:2610.35859, Table 3 (p. 31, PDF 33),
Definition 36 (p. 38, PDF 40), p. 40 (PDF 42), §5.4.1 (pp. 41–42, PDF 43–44).

All Table 3 parameters are functions of the number of vertices `n`; `β = 0.692601` exactly.
`H₀ = 2/(1−β)` and `D = 2β/(1−β)` are the constants defined by `n = e^{H₀t²/2}`,
`n^β = e^{Dt²/2}` with `t = √((1−β) log n)`. -/

variable {n d : ℕ}

/-- `β = 0.692601` (Theorem 5, Table 3). -/
def beta5 : ℝ := 692601 / 1000000

/-- `η = 10⁻⁶` (Table 3). -/
def eta5 : ℝ := 1 / 1000000

/-- `δ = n^{−(1−β)/2}` (Table 3). -/
def delta5 (n : ℕ) : ℝ := (n : ℝ) ^ (-((1 - beta5) / 2))

/-- `T = ⌈nδ/(100ℓ⁴)⌉` (Table 3). -/
def target5 (n : ℕ) : ℕ := ⌈(n : ℝ) * delta5 n / (100 * (numLevels n : ℝ) ^ 4)⌉₊

/-- `R = ⌈32 δ^{−2} log(8nℓ)⌉` (Table 3). -/
def runs5 (n : ℕ) : ℕ := ⌈32 * (delta5 n)⁻¹ ^ 2 * Real.log (8 * n * (numLevels n : ℝ))⌉₊

/-- `t = √(2 log(1/δ)) = √((1−β) log n)` (Table 3). -/
def t5 (n : ℕ) : ℝ := Real.sqrt ((1 - beta5) * Real.log n)

/-- `H₀ = 2/(1−β)` (Table 3). -/
def H0 : ℝ := 2 / (1 - beta5)

/-- `D = 2β/(1−β)` (Table 3). -/
def D5 : ℝ := 2 * beta5 / (1 - beta5)

/-- `D_a = D + 3η` (Table 3). -/
def Da : ℝ := D5 + 3 * eta5

/-- `H = H₀ + 3η` (Table 3). -/
def H5 : ℝ := H0 + 3 * eta5

/-- `w = log t / t²` (Table 3). -/
def w5 (n : ℕ) : ℝ := Real.log (t5 n) / t5 n ^ 2

/-- `A₀ = √(D_a + 1/4)` (p. 31). -/
def A0 : ℝ := Real.sqrt (Da + 1 / 4)

/-- `A_i = max{1.968, A₀ − i w}` (Table 3). -/
def Ai (n i : ℕ) : ℝ := max (1968 / 1000) (A0 - i * w5 n)

/-- `m₀ = ⌈(A₀ − 1.968)/w⌉` (Table 3). -/
def m0 (n : ℕ) : ℕ := ⌈(A0 - 1968 / 1000) / w5 n⌉₊

/-- `U₀ = 3/(2√2)` (§4, p. 14, kept in §5). -/
def U0 : ℝ := 3 / (2 * Real.sqrt 2)

/-- `U_i = U₀ + i/3000` (Table 3). -/
def Ui (i : ℕ) : ℝ := U0 + i / 3000

/-- `ε_t = exp(−(1/4 + η) t²/2)` (p. 40). -/
def epsT (n : ℕ) : ℝ := Real.exp (-((1 / 4 + eta5) * t5 n ^ 2 / 2))

/-- **Definition 36** (capacity), for `ρ ∈ [−1/2, 1]`:
`min{D+2, ½(1 + √(1 + 6D(D+1)(1−2ρ)/(1−4ρ)))}` on `[−1/2, 0]`,
`min{D+2, ½(1 + √(1 + 6D(D+1)/(1+2ρ)))}` on `[0, 1/4]`, and `D + 1` on `(1/4, 1]`
(the two formulas agree at `ρ = 0`). -/
def capacity (D ρ : ℝ) : ℝ :=
  if ρ ≤ 0 then
    min (D + 2) ((1 + Real.sqrt (1 + 6 * D * (D + 1) * ((1 - 2 * ρ) / (1 - 4 * ρ)))) / 2)
  else if ρ ≤ 1 / 4 then
    min (D + 2) ((1 + Real.sqrt (1 + 6 * D * (D + 1) / (1 + 2 * ρ))) / 2)
  else D + 1

/-- `q_c(ρ) = √((1−ρ²)(C_{D_a}(ρ) + 1/4))` (§5.4.1). -/
def qc (ρ : ℝ) : ℝ := Real.sqrt ((1 - ρ ^ 2) * (capacity Da ρ + 1 / 4))

/-- `f̃(A) = 2.466 + 0.52(A−2) + 2.46(A−2)²` (§5.4.1). -/
def ftilde (A : ℝ) : ℝ := 2466 / 1000 + 52 / 100 * (A - 2) + 246 / 100 * (A - 2) ^ 2

/-- `f_A(ρ) = f̃(A)√(1−ρ²) − 0.714ζ₁ + 0.826ζ₁² − 0.8ζ₂ + 0.45ζ₂² + 0.39ζ₃ + 0.65ζ₃²` with
`ζ₁ = (−1/40 − ρ)₊`, `ζ₂ = (ρ − 1/50)₊`, `ζ₃ = (ρ − 1/4)₊` (§5.4.1, rendered p. 41). -/
def fA (A ρ : ℝ) : ℝ :=
  let z1 := max (-(1 / 40) - ρ) 0
  let z2 := max (ρ - 1 / 50) 0
  let z3 := max (ρ - 1 / 4) 0
  ftilde A * Real.sqrt (1 - ρ ^ 2) - 714 / 1000 * z1 + 826 / 1000 * z1 ^ 2
    - 8 / 10 * z2 + 45 / 100 * z2 ^ 2 + 39 / 100 * z3 + 65 / 100 * z3 ^ 2

/-- `q_A(ρ) = min{q_c(ρ), f_A(ρ)}` (§5.4.1). -/
def qA (A ρ : ℝ) : ℝ := min (qc ρ) (fA A ρ)

/-- The global event `𝒢_i(r) = {∃ x ∈ F_{i+1} : |⟨g, u_x⟩| > q_{A_i}(ρ_x) t}` (p. 40), for a
core sequence `F` and root `r`. -/
def globalEvent (v : Fin n → Space d) (F : ℕ → Finset (Fin n)) (r : Fin n) (i : ℕ) :
    Set (Space d) :=
  {g | ∃ x ∈ F (i + 1), qA (Ai n i) (rho v r x) * t5 n < |⟪g, uvec v r x⟫|}

/-- The local event `ℒ_i(r) = {M_{F_{i+1}}(r) > A_i t}` (p. 40). -/
def localEvent (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (F : ℕ → Finset (Fin n))
    (r : Fin n) (i : ℕ) : Set (Space d) :=
  {g | ((Ai n i * t5 n : ℝ) : WithBot ℝ) < nbrMax G v (F (i + 1)) r g}

/-- The left-hand side of Lemma 40 (iv), for the entries `L` and the parameters. -/
def l40Lhs (A ρ L a b c θ ρ' : ℝ) : ℝ :=
  (L * (1 / 2 + ρ * ρ') - (1 + θ) * b * (ρ' + ρ / 2) + θ * c * |ρ' + ρ / 2|) /
      Real.sqrt (1 - ρ ^ 2)
    + 3 / 2 * (1 + θ) * a - Real.sqrt 3 / 2 * θ * A

/-- Conditions (i)–(iv) of **Lemma 40** for the parameters `(a, b, μ, c, κ, θ)`, the threshold
parameter `A`, the correlation `ρ` and the table entries `(L, J, Λ)`. -/
def L40Conds (A ρ L J Λ a b μ c κ θ : ℝ) : Prop :=
  (0 ≤ a ∧ 0 ≤ μ ∧ 0 ≤ c ∧ 0 ≤ κ ∧ 0 < θ ∧ θ < 14) ∧
  (a ^ 2 + b ^ 2 + μ ^ 2 ≤ 1 - 1 / 10 ^ 12 ∧ c ^ 2 + κ ^ 2 ≤ 1 / 4 - 1 / 10 ^ 20) ∧
  (L ^ 2 + Λ * (μ + θ * (μ + κ)) ^ 2 ≥ J + 1 / 10 ^ 18) ∧
  (∀ ρ' : ℝ, -(1 / 2) ≤ ρ' → ρ' ≤ 1 / 2 - ρ → 0 ≤ 3 / 4 - ρ ^ 2 - ρ' ^ 2 - ρ * ρ' →
    l40Lhs A ρ L a b c θ ρ' ≥ qA A ρ' + 3 / 10 ^ 6)

/-- Lemma 40, Case 1 entries: `L = q_A(ρ)/√(1−ρ²)`, `J = C_{D_a}(ρ) + 1/4`, `Λ = 1`. -/
def L40Case1 (A ρ a b μ c κ θ : ℝ) : Prop :=
  L40Conds A ρ (qA A ρ / Real.sqrt (1 - ρ ^ 2)) (capacity Da ρ + 1 / 4) 1 a b μ c κ θ

/-- Lemma 40, Case 2 entries (`ρ = −1/2`): `L = A`, `J = D_a + 1/4`, `Λ = 3999/1000`. -/
def L40Case2 (A a b μ c κ θ : ℝ) : Prop :=
  L40Conds A (-(1 / 2)) A (Da + 1 / 4) (3999 / 1000) a b μ c κ θ

/-- The maximizer of `M_F(x)` (p. 43, Lemma 42 (ii)): the vertex `y ∈ N_F(x)` maximizing
`⟨g, v_xy⟩`, ties broken by the order of `Fin n` (the least maximizer); `x` itself when
`N_F(x) = ∅` (never used: the maximizer is only taken on `{M_F(x) > A t}`). -/
def nbrArgmax (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n)
    (g : Space d) : Fin n :=
  if h : ((nbr G F x).filter fun y => ∀ z ∈ nbr G F x,
      ⟪g, residual v x z⟫ ≤ ⟪g, residual v x y⟫).Nonempty then
    ((nbr G F x).filter fun y => ∀ z ∈ nbr G F x,
      ⟪g, residual v x z⟫ ≤ ⟪g, residual v x y⟫).min' h
  else x

end GaussLocalMaxColoring.Main


