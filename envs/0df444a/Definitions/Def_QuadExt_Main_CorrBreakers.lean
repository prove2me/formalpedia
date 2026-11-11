-- Prove2me | Definitions.Def_QuadExt_Main_CorrBreakers
-- name    : QuadExt_Main_CorrBreakers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:03:57.234376+00:00
-- url     : https://prove2.me/theorems/5a975262-147d-417a-8ea4-9eeebf51ad4f
-- title:
--   Advice correlation breakers (Def. 4.4), quadratic correlation breakers (Def. 7.1) and Algorithm 1 (QuadCB)
-- statement:
--   **Advice correlation breaker (Definition 4.4).** $\mathrm{CB} : \{0,1\}^n \times \{0,1\}^d \times \{0,1\}^a \to \{0,1\}^m$ is a $(t, k, \varepsilon)$-advice correlation breaker if for all random variables $X, X^{[t]} = (X_1, \dots, X_t), Y, Y^{[t]}$ and advice strings $\alpha, \alpha_1, \dots, \alpha_t$ with (1) $H_\infty(X) \ge k$, (2) $Y = U_d$, (3) $(X, X^{[t]})$ independent of $(Y, Y^{[t]})$, (4) $\alpha \ne \alpha_i$ for all $i$,
--   $$\big(\mathrm{CB}(X, Y, \alpha) \approx_\varepsilon U_m\big) \mid \{\mathrm{CB}(X_i, Y_i, \alpha_i)\}_{i \in [t]}. \qquad (4)$$
--
--   **Quadratic correlation breaker (Definition 7.1).** $\mathrm{QuadCB} : \mathbb F_2^n \times \mathbb F_2^d \times \{0,1\}^a \to \{0,1\}^m$ is a $(t, k, q, \delta)$-quadratic correlation breaker (with absolute constant $c > 0$) if for all $X, W, W^{[t]}$ and advice strings with (1) $X = f(V)$ a $q$-pure quadratic source with $H_\infty(X) \ge k$, $V = U_s$ and $s \le k + c \log_2(1/\delta)$, (2) $W = p(V)$, $W^i = p_i(V)$ for quadratic $p, p_1, \dots, p_t : \mathbb F_2^s \to \mathbb F_2^d$, (3) $W = U_d$, (4) $\alpha \ne \alpha_i$:
--   $$\big(\mathrm{QuadCB}(X, W, \alpha) \approx_\delta U_m\big) \mid \{\mathrm{QuadCB}(X, W^i, \alpha^i)\}_{i \in [t]}. \qquad (5)$$
--   The **relaxed** version (the "Moreover" of Theorem 7.2) replaces Item 1's $H_\infty(X) \ge k$ by $H^{\eta_X}_\infty(X) \ge k$ and Item 3's $W = U_d$ by $W \approx_{\eta_W} U_d$.
--
--   **Algorithm 1 (QuadCB).** Given a linear seeded extractor $\mathrm{LExt} : \{0,1\}^n \times \{0,1\}^{d_0} \to \{0,1\}^{d_1}$ and an advice correlation breaker $\mathrm{CB} : \{0,1\}^d \times \{0,1\}^{d_1} \times \{0,1\}^a \to \{0,1\}^m$, on input $(x, w, \alpha)$: $s_1 = w_{[d_0]}$ (the first $d_0$ bits of $w$), $r = \mathrm{LExt}(x, s_1)$, output $\mathrm{CB}(w, r, \alpha)$. Its parameters are $d_1 = O(t(m + t \log a \log(n/\delta)))$ and $d_0 = O(d_1 + \log(1/\delta))$ (`Alg1Params A₀ A₁`, the two $O(\cdot)$ constants being $A_1$, $A_0$).
--
--   **Formalization Note.** All strings are `Fin _ → ZMod 2`. A tuple $X^{[t]}$ is one random element of `Fin t → 𝔽₂^n`; the joint laws of $(X, X^{[t]})$ and $(Y, Y^{[t]})$ are arbitrary and the two are independent (`indepPair`). The absolute constant $c$ of Definition 7.1 is a parameter of `IsQuadCB` and statements quantify $\exists c > 0$ before all other parameters. `alg1` takes the sub-routines `LExt`, `CB` and a proof of $d_0 \le d$ (needed for $w_{[d_0]}$ to exist) as arguments. Logarithms are base 2.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 14 (PDF 15), Definition 4.4; p. 20 (PDF 21), Definition 7.1; p. 21 (PDF 22), Algorithm 1 and Theorem 7.2 ('Moreover')

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_QuadExt_Main_Closeness
import Definitions.Def_QuadExt_Main_Pure

namespace QuadExt.Main

/-!
# Advice correlation breakers, quadratic correlation breakers, and Algorithm 1 (QuadCB)

Chandrasekaran, Goodman, Zuckerman, *Quadratic Extractors*, STOC 2027 submission (manuscript
sha256 ddc80a9a…): Definition 4.4, p. 14 (PDF 15); Definition 7.1, p. 20 (PDF 21); the relaxation
in the "Moreover" sentence of Theorem 7.2, p. 21 (PDF 22); Algorithm 1, p. 21 (PDF 22).

Bit strings (sources, seeds, advice strings, outputs) are `Fin _ → ZMod 2`. A tuple `X^{[t]}` of
`t` random strings is one random element of `Fin t → (Fin n → ZMod 2)`.
-/

/-- A **`(t, k, ε)`-advice correlation breaker** `CB : {0,1}^n × {0,1}^d × {0,1}^a → {0,1}^m`
(Definition 4.4): for all jointly distributed `(X, X^{[t]})` and `(Y, Y^{[t]})`, the two tuples
independent of each other, with `H_∞(X) ≥ k` and `Y = U_d`, and all advice strings with `α ≠ α_i`
for every `i`, `(CB(X, Y, α) ≈_ε U_m) | {CB(X_i, Y_i, α_i)}_{i∈[t]}` (Equation (4)). -/
def IsAdviceCB {n d a m : ℕ} (t : ℕ) (k ε : ℝ)
    (CB : (Fin n → ZMod 2) → (Fin d → ZMod 2) → (Fin a → ZMod 2) → (Fin m → ZMod 2)) : Prop :=
  ∀ (μX : PMF ((Fin n → ZMod 2) × (Fin t → Fin n → ZMod 2)))
    (μY : PMF ((Fin d → ZMod 2) × (Fin t → Fin d → ZMod 2)))
    (α : Fin a → ZMod 2) (αs : Fin t → Fin a → ZMod 2),
    k ≤ SSNonExt.minEntropy (μX.map Prod.fst) →
    μY.map Prod.fst = PMF.uniformOfFintype (Fin d → ZMod 2) →
    (∀ i, α ≠ αs i) →
    CondCloseUnif ε ((indepPair μX μY).map fun p =>
      (CB p.1.1 p.2.1 α, fun i => CB (p.1.2 i) (p.2.2 i) (αs i)))

/-- A **`(t, k, q, δ)`-quadratic correlation breaker** (Definition 7.1), with the definition's
absolute constant `c` as an explicit parameter (statements quantify `∃ c > 0` before every other
parameter). For every `s`, every quadratic `q`-pure generating map `f : 𝔽₂^s → 𝔽₂^n` with
`H_∞(f(V)) ≥ k` and `s ≤ k + c·log₂(1/δ)` (Item 1), all quadratic `p, p_1, …, p_t : 𝔽₂^s → 𝔽₂^d`
(Item 2) with `W = p(V)` uniform (Item 3), where `V = U_s`, and all advice strings with `α ≠ α_i`
(Item 4): `(QuadCB(X, W, α) ≈_δ U_m) | {QuadCB(X, W^i, α^i)}_{i∈[t]}` (Equation (5)), where
`X = f(V)`, `W^i = p_i(V)`. -/
def IsQuadCB {n d a m : ℕ} (c : ℝ) (t : ℕ) (k q δ : ℝ)
    (QuadCB : (Fin n → ZMod 2) → (Fin d → ZMod 2) → (Fin a → ZMod 2) → (Fin m → ZMod 2)) : Prop :=
  ∀ (s : ℕ) (f : (Fin s → ZMod 2) → (Fin n → ZMod 2)) (p : (Fin s → ZMod 2) → (Fin d → ZMod 2))
    (ps : Fin t → (Fin s → ZMod 2) → (Fin d → ZMod 2))
    (α : Fin a → ZMod 2) (αs : Fin t → Fin a → ZMod 2),
    IsQuadraticMap f → IsPure q f → k ≤ SSNonExt.minEntropy (source f) →
    (s : ℝ) ≤ k + c * Real.logb 2 (1 / δ) →
    IsQuadraticMap p → (∀ i, IsQuadraticMap (ps i)) →
    source p = PMF.uniformOfFintype (Fin d → ZMod 2) →
    (∀ i, α ≠ αs i) →
    CondCloseUnif δ ((unif (Fin s)).map fun v =>
      (QuadCB (f v) (p v) α, fun i => QuadCB (f v) (ps i v) (αs i)))

/-- Definition 7.1 with Items 1 and 3 **relaxed** as in the "Moreover" sentence of Theorem 7.2:
`H^{ηX}_∞(X) ≥ k` instead of `H_∞(X) ≥ k`, and `W ≈_{ηW} U_d` instead of `W = U_d`; everything else,
including `s ≤ k + c·log₂(1/δ)` and the error `δ` in Equation (5), as in `IsQuadCB`. -/
def IsQuadCBRelaxed {n d a m : ℕ} (c : ℝ) (t : ℕ) (k q δ ηX ηW : ℝ)
    (QuadCB : (Fin n → ZMod 2) → (Fin d → ZMod 2) → (Fin a → ZMod 2) → (Fin m → ZMod 2)) : Prop :=
  ∀ (s : ℕ) (f : (Fin s → ZMod 2) → (Fin n → ZMod 2)) (p : (Fin s → ZMod 2) → (Fin d → ZMod 2))
    (ps : Fin t → (Fin s → ZMod 2) → (Fin d → ZMod 2))
    (α : Fin a → ZMod 2) (αs : Fin t → Fin a → ZMod 2),
    IsQuadraticMap f → IsPure q f → SmoothMinEntropyGE ηX (source f) k →
    (s : ℝ) ≤ k + c * Real.logb 2 (1 / δ) →
    IsQuadraticMap p → (∀ i, IsQuadraticMap (ps i)) →
    SSNonExt.TV (source p) (PMF.uniformOfFintype (Fin d → ZMod 2)) ≤ ηW →
    (∀ i, α ≠ αs i) →
    CondCloseUnif δ ((unif (Fin s)).map fun v =>
      (QuadCB (f v) (p v) α, fun i => QuadCB (f v) (ps i v) (αs i)))

/-- **Algorithm 1 (QuadCB)**, p. 21 (PDF 22), with its two sub-routines as parameters: on input
`x ∈ {0,1}^n`, seed `w ∈ {0,1}^d` and advice `α ∈ {0,1}^a`,
`s₁ = w_{[d₀]}` (the first `d₀` bits of `w`), `r = LExt(x, s₁)`, output `CB(w, r, α)`.
`h : d₀ ≤ d` is needed for `w_{[d₀]}` to exist. -/
def alg1 {n d d0 d1 a m : ℕ} (h : d0 ≤ d)
    (LExt : (Fin n → ZMod 2) → (Fin d0 → ZMod 2) → (Fin d1 → ZMod 2))
    (CB : (Fin d → ZMod 2) → (Fin d1 → ZMod 2) → (Fin a → ZMod 2) → (Fin m → ZMod 2)) :
    (Fin n → ZMod 2) → (Fin d → ZMod 2) → (Fin a → ZMod 2) → (Fin m → ZMod 2) :=
  fun x w α => CB w (LExt x (fun j => w (Fin.castLE h j))) α

/-- The **parameters of Algorithm 1** (p. 21): `d₁ = O(t(m + t·log a·log(n/δ)))` and
`d₀ = O(d₁ + log(1/δ))`, the `O(·)` constants being `A₁` and `A₀`; logarithms base 2. -/
def Alg1Params (A₀ A₁ δ : ℝ) (t a m n d0 d1 : ℕ) : Prop :=
  (d1 : ℝ) ≤ A₁ * t * (m + t * Real.logb 2 a * Real.logb 2 (n / δ)) ∧
  (d0 : ℝ) ≤ A₀ * (d1 + Real.logb 2 (1 / δ))

end QuadExt.Main


