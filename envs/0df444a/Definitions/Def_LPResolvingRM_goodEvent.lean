-- Prove2me | Definitions.Def_LPResolvingRM_goodEvent
-- name    : LPResolvingRM_goodEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:43:25.43188+00:00
-- url     : https://prove2.me/theorems/66cb07f1-ce3b-4f28-97e5-5b1821ce7481
-- title:
--   The good event $\mathcal E_t$, the frozen process $\tilde b_t$, the constants $\kappa$, $T_1$, and the events $\mathcal A^{(j)}_t$, $\mathcal B^{(j)}_t$
-- statement:
--   Let $\underline b=\min_ib_i$, $\kappa=(1-e^{-L/8})\wedge(1-e^{-L/(8(1+L-\underline b))})$, and
--   $$\epsilon^*_t=\begin{cases}1&t\le\kappa T\\ t^{-1/4}&t>\kappa T\end{cases},\qquad \epsilon'_t=\begin{cases}1+L-\underline b&t\le\kappa T\\ t^{-1/4}&t>\kappa T.\end{cases}$$
--   The **good event** is
--   $$\mathcal E_t:=\Big\{\mathcal H_{t-1}\ \Big|\ \sup_{b'\in\mathfrak B}\big\|\mathbb E[a_{\mathcal I^*,t}x_t(b')|\mathcal H_{t-1}]-b'_{\mathcal I^*}\big\|_\infty\le\epsilon^*_{t-1}\text{ and }\sup_{b'\in\mathfrak B}\mathbb E[a_{\mathcal I',t}x_t(b')|\mathcal H_{t-1}]-b'_{\mathcal I'}\le\epsilon'_{t-1}\Big\},$$
--   where $x_t(b')$ is the decision of Algorithm 1 at period $t$ when $b_t=b'$; given the history, $\mathbb E[a_tx_t(b')|\mathcal H_{t-1}]=\sum_jp_jc_jy_{j,t}(b')$. Further, $\tilde\tau:=\min\{t\le T:b_t\notin\mathfrak B\text{ or }\mathcal H_{t-1}\notin\mathcal E_t\}\cup\{T+1\}$, the **frozen process** $\tilde b_t=b_t$ for $t<\tilde\tau$ and $b_{\tilde\tau}$ for $t\ge\tilde\tau$, $T_1$ is the minimal integer with $T_1\ge(\frac1{e^{L/8}-1}+2)\vee(\frac1{e^{L/(8(1+L-\underline b))}-1}+2)$ and $\frac{\log T_1}{T_1^{1/4}}\le\frac{\kappa^{1/4}L}4$, and for $t\ge2$
--   $$\mathcal A^{(j)}_t=\Big\{\Big|\tfrac{n_j(t-1)}{t-1}-p_j\Big|\le L\Big\},\qquad\mathcal B^{(j)}_t=\Big\{\Big|\tfrac{n_j(t-1)}{t-1}-p_j\Big|\le\tfrac1{n(t-1)^{1/4}}\Big\},$$
--   both the whole space at $t=1$.
--
--   **Formalization Note** The suprema over the unbounded $\mathfrak B$ are "for all $b'\in\mathfrak B$". $\kappa T$ enters as $\lfloor\kappa T\rfloor$ (p.12 assumes it is an integer); comparisons $t\le\kappa T$ are unchanged for integer $t$. $T_1$ is the infimum of a nonempty set of naturals when $\kappa>0$.
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Appendix C.1, pp.35–36; pp.14, 36

import Definitions.Def_LPResolvingRM_tauS

open scoped Classical

namespace LPResolvingRM

/-- `b̲ := min{b₁, …, b_m}` (arXiv:2101.11092v3, Appendix C.1, p.35).

**Formalization Note.** An infimum over `Fin m`; it is the minimum for `m ≥ 1`, which every
statement using it assumes. -/
noncomputable def bmin {n m : ℕ} (I : Instance n m) : ℝ := ⨅ i : Fin m, I.b i

/-- **The constant `κ`** of Lemma 12 (arXiv:2101.11092v3, p.36):
`κ = (1 − exp(−L/8)) ∧ (1 − exp(−L/(8(1 + L − b̲))))`. It lies in `(0, 1)` when `L > 0` and
`1 + L − b̲ > 0`. -/
noncomputable def kappa {n m : ℕ} (I : Instance n m) (L : ℝ) : ℝ :=
  min (1 - Real.exp (-(L / 8))) (1 - Real.exp (-(L / (8 * (1 + L - bmin I)))))

/-- **The threshold `κT`** as an integer: `⌊κT⌋` (arXiv:2101.11092v3, p.12: "Without loss of
generality, we assume κT takes an integer value").

**Formalization Note.** For an integer `t`, `t ≤ κT` iff `t ≤ ⌊κT⌋`, so the case splits at `κT`
are unchanged; where `κT` enters a formula as a number (Lemmas 11 and 13) the integer `⌊κT⌋`
is used, which equals `κT` in the case the paper treats. -/
noncomputable def kT {n m : ℕ} (I : Instance n m) (L : ℝ) (T : ℕ) : ℕ :=
  ⌊kappa I L * T⌋₊

/-- **The tolerance `ϵ*_t`** for the binding coordinates (arXiv:2101.11092v3, p.35):
`ϵ*_t := 1` for `t ≤ κT` and `1/t^{1/4}` for `t > κT`. -/
noncomputable def epsStar {n m : ℕ} (I : Instance n m) (L : ℝ) (T t : ℕ) : ℝ :=
  if t ≤ kT I L T then 1 else 1 / (t : ℝ) ^ (1 / 4 : ℝ)

/-- **The tolerance `ϵ'_t`** for the non-binding coordinates (arXiv:2101.11092v3, p.35):
`ϵ'_t := 1 + L − b̲` for `t ≤ κT` and `1/t^{1/4}` for `t > κT`. -/
noncomputable def epsPrime {n m : ℕ} (I : Instance n m) (L : ℝ) (T t : ℕ) : ℝ :=
  if t ≤ kT I L T then 1 + L - bmin I else 1 / (t : ℝ) ^ (1 / 4 : ℝ)

/-- **The good event `𝓔_t`** (arXiv:2101.11092v3, Appendix C.1, p.35):
`𝓔_t := {H_{t−1} | sup_{b'∈𝔅} ‖E[a_{I*,t}x_t(b')|H_{t−1}] − b'_{I*}‖_∞ ≤ ϵ*_{t−1} and
sup_{b'∈𝔅} E[a_{I',t}x_t(b')|H_{t−1}] − b'_{I'} ≤ ϵ'_{t−1}}`, where `x_t(b')` is the decision of
Algorithm 1 at period `t` when `b_t = b'`.

Given the history, `E[a_t x_t(b') | H_{t−1}] = ∑_j p_j c_j y_{j,t}(b')` with `y_t(b')` the
acceptance probabilities of Algorithm 1 at period `t` and right-hand side `b'`
(`LPResolvingRM.yRule`: `1` at `t = 1`, `sel(n_{t−1}/(t−1), b')` for `t ≥ 2`; p.15, (13)).

**Formalization Note.** The suprema over the unbounded region `𝔅` are written as "for all
`b' ∈ 𝔅`", which is the same condition and avoids a junk `sSup`; the second condition is
coordinatewise on `I'`, the first is the maximum over `I*`. The event depends only on the type
sequence of the periods before `t` (the history `H_{t−1}`). -/
def goodEvent {n m : ℕ} (I : Instance n m) (sel : Selector n m) (ystar : Fin n → ℝ) (L : ℝ)
    (T : ℕ) (ω : Fin T → Fin n) (t : ℕ) : Prop :=
  ∀ r, region I ystar L r →
    (∀ i ∈ binding I ystar,
      |∑ j, I.p j * I.c j i * yRule sel ω (t - 1) r j - r i| ≤ epsStar I L T (t - 1)) ∧
    (∀ i ∉ binding I ystar,
      ∑ j, I.p j * I.c j i * yRule sel ω (t - 1) r j - r i ≤ epsPrime I L T (t - 1))

/-- **The stopping time `τ̃`** (arXiv:2101.11092v3, p.36):
`τ̃ := min{t ≤ T : b_t ∉ 𝔅 or H_{t−1} ∉ 𝓔_t} ∪ {T + 1}`, over the paper's periods `t ≥ 1`. -/
noncomputable def tauTilde {n m : ℕ} (I : Instance n m) (sel : Selector n m)
    (ystar : Fin n → ℝ) (L : ℝ) (T : ℕ) (ω : Fin T → Fin n) (β : Fin T → Bool) : ℕ :=
  if h : ∃ t, 1 ≤ t ∧ t ≤ T ∧
      (¬ region I ystar L (avgCap I T ω β (t - 1)) ∨ ¬ goodEvent I sel ystar L T ω t) then
    Nat.find h
  else T + 1

/-- **The frozen process `b̃_t`** (arXiv:2101.11092v3, p.36): `b̃_t := b_t` for `t < τ̃` and
`b_{τ̃}` for `t ≥ τ̃`, with `b_t = LPResolvingRM.avgCap … (t − 1)`. -/
noncomputable def bTilde {n m : ℕ} (I : Instance n m) (sel : Selector n m) (ystar : Fin n → ℝ)
    (L : ℝ) (T : ℕ) (ω : Fin T → Fin n) (β : Fin T → Bool) (t : ℕ) : Fin m → ℝ :=
  if t < tauTilde I sel ystar L T ω β then avgCap I T ω β (t - 1)
  else avgCap I T ω β (tauTilde I sel ystar L T ω β - 1)

/-- **The constant `T₁`** of Lemma 12 (arXiv:2101.11092v3, p.36): the minimal integer such that
`T₁ ≥ (1/(exp(L/8) − 1) + 2) ∨ (1/(exp(L/(8(1 + L − b̲))) − 1) + 2)` and
`log T₁ / T₁^{1/4} ≤ κ^{1/4} L / 4`.

**Formalization Note.** The infimum of the set of such natural numbers; the set is nonempty
(`log N / N^{1/4} → 0`) when `κ > 0`. -/
noncomputable def T1 {n m : ℕ} (I : Instance n m) (L : ℝ) : ℕ :=
  sInf {N : ℕ | max (1 / (Real.exp (L / 8) - 1) + 2)
      (1 / (Real.exp (L / (8 * (1 + L - bmin I))) - 1) + 2) ≤ (N : ℝ) ∧
    Real.log N / (N : ℝ) ^ (1 / 4 : ℝ) ≤ kappa I L ^ (1 / 4 : ℝ) * L / 4}

/-- **The event `𝒜^{(j)}_t`** (arXiv:2101.11092v3, pp.14, 36):
`𝒜^{(j)}_t := {|n_j(t−1)/(t−1) − p_j| ≤ L}` for `t ≥ 2`; the whole space for `t = 1`. -/
def eventA {n m : ℕ} (I : Instance n m) (L : ℝ) (T : ℕ) (ω : Fin T → Fin n) (t : ℕ)
    (j : Fin n) : Prop :=
  t ≤ 1 ∨ |freq ω (t - 1) j - I.p j| ≤ L

/-- **The event `ℬ^{(j)}_t`** (arXiv:2101.11092v3, pp.14, 36):
`ℬ^{(j)}_t := {|n_j(t−1)/(t−1) − p_j| ≤ 1/(n(t−1)^{1/4})}` for `t ≥ 2`; the whole space for
`t = 1`. -/
def eventB {n m : ℕ} (I : Instance n m) (T : ℕ) (ω : Fin T → Fin n) (t : ℕ) (j : Fin n) :
    Prop :=
  t ≤ 1 ∨ |freq ω (t - 1) j - I.p j| ≤ 1 / ((n : ℝ) * ((t : ℝ) - 1) ^ (1 / 4 : ℝ))

end LPResolvingRM


