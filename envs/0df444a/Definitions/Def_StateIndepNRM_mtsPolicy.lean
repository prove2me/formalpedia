-- Prove2me | Definitions.Def_StateIndepNRM_mtsPolicy
-- name    : StateIndepNRM_mtsPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:37:50.869677+00:00
-- url     : https://prove2.me/theorems/99eafbeb-9a0f-4efe-b33f-0c6374a7e63f
-- title:
--   The make-to-stock policy, its stock-out times and $\Delta$
-- statement:
--   Let $l$ be a rate function, $X$ a demand process with rate $l$, and $D_n=\lfloor\int_0^Tl_{n,t}\,dt\rfloor$.
--
--   1. The **stock-out time** $\tau$ is the earliest time in $[0,T]$ at which some product has $D_n$ units sold, and $T$ if there is none.
--   2. The **product stock-out time** $\tau_n$ is the first time with $X_n(t)\ge D_n$ if $X_n(T)\ge D_n$, and $T$ otherwise.
--   3. The **make-to-stock (MTS) policy** uses the rate $l_t$ for $t\le\tau$ and the zero rate (the null price vector) afterwards, so its sales are $X_n(t\wedge\tau)$.
--   4. $\Pi^{MTS}_C$ is the expected revenue of this policy, and
--
--   $$
--   \Delta:=\int_0^Tr^*_t\,dt-\mathbb E\int_0^\tau r^*_t\,dt.
--   $$
--
--   **Formalization Note** The set defining $\tau$ always contains $T$, so `sInf ∅ = 0` never occurs. The condition $D_n\le X_n(t)$ replaces the page's "equals $D_n$": it gives the same time because jumps are unit almost surely. $D_n=0$ gives $\tau=0$, as on the page. This is the §3 p.9 policy, not the p.7 one, which keeps selling the other products after $\tau$.
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, §3, pp.7, 9 (MTS, τ^MTS, D_n), §3.1, pp.10–11 (Π^MTS_C, (3), τ_n)

import Mathlib
import Definitions.Def_StateIndepNRM_IsAdmissible
import Definitions.Def_StateIndepNRM_IsDetOptimal

open MeasureTheory Set

namespace StateIndepNRM

variable {M N : ℕ}

/-- The stock `D_n = ⌊∫₀ᵀ l t n dt⌋` of product `n` (Manchiraju–Dawande–Janakiraman, SSRN 3831496,
§3, p.7). -/
noncomputable def fluidStock (T : ℝ) (l : ℝ → Fin N → ℝ) (n : Fin N) : ℕ :=
  ⌊∫ t in (0 : ℝ)..T, l t n⌋₊

/-- The stock-out time `τ^MTS` (SSRN 3831496, §3, p.7): the earliest time in `[0, T]` at which
some product has `D_n` units sold under the demand process `X`, and `T` if there is none.

**Formalization Note.** The set always contains `T`, so `sInf ∅ = 0` never occurs. `D_n ≤ X n t`
replaces the page's "equals D_n": they give the same time, since `X n` has unit jumps almost
surely and reaches `D_n` from below. `D_n = 0` gives `τ = 0`, as on the page. -/
noncomputable def stockoutTime {Ω : Type} (T : ℝ) (l : ℝ → Fin N → ℝ) (X : Fin N → ℝ → Ω → ℕ)
    (ω : Ω) : ℝ :=
  sInf ({t ∈ Icc 0 T | ∃ n, fluidStock T l n ≤ X n t ω} ∪ {T})

open Classical in
/-- The stock-out time `τ_n` of product `n` (SSRN 3831496, §3.1, p.11): the first time `X n` reaches
`D_n` if `X n T ≥ D_n`, and `T` otherwise.

**Formalization Note.** `D_n ≤ X n t` replaces the page's `X_n(t) = D_n` for the same reason as in
`stockoutTime`; under the `if` the set contains `T`, so it is nonempty. -/
noncomputable def productStockoutTime {Ω : Type} (T : ℝ) (l : ℝ → Fin N → ℝ) (n : Fin N)
    (X : Fin N → ℝ → Ω → ℕ) (ω : Ω) : ℝ :=
  if fluidStock T l n ≤ X n T ω then sInf {t ∈ Icc 0 T | fluidStock T l n ≤ X n t ω} else T

open Classical in
/-- The make-to-stock policy of §3, p.9 (SSRN 3831496): "In the MTS policy, after time t ≥ τ^MTS, we
set the price vector of the products to p∞_t, the null price vector at time t." It follows the rate
`l t` up to `τ` and the zero rate afterwards, so its sales are the demand process stopped at `τ`.

**Formalization Note.** This is the §3 p.9 version, not the p.7 one, which keeps selling the other
products after `τ`. The zero rate is feasible by Assumption 2. -/
noncomputable def mtsPolicy {Ω : Type} {mΩ : MeasurableSpace Ω} (T : ℝ) (l : ℝ → Fin N → ℝ)
    (𝓕 : Filtration (Icc (0 : ℝ) T) mΩ) (X : Fin N → ℝ → Ω → ℕ) : PricingSystem T N mΩ where
  𝓕 := 𝓕
  lam := fun t ω => if t ≤ stockoutTime T l X ω then l t else 0
  X := fun n t ω => X n (min t (stockoutTime T l X ω)) ω

/-- The expected revenue `Π^MTS_C` of the MTS policy (SSRN 3831496, §3.1, p.10). -/
noncomputable def mtsRevenue (I : Instance M N) {Ω : Type} {mΩ : MeasurableSpace Ω}
    (l : ℝ → Fin N → ℝ) (P : Measure Ω) (𝓕 : Filtration (Icc (0 : ℝ) I.T) mΩ)
    (X : Fin N → ℝ → Ω → ℕ) : ℝ :=
  revenue I P (mtsPolicy I.T l 𝓕 X)

/-- `Δ := ∫₀ᵀ r*_t dt − E[Π[0, τ]]` of (3) (SSRN 3831496, §3.1, p.11), where `Π[0, τ]` has
expectation `E ∫₀^τ r*_t dt`.

**Formalization Note.** `Π[0, τ]` is the revenue over `[0, τ]`, written as the integral of the
revenue rate, as for `revenue`. -/
noncomputable def mtsDelta (I : Instance M N) {Ω : Type} {mΩ : MeasurableSpace Ω}
    (l : ℝ → Fin N → ℝ) (P : Measure Ω) (X : Fin N → ℝ → Ω → ℕ) : ℝ :=
  detValue I l - ∫ ω, (∫ t in (0 : ℝ)..stockoutTime I.T l X ω, I.revRate t (l t)) ∂P

end StateIndepNRM


