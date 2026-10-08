-- Prove2me | Definitions.Def_ClassifAgg_Aggregation_Suprema
-- name    : ClassifAgg_Aggregation_Suprema
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:36.430865+00:00
-- url     : https://prove2.me/theorems/a9251de4-ff47-4d57-a8b3-7c970ccc93ff
-- title:
--   Appendix, pp. 163–164 — the suprema W_n, W_0n, V_n, V_0n and sup_G |R_n(G*) − R_n(G) + d(G, G*)|
-- statement:
--   The suprema of empirical processes studied in the Appendix.
--
--   Let $\mathcal G$ be a class of sets, $0<\rho<1$, $r_n=n^{-1/(1+\rho)}$, $c_1,c_2>0$, and $G^*=\{\eta\ge1/2\}$. On a sample of size $n$ define
--
--   $$W_n(\mathcal G)=\sup_{(G,G')\in\mathcal S}\left|\left(\frac{d_{\triangle,e}(G,G')}{d_\triangle(G,G')}\right)^{(1-\rho)/2}-1\right|,\qquad \mathcal S=\{(G,G'):G,G'\in\mathcal G,\ d_\triangle(G,G')\ge c_1r_n\},$$
--
--   $$W_{0n}(\mathcal G)=\sup_{G,G'\in\mathcal G:\ d_\triangle(G,G')\le c_1r_n}d_{\triangle,e}(G,G'),$$
--
--   $$V_n(\mathcal G)=\sup_{G\in\mathcal G:\ d_\triangle(G,G^*)\ge c_1r_n}\frac{\sqrt n\,|R_n(G^*)-R_n(G)+d(G,G^*)|}{d_\triangle^{(1-\rho)/2}(G,G^*)},$$
--
--   $$V_{0n}(\mathcal G)=\sup_{G\in\mathcal G:\ d_\triangle(G,G^*)\le c_2r_n}|R_n(G^*)-R_n(G)+d(G,G^*)|,$$
--
--   and the global deviation $\sup_{G\in\mathcal G}|R_n(G^*)-R_n(G)+d(G,G^*)|$ of Lemma 11.
--
--   Since $d(G,G^*)=E(R_n(G)-R_n(G^*))$ and $d_\triangle=E\,d_{\triangle,e}$, these suprema measure how far the empirical risk differences and empirical distances deviate from their means; Lemmas 7–11 bound their tails.
--
--   **Formalization Note** Each supremum is a real supremum over the indexed subset, which is bounded above when $c_1>0$, $n\ge1$, $0<\rho<1$ and $(P_X,\eta)$ is a distribution: by $(c_1r_n)^{-(1-\rho)/2}+1$ for $W_n$ (as $d_{\triangle,e}\le1$), by $1$ for $W_{0n}$, by $2\sqrt n\,(c_1r_n)^{-(1-\rho)/2}$ for $V_n$, and by $2$ for $V_{0n}$ and the global deviation. So the real supremum is the true one; an empty index set gives the value $0$, which is harmless for the positive thresholds of Lemmas 7–11.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Appendix, p. 163 (W_n), p. 164 (W_0n, V_n, V_0n, Lemma 11)

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Model

namespace ClassifAgg.Aggregation

open MeasureTheory

/-- The rate `rₙ = n^{-1/(1+ρ)}` of the Appendix (p. 163). -/
noncomputable def rate (n : ℕ) (ρ : ℝ) : ℝ := (n : ℝ) ^ (-1 / (1 + ρ))

/-- `Wₙ(𝒢) = sup_{(G, G') ∈ 𝒮} |(d_{△,e}(G, G') / d_△(G, G'))^{(1-ρ)/2} − 1|`, where
`𝒮 = {(G, G') : G, G' ∈ 𝒢, d_△(G, G') ≥ c₁ n^{-1/(1+ρ)}}` (Appendix, p. 163).

The supremum is a real `⨆` over the subtype `𝒮`. For `c₁ > 0`, `n ≥ 1` and `0 < ρ < 1` the
family is bounded above by `(c₁ rₙ)^{-(1-ρ)/2} + 1` (as `d_{△,e} ≤ 1`), so `⨆` is the true
supremum; an empty `𝒮` gives `0`. -/
noncomputable def Wsup {d n : ℕ} (c1 ρ : ℝ) (PX : Measure (E d)) (cls : Set (Set (E d)))
    (s : Fin n → E d × Bool) : ℝ :=
  ⨆ p : {p : Set (E d) × Set (E d) //
      p.1 ∈ cls ∧ p.2 ∈ cls ∧ c1 * rate n ρ ≤ dTri PX p.1 p.2},
    |(dTriEmp s p.1.1 p.1.2 / dTri PX p.1.1 p.1.2) ^ ((1 - ρ) / 2) - 1|

/-- `W₀ₙ(𝒢) = sup_{G, G' ∈ 𝒢 : d_△(G, G') ≤ c₁ n^{-1/(1+ρ)}} d_{△,e}(G, G')` (Appendix, p. 164).
Bounded above by `1`, so `⨆` is the true supremum; an empty index set gives `0`. -/
noncomputable def W0sup {d n : ℕ} (c1 ρ : ℝ) (PX : Measure (E d)) (cls : Set (Set (E d)))
    (s : Fin n → E d × Bool) : ℝ :=
  ⨆ p : {p : Set (E d) × Set (E d) //
      p.1 ∈ cls ∧ p.2 ∈ cls ∧ dTri PX p.1 p.2 ≤ c1 * rate n ρ},
    dTriEmp s p.1.1 p.1.2

/-- `Vₙ(𝒢) = sup_{G ∈ 𝒢 : d_△(G, G*) ≥ c₁ n^{-1/(1+ρ)}}
√n |Rₙ(G*) − Rₙ(G) + d(G, G*)| / d_△^{(1-ρ)/2}(G, G*)` (Appendix, p. 164).
For `c₁ > 0`, `n ≥ 1`, `0 < ρ < 1` and `0 ≤ η ≤ 1` under a probability measure, the family is
bounded above by `2√n (c₁ rₙ)^{-(1-ρ)/2}`, so `⨆` is the true supremum; an empty index set gives
`0`. -/
noncomputable def Vsup {d n : ℕ} (c1 ρ : ℝ) (PX : Measure (E d)) (η : E d → ℝ)
    (cls : Set (Set (E d))) (s : Fin n → E d × Bool) : ℝ :=
  ⨆ G : {G : Set (E d) // G ∈ cls ∧ c1 * rate n ρ ≤ dTri PX G (bayesSet η)},
    Real.sqrt n * |empRisk s (bayesSet η) - empRisk s G.1 + excess PX η G.1| /
      dTri PX G.1 (bayesSet η) ^ ((1 - ρ) / 2)

/-- `V₀ₙ(𝒢) = sup_{G ∈ 𝒢 : d_△(G, G*) ≤ c₂ n^{-1/(1+ρ)}} |Rₙ(G*) − Rₙ(G) + d(G, G*)|`
(Appendix, p. 164). Bounded above by `2` (for `0 ≤ η ≤ 1` under a probability measure), so `⨆` is
the true supremum; an empty index set gives `0`. -/
noncomputable def V0sup {d n : ℕ} (c2 ρ : ℝ) (PX : Measure (E d)) (η : E d → ℝ)
    (cls : Set (Set (E d))) (s : Fin n → E d × Bool) : ℝ :=
  ⨆ G : {G : Set (E d) // G ∈ cls ∧ dTri PX G (bayesSet η) ≤ c2 * rate n ρ},
    |empRisk s (bayesSet η) - empRisk s G.1 + excess PX η G.1|

/-- `sup_{G ∈ 𝒢} |Rₙ(G*) − Rₙ(G) + d(G, G*)|` (Lemma 11, p. 164). Bounded above by `2` (for
`0 ≤ η ≤ 1` under a probability measure), so `⨆` is the true supremum; an empty `𝒢` gives `0`. -/
noncomputable def devSup {d n : ℕ} (PX : Measure (E d)) (η : E d → ℝ) (cls : Set (Set (E d)))
    (s : Fin n → E d × Bool) : ℝ :=
  ⨆ G : {G : Set (E d) // G ∈ cls},
    |empRisk s (bayesSet η) - empRisk s G.1 + excess PX η G.1|

end ClassifAgg.Aggregation


