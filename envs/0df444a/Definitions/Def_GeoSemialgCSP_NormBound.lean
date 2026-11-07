-- Prove2me | Definitions.Def_GeoSemialgCSP_NormBound
-- name    : GeoSemialgCSP_NormBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:51:30.385013+00:00
-- url     : https://prove2.me/theorems/a77cd9fb-3576-4a44-8150-999b08a3bc44
-- title:
--   The norm-bound property of Theorem 8.1
-- statement:
--   Fix $d_{\mathrm{VC}}\ge1$ and $0<\eta<1$. Constants $C,b$ have the **norm-bound property** if for every alphabet size $M\ge1$, every $q\ge1$ and every $0<\kappa<1$ there is $\tau>0$, independent of $R$, such that the following holds. Let $G:[M]^R\to\mathcal P_q$, let $F=T_{1-\eta}G$ be $\tau$-pseudorandom (total vector influence), let $Z$ be uniform on $[M]^R$ and $\mu=\mathbb EF(Z)$. Then for every $0<t\le1$ and every family $\mathcal B$ of subsets of $[q]$ with $\mathrm{VCdim}(\mathcal B)\le d_{\mathrm{VC}}$ and $\mu(B)\le t$ for all $B\in\mathcal B$,
--   $$\mathbb E\Bigl[\max_{B\in\mathcal B}F_B(Z)\Bigr]\ \le\ C\,t^b+\kappa .$$
--   The same $\tau$ works for all families and all cutoffs.
--
--   **Formalization Note** $[M]$ is any nonempty finite set $W$. The maximum over an empty family is $0$ (the paper's convention).
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 8.1, Eq. (16), p.22 (PDF p.23)

import Mathlib
import Definitions.Def_GeoSemialgCSP_noiseOpV
import Definitions.Def_GeoSemialgCSP_inflV
import Definitions.Def_GeoSemialgCSP_vcSets
import Definitions.Def_GeoSemialgCSP_massB
import Definitions.Def_GeoSemialgCSP_unifAvg

namespace GeoSemialgCSP

/-- **The norm-bound property of Theorem 8.1.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 8.1, printed p.22 (PDF
p.23): constants `C, b` have the property that for every `M, q ≥ 1` and every `0 < κ < 1` there is
`τ > 0`, independent of `R`, such that: for `G : [M]^R → P_q`, if `F = T_{1−η}G` is
`τ`-pseudorandom and `Z` is uniform on `[M]^R`, `μ = E F(Z)`, then for every `0 < t ≤ 1` and every
family `𝓑 ⊆ 2^{[q]}` with `VCdim(𝓑) ≤ d_VC` and `μ(B) ≤ t` for all `B ∈ 𝓑`,
`E[max_{B ∈ 𝓑} F_B(Z)] ≤ C t^b + κ` (16). The same `τ` works for all `𝓑` and all `t`.

**Formalization Note.** `[M]` is any nonempty finite type `W` (`τ` may depend on it, as
`τ(M, …)` does). `τ`-pseudorandom means total vector influence at most `τ` in every coordinate.
The maximum over `𝓑` is the real `⨆ B ∈ 𝓑`: it is `0` for empty `𝓑` (the paper's convention,
p.22), and the junk value `0` for `B ∉ 𝓑` is harmless because `F_B ≥ 0`. `t^b` is `Real.rpow`. -/
def NormBound (dVC : ℕ) (η C b : ℝ) : Prop :=
  ∀ (W : Type) [Fintype W] [Nonempty W] (q : ℕ), 1 ≤ q → ∀ κ : ℝ, 0 < κ → κ < 1 →
    ∃ τ : ℝ, 0 < τ ∧ ∀ (R : ℕ) (G : (Fin R → W) → Fin q → ℝ),
      (∀ z, G z ∈ stdSimplex ℝ (Fin q)) →
      (∀ r, inflV (noiseOpV (1 - η) G) r ≤ τ) →
      ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ 𝓑 : Set (Set (Fin q)), vcSets 𝓑 ≤ (dVC : ℕ∞) →
        (∀ B ∈ 𝓑, massB (fun a => unifAvg (fun z => noiseOpV (1 - η) G z a)) B ≤ t) →
        unifAvg (fun z => ⨆ B ∈ 𝓑, massB (noiseOpV (1 - η) G z) B) ≤ C * t ^ b + κ

end GeoSemialgCSP


