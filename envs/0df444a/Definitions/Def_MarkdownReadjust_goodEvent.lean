-- Prove2me | Definitions.Def_MarkdownReadjust_goodEvent
-- name    : MarkdownReadjust_goodEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:15:49.794083+00:00
-- url     : https://prove2.me/theorems/b6a1c891-943c-462e-9998-797694724799
-- title:
--   Good event $\mathcal G$
-- statement:
--   The good event is $\mathcal G=\bigcap_{n=1}^N(\mathcal G_{n0}\cap\mathcal G_{n1})$, where
--
--   $$
--   \mathcal G_{n0}=\Big\{\eta_{n-1}-\eta_n>\frac{\hat\Delta_{n-1}}{\lambda(T-t_n)}\Big\},\qquad \mathcal G_{n1}=\Big\{\rho^d-\eta_n-\sum_{m=0}^{n-1}\frac{\hat\Delta_m}{\lambda(T-t_{m+1})}\in(0,1)\Big\}.
--   $$
--
--   On $\mathcal G$ neither the projection nor the maximum in the definition of $\hat\rho_n$ is active, which makes the adjusted rates linear in past sales deviations.
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Appendix B.1, p.ec13

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_rhoD
import Definitions.Def_MarkdownReadjust_tgrid
import Definitions.Def_MarkdownReadjust_eta
import Definitions.Def_MarkdownReadjust_seqPoissonLaw
import Definitions.Def_MarkdownReadjust_hatLaw

namespace MarkdownReadjust

/-- The "good event" `𝒢 = ∩_{n=1}^{N} (𝒢_{n0} ∩ 𝒢_{n1})` (Chen–Jasin, SSRN 3740871, p.ec13),
a set of uncapped sales paths `(Ŝ₀, …, Ŝ_N)`, where
`𝒢_{n0} = {η_{n−1} − ηₙ > Δ̂_{n−1}/(λ(T − tₙ))}` and
`𝒢_{n1} = {ρᵈ − ηₙ − Σ_{m=0}^{n−1} Δ̂ₘ/(λ(T − t_{m+1})) ∈ (0,1)}`. -/
def goodEvent (M : Model) (α : ℝ) (N x : ℕ) (τ : ℝ) : Set (Fin (N + 1) → ℕ) :=
  {ω | ∀ n : ℕ, 1 ≤ n → n ≤ N →
    (DeltaHat M α N x τ (pathExt ω) (n - 1) / (M.lam * (τ - tgrid x τ N n))
        < eta M.lam α x τ N (n - 1) - eta M.lam α x τ N n) ∧
    (rhoD M x τ - eta M.lam α x τ N n
        - ∑ m ∈ Finset.range n,
            DeltaHat M α N x τ (pathExt ω) m / (M.lam * (τ - tgrid x τ N (m + 1))))
      ∈ Set.Ioo (0 : ℝ) 1}

end MarkdownReadjust


