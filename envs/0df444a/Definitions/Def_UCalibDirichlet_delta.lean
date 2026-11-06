-- Prove2me | Definitions.Def_UCalibDirichlet_delta
-- name    : UCalibDirichlet_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:11.373605+00:00
-- url     : https://prove2.me/theorems/3493ce5f-a3c7-40b3-9e69-c97dad1eb58f
-- title:
--   Stability term $\delta^i_F(a)$
-- statement:
--   For a proper loss $\ell_F$, an outcome $i$ and a count vector $a\in\mathbb R^K_{>0}$,
--   $$\delta^i_F(a)=\mathbb E_{P\sim\mathrm{Dir}(a)}[\ell_F(P,i)]-\mathbb E_{P\sim\mathrm{Dir}(a+e_i)}[\ell_F(P,i)].$$
--   It compares the expected loss of Algorithm 1's forecast (follow the perturbed leader) with that of the forecast which has already counted the outcome $i$ (be the perturbed leader); its sum over rounds is the stability term of the regret decomposition (8).
--
--   **Formalization Note** The difference is taken in the extended reals; the subtracted term is finite for a proper loss with finite Bayes risk (Lemma 1.3).
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma 1.4, p.4

import Mathlib
import Definitions.Def_UCalibDirichlet_dir
import Definitions.Def_UCalibDirichlet_expLoss

namespace UCalibDirichlet

/-- **The stability term `δ^i_F(a)`.** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), Lemma 1.4, p.4: "where `δ^i_F(a) = E_{P∼Dir(a)}[ℓ_F(P, i)] − E_{P∼Dir(a+e_i)}[ℓ_F(P, i)]`."

`delta ℓ i a = E_{P∼Dir(a)}[ℓ(P, i)] − E_{P∼Dir(a + e_i)}[ℓ(P, i)]`, with `e_i = Pi.single i 1`.

**Formalization Note.** The difference is taken in `EReal`. For a proper loss with finite Bayes
risk and `a > 0`, the subtracted term is finite (Lemma 1.3 gives it as `Λ_F(a) − Λ_F(a + e_i)`), so
no `⊤ − ⊤` occurs. -/
noncomputable def delta {K : ℕ} (ℓ : (Fin K → ℝ) → Fin K → EReal) (i : Fin K) (a : Fin K → ℝ) :
    EReal :=
  expLoss ℓ (dir a) i - expLoss ℓ (dir (a + Pi.single i 1)) i

end UCalibDirichlet


