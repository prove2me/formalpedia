-- Prove2me | Definitions.Def_OTSensitivity_Info_InjectiveAE
-- name    : OTSensitivity_Info_InjectiveAE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:18.721236+00:00
-- url     : https://prove2.me/theorems/43d40b08-879c-49d7-bcb7-1be2822cc19d
-- title:
--   Injectivity almost everywhere (Theorem 8)
-- statement:
--   Let $\mu$ be a measure on a measurable space $\mathsf X$ and $g:\mathsf X\to\mathsf U$ a map. We say that $g$ is **injective $\mu$-almost everywhere** if there is a measurable set $S\subseteq\mathsf X$ with
--   $$\mu(\mathsf X\setminus S)=0\qquad\text{and}\qquad g|_S\ \text{injective}.$$
--
--   This is the hypothesis of the last sentence of Theorem 8, under which a transformation $U=g(X)$ of the input carries as much information as $X$ itself.
--
--   **Formalization Note** The paper says only "injective almost everywhere"; it is read with respect to $\mu$, the law of $X$ (not $\mathbb P$ on $\Omega$, not the law of $Y$), and as injectivity on a measurable set of full measure.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Theorem 8 (last sentence), p. 11

import Mathlib

namespace OTSensitivity.Info

/-- Theorem 8, p. 11: `g` is injective almost everywhere with respect to `µ`, read as: there is a
measurable set `S ⊆ 𝓧` of full `µ`-measure (`µ(Sᶜ) = 0`) on which `g` is injective. -/
def IsInjectiveAE {𝓧 𝓤 : Type*} [MeasurableSpace 𝓧] (μ : MeasureTheory.Measure 𝓧) (g : 𝓧 → 𝓤) :
    Prop :=
  ∃ S : Set 𝓧, MeasurableSet S ∧ μ Sᶜ = 0 ∧ Set.InjOn g S

end OTSensitivity.Info


