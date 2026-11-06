-- Prove2me | Definitions.Def_MemQueryFeas_IsGame1Nature
-- name    : MemQueryFeas_IsGame1Nature
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:38:12.001599+00:00
-- url     : https://prove2.me/theorems/c2832369-f353-40e2-b05d-458891bbebab
-- title:
--   Nature's move in Game 1
-- statement:
--   In Game 1 nature samples $E\sim\mathrm{Unif}(\mathrm{Gr}(\tilde d,d))$ and then
--   $$
--   E^{(\le N)}=\mathrm{NoiseAddition}\big(T(E),\delta^{(\le N)}\big)
--   $$
--   for a fixed linear map $T$ and accuracies $\delta^{(0)},\dots,\delta^{(N)}$. The predicate says that random variables $E,E^{(0)},\dots,E^{(N)}$ on a probability space have this joint law.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Game 1, line 1, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_MemQueryFeas_IsHaarGr
import Definitions.Def_MemQueryFeas_imageProj
import Definitions.Def_MemQueryFeas_IsNoiseAddition

open MeasureTheory

namespace MemQueryFeas

/-- **Nature's move in Game 1.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Game 1, line 1, p.12 (PDF p.13): "Nature: Sample
`E ∼ Unif(Gr(d̃, d))` and `E^(≤N) := NoiseAddition(T(E), δ^(≤N))` (see Alg. 1)".

`IsGame1Nature μ ν d̃ T δ N E ch`: on `(Ω, μ)`, `ν` is the Haar law of `Gr(d̃,d)`, `E` is measurable
with law `ν`, every `ch i` is measurable, and `ch 0, …, ch N` is NoiseAddition started at `T(E)`
with accuracies `δ 0, …, δ N` (conditioning variable `E`).

**Formalization Note.** `μ` is a probability measure in every use (instance hypothesis of the
theorems); invertibility of `T` and positivity of the accuracies are hypotheses of the theorems. -/
def IsGame1Nature {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω) (ν : Measure (Op d))
    (dt : ℕ) (T : Op d) (δ : ℕ → ℝ) (N : ℕ) (E : Ω → Op d) (ch : ℕ → Ω → Op d) : Prop :=
  IsHaarGr dt ν ∧ Measurable E ∧ μ.map E = ν ∧ (∀ i, Measurable (ch i)) ∧
    IsNoiseAddition μ ν dt E (imageProj T) δ N ch

end MemQueryFeas


