-- Prove2me | Definitions.Def_HierADA_noiseLaw
-- name    : HierADA_noiseLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:59.444219+00:00
-- url     : https://prove2.me/theorems/708d5dfb-b0e3-45ea-8e6f-12b1eaf46623
-- title:
--   Law of the pre-assigned Laplace noise
-- statement:
--   The law of the noise of the auxiliary mechanism makes all the following draws independent, with the Laplace law $\mathrm{Lap}(s)$ of density $\frac1{2s}e^{-|x|/s}$:
--
--   1. answer noise $E_t\sim\mathrm{Lap}(b)$ for the $k$ queries;
--   2. threshold noise $Z_{j,\varphi}\sim\mathrm{Lap}(2b)$ for every edge $j$ and phase $\varphi<B_j$;
--   3. test noise $V_m\sim\mathrm{Lap}(4b)$ for the $2(p-1)(k+\sum_jB_j)$ possible signed tests.
--
--   The auxiliary execution reads no other coordinate (p.25 counts at most $2p(k+\sum_jB_j+1)$ draws), and the remaining coordinates are set to $0$.
--
--   **Formalization Note** The law is the image of the finite product measure under the extension map; the verification file proves that this map is measurable, so the image is a genuine push-forward. The Laplace law is the published `PrivLearn.Generic.laplace`.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Algorithms 1–2 (pp.13–14), Definition 2.2 (p.12) and the proof of Theorem 3.7 (p.25)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_HierADA_params__e3298e
import Definitions.Def_HierADA_Noise

set_option autoImplicit false

open MeasureTheory

namespace HierADA

/-- **The law of the pre-assigned noise of the auxiliary mechanism** — Gribelyuk–Lin–Lyu–Majid–
Woodruff–Yu–Zhou, *Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*,
preprint (version of 2026-11-03, sha256 f220ae51…), Algorithms 1–2 (pp.13–14) and the proof of
Theorem 3.7 (p.25: "assign independent randomness to all potential phases and numerical releases in
advance"; "the total number of noise draws is at most `2p(k + ∑_{j=1}^{p-1} B_j + 1)`").

Independent draws, with the published Laplace law `Lap(s)` (density `e^{−|x|/s}/(2s)`):
* answer noise `E_t ∼ Lap(b)` for the `k` queries `t < k`;
* threshold noise `Z_{j,φ} ∼ Lap(2b)` for every edge `j` and phase `φ < B_j`;
* test noise `V_m ∼ Lap(4b)` for the `m < 2(p − 1)(k + ∑_j B_j)` signed tests.
The law is the product of these, carried to `Noise` by setting every other coordinate to `0`; the
auxiliary execution never reads another coordinate.

**Formalization Note.** `b = prm.b`. Coordinates beyond the draw counts above are never read by
`auxRun` (at most `k + ∑_j B_j` scans, each with at most `p − 1` edges and two tests per edge, and at
most `B_j` phases on edge `j`), so fixing them to `0` is immaterial. The extension map is measurable
(verification file), so this push-forward is a probability measure. -/
noncomputable def noiseLaw (prm : Params) (k : ℕ) : Measure Noise :=
  Measure.map toNoise
    ((Measure.pi fun _ : Fin k => PrivLearn.Generic.laplace prm.b).prod
      ((Measure.pi fun j : Fin prm.p =>
          Measure.pi fun _ : Fin (prm.B j) => PrivLearn.Generic.laplace (2 * prm.b)).prod
        (Measure.pi fun _ : Fin (2 * (prm.p - 1) * (k + ∑ j, prm.B j)) =>
          PrivLearn.Generic.laplace (4 * prm.b))))
where
  /-- Extend the finitely many draws to a full noise realization (other coordinates `0`). -/
  toNoise (x : (Fin k → ℝ) × (((j : Fin prm.p) → Fin (prm.B j) → ℝ) ×
      (Fin (2 * (prm.p - 1) * (k + ∑ j, prm.B j)) → ℝ))) : Noise :=
    (fun t => if h : t < k then x.1 ⟨t, h⟩ else 0,
     fun j φ => if h : j < prm.p then
        (if h2 : φ < prm.B ⟨j, h⟩ then x.2.1 ⟨j, h⟩ ⟨φ, h2⟩ else 0) else 0,
     fun m => if h : m < 2 * (prm.p - 1) * (k + ∑ j, prm.B j) then x.2.2 ⟨m, h⟩ else 0)

end HierADA


