-- Prove2me | Definitions.Def_PFRelease_svLaw
-- name    : PFRelease_svLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:19.651658+00:00
-- url     : https://prove2.me/theorems/2a2ef5a7-509b-49d7-86a3-101d0e9b0b58
-- title:
--   Fixed-threshold sparse vector $\mathrm{SV}_{t,\kappa,\sigma}$ (Algorithm 2)
-- statement:
--   **Fixed-threshold sparse vector** $\mathrm{SV}_{t,\kappa,\sigma}(q;s)$ takes a dataset $s$, queries $q_1,\dots,q_n$, a threshold $t\in\mathbb R$, a failure cap $\kappa\in\mathbb N$ and a noise scale $\sigma>0$, and runs:
--
--   1. $u\leftarrow()$;
--   2. for $i=1,\dots,n$: draw $\gamma_i\sim\mathrm{Lap}(\sigma)$, set $u_i\leftarrow\mathbf 1\{q_i(s)+\gamma_i\le t\}$ (a failure), append $u_i$ to $u$, and return $u$ if $\|u\|=\kappa$;
--   3. return $u$.
--
--   Here $\|u\|$ is the number of ones of the transcript $u$. The queries are adaptive: $q_i$ may depend on $(u_1,\dots,u_{i-1})$. The object defined is the law of the returned transcript.
--
--   **Formalization Note** `svRun` is the transcript as a function of the noise vector $\gamma\in\mathbb R^n$ (all noises drawn in advance; unused ones do not change the law), with `q i u d` the $i$th query chosen after the prefix $u$, evaluated on $d$. `svLaw` is the image of $\mathrm{Lap}(\sigma)^{\otimes n}$; the map is measurable (proved in the mission's verification file), so the law is a probability measure. Transcripts carry the discrete $\sigma$-algebra.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Algorithm 2, p.8 (PDF p.10), and §3.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_PFRelease_Dataset

open MeasureTheory

namespace PFRelease

/-- Binary transcripts `u = (u₁, u₂, …)` of sparse vector and of Boolean interactions
(arXiv:2610.40654, §3.2, p.9): lists of bits, `true` = 1 (a failure). The type synonym carries
the discrete σ-algebra `⊤`, so every set of transcripts is an event. -/
def Transcript : Type := List Bool

instance : MeasurableSpace Transcript := ⊤

instance : Countable Transcript := inferInstanceAs (Countable (List Bool))

/-- The state of fixed-threshold sparse vector after its first `k` loop iterations: the transcript
so far and whether the algorithm has returned. Iteration `k` (slot `k`, 0-based) is skipped once
the algorithm has returned or when `k ≥ n`. Otherwise it appends `u_k = 1{q_k(u, d) + γ_k ≤ t}`,
where `u` is the preceding transcript, and returns if `∥u∥ = κ` afterwards. -/
noncomputable def svAux {D : Type*} {n : ℕ} (t : ℝ) (κ : ℕ) (q : Fin n → List Bool → D → ℝ) (d : D)
    (γ : Fin n → ℝ) : ℕ → List Bool × Bool
  | 0 => ([], false)
  | k + 1 =>
    let st := svAux t κ q d γ k
    if h : k < n then
      if st.2 then st else
        let u := st.1 ++ [decide (q ⟨k, h⟩ st.1 d + γ ⟨k, h⟩ ≤ t)]
        (u, decide (u.count true = κ))
    else st

/-- The output transcript of fixed-threshold sparse vector `SV_{t,κ,σ}(q; d)` (Shenfeld, Tsfadia,
Ligett, arXiv:2610.40654, held version sha256 e1d516b3…, Algorithm 2, p.8 = PDF p.10) as a
function of its noises `γ ∈ ℝⁿ`:

`u ← ()`; for `i ∈ [n]`: `γᵢ ∼ Lap(σ)`, `uᵢ ← 1{qᵢ(d) + γᵢ ≤ t}`, `u ← (u, uᵢ)`,
if `∥u∥ = κ` then return `u`; return `u`.

**Formalization Note** The queries are adaptive (p.9): `q i u d` is the value on the dataset `d`
of the query chosen after the preceding transcript `u`. The test `∥u∥ = κ` is made after each
append, literally as in the algorithm. All `n` noises are drawn in advance; those after the
return are unused, which does not change the law of the transcript. -/
noncomputable def svRun {D : Type*} {n : ℕ} (t : ℝ) (κ : ℕ) (q : Fin n → List Bool → D → ℝ) (d : D)
    (γ : Fin n → ℝ) : Transcript :=
  (svAux t κ q d γ n).1

/-- The law of the transcript of `SV_{t,κ,σ}(q; d)` (Algorithm 2, p.8): the image of the i.i.d.
noise law `Lap(σ)^{⊗n}` under `svRun`. The map is measurable (each transcript is cut out by
finitely many half-space conditions), so this image is not degenerate. -/
noncomputable def svLaw {D : Type*} {n : ℕ} (t : ℝ) (κ : ℕ) (σ : ℝ)
    (q : Fin n → List Bool → D → ℝ) (d : D) : Measure Transcript :=
  (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace σ).map (svRun t κ q d)

end PFRelease


