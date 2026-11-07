-- Prove2me | Definitions.Def_PFRelease_filterLaw
-- name    : PFRelease_filterLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:23.82418+00:00
-- url     : https://prove2.me/theorems/bea3ecf2-30be-468e-be2c-7f7126e7fa12
-- title:
--   Private element–block filter $\mathcal F_{b,t,\kappa,\sigma,\sigma'}(F;\cdot)$ (Algorithm 1)
-- statement:
--   The **private filter** $\mathcal F_{b,t,\kappa,\sigma,\sigma'}(F;s)$ with block size $b$, threshold $t$, cap $\kappa$ and noise scales $\sigma,\sigma'>0$ runs on $s\in\mathcal X^n$, $b\mid n$:
--
--   1. $m\leftarrow n/b$; $\tilde\kappa\leftarrow\lceil\kappa+\eta\rceil$ with $\eta\sim\mathrm{Lap}(\sigma)$; if $\tilde\kappa\le0$ return $\perp^n$;
--   2. draw a uniformly random partition of $[n]$ into $m$ subsets of size $b$, independent of the data, and let $s^{(1)},\dots,s^{(m)}$ be the blocks (records of each subset in index order);
--   3. $q_i(\cdot):=\sum_{j\in[m]}F(\cdot^{(j)},s_i)$, the friend count of $s_i$;
--   4. $u\leftarrow\mathrm{SV}_{t,\tilde\kappa,\sigma'}(q;s)$; if $\|u\|=\tilde\kappa$ return $\perp^n$;
--   5. return $s^{R\to\perp}$ with $R:=\{i:u_i=1\}$.
--
--   The object defined is $\Pr[\mathcal F(s)=s^{I\to\perp}]$ as a function of $I$.
--
--   **Formalization Note** Labelled equipartitions $\pi:[n]\to[m]$ with every fibre of size $b$ stand for unordered partitions; the uniform law on them induces the uniform law on partitions and no friend count depends on the labels. The run is the literal transcription (`filterOut`), with the sparse-vector run `svRun`; abort ($\perp^n$) is $I=[n]$. The noises $\eta,\gamma_1,\dots,\gamma_n$ are independent Laplace (the published `PrivLearn.Generic.laplace`). That the weights sum to one for $b>0$, $b\mid n$, $\sigma,\sigma'>0$ is proved in the mission's verification file.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Algorithm 1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_PFRelease_Dataset
import Definitions.Def_PFRelease_svLaw

open MeasureTheory

namespace PFRelease

/-- A map `π : Fin n → Fin m` is an equipartition with blocks of size `b` if every block
`π⁻¹(j)` has exactly `b` slots. -/
def IsEquipartition {n m : ℕ} (b : ℕ) (π : Fin n → Fin m) : Prop :=
  ∀ j : Fin m, (Finset.univ.filter (fun k => π k = j)).card = b

open Classical in
/-- The finite set of equipartitions of the `n` slots into `m = n / b` labelled blocks of size `b`. -/
noncomputable def equipartitions (n b : ℕ) : Finset (Fin n → Fin (n / b)) :=
  Finset.univ.filter (fun π => IsEquipartition b π)

/-- The block `s^{(j)}` of a partition `π`: the records of the slots `k` with `π k = j`, in their
original index order (Algorithm 1, p.8: "`s^{(j)}` holds the records in the `j`th subset in their
original index order"). -/
def block {X : Type*} {n m : ℕ} (π : Fin n → Fin m) (s : Fin n → Option X) (j : Fin m) :
    List (Option X) :=
  ((List.finRange n).filter (fun k => decide (π k = j))).map s

/-- The friend count `Σ_{j∈[m]} F(s^{(j)}, x)`: the number of blocks of `s` under `π` that the
record `x` is friendly with. -/
def friendCount {X : Type*} {n m : ℕ} (F : List (Option X) → Option X → Bool)
    (π : Fin n → Fin m) (s : Fin n → Option X) (x : Option X) : ℕ :=
  (Finset.univ.filter (fun j => F (block π s j) x = true)).card

/-- The nulled index set of one run of the private filter `F_{b,t,κ,σ,σ′}(F; s)` (Algorithm 1,
p.8), given its partition `π`, cap noise `η` and test noises `γ`:

`κ̃ ← ⌈κ + η⌉`; if `κ̃ ≤ 0` return `⊥ⁿ`; `qᵢ(·) := Σ_{j∈[m]} F(·^{(j)}, sᵢ)`;
`u ← SV_{t,κ̃,σ′}(q; s)`; if `∥u∥ = κ̃` return `⊥ⁿ`; return `s^{R→⊥}`, `R := {i : uᵢ = 1}`.

**Formalization Note** The output `s^{I→⊥}` is represented by `I`; `⊥ⁿ = s^{[n]→⊥}` is
`I = univ`. The sparse vector run is the literal `svRun` (Algorithm 2) with the non-adaptive
queries `qᵢ(w) = Σⱼ F(w^{(j)}, sᵢ)` evaluated on `w = s`; its cap is `κ̃` as a natural number
(`κ̃ > 0` at that point). -/
noncomputable def filterOut {X : Type*} {n : ℕ} (b : ℕ) (t κ : ℝ)
    (F : List (Option X) → Option X → Bool) (s : Fin n → Option X) (π : Fin n → Fin (n / b))
    (η : ℝ) (γ : Fin n → ℝ) : Finset (Fin n) :=
  if ⌈κ + η⌉ ≤ 0 then Finset.univ else
    let u : Transcript :=
      svRun t (⌈κ + η⌉).toNat (fun i _ w => (friendCount F π w (s i) : ℝ)) s γ
    if ((List.count true u : ℕ) : ℤ) = ⌈κ + η⌉ then Finset.univ
    else Finset.univ.filter (fun i => List.getD u i.val false = true)

/-- The law of the private filter `F_{b,t,κ,σ,σ′}(F; s)` with element–block filtering (Shenfeld,
Tsfadia, Ligett, arXiv:2610.40654, held version sha256 e1d516b3…, Algorithm 1, p.8 = PDF p.10):
`filterLaw b t κ σ σ′ F s I` is the probability that the run on `s` nulls exactly the slots `I`,
i.e. returns `s^{I→⊥}`.

The partition `π` is uniform over the equipartitions of `[n]` into `m = n/b` blocks of size `b`,
drawn independently of the data; `η ∼ Lap(σ)` and `γ₁, …, γₙ ∼ Lap(σ′)` are independent.

**Formalization Note** Labelled equipartitions `π : Fin n → Fin (n/b)` stand for the paper's
unordered partitions: every unordered partition has the same number `m!` of labellings, and no
friend count depends on the labels, so the law is the paper's. The parameters `t, κ ∈ ℝ` and
`σ, σ′ > 0` are real; `b ∣ n` and `b > 0` are hypotheses of the theorems (the paper's standing
assumption, p.8). `Lap(σ)` is the published `PrivLearn.Generic.laplace`. -/
noncomputable def filterLaw {X : Type*} {n : ℕ} (b : ℕ) (t κ σ σ' : ℝ)
    (F : List (Option X) → Option X → Bool) (s : Fin n → Option X) (I : Finset (Fin n)) :
    ENNReal :=
  ∑ π ∈ equipartitions n b, ((equipartitions n b).card : ENNReal)⁻¹ *
    ((PrivLearn.Generic.laplace σ).prod (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace σ'))
      {ω | filterOut b t κ F s π ω.1 ω.2 = I}

end PFRelease


