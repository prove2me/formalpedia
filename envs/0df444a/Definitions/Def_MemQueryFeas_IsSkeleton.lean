-- Prove2me | Definitions.Def_MemQueryFeas_IsSkeleton
-- name    : MemQueryFeas_IsSkeleton
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:38:34.717109+00:00
-- url     : https://prove2.me/theorems/77168b48-9945-4c79-aaa3-b7aefe83f4cf
-- title:
--   The skeleton tree construction (Algorithm 2)
-- statement:
--   On a probability space, random subspaces $E_1,\dots,E_P$ and versions $E^{(i)}_{v',p}$ ($p\in[P]$, $v'\in V_{p-1}$, $0\le i\le N_p$) follow **Algorithm 2** if
--   1. $E_1,\dots,E_P$ are independent with law $\mathrm{Unif}(\mathrm{Gr}(\tilde d,d))$, $\tilde d=\lfloor d/(36P)\rfloor$;
--   2. for every $p$ and $v'\in V_{p-1}$, independently of all other variables,
--   $$
--   E^{(\le N_p)}_{v',p}=\mathrm{NoiseAddition}\big(H_{v'}(E_p),\ \delta_p^{(\le N_p)}/\sqrt{3P}\big),
--   $$
--   where $H_{v'}=T_{v'}^{-\top}$ is computed from the versions of the earlier layers.
--
--   "Independently of all other variables" is expressed by conditioning each sampling step on $E_1,\dots,E_P$, on all versions of earlier layers and on the other version sequences of the same layer.
--
--   **Formalization Note** All variables live on an abstract probability space and are measurable.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §3.1 and Algorithm 2, pp.7–8 (PDF pp.8–9)

import Mathlib
import Definitions.Def_MemQueryFeas_IsHaarGr
import Definitions.Def_MemQueryFeas_IsNoiseAddition
import Definitions.Def_MemQueryFeas_imageProj
import Definitions.Def_MemQueryFeas_Hmap
import Definitions.Def_MemQueryFeas_IsPhase
import Definitions.Def_MemQueryFeas_dt
import Definitions.Def_MemQueryFeas_Np
import Definitions.Def_MemQueryFeas_delta

open MeasureTheory ProbabilityTheory

namespace MemQueryFeas

open Classical in
/-- **The skeleton tree (Algorithm 2).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.1 and Algorithm 2, pp.7–8 (PDF pp.8–9): "Sample
`E_1, …, E_P` iid `∼ Unif(Gr(d̃, d))` and initialize `T_∅ = I`; for `p = 1, …, P` do for
`v' ∈ V_{p−1}` do Sample independently `E^(≤N_p)_{v',p} := NoiseAddition(H_{v'}(E_p),
δ_p^(≤N_p)/√(3P))`", "independently from all other variables".

`IsSkeleton d ε P μ ν Eb ch`: on `(Ω, μ)`, with `Eb p = P_{E_p}` and `ch p v' i = E^(i)_{v',p}`:
1. `ν` is the Haar law of `Gr(d̃, d)`, `d̃ = ⌊d/(36P)⌋`;
2. all `Eb p` and `ch p v' i` are measurable;
3. `E_1, …, E_P` are independent with law `ν`;
4. for every `p ∈ [P]` and `v' ∈ V_{p−1}`, `ch p v' 0, …, ch p v' N_p` is NoiseAddition started at
   `H_{v'}(E_p)` with accuracies `δ_p^(i)/√(3P)`, using fresh randomness: the conditioning variable
   is `(E_1, …, E_P)` together with every version of the layers `q < p` and every other version
   sequence `(u, p)`, `u ≠ v'`, of layer `p` (entries with an index outside the tree replaced
   by `0`). `H_{v'} = T_{v'}^{−⊤}` is computed from the versions of the layers `< p`.

**Formalization Note.** An abstract probability space carries all variables; `μ` is a probability
measure in every use (instance hypothesis of the theorems). Indices: `p, q` are 1-based layers,
phase lists are `IsPhase`, version indices run over `0, …, N_p`. Conditioning on the other
sequences of the same layer expresses their mutual independence given the earlier layers. -/
def IsSkeleton {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (ε : ℝ) (P : ℕ) (μ : Measure Ω)
    (ν : Measure (Op d)) (Eb : ℕ → Ω → Op d) (ch : ℕ → List ℕ → ℕ → Ω → Op d) : Prop :=
  IsHaarGr (dt d P) ν ∧ (∀ p, Measurable (Eb p)) ∧ (∀ p v i, Measurable (ch p v i)) ∧
    iIndepFun (fun p : Fin P => Eb (p.1 + 1)) μ ∧
    (∀ p, 1 ≤ p → p ≤ P → μ.map (Eb p) = ν) ∧
    ∀ p, 1 ≤ p → p ≤ P → ∀ v', IsPhase (Np d ε P) (p - 1) v' →
      IsNoiseAddition μ ν (dt d P)
        (fun ω => ((fun q => Eb q ω), fun q u j =>
          if (q < p ∨ (q = p ∧ u ≠ v')) ∧ 1 ≤ q ∧ IsPhase (Np d ε P) (q - 1) u ∧
              j ≤ Np d ε P q then ch q u j ω else 0))
        (fun z => imageProj (Hmap (delta d ε P) z.2 v') (z.1 p))
        (fun i => delta d ε P p i / Real.sqrt (3 * P)) (Np d ε P p) (ch p v')

end MemQueryFeas


