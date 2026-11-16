-- Prove2me | Definitions.Def_DQILocal_Recon_Supplement_ConfigModel
-- name    : DQILocal_Recon_Supplement_ConfigModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:26:19.166089+00:00
-- url     : https://prove2.me/theorems/dafcf0d8-bffc-4a89-8546-7fce62a3064b
-- title:
--   The configuration model with and without the conditioning on multiple edges
-- statement:
--   Let $k,D\ge1$ and let $m$ be admissible, $D\mid km$, with $n=km/D$ checks. Symbol $j$ has the half-edges $jk,\dots,jk+k-1$ and check $a$ the half-edges $aD,\dots,aD+D-1$.
--
--   1. **Without the conditioning**, a uniformly random bijection $\sigma$ of the $km$ half-edges pairs symbol half-edge $h$ with check $\lfloor\sigma(h)/D\rfloor$, and $B_{ja}$ is the number of half-edges of $j$ paired with $a$, reduced modulo two (the incidence matrix of the bipartite multigraph reduced modulo two).
--   2. **With the conditioning** on the absence of multiple edges, $B$ is uniform on the $(k,D)$-regular $m\times n$ 0/1 matrices.
--
--   Expectations and probabilities over $B$ are finite averages, and every limit as $m\to\infty$ is taken along the admissible $m$.
--
--   **Formalization Note** Every simple biregular graph arises from exactly $(k!)^m(D!)^n$ bijections, so the conditioned model is the uniform law on regular matrices, as in the base definition `configProb`.
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), §5.1, p. 31; §7.3, p. 60

import Mathlib
import Definitions.Def_DQILocal_Recon_LocalConditions

namespace DQILocal.Recon.Supplement

open scoped BigOperators
open DQILocal.Recon Filter

/-- **The pairing matrix of the configuration model.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), §5.1, p. 31 ("Give each
of the `m` symbols `k` half-edges and each of the `n = mk/D` checks `D` half-edges, pair the two sets
of half-edges by a uniformly random bijection") and §7.3, p. 60 ("Without the conditioning, `B` is
the incidence matrix of the bipartite multigraph reduced modulo two").

Symbol `j` owns the half-edges `jk, …, jk + k - 1` and check `a` the half-edges `aD, …, aD + D - 1`,
both index sets being `Fin (km)`; the bijection `σ` pairs the symbol half-edge `h` with the check
half-edge `σ(h)`, i.e. with the check `⌊σ(h)/D⌋`. The entry `B_{ja}` is the number of half-edges of
`j` paired with `a`, reduced modulo two (`true` for odd).

**Formalization Note.** The model is used only along admissible `m` (`D ∣ km`, so `n = km/D`
exactly, see `admissible`). -/
def configMatrix (k D m : ℕ) (σ : Equiv.Perm (Fin (k * m))) : Matrix (Fin m) (Fin (k * m / D)) Bool :=
  fun j a => decide ((Finset.univ.filter fun h : Fin (k * m) =>
    h.val / k = j.val ∧ (σ h).val / D = a.val).card % 2 = 1)

/-- The two laws of the random instance `B` (§5.1, p. 31; §7.3, p. 60). -/
inductive CfgLaw
  /-- the configuration model without the conditioning: `B = configMatrix σ` with `σ` a uniformly
  random bijection of the `km` half-edges -/
  | pairing
  /-- the configuration model conditioned on the absence of multiple edges: as in the published
  base definition `configProb`, this is the uniform law on the `(k, D)`-regular `m × n` 0/1 matrices
  (every simple biregular graph arises from exactly `(k!)^m (D!)^n` bijections) -/
  | simple

/-- **Expectation `E_B[g(B)]` over the random instance** (finite averages): over the `(km)!`
bijections for `pairing`, over the `(k, D)`-regular `m × (km/D)` matrices for `simple`. -/
noncomputable def cfgExpect : CfgLaw → (k D m : ℕ) → (Matrix (Fin m) (Fin (k * m / D)) Bool → ℝ) → ℝ
  | .pairing, k, D, m, g =>
      (1 / (Fintype.card (Equiv.Perm (Fin (k * m))) : ℝ)) * ∑ σ, g (configMatrix k D m σ)
  | .simple, k, D, m, g => by
      classical
      exact (∑ B ∈ Finset.univ.filter (fun B : Matrix (Fin m) (Fin (k * m / D)) Bool =>
          IsRegular k D B), g B) /
        ((Finset.univ.filter fun B : Matrix (Fin m) (Fin (k * m / D)) Bool => IsRegular k D B).card :
          ℝ)

/-- **Probability `Pr_B[E(B)]` of an event of the random instance.** -/
noncomputable def cfgProb (L : CfgLaw) (k D m : ℕ) (E : Matrix (Fin m) (Fin (k * m / D)) Bool → Prop) :
    ℝ := by
  classical
  exact cfgExpect L k D m fun B => if E B then 1 else 0

/-- **Admissible sizes**: `m → ∞` along the `m` with `D ∣ km` (so that `n = km/D` checks exist). All
limits "as `m → ∞`" and "with probability `1 - o(1)`" are taken along this filter. -/
def admissible (k D : ℕ) : Filter ℕ := atTop ⊓ 𝓟 {m | D ∣ k * m}

end DQILocal.Recon.Supplement


