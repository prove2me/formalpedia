-- Prove2me | Definitions.Def_RevRedSAT_Supplement_EdgeMonteCarloWithin
-- name    : RevRedSAT_Supplement_EdgeMonteCarloWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:56:05.156594+00:00
-- url     : https://prove2.me/theorems/20f7cf33-cb73-4533-bce9-54b931ec29e7
-- title:
--   Monte Carlo search algorithms whose solutions are edge sets
-- statement:
--   This is the published notion `RevRedSAT.MonteCarloWithin` for problems whose solutions are sets of edges (Steiner Tree, Max Leaf Spanning Tree) instead of sets of vertices.
--
--   A machine is a **Monte Carlo search algorithm with success probability $\theta$ within $T$** if there is a computable rule $\rho$ with $\rho(t)\le t$ such that, on every code $w$ of every instance $I$ and with $t=T(I,w)$:
--
--   1. for every random string $r\in\{0,1\}^{\rho(t)}$, the machine run on $w$ followed by $r$ halts within $t$ steps and outputs either "no" or "yes" followed by a list of edges, each edge once, whose edge set is a feasible solution (no false positives);
--   2. if a feasible solution exists, at least a $\theta$ fraction of the $2^{\rho(t)}$ random strings make it output a solution.
--
--   **Formalization Note** The probability is the uniform measure on random strings; the time bound holds on every string.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Table 1, p.8 (randomized algorithms); Theorems 8.3, p.57 and 8.7, p.61

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RevRedSAT_VCInstance

set_option autoImplicit false

namespace RevRedSAT.Supplement

open RSListDecodingCapacity.AllRates

/-- **An output without false positives, for problems whose solutions are edge sets**: `[false]`,
or `true` followed by the code of a list of edges, each edge once (in either orientation), whose
edge set is feasible. -/
def IsEdgeSoundOutput {n : ℕ} (valid : Finset (Sym2 (Fin n)) → Prop) (out : List Bool) : Prop :=
  out = [false] ∨ ∃ L : List (Fin n × Fin n), (L.map fun e : Fin n × Fin n => s(e.1, e.2)).Nodup ∧
    valid (L.map fun e : Fin n × Fin n => s(e.1, e.2)).toFinset ∧ out = true :: encList encEdge L

/-- **A Monte Carlo search algorithm whose solutions are edge sets, with success probability `θ`.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Table 1, p.8: "Randomized algorithms have no false positives and return a valid solution on a
YES instance with probability at least 2/3"; Theorems 8.3 (p.57) and 8.7 (p.61).

The same notion as the published `RevRedSAT.MonteCarloWithin`, with solutions that are sets of
edges instead of sets of vertices: there is a computable rule `ρ` giving the number of random bits
as a function of the time bound; on every code `w` of every instance `I`, with `t = T I w`, for
every random string `r ∈ {0,1}^{ρ(t)}` (`ρ(t) ≤ t`) the machine, run on `w` followed by `r`, halts
within `t` steps with an output without false positives (`IsEdgeSoundOutput`); and if a feasible
solution exists, at least a `θ` fraction of the random strings make it output a solution.

**Formalization Note** Random bits are read after the instance code; probability is the uniform
measure on `{0,1}^{ρ(t)}`, i.e. a count; worst-case time on every random string. -/
def EdgeMonteCarloWithin {ι : Type} (M : Turing.TM2ComputableAux Bool Bool) (n : ι → ℕ)
    (IsCode : ι → List Bool → Prop) (valid : (I : ι) → Finset (Sym2 (Fin (n I))) → Prop)
    (T : ι → List Bool → ℕ) (θ : ℝ) : Prop :=
  ∃ ρ : ℕ → ℕ, Computable ρ ∧ (∀ t, ρ t ≤ t) ∧ ∀ I w, IsCode I w →
    ∃ out : (Fin (ρ (T I w)) → Bool) → List Bool,
      (∀ r, IsEdgeSoundOutput (valid I) (out r) ∧
        HMBinPacking.OutputsWithin M (w ++ List.ofFn r) (out r) (T I w)) ∧
      ((∃ S, valid I S) →
        θ * 2 ^ (ρ (T I w)) ≤ ((Finset.univ.filter fun r => out r ≠ [false]).card : ℝ))

end RevRedSAT.Supplement


