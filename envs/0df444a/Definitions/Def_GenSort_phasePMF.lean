-- Prove2me | Definitions.Def_GenSort_phasePMF
-- name    : GenSort_phasePMF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:35:17.531652+00:00
-- url     : https://prove2.me/theorems/1d6f503e-250c-4c2e-85a1-c3ea3599c145
-- title:
--   One phase of the prediction construction (§3.1–§3.5)
-- statement:
--   One phase on an edge set $F$ with $f = |F|$ and $d = \lceil f/n \rceil$:
--   1. sample $\lceil 2^{32} n\log^3 n\rceil$ edges of $F$ uniformly with replacement, query them, and let $\sigma$ be a permutation agreeing with every reported orientation;
--   2. build the bipartite graph $H_0$ of §3.2 from $\sigma$ and a split into groups of size at most $d$;
--   3. sample $\lceil 2^{32} n\log^3 n\rceil$ edges again, query them, flag the right vertices with at least $2^9\log n$ sampled bad edges, and remove all their edges, giving $H_1$;
--   4. run $\lceil \log n\rceil$ error isolation passes on $H_1$, giving $H_f$.
--
--   The number of queries is tallied. The fallback of §3.6 (remove nothing if more than $f/2$ edges would be removed) is not part of this process.
--
--   **Formalization Note** The arbitrary choices of the page (the permutation $\sigma$, the split, tie-breaking and the choice of $\tau'$) are inputs, and statements quantify over all valid choices. The flagging sample is drawn from the edges of $H_0$, which correspond one-to-one to the edges of $F$. $\log = \log_2$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.1–§3.5, pp.5–12 (PDF pp.7–14)

import Mathlib
import Definitions.Def_GenSort_k0
import Definitions.Def_GenSort_dPar
import Definitions.Def_GenSort_sPar
import Definitions.Def_GenSort_Split
import Definitions.Def_GenSort_Hedges
import Definitions.Def_GenSort_flagged
import Definitions.Def_GenSort_TieRules
import Definitions.Def_GenSort_passesPMF
import Definitions.Def_GenSort_PhaseOut

namespace GenSort

/-- **One phase of the prediction construction of §3** (before the fallback of §3.6), Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…),
§3.1–§3.5, pp.5–12 (PDF pp.7–14), for an edge set `F` with `f = |F|` and `d = ⌈f/n⌉`:

1. (§3.1) sample `k0 n = ⌈2^32 n log³ n⌉` edges of `F` uniformly with replacement, query them, and
   let `σ = σr x` (the rule `σr` chooses a permutation agreeing with every reported orientation);
2. (§3.2) build `H₀ = Hedges (spr σ)`, the bipartite graph with groups of size at most `d`;
3. (§3.3) take a fresh sample of `k0 n` edges, query them, and remove all edges at flagged right
   vertices, giving `H₁`;
4. (§3.5) run `⌈log₂ n⌉` error isolation passes on `H₁`, giving `Hf`.

The queries are tallied: `k0 n` for each of the two samples, plus those of the passes.

**Formalization Note.** The arbitrary choices of the page (σ, the split, ties, `τ'`) are inputs
`σr`, `spr`, `ρ`; theorems quantify over all valid choices. The flagging sample is drawn from the
edges of `H₀`, which correspond one-to-one to the edges of `F`. `log` is `log₂`, and "log n
passes" is `⌈log₂ n⌉`. -/
noncomputable def phasePMF {n : ℕ} (F : Finset (Sym2 (Fin n))) (π : Equiv.Perm (Fin n))
    (σr : (Fin (k0 n) → F) → Equiv.Perm (Fin n))
    (spr : (σ : Equiv.Perm (Fin n)) → Split F σ (dPar n F.card))
    (ρ : TieRules (Fin n × Fin n) (Fin n × Fin n) (sPar n (dPar n F.card))) :
    PMF (PhaseOut n) :=
  open Classical in
  if hF : F.Nonempty then
    haveI : Nonempty F := hF.to_subtype
    (PMF.uniformOfFintype (Fin (k0 n) → F)).bind fun x =>
      if h₀ : (Hedges (spr (σr x))).Nonempty then
        haveI : Nonempty (Hedges (spr (σr x))) := h₀.to_subtype
        (PMF.uniformOfFintype (Fin (k0 n) → Hedges (spr (σr x)))).bind fun z =>
          (passesPMF Prod.fst Prod.fst π (dPar n F.card) ρ ⌈Real.logb 2 n⌉₊
              ((Hedges (spr (σr x))).filter fun p =>
                ¬ flagged (Hedges (spr (σr x))) Prod.fst Prod.fst π (k0 n) z p.2)).map fun o =>
            ⟨σr x, Hedges (spr (σr x)),
              (Hedges (spr (σr x))).filter fun p =>
                ¬ flagged (Hedges (spr (σr x))) Prod.fst Prod.fst π (k0 n) z p.2,
              o.1, 2 * k0 n + o.2⟩
      else PMF.pure ⟨σr x, Hedges (spr (σr x)), Hedges (spr (σr x)), Hedges (spr (σr x)), k0 n⟩
  else PMF.pure ⟨1, ∅, ∅, ∅, 0⟩

end GenSort


