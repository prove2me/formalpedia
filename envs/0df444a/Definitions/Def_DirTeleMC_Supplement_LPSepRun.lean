-- Prove2me | Definitions.Def_DirTeleMC_Supplement_LPSepRun
-- name    : DirTeleMC_Supplement_LPSepRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:43:19.388561+00:00
-- url     : https://prove2.me/theorems/ed95d53b-823f-47be-9222-06d226d228e9
-- title:
--   LPSEP
-- statement:
--   **LPSEP** with an integer $p$ and a separator algorithm, on a DTM instance with $k=|K|$ terminals:
--
--   1. compute the fallback schedule $\mathrm{best}$, the busy schedule along a shortest-path out-arborescence from $s$ to $K$;
--   2. for $\theta=1,\dots,k-1$: at the first $\theta$ for which LP($\theta$) is feasible, compute a rational $x$ feasible for LP($\theta$) and run LEVELSEP; if it fails, return $\mathrm{best}$; otherwise return the shorter of $\mathrm{best}$ and the phase schedule of its pieces;
--   3. if LP($\theta$) is infeasible for all these $\theta$, return $\mathrm{best}$.
--
--   The relation $\mathrm{LPSepRun}(p,Z,I,S)$ holds when $S$ is the output of some run.
--
--   LPSEP is the algorithm of Theorems 5.2 and 1.3.
--
--   **Formalization Note** The fallback is the published `FallbackRun`. Every free choice is open, including the rational solution $x$ and which of two schedules of equal length is returned.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Algorithm 5, p.41 (PDF p.42); App. C.3, p.40 (PDF p.41)

import Mathlib
import Definitions.Def_DirTeleMC_FallbackRun
import Definitions.Def_DirTeleMC_Supplement_PhaseScheduleRun

namespace DirTeleMC.Supplement

open DirTeleMC

/-- **A run of LPSEP** (Algorithm 5, p.42).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Algorithm 5 and App. C.3, pp.40–42: "best ← the busy schedule along a shortest-path
out-arborescence from s to K (Lemma B.3); for θ = 1, . . . , k − 1 do: if LP(θ) is feasible (Lemma C.2(b)) then
Q ← LEVELSEP(G, s, K, θ) (Algorithm 4); if Q is failure then return best; Y ← the phase schedule of the pieces in Q
(Definition C.5); return the shorter of best and Y; end if; end for; return best".

`LPSepRun p Z I S`, for the integer `p` and the class algorithm `Z`, with `k = |K|`: some fallback schedule `best`
(the published `FallbackRun`, Lemma B.3) is computed; then either LP(θ) is infeasible for every `θ ∈ {1, …, k − 1}`
and `S = best`, or for the least such `θ` with LP(θ) feasible, some rational `x` feasible for LP(θ) (Lemma C.2(b)) is
used by a run of LEVELSEP, and `S = best` if it fails, and otherwise `S` is the shorter of `best` and a phase schedule
`Y` of its pieces.

**Formalization Note.** Every free choice is open: the fallback schedule, the rational solution `x` (any rational
`x` for which some path flow is feasible), the choices inside LEVELSEP and the phase schedule, and which of two
schedules of equal length is returned. -/
def LPSepRun (p : ℕ) (Z : SepInput → List ℕ) (I : Inst) (S : Schedule I.n) : Prop :=
  ∃ best : Schedule I.n, FallbackRun I best ∧
    (((∀ θ, 1 ≤ θ → θ + 1 ≤ I.K.card → ¬ ∃ x, LPFeasible I θ x) ∧ S = best) ∨
     ∃ θ, 1 ≤ θ ∧ θ + 1 ≤ I.K.card ∧ (∀ θ', 1 ≤ θ' → θ' < θ → ¬ ∃ x, LPFeasible I θ' x) ∧
       ∃ x : Fin I.n → Fin I.n → ℚ, LPFeasible I θ (fun u v => (x u v : ℝ)) ∧
         ((LevelSepRun { I := I, p := p, Z := Z, θ := θ, x := x } none ∧ S = best) ∨
          ∃ (pcs : List (Piece I.n)) (Y : Schedule I.n),
            LevelSepRun { I := I, p := p, Z := Z, θ := θ, x := x } (some pcs) ∧
            PhaseScheduleRun { I := I, p := p, Z := Z, θ := θ, x := x } pcs Y ∧
            ((S = best ∧ best.length ≤ Y.length) ∨ (S = Y ∧ Y.length ≤ best.length))))

end DirTeleMC.Supplement


