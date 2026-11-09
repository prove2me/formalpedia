-- Prove2me | Definitions.Def_MWCSherali_Omega
-- name    : MWCSherali_Omega
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:29.877207+00:00
-- url     : https://prove2.me/theorems/49b938b0-9f70-469b-914f-f6a19906679d
-- title:
--   Valid labelings $\Omega^{\mathrm{no}}_C$ of a downward cell
-- statement:
--   For a downward cell $C$,
--
--   $$\Omega^{\mathrm{no}}_C=\{\sigma\in[k+1]^C\mid \forall u\in C,\ \sigma(u)\in L^{\mathrm{no}}(u)\},$$
--
--   the labelings of the vertices of $C$ consistent with the non-opposite requirements. The vertex-consistency LP keeps a probability distribution over $\Omega^{\mathrm{no}}_C$ for every cell.
--
--   **Formalization Note** A labeling of $C$ is stored as a labeling of all of $\Delta_{k,n}$ that is valid on $C$ and equals the neutral label off $C$; these are in bijection with $\Omega^{\mathrm{no}}_C$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §2.2, p.15

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_Lno
import Definitions.Def_MWCSherali_cell

namespace MWCSherali

/-- **Valid labelings `Ω^no_C` of a downward cell.** Brakensiek–Huang–Potechin–Zwick,
arXiv:2611.05511 (version of Nov. 3, 2026), §2.2, p.15:
`Ω^no_C = {σ ∈ [k+1]^C | ∀ u ∈ C, σ(u) ∈ L^no(u)}`.

**Formalization Note.** A labeling `σ ∈ [k+1]^C` of the cell `C = D(V)` is stored as a total map
`Grid k n → Fin (k+1)` that is valid on `C` and takes the fixed value `Fin.last k` off `C`; these
maps are in bijection with `Ω^no_C`, so every sum over `Omega V` is a sum over `Ω^no_C`. -/
def Omega {k n : ℕ} (V : Grid k (n + 1)) : Type :=
  {σ : Grid k n → Fin (k + 1) //
    ∀ u, (u ∈ cell V → σ u ∈ Lno u) ∧ (u ∉ cell V → σ u = Fin.last k)}

noncomputable instance {k n : ℕ} (V : Grid k (n + 1)) : Fintype (Omega V) := by
  classical
  unfold Omega
  infer_instance

end MWCSherali


