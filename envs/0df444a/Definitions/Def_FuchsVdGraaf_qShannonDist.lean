-- Prove2me | Definitions.Def_FuchsVdGraaf_qShannonDist
-- name    : FuchsVdGraaf_qShannonDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:22.381071+00:00
-- url     : https://prove2.me/theorems/0a5aea9c-9d39-4f21-8816-00568638ccf1
-- title:
--   Quantum Shannon distinguishability $SD(\rho_0,\rho_1)$ (Definition 11)
-- statement:
--   For density matrices $\rho_0, \rho_1$, the **Shannon distinguishability** is the largest classical Shannon distinguishability achievable by a measurement:
--
--   $$
--   \mathrm{SD}(\rho_0,\rho_1) = \sup_{E\in\mathcal M} \mathrm{SD}\big(p_0(E), p_1(E)\big),
--   $$
--
--   where $E$ ranges over all POVMs $\mathcal M$ and $p_t(E)(x) = \mathrm{Tr}(\rho_t E_x)$. It is the accessible information of the ensemble $\{\tfrac12\rho_0, \tfrac12\rho_1\}$; no closed formula for it is known in general.
--
--   **Formalization Note** The paper writes $\max$ (p.10: "more carefully … infimum", resp. supremum). The supremum is taken in $\mathbb R$ over the set of values at all POVMs $E : \mathrm{Fin}\,m \to M_n(\mathbb C)$, $m\in\mathbb N$; for density matrices the set is nonempty and bounded above by $1$.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Definition 11, eq. (41), p.16

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsVdGraaf_outcomeDist
import Definitions.Def_FuchsVdGraaf_shannonDist

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Definition 11, eq. (41), p.16: the Shannon distinguishability between two
density matrices `ρ₀`, `ρ₁` is
`SD(ρ₀, ρ₁) = max_{E∈M} SD(p₀(E), p₁(E))`, where the POVM `E` ranges over the set `M` of all
possible measurements and `p_t(E)(x) = Tr(ρ_t E_x)` (eq. (10)).

**Formalization Note.** The paper writes max and adds (p.10): "More carefully, one should use
'supremum' in this definition." This is the supremum (`sSup` in `ℝ`) of the *set* of values
`SD(p₀(E), p₁(E))` over every POVM `E : Fin m → Matrix n n ℂ` with any number `m` of outcomes.
The set contains the value at the one-outcome POVM `![1]`, so it is nonempty, and for density
matrices it lies in a bounded interval, so the `sSup` is the paper's supremum and not a junk value. -/
noncomputable def qShannonDist {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ) : ℝ :=
  sSup {v : ℝ | ∃ (m : ℕ) (E : Fin m → Matrix n n ℂ),
    IsPOVM E ∧ v = shannonDist (outcomeDist ρ0 E) (outcomeDist ρ1 E)}

end FuchsVdGraaf


