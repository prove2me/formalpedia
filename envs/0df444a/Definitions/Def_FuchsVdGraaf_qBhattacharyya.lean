-- Prove2me | Definitions.Def_FuchsVdGraaf_qBhattacharyya
-- name    : FuchsVdGraaf_qBhattacharyya
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:39.125546+00:00
-- url     : https://prove2.me/theorems/64d53d84-91fc-4d9d-92f4-cfd52a567468
-- title:
--   Quantum Bhattacharyya coefficient $B(\rho_0,\rho_1)$ (Definition 8)
-- statement:
--   For density matrices $\rho_0, \rho_1$, the **Bhattacharyya coefficient** is the smallest classical Bhattacharyya coefficient achievable by a measurement:
--
--   $$
--   B(\rho_0,\rho_1) = \inf_{E\in\mathcal M} B\big(p_0(E), p_1(E)\big),
--   $$
--
--   where $E$ ranges over all POVMs $\mathcal M$ and $p_t(E)(x) = \mathrm{Tr}(\rho_t E_x)$. (By a theorem of Fuchs and Caves, cited but not used here, it equals $\mathrm{Tr}\sqrt{\sqrt{\rho_0}\,\rho_1\sqrt{\rho_0}}$.)
--
--   **Formalization Note** The paper writes $\min$ (p.10: "more carefully, one should use infimum"). The infimum is taken in $\mathbb R$ over the set of values at all POVMs $E : \mathrm{Fin}\,m \to M_n(\mathbb C)$, $m\in\mathbb N$; the set is nonempty and bounded below by $0$. The closed fidelity formula is not used as the definition.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Definition 8, eq. (23), p.13

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsVdGraaf_outcomeDist
import Definitions.Def_FuchsVdGraaf_bhattacharyya

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Definition 8, eq. (23), p.13: the Bhattacharyya coefficient between two
density matrices `ρ₀`, `ρ₁` is
`B(ρ₀, ρ₁) = min_{E∈M} B(p₀(E), p₁(E))`, where the POVM `E` ranges over the set `M` of all
possible measurements and `p_t(E)(x) = Tr(ρ_t E_x)` (eq. (10)).

**Formalization Note.** The paper writes min and adds (p.10): "More carefully, one should use
'infimum' in this definition." This is the infimum (`sInf` in `ℝ`) of the *set* of values
`B(p₀(E), p₁(E))` over every POVM `E : Fin m → Matrix n n ℂ` with any number `m` of outcomes.
The set contains the value at the one-outcome POVM `![1]`, so it is nonempty, and for density
matrices it lies in a bounded interval, so the `sInf` is the paper's infimum and not a junk value. -/
noncomputable def qBhattacharyya {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ) : ℝ :=
  sInf {v : ℝ | ∃ (m : ℕ) (E : Fin m → Matrix n n ℂ),
    IsPOVM E ∧ v = bhattacharyya (outcomeDist ρ0 E) (outcomeDist ρ1 E)}

end FuchsVdGraaf


