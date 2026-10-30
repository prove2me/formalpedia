-- Prove2me | Definitions.Def_FuchsVdGraaf_qErrorProb
-- name    : FuchsVdGraaf_qErrorProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:13.332718+00:00
-- url     : https://prove2.me/theorems/1222e66a-905c-4242-a1a6-6821265bdf64
-- title:
--   Quantum probability of error $\mathrm{PE}(\rho_0,\rho_1)$ (Definition 4)
-- statement:
--   For density matrices $\rho_0, \rho_1$, the **probability of error** is the smallest classical probability of error achievable by a measurement:
--
--   $$
--   \mathrm{PE}(\rho_0,\rho_1) = \inf_{E\in\mathcal M} \mathrm{PE}\big(p_0(E), p_1(E)\big),
--   $$
--
--   where $E$ ranges over all POVMs $\mathcal M$ (any number of outcomes) and $p_t(E)(x) = \mathrm{Tr}(\rho_t E_x)$.
--
--   **Formalization Note** The paper writes $\min$ and remarks (p.10) that "more carefully, one should use infimum". The infimum is taken in $\mathbb R$ over the set of values at all POVMs $E : \mathrm{Fin}\,m \to M_n(\mathbb C)$, $m \in \mathbb N$; this set is nonempty (trivial one-outcome POVM) and bounded below by $0$, so the infimum is the true one.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Definition 4, eq. (12), p.10

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsVdGraaf_outcomeDist
import Definitions.Def_FuchsVdGraaf_errorProb

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Definition 4, eq. (12), p.10: the probability of error between two
density matrices `ρ₀`, `ρ₁` is
`PE(ρ₀, ρ₁) = min_{E∈M} PE(p₀(E), p₁(E))`, where the POVM `E` ranges over the set `M` of all
possible measurements and `p_t(E)(x) = Tr(ρ_t E_x)` (eq. (10)).

**Formalization Note.** The paper writes min and adds (p.10): "More carefully, one should use
'infimum' in this definition." This is the infimum (`sInf` in `ℝ`) of the *set* of values
`PE(p₀(E), p₁(E))` over every POVM `E : Fin m → Matrix n n ℂ` with any number `m` of outcomes.
The set contains the value at the one-outcome POVM `![1]`, so it is nonempty, and for density
matrices it lies in a bounded interval, so the `sInf` is the paper's infimum and not a junk value. -/
noncomputable def qErrorProb {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ) : ℝ :=
  sInf {v : ℝ | ∃ (m : ℕ) (E : Fin m → Matrix n n ℂ),
    IsPOVM E ∧ v = errorProb (outcomeDist ρ0 E) (outcomeDist ρ1 E)}

end FuchsVdGraaf


