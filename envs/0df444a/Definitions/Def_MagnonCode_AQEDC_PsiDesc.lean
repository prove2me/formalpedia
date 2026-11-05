-- Prove2me | Definitions.Def_MagnonCode_AQEDC_PsiDesc
-- name    : MagnonCode_AQEDC_PsiDesc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:13.602653+00:00
-- url     : https://prove2.me/theorems/af9e2624-4224-49f1-8224-f1ec1a14fc4d
-- title:
--   Eq. (83): the descendants $|\Psi_r\rangle=S_-^r|\Psi\rangle$
-- statement:
--   The $r$-th descendant of the one-magnon state is
--
--   $$
--   |\Psi_r\rangle:=S_-^r|\Psi\rangle,\qquad r=0,\dots,n-2.
--   $$
--
--   It has $r+1$ qubits in the state $|0\rangle$ in each of its components, so different descendants have different magnetization.
--
--   **Formalization Note** The definition is total in $r$; every statement of the mission restricts to $r\le n-2$.
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Eq. (83), p. 54

import Mathlib
import Definitions.Def_MagnonCode_AQEDC_Psi

open scoped Matrix

namespace MagnonCode.AQEDC

/-- **Eq. (83)** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 54): the `r`-th descendant `|Ψ_r⟩ = S₋^r |Ψ⟩`.

**Formalization Note** The page uses `r = 0, …, n − 2`; this total definition also has values at
larger `r`, which no statement of the mission uses. -/
noncomputable def PsiDesc (n r : ℕ) : (Fin n → Fin 2) → ℂ :=
  (SMinus n ^ r) *ᵥ Psi n

end MagnonCode.AQEDC


