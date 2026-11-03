-- Prove2me | Definitions.Def_HolevoEntropyGain_gibbsOperator
-- name    : HolevoEntropyGain_gibbsOperator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:00.421198+00:00
-- url     : https://prove2.me/theorems/32f8e244-4a8a-4df1-a713-0a4a4a97b9fe
-- title:
--   The operator $\exp(-\beta F)$
-- statement:
--   For $F$ with eigenbasis $(e_n)$ and eigenvalues $(E_n)$ and a real $\beta$,
--
--   $$
--   \exp(-\beta F) = \sum_n e^{-\beta E_n}\,|e_n\rangle\langle e_n| ,
--   $$
--
--   given by its coefficient array $\big(\sum_n e^{-\beta E_n}\, e_n(i)\,\overline{e_n(j)}\big)_{i,j}$. Under (5), $\operatorname{Tr}\exp(-\beta F) = \sum_n e^{-\beta E_n}<\infty$ for every $\beta>0$, and it is trace class.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (5), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters

open QAlgorithms.RealRegisters (Hilbert)

namespace HolevoEntropyGain

/-- The coefficient array of `exp(-βF) = ∑ₙ e^{-βEₙ} |eₙ⟩⟨eₙ|`, for `F` with spectral data `(eₙ, Eₙ)`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (5), p.3, PDF p.3). -/
noncomputable def gibbsOperator {I : Type} (e : HilbertBasis I ℂ (Hilbert I)) (E : I → ℝ) (β : ℝ) :
    Matrix I I ℂ :=
  fun i j => ∑' n, (Real.exp (-β * E n) : ℂ) * (e n : Hilbert I) i * star ((e n : Hilbert I) j)

end HolevoEntropyGain


