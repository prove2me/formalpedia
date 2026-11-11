-- Prove2me | Definitions.Def_FlexRigidity_depol
-- name    : FlexRigidity_depol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:16:44.580555+00:00
-- url     : https://prove2.me/theorems/46c12ff9-51d2-474d-aa90-7ff2da8a2731
-- title:
--   Depolarization $(1-\mu)X+\mu I/|S|$
-- statement:
--   For an operator $X$ on a register $S$, its $\mu$-depolarization is $(1-\mu)X+\mu I_S/|S|$. It gives $\omega^\mu_S$ (Lemma 4.5), $\omega^{\mu,x}_{S_i}$ (51) and $\tilde\omega^{\mu,x}_{S_i}$ (56).
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 4.5, p. 35; pp. 46, 49

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Depolarization** `(1 − µ) X + µ I_S/|S|` (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, Lemma 4.5, p. 35, and (36), (50), (56), pp. 37, 46,
49). -/
def depol {S : Type} [Fintype S] [DecidableEq S] (μ : ℝ) (X : Matrix S S ℂ) : Matrix S S ℂ :=
  (((1 - μ : ℝ)) : ℂ) • X + (((μ / (Fintype.card S : ℝ) : ℝ)) : ℂ) • (1 : Matrix S S ℂ)

end FlexRigidity


