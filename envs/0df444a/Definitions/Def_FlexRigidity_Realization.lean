-- Prove2me | Definitions.Def_FlexRigidity_Realization
-- name    : FlexRigidity_Realization
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:45.456387+00:00
-- url     : https://prove2.me/theorems/f611aa9d-0195-4fcb-8b07-60703ad779fe
-- title:
--   Entanglement-based realization, Postulate Set 5.3(i)–(ii)
-- statement:
--   The realization of the trusted preparation: Alice's input distribution $P_X$, a pure state $|\phi\rangle_{S_{\mathrm A}S_{\mathrm B}}$, Alice's projective measurements $(\{T^x_a\}_a)_x$ on $S_{\mathrm A}$ and Bob's projective measurements $(\{N^y_b\}_b)_y$ on $S_{\mathrm B}$. `IsPostulate53ii G` states: $P_X(x)>0$ for every $x$ (inputs of probability zero are removed); $P_X$ is the $X$-marginal of $P_{XY}$; $|\phi\rangle$ is normalized; the measurements are projective; and the strategy is optimal for $\mathsf G$,
--   $$\sum_{x,y,a,b}P_{XY}(x,y)V(x,y,a,b)\langle\phi|(T^x_a\otimes N^y_b)|\phi\rangle=\omega^*(\mathsf G).$$
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Fact 5.2 and Postulate Set 5.3(i)–(ii), pp. 38–39

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_quantumValue
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_FlexRigidity_IsProjMeas
import Definitions.Def_ObliviousRSP_pureState
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Entanglement-based realization, Postulate Set 5.3(i)–(ii)** (Arqand–Kundu–Tan, *Flexible
rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, Fact 5.2 and Postulate Set 5.3, pp. 38–39):
Alice's input distribution `P_X`, a pure state `|ϕ⟩_{S_A S_B}`, Alice's projective measurements
`({T^x_a}_a)_x` on `S_A` and Bob's projective measurements `({N^y_b}_b)_y` on `S_B`.

`IsPostulate53ii G` says: `P_X(x) > 0` for every `x` (inputs of probability zero are removed,
p. 38); `P_X` is the `X`-marginal of `P_{XY}`; `|ϕ⟩` is normalized; the `T^x` and `N^y` are
projective; and the strategy `(|ϕ⟩, {T^x_a}, {N^y_b})` is optimal for `G`:
`Σ_{x,y,a,b} P_{XY}(x,y) V(x,y,a,b) ⟨ϕ|(T^x_a ⊗ N^y_b)|ϕ⟩ = ω*(G)` (Postulate 5.3(ii)). -/
structure Realization (X Y A B SA SB : Type) where
  /-- Alice's input distribution `P_X` -/
  PX : X → ℝ
  /-- the shared pure state `|ϕ⟩_{S_A S_B}` -/
  ϕ : SA × SB → ℂ
  /-- Alice's projective measurements `T^x_a` on `S_A` -/
  T : X → A → Matrix SA SA ℂ
  /-- Bob's projective measurements `N^y_b` on `S_B` -/
  N : Y → B → Matrix SB SB ℂ

/-- Postulate Set 5.3(i)–(ii) for the realization and the game `G`. -/
def Realization.IsPostulate53ii {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A]
    [Fintype B] [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (Rz : Realization X Y A B SA SB) (G : Game X Y A B) : Prop :=
  (∀ x, 0 < Rz.PX x) ∧ (∀ x, ∑ y, G.PXY x y = Rz.PX x) ∧ DHRUniq.IsUnitVec Rz.ϕ ∧
  (∀ x, IsProjMeas (Rz.T x)) ∧ (∀ y, IsProjMeas (Rz.N y)) ∧
  winProb G (ObliviousRSP.pureState Rz.ϕ) Rz.T Rz.N = quantumValue G

end FlexRigidity


