-- Prove2me | Definitions.Def_FlexRigidity_Supplement_CHSH
-- name    : FlexRigidity_Supplement_CHSH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:07:26.43182+00:00
-- url     : https://prove2.me/theorems/e11a12ad-c6a3-44b1-85a6-5ed340fc550b
-- title:
--   The CHSH game, the Wiesner realization, and the honest noisy EPR pair
-- statement:
--   1. The **CHSH game**: inputs $x,y\in\{0,1\}$ uniform ($P_{XY}=1/4$), outputs $a,b\in\{0,1\}$, and the players win iff $a\oplus b=x\wedge y$.
--   2. The **Wiesner realization** of Protocol 1 for this game: $P_X$ uniform, the EPR pair $|\phi\rangle_{S_AS_B}=(|00\rangle+|11\rangle)/\sqrt2$, Alice's projectors
--   $$T^0_a=\tfrac12(I+(-1)^aZ),\qquad T^1_a=\tfrac12(I+(-1)^aX),$$
--   and Bob's usual CHSH measurements $N^y_b=\tfrac12\big(I+(-1)^b(Z+(-1)^yX)/\sqrt2\big)$. Measuring $S_A$ remotely prepares $H^x|a\rangle$ on $S_B$ with $P_{XA}(x,a)=1/4$, which is (75).
--   3. The **honest round state** under depolarizing noise $2\sqrt2\,\delta_{\mathrm{hon}}$:
--   $$(1-2\sqrt2\,\delta_{\mathrm{hon}})\,|\phi\rangle\langle\phi|+2\sqrt2\,\delta_{\mathrm{hon}}\,I_{S_AS_B}/4 .$$
--
--   With the ideal measurements this state wins CHSH with probability $\omega^*-\delta_{\mathrm{hon}}$, $\omega^*=\tfrac12+\tfrac1{2\sqrt2}$. These are the objects of the uncloneable-encryption and copy-protection protocols (Protocols 3–5).
--
--   **Formalization Note** Bits are `Bool`; the game is the published `FlexRigidity.Game`, the realization the published `FlexRigidity.Realization`, the noisy state the published `FlexRigidity.depol` applied to `ObliviousRSP.pureState` of the EPR vector.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d0306379cc99bf71e2a9200405805925b8b1d8429e876e9655a3fe12c), §6 p. 60 (honest noise), §6.1.1 p. 62 (CHSH, Wiesner states, (75)), Fact 6.4 p. 64 (T^x_a)

import Mathlib
import Definitions.Def_FlexRigidity_Game
import Definitions.Def_FlexRigidity_Realization
import Definitions.Def_FlexRigidity_depol
import Definitions.Def_ObliviousRSP_pureState

set_option autoImplicit false

open scoped Matrix ComplexOrder

noncomputable section

namespace FlexRigidity.Supplement

/-- **The CHSH game** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact sha256
8c67699d…, §6.1.1, p. 62, and §6, p. 60): inputs `x, y ∈ {0,1}` uniform, outputs `a, b ∈ {0,1}`,
and the players win iff `a ⊕ b = x ∧ y`. Bits are `Bool` (`false` = 0, `true` = 1). -/
def chshGame : Game Bool Bool Bool Bool where
  PXY := fun _ _ => 1 / 4
  V := fun x y a b => xor a b == (x && y)

/-- Pauli `Z` on a qubit. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Pauli `X` on a qubit. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The sign `(−1)^a`. -/
def sgn (a : Bool) : ℂ := if a then -1 else 1

/-- **Alice's ideal preparation projectors** (p. 64, Fact 6.4): `T^0_a = (I + (−1)^a Z)/2` and
`T^1_a = (I + (−1)^a X)/2`, the `Z`- and `X`-basis projectors (p. 62). Honest Bob uses the same
projectors on his retained qubit when he decrypts with key bit `x` (Protocol 3, step 4). -/
def wiesnerT (x a : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + sgn a • (if x then pauliX else pauliZ))

/-- **Bob's usual CHSH measurements** (p. 62): the eigenprojectors of `(Z + X)/√2` for `y = 0` and
of `(Z − X)/√2` for `y = 1`, `N^y_b = (I + (−1)^b (Z + (−1)^y X)/√2)/2`. -/
def chshN (y b : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + sgn b • (((1 / Real.sqrt 2 : ℝ) : ℂ) • (pauliZ + sgn y • pauliX)))

/-- The EPR pair `|ϕ⟩ = (|00⟩ + |11⟩)/√2` on `S_A S_B` (p. 62). -/
def epr : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- **The Wiesner-state realization of CHSH** (pp. 62–64): `P_X` uniform, `|ϕ⟩` the EPR pair,
Alice's projectors `T^x_a`, Bob's CHSH measurements `N^y_b`. Measuring `S_A` remotely prepares
`H^x|a⟩` on `S_B` with `P_{XA}(x, a) = 1/4` (75). -/
def wiesnerRz : Realization Bool Bool Bool Bool (Fin 2) (Fin 2) where
  PX := fun _ => 1 / 2
  ϕ := epr
  T := wiesnerT
  N := chshN

/-- **The honest CHSH round state under depolarizing noise** (p. 60):
`(1 − 2√2 δ_hon) |ϕ⟩⟨ϕ| + 2√2 δ_hon I_{S_A S_B}/4`, one EPR pair per round. -/
def honestCHSH (δ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  depol (2 * Real.sqrt 2 * δ) (ObliviousRSP.pureState epr)

end FlexRigidity.Supplement


