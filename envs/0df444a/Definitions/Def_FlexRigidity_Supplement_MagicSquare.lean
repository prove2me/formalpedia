-- Prove2me | Definitions.Def_FlexRigidity_Supplement_MagicSquare
-- name    : FlexRigidity_Supplement_MagicSquare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:12:06.621698+00:00
-- url     : https://prove2.me/theorems/e858f84d-a8e1-486a-b39e-0327aa98d573
-- title:
--   The Magic Square game and perfect strategies on two EPR pairs
-- statement:
--   In the **Magic Square game**, independent uniform inputs $x,y\in\{0,1,2\}$ ask Alice for an even-parity row $a\in\{0,1\}^3$ and Bob for an odd-parity column $b\in\{0,1\}^3$ (four possible answers each); they win iff $a[y]=b[x]$. Its quantum value is $\omega^*=1$.
--
--   A **perfect strategy on two EPR pairs** is a pair of projective measurements $\{T^x_a\}_a$ on $S_A$ and $\{N^y_b\}_b$ on $S_B$, $|S_A|=|S_B|=4$, with rank-one projectors, that wins with probability $1$ on $|\phi\rangle_{S_AS_B}=|\Phi^+\rangle_{A_1B_1}|\Phi^+\rangle_{A_2B_2}$. The **honest round state** under depolarizing noise $2\delta_{\mathrm{hon}}$ is $(1-2\delta_{\mathrm{hon}})|\phi\rangle\langle\phi|+2\delta_{\mathrm{hon}}I_{S_AS_B}/16$.
--
--   These are the objects of the blind randomness expansion protocol (Protocol 6, Theorem 6.14).
--
--   **Formalization Note** The game is the published `FlexRigidity.Game` with answer alphabets the subtypes of even- and odd-parity strings.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d0306379cc99bf71e2a9200405805925b8b1d8429e876e9655a3fe12c), §6 p. 60 (honest noise), §6.3.1 p. 70 (game), Fact 6.11 p. 71 (perfect strategy)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Game
import Definitions.Def_FlexRigidity_winProb
import Definitions.Def_FlexRigidity_IsProjMeas
import Definitions.Def_FlexRigidity_depol
import Definitions.Def_ObliviousRSP_pureState

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr)

noncomputable section

namespace FlexRigidity.Supplement

/-- Alice's Magic Square answers: rows `a ∈ {0,1}^3` of even parity (four values). -/
abbrev MSRow : Type := {a : Fin 3 → Bool // Even (Finset.univ.filter fun i => a i = true).card}

/-- Bob's Magic Square answers: columns `b ∈ {0,1}^3` of odd parity (four values). -/
abbrev MSCol : Type := {b : Fin 3 → Bool // Odd (Finset.univ.filter fun i => b i = true).card}

/-- **The Magic Square game** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact
sha256 8c67699d…, §6.3.1, p. 70): independent uniform inputs `x, y ∈ {0,1,2}`; Alice answers an
even-parity row `a`, Bob an odd-parity column `b`; they win iff `a[y] = b[x]`. -/
def msGame : Game (Fin 3) (Fin 3) MSRow MSCol where
  PXY := fun _ _ => 1 / 9
  V := fun x y a b => a.1 y == b.1 x

/-- Two EPR pairs `|ϕ⟩_{S_A S_B} = |Φ⁺⟩_{A₁B₁}|Φ⁺⟩_{A₂B₂}` with `S_A = A₁A₂`, `S_B = B₁B₂`
(p. 60 and Fact 6.11, p. 71). -/
def eprPair2 : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) → ℂ :=
  fun p => if p.1 = p.2 then (1 / 2 : ℂ) else 0

/-- **A perfect Magic Square strategy on two EPR pairs** (Fact 6.11, p. 71): projective
measurements `{T^x_a}_a` on `S_A` and `{N^y_b}_b` on `S_B` with rank-one projectors (trace `1`),
which win the Magic Square game with probability `1` on `|ϕ⟩ = eprPair2`. -/
def IsPerfectMSStrategy (T : Fin 3 → MSRow → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (N : Fin 3 → MSCol → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  (∀ x, IsProjMeas (T x)) ∧ (∀ y, IsProjMeas (N y)) ∧ (∀ x a, tr (T x a) = 1) ∧
    (∀ y b, tr (N y b) = 1) ∧ winProb msGame (ObliviousRSP.pureState eprPair2) T N = 1

/-- **The honest Magic Square round state under depolarizing noise** (p. 60):
`(1 − 2δ_hon)|ϕ⟩⟨ϕ| + 2δ_hon I_{S_A S_B}/16`. -/
def honestMS (δ : ℝ) : Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ :=
  depol (2 * δ) (ObliviousRSP.pureState eprPair2)

end FlexRigidity.Supplement


